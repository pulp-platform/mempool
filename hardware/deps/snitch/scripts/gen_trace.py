#!/usr/bin/env python3
# This script takes a trace generated for a Snitch hart and transforms the
# additional decode stage info into meaningful annotation. It also counts
# and computes various performance metrics up to each mcycle CSR read.

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>

# TODO: OPER_TYPES and FPU_OPER_TYPES could break: optimization might alter enum mapping
# TODO: We annotate all FP16 LSU values as IEEE, not FP16ALT... can we do better?

import sys
import re
import math
import argparse
from ctypes import c_int32, c_uint32
from collections import deque, defaultdict


EXTRA_WB_WARN = 'WARNING: {} transactions still in flight for {}.'

GENERAL_WARN = 'WARNING: Inconsistent final state; performance metrics may be inaccurate. Is this trace complete?\n'

TRACE_IN_REGEX = r'(\d+)\s+(\d+)\s+(0x[0-9A-Fa-fz]+)\s+([^#;]*)(\s*#;\s*(.*))?'

TRACE_OUT_FMT = '{:>8} {:>8} {:>10} {:<30}'


# -------------------- Tracer configuration  --------------------

# Below this absolute value: use signed int representation. Above: unsigned 32-bit hex
MAX_SIGNED_INT_LIT = 0xFFFF

# Performance keys which only serve to compute other metrics: omit on printing
PERF_EVAL_KEYS_OMIT = ('start', 'end', 'snitch_issues', 'snitch_load_latency')


# -------------------- Architectural constants and enums  --------------------

REG_ABI_NAMES_I = (
	'zero', 'ra', 'sp', 'gp', 'tp',
	't0', 't1', 't2',
	's0', 's1',
	*('a{}'.format(i) for i in range(8)),
	*('s{}'.format(i) for i in range(2, 12)),
	*('t{}'.format(i) for i in range(3, 7))
)

REG_ABI_NAMES_F = (
	*('ft{}'.format(i) for i in range(0, 8)),
	'fs0', 'fs1',
	'fa0', 'fa1',
	*('fa{}'.format(i) for i in range(2, 8)),
	*('fs{}'.format(i) for i in range(2, 12)),
	*('ft{}'.format(i) for i in range(8, 12))
)

TRACE_SRCES = {'snitch': 0, 'fpu': 1, 'sequencer': 2}

LS_SIZES = ('Byte', 'Half', 'Word', 'Doub')

OPER_TYPES = {'gpr': 1, 'csr': 8}

FPU_OPER_TYPES = ('NONE', 'acc', 'rs1', 'rs2', 'rs3', 'rs1', 'rd')

FLOAT_FMTS = ((8, 23), (11, 52), (5, 10), (5, 2), (8, 7))

LS_TO_FLOAT = (3, 2, 0, 1)

CSR_NAMES = {0xb00: 'mcycle', 0xf14: 'mhartid'}


# -------------------- FPU helpers  --------------------

def flt_oper(extras: dict, port: int) -> (str, str):
	op_sel = extras['op_sel_{}'.format(port)]
	oper_type = FPU_OPER_TYPES[op_sel]
	if oper_type == 'acc':
		return 'ac{}'.format(port + 1), int_lit(extras['acc_qdata_{}'.format(port)], extras['int_fmt'])
	elif oper_type == 'NONE':
		return oper_type, None
	else:
		fmt = LS_TO_FLOAT[extras['ls_size']] if extras['is_store'] else extras['src_fmt']
		return REG_ABI_NAMES_F[extras[oper_type]], flt_lit(extras['op_{}'.format(port)], fmt)


def flt_decode(val: int, fmt: int) -> float:
	# get format and bit vector
	w_exp, w_mnt = FLOAT_FMTS[fmt]
	width = 1 + w_exp + w_mnt
	bitstr = '{:064b}'.format(val)[-width:]
	# print(bitstr)
	# Read bit vector slices
	sgn = -1.0 if bitstr[0] == '1' else 1.0
	mnt = int(bitstr[w_exp + 1:], 2)
	exp_unb = int(bitstr[1:w_exp + 1], 2)
	# derive base and exponent
	bse = int('1' + bitstr[w_exp + 1:], 2) / (2 ** w_mnt)
	exp_bias = -(2 ** (w_exp - 1) - 1)
	exp = exp_unb + exp_bias
	# case analysis
	if exp_unb == 2 ** w_exp - 1:
		return sgn * float('inf' if mnt == 0 else 'nan')
	elif exp_unb == 0 and mnt == 0:
		return sgn * 0.0
	elif exp_unb == 0:
		return float(sgn * mnt / (2 ** w_mnt) * (2 ** (exp_bias + 1)))
	else:
		return float(sgn * bse * (2 ** exp))


def flt_fmt(flt: float, width: int = 7) -> str:
	# If default literal shorter: use it
	default_str = str(flt)
	if len(default_str) - 1 <= width:
		return default_str
	# Else: fix significant digits, using exponential if needed
	exp, _ = math.frexp(flt)
	fmt = '{:1.' + str(width - 3) + 'e}'
	if not math.isnan(exp) and -1 < exp <= width:
		exp = int(exp)
		fmt = '{:' + str(exp) + '.' + str(width - exp) + 'f}'
	return fmt.format(flt)


# -------------------- Literal formatting  --------------------

def int_lit(num: int, size: int = 2, force_hex: bool = False) -> str:
	width = (8 * int(2 ** size))
	size_mask = (0x1 << width) - 1
	num = num & size_mask  # num is unsigned
	num_signed = c_int32(c_uint32(num).value).value
	if force_hex or abs(num_signed) > MAX_SIGNED_INT_LIT:
		return '0x{0:0{1}x}'.format(num, width // 4)
	else:
		return str(num_signed)


def flt_lit(num: int, fmt: int, width: int = 7) -> str:
	return flt_fmt(flt_decode(num, fmt), width)


# -------------------- FPU Sequencer --------------------

def dasm_seq(extras: dict,) -> str:
	return '{:<8}'.format('frep') + ', '.join([str(extras['max_rpt']+1), str(extras['max_inst']+1)]
			+ ([bin(extras['stg_mask']), str(extras['stg_max']+1)] if extras['stg_mask'] else []))


def emul_seq(fseq_info: dict, permissive: bool = False) -> (str, int, str, tuple):
	fseq_annot = None
	# We are only called on FPSS issues, not on FSEQ issues -> we must consume FReps in same call
	cfg = fseq_info['curr_cfg']
	if cfg is None:
		is_frep = fseq_info['fpss_pcs'][-1][2] if len(fseq_info['fpss_pcs']) else False
		# Is an FRep incoming?
		if is_frep:
			fseq_info['fpss_pcs'].pop()
			cfg = fseq_info['cfg_buf'].pop()
			cfg['inst_iter'] = 0
			cfg['fpss_buf'] = deque()
			cfg['outer_buf'] = deque()
			fseq_info['curr_cfg'] = cfg
	# Are we working on an FRep ...
	if cfg is not None:
		# If we are still filling our loop buffer: add to it and replicate
		if cfg['inst_iter'] <= cfg['max_inst']:
			pc_str, curr_sec, is_frep = fseq_info['fpss_pcs'].pop()
			if is_frep:
				msg_type = 'WARNING' if permissive else 'FATAL'
				sys.stderr.write('{}: FRep at {} contains another nested FRep'.format(msg_type, cfg['fseq_pc']))
				if not permissive:
					sys.exit(1)
			# Outer loops: first consume loop body, then replicate buffer
			if cfg['is_outer']:
				buf_entry = (pc_str, curr_sec, (0, cfg['inst_iter']))
				cfg['fpss_buf'].appendleft(buf_entry)
				cfg['outer_buf'].appendleft(buf_entry)
				# Once all loop instructions received: replicate buffer in outer-loop order
				if cfg['inst_iter'] == cfg['max_inst']:
					for curr_rep in range(1, cfg['max_rpt'] + 1):
						ob_rev = reversed(cfg['outer_buf'])
						for inst_idx, inst in enumerate(ob_rev):
							pc_str, curr_sec, _ = inst
							fseq_annot = (curr_rep, inst_idx)
							cfg['fpss_buf'].appendleft((pc_str, curr_sec, fseq_annot))
			# Inner loops: replicate instructions during loop body consumption
			else:
				for curr_rep in range(0, cfg['max_rpt'] + 1):
					fseq_annot = (curr_rep, cfg['inst_iter'])
					cfg['fpss_buf'].appendleft((pc_str, curr_sec, fseq_annot))
			# Iterate loop body instruction consumed
			cfg['inst_iter'] += 1
		# Pull our instruction from the loop buffer
		pc_str, curr_sec, fseq_annot = cfg['fpss_buf'].pop()
		# If we reached last iteration: terminate this FRep
		if fseq_annot[0] == cfg['max_rpt'] and fseq_annot[1] == cfg['max_inst']:
			fseq_info['curr_cfg'] = None
	# ... or is this a regular pass-through?
	else:
		pc_str, curr_sec, _ = fseq_info['fpss_pcs'].pop()
	fseq_pc_str = None if cfg is None else cfg['fseq_pc']
	return pc_str, curr_sec, fseq_pc_str, fseq_annot


# -------------------- Annotation --------------------


def read_annotations(dict_str: str) -> dict:
	# return literal_eval(dict_str) 	# Could be used, but slow due to universality: needs compiler
	return {key: int(val, 16) for key, val in re.findall(r"'([^']+)'\s*:\s*([^\s,]+)", dict_str)}


def annotate_snitch(
		extras: dict,
		cycle: int,
		pc: int,
		gpr_wb_info: dict,
		perf_metrics: list,
		annot_fseq_offl: bool = False,
		force_hex_addr: bool = True,
		permissive: bool = False
) -> str:
	# Compound annotations in datapath order
	ret = []
	# If Sequencer offload: annotate if desired
	if annot_fseq_offl and extras['fpu_offload']:
		target_name = 'FSEQ' if extras['is_seq_insn'] else 'FPSS'
		ret.append('{} <~~ 0x{:08x}'.format(target_name, pc))
	# Regular linear datapath operation
	if not (extras['stall'] or extras['fpu_offload']):
		# Operand registers
		if extras['opa_select'] == OPER_TYPES['gpr'] and extras['rs1'] != 0:
			ret.append('{:<3} = {}'.format(REG_ABI_NAMES_I[extras['rs1']], int_lit(extras['opa'])))
		if extras['opb_select'] == OPER_TYPES['gpr'] and extras['rs2'] != 0:
			ret.append('{:<3} = {}'.format(REG_ABI_NAMES_I[extras['rs2']], int_lit(extras['opb'])))
		# CSR (always operand b)
		if extras['opb_select'] == OPER_TYPES['csr']:
			csr_addr = extras['csr_addr']
			csr_name = CSR_NAMES[csr_addr] if csr_addr in CSR_NAMES else 'csr@{:x}'.format(csr_addr)
			cycles_past = extras['opb']
			if csr_name == 'mcycle':
				perf_metrics[-1]['end'] = cycles_past
				perf_metrics.append(defaultdict(int))
				perf_metrics[-1]['start'] = cycles_past + 2
			ret.append('{} = {}'.format(csr_name, int_lit(cycles_past)))
		# Load / Store
		if extras['is_load']:
			perf_metrics[-1]['snitch_loads'] += 1
			gpr_wb_info[extras['rd']].appendleft(cycle)
			ret.append('{:<3} <~~ {}[{}]'.format(
				REG_ABI_NAMES_I[extras['rd']], LS_SIZES[extras['ls_size']],
				int_lit(extras['alu_result'], force_hex=force_hex_addr)))
		elif extras['is_store']:
			perf_metrics[-1]['snitch_stores'] += 1
			ret.append('{} ~~> {}[{}]'.format(
				int_lit(extras['gpr_rdata_1']), LS_SIZES[extras['ls_size']],
				int_lit(extras['alu_result'], force_hex=force_hex_addr)))
		# Branches: all reg-reg ops
		elif extras['is_branch']:
			ret.append('{}taken'.format('' if extras['alu_result'] else 'not '))
		# Datapath (ALU / Jump Target / Bypass) register writeback
		if extras['write_rd'] and extras['rd'] != 0:
			ret.append('(wrb) {:<3} <-- {}'.format(REG_ABI_NAMES_I[extras['rd']], int_lit(extras['writeback'])))
	# Retired loads and accelerator (includes FPU) data: can come back on stall and during other ops
	if extras['retire_load'] and extras['lsu_rd'] != 0:
		try:
			start_time = gpr_wb_info[extras['lsu_rd']].pop()
			perf_metrics[-1]['snitch_load_latency'] += cycle - start_time
		except IndexError:
			msg_type = 'WARNING' if permissive else 'FATAL'
			sys.stderr.write('{}: In cycle {}, LSU attempts writeback to {}, but none in flight.\n'.format(
				msg_type, cycle, REG_ABI_NAMES_F[extras['fpr_waddr']]))
			if not permissive:
				sys.exit(1)
		ret.append('(lsu) {:<3} <-- {}'.format(REG_ABI_NAMES_I[extras['lsu_rd']], int_lit(extras['ld_result_32'])))
	if extras['retire_acc'] and extras['acc_pid'] != 0:
		ret.append('(acc) {:<3} <-- {}'.format(REG_ABI_NAMES_I[extras['acc_pid']], int_lit(extras['acc_pdata_32'])))
	# Any kind of PC change: Branch, Jump, etc.
	if not extras['stall'] and extras['pc_d'] != pc + 4:
		ret.append('goto {}'.format(int_lit(extras['pc_d'])))
	# Return comma-delimited list
	return ', '.join(ret)


def annotate_fpu(
		extras: dict,
		cycle: int,
		fpr_wb_info: dict,
		perf_metrics: list,
		curr_sec: int = -1, 	# Everything FPU does may have been issued in a previous section
		force_hex_addr: bool = True,
		permissive: bool = False
) -> str:
	ret = []
	# On issuing of instruction
	if extras['acc_q_hs']:
		# If computation initiated: remember FPU destination format
		if extras['use_fpu'] and not extras['fpu_in_acc']:
			fpr_wb_info[extras['fpu_in_rd']].appendleft((extras['dst_fmt'], cycle))
		# Operands: omit on store
		if not extras['is_store']:
			for i_op in range(3):
				oper_name, val = flt_oper(extras, i_op)
				if oper_name != 'NONE':
					ret.append('{:<4} = {}'.format(oper_name, val))
		# Load / Store requests
		if extras['lsu_q_hs']:
			s = extras['ls_size']
			if extras['is_load']:
				perf_metrics[curr_sec]['fpss_loads'] += 1
				# Load initiated: remember LSU destination format
				fpr_wb_info[extras['rd']].appendleft((LS_TO_FLOAT[s], cycle))
				ret.append('{:<4} <~~ {}[{}]'.format(
					REG_ABI_NAMES_F[extras['rd']], LS_SIZES[s], int_lit(extras['lsu_qaddr'], force_hex=force_hex_addr)))
			if extras['is_store']:
				perf_metrics[curr_sec]['fpss_stores'] += 1
				_, val = flt_oper(extras, 1)
				ret.append('{} ~~> {}[{}]'.format(
					val, LS_SIZES[s], int_lit(extras['lsu_qaddr'], force_hex=force_hex_addr)))
	# On FLOP completion
	if extras['fpu_out_hs']:
		perf_metrics[-1]['fpss_fpu_issues'] += 1
	# Register writeback
	if extras['fpr_we']:
		writer = 'acc' if extras['acc_q_hs'] and extras['acc_wb_ready'] else (
			'fpu' if extras['fpu_out_hs'] and not extras['fpu_out_acc'] else 'lsu')
		fmt = 0  # accelerator bus format is 0 for regular float32
		if writer == 'fpu' or writer == 'lsu':
			try:
				fmt, start_time = fpr_wb_info[extras['fpr_waddr']].pop()
				if writer == 'lsu':
					perf_metrics[curr_sec]['fpss_load_latency'] += cycle - start_time
				else:
					perf_metrics[curr_sec]['fpss_fpu_latency'] += cycle - start_time
			except IndexError:
				msg_type = 'WARNING' if permissive else 'FATAL'
				sys.stderr.write('{}: In cycle {}, {} attempts writeback to {}, but none in flight.\n'.format(
					msg_type, cycle, writer.upper(), REG_ABI_NAMES_F[extras['fpr_waddr']]))
				if not permissive:
					sys.exit(1)
		ret.append('(f:{}) {:<4} <-- {}'.format(
			writer, REG_ABI_NAMES_F[extras['fpr_waddr']], flt_lit(extras['fpr_wdata'], fmt)))
	return ', '.join(ret)


# noinspection PyTypeChecker
def annotate_insn(
		line: str,
		gpr_wb_info: dict,  				# One deque (FIFO) per GPR storing start cycles for each GPR WB
		fpr_wb_info: dict,  				# One deque (FIFO) per FPR storing start cycles and formats for each FPR WB
		fseq_info: dict,  					# Info on the sequencer to properly map tunneled instruction PCs
		perf_metrics: list,  				# A list performance metric dicts
		dupl_time_info: bool = True,  		# Show sim time and cycle again if same as previous line?
		last_time_info: tuple = None,  		# Previous timestamp (keeps this method stateless)
		annot_fseq_offl: bool = False, 		# Annotate whenever core offloads to CPU on own line
		force_hex_addr: bool = True,
		permissive: bool = True
) -> (str, tuple, bool):  					# Return time info, whether trace line contains no info, and fseq_len
	match = re.search(TRACE_IN_REGEX, line.strip('\n'))
	if match is None:
		raise ValueError('Not a valid trace line:\n{}'.format(line))
	time_str, cycle_str, pc_str, insn, _, extras_str = match.groups()
	time_info = (int(time_str), int(cycle_str))
	show_time_info = (dupl_time_info or time_info != last_time_info)
	time_info_strs = tuple((str(elem) if show_time_info else '') for elem in time_info)
	# Annotated trace
	if extras_str:
		extras = read_annotations(extras_str)
		# Annotate snitch
		if extras['source'] == TRACE_SRCES['snitch']:
			annot = annotate_snitch(extras, time_info[1], int(pc_str, 16),
				gpr_wb_info, perf_metrics, annot_fseq_offl, force_hex_addr, permissive)
			if extras['fpu_offload']:
				perf_metrics[-1]['snitch_fseq_offloads'] += 1
				fseq_info['fpss_pcs'].appendleft((pc_str, len(perf_metrics) - 1, extras['is_seq_insn']))
				if extras['is_seq_insn']:
					fseq_info['fseq_pcs'].appendleft(pc_str)
			if extras['stall'] or extras['fpu_offload']:
				insn, pc_str = ('', '')
			else:
				perf_metrics[-1]['snitch_issues'] += 1
		# Annotate sequencer
		elif extras['source'] == TRACE_SRCES['sequencer']:
			if extras['cbuf_push']:
				fseq_info['cfg_buf'].appendleft(extras)
				frep_pc_str = fseq_info['fseq_pcs'].pop()
				insn, pc_str = (dasm_seq(extras), frep_pc_str)
				extras['fseq_pc'] = frep_pc_str
				annot = ', '.join(['outer' if extras['is_outer'] else 'inner',
					'{} issues'.format((extras['max_inst'] + 1) * (extras['max_rpt'] + 1))])
			else:
				insn, pc_str, annot = ('', '', '')
		# Annotate FPSS
		elif extras['source'] == TRACE_SRCES['fpu']:
			annot_list = []
			if not extras['acc_q_hs']:
				insn, pc_str = ('', '')
			else:
				pc_str, curr_sec, fseq_pc_str, fseq_annot = emul_seq(fseq_info, permissive)
				fseq_info['curr_sec'] = curr_sec
				perf_metrics[curr_sec]['end_fpss'] = time_info[1] 	# Record cycle in case this was last insn in section
				perf_metrics[curr_sec]['fpss_issues'] += 1
				if fseq_annot is not None:
					annot_list.append('[{} {}:{}]'.format(fseq_pc_str[-4:], *fseq_annot))
			annot_list.append(annotate_fpu(extras, time_info[1],
				fpr_wb_info, perf_metrics, fseq_info['curr_sec'], force_hex_addr, permissive))
			annot = ', '.join(annot_list)
		else:
			raise ValueError('Unknown trace source: {}'.format(extras['source']))
		empty = not (insn or annot)  # omit empty trace lines (due to double stalls, performance measures)
		if empty:
			time_info = last_time_info  # Reset time info if empty: last line on record is previous one!
		return (TRACE_OUT_FMT + ' #; {}').format(*time_info_strs, pc_str, insn, annot), time_info, empty
	# Vanilla trace
	else:
		return TRACE_OUT_FMT.format(*time_info_strs, pc_str, insn), time_info, False


# -------------------- Performance metrics --------------------

def safe_div(dividend, divisor):
	return dividend / divisor if divisor else None


def eval_perf_metrics(perf_metrics: list):
	for seg in perf_metrics:
		end = seg['end']
		cycles = end - seg['start'] + 1
		seg.update({
			# Snitch
			'snitch_avg_load_latency': safe_div(seg['snitch_load_latency'], seg['snitch_loads']),
			'snitch_occupancy': safe_div(seg['snitch_issues'], cycles),
		})
		seg['cycles'] = cycles
		seg['total_ipc'] = seg['snitch_occupancy']


def fmt_perf_metrics(perf_metrics: list, idx: int, omit_keys: bool = True):
	ret = ['Performance metrics for section {} @ ({}, {}):'.format(
		idx, perf_metrics[idx]['start'], perf_metrics[idx]['end'])]
	for key, val in perf_metrics[idx].items():
		if omit_keys and key in PERF_EVAL_KEYS_OMIT:
			continue
		if val is None:
			val_str = str(None)
		elif isinstance(val, float):
			val_str = flt_fmt(val, 4)
		else:
			val_str = int_lit(val)
		ret.append('{:<40}{:>10}'.format(key, val_str))
	return '\n'.join(ret)


# -------------------- Main --------------------

# noinspection PyTypeChecker
def main():
	# Argument parsing and iterator creation
	parser = argparse.ArgumentParser()
	parser.add_argument('infile', metavar='infile.dasm',  nargs='?', type=argparse.FileType('r'), default=sys.stdin,
						help='A matching ASCII signal dump',)
	parser.add_argument('-o', '--offl', action='store_true',
						help='Annotate FPSS and sequencer offloads when they happen in core')
	parser.add_argument('-s', '--saddr', action='store_true',
						help='Use signed decimal (not unsigned hex) for small addresses')
	parser.add_argument('-a', '--allkeys', action='store_true',
						help='Include performance metrics measured to compute others')
	parser.add_argument('-p', '--permissive', action='store_true',
						help='Ignore some state-related issues when they occur')
	args = parser.parse_args()
	line_iter = iter(args.infile.readline,  b'')
	# Prepare stateful data structures
	time_info = None
	gpr_wb_info = defaultdict(deque)
	fpr_wb_info = defaultdict(deque)
	fseq_info = {
		'curr_sec': 0,
		'fpss_pcs': deque(),
		'fseq_pcs': deque(),
		'cfg_buf': deque(),
		'curr_cfg': None
	}
	perf_metrics = [defaultdict(int)]  # all values initially 0, also 'start' time of measurement 0
	perf_metrics[0]['start'] = None
	# Parse input line by line
	for line in line_iter:
		if line:
			ann_insn, time_info, empty = annotate_insn(line, gpr_wb_info, fpr_wb_info, fseq_info, perf_metrics,
				False, time_info, args.offl, not args.saddr, args.permissive)
			if perf_metrics[0]['start'] is None:
				perf_metrics[0]['start'] = time_info[1]
			# Create a new section after every 'nop' instruction
			if 'cycle' in ann_insn:
				perf_metrics[-1]['end'] = time_info[1]
				perf_metrics.append(defaultdict(int))
				perf_metrics[-1]['start'] = time_info[1]
			if not empty:
				print(ann_insn)
		else:
			break  # Nothing more in pipe, EOF
	perf_metrics[-1]['end'] = time_info[1]
	# Compute metrics
	eval_perf_metrics(perf_metrics)
	# Emit metrics
	print('\n## Performance metrics')
	for idx in range(len(perf_metrics)):
		print('\n' + fmt_perf_metrics(perf_metrics, idx, not args.allkeys))
	# Check for any loose ends and warn before exiting
	seq_isns = len(fseq_info['fseq_pcs']) + len(fseq_info['cfg_buf'])
	unseq_left = len(fseq_info['fpss_pcs']) - len(fseq_info['fseq_pcs'])
	fseq_cfg = fseq_info['curr_cfg']
	warn_trip = False
	for fpr, que in fpr_wb_info.items():
		if len(que) != 0:
			warn_trip = True
			sys.stderr.write(EXTRA_WB_WARN.format(len(que), REG_ABI_NAMES_F[fpr]) + '\n')
	for gpr, que in fpr_wb_info.items():
		if len(que) != 0:
			warn_trip = True
			sys.stderr.write(EXTRA_WB_WARN.format(len(que), REG_ABI_NAMES_I[gpr]) + '\n')
	if seq_isns:
		warn_trip = True
		sys.stderr.write('WARNING: {} Sequencer instructions were not issued.\n'.format(seq_isns))
	if unseq_left:
		warn_trip = True
		sys.stderr.write('WARNING: {} unsequenced FPSS instructions were not issued.\n'.format(unseq_left))
	if fseq_cfg is not None:
		warn_trip = True
		pc_str = fseq_cfg['fseq_pc']
		sys.stderr.write('WARNING: Not all FPSS instructions from sequence {} were issued.\n'.format(pc_str))
	if warn_trip:
		sys.stderr.write(GENERAL_WARN)
	return 0


if __name__ == '__main__':
	sys.exit(main())
