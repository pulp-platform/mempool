
import re, os, sys
import progressbar

# line format:
# 101000 82      M         0x00001000 csrr    a0, mhartid     #; comment
# time   cycle   priv_lvl  pc         insn

# regex matches to groups
# 0 -> time
# 1 -> cycle
# 2 -> privilege level
# 3 -> pc (hex with 0x prefix)
# 4 -> instruction
# 5 -> args
LINE_REGEX = r' *(\d+) +(\d+) +([3M1S0U]?) *(0x[0-9a-f]+) ([.\w]+) +(.+)#'

# regex matches a line of instruction retired by the accelerator
# 2 -> privilege level
# 3 -> pc (hex with 0x prefix)
# 4 -> instruction
# 5 -> args
ACC_LINE_REGEX = r' +([3M1S0U]?) *(0x[0-9a-f]+) ([.\w]+) +(.+)#'

re_line = re.compile(LINE_REGEX)
re_acc_line = re.compile(ACC_LINE_REGEX)
# re_line = re.compile(r'(\d+)')

buf = []

def flush(buf, hartid):
  # get function names
  pcs = [x[3] for x in buf]
  a2ls = os.popen(f'addr2line -e {elf} -f -a -i {pcs}').read().split('\n')[:-1]
  
  for i in range(len(buf)-1):
    (time, cyc, priv, pc, instr, args) = buf.pop(0)

    next_time = 1.0e-3*int(buf[0][0])

    time = 1.0e-3*int(time)
    # print(f'time "{time}", cyc "{cyc}", priv "{priv}", pc "{pc}", instr "{instr}", args "{args}"', file=sys.stderr)
    
    [pc, func, file] = a2ls.pop(0), a2ls.pop(0), a2ls.pop(0)

    # check for more output of a2l
    inlined = ''
    while not a2ls[0].startswith('0x'):
      inlined += '(inlined by) ' +  a2ls.pop(0)
    # print(f'pc "{pc}", func "{func}", file "{file}"')

    # assemble values for json
    label = instr
    cat   = instr
    start_time = time
    duration = next_time - time
    # print(f'"{label}" time {time} next: {next_time} duration: {duration}', file=sys.stderr)
    pid = elf+':hartid'+str(hartid)
    funcname = func

    last_time = time

    # args
    arg_pc = pc
    arg_instr = instr
    arg_args = args
    arg_cycles = cyc
    arg_coords = file
    arg_inlined = inlined

    print((
          f'{{"name": "{label}", "cat": "{cat}", "ph": "X", "ts": {start_time}, '
          f'"dur": {duration}, "pid": "{pid}", "tid": "{funcname}", '
          f'"args": {{'
          f'  "pc": "{arg_pc}", "instr": "{arg_instr} {arg_args}", '
          f'  "time": "{arg_cycles}", "Origin": "{arg_coords}", "inline": "{inlined}"'
          f'}}}},'))

last_time = last_cyc = 0
def parse_line(line, hartid):
  global last_time, last_cyc
  # print(line)
  match = re_line.match(line)
  if match:
    (time, cyc, priv, pc, instr, args) = tuple([match.group(i+1).strip() for i in range(re_line.groups)])
  # print(match)

  if not match:
    # match accelerator line with same timestamp as before
    match = re_acc_line.match(line)
    if match:
      (priv, pc, instr, args) = tuple([match.group(i+1).strip() for i in range(re_acc_line.groups)])
      # use time,cyc from last line
      time, cyc = last_time,last_cyc
    else:
      return 1

  # print(line)
  buf.append((time, cyc, priv, pc, instr, args))
  last_time, last_cyc = time,cyc

  if len(buf) > 10:
    flush(buf, hartid)
  return 0

fails = lines = 0


if len(sys.argv) < 3:
  print('Usage: tracevis.py <elf> <trace> [trace ...]', file=sys.stderr)
  exit(-1)

elf = sys.argv[1]
traces = sys.argv[2:]

print('elf',elf, file=sys.stderr)
print('traces',traces, file=sys.stderr)

# json header
print('{"traceEvents": [')

for filename in traces:
  hartid = 0
  parsed_nums = re.findall(r'\d+', filename)
  hartid = int(parsed_nums[-1]) if len(parsed_nums) else hartid+1

  print(f'parsing hartid {hartid} with trace {filename}', file=sys.stderr)
  tot_lines = len(open(filename).readlines())
  with open(filename) as f:
    for lino, line in progressbar.progressbar(enumerate(f.readlines()), max_value=tot_lines):
      fails += parse_line(line, hartid)
      lines += 1
      if lino > 30000:
        break
    flush(buf, hartid)
    print(f'parsed {lines-fails} of {lines} lines', file=sys.stderr)

# json footer
print('{}]}')