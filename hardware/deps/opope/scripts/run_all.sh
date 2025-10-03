#!/bin/bash

# === Setup ===
FIFOS=(0 4)
READOUT=(0 1) # Mux = 1, Sys = 0; You can choose among (0),(1),(0 1)
HEIGHTS=(4 8 16)
ACCS=(16 32)

# Active flags
FIFO_0__H_04__ACC_16_active=1
FIFO_0__H_08__ACC_16_active=1
FIFO_0__H_16__ACC_16_active=1
FIFO_4__H_04__ACC_16_active=0
FIFO_4__H_08__ACC_16_active=1
FIFO_4__H_16__ACC_16_active=1
FIFO_0__H_04__ACC_32_active=1
FIFO_0__H_08__ACC_32_active=1
FIFO_0__H_16__ACC_32_active=1
FIFO_4__H_04__ACC_32_active=0
FIFO_4__H_08__ACC_32_active=1
FIFO_4__H_16__ACC_32_active=1

# === Functions ===
extract_info(){
  transcript="target/sim/vsim/transcript"
  tmp_log="logs/tmp.log"
  
  grep -E '^[[:space:]]*#[[:space:]]*\[SAVE\] -' "${transcript}" > "${tmp_log}" || true

  # parse the "[Data]" line
  data_line=$(grep -m1 -E '^\s*#\s*\[SAVE\] - \[Data\]:' "$tmp_log" || echo "")
  cycles=$(echo "$data_line" | sed -n 's/.*Cycles: \([0-9]\+\).*/\1/p')
  memreq=$(echo "$data_line" | sed -n 's/.*TCDM Request count: \([0-9]\+\).*/\1/p')

  # detect success/fail
  if grep -q '^\s*#\s*\[SAVE\] - \[TB\] - Success!' "${tmp_log}"; then
    (( success_count++ ))
    status="${Green}${CheckMark} SUCCESS${EndColor}"
  else
    (( fail_count++ ))
    status="${Red}${CrossMark} FAIL${EndColor}"
  fi 
  rm -rf $tmp_log
}
run_config() {
  local FIFO=$1
  local HEIGHT=$2
  local ACC=$3
  local FPFORMAT=$4
  local FPFMTCONFIG=$5
  local LOGFILE="$MAKE_PATH/logs/performance_${FIFO}_${HEIGHT}_${ACC}.log"
  local fp_combos
  local sizes
  if   [ "$ACC" -eq 16 ]; then fp_combos=("FP8FP16" "FP16")
  elif [ "$ACC" -eq 32 ]; then fp_combos=("FP16FP32" "FP32")
  fi

  if   [ "$HEIGHT" -eq 4  ]; then sizes=(16 32 64 96)
  elif [ "$HEIGHT" -eq 8  ]; then sizes=(16 32 64 96)
  elif [ "$HEIGHT" -eq 16 ]; then sizes=(32 64 96)
  fi
  echo "=== Running config: FIFO=$FIFO, HEIGHT=$HEIGHT, ACC=$ACC ==="
  echo 'start' &> "$LOGFILE"
  date '+%Y-%m-%d %H:%M:%S' &>> "$LOGFILE"

  # Update RTL files
  sed -i "14s|.*|  parameter int unsigned            ARRAY_HEIGHT = $HEIGHT;|" "$MAKE_PATH/rtl/opope_pkg.sv"
  sed -i "15s|.*|  parameter fpnew_pkg::fp_format_e  FPFORMAT     = fpnew_pkg::$FPFORMAT;|" "$MAKE_PATH/rtl/opope_pkg.sv"
  sed -i "29s|.*|  parameter fpnew_pkg::fmt_logic_t  FpFmtConfig  = $FPFMTCONFIG;|" "$MAKE_PATH/rtl/opope_pkg.sv"
  sed -i "41s|.*|  localparam int unsigned X_FIFO_DEPTH = $FIFO;|" "$MAKE_PATH/rtl/opope_buffers.sv"
  sed -i "42s|.*|  localparam int unsigned W_FIFO_DEPTH = $FIFO;|" "$MAKE_PATH/rtl/opope_buffers.sv"
  sed -i "43s|.*|  localparam int unsigned Y_FIFO_DEPTH = $FIFO;|" "$MAKE_PATH/rtl/opope_buffers.sv"
  sed -i "44s|.*|  localparam int unsigned Z_FIFO_DEPTH = $FIFO;|" "$MAKE_PATH/rtl/opope_buffers.sv"


  for mux in "${READOUT[@]}"; do
    if [ "$mux" -eq 1 ]; then sed -i "21s|.*| localparam int unsigned  MUX_SH_n    = 1|" "$MAKE_PATH/rtl/opope_engine.sv"
    else                      sed -i "21s|.*| localparam int unsigned  MUX_SH_n    = 0|" "$MAKE_PATH/rtl/opope_engine.sv"
    fi

    for fp in "${fp_combos[@]}"; do
      for size in "${sizes[@]}"; do
        echo "=== Simulation: $size x $size x $size $fp ==="
        make golden OP=gemm M=$size N=$size K=$size fp_fmt=$fp &> /dev/null
        make sim target=vsim gui=0 &>> "$LOGFILE"
        extract_info
        ((total_count++))
        if   [ -n "$cycles" ] && [ "$cycles" -ne 0 ] && { [ "$fp" = "FP8FP16" ] || [ "$fp" = "FP16FP32" ]; }; then
          eff=$(echo "scale=2; $size * $size * $size * 50 / ($HEIGHT * $HEIGHT * $cycles)" | bc -l)
        elif [ -n "$cycles" ] && [ "$cycles" -ne 0 ] && { [ "$fp" = "FP16" ] || [ "$fp" = "FP32" ]; }; then
          eff=$(echo "scale=2; $size * $size * $size * 100 / ($HEIGHT * $HEIGHT * $cycles)" | bc -l)
        else
          eff="NA"
        fi
        SUMMARY_LINES+=(
          "$(printf "%2s x %2s   %-10s %3d %3d %3d   %2d     %d   %-8s  %7s  %6s   %7s" \
          "$HEIGHT" "$HEIGHT" "$fp" "$size" "$size" "$size" "$FIFO" "$mux" "$status" "${cycles:--}" "${memreq:--}" "$eff")"
        )
      done
    done
  done
}

# === Run ===
set -u
set -o pipefail
# ─── Set directories ────────────────────────────────────────────────────────────
CURRENT_DIR=$(pwd)
SCRIPT_PATH="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
MAKE_PATH=$SCRIPT_PATH/..
cd $MAKE_PATH

# ─── Colours & symbols ──────────────────────────────────────────────────────────
Red="\e[31m"
Green="\e[32m"
Yellow="\e[33m"
EndColor="\e[0m"
CheckMark="✅"
CrossMark="❌"

# ─── Counters & storage ─────────────────────────────────────────────────────────
total_count=0
success_count=0
fail_count=0
declare -a SUMMARY_LINES
# Header: Target, M, N, K, FIFO, MUX, Status,   Cycles,    MemReq
SUMMARY_LINES=(" Engine    Target     M   N   K   FIFO   MUX   Status       Cycles   MemReq   Util ")
SUMMARY_LINES+=("──────────────────────────────────────────────────────────────────────────────────")
# ─── Simulations ────────────────────────────────────────────────────────────────
sed -i '70s/.*/  -do "run 2 ms; quit -f;"/' "$MAKE_PATH/target/sim/vsim/vsim.mk"
sed -i '527s/.*/    int ENABLE_ENGINE_OUTPUT  = 0;/' "$MAKE_PATH/target/sim/src/opope_tb.sv"
sed -i '21s/.*/ localparam int unsigned  MUX_SH_n    = 1/' "$MAKE_PATH/rtl/opope_engine.sv"
for FIFO in "${FIFOS[@]}"; do
  for HEIGHT in "${HEIGHTS[@]}"; do
    for ACC in "${ACCS[@]}"; do
      flag="FIFO_${FIFO}__H_$(printf '%02d' $HEIGHT)__ACC_${ACC}_active"

      if [ "$ACC" -eq 16 ]; then
        FPFORMAT="FP16"
        FPFMTCONFIG="6'b001100"
      elif [ "$ACC" -eq 32 ]; then
        FPFORMAT="FP32"
        FPFMTCONFIG="6'b101000"
      fi

      if [ "${!flag}" -eq 1 ]; then
        run_config "$FIFO" "$HEIGHT" "$ACC" "$FPFORMAT" "$FPFMTCONFIG"
      fi
    done
  done
done
# ─── Print summary ──────────────────────────────────────────────────────────────
echo -e "\n${Yellow}========= Final Report =========${EndColor}"
for line in "${SUMMARY_LINES[@]}"; do
  echo -e "$line"
done
echo -e "\nTotals:   runs=${total_count}, success=${success_count}, fail=${fail_count}"
echo -e "Error rate: $(printf "%.2f%%" "$(echo "100 * $fail_count / $total_count" | bc -l)")"

### DEFAULT CONFIGURATION
sed -i '70s|.*|  -do "run -a;"|' "$MAKE_PATH/target/sim/vsim/vsim.mk"
sed -i '527s/.*/    int ENABLE_ENGINE_OUTPUT  = 0;/' "$MAKE_PATH/target/sim/src/opope_tb.sv"
sed -i '14s/.*/  parameter int unsigned            ARRAY_HEIGHT = 8;/' "$MAKE_PATH/rtl/opope_pkg.sv"
sed -i '15s/.*/  parameter fpnew_pkg::fp_format_e  FPFORMAT     = fpnew_pkg::FP16;/' "$MAKE_PATH/rtl/opope_pkg.sv"
sed -i "29s|.*|  parameter fpnew_pkg::fmt_logic_t  FpFmtConfig  = 6'b001100;|" "$MAKE_PATH/rtl/opope_pkg.sv"
sed -i '41s/.*/  localparam int unsigned X_FIFO_DEPTH = 0;/' "$MAKE_PATH/rtl/opope_buffers.sv"
sed -i '42s/.*/  localparam int unsigned W_FIFO_DEPTH = 0;/' "$MAKE_PATH/rtl/opope_buffers.sv"
sed -i '43s/.*/  localparam int unsigned Y_FIFO_DEPTH = 0;/' "$MAKE_PATH/rtl/opope_buffers.sv"
sed -i '44s/.*/  localparam int unsigned Z_FIFO_DEPTH = 0;/' "$MAKE_PATH/rtl/opope_buffers.sv"
sed -i '21s/.*/ localparam int unsigned  MUX_SH_n    = 1/' "$MAKE_PATH/rtl/opope_engine.sv"
cd $CURRENT_DIR
echo "=== All done ==="