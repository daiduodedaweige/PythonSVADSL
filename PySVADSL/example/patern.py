import sys
sys.path.append("/nfs/home/weijing/workspace/generateSVA")
from PySVADSL.env.sva_dsl import SVAExpr, generate_macro_state_transfer
from PySVADSL.env.sva_utils import build_full_module_code, dump_verilog_exprs, save_to_file, include
from enum import IntEnum
pkg = include("assert_macros.svh")
sva_code = ""
module = "DataCtrlEntryStateChecker"
clk = "clock"

# state


# signal


# assert



# generate
full_code = build_full_module_code(module, pkg, clk, sva_code)
save_to_file("assertions.sv", full_code)
dump_verilog_exprs()
print("✅ assertions.sv 已生成")
