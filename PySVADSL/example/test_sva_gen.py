from sva_dsl import SVAExpr, generate_macro_state_transfer
from env.sva_utils import build_full_module_code, dump_verilog_exprs, save_to_file
sva_code = ""
module = "cocotb"

clk = "clock"
state = SVAExpr("stateReg_value")
alloc_fire = SVAExpr("io_alloc_valid") & SVAExpr("io_alloc_ready")
condition = (state == 0) & alloc_fire
result = SVAExpr("io_fthInst_valid")
ccnnk = SVAExpr("io_sdfsd")

# 生成断言代码

sva_code += generate_macro_state_transfer("assert_from_FREE_to_FSTTASK", clk, condition, result)

# 输出模块代码
full_code = build_full_module_code(module, clk, sva_code)

# 写入文件
save_to_file("assertions.sv", full_code)
dump_verilog_exprs()

print("✅ assertions.sv 已生成")
