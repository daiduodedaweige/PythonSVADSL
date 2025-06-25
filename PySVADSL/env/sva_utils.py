from external.PythonSVADSL.PySVADSL.env.sva_dsl import _value_, _signal_widths
import re

def dump_verilog_exprs(filename="signals.log"):
    with open(filename, "w") as f:
        for expr in sorted(_value_):
            f.write(expr + "\n")

def emit_module_ports(module_name, clk_name):
    port_lines = [f"module {module_name}(", f"    input logic {clk_name},", "    input logic reset,"]
    for sig in sorted(_value_):
        width = _signal_widths.get(sig, "")
        if width:
            port_lines.append(f"    input logic {width} {sig},")
        else:
            port_lines.append(f"    input logic {sig},")
    port_lines[-1] = port_lines[-1].rstrip(",")  # 移除最后一个逗号
    port_lines.append(");")
    return "\n".join(port_lines)

def sanitize_sva_expr(sva_body):
    # 替换所有合法路径名（形如 a.b.c）为 a_b_c，忽略函数名如 $rose(x.y)
    return re.sub(r'(?<!\$)(\b[a-zA-Z_]\w*(?:\.[a-zA-Z_]\w*)+)', lambda m: m.group(0).replace('.', '_'), sva_body)

def build_full_module_code(module_name, include, clk_name, sva_body):
    sva_port = emit_module_ports(module_name, clk_name)
    finalsva = include + f"{sva_port}\n\n{sva_body}\n\nendmodule\n"
    finalsva = sanitize_sva_expr(finalsva)
    return finalsva

def save_to_file(filename, content):
    with open(filename, "w") as f:
        f.write(content)

def include(include_filename):
    return f'`include "{include_filename}"\n'

def generate_bind_statement(target_module="DataCM", checker_module="DataCtrlEntryStateChecker", instance_name="u_chk"):
    bind_lines = [f"bind {target_module} {checker_module} {instance_name} ("]
    bind_lines.append("    .clock(clock),")
    bind_lines.append("    .reset(reset),")
    
    for sig in sorted(_value_):
        port_name = sig.replace(".", "_")  # 转换成合法端口名
        bind_lines.append(f"    .{port_name}({sig}),")
    
    # 移除最后一个逗号
    bind_lines[-1] = bind_lines[-1].rstrip(",")
    bind_lines.append(");")
    
    return "\n".join(bind_lines)
