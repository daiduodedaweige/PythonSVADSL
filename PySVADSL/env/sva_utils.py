from PySVADSL.env.sva_dsl import _value_, _signal_widths

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

def build_full_module_code(module_name, include, clk_name, sva_body):
    sva_port = emit_module_ports(module_name, clk_name)
    return include + f"{sva_port}\n\n{sva_body}\n\nendmodule\n"

def save_to_file(filename, content):
    with open(filename, "w") as f:
        f.write(content)

def include(include_filename):
    return f'`include "{include_filename}"\n'
