# 全局变量
_value_ = set()
_signal_widths = {}

class SVAExpr(str):
    def __new__(cls, expr_str, is_raw=True, width=None):
        obj = super().__new__(cls, expr_str)
        obj._is_raw = is_raw
        obj._width = width
        if is_raw:
            _value_.add(expr_str)
            if isinstance(width, int) and width > 1:
                _signal_widths[expr_str] = f"[{width - 1}:0]"
            else:
                _signal_widths[expr_str] = ""  # 1位或未指定
        return obj
    def __and__(self, other): return SVAExpr(f"({self}) && ({other})", is_raw=False)
    def __or__(self, other): return SVAExpr(f"({self}) || ({other})", is_raw=False)
    def __invert__(self): return SVAExpr(f"!({self})", is_raw=False)
    def __rshift__(self, other): return SVAExpr(f"({self}) |-> ({other})", is_raw=False)
    def __matmul__(self, other): return SVAExpr(f"({self}) ## ({other})", is_raw=False)
    def seq(self, delay): return SVAExpr(f"({self}) ##{delay}", is_raw=False)
    def __eq__(self, other):
        if isinstance(other, int): return SVAExpr(f"{self}=='h{other:X}", is_raw=False)
        return SVAExpr(f"{self}=={other}", is_raw=False)




def generate_macro_state_transfer(name: str, clock: str, start_cond: str, end_cond: str) -> str:
    return f"""    `state_transfer(
        {name},
        {clock},
        ({start_cond}),
        ({end_cond})
    );"""

def generate_macro_assert(name: str, clock: str, start_cond: str, end_cond: str) -> str:
    return f"""    `state_transfer(
        {name},
        {clock},
        ({start_cond}),
        ({end_cond})
    );"""