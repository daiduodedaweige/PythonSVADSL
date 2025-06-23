import re
# 全局变量
_value_ = set()
_signal_widths = {}

class SVAExpr(str):
    def __new__(cls, expr_str, is_raw=True, width=1):
        obj = super().__new__(cls, expr_str)
        obj._is_raw = is_raw
        obj._width = width

        if is_raw:
            if cls._is_valid_signal(expr_str):
                base_name = cls._extract_base_name(expr_str)
                _value_.add(base_name)
                if isinstance(width, int) and width > 1:
                    _signal_widths[base_name] = f"[{width - 1}:0]"
                else:
                    _signal_widths[base_name] = ""
        return obj
    @staticmethod
    def _extract_base_name(expr_str):
        return re.sub(r'\[.*?\]', '', expr_str.strip())
    @staticmethod
    def _is_valid_signal(expr_str):
        expr_str = expr_str.strip()
        # 排除字面常量，如 23'hEA5F、4'b1010、16'd5
        if re.match(r"^\d+'\w[a-fA-F0-9_]+$", expr_str):
            return False
        # 排除索引信号，如 cnt[3] 或 io.cnt[7:0]
        if "[" in expr_str and "]" in expr_str:
            return False
        return True
    def __and__(self, other): return SVAExpr(f"({self}) && ({other})", is_raw=False)
    def __or__(self, other): return SVAExpr(f"({self}) || ({other})", is_raw=False)
    def __xor__(self, other): return SVAExpr(f"({self}) ^ ({other})", is_raw=False)
    def __invert__(self): return SVAExpr(f"!({self})", is_raw=False)
    def __rshift__(self, other): return SVAExpr(f"({self}) |-> ({other})", is_raw=False)
    def __matmul__(self, other): return SVAExpr(f"({self}) ## ({other})", is_raw=False)
    def seq(self, delay): return SVAExpr(f"({self}) ##{delay}", is_raw=False)
    def __add__(self, other):
        return SVAExpr(f"{self} + {other}", is_raw=False)
    def __sub__(self, other):
        return SVAExpr(f"{self} - {other}", is_raw=False)
    def __eq__(self, other):
        if isinstance(other, int): return SVAExpr(f"{self} == {self._width}'h{other:X}", is_raw=False)
        return SVAExpr(f"{self} == {other}", is_raw=False)
    def __ne__(self, other):
        if isinstance(other, int): return SVAExpr(f"{self} != {self._width}'h{other:X}", is_raw=False)
        return SVAExpr(f"{self} != {other}", is_raw=False)
    def __lt__(self, other):  # self < other
        if isinstance(other, int): return SVAExpr(f"{self} < {self._width}'h{other:X}", is_raw=False)
        return SVAExpr(f"{self} < {other}", is_raw=False)
    def __le__(self, other):  # self <= other
        if isinstance(other, int): return SVAExpr(f"{self} <= {self._width}'h{other:X}", is_raw=False)
        return SVAExpr(f"{self} <= {other}", is_raw=False)
    def __gt__(self, other):  # self > other
        if isinstance(other, int): return SVAExpr(f"{self} > {self._width}'h{other:X}", is_raw=False)
        return SVAExpr(f"{self} > {other}", is_raw=False)
    def __ge__(self, other):  # self >= other
        if isinstance(other, int): return SVAExpr(f"{self} >= {self._width}'h{other:X}", is_raw=False)
        return SVAExpr(f"{self} >= {other}", is_raw=False)
    def not_expr(self): return SVAExpr(f"!{self}", is_raw=False)
    def rose(self): return SVAExpr(f"$rose({self})", is_raw=False)
    def fell(self): return SVAExpr(f"$fell({self})", is_raw=False)
    def past(self): return SVAExpr(f"$past({self})", is_raw=False)
    def __getitem__(self, key):
        if isinstance(key, int):
            return SVAExpr(f"{self}[{key}]")
        elif isinstance(key, slice):
            msb = key.start
            lsb = key.stop
            if msb is None or lsb is None:
                raise ValueError("Slice must specify both start and stop.")
            return SVAExpr(f"{self}[{msb}:{lsb}]")
        else:
            raise TypeError("Index must be int or slice.")


def state_transfer(name: str, clock: str, start_cond: str, end_cond: str) -> str:
    return f"""    `state_transfer(
        {name},
        {clock},
        ({start_cond}),
        ({end_cond})
    );\n"""

def assert_Imp(name: str, clock: str, start_cond: str, end_cond: str) -> str:
    return f"""    `assert_with_result(
        {name},
        {clock},
        ({start_cond}),
        ({end_cond})
    );\n"""

def assert_notImp(name: str, clock: str, end_cond: str) -> str:
    return f"""    `assert_without_result(
        {name},
        {clock},
        ({end_cond})
    );\n"""

def assume_Imp(name: str, clock: str, start_cond: str, end_cond: str) -> str:
    return f"""    `assume_with_result(
        {name},
        {clock},
        ({start_cond}),
        ({end_cond})
    );\n"""

def assume_notImp(name: str, clock: str, end_cond: str) -> str:
    return f"""    `assume_without_result(
        {name},
        {clock},
        ({end_cond})
    );\n"""

def cover(name: str, clock: str, end_cond: str) -> str:
    return f"""    `cover(
        {name},
        {clock},
        ({end_cond})
    );\n"""