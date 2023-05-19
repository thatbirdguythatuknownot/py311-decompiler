from collections import defaultdict
from dis import findlinestarts
from functools import wraps
from itertools import zip_longest
from opcode import (_inline_cache_entries as ICE, HAVE_ARGUMENT,
                    _nb_ops as B_ops, hascompare, hasconst, hasfree,
                    hasjrel as hasj, haslocal, hasname, opmap, opname,
                    stack_effect)
from struct import iter_unpack
from types import CodeType, FunctionType, MemberDescriptorType
from typing import Any, Generator, Optional, Self

# Constant/initial variables

globals().update(opmap)

B_ops: list[str] = [x[1] for x in B_ops]
hascompare: set[int] = {*hascompare}
hasconst: set[int] = {*hasconst}
hasfree: set[int] = {*hasfree}
hasj: set[int] = {*hasj} - {LOAD_GLOBAL}
hasjback: set[int] = {x for x in hasj if 'BACKWARD' in opname[x]}
hasjbool: set[int] = {JUMP_IF_FALSE_OR_POP, JUMP_IF_TRUE_OR_POP,
                      POP_JUMP_FORWARD_IF_FALSE, POP_JUMP_FORWARD_IF_TRUE}
haslocal: set[int] = {*haslocal}
hasname: set[int] = {*hasname}
U_ops: dict[int, str] = {UNARY_POSITIVE: '+', UNARY_NEGATIVE: '-',
                         UNARY_INVERT: '~', UNARY_NOT: 'not'}
C_ops = "<", "<=", "==", "!=", ">", ">="
cache_T: tuple[int, int] = CACHE, 0
name_stores: dict[int, int] = {STORE_NAME: 0, STORE_GLOBAL: 1,
                               STORE_FAST: 2, STORE_DEREF: 3}
name_loads: dict[int, int] = {LOAD_NAME: 0, LOAD_GLOBAL: 1,
                              LOAD_FAST: 2, LOAD_CLOSURE: 2,
                              LOAD_DEREF: 3, LOAD_CLASSDEREF: 3}
P_NAMED_EXPR = 0
P_TUPLE = P_NAMED_EXPR + 1
P_TEST = P_TUPLE + 1
P_OR = P_TEST + 1
P_AND = P_OR + 1
P_NOT = P_AND + 1
P_CMP = P_NOT + 1
P_BOR = P_EXPR = P_CMP + 1
P_BXOR = P_BOR + 1
P_BAND = P_BXOR + 1
P_SHIFT = P_BAND + 1
P_ARITH = P_SHIFT + 1
P_TERM = P_ARITH + 1
P_FACTOR = P_TERM + 1
P_POWER = P_FACTOR + 1
P_AWAIT = P_POWER + 1
P_ATOM = P_AWAIT + 1
B_ops_prec: dict[str, int] = {'+': P_ARITH, '&': P_BAND, '//': P_TERM,
                              '<<': P_SHIFT, '@': P_TERM, '*': P_TERM,
                              '%': P_TERM, '|': P_BOR, '**': P_POWER,
                              '>>': P_SHIFT, '-': P_ARITH, '/': P_TERM,
                              '^': P_BXOR}
U_ops_prec: dict[str, int] = {'+': P_FACTOR, '-': P_FACTOR, '~': P_FACTOR,
                              'not': P_NOT}

# Utility functions

def list_add(list_, obj):
    try:
        return list_.index(obj)
    except ValueError:
        res = len(list_)
        list_.append(obj)
        return res

def write_varint(val, append):
    while val > 63:
        append(64 + (val & 63))
        val >>= 6
    append(val)

def write_svarint(val, append):
    return (write_varint(-2*val + 1, append)
            if val < 0 else
            write_varint(2*val, append))

def write_loc(start_line, end_line, start_col, end_col,
              delta, isize_m1, append):
    if start_line is not None:
        if start_col is not None is not end_col:
            if end_line == start_line:
                if (not delta and start_col < 80 and end_col - start_col < 16
                        and end_col >= start_col):
                    # 120 == 0b1111000
                    # `& 120` gets the needed upper 4 bits
                    # 128 (bit 7) is used to signify an entry start
                    # PY_CODE_LOCATION_INFO_SHORT0 = 0; this is not added
                    # this covers all codes in `range(10)`
                    append(128 + (start_col & 120) + isize_m1)
                    append(((start_col & 7) << 4) + (end_col - start_col))
                    return
                elif 0 <= delta < 3 and start_col < 128 > end_col:
                    # 8*x == x << 3
                    # PY_CODE_LOCATION_INFO_ONE_LINE0 = 10
                    # 208 == 128 | (10 << 3)
                    # this covers all codes in `range(10, 13)`
                    append(208 + 8*delta + isize_m1)
                    append(start_col)
                    append(end_col)
                    return
        elif end_line == start_line or end_line is None:
            # PY_CODE_LOCATION_INFO_NO_COLUMNS = 13
            # 232 == 128 | (13 << 3)
            append(232 + isize_m1)
            write_svarint(delta, append)
            return
        # PY_CODE_LOCATION_INFO_LONG = 14
        # 240 == 128 | (14 << 3)
        append(240 + isize_m1)
        write_svarint(delta, append)
        write_varint(end_line - start_line, append)
        write_varint(start_col + 1, append)
        write_varint(end_col + 1, append)
        return
    # PY_CODE_LOCATION_INFO_NONE = 15
    # 248 == 128 | (15 << 3)
    append(248 + isize_m1)

# all types here are defined later
def named_expr_deco(func):
    @wraps(func)
    def wrapper(self, *args, **kwargs):
        if expr := func(*args, **kwargs):
            if ((instr := self.peek()).opcode is COPY
                    and instr.oparg_or_arg == 1
                    and (instr := self.peek()).opcode in name_stores):
                self.skip(2)
                return NamedExpr(expr, instr.oparg_or_arg,
                                 op_kind=name_stores[instr.opcode])
        return expr
    return wrapper

def n_extargs(oparg):
    return (0xFFFFFF < oparg) + (0xFFFF < oparg) + (0xFF < oparg)

def tag(obj, string):
    obj.tags.add(string)
    return obj

# implicitly passes if the tag does not exist
def untag(obj, string):
    obj.tags.discard(string)
    return obj

# Main classes

class Instr:
    """
    Instruction class 
    """
    
    __slots__ = ('opcode', 'oparg_or_arg', 'line_pos', 'col_pos', 'jump_id',
                 'target_id', 'has_real_arg', 'extra_info')
    
    opcode: int
    line_pos: tuple[int | None, int | None]
    col_pos: tuple[int | None, int | None]
    jump_id: int | None
    target_id: int
    has_real_arg: bool
    extra_info: dict # may show up in `.__str__()`, but by default does not
    
    def __init__(self: Self, opcode: int, oparg_or_arg,
                 line_pos: tuple[int, int] | None,
                 col_pos: tuple[int, int] | None,
                 jump_id: int | None = None,
                 target_id: int | None = None,
                 has_real_arg: bool = False,
                 **extra_info) -> None:
        self.opcode = opcode
        self.oparg_or_arg = oparg_or_arg
        self.line_pos = line_pos
        self.col_pos = col_pos
        self.jump_id = jump_id
        self.target_id = target_id
        self.has_real_arg = has_real_arg
        self.extra_info = extra_info
    
    def __eq__(self: Self, other) -> bool:
        return (
            isinstance(other, Instr)
            and self.opcode is other.opcode
            and self.oparg_or_arg == other.oparg_or_arg
            and self.jump_id == other.jump_id
            and self.target_id == other.target_id
            and self.has_real_arg is other.has_real_arg
            and self.extra_info == other.extra_info
        )
    
    def __hash__(self: Self) -> int:
        res = ((hash(self.opcode) &
                   (hash(self.oparg_or_arg) ^ self.has_real_arg))
              ^ hash(self.line_pos) ^ hash(self.col_pos) ^ hash(self.jump_id))
        for instr in self.targeters:
            if instr is not self:
                res ^= hash(instr)
        return res
    
    def __repr__(self: Self) -> str:
        return (f"Instr(opcode={opname[self.opcode]}, "
                      f"oparg_or_arg={self.oparg_or_arg!r}, "
                      f"start_pos={self.line_pos!r}, "
                      f"end_pos={self.col_pos!r}, jump_id={self.jump_id}, "
                      f"target_id={self.target_id}, "
                      f"has_real_arg={self.has_real_arg!r}, "
                      f"extra_info={self.extra_info!r})")
    
    def __str__(self: Self) -> str:
        line_pos = self.line_pos
        col_pos = self.col_pos
        pos_s = "[L({})C({}) -> L({})C({})]".format(line_pos[0], col_pos[0],
                                                    line_pos[1], col_pos[1])
        if self.has_real_arg:
            if self.opcode is LOAD_GLOBAL and self.extra_info['loads_null']:
                arg_s = f" {{NULL, {self.oparg_or_arg!r}}}"
            else:
                arg_s = f" {{{self.oparg_or_arg!r}}}"
        elif self.opcode < HAVE_ARGUMENT:
            arg_s = ""
        elif self.opcode is IS_OP:
            arg_s = f" [is{' not' * self.oparg_or_arg}]"
        elif self.opcode is CONTAINS_OP:
            arg_s = f" [{'not ' * self.oparg_or_arg}in]"
        else:
            arg_s = f" ({self.oparg_or_arg})"
        if self.opcode in hasj:
            arg_s = ""
            jump_s = f" |{self.jump_id}| >> "
        else:
            jump_s = ""
        if self.target_id is not None:
            jump_s += f" << |{self.target_id}|"
        return f"{pos_s:<38} {opname[self.opcode]:<30}{arg_s}{jump_s}"

class Stmt:
    __slots__ = ('__dict__', '__fmt_str__', '__args_attrs__',
                 '__kwargs_attrs__', '__defaults__', '__kwdefaults__',
                 '__start_default__', 'tags', 'extra_info')
    
    __fmt_str__: str # this is not guaranteed to exist
    __args_attrs__: tuple[str]
    __kwargs_attrs__: tuple[str]
    __defaults__: tuple
    __kwdefaults__: dict[str, Any]
    __start_default__: int
    tags: set[str]
    extra_info: dict[str, Any]
    
    def __init_subclass__(cls, **kwargs) -> None:
        super().__init_subclass__(**kwargs)
        if isinstance(cls.__args_attrs__, MemberDescriptorType):
            cls.__args_attrs__ = ('val',)
        if isinstance(cls.__kwargs_attrs__, MemberDescriptorType):
            cls.__kwargs_attrs__ = ()
        if isinstance(cls.__defaults__, MemberDescriptorType):
            cls.__defaults__ = ()
        if isinstance(cls.__kwdefaults__, MemberDescriptorType):
            cls.__kwdefaults__ = {}
        if isinstance(cls.__fmt_str__, MemberDescriptorType):
            if cls.__str__ is object.__str__:
                cls.__str__ = cls.__repr__
        cls.__start_default__ = max(
            len(cls.__args_attrs__) - len(cls.__defaults__),
            0
        )
        if hasattr(cls, '__init__') and not hasattr(cls, '__real_init__'):
            cls.__real_init__ = cls.__init__
            cls.__init__ = lambda self, *args, **kwargs: None
            if cls.__real_init__ is object.__init__:
                cls.__real_init__ = cls.__init__
    
    def __new__(cls, *args, **kwargs) -> Self:
        inst = super().__new__(cls)
        idx = 0
        for attr, val in zip(it := iter(cls.__args_attrs__), args):
            setattr(inst, attr, val)
            idx += 1
        for attr in cls.__args_attrs__:
            if attr in kwargs:
                setattr(inst, attr, kwargs[attr])
                del kwargs[attr]
                idx += 1
        delta = idx - cls.__start_default__
        if delta < 0:
            raise ValueError(
                f"unsupplied arguments: {cls.__args_attrs__[idx:]}"
            )
        for attr, val in zip(it, cls.__defaults__):
            setattr(inst, attr, val)
        kwdefaults = cls.__kwdefaults__
        for attr in cls.__kwargs_attrs__:
            if attr in kwargs:
                setattr(inst, attr, kwargs[attr])
                del kwargs[attr]
            elif attr in kwdefaults:
                setattr(inst, attr, kwdefaults[attr])
            else:
                raise ValueError(
                    f"unsupplied keyword argument: {attr}"
                )
        inst.extra_info = kwargs
        if not hasattr(inst, 'tags'):
            inst.tags = set()
        inst.__real_init__(*args, **kwargs)
        return inst
    
    def __repr__(self: Self) -> str:
        args_s = ', '.join(f"{name}={getattr(self, name)!r}"
                           for name in (
                              self.__args_attrs__ + self.__kwargs_attrs__
                           ))
        return f"{self.__class__.__name__}({args_s})"
    
    def __str__(self: Self) -> str:
        return self.__fmt_str__.format(*[
            getattr(self, name) for name in (
                self.__args_attrs__ + self.__kwargs_attrs__
            )
        ])
    
    def copy(self: Self) -> str:
        cls = type(self)
        args = [getattr(self, attr) for attr in cls.__args_attrs__]
        kwargs = {attr: getattr(self, attr) for attr in cls.__kwargs_attrs__}
        return cls(*args, **kwargs)

class Assign(Stmt):
    __args_attrs__ = ("val", "assigns")
    
    def __str__(self: Self) -> str:
        return f"{' = '.join(map(str, self.assigns))} = {self.val!s}"

class BinAssign(Stmt):
    __fmt_str__ = "{1!s} {2} {0!s}"
    __args_attrs__ = ("val", "left", "op")

class Return(Stmt):
    def __str__(self: Self) -> str:
        return f"return {self.val!s}"

class Expr(Stmt):
    pass

class ExprPrecedenced(Expr):
    __slots__ = ('precedence', 'hs_precedences', 'no_precs')
    
    precedence: int
    hs_precedences: dict[str, int]
    no_precs: set[str]
    
    __fmt_str__ = "{0!s}"
    
    val: Expr
    
    def __init_subclass__(cls, **kwargs):
        super(Expr, cls).__init_subclass__(**kwargs)
        hs_precedences = cls.hs_precedences
        if isinstance(hs_precedences, MemberDescriptorType):
            if 'hs_precedences' not in cls.__kwargs_attrs__:
                cls.__kwargs_attrs__ = \
                    ('hs_precedences',) + cls.__kwargs_attrs__
            if 'hs_precedences' not in cls.__kwdefaults__:
                cls.__kwdefaults__['hs_precedences'] = None
        if isinstance(cls.no_precs, MemberDescriptorType):
            cls.no_precs = set()
        no_precs = cls.no_precs
        if isinstance(cls.precedence, MemberDescriptorType):
            if 'precedence' not in cls.__kwargs_attrs__:
                cls.__kwargs_attrs__ = ('precedence',) + cls.__kwargs_attrs__
            if 'precedence' not in cls.__kwdefaults__:
                cls.__kwdefaults__['precedence'] = 0
        elif not isinstance(hs_precedences, MemberDescriptorType):
            precedence = cls.precedence
            for attr in cls.__args_attrs__:
                if attr not in no_precs and attr not in hs_precedences:
                    hs_precedences[attr] = precedence
    
    def __init__(self, *args,
                 precedence: int = 0,
                 hs_precedences: dict[str, int] | None = None,
                 **kwargs):
        if self.hs_precedences is None:
            if hs_precedences is not None:
                self.hs_precedences = hs_precedences
            else:
                self.hs_precedences = {}
        no_precs = self.no_precs
        precedence = self.precedence
        hs_precedences = self.hs_precedences
        for attr in self.__args_attrs__:
            if attr not in no_precs and attr not in hs_precedences:
                hs_precedences[attr] = precedence
    
    def __str__(self: Self) -> str:
        if self.__fmt_str__:
            strings_list: list[str] = []
            strings_append = strings_list.append
            hs_precedences = self.hs_precedences
            no_precs = self.no_precs
            for attr in self.__args_attrs__:
                exp = getattr(self, attr)
                if attr not in no_precs:
                    string = f"{exp!s}"
                    if exp.precedence < hs_precedences[attr]:
                        string = f"({string})"
                else:
                    string = exp
                strings_append(string)
            return self.__fmt_str__.format(*strings_list)
        return self.__repr__()

class StmtExpr(ExprPrecedenced):
    precedence = P_TUPLE

class StmtWrap(ExprPrecedenced):
    precedence = P_TEST

class Constant(ExprPrecedenced):
    precedence = P_ATOM
    
    def __str__(self: Self) -> str:
        return f"{self.val!r}"

class Name(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('val',)

class VarUnpack(ExprPrecedenced):
    precedence = P_EXPR
    
    __fmt_str__ = "*{0!s}"

# (T)uple, (L)ist, (S)et Literal
class TLSLiteral(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('vals', 'kind')
    
    __args_attrs__ = ('vals', 'kind')
    
    vals: list[Expr]
    kind: int
    
    def __str__(self: Self) -> str:
        if self.vals or self.kind != 2:
            vals_s = ', '.join(map(str, self.vals))
            if not self.kind and len(self.vals) == 1:
                vals_s += ','
            if self.kind or 'no_parens' not in self.extra_info:
                return (('({})', '[{}]', '{{{}}}')[self.kind]
                            .format(vals_s))
            return vals_s
        return '{*()}'

class DictLiteral(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('keys', 'vals')
    
    __args_attrs__ = ('keys', 'vals')
    
    keys: list[Expr | None]
    vals: list[Expr]
    
    def __str__(self: Self) -> str:
        inner_s = ""
        for key, val in zip(self.keys, self.vals):
            if key is not None:
                key_s = f"{key!s}"
                if key.precedence < P_TEST:
                    key_s = f"({key_s})"
                key_s = f"{key_s}: "
                val_s = f"{val!s}"
                if val.precedence < P_TEST:
                    val_s = f"({val_s})"
            else:
                key_s = ""
                val_s = f"{val!s}"
                if val.precedence < P_EXPR:
                    val_s = f"({val_s})"
                val_s = f"**{val_s}"
            inner_s = f"{inner_s}, {key_s}{val_s}"
        return f"{{{inner_s.removeprefix(', ')}}}"

class Attr(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('attr',)
    
    __fmt_str__ = '{0!s}.{1}'
    __args_attrs__ = ('val', 'attr')
    
    val: Expr
    attr: str

class Call(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('args', 'kwargs')
    
    __args_attrs__ = ('func', 'args', 'keys', 'vals')
    
    func: Expr
    args: list[Expr]
    keys: tuple[str | None]
    vals: list[Expr]
    
    def __str__(self: Self) -> str:
        args_s = ', '.join(map(str, self.args))
        kwargs_s = ""
        for key, val in zip(self.keys, self.vals):
            val_s = f"{val!s}"
            if key is not None:
                key_s = f"{key}="
                if val.precedence < P_TEST:
                    val_s = f"({val_s})"
            else:
                key_s = ""
                if val.precedence < P_EXPR:
                    val_s = f"({val_s})"
                val_s = f"**{val_s}"
            kwargs_s = f"{kwargs_s}, {key_s}{val_s}"
        kwargs_s = kwargs_s.removeprefix(", ")
        opt_comma = ', ' if args_s and kwargs_s else ''
        return f"{self.func!s}({args_s}{opt_comma}{kwargs_s})"

class Slice(ExprPrecedenced):
    precedence = P_TEST
    
    __args_attrs__ = ('start', 'stop', 'step')
    
    start: Expr
    stop: Expr
    step: Expr
    
    def __str__(self: Self) -> str:
        start = self.start
        stop = self.stop
        step = self.step
        if not isinstance(start, Constant) or start.val is not None:
            start_s = f"{start!s}"
            if start.precedence < self.precedence:
                start_s = f"({start_s})"
        else:
            start_s = ""
        if not isinstance(stop, Constant) or stop.val is not None:
            stop_s = f"{stop!s}"
            if stop.precedence < self.precedence:
                stop_s = f"({stop_s})"
        else:
            stop_s = ""
        if not isinstance(step, Constant) or step.val is not None:
            step_s = f"{step!s}"
            if step.precedence < self.precedence:
                step_s = f"({step_s})"
        else:
            step_s = ""
        colon_0 = ":"
        colon_1 = ":" * bool(step_s)
        return f"{start_s}{colon_0}{stop_s}{colon_1}{step_s}"

class Subscr(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('slice',)
    
    __fmt_str__ = '{0!s}[{1!s}]'
    __args_attrs__ = ('val', 'slice')
    
    val: Expr
    slice: Expr

class NamedExpr(ExprPrecedenced):
    precedence = P_NAMED_EXPR
    hs_precedences = {'val': P_TEST}
    no_precs = ('name',)
    
    __fmt_str__ = '{1} := {0!s}'
    __args_attrs__ = ('val', 'name')
    
    val: Expr
    name: str

class BinOp(ExprPrecedenced):
    no_precs = ('op',)
    
    __fmt_str__ = '{0!s} {2} {1!s}'
    __args_attrs__ = ('lhs', 'rhs', 'op')
    
    lhs: Expr
    rhs: Expr
    op: str

class UnaryOp(ExprPrecedenced):
    no_precs = ('op',)
    
    __args_attrs__ = ('val', 'op')
    
    val: Expr
    op: str
    
    def __str__(self: Self) -> str:
        if self.val.precedence < self.precedence:
            val_s = f"({self.val!s})"
        else:
            val_s = f"{self.val!s}"
        if self.op == 'not':
            return f"not {val_s}"
        return f"{self.op}{val_s}"

class BoolOp(ExprPrecedenced):
    precedence = P_AND
    no_precs = ('bkind',)
    
    __args_attrs__ = ('vals', 'bkind')
    
    vals: list[Expr]
    bkind: bool | type(...) | None
    
    def __init__(self, vals, bkind, **kwargs) -> Self:
        super().__init__(vals, bkind, **kwargs)
        if not bkind:
            self.precedence = P_OR
    
    def __str__(self: Self) -> str:
        sep = " and " if self.bkind else " or "
        vals_it = iter(self.vals)
        exp = next(vals_it)
        if exp.precedence < self.precedence:
            res = f"({exp!s})"
        else:
            res = f"{exp!s}"
        for exp in vals_it:
            if exp.precedence < self.precedence:
                res = f"{res}{sep}({exp!s})"
            else:
                res = f"{res}{sep}{exp!s}"
        return res

class AwaitExpr(ExprPrecedenced):
    precedence = P_AWAIT
    
    __fmt_str__ = 'await {0!s}'
    __args_attrs__ = ('val',)
    
    val: Expr

class CompareOp(ExprPrecedenced):
    precedence = P_CMP
    no_precs = ('vals', 'ops')
    
    __args_attrs__ = ('left', 'vals', 'ops')
    
    left: Expr
    vals: list[Expr]
    ops: list[str]
    
    def __str__(self: Self) -> str:
        left_s = f"{self.left!s}"
        if self.left.precedence < P_CMP:
            left_s = f"({left_s})"
        strings_list: list[str] = [left_s]
        strings_append = strings_list.append
        hs_precedences = self.hs_precedences
        for op, exp in zip(self.ops, self.vals):
            strings_append(f" {op} ")
            string = f"{exp!s}"
            if exp.precedence < self.precedence:
                string = f"({string})"
            strings_append(string)
        return ''.join(strings_list)

class Bytecode:
    """
    Bytecode class for easy disassembly/assembly of code.
    
    Contains 3 attributes:
        .code: CodeType
        .doc_const: str | None
        .instrs: list[Instr]
        .jumps: list[Instr]
    
    Bytecode(code_: CodeType | FunctionType) -> Bytecode
    """
    
    __slots__ = ('code', 'doc_const', 'instrs', 'jumps')
    
    code: CodeType
    instrs: list[Instr]
    jumps: list[Instr]
    
    def __init__(self: Self, code_: CodeType | FunctionType) -> None:
        if isinstance(code_, FunctionType):
            code_ = code_.__code__
        self.code = code_
        self.doc_const: str | None = code_.co_consts[0]
        localsplus_names: tuple[str] = code_.co_varnames + code_.co_cellvars
        freevars_start: int = len(localsplus_names)
        localsplus_names += code_.co_freevars
        jumps: list[Instr] = []
        jumps_append = jumps.append
        target_id = 0
        instrs: list[Instr] = []
        instrs_append = instrs.append
        line_starts: Generator[tuple[int, int],
                               None, None] = findlinestarts(code_)
        offset_jumps: defaultdict[int, list[Instr]] = defaultdict(list)
        iterator = enumerate(zip_longest(iter_unpack('BB', code_.co_code),
                                         code_.co_positions(),
                                         fillvalue=(0, 0, 0, 0)))
        for BC, ((opcode, oparg), positions) in iterator:
            orig_BC = BC
            while opcode is EXTENDED_ARG:
                oparg *= 256
                BC, ((opcode, oparg_), _) = next(iterator)
                oparg += oparg_
            extra_info = {}
            has_real_arg: bool = True
            # we can safely modify `oparg` in these paths
            if opcode in hasconst:
                oparg = code_.co_consts[oparg]
            elif opcode in haslocal:
                oparg = localsplus_names[oparg]
                extra_info['kind'] = 0
            elif opcode in hasfree:
                kind = 2 - (oparg < freevars_start)
                oparg = localsplus_names[oparg]
                extra_info['kind'] = kind
            elif opcode is LOAD_GLOBAL:
                extra_info['loads_null'] = oparg & 1
                oparg = code_.co_names[oparg >> 1]
            elif opcode in hasname:
                oparg = code_.co_names[oparg]
            elif opcode is BINARY_OP:
                oparg = B_ops[oparg]
            elif opcode in U_ops:
                oparg = U_ops[opcode]
            elif opcode in hascompare:
                oparg = C_ops[oparg]
            else:
                has_real_arg = False
            instrs_append(instr := Instr(opcode, oparg, positions[:2],
                                         positions[2:],
                                         has_real_arg=has_real_arg,
                                         **extra_info))
            if opcode in hasj:
                if opcode not in hasjback:
                    offset_jumps[BC + oparg + 1].append(instr)
                else:
                    if oparg:
                        target = instrs[-oparg]
                        if target.target_id is None:
                            target.target_id = target_id
                            jumps_append(target)
                            target_id += 1
                        instr.jump_id = target.target_id
                    else:
                        offset_jumps[BC + 1].append(instr)
            if orig_BC in offset_jumps:
                instr.target_id = target_id
                jumps_append(instr)
                for instr_source in offset_jumps.pop(orig_BC):
                    instr_source.jump_id = target_id
                target_id += 1
            # skip possible `CACHE`s
            if cache_count := ICE[opcode]:
                for _ in range(cache_count):
                    next(iterator)
        self.instrs = instrs
        self.jumps = jumps
    
    def assemble(self: Self) -> CodeType:
        extarg_offs: list[int] = []
        extarg_off = extarg_offs.append
        extarg_offlot = extarg_offs.extend
        consts_list: list = [self.doc_const]
        localsplus_name_lists: tuple[list[str],
                                     list[str],
                                     list[str]] = [], [], []
        names_list: list[str] = []
        code_as_list: list[int] = []
        code_append = code_as_list.append
        code_extend = code_as_list.extend
        code_insert = code_as_list.insert
        instrs: list[Instr] = self.instrs
        
        # first pass: convert non-"real" opargs to "real" opargs
        cumul_extarg = 0
        for instr in instrs:
            code_append(opcode := instr.opcode)
            num_caches = ICE[opcode]
            if (jump_id := instr.jump_id) is not None:
                code_append(-1)
                extarg_off(-1)
                extarg_offlot((0,) * num_caches)
                code_extend(cache_T * num_caches)
                continue
            oparg = instr.oparg_or_arg
            if opcode in hasconst:
                code_append(oparg := list_add(consts_list, oparg))
            elif opcode in haslocal or opcode in hasfree:
                # we'll do a second pass through the code later
                # once varnames, cellvars, and freevars are complete
                list_add(localsplus_name_lists[instr.extra_info['kind']],
                         oparg)
                code_append(oparg)
                oparg = 0
            elif opcode is LOAD_GLOBAL:
                code_append(oparg := list_add(names_list, oparg)*2
                           + instr.extra_info['loads_null'])
            elif opcode in hasname:
                code_append(oparg := list_add(names_list, oparg))
            elif opcode is BINARY_OP:
                code_append(oparg := B_ops.index(oparg))
            elif opcode in hascompare:
                code_append(oparg := C_ops.index(oparg))
            else:
                if opcode < HAVE_ARGUMENT:
                    code_append(0)
                else:
                    code_append(oparg)
            extarg_off(n_extargs(oparg))
            extarg_offlot((0,) * num_caches)
            code_extend(cache_T * num_caches)
        
        # second pass: convert local/nonlocal names
        co_varnames: tuple[str] = *localsplus_name_lists[0],
        co_cellvars: tuple[str] = *localsplus_name_lists[1],
        co_freevars: tuple[str] = *localsplus_name_lists[2],
        cellvars_start: int = len(co_varnames)
        freevars_start: int = cellvars_start + len(co_cellvars)
        len_code = len(code_as_list)
        for idx in range(0, len_code, 2):
            opcode = code_as_list[idx]
            oparg = code_as_list[idx + 1]
            if opcode < HAVE_ARGUMENT and oparg:
                # just in case
                code_as_list[idx + 1] = 0
            else:
                assert oparg != -1 or opcode in hasj, \
                    f"{opname[opcode]} opcode was not translated"
                if opcode in haslocal:
                    code_as_list[idx + 1] = oparg = co_varnames.index(oparg)
                    extarg_offs[idx >> 1] = n_extargs(oparg)
                elif opcode in hasfree:
                    if self.extra_info['kind'] == 1:
                        oparg = cellvars_start + co_cellvars.index(oparg)
                    else:
                        oparg = freevars_start + co_freevars.index(oparg)
                    code_as_list[idx + 1] = oparg
                    extarg_offs[idx >> 1] = n_extargs(oparg)
        
        # second pass: convert jump/target ids to offsets
        jump_delays: defaultdict[int, list[int]] = defaultdict(list)
        target_positions: dict[int, int] = {}
        BC = 0
        BC_with_extarg = 0
        while True:
            for instr in instrs:
                num_caches = ICE[opcode := instr.opcode]
                old_BC = BC
                loc = BC * 2
                BC += num_caches + 1
                if (jump_id := instr.jump_id) is not None:
                    if jump_id in target_positions:
                        assert instr.opcode in hasjback, \
                            f"cannot jump backwards with {opname[opcode]}"
                        code_as_list[loc + 1] = oparg = \
                            BC_with_extarg - target_positions[jump_id] + 1
                        oparg = BC_with_extarg - target_positions[jump_id] + 1
                        num_extargs = n_extargs(oparg)
                        old_extargs = extarg_offs[old_BC]
                        if old_extargs == -1:
                            extarg_offs[old_BC] = old_extargs = num_extargs
                        oparg += num_extargs
                        num_extargs = n_extargs(oparg)
                        if old_extargs != num_extargs:
                            extarg_offs[old_BC] = num_extargs
                            break
                        code_as_list[loc + 1] = oparg
                    else:
                        jump_delays[jump_id].append((old_BC,
                                                     BC_with_extarg + 1))
                        num_extargs = extarg_offs[old_BC]
                        if num_extargs == -1:
                            num_extargs = 0
                else:
                    num_extargs = extarg_offs[old_BC]
                BC_with_extarg += num_extargs
                if ((target_id := instr.target_id) is not None
                        and target_id in jump_delays):
                    do_break = False
                    target_positions[target_id] = BC_with_extarg
                    for pos, off in jump_delays.pop(target_id):
                        oparg = BC_with_extarg - off
                        num_extargs = n_extargs(oparg)
                        old_extargs = extarg_offs[pos]
                        if old_extargs == -1:
                            extarg_offs[pos] = num_extargs
                        elif old_extargs != num_extargs:
                            extarg_offs[pos] = num_extargs
                            do_break = True
                            break
                        code_as_list[pos*2 + 1] = oparg
                    if do_break:
                        break
                BC_with_extarg += num_caches + 1
            else:
                break
            jump_delays.clear()
            target_positions.clear()
            BC_with_extarg = BC = 0
        assert not jump_delays, f"invalid jumps: {[*jump_delays.keys()]}"
        
        # fourth pass: add EXTENDED_ARGs, calculate stack depth, make the
        # line table
        # TODO: calculate max stack depth instead of a linear no-jump path
        # through the code
        maxdepth = depth = BC = idx = idx_noext = 0
        linetable = bytearray()
        linetable_append = linetable.append
        lastline = 1
        while idx < len_code:
            (line0, line1), (col0, col1) = (instrs[BC].line_pos,
                                            instrs[BC].col_pos)
            opcode = code_as_list[idx]
            ncaches: int = ICE[opcode]
            isize_m1 = ncaches # "isize minus 1"
            delta = line0 - lastline
            while isize_m1 > 7:
                write_loc(line0, line1, col0, col1,
                          delta, 7, linetable_append)
                isize_m1 -= 8
            write_loc(line0, line1, col0, col1,
                      delta, isize_m1, linetable_append)
            if delta:
                lastline = line0
            oparg = code_as_list[idx + 1]
            if opcode < HAVE_ARGUMENT:
                oparg = None
            else:
                if oparg > 0xFF:
                    ext_oparg = oparg
                    while ext_oparg := ext_oparg >> 8:
                        code_insert(idx, ext_oparg & 0xFF)
                        code_insert(idx, EXTENDED_ARG)
                    idx += extarg_offs[idx_noext] * 2
                    code_as_list[idx + 1] = oparg & 0xFF
            depth += stack_effect(opcode, oparg, jump=False)
            if depth > maxdepth:
                maxdepth = depth
            BC += 1
            idx += 2 * (ncaches + 1)
            idx_noext += ncaches + 1
        
        # assemble the code object
        # TODO: make the exception table
        co_consts = tuple(consts_list)
        co_names = tuple(names_list)
        code = self.code
        return CodeType(code.co_argcount, code.co_posonlyargcount,
                        code.co_kwonlyargcount, len(co_varnames),
                        maxdepth, code.co_flags, bytes(code_as_list),
                        co_consts, co_names, co_varnames, code.co_filename,
                        code.co_name, code.co_qualname, code.co_firstlineno,
                        bytes(linetable), code.co_exceptiontable,
                        co_freevars, co_cellvars)

class BytecodeParser(Bytecode):
    __slots__ = ('__dict__', 'idx', 'stack', 'jumplead_bexpr', 'call_shape')
    
    idx: int
    stack: list[Expr]
    jumplead_bexpr: list[bool]
    call_shape: dict[str, Any]
    
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.idx = 0
        self.stack = []
        self.spush = self.stack.append
        self.spop = self.stack.pop
        self.call_shape = {'kwnames': ()}
        len_jumps = len(jumps := self.jumps)
        len_instrs = len(instrs := self.instrs)
        self.jumplead_bexpr = jumplead_bexpr = [None] * len_jumps
        indices: set[int] = {*range(len_jumps)}
        j = 0
        while True:
            try:
                i = min(indices)
            except ValueError:
                break
            tempset: set[int] = set()
            verdict: bool | None = False
            while True:
                tempset.add(i)
                inst = jumps[i]
                while j < len_instrs:
                    if instrs[j] is inst:
                        break
                    j += 1
                else:
                    break
                inst = instrs[j - 1]
                if (inst.opcode is JUMP_IF_FALSE_OR_POP or
                        inst.opcode is JUMP_IF_TRUE_OR_POP):
                    verdict = True
                    break
                elif inst.jump_id == i:
                    break
                elif inst.opcode not in hasjbool:
                    verdict = None
                    break
                i = inst.jump_id
            indices -= tempset
            for index in tempset:
                jumplead_bexpr[index] = verdict
    
    def advance(self: Self) -> Instr | None:
        try:
            res = self.instrs[self.idx]
            self.idx += 1
        except IndexError:
            return None
        return res
    
    def skip(self: Self, n: int = 1) -> None:
        self.idx += n
    
    def peek(self: Self, n: int = 0) -> Instr | None:
        try:
            return self.instrs[self.idx + n]
        except IndexError:
            return None
    
    def decompile_expr(self: Self) -> None:
        stack = self.stack
        PUSH = self.spush
        POP = self.spop
        call_shape = self.call_shape
        # only a dict for easy contains checking + getting the list
        # of values and operations (structured like the AST structure
        # of ast.Compare)
        compare_stack: dict[int, list[list[Expr], list[str], int]] = {}
        skip_cause_compare: set[int] = set()
        skip_ccmp_add = skip_cause_compare.add
        skip_ccmp_remove = skip_cause_compare.remove
        cPOP = compare_stack.pop
        compare_popitem = compare_stack.popitem
        boolop_stack: list[tuple[bool, list, Optional[int]]] = []
        len_boolop_stack = 0
        def bPUSH(x):
            nonlocal len_boolop_stack
            boolop_stack.append(x)
            len_boolop_stack += 1
        def bPOP(n=-1):
            nonlocal len_boolop_stack
            len_boolop_stack -= 1
            return boolop_stack.pop(n)
        boolop_jumps: set[int] = set()
        bjump_add = boolop_jumps.add
        bjump_remove = boolop_jumps.remove
        instr: Instr | None = None
        while instr := self.advance():
            opcode = instr.opcode
            if instr.target_id is not None:
                if self.peek(-2).opcode in hasjbool and len_boolop_stack > 1:
                    vals = boolop_stack[-1][1]
                    assert len(vals) == 1, "?? (-2 peek)"
                    val = vals[0]
                    while (len_boolop_stack > 1
                            and boolop_stack[-2][2] == instr.target_id):
                        bkind, vals, id = bPOP(-2)
                        vals.append(val)
                        val = BoolOp(vals, bkind)
                    boolop_stack[-1][1][0] = val
                if stack:
                    val = stack[-1]
                    while (boolop_stack
                            and boolop_stack[-1][2] == instr.target_id):
                        bkind, vals, id = bPOP()
                        vals.append(val)
                        val = BoolOp(vals, bkind)
                    stack[-1] = val
            if (opcode is COMPARE_OP
                    or opcode is IS_OP
                    or opcode is CONTAINS_OP):
                rhs = POP()
                if opcode is IS_OP:
                    op = 'is' + ' not' * instr.oparg_or_arg
                elif opcode is CONTAINS_OP:
                    op = 'not ' * instr.oparg_or_arg + 'in'
                    if isinstance(rhs, frozenset):
                        rhs = TLSLiteral([*map(Constant, rhs)], 2)
                else:
                    op = instr.oparg_or_arg
                possible_SWAP = self.peek(-3)
                possible_COPY = self.peek(-2)
                possible_jump = self.peek()
                # detect a chained comparison:
                # (load first arg)
                # (load second arg)
                # SWAP 2
                # COPY 2
                # {COMPARE,IS,CONTAINS}_OP << here
                # POP_JUMP_FORWARD_IF_FALSE/JUMP_IF_FALSE_OR_POP
                if (possible_COPY.opcode is COPY
                        and possible_COPY.oparg_or_arg == 2
                        and possible_SWAP.opcode is SWAP
                        and possible_SWAP.oparg_or_arg == 2
                        and possible_jump.opcode
                            is POP_JUMP_FORWARD_IF_FALSE
                            or possible_jump.opcode
                                is JUMP_IF_FALSE_OR_POP):
                    jump_id = possible_jump.jump_id
                    if jump_id in compare_stack:
                        POP() # pop (first arg) for the jump
                        _, vals_list, ops_list, _ = \
                            cmp_info = compare_stack[jump_id]
                        vals_list.append(rhs)
                        ops_list.append(op)
                        cmp_info[3] = len(stack)
                        continue
                    # is this check (for the finalizing code) needed?
                    elif ((target := self.jumps[jump_id]).opcode is SWAP
                            and target.oparg_or_arg == 2
                            or
                            target.opcode is POP_TOP):
                        left = POP() # pop (very first arg)
                        self.skip() # skip the jump
                        compare_stack[jump_id] = \
                            [left, [rhs], [op], len(stack)]
                        continue
                elif compare_stack:
                    # (dangerous assumption) bytecode structure preceding
                    # last compare in chained comparisons:
                    # POP_JUMP_FORWARD_IF_FALSE/JUMP_IF_FALSE_OR_POP
                    # (load second arg)
                    # {COMPARE,IS,CONTAINS}_OP
                    # check for the last jump by checking for the stack
                    # size; if it's just a 1-difference, it's part of
                    # the last chain compare
                    target = next(reversed(compare_stack))
                    left, vals_list, ops_list, last_ss = compare_stack[target]
                    # check for 0 because we assigned POP() to `rhs`
                    if len(stack) - last_ss == 0:
                        vals_list.append(rhs)
                        ops_list.append(op)
                        PUSH(CompareOp(left, vals_list, ops_list))
                        del compare_stack[target]
                        skip_ccmp_add(target)
                        continue
                stack[-1] = CompareOp(stack[-1], [rhs], [op])
            elif instr.has_real_arg:
                if opcode is KW_NAMES:
                    assert not call_shape['kwnames'], \
                        "call_shape has non-empty 'kwnames'"
                    call_shape['kwnames'] = instr.oparg_or_arg
                elif opcode in hasconst:
                    PUSH(Constant(instr.oparg_or_arg))
                elif opcode is LOAD_ATTR or opcode is LOAD_METHOD:
                    stack[-1] = Attr(stack[-1], instr.oparg_or_arg)
                elif opcode is LOAD_GLOBAL:
                    PUSH(Name(instr.oparg_or_arg, op_kind=1))
                elif opcode in name_loads:
                    PUSH(Name(instr.oparg_or_arg, op_kind=name_loads[opcode],
                              **instr.extra_info))
                elif opcode is BINARY_OP:
                    if instr.oparg_or_arg not in B_ops_prec:
                        return instr
                    rhs = POP()
                    stack[-1] = BinOp(stack[-1], rhs, instr.oparg_or_arg,
                                      precedence=B_ops_prec[
                                          instr.oparg_or_arg
                                      ])
                elif opcode in U_ops:
                    stack[-1] = UnaryOp(stack[-1], instr.oparg_or_arg,
                                        precedence=U_ops_prec[
                                            instr.oparg_or_arg
                                        ])
                else:
                    break
            elif (instr.target_id is not None
                    and instr.target_id in skip_cause_compare):
                skip_ccmp_remove(instr.target_id)
                if instr.opcode is not POP_TOP:
                    self.skip() # instr must be a SWAP 2,
                                # skip the POP_TOP opcode
                # we have nothing else to do here
            elif opcode is BINARY_SUBSCR:
                item = POP()
                if isinstance(item, TLSLiteral) and not item.kind:
                    # setting to None because this is only
                    # used with a containment check
                    item.extra_info['no_parens'] = None
                stack[-1] = Subscr(stack[-1], item)
            elif opcode is PRECALL:
                # nothing significant to do here
                pass
            elif opcode is CALL:
                oparg = instr.oparg_or_arg
                pargs_end = -len(call_shape['kwnames'])
                if not pargs_end:
                    pargs_end = None
                res = Call(stack[~oparg],
                           stack[-oparg : pargs_end],
                           call_shape['kwnames'],
                           stack[pargs_end :])
                call_shape['kwnames'] = ()
                del stack[-oparg:]
                stack[-1] = res
            elif opcode is CALL_FUNCTION_EX:
                if instr.oparg_or_arg & 1:
                    kwargs = POP()
                    kwargs_keys = tuple([key.val if key is not None else None
                                         for key in kwargs.keys])
                    kwargs_vals = kwargs.vals
                else:
                    kwargs_keys = ()
                    kwargs_vals = []
                args = POP()
                stack[-1] = Call(stack[-1], args.vals, kwargs_keys, kwargs_vals)
            elif opcode is BUILD_TUPLE:
                if oparg := instr.oparg_or_arg:
                    stack[-oparg:] = [TLSLiteral(stack[-oparg:], 0)]
                else:
                    PUSH(TLSLiteral([], 0))
            elif opcode is BUILD_LIST:
                if oparg := instr.oparg_or_arg:
                    stack[-oparg:] = [TLSLiteral(stack[-oparg:], 1)]
                else:
                    PUSH(TLSLiteral([], 1))
            elif opcode is BUILD_SET:
                if oparg := instr.oparg_or_arg:
                    stack[-oparg:] = [TLSLiteral(stack[-oparg:], 2)]
                else:
                    PUSH(TLSLiteral([], 2))
            elif opcode is BUILD_MAP:
                if oparg := instr.oparg_or_arg:
                    oparg *= -2
                    stack[oparg:] = [DictLiteral(stack[oparg::2],
                                                  stack[oparg + 1 :: 2])]
                else:
                    PUSH(DictLiteral([], []))
            elif opcode is BUILD_SLICE:
                if (oparg := instr.oparg_or_arg) == 2:
                    start = stack[-2]
                    stop = stack[-1]
                    step = Constant(None)
                else:
                    start = stack[-3]
                    stop = stack[-2]
                    step = stack[-1]
                stack[-oparg:] = [Slice(start, stop, step)]
            elif opcode is LIST_EXTEND:
                val = POP()
                stack[-instr.oparg_or_arg].vals.append(VarUnpack(val))
            elif opcode is LIST_APPEND:
                val = POP()
                stack[-instr.oparg_or_arg].vals.append(val)
            elif opcode is LIST_TO_TUPLE:
                stack[-1].kind = 0
            elif opcode is DICT_MERGE:
                val = POP()
                literal: DictLiteral = stack[-instr.oparg_or_arg]
                if isinstance(val, DictLiteral):
                    literal.keys.extend(val.keys)
                    literal.vals.extend(val.vals)
                else:
                    literal.keys.append(None)
                    literal.vals.append(val)
            elif opcode is DICT_UPDATE:
                val = POP()
                key = POP()
                literal: DictLiteral = stack[-instr.oparg_or_arg]
                literal.keys.append(key)
                literal.vals.append(val)
            elif opcode is PUSH_NULL:
                # nothing should be pushed here like in LOAD_GLOBAL
                pass
            elif opcode is NOP:
                pass
            elif opcode is SWAP:
                oparg = instr.oparg_or_arg
                stack[-1], stack[-oparg] = stack[-oparg], stack[-1]
            elif opcode is COPY:
                if self.peek().opcode in name_stores:
                    name_instr = self.advance()
                    stack[-1] = NamedExpr(stack[-1], name_instr.oparg_or_arg,
                                          op_kind=
                                            name_stores[name_instr.opcode],
                                          **name_instr.extra_info)
                else:
                    PUSH(tag(stack[-instr.oparg_or_arg].copy(), 'copy'))
            elif opcode is JUMP_IF_FALSE_OR_POP:
                val = POP()
                if boolop_stack and boolop_stack[-1][0] is True:
                    boolop_stack[-1][1].append(val)
                else:
                    bPUSH((True, [val], instr.jump_id))
            elif opcode is JUMP_IF_TRUE_OR_POP:
                val = POP()
                if boolop_stack and boolop_stack[-1][0] is False:
                    boolop_stack[-1][1].append(val)
                else:
                    bPUSH((False, [val], instr.jump_id))
            elif (opcode is POP_JUMP_FORWARD_IF_FALSE
                    or opcode is POP_JUMP_FORWARD_IF_TRUE):
                if not self.jumplead_bexpr[instr.jump_id]:
                    break
                val = POP()
                op_bkind = (
                    ...
                    if opcode is POP_JUMP_FORWARD_IF_FALSE else
                    None
                )
                if boolop_stack and boolop_stack[-1][0] is op_bkind:
                    boolop_stack[-1][1].append(val)
                else:
                    bPUSH((op_bkind, [val], instr.jump_id))
            else:
                break
        if boolop_stack:
            val = stack[-1]
            while boolop_stack:
                bkind, vals, _, *ext = bPOP()
                vals.append(val)
                val = BoolOp(vals, bkind)
            stack[-1] = val
        return instr
    
    def decompile_stmt(self: Self) -> Stmt | None:
        stack = self.stack
        PUSH = self.spush
        POP = self.spop
        assign_list: list[Expr] | None = None
        stack_unpack: list[list[int, list[Expr]]] = []
        while True:
            instr = self.decompile_expr()
            if instr is None:
                break
            opcode = instr.opcode
            if opcode is POP_TOP:
                return StmtExpr(POP())
            elif opcode in name_stores:
                node = Name(instr.oparg_or_arg, op_kind=name_stores[opcode],
                            **instr.extra_info)
            elif opcode is STORE_ATTR:
                node = Attr(POP(), instr.oparg_or_arg)
            elif opcode is STORE_SUBSCR:
                sub = POP()
                node = Subscr(POP(), sub, instr.oparg_or_arg)
            elif opcode is UNPACK_SEQUENCE:
                n = instr.oparg_or_arg
                stack_unpack.append([n, [], None, 0])
                if n:
                    continue
            elif opcode is UNPACK_EX:
                n = instr.oparg_or_arg
                stack_unpack.append([n & 0xFF, [], False, n >> 8])
                continue
            elif opcode is BINARY_OP:
                node = POP()
                if isinstance(node, Subscr):
                    self.idx += 3
                elif isinstance(node, Attr):
                    self.idx += 2
                else:
                    self.idx += 1
                return BinAssign(StmtWrap(node), POP(), instr.oparg_or_arg)
            elif opcode is RETURN_VALUE:
                return Return(StmtWrap(POP()))
            elif opcode is RESUME:
                continue
            else:
                break
            backed = False
            while stack_unpack:
                info = stack_unpack[-1]
                if info[0]:
                    info[1].append(node)
                    info[0] -= 1
                    if info[0] or info[2] is False:
                        break
                elif info[2] is False:
                    info[1].append(VarUnpack(node))
                    info[2] = True
                    info[0] = info[3]
                    if info[0]:
                        break
                else:
                    if backed:
                        raise ValueError(
                            f"empty stack unprocessed: {info[1]}"
                        )
                stack_unpack.pop()
                els = info[1]
                node = TLSLiteral(els, 0)
                if not stack_unpack and els:
                    node.extra_info['no_parens'] = True
                backed = True
            else:
                el = POP()
                if 'copy' in el.tags:
                    if not assign_list:
                        assign_list = [node]
                    else:
                        assign_list.append(node)
                else:
                    if assign_list:
                        assign_list.append(node)
                        arg = assign_list
                        assign_list = None
                    else:
                        arg = [node]
                    return Assign(StmtWrap(el), arg)
