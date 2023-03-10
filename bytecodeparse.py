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
from typing import Generator, Self

# Constant/initial variables

globals().update(opmap)

B_ops: list[str] = [x[1] for x in B_ops]
hascompare: set[int] = {*hascompare}
hasconst: set[int] = {*hasconst}
hasfree: set[int] = {*hasfree}
hasj: set[int] = {*hasj} - {LOAD_GLOBAL}
hasjback: set[int] = {x for x in hasj if 'BACKWARD' in opname[x]}
haslocal: set[int] = {*haslocal}
hasname: set[int] = {*hasname}
U_ops: dict[int, str] = {UNARY_POSITIVE: '+', UNARY_NEGATIVE: '-',
                         UNARY_INVERT: '~', UNARY_NOT: 'not'}
C_ops = "<", "<=", "==", "!=", ">", ">="
cache_T: tuple[int, int] = CACHE, 0
name_stores: dict[int, int] = {STORE_NAME: 0, STORE_GLOBAL: 1,
                               STORE_FAST: 2, STORE_DEREF: 3}
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
                                 kind=name_stores[instr.opcode])
        return expr
    return wrapper

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
    jump_id: int
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
              ^ hash(self.line_pos) ^ hash(self.col_pos) ^ self.jump_id)
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

class Expr:
    __slots__ = ('__dict__', '__fmt_str__', '__args_attrs__',
                 '__kwargs_attrs__', '__defaults__', '__kwdefaults__',
                 '__start_default__', 'extra_info')
    
    __fmt_str__: str # this is not guaranteed to exist
    __args_attrs__: tuple[str]
    __kwargs_attrs__: tuple[str]
    __defaults__: tuple
    __kwdefaults__: dict[str, object]
    __start_default__: int
    extra_info: dict[str, object]
    
    def __init_subclass__(cls, **kwargs) -> None:
        super().__init_subclass__(**kwargs)
        if isinstance(cls.__args_attrs__, MemberDescriptorType):
            cls.__args_attrs__ = ()
        if isinstance(cls.__kwargs_attrs__, MemberDescriptorType):
            cls.__kwargs_attrs__ = ()
        if isinstance(cls.__defaults__, MemberDescriptorType):
            cls.__defaults__ = ()
        if isinstance(cls.__kwdefaults__, MemberDescriptorType):
            cls.__kwdefaults__ = {}
        if isinstance(cls.__fmt_str__, MemberDescriptorType):
            cls.__str__ = cls.__repr__
        cls.__start_default__ = max(
            len(cls.__args_attrs__) - len(cls.__defaults__),
            0
        )
        if hasattr(cls, '__init__'):
            cls.__real_init__ = cls.__init__
            cls.__init__ = lambda self, *args, **kwargs: None
    
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

class ExprPrecedenced(Expr):
    __slots__ = ('precedence', 'hs_precedences', 'no_precs')
    
    __args_attrs__ = ('val',)
    
    __fmt_str__ = ""
    
    precedence: int
    hs_precedences: dict[str, int]
    no_precs: set[str]
    
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
            for attr in self.__args_attrs__:
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

class Constant(ExprPrecedenced):
    precedence = P_ATOM
    def __str__(self: Self) -> str:
        return f"{self.val!r}"

class Name(ExprPrecedenced):
    precedence = P_ATOM
    def __str__(self: Self) -> str:
        return f"{self.val}"

class Attr(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('attr',)
    __fmt_str__ = '{0!s}.{1}'
    __args_attrs__ = ('val', 'attr')

class Call(ExprPrecedenced):
    precedence = P_ATOM
    no_precs = ('args', 'kwargs')
    __args_attrs__ = ('func', 'args', 'kwargs')
    def __str__(self: Self) -> str:
        args_s = ', '.join(map(str, self.args))
        kwargs_s = ', '.join(f"{x}={y!s}" for x, y in self.kwargs.items())
        opt_comma = ', ' if args_s and kwargs_s else ''
        return f"{self.func!s}({args_s}{opt_comma}{kwargs_s})"

class NamedExpr(ExprPrecedenced):
    precedence = P_NAMED_EXPR
    no_precs = ('name',)
    __fmt_str__ = '{1} := {0!s}'
    __args_attrs__ = ('val', 'name')

class BinOp(ExprPrecedenced):
    no_precs = ('op',)
    __fmt_str__ = '{0!s} {2} {1!s}'
    __args_attrs__ = ('lhs', 'rhs', 'op')

class UnaryOp(ExprPrecedenced):
    no_precs = ('op',)
    __args_attrs__ = ('val', 'op')
    def __str__(self: Self) -> str:
        if self.op == 'not':
            return f"not {self.val!s}"
        return f"{self.op}{self.val!s}"

class AwaitExpr(ExprPrecedenced):
    precedence = P_AWAIT
    __fmt_str__ = 'await {0!s}'
    __args_attrs__ = ('val',)

class CompareOp(ExprPrecedenced):
    no_precs = ('vals', 'ops')
    precedence = P_CMP
    __args_attrs__ = ('left', 'vals', 'ops')
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
        .instrs: list[Instr]
        .jumps: list[Instr]
    
    Bytecode(code_: CodeType | FunctionType) -> Bytecode
    """
    
    __slots__ = ('code', 'instrs', 'jumps')
    
    code: CodeType
    instrs: list[Instr]
    jumps: list[Instr]
    
    def __init__(self: Self, code_: CodeType | FunctionType) -> None:
        if isinstance(code_, FunctionType):
            code_ = code_.__code__
        self.code = code_
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
        iterator = enumerate(zip(iter_unpack('BB', code_.co_code),
                                 code_.co_positions()))
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
                oparg = U_ops[oparg]
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
        jump_delays: defaultdict[int, list[int]] = defaultdict(list)
        target_positions: dict[int, int] = {}
        target_poses: set[int] = set()
        targets_addpos = target_poses.add
        consts_list: list = []
        localsplus_name_lists: tuple[list[str],
                                     list[str],
                                     list[str]] = [], [], []
        names_list: list[str] = []
        code_as_list: list[int] = []
        code_append = code_as_list.append
        code_extend = code_as_list.extend
        code_insert = code_as_list.insert
        instrs: list[Instr] = self.instrs
        
        # first pass: convert jump/target ids to offsets, convert
        # non-"real" opargs to "real" opargs
        BC = 0
        for instr in instrs:
            code_append(opcode := instr.opcode)
            num_caches = ICE[opcode]
            if (jump_id := instr.jump_id) is not None:
                if jump_id in target_positions:
                    assert instr.opcode in hasjback, \
                        f"cannot jump backwards with {opname[opcode]}"
                    code_append(BC - target_positions[jump_id] + 1)
                else:
                    jump_delays[jump_id].append(BC + 1)
                    code_append(-1)
                
                code_extend(cache_T * num_caches)
                BC += num_caches + 1
                continue
            if ((target_id := instr.target_id) is not None
                    and target_id in jump_delays):
                target_positions[target_id] = BC
                targets_addpos(BC)
                for pos in jump_delays.pop(target_id):
                    code_as_list[pos*2 - 1] = BC - pos
            oparg = instr.oparg_or_arg
            if opcode in hasconst:
                code_append(list_add(consts_list, oparg))
            elif opcode in haslocal or opcode in hasfree:
                # we'll do a second pass through the code later
                # once varnames, cellvars, and freevars are complete
                list_add(localsplus_name_lists[instr.extra_info['kind']],
                         oparg)
                code_append(oparg)
            elif opcode is LOAD_GLOBAL:
                code_append(list_add(names_list, oparg)*2
                           + instr.extra_info['loads_null'])
            elif opcode in hasname:
                code_append(list_add(names_list, oparg))
            elif opcode is BINARY_OP:
                code_append(B_ops.index(oparg))
            elif opcode in hascompare:
                code_append(C_ops.index(oparg))
            else:
                if opcode < HAVE_ARGUMENT:
                    code_append(0)
                else:
                    code_append(oparg)
            code_extend(cache_T * num_caches)
            BC += num_caches + 1
        assert not jump_delays, f"invalid jumps: {[*jump_delays.keys()]}"
        
        # second pass: convert local/nonlocal names, check for nontranslated
        # jumps, calculate EXTENDED_ARG offsets, adjust backward jump offsets
        co_varnames: tuple[str] = *localsplus_name_lists[0],
        co_cellvars: tuple[str] = *localsplus_name_lists[1],
        co_freevars: tuple[str] = *localsplus_name_lists[2],
        cellvars_start: int = len(co_varnames)
        freevars_start: int = cellvars_start + len(co_cellvars)
        bc_numextargs: list[int] = [0] * BC
        bc_cumul_numextargs: list[int] = [0] * BC
        total_numextargs = BC = 0
        len_code = len(code_as_list)
        for idx in range(0, len_code, 2):
            opcode = code_as_list[idx]
            oparg = code_as_list[idx + 1]
            if opcode < HAVE_ARGUMENT:
                # just in case
                code_as_list[idx + 1] = 0
            else:
                assert oparg != -1, \
                    f"{opname[opcode]} opcode was not translated"
                if opcode in haslocal:
                    code_as_list[idx + 1] = oparg = co_varnames.index(oparg)
                elif opcode in hasfree:
                    if self.extra_info['kind'] == 1:
                        oparg = cellvars_start + co_cellvars.index(oparg)
                    else:
                        oparg = freevars_start + co_freevars.index(oparg)
                    code_as_list[idx + 1] = oparg
                """
                numextargs = 0
                ext_oparg: int = oparg
                while ext_oparg := ext_oparg >> 8:
                    numextargs += 1
                if opcode in hasjback:
                    targetp = BC - oparg + 1
                    new_oparg = (oparg
                                + abs(total_numextargs + numextargs
                                     - bc_cumul_numextargs[targetp]))
                    new_numextargs = 0
                    ext_oparg = new_oparg
                    while ext_oparg := ext_oparg >> 8:
                        new_numextargs += 1
                    if new_numextargs > numextargs:
                        numextargs = new_numextargs
                    code_as_list[idx + 1] = new_oparg
                if numextargs:
                    total_numextargs += numextargs
                    bc_numextargs[BC] = numextargs
                    bc_cumul_numextargs[BC] = total_numextargs
                """
                assert oparg < 256, \
                    "assembling EXTENDED_ARGs not yet supported"
            BC += 1
        
        # third pass: adjust forward jump offsets, final adjustment to all
        # jump offsets before conversion to EXTENDED_ARG
        #while idx:
        #    BC -= 1
        #    idx -= 2
        #    if opcode in hasj and not in hasjback:
        #        
        
        # fourth pass: add EXTENDED_ARGs, adjust jump offsets, calculate stack
        # depth, make the line table
        # TODO: calculate max stack depth instead of a linear no-jump path
        # through the code
        maxdepth = depth = BC = idx = 0
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
                """
                if oparg > 0xFF:
                    ext_oparg = oparg
                    while ext_oparg := ext_oparg >> 8:
                        code_insert(idx, ext_oparg & 0xFF)
                        code_insert(idx, EXTENDED_ARG)
                    idx += bc_numextargs[BC] * 2
                    code_as_list[idx + 1] = oparg & 0xFF
                """
                pass
            depth += stack_effect(opcode, oparg, jump=False)
            if depth > maxdepth:
                maxdepth = depth
            BC += 1
            idx += 2 * (ncaches + 1)
        
        # fourth pass: add EXTENDED_ARGs for jump opcodes
        """
        maxdepth = depth = idx = 0
        while idx < len_code:
            opcode = code_as_list[idx]
            oparg = code_as_list[idx + 1]
            if opcode < HAVE_ARGUMENT:
                oparg = None
            depth += stack_effect(opcode, oparg, jump=False)
            if depth > maxdepth:
                maxdepth = depth
            idx += 2
        """
        
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
    __slots__ = ('__dict__', 'idx', 'stack', 'call_shape')
    
    idx: int
    stack: list[Expr]
    call_shape: dict[str, object]
    
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.idx = 0
        self.stack = []
        self.spush = self.stack.append
        self.spop = self.stack.pop
        self.call_shape = {'kwnames': ()}
    
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
    
    def decompile_expr(self: Self) -> Expr | None:
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
        while instr := self.advance():
            pos: int = self.idx - 1
            opcode = instr.opcode
            if instr.has_real_arg:
                if opcode is KW_NAMES:
                    assert not call_shape['kwnames'], \
                        "call_shape has non-empty 'kwnames'"
                    call_shape['kwnames'] = instr.oparg_or_arg
                elif opcode in hasconst:
                    PUSH(Constant(instr.oparg_or_arg))
                elif opcode is LOAD_ATTR or opcode is LOAD_METHOD:
                    stack[-1] = Attr(stack[-1], instr.oparg_or_arg)
                elif opcode is LOAD_GLOBAL:
                    PUSH(Name(instr.oparg_or_arg))
                elif 'LOAD' in opname[opcode]:
                    PUSH(Name(instr.oparg_or_arg, **instr.extra_info))
                elif opcode is BINARY_OP:
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
                elif opcode in hascompare:
                    rhs = POP()
                    op: str = instr.oparg_or_arg
                    possible_SWAP = self.peek(-3)
                    possible_COPY = self.peek(-2)
                    possible_jump = self.peek()
                    # detect a chained comparison:
                    # (load first arg)
                    # (load second arg)
                    # SWAP 2
                    # COPY 2
                    # COMPARE_OP << here
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
                        # COMPARE_OP
                        # check for the last jump by checking for the stack
                        # size; if it's just a 1-difference, it's part of
                        # the last chain compare
                        target = next(reversed(compare_stack))
                        left, vals_list, ops_list, last_ss = \
                            compare_stack[target]
                        # check for 0 because we assigned POP() to `rhs`
                        if len(stack) - last_ss == 0:
                            vals_list.append(rhs)
                            ops_list.append(op)
                            PUSH(CompareOp(left, vals_list, ops_list))
                            del compare_stack[target]
                            skip_ccmp_add(target)
                            continue
                    stack[-1] = CompareOp(stack[-1], [rhs], [op])
            elif (instr.target_id is not None
                    and instr.target_id in skip_cause_compare):
                skip_ccmp_remove(instr.target_id)
                if instr.opcode is not POP_TOP:
                    self.skip() # instr must be a SWAP 2,
                                # skip the POP_TOP opcode
                # we have nothing else to do here
            elif opcode is PRECALL:
                # nothing significant to do here
                pass
            elif opcode is CALL:
                oparg = instr.oparg_or_arg
                pargs_len = oparg - len(call_shape['kwnames'])
                kwargs: dict[str, object] = {}
                for name, val in zip(call_shape['kwnames'],
                                     stack[-oparg + pargs_len :]):
                    kwargs[name] = val
                res = Call(stack[-oparg - 1],
                           stack[-oparg : -oparg + pargs_len],
                           kwargs)
                call_shape['kwnames'] = ()
                del stack[-oparg:]
                stack[-1] = res
