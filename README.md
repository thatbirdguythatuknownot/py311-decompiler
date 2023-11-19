# py311-decompiler
A Python decompiler for 3.11; WIP.

Credits to [greyblue9](https://github.com/greyblue9/) and [the unpyc 3.7-3.10 project](https://github.com/greyblue9/unpyc37-3.10/) for most of the inspiration.

## Classes
```
Stmt
- Assign(val: StmtWrap, assigns: list[Expr]) e.g. `a = b = 2`
    `val` is the rightmost expression in the assignment; i.e. the `2` in the example
    `assigns` is a list of targets; i.e. the `a` and `b` in the example

- BinAssign(val: StmtWrap, left: Expr, op: str) `left op= val` e.g. `x += 5`
    `val` is the righthand expression side of the assignment; i.e. `5` in the example
    `left` is the target of the assignment; i.e. `x` in the example
    `op` is the operation; i.e. `+` in the example

- Return(val: StmtWrap) e.g. `return val`


Expr
- StmtExpr(val: Expr)
    the standalone expression inside of a line

- StmtWrap(val: Expr)
    wrapper for expressions in `Assign`/`BinAssign`/`Return`

- Constant(val) e.g. `1`, `"abc"`

- Name(val: str) e.g. `ident`, `foo`

- VarUnpack(val: Expr) `*val`

- TLSLiteral(vals: list[Expr], kind: int) e.g. `[1, 2, 3]`, `("a", "b", "c")`, `{5, 7, 9}`
    `vals` is a list of elements
    `kind` is 0 for a tuple, `1` for a list, and `2` for a set

- DictLiteral(keys: list[Expr | None], vals: list[Expr]) e.g. `{1: 2, 3: 4, 5: 6, **b}`
    `keys` is a list of keys; i.e. `[1, 3, 5, None]` in the example
    `vals` is a list of values; i.e. `[2, 4, 6, b]` in the example

- Attr(val: Expr, attr: str) `val.attr`

- Call(func: Expr, args: list[Expr], keys: tuple[str | None], vals: list[Expr]) e.g. `a(b, b2, *d, c=2, d=3, **e)`
    `func` is the function; i.e. `a` in the example
    `args` is a list of positional arguments; i.e. `[b, b2, VarUnpack(d)]` in the example
    `keys` is a list of keyword argument names; i.e. `[c, d, None]` in the example
    `vals` is a list of keyword argument values; i.e. `[2, 3, e]` in the example

- Slice(start: Expr, stop: Expr, step: Expr) `start:stop:step`

- Subscr(val: Expr, slice: Expr) `val[slice]`

- NamedExpr(val: Expr, name: str) `name := val`

- BinOp(lhs: Expr, rhs: Expr, op: str) `lhs op= rhs`

- UnaryOp(val: Expr, op: str) `op val` e.g. `-val`, `+val`, `not val`

- BoolOp(vals: list[Expr], bkind: bool | type(...) | None) e.g. `a and b and c`
    `vals` is a list of values; i.e. `[a, b, c]` in the example
    `bkind` is truthy for `and`, falsy for `or`

- AwaitExpr(val: Expr) `await val`

- CompareOp(left: Expr, vals: list[Expr], ops: list[str]) e.g. `a < b > c != d`
    `left` is the leftmost value; i.e. `a` in the example
    `vals` is a list of values; i.e. `[b, c, d]` in the example
    `ops` is a list of operators; i.e. `<`, `>`, and `!=` in the example
```

## Usage
```py
from bytecodeparse import BytecodeParser

def a():
    b = 2
    return b

parser = BytecodeParser(a) # can also use a `code` instance as the argument
while stmt := parser.decompile_stmt():
    # stmt should be an AST-like object
    print(stmt)
```
**Output**
```
b = 2
return b
```
