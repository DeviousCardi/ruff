# Display of recursive types

```toml
[environment]
python-version = "3.12"
```

## Binder precedence

A recursive binder extends over its whole body and binds less tightly than union and intersection.
It needs no parentheses at the top level or within brackets and parameter lists, where the enclosing
delimiters already mark its boundary. As an operand of union, intersection, or negation, it is
parenthesized to keep those operations outside the binder.

The loop builds a recursive tuple. After narrowing out the initial integer, the remaining type shows
the same binder in each enclosing type expression.

```py
from typing import Callable
from ty_extensions import Intersection, Not
from ty_extensions._internal import TypeOf

def show(n: int):
    recursive = 0
    for _ in range(n):
        recursive = (recursive,)
    if isinstance(recursive, tuple):
        reveal_type(recursive)  # revealed: μa0. tuple[Literal[0] | a0, ...]
        def contexts[T](
            array: list[TypeOf[recursive]],
            pair: tuple[TypeOf[recursive], TypeOf[recursive]],
            union: TypeOf[recursive] | int,
            intersection: Intersection[TypeOf[recursive], T],
            complement: Not[TypeOf[recursive]],
            callback: Callable[[TypeOf[recursive]], TypeOf[recursive]],
        ):
            reveal_type(array)  # revealed: list[μa0. tuple[Literal[0] | a0, ...]]
            reveal_type(pair)  # revealed: tuple[μa0. tuple[Literal[0] | a0, ...], μa0. tuple[Literal[0] | a0, ...]]
            reveal_type(union)  # revealed: (μa0. tuple[Literal[0] | a0, ...]) | int
            reveal_type(intersection)  # revealed: (μa0. tuple[Literal[0] | a0, ...]) & T@contexts
            reveal_type(complement)  # revealed: ~(μa0. tuple[Literal[0] | a0, ...])
            reveal_type(callback)  # revealed: (μa0. tuple[Literal[0] | a0, ...], /) -> μa0. tuple[Literal[0] | a0, ...]
```
