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

The initial value contributes `int` to the recursive type. Intersections and negations distribute
over this alternative before the result is displayed.

```py
from typing import Callable
from ty_extensions import Intersection, Not
from ty_extensions._internal import TypeOf

class C:
    def __init__(self):
        self.value = 0

    def update(self):
        self.value = (self.value,)

recursive = C().value
reveal_type(recursive)  # revealed: μa0. tuple[a0] | int

def contexts[T](
    array: list[TypeOf[recursive]],
    pair: tuple[TypeOf[recursive], TypeOf[recursive]],
    union: TypeOf[recursive] | int,
    intersection: Intersection[TypeOf[recursive], T],
    complement: Not[TypeOf[recursive]],
    callback: Callable[[TypeOf[recursive]], TypeOf[recursive]],
):
    reveal_type(array)  # revealed: list[μa0. tuple[a0] | int]
    reveal_type(pair)  # revealed: tuple[μa0. tuple[a0] | int, μa0. tuple[a0] | int]
    reveal_type(union)  # revealed: (μa0. tuple[a0] | int) | int
    reveal_type(intersection)  # revealed: (int & T@contexts) | ((μa0. tuple[a0 | int]) & T@contexts)
    reveal_type(complement)  # revealed: ~(μa0. tuple[a0 | int]) & ~int
    reveal_type(callback)  # revealed: (μa0. tuple[a0] | int, /) -> μa0. tuple[a0] | int
```
