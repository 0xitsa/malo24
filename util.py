"""Utility module used for other modules."""

from __future__ import annotations

from functools import update_wrapper, wraps
from typing import TYPE_CHECKING, Protocol, Self, TypeVar, runtime_checkable

if TYPE_CHECKING:
    from collections.abc import Callable

T = TypeVar("T")
S = TypeVar("S")


@runtime_checkable
class Copiable(Protocol):
    def copy(self) -> Self: ...


def memoize(method: Callable[[T], S]) -> Callable[[T], S]:
    """A method decorator for parameterless methods of immutable classes that
    memoizes the return value to avoid recalculation.

    Parameters:
        method: method to modify.

    Returns:
        The given method, modified so that after its first execution, its
        functionality is replaced with simply returning the value calculated by
        its first execution. If the value calculated by the given method has a
        `copy()` method, then instead of returning this value, each
        execution of the returned method, including the first one, makes a fresh
        call to this `copy()` method and returns the result.
    """
    methodname = method.__name__

    @wraps(method)
    def wrapper(self: T) -> S:
        value = method(self)
        if isinstance(value, Copiable):

            def new() -> S:
                return value.copy()
        else:

            def new() -> S:
                return value

        object.__setattr__(self, methodname, update_wrapper(new, method))
        return new()

    return wrapper
