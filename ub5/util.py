"""Utility module used for other modules."""

from __future__ import annotations

from collections.abc import Callable, Collection, Container, Iterable
from dataclasses import dataclass
from functools import update_wrapper, wraps
from typing import Any, ClassVar, Generic, Protocol, cast, runtime_checkable

from typing_extensions import ParamSpec, Self, TypeVar, TypeVarTuple, Unpack

T, S, Args, P = TypeVar("T", infer_variance=True), TypeVar("S"), TypeVarTuple("Args"), ParamSpec("P")


class PyMaLoError(Exception):
    """Common base class for all custom exceptions raised by the pymalo package."""


@runtime_checkable
class Copyable(Protocol):
    def copy(self) -> Self: ...


class IterableContainer(Iterable[T], Container[T], Protocol[T]):
    pass


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
        if isinstance(value, Copyable):

            def new() -> S:
                return value.copy()
        else:

            def new() -> S:
                return value

        object.__setattr__(self, methodname, update_wrapper(new, method))
        return new()

    return wrapper


@dataclass(frozen=True)
class CustomTest(Generic[Unpack[Args], T]):
    """Defines a custom test that will be run alongside the predefined tests.

    It's recommended to not construct these tests directly, but instead use the `custom_test` decorator.
    """

    input: tuple[Unpack[Args]]
    """A tuple containing the input values the function will be tested with."""

    output: T | Collection[T] | Callable[[T], bool]
    """The expected output value."""

    func: Callable[[Unpack[Args]], T]
    """The tested function."""

    name: str | None = None
    """The name of the test as displayed in the VPL output.
    
    If set to `None`, it will default to the input.
    """

    _from_decorator: bool = False

    _tests: ClassVar[list[CustomTest[Unpack[tuple[Any, ...]], Any]]] = []

    def __post_init__(self) -> None:
        self._tests.append(self)


def custom_test(
    input: tuple[object, ...] | object,
    output: object | Collection[object] | Callable[[object], bool],
    name: str | None = None,
) -> Callable[[Callable[P, T]], Callable[P, T]]:
    """Defines a custom test that will be run alongside the predefined tests.

    Use this by decorating the function you want to test with this and specify the input and expected output you want
    to use in the test. When you run the predefined tests in the VPL, your custom tests will then also be run and check
    whether the function returns the expected output given that input. You can add tests to any of your functions. To
    add multiple tests for a single function, you can just stack multiple decorators on top of each other.

    For example:
    ```
    @custom_test((0, 1, 2), 3)
    @custom_test((3, 4, 5), 12)
    def add(a: int, b: int, c: int) -> int:
        return b + c
    ```
    Will result in the VPL execution results also including these lines:
    ```
    add(0, 1, 2): passed
    add(3, 4, 5): error; returned 9 instead of 12
    ```

    The output can be specified in any of three ways:
    - A plain value: The test passes if the tested function returns a value that is equal to it.
    - A container of values: The test passes if the returned value is contained in it.
    - A function: The test passes if it returns `True` when called with the value the tested function returned.

    Args:
        input: A tuple containing the input values. If the input is a single value that isn't a tuple,
            it can also be passed directly.
        output: The expected output the tested function should return
        name: The name of this test that will be displayed in the VPL output. Defaults to the name of the function and
            passed parameters.
    Returns:
        A wrapper around the tested function that creates the custom test.
    Example:
        ```
        @custom_test(input=(1,), output=1)
        @custom_test(1, 1)
        @custom_test((1, 2, 3), 6, "my custom test")
        @custom_test(5, [4, 5, 6])
        @custom_test(5, lambda val: val % 5 == 0 and val // 5 == 1)
        def add(*args: int) -> int:
            return sum(args)
        ```
    """

    def inner(func: Callable[P, T]) -> Callable[P, T]:
        nonlocal input
        if not isinstance(input, tuple):
            input = (input,)
        CustomTest(input=input, output=output, name=name, func=cast(Any, func), _from_decorator=True)
        return func

    return inner
