"""Module containing first order logic utilities.

This module defines Python implementations of many commonly used concepts in first order logic like formulae,
structures, etc.

Much of the code here is rather complicated and not meant to be understood in full detail immediately. We recommend that
you primarily reference the explanations in docstrings and other course material before delving too deep into the
implementations of everything here.
"""

from __future__ import annotations

import re
from abc import ABC, abstractmethod
from collections.abc import Callable, Container, Iterable
from dataclasses import dataclass
from functools import wraps
from itertools import chain, islice
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, ClassVar, Generic, Literal, cast, overload

from typing_extensions import ParamSpec, TypeAlias, TypeGuard, TypeVar
from util import PyMaLoError

if TYPE_CHECKING:
    from collections.abc import Iterator, Mapping

    from util import IterableContainer

T = TypeVar("T", infer_variance=True)
P = ParamSpec("P")
Arity = TypeVar("Arity", Literal[0], Literal[1], Literal[2], Literal[3], Literal[4], Literal[5], int, default=int)
RawTruthConstant: TypeAlias = "bool | Literal[0, 1, '0', '1']"


class MismatchedArity(PyMaLoError, ValueError):
    """Indicates that a function or relation symbol was used with an incorrect number of arguments."""

    def __init__(self, symbol: Symbol[Any], symbol_args: tuple[TermExpr, ...]) -> None:
        super().__init__(f"Symbol {symbol} has arity {symbol.arity} but is called with {len(symbol_args)} arguments")


class IllegalName(PyMaLoError, ValueError):
    """Indicates that a symbol or name has been given an name that is not allowed."""

    def __init__(self, symbol_type: type[Symbol[Any] | Variable], name: str) -> None:
        super().__init__(f"The name `{name}` does not match the requirements for {symbol_type.__name__} names")


class NotInUniverse(PyMaLoError, ValueError):
    """Indicates that value is not contained in the universe of a structure it needs to be."""

    def __init__(
        self, occurrence: Literal["argument", "return", "assignment"], value: object, universe: IterableContainer[Any]
    ) -> None:
        universe_str = str(universe)
        if len(universe_str) > 20:
            universe_str = f"{universe_str:.20}..."
        super().__init__(f"{occurrence.capitalize()} value {value} is not contained in the universe {universe_str}")


# * ----------------------------------------------------- Symbols ------------------------------------------------------


@dataclass(frozen=True)
class Symbol(ABC, Generic[Arity]):
    """A relation or function symbol."""

    name: str
    """The name of the symbol.
    
    Must start with an uppercase ASCII letter or an underscore and then only contain ASCII letters, digits,
    underscores, and hyphens.
    """
    arity: int
    """The symbol's arity."""

    name_pattern: ClassVar = re.compile(r"[A-Z_][A-Za-z0-9_\-]*")

    def __post_init__(self) -> None:
        if not self.name_pattern.fullmatch(self.name) or self.arity < 0:
            raise IllegalName(type(self), self.name)

    def __str__(self) -> str:
        return f"{self.name}/{self.arity}"


@dataclass(frozen=True)
class FunctionSymbol(Symbol[Arity]):
    """A function symbol.

    Consists of the symbol's name and its arity.
    If an invalid name is passed to the constructor, `IllegalName` is raised.

    You can easily create terms from these function symbols (and other terms) by using the usual Python call operator.
    For example:
    ```
    f = FunctionSymbol("F", 2)
    x = Variable("$x")

    assert str(f(x, x)) == "F($x, $x)"
    ```

    A function symbol or arity `0` will automatically be converted into the term calling it with no arguments if it is
    encountered in a term or formula building context. That is, you do not need to write e.g. `c()` and can just use
    `c` as a term directly.
    """

    if TYPE_CHECKING:

        def __init__(self, name: str, arity: Arity) -> None: ...

    @overload
    def __call__(self: FunctionSymbol[Literal[0]]) -> FunctionTerm: ...
    @overload
    def __call__(self: FunctionSymbol[Literal[1]], t1: TermExpr, /) -> FunctionTerm: ...
    @overload
    def __call__(self: FunctionSymbol[Literal[2]], t1: TermExpr, t2: TermExpr, /) -> FunctionTerm: ...
    @overload
    def __call__(self: FunctionSymbol[Literal[3]], t1: TermExpr, t2: TermExpr, t3: TermExpr, /) -> FunctionTerm: ...
    @overload
    def __call__(
        self: FunctionSymbol[Literal[4]], t1: TermExpr, t2: TermExpr, t3: TermExpr, t4: TermExpr, /
    ) -> FunctionTerm: ...
    @overload
    def __call__(
        self: FunctionSymbol[Literal[5]], t1: TermExpr, t2: TermExpr, t3: TermExpr, t4: TermExpr, t5: TermExpr, /
    ) -> FunctionTerm: ...
    @overload
    def __call__(self: FunctionSymbol[int], *args: TermExpr) -> FunctionTerm: ...

    def __call__(self, *args: TermExpr) -> FunctionTerm:
        """Creates the term that expresses the function symbol's application to the given arguments.

        Raises:
            MismatchedArity: if the number of terms is not equal to the symbol's arity.
        Example:
            ```
            f, x = FunctionSymbol("F", 2), Variable("$x")
            assert str(f(x, x)) == "F($x, $x)"
            ```
        """
        return FunctionTerm(self, tuple(as_term(arg) for arg in args))

    @overload
    def __eq__(self, other: TermExpr) -> Equality: ...
    @overload
    def __eq__(self, other: FunctionSymbol) -> bool: ...

    def __eq__(self, other: TermExpr | FunctionSymbol) -> Equality | bool:  # type: ignore[reportIncompatibleMethodOverride]
        """Creates a `Formula` expressing the equality of the two terms, or performs the usual equality comparison.

        If either of the passed objects is not a term the objects are compared for equality as usual.
        If instead both are terms, then an `Equality` formula containing them is created. That object's `__bool__` will
        return true iff the usual equality comparison of the terms would return `True`. This means that you can use this
        method both to create formulas from terms and to compare them for equality as usual.
        """
        if is_term_expr(self) and is_term_expr(other):
            return Equality(as_term(cast(TermExpr, self)), as_term(other))
        elif isinstance(other, FunctionSymbol):
            return self.name == other.name and self.arity == other.arity
        else:
            return NotImplemented


@dataclass(frozen=True)
class RelationSymbol(Symbol[Arity]):
    """A relation symbol.

    Consists of the symbol's name and its arity.
    If an invalid name is passed to the constructor, `IllegalName` is raised.

    You can easily create formulas from these relation symbols (and other terms) by using the Python call operator.
    For example:
    ```
    R = RelationSymbol("R", 2)
    x = Variable("$x")

    assert str(R(x, x)) == "R($x, $x)"
    ```
    """

    if TYPE_CHECKING:

        def __init__(self, name: str, arity: Arity) -> None: ...

    @overload
    def __call__(self: RelationSymbol[Literal[0]]) -> RelationFormula: ...
    @overload
    def __call__(self: RelationSymbol[Literal[1]], t1: TermExpr, /) -> RelationFormula: ...
    @overload
    def __call__(self: RelationSymbol[Literal[2]], t1: TermExpr, t2: TermExpr, /) -> RelationFormula: ...
    @overload
    def __call__(self: RelationSymbol[Literal[3]], t1: TermExpr, t2: TermExpr, t3: TermExpr, /) -> RelationFormula: ...
    @overload
    def __call__(
        self: RelationSymbol[Literal[4]], t1: TermExpr, t2: TermExpr, t3: TermExpr, t4: TermExpr, /
    ) -> RelationFormula: ...
    @overload
    def __call__(
        self: RelationSymbol[Literal[5]], t1: TermExpr, t2: TermExpr, t3: TermExpr, t4: TermExpr, t5: TermExpr, /
    ) -> RelationFormula: ...
    @overload
    def __call__(self: RelationSymbol[int], *args: TermExpr) -> RelationFormula: ...

    def __call__(self, *args: TermExpr) -> RelationFormula:
        """Creates the formula that expresses the relation symbol's application to the given arguments.

        Raises:
            MismatchedArity: if the number of terms is not equal to the symbol's arity.
        Example:
            ```
            R, x = RelationSymbol("R", 2), Variable("$x")
            assert str(R(x, x)) == "R($x, $x)"
            ```
        """
        return RelationFormula(self, tuple(as_term(arg) for arg in args))


# * ---------------------------------------------------- Structures ----------------------------------------------------


def _constant_function(value: T) -> Callable[[], T]:
    """Returns a constant function that always returns the passed value."""

    # We cannot move the function definition out of this scope. The `value` is captured as a cell var, not by value.
    # That means that if the defn is in a scope where `value` mutates it will not be correct. By first moving the
    # variable to this new scope and then binding to that we effectively get pass by value behavior.

    return lambda: value


def _unwrapped_contains(container: Container[T]) -> Callable[[*tuple[T, ...]], bool]:
    """Creates a function that checks containment of an unwrapped tuple in a container.

    If a single value is given, the single argument is tested instead, not a unary tuple containing it.
    """

    def inner(*args: T) -> bool:
        return (args[0] if len(args) == 1 else args) in container

    return inner


@dataclass(frozen=True)
class Structure(Generic[T]):
    """A structure consisting of a universe and interpretations for a set of relation and function variables.

    The structures universe can be any type that is both `Iterable` and a `Container`. For example, a `set`, a `list`,
    a `tuple`, or similar. In general, you should prefer using a `set` since that will offer much better performance for
    all common operations. You can also create infinite structures by passing a value with algorithmic `__iter__` and
    `__next__` methods.

    The `relations` and `functions` attributes contain the interpretations for the relation and function symbols the
    structure interprets. These are ordinary Python callables and can be called directly.

    For example:
    ```
    R, f = RelationSymbol("R", 2), FunctionSymbol("F", 1)

    some_structure = Structure({1, 2, 3}, {R: lambda a, b: a <= b, f: lambda a: a + 1})
    assert some_structure.relations[R](1, 2)
    assert some_structure.functions[f](2) == 3
    ```
    """

    universe: IterableContainer[T]
    """The collection of values in the structure."""
    relations: Mapping[RelationSymbol[Any], Callable[..., bool]]
    """Interpretations for all relations this structure defines."""
    functions: Mapping[FunctionSymbol[Any], Callable[..., T]]
    """Interpretations for all functions this structure defines."""

    def __init__(
        self,
        universe: IterableContainer[T],
        interpretations: Mapping[Symbol[Any], Callable[..., bool | T] | T | Container[T | tuple[T, ...]] | bool],
    ) -> None:
        """Constructs a structure using the given universe and interpretations.

        If the passed universe is a `set` or `list` an immutable copy of it will be created. Otherwise, the user must
        ensure not mutating it.
        The interpreted functions must always return values contained in the universe if called with values from it.
        If that is not the case, a `NotInUniverse` error will be raised when the function is invoked (i.e. not during
        the `Structure` constructor call, but at any later point).
        Similarly, the interpreted relations must always return a `bool` if called with values from the universe.
        Otherwise, a `TypeError` is raised when it is called.

        Args:
            universe: An `Iterable` and `Container`, e.g. a `set`, `list`, `tuple`, etc.
            interpretations: A mapping from symbols to their interpretations. If a value in the mapping is a callable,
                it will be used directly as the interpretation. If it is a constant value and interprets a nullary
                symbol, it will be converted to a nullary function returning that value. And finally, if it is a
                `Container` (e.g. `set`) and interprets a relation symbol, it will be converted to a function
                checking membership in it.
        Examples:
            Given the symbols `c, f, R = FunctionSymbol("C", 0), FunctionSymbol("F", 1), RelationSymbol("R", 2)` and
            universe `u = {1, 2, 3, 4, 5}` the following are equivalent:
            ```
            Structure(u, {c: 1, R: {(1, 2), (2, 3), (3, 4), (4, 5)}})
            Structure(u, {c: lambda: 1, R: lambda n, m: n + 1 == m})
            ```

            This creates a structure containing the numbers 0, ..., 9 and the usual addition operation capped at 9:
            ```
            add = FunctionSymbol("Add")
            digits = Structure(range(10), {add: lambda a, b: min(9, a + b)})
            ```

            This creates a simple directed graph where vertex `"v2"` is the successor of every other vertex and no other
            edges exist:
            ```
            E = RelationSymbol("E")
            graph = Structure({"v1", "v2", "v3", "v4"}, {E: lambda u, v: v == "v2" and u != "v2"})
            ```
        """
        relations = dict[RelationSymbol, Callable[..., Any]]()
        functions = dict[FunctionSymbol, Callable[..., Any]]()
        for symbol, obj in interpretations.items():
            if isinstance(symbol, FunctionSymbol):
                if symbol.arity == 0 and obj in universe:
                    functions[symbol] = _constant_function(obj)
                elif callable(obj):
                    functions[symbol] = obj
                else:
                    raise TypeError
            elif isinstance(symbol, RelationSymbol):
                if symbol.arity == 0 and isinstance(obj, bool):
                    relations[symbol] = _constant_function(obj)
                elif callable(obj):
                    relations[symbol] = obj
                elif isinstance(obj, Container):
                    relations[symbol] = _unwrapped_contains(obj)
                else:
                    raise TypeError
            else:
                raise TypeError
        for symbol, func in relations.items():
            relations[symbol] = self._checked_values(func, "relation")
        for symbol, func in functions.items():
            functions[symbol] = self._checked_values(func, "function")

        if isinstance(universe, list):
            universe = tuple(universe)
        elif isinstance(universe, set):
            universe = frozenset(universe)
        object.__setattr__(self, "universe", universe)
        object.__setattr__(self, "relations", MappingProxyType(relations))
        object.__setattr__(self, "functions", MappingProxyType(functions))

    def __contains__(self, obj: object) -> bool:
        """Checks containment in the structure's universe."""
        return obj in self.universe

    def __iter__(self) -> Iterator[T]:
        """Iterates over the structure's universe."""
        return iter(self.universe)

    def __str__(self) -> str:
        universe_elements = ", ".join(str(item) for item in islice(self.universe, 3))
        universe = f"{{{universe_elements}{', ...' if islice(self.universe, 3, 4) else ''}}}"
        symbols = f"{{{', '.join(str(sym) for sym in chain(self.functions, self.relations))}}}"
        return f"Structure({universe}, {symbols})"

    def _checked_values(self, func: Callable[P, T], func_type: Literal["relation", "function"]) -> Callable[P, T]:
        """Wraps the passed function so that it confirms all occurring values are in the structure's universe."""

        @wraps(func)
        def inner(*args: P.args, **kwargs: P.kwargs) -> T:
            for value in chain(args, kwargs.items()):
                if value not in self.universe:
                    raise NotInUniverse("argument", value, self.universe)
            result = func(*args, **kwargs)
            if func_type == "function":
                if result not in self.universe:
                    raise NotInUniverse("return", result, self.universe)
            else:
                if not isinstance(result, bool):
                    raise TypeError
            return result

        return inner

    @property
    def symbols(self) -> set[Symbol]:
        """The set of symbols the structure interprets."""
        return cast(set[Symbol], self.relations.keys() | self.functions.keys())


# * ------------------------------------------------------ Terms -------------------------------------------------------


class Term(ABC):
    """A term in a first order formula.

    Can either be a variable or a function symbol applied to a tuple of other terms.
    While constant symbols can be used as though they are terms in certain contexts, they will automatically be
    converted to the application of them to a tuple of no arguments. Anything else expecting a term does not need to
    consider these as a special case.

    You can use the Python call operator to easily create terms from symbols and variables. For example, if `f` is a
    binary function symbol, `g` unary, `c` a constant, and `x` a variable, then `f(c, g(y))` creates the term
    `FunctionTerm(f, (FunctionTerm(c, ()), FunctionTerm(g, (y,))))`, written as "F(C, G($y))".
    """

    def __eq__(self, value: TermExpr, /) -> Equality:  # type: ignore[reportIncompatibleMethodOverride]
        """Creates a `Formula` expressing the equality of the two terms.

        The created object's `__bool__` will return true iff the usual equality comparison of the terms would return
        `True`. This means that you can use this method both to create formulas from terms and to compare them for
        equality as usual.

        Note that you cannot use the != operator similarly. It only performs the actual inequality comparison. If you
        want to create the corresponding formula, you must use `~(term == other_term)` instead.
        """
        assert isinstance(self, Term)
        return Equality(self, as_term(value)) if is_term_expr(value) else NotImplemented

    @abstractmethod
    def __str__(self) -> str: ...

    @property
    @abstractmethod
    def variables(self) -> set[Variable]:
        """The set of variables occurring in the term."""
        ...

    @property
    @abstractmethod
    def symbols(self) -> set[Symbol]:
        """The set of symbols occurring in the term."""
        ...


@dataclass(frozen=True, eq=False, unsafe_hash=True)
class Variable(Term):
    """A variable in a first order formula."""

    name: str
    """The name of the variable.
    
    Always starts with a "$" and then contains any number of upper or lower case ASCII letters, digits,
    underscores, or hyphens.
    """

    name_pattern: ClassVar = re.compile(r"\$[A-Za-z0-9_\-]+")

    def __init__(self, name: str) -> None:
        """Creates a Variable.

        Args:
            name: The name of the variable. If it does not start with a "$", it will be prepended to the given name
        Raises:
            IllegalName: If the name is not a legal variable name.
        """
        if not name or name[0] != "$":
            name = f"${name}"
        if not self.name_pattern.fullmatch(name):
            raise IllegalName(type(self), name)
        object.__setattr__(self, "name", name)

    def __str__(self) -> str:
        return self.name

    @property
    def variables(self) -> set[Variable]:
        return {self}

    @property
    def symbols(self) -> set[Symbol]:
        return set()


@dataclass(frozen=True, eq=False, unsafe_hash=True)
class FunctionTerm(Term):
    """A term expressing the application of a function symbol to other terms.

    The constructor will raise a `MismatchedArity` if the number of terms is not equal to the symbol's arity.
    """

    function: FunctionSymbol[Any]
    """The function symbol that is being applied."""
    arguments: tuple[Term, ...]
    """The terms that the function symbol is applied to."""

    def __post_init__(self) -> None:
        if len(self.arguments) != self.function.arity:
            raise MismatchedArity(self.function, self.arguments)

    def __str__(self) -> str:
        return f"{self.function.name}({', '.join(str(arg) for arg in self.arguments)})"

    @property
    def variables(self) -> set[Variable]:
        return set[Variable]().union(*(arg.variables for arg in self.arguments))

    @property
    def symbols(self) -> set[Symbol]:
        return set[Symbol]([self.function]).union(*(arg.symbols for arg in self.arguments))


TermExpr: TypeAlias = "Term | FunctionSymbol[Literal[0]]"
"""The type of values that can occur in certain formula building contexts.

When writing out a formula, we often want to use constant (nullary function) symbols as terms directly without calling
them with no arguments. Many utility functions related to building terms and formulas accept these and automatically
convert them to the proper function term. These are annotated by `TermExpr` instead of just a plain `Term`.
"""


def is_term_expr(obj: object) -> TypeGuard[TermExpr]:
    """Checks whether an object is a valid term or constant symbol."""
    return isinstance(obj, Term) or (isinstance(obj, FunctionSymbol) and obj.arity == 0)


def as_term(expr: TermExpr) -> Term:
    """Converts constant symbols to the corresponding term."""
    return expr() if isinstance(expr, FunctionSymbol) else expr


# * ----------------------------------------------------- Formulas -----------------------------------------------------


class Formula(ABC):
    """A first order logic formula.

    Behaves very similarly to the `Formula` class from the `propositional` module. You also cannot create these
    `Formula` objects directly but must use the appropriate subclass for each type of formula. These are:
    - `Equality`: A formula expressing the equality of two terms, e.g. `f($x) = $y`.
    - `RelationFormula`: A formula applying a relation symbol to some terms, e.g. `R($x, $y, $z)`.
    - `TruthConstant`: An atomic boolean constant, e.g. `1`.
    - `Exists` and `Forall`: A formula applying a first order quantifier to some subformula, e.g. `ex $x R($x, $x)`.
    - `Not`, `Or`, `And`, `Impl`: The usual boolean connectives, e.g. `(0 \\/ (f($x) = c() -> R($y, $z)))`.

    You can use the Python bitwise operators to combine formulas into more complex ones. You can also use the equality
    comparison to create atomic equality formulas. For example:
    ```
    f, c, x, R = FunctionSymbol("F", 2), FunctionSymbol("C", 0), Variable("x"), RelationSymbol("R", 1)
    some_formula = R(x) & (f(c, x) == x)
    assert some_formula == And(
        first=RelationFormula(R, (x,)),
        second=Equality(FunctionTerm(f, (c, x)), x),
    )
    ```
    Note that the parentheses around the equality are necessary since Python bitwise operators bind stronger than
    comparisons.

    Accessing subformulas follows the same structure as for propositional formulas. Note that there are no `label`
    attributes in first order `Formula` instances. If you want to inspect what kind of formula an object is, use the
    `isinstance(some_formula, SomeFormulaType)` function or a match statement like this:
    ```
    match formula:
        case And(first, second):
            ...
        case Forall(var, inner):
            ...
    ```
    which is equivalent to:
    ```
    if isinstance(formula, And):
        first, second = formula.first, formula.second
        ...
    elif isinstance(formula, Forall):
        var, inner = formula.variable, subformula.subformula
        ...
    ```
    """

    @staticmethod
    def _as_formula(value: Formula | RawTruthConstant) -> Formula:
        return value if isinstance(value, Formula) else TruthConstant(value)

    def __invert__(self) -> Neg:
        """Returns the negated formula."""
        return Neg(self)

    def __or__(self, other: Formula | RawTruthConstant, /) -> Or:
        """Returns the disjunction of both formulae."""
        return Or(self, self._as_formula(other))

    def __ror__(self, other: Formula | RawTruthConstant, /) -> Or:
        """Returns the disjunction of both formulae."""
        return Or(self._as_formula(other), self)

    def __and__(self, other: Formula | RawTruthConstant, /) -> And:
        """Returns the conjunction of both formulae."""
        return And(self, self._as_formula(other))

    def __rand__(self, other: Formula | RawTruthConstant, /) -> And:
        """Returns the conjunction of both formulae."""
        return And(self._as_formula(other), self)

    @abstractmethod
    def __str__(self) -> str: ...

    @property
    @abstractmethod
    def free_variables(self) -> set[Variable]:
        """The set of variables occurring freely in the formula."""
        ...

    @property
    @abstractmethod
    def symbols(self) -> set[Symbol]:
        """The set of function and relation symbols in the formula."""
        ...


class AtomicFormula(Formula, ABC):
    """An atomic first order formula.

    Can either be an `Equality`, a `RelationFormula`, or a `TruthConstant`.
    """


@dataclass(frozen=True)
class Equality(AtomicFormula):
    """A first order formula expressing the equality of two terms."""

    first: Term
    """The left-hand side of the equality."""
    second: Term
    """The right-hand side of the equality."""

    def __init__(self, first: TermExpr, second: TermExpr) -> None:
        for name, val in (("first", first), ("second", second)):
            if isinstance(val, FunctionSymbol):
                if val.arity != 0:
                    raise TypeError
                val = val()
            object.__setattr__(self, name, val)

    def __bool__(self) -> bool:
        """An `Equality` formula is truthy if both terms are equal according to regular dataclass semantics.

        You can use `f(a, b, c) == some_term` both as a way to build a formula and to actually compare terms.
        """
        if isinstance(self.first, Variable) and isinstance(self.second, Variable):
            return self.first.name == self.second.name
        elif isinstance(self.first, FunctionTerm) and isinstance(self.second, FunctionTerm):
            return (
                self.first.function.name == self.second.function.name and self.first.arguments == self.second.arguments
            )
        else:
            return False

    def __str__(self) -> str:
        return f"{self.first} = {self.second}"

    @property
    def free_variables(self) -> set[Variable]:
        return self.first.variables | self.second.variables

    @property
    def symbols(self) -> set[Symbol]:
        return self.first.symbols | self.second.symbols


@dataclass(frozen=True)
class RelationFormula(AtomicFormula):
    """A formula that applies a relation symbol to some number of terms.

    The constructor will raise a `MismatchedArity` if the number of terms is not equal to the symbol's arity.
    """

    relation: RelationSymbol[Any]
    """The relation symbol that is being applied."""
    arguments: tuple[Term, ...]
    """The terms that the relation symbol is applied to."""

    def __post_init__(self) -> None:
        if len(self.arguments) != self.relation.arity:
            raise MismatchedArity(self.relation, self.arguments)

    def __str__(self) -> str:
        return f"{self.relation.name}({', '.join(str(arg) for arg in self.arguments)})"

    @property
    def free_variables(self) -> set[Variable]:
        return set[Variable]().union(*(arg.variables for arg in self.arguments))

    @property
    def symbols(self) -> set[Symbol]:
        return set[Symbol]([self.relation]).union(*(arg.symbols for arg in self.arguments))


@dataclass(frozen=True)
class TruthConstant(AtomicFormula):
    """An atomic truth constant.

    Note that these represent the direct Truth values `0` and `1`, not first order constant symbols.
    """

    value: bool
    """The truth value of the constant."""

    def __init__(self, value: RawTruthConstant) -> None:
        """Constructs a `TruthConstant` from the given Python equivalent.

        Accepts any of `False`/`True`, `0`/`1`, or `"0"`, `"1"`, always converting them to `bool`.
        """
        object.__setattr__(self, "value", bool(int(value)))

    def __str__(self) -> str:
        return str(int(self.value))

    @property
    def free_variables(self) -> set[Variable]:
        return set()

    @property
    def symbols(self) -> set[Symbol]:
        return set()


@dataclass(frozen=True)
class Neg(Formula):
    """A first order negation formula."""

    subformula: Formula
    """The negated subformula."""

    def __str__(self) -> str:
        return f"~{self.subformula}"

    @property
    def free_variables(self) -> set[Variable]:
        return self.subformula.free_variables

    @property
    def symbols(self) -> set[Symbol]:
        return self.subformula.symbols


@dataclass(frozen=True)
class BinaryFormula(Formula, ABC):
    """A binary boolean connective for first order formulas.

    Can either be an `Or`, an `And`, or an `Impl`.
    """

    first: Formula
    """The left-hand side subformula."""
    second: Formula
    """The right-hand side subformula."""

    _name: ClassVar[Literal["\\/", "/\\", "->"]]

    def __str__(self) -> str:
        return f"({self.first} {self._name} {self.second})"

    @property
    def free_variables(self) -> set[Variable]:
        return self.first.free_variables | self.second.free_variables

    @property
    def symbols(self) -> set[Symbol]:
        return self.first.symbols | self.second.symbols


class Or(BinaryFormula):
    """A first order disjunction."""

    _name = "\\/"


class And(BinaryFormula):
    """A first order conjunction."""

    _name = "/\\"


class Impl(BinaryFormula):
    """A first order implication."""

    _name = "->"


@dataclass(frozen=True)
class Quantifier(Formula, ABC):
    """The application of a first order quantifier to a subformula."""

    variable: Variable
    """The variable bound by this quantifier."""
    subformula: Formula
    """The subformula in which the variable is bound."""

    _test: ClassVar[Callable[[Iterable[object]], bool]]
    _name: ClassVar[str]

    def __str__(self) -> str:
        return f"{self._name} {self.variable} {self.subformula}"

    @property
    def free_variables(self) -> set[Variable]:
        return self.subformula.free_variables - {self.variable}

    @property
    def symbols(self) -> set[Symbol]:
        return self.subformula.symbols


class Exists(Quantifier):
    """A formula using an existential first oder quantifier."""

    _test = any
    _name = "ex"


class Forall(Quantifier):
    """A formula using a universal first oder quantifier."""

    _test = all
    _name = "fa"


# * ----------------------------------------------------- Semantics ----------------------------------------------------


Assignment = dict[Variable, T]
"""An assignment of free variables to values in some structure.

These just are plain Python dictionaries with keys that are `Variable` instances (not their string names) that are
mapped to some value in a structure. For example:
```
some_assignment = {
    Variable("x"): 1,
    Variable("y"): 2,
    Variable("z"): 3,
}
```
"""


@dataclass(frozen=True)
class Interpretation(Generic[T]):
    """A first order logic interpretation.

    Consists of a structure and corresponding interpretation. The interpretation must map variables to values that
    are contained in the structure's universe. The constructor raises a `NotInUniverse` if that is not the case.
    """

    structure: Structure[T]
    """The structure this interpretation uses."""
    assignment: Assignment[T]
    """The variable assignment this interpretation uses."""

    def __post_init__(self) -> None:
        for value in self.assignment.values():
            if value not in self.structure.universe:
                raise NotInUniverse("assignment", value, self.structure.universe)

    def __str__(self) -> str:
        assignment = f"{{{', '.join(f'{var.name}: {val}' for var, val in self.assignment.items())}}}"
        return f"Interpretation({self.structure}, {assignment})"

    @property
    def symbols(self) -> set[Symbol]:
        """The set of symbols this interpretation interprets."""
        return self.structure.symbols
