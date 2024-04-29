"""Module containing propositional logic utilities.

This module defines Python implemenatations of many commonly used concepts in propositional logic like formulae,
interpretations, truth tables, etc. Objects defined here can generally be used in many different but equivalent
ways for convenience.

Much of the code here is rather complicated and not meant to be understood in full detail immediatly. We recommend that
you primarily reference the explanations in docstrings and other course material before delving too deep into the
implementations of everything here.
"""

from __future__ import annotations

import re
import string
from abc import ABC, abstractmethod
from collections.abc import Mapping
from dataclasses import InitVar, dataclass, field
from functools import cached_property
from itertools import pairwise
from typing import TYPE_CHECKING, ClassVar, Final, Literal, TypeAlias, cast, overload

from util import memoize

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator

ConstantVal = Literal["0", "1"]
UnaryOperator = Literal["~"]
BinaryOperator = Literal["\\/", "/\\", "->"]
Operator = ConstantVal | UnaryOperator | BinaryOperator

symbol_pattern = re.compile(r"[A-Z_][a-zA-Z_\-0-9]*")
symbol_first_char = set(string.ascii_uppercase + "_")
symbol_other_chars = set(string.ascii_letters + string.digits + "_-")


class Formula(ABC):
    """A propositional logic formula in tree representation.

    You cannot instantiate Formula objects directly, rather there is a subclass for each formula type that creates a
    formula of that type. The formula types are:
    - `Symbol` and `Constant`: the leaves of a formula tree, corresponding to propositional symbols and the 0 and 1
        truth value constants.
    - `Neg`: the only unary operator, representing negated formulae. Its child is available on the `subformula`
        attribute.
    - `Or`, `And`, and `Impl`: the binary operators representing disjunction, conjunction, and implication. Their
        subformulae are available on the `first` and `second` attributes.

    E.g. To create the Formula for `A or B` you need to use `Or(Symbol("A"), Symbol("B"))` and the Python
    representation of `(A -> B) and (not C)` is
    ```py
    And(
        first=Impl(
            first=Symbol("A"),
            second=Symbol("B"),
        ),
        second=Neg(
            subformula=Symbol("C"),
        ),
    )
    ```

    There are two methods to more easily create `Formula` objects rather than manually invoking the constructors several
    times:
    - Write the formula in its string representation and then use `Formula.parse()`. Note the exact format specification
        required of these strings given in the `.parse()` method and lecture slides.
    - Use Python's bitwise operators to combine `Formula` objects and strings for symbol names or constant. Forexample,
        `(Symbol("A") | Symbol("B")) & ~Symbol("C")` creates the same object as above. You can also use plain strings
        to specify symbols or constants, but only in binary operators and only if the other argument to the operator is
        a `Formula` object. E.g. `"A" | ("0" & Symbol("B"))` works, but `("A" | "0") & Symbol("B")` does not since both
        sides of `"A" | "0"` are plain strings. This is an unfortunate limitation in Python and will always raise a
        `TypeError`. There unfortunately also does not exist a bitwise implication operator, so these formulae will
        always have to be created another way.

    The operator at the top-most level of a formula is stored in its `label` attribute. That is, the above example's
    `formula.label` is `"/\\"` since it is a formula representing the conjunction of two formulae. For `Formula` objects
    representing symbols or constants this attribute will instead contain that symbol's name or the constant value.

    Either the `subformula` or the `first` and `second` attributes contain the direct subformulae of a formula.
    Unary operators use `subformula`, binary operators `first` and `second`. Attempting to access one of these
    attributes on a `Formula` that is not the correct type will raise an `AttributeError`. E.g. `some_and.subformula`
    will raise it if `some_and` is an `And` object. Similarly, `Constant` and `Symbol` formulae will always raise
    these errors.

    For example, if you have a formula `my_formula` you can print out what kind of operator it is with
    `print(my_formula.label)` and what it's left subformula is with `print(my_formula.first)`.
    """

    @overload
    @staticmethod
    def from_parts(label: str | ConstantVal) -> Formula: ...
    @overload
    @staticmethod
    def from_parts(label: UnaryOperator, first: Formula) -> Formula: ...
    @overload
    @staticmethod
    def from_parts(label: BinaryOperator, first: Formula, second: Formula) -> Formula: ...

    @staticmethod
    def from_parts(
        label: str | ConstantVal | UnaryOperator | BinaryOperator,
        first: Formula | None = None,
        second: Formula | None = None,
    ) -> Formula:
        match label, first, second:
            case "0" | "1", None, None:
                return Constant(label)
            case str(), None, None:
                return Symbol(label)
            case "~", Formula(), None:
                return Neg(first)
            case "\\/", Formula(), Formula():
                return Or(first, second)
            case "/\\", Formula(), Formula():
                return And(first, second)
            case "->", Formula(), Formula():
                return Impl(first, second)
            case _:
                raise TypeError

    @abstractmethod
    def __str__(self) -> str: ...

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one."""
        return isinstance(other, Formula) and str(self) == str(other)

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def _preprocess(other: Formula | str) -> Formula:
        if other in ("0", "1"):
            return Constant(other)
        elif isinstance(other, str):
            return Symbol(other)
        else:
            return other

    def __invert__(self) -> Formula:
        """Returns the negated formula."""
        return Neg(self)

    def __or__(self, other: Formula | str, /) -> Formula:
        """Returns the disjunction of both formulae."""
        return Or(self, self._preprocess(other))

    def __ror__(self, other: Formula | str, /) -> Formula:
        """Returns the disjunction of both formulae."""
        return Or(self._preprocess(other), self)

    def __and__(self, other: Formula | str, /) -> Formula:
        """Returns the conjunction of both formulae."""
        return And(self, self._preprocess(other))

    def __rand__(self, other: Formula | str, /) -> Formula:
        """Returns the conjunction of both formulae."""
        return And(self._preprocess(other), self)

    @cached_property
    @abstractmethod
    def symbols(self) -> frozenset[Symbol]:
        """All propositional symbols occuring in this formula.

        This includes all symbols in any subformulae, but every occurring symbol only once. For example, the
        Formula object corresponding to `(A /\\ B) -> (B /\\ C)` contains symbols `A, B, C`.
        """
        ...

    @cached_property
    @abstractmethod
    def operators(self) -> frozenset[Operator]:
        """All operators occuring in this formula.

        This includes negation "~", the binary operators "\\/", "/\\", "->", and the constants "0", "1". Any operator
        occurring in any subformula is included, but every operator at most once. For example, the operators in the
        formula `(0 /\\ A) \\/ (1 -> ~B)` are `0, /\\, \\/, 1, ~`.
        """
        ...

    Token: TypeAlias = 'Symbol | Operator | Literal["(", ")"]'

    @staticmethod
    def _tokenize(string: str) -> Iterator[Token]:
        """Splits the passed string into a list of the individual symbols, operators, and parentheses in it."""
        iterator = pairwise(string + " ")  # we need one character of lookahead for binary operators and symbol names
        while True:
            try:
                match next(iterator):
                    # skip spaces, effectively stripping them from the output
                    case " ", _:
                        continue

                    # single char tokens can be passed through
                    case "0" | "1" | "~" | "(" | ")" as single_char_op, _:
                        yield single_char_op

                    # two char tokens are combined
                    case ("\\", "/") | ("/", "\\") | ("-", ">") as two_char_op:
                        yield cast(Literal["\\/", "/\\", "->"], "".join(two_char_op))
                        next(iterator)  # skip the second char of the operator

                    # for symbol names we ned to combine them until we find a non-symbol-name char
                    case symbol_name_start, lookahead if symbol_name_start in symbol_first_char:  #
                        symbol_name = [symbol_name_start]
                        try:
                            # take from lookahead since the char that ends the symbol name is the first char after it
                            # i.e. it needs to be the next one yielded in the outer loop
                            while lookahead in symbol_other_chars:
                                symbol_name.append(lookahead)
                                _, lookahead = next(iterator)
                        except StopIteration:
                            pass
                        yield Symbol("".join(symbol_name))

                    # if it's not one of the above combinations then it's not a valid token
                    case first, second:
                        raise ValueError(f"Invalid characters '{first}{second}'")
            except StopIteration:
                return

    @staticmethod
    def _parse_prefix(tokens: list[Token]) -> tuple[Formula, list[Token]]:
        """Parses a prefix of the given tokenized string into a formula.

        Parameters:
            string: string to parse, split into single characters.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix that is a symbol name (e.g. `X123`) or a unary operator followed by a symbol
            name, then the parsed prefix will include that entire symbol name (not just a part of it, such as `X1`).

        Raises:
            ValueError: If no prefix of the given string is a valid string representation of a formula.
        """
        match tokens:
            # empty tokens list means the formula was empty
            case []:
                raise ValueError("The empty string is not a valid formula")

            # constants and symbols can be handled directly
            case (("0" | "1" as value), *rest):
                return Constant(value), rest
            case Symbol() as symbol, *rest:
                return symbol, rest

            # for negated formulae we just parse the rest of the input and negate it in the formula tree
            case "~", *rest:
                subformula, rest = Formula._parse_prefix(rest)
                return Neg(subformula), rest

            # for binary operators we assert that they have the form `(formula binop formula)`
            # and create the tree accordingly
            case "(", *rest:
                first_subformula, rest = Formula._parse_prefix(rest)
                operator, *rest = rest
                if operator not in ("\\/", "/\\", "->"):
                    raise ValueError("Invalid binary operator")
                second_subformula, rest = Formula._parse_prefix(rest)
                closing_parens, *rest = rest
                if closing_parens != ")":
                    raise ValueError("Invalid parentheses")
                return Formula.from_parts(operator, first_subformula, second_subformula), rest

            # otherwise the formula is invalid since it starts with a binary operator or ')'
            case _:
                raise ValueError("Invalid formula")

    @staticmethod
    def parse(string: str) -> Formula:
        """Parses the given valid string representation into a Formula object.

        The passed string must adhere completely to the defined propositional logic syntax. That is:
        - Every symbol must begin with an uppercase ASCII character or an underscore and then contain only ASCII
            letters, underscores, and hyphens.
        - Every formula defined by a binary operator is surrounded by a pair of parentheses. That is, if `f1, f2` are
            valid formula strings, so is `(f1->f2)` but not `f1->f2`.
        - Parentheses in other places are forbidden, in particular negated formulae are not parenthesised.
        - Spaces can be inserted arbitrarily between other tokens without affecting the parsed formula. Other
            whitespace is forbidden.
        - The constant values `0` and `1` can occurr in any place a symbol could.

        Some valid example formulae are `(X \\/ Y)`, `~MySymbol`, `(A1 -> (B \\/ C17))`,
        or `(1 /\\ ((A -> ~ B) \\/ C))`.

        raises:
            ValueError: if the given string is not a valid formula.
        """
        tokens = list(Formula._tokenize(string))
        formula, rest = Formula._parse_prefix(tokens)
        if rest:
            raise ValueError
        return formula

    @classmethod
    def is_formula(cls, string: str) -> bool:
        """Checks if the given string is a valid string representation of a formula."""
        try:
            cls.parse(string)
        except ValueError:
            return False
        else:
            return True

    @abstractmethod
    def evaluate(self, interpretation: Interpretation) -> bool:
        """Evaluates the truth value of the formula under a given interpretation.

        raises:
            KeyError: if the interpretation does not contain every Symbol occurring in the formula.
        """
        ...

    def generate_truth_table(self) -> TruthTable:
        """Creates the truth table of this formula."""

        truth_table = TruthTable(self.symbols)
        for interpretation in truth_table:
            truth_table[interpretation] = self.evaluate(interpretation)
        return truth_table


@dataclass(frozen=True, slots=True, order=True)
class Symbol(Formula):
    """A single propositional symbol.

    Consists of a single string, the symbol's name. If an instance is created with an invalid name, `ValuError` is
    raised.
    """

    label: str
    """The symbol's name.
    
    Must start with an uppercase ASCII letter or an underscore and then only contain ASCII letters, underscores, and
    hyphens.
    """

    def __post_init__(self) -> None:
        if symbol_pattern.fullmatch(self.label) is None:
            raise ValueError

    @memoize
    def __str__(self) -> str:
        return self.label

    def __len__(self) -> int:
        return len(self.label)

    def __format__(self, format_spec: str) -> str:
        return self.label.__format__(format_spec)

    @cached_property
    def operators(self) -> frozenset[Operator]:
        return frozenset()

    @cached_property
    def symbols(self) -> frozenset[Symbol]:
        return frozenset([self])

    def evaluate(self, interpretation: dict[Symbol, bool]) -> bool:
        return interpretation[self]


@dataclass(frozen=True, slots=True)
class Constant(Formula):
    label: ConstantVal

    @memoize
    def __str__(self) -> str:
        return self.label

    @cached_property
    def operators(self) -> frozenset[Operator]:
        return frozenset([self.label])

    @cached_property
    def symbols(self) -> frozenset[Symbol]:
        return frozenset()

    def evaluate(self, interpretation: dict[Symbol, bool]) -> bool:
        return self.label == "1"


@dataclass(frozen=True, slots=True)
class Neg(Formula):
    subformula: Formula

    label: Final = "~"

    @memoize
    def __str__(self) -> str:
        return f"~{self.subformula}"

    @cached_property
    def operators(self) -> frozenset[Operator]:
        return self.subformula.operators | cast(set[Operator], {self.label})

    @cached_property
    def symbols(self) -> frozenset[Symbol]:
        return self.subformula.symbols

    def evaluate(self, interpretation: dict[Symbol, bool]) -> bool:
        return not self.subformula.evaluate(interpretation)


@dataclass(frozen=True, slots=True)
class BinaryFormula(Formula, ABC):
    first: Formula
    second: Formula

    label: ClassVar[BinaryOperator]

    @memoize
    def __str__(self) -> str:
        return f"({self.first} {self.label} {self.second})"

    @cached_property
    def operators(self) -> frozenset[Operator]:
        return self.first.operators | self.second.operators | cast(set[Operator], {self.label})

    @cached_property
    def symbols(self) -> frozenset[Symbol]:
        return self.first.symbols | self.second.symbols


@dataclass(frozen=True, slots=True)
class Or(BinaryFormula):
    label = "\\/"

    def evaluate(self, interpretation: dict[Symbol, bool]) -> bool:
        return self.first.evaluate(interpretation) or self.second.evaluate(interpretation)


@dataclass(frozen=True, slots=True)
class And(BinaryFormula):
    label = "/\\"

    def evaluate(self, interpretation: dict[Symbol, bool]) -> bool:
        return self.first.evaluate(interpretation) and self.second.evaluate(interpretation)


@dataclass(frozen=True, slots=True)
class Impl(BinaryFormula):
    label = "->"

    def evaluate(self, interpretation: dict[Symbol, bool]) -> bool:
        return self.first.evaluate(interpretation) <= self.second.evaluate(interpretation)


Interpretation = dict[Symbol, bool]
"""A propositional logic interpretation.

To create an interpretation you can just use plain Python dictionaries. For example,
```py
my_interpretation = {
    Symbol("X"): True,
    Symbol("Y"): False,
    Symbol("Z"): True,
}
```

To then access the value of a symbol under an interpretation use the indexing operator `my_interpretation[Symbol("X")]`.
You can also use this to change the interpretation of a symbol: `my_interpretation[Symbol("X")] = False`.
"""


@dataclass(frozen=True)
class TruthTable(Mapping[Interpretation, bool]):
    """A simple truth table.

    Maps all possible symbol interpretations over some set of symbol to a truth value. In particular, the truth table
    of a given formula contains that formula's truth value for every possible interpretation of that formula's symbols.

    During initialization you must pass the set of symbols this truth table ranges over, for example
    `TruthTable([Symbol("X"), Symbol("Y"), Symbol("Z")])`.

    Each of these symbols becomes a column in the table. The table's rows correspond to interpretations of them. A final
    column contains the value the truth table maps the interpretation rows to. For example, a truth table for symbols
    `X, Y, Z` might look like this:
    ```
     X Y Z │ φ
    ╶──────┼───
     0 0 0 │ 0
     0 0 1 │ 1
     0 1 0 │ 1
     0 1 1 │ 0
     1 0 0 │ 1
     1 0 1 │ 0
     1 1 0 │ 0
     1 1 1 │ 0
    ```
    This indicated that e.g. the interpretation `X -> 0, Y -> 0, Z -> 0` is mapped to `0`, but `X -> 0, Y -> 0, Z -> 1` is
    assigned `1`.

    Using `TruthTable` instances is based on viewing them as mappings from interpretations to symbols. After creating one
    for some set of symbols this mapping defaults to every interpretation being mapped to `False`. To read entries and
    write to them we use the standard python mapping operators, i.e. `some_truth_table[some_interpretation] = value`.
    There are three options for what we can put in the place of `some_interpretation`:
    - A regular `Interpretation`, that is a `dict[Symbol, bool]`. E.g. `some_truth_table[{x: True, y: False, z: True}]`.
    - A direct mapping of symbols to truth values. E.g. we can simple write
        `some_truth_table[x: True, y: False, z: True]` instead of the above line.
    - A list of truth values. These will correspond to the symbols in the truth table in lexicographic order. E.g.
        `some_truth_table[True, False, False]` is again equivalent to the above.

    In all of these examples, the symbols `x, y, z` contain `Symbol` objects with the corresponding names.

    You can also access all data contained in a `TruthTable` using the normal Python Mapping protocol. For example,
    if you want to iterate over all interpretations and what the table maps them to you can write:
    ```py
    for interpretation, value in some_truth_table.items():
        ...
    ```

    We recommend using the builtin `str` to get a human readable representation of the truth table like the example
    above. Note that these get very long for truth tables containing many symbols.
    """

    symbols: InitVar[Iterable[Symbol]]
    """The symbols this truth table maps."""
    _symbols: tuple[Symbol] = field(init=False)
    _values: list[bool] = field(init=False)

    def __post_init__(self, symbols: Iterable[Symbol]) -> None:
        object.__setattr__(self, "_symbols", tuple(sorted(set(symbols))))
        object.__setattr__(self, "_values", [False] * (2 ** len(self._symbols)))

    def _index(self, interpretation: Interpretation) -> int:
        offset = len(self._symbols) - 1
        return sum(int(interpretation[sym]) << (offset - i) for (i, sym) in enumerate(self._symbols))

    def _interpretation_tuple(self, index: int) -> tuple[bool, ...]:
        return tuple(bool(index & (1 << i)) for i in range(len(self._symbols) - 1, -1, -1))

    def _tuple_to_interpretation(self, interpretation: tuple[bool, ...] | tuple[slice, ...]) -> Interpretation:
        if len(interpretation) != len(self._symbols):
            raise ValueError
        if not interpretation:
            return {}
        if isinstance(interpretation[0], bool):
            interpretation = cast(tuple[bool, ...], interpretation)
            return {self._symbols[i]: val for (i, val) in enumerate(interpretation)}
        else:
            interpretation = cast(tuple[slice, ...], interpretation)
            return {s.start: s.stop for s in interpretation}

    def __getitem__(
        self, interpretation: Interpretation | bool | slice | tuple[bool, ...] | tuple[slice, ...], /
    ) -> bool:
        if isinstance(interpretation, bool | slice):
            interpretation = cast(tuple[bool] | tuple[slice], (interpretation,))

        if isinstance(interpretation, tuple):
            interpretation = self._tuple_to_interpretation(interpretation)
        elif set(interpretation.keys()) != set(self._symbols):
            raise ValueError

        return self._values[self._index(interpretation)]

    def __setitem__(
        self, interpretation: Interpretation | bool | slice | tuple[bool, ...] | tuple[slice, ...], value: bool, /
    ) -> None:
        if isinstance(interpretation, bool | slice):
            interpretation = cast(tuple[bool] | tuple[slice], (interpretation,))

        if isinstance(interpretation, tuple):
            interpretation = self._tuple_to_interpretation(interpretation)
        elif set(interpretation.keys()) != set(self._symbols):
            raise ValueError

        self._values[self._index(interpretation)] = value

    def __str__(self) -> str:
        sym_widths = [len(sym) for sym in self._symbols]
        row_pattern = "".join(f" {{: ^{width}}}" for width in sym_widths) + " │{: ^3}"
        header = row_pattern.format(*self._symbols, "φ")
        header_sep = "╶" + "─" * (sum(sym_widths) + len(sym_widths)) + "┼───"
        rows = [
            row_pattern.format(*(int(val) for val in self._interpretation_tuple(i)), int(value))
            for (i, value) in enumerate(self._values)
        ]
        return "\n".join((header, header_sep, *rows))

    def __iter__(self) -> Iterator[dict[Symbol, bool]]:
        for index in range(len(self._values)):
            yield dict(zip(self._symbols, self._interpretation_tuple(index), strict=True))

    def __len__(self) -> int:
        return self._values.__len__()

    def __contains__(self, key: object, /) -> bool:
        return isinstance(key, dict) and key.keys() == set(self._symbols)
