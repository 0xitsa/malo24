"""Week 5 assignment."""

from first_order import *
from typing_extensions import TypeVar
from util import custom_test

T = TypeVar("T")

f, c, x = FunctionSymbol("F", 1), FunctionSymbol("C", 0), Variable("x")
some_interpretation = Interpretation(
    Structure(range(10), {f: lambda n: n + 1, c: 5}),
    {x: 3},
)


def complicated_test(value: int) -> bool:
    return True


@custom_test((f(x), some_interpretation), 4)
@custom_test((f(x), some_interpretation), [3, 4, 5])
@custom_test((f(x), some_interpretation), complicated_test)
def evaluate_term(term: Term, interpretation: Interpretation[T]) -> T:
    """Evaluates a term to the element of the universe defined by it and the interpretation.

    Args:
        term: An arbitrary term using the same signature as the structure and variables from the assignment.
        interpretation: The corresponding interpretation.
    Returns:
        The value the term evaluates to.
    Example:
        Given `f(a, b)` and an interpretation where `f` is interpreted as addition and `a` and `b` as 1 and 2,
        this function should return `3`.
    """

    assert term.symbols <= interpretation.structure.symbols
    assert term.variables <= interpretation.assignment.keys()

    if isinstance(term, Variable):
        return interpretation.assignment[term]
    elif isinstance(term, FunctionTerm):
        return interpretation.structure.functions[term.function](
            *[evaluate_term(arg, interpretation) for arg in term.arguments]
        )
    else:
        raise TypeError

@custom_test(input=(f(x) == c, some_interpretation), output=False)
def evaluate_atom(atom: AtomicFormula, interpretation: Interpretation[T]) -> bool:
    """Evaluates an atomic formula to its truth value.

    Args:
        atom: An atomic formula (Equality, RelationFormula, or TruthConstant).
        interpretation: An interpretation over the same signature as the atomic formula that also interprets all
            variables occurring in it.
    Returns:
        The truth value of the atomic formula under the given interpretation.
    Example:
        Given `a == b` and an interpretation where `a` and `b` are interpreted as 1 and 2,
        this function should return `False`.
    """

    assert atom.symbols <= interpretation.structure.symbols
    assert atom.free_variables <= interpretation.assignment.keys()

    """Evaluates an atomic formula to its truth value.

    Args:
        atom: An atomic formula (Equality, RelationFormula, or TruthConstant).
        interpretation: An interpretation over the same signature as the atomic formula that also interprets all
            variables occurring in it.
    Returns:
        The truth value of the atomic formula under the given interpretation.
    Example:
        Given `a == b` and an interpretation where `a` and `b` are interpreted as 1 and 2,
        this function should return `False`.
    """

    assert atom.symbols <= interpretation.structure.symbols
    assert atom.free_variables <= interpretation.assignment.keys()

    if isinstance(atom, TruthConstant):
        return atom.value
    elif isinstance(atom, Equality):
        return evaluate_term(atom.first, interpretation) == evaluate_term(atom.second, interpretation)
    elif isinstance(atom, RelationFormula):
        return interpretation.structure.relations[atom.relation](
            *[evaluate_term(arg, interpretation) for arg in atom.arguments]
        )
    else:
        raise TypeError
