"""Week 3 assignment.

Note that this week's `propositional.py` defines `BigAnd` and `BigOr` differently.
In particular, the `subformulae` attribute now is a tuple instead of a list. This means that you can no longer change an
existing `BigAnd` or `BigOr` objects, but you can now always safely use their `symbols` or `operators` properties.

We also simplified constructing these objects, you no longer need to pass a list of formulae but can instead list them
directly in the constructor arguments like `BigAnd(X, Y, Z)`. Invocations using a signle `Iterable` like a list
`BigAnd([X, Y, Z])` still are supported. See the constructor documentation for more detail.

Further, we have updated the `Formula` definition to now allow for better type checking. The functionality of all
classes remain exactly the same. If you are not using a type checker, you can ignore the new type aliases and e.g.
treat `CNF` exactly the same as `BigAnd` or `DNF` the same as `BigOr`.
"""

from propositional import CNF, Interpretation


def pure_literal_rule(formula: CNF) -> tuple[CNF, Interpretation] | None:
    """Tries to apply the pure literal rule to the given formula.

    A pure literal is one whose complement does not occur within the formula. If one of the literals in the input
    formula is pure this function creates a new formula that is identical to the input, except that all clauses
    containing the pure literal are removed. The generated interpretation assigns the symbol of the found pure literal
    such that the literal is true, and all other symbols that only occurred in removed clauses to false.

    Args:
        formula: A formula in CNF (see Blatt 2).
    Returns:
        If the pure literal rule can be applied, the tuple of the resulting CNF formula and interpretation of removed
        symbols. Or `None` if there are no pure literals.
    Example:
        In `((X \\/ Y) /\\ (X \\/ ~Y)) /\\ (Z \\/ ~Z)` the literal `X` is pure. The resulting formula should be
        `((Z \\/ ~Z))` and the interpretation `{X: True, Y: False}`.
    """

    ...  # your code here


def unit_propagation_rule(formula: CNF) -> tuple[CNF, Interpretation] | None:
    """Tries to apply the unit propagation rule to the given formula.

    A unit is a clause which contains only a single literal. If the input formula contains a unit this function creates
    a new formula that is identical to it, except that all clauses containing the unit clause's literal are removed and
    that literal's complement is removed from all other clauses. The generated interpretation assigns the symbol of
    that literal such that the literal is true, and all other symbols that only occurred in removed clauses to false.

    Args:
        formula: A formula in CNF (see Blatt 2).
    Returns:
        If the unit propagation rule can be applied, the tuple of the resulting CNF formula and interpretation of
        removed symbols. Or `None` if there are no units.
    Example:
        In `((X) /\\ (X \\/ ~Y)) /\\ (Z \\/ ~Z)` the clause `(X)` is a unit. The resulting formula should be
        `((Z \\/ ~Z))` and the interpretation `{X: True, Y: False}`.
    """

    ...  # your code here


def simplify(formula: CNF) -> tuple[CNF, Interpretation]:
    """Simplifies the given formula until it contains no unit clauses or pure literals.

    Args:
        formula: A formula in CNF (see Blatt 2).
    Returns:
        A tuple of the simplified formula and an interpretation of removed symbols such that all models of the input
        are extensions of the returned interpretation.
    Example:
        Given `((X) /\\ (X \\/ ~Y) /\\ (~X \\/ Y \\/ Z \\/ ~Z))` the resulting formula is `()` and the interpretation
        is `{X: True, Y: True, Z: False}`.
    """

    ...  # your code here
