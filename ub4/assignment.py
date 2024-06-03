"""Week 4 assignment.

You can now add custom tests by using the `custom_test` decorator from the `util` module. Its docstring explains
more on how to use it.

If you want to print out a more detailed view of a Python object, you can use the `repr` function. It does not print
a human readable string, but a detailed breakdown of the internal Python object. For example, Formula objects are not
printed as e.g. `(X /\\ Y)` but instead `BigAnd(subformulae=(Symbol("X"), Symbol("Y")))`.
"""

from propositional import CNF, BigAnd, BigOr, Interpretation, LiteralFormula, Symbol
from util import custom_test
from propositional import *
from random import choice

X = Symbol("X")

@custom_test(BigAnd(BigOr(X)), BigAnd(BigOr(X)))
@custom_test(Neg(BigAnd([X, Symbol("Y")])), BigOr([Neg(X), Neg(Symbol("Y"))]))
@custom_test(Neg(Neg(X)), X)
@custom_test(Neg(Neg(Neg(X))), Neg(X))
def neg_checker(formula):
    if type(formula).__name__ != 'Neg': return formula
    if type(formula.subformula).__name__ == 'BigAnd':
        corr = BigOr([neg_checker(Neg(el)) for el in formula.subformula.subformulae])
    elif type(formula.subformula).__name__ == 'BigOr':
        corr = BigAnd([neg_checker(Neg(el)) for el in formula.subformula.subformulae])
    elif type(formula.subformula).__name__ == 'And':
        corr = BigOr([neg_checker(Neg(formula.subformula.first)), neg_checker(Neg(formula.subformula.second))])
    elif type(formula.subformula).__name__ == 'Or':
        corr = BigAnd([neg_checker(Neg(formula.subformula.first)), neg_checker(Neg(formula.subformula.second))])
    elif type(formula.subformula).__name__ == 'Neg':
        corr = neg_checker(formula.subformula.subformula)
    elif type(formula.subformula).__name__ == 'bool':
        return not formula
    else: return formula
    return corr

@custom_test(BigAnd(X, Symbol("Y")), BigAnd((BigOr(X), BigOr(Symbol("Y")))))
@custom_test(BigAnd(BigOr(X)), BigAnd(BigOr(X)))
@custom_test(BigAnd(Or(X, Symbol("Y"))), BigAnd((X, Symbol("Y"))))
def make_clauses(formula):
    if type(formula).__name__ != "BigAnd": raise TypeError("Unsupported formula type is not BigAnd!!!")
    new = []
    for clause in formula:
        if type(clause).__name__ == 'BigAnd' or type(clause).__name__ == 'And' or type(clause).__name__ == 'Impl': raise TypeError("Unsupported clause type, formula should be in CNF dummy :)")
        elif type(clause).__name__ == 'BigOr': new.append(clause)
        elif type(clause).__name__ == 'Symbol' or type(clause).__name__ == 'Constant' or type(clause).__name__ == 'bool': new.append(BigOr([clause,]))
        elif type(clause).__name__ == "Neg": new.append(BigOr([neg_checker(clause),]))
        elif type(clause).__name__ == "Or": new.append(BigOr((clause.first, clause.second)))
        else: raise TypeError(f"Unknown type: {type(clause).__name__} - should it be handled?")
    nf = BigAnd(new)
    return nf

def get_literals(formula):
    match formula:
        case Symbol(s) | Neg(Symbol(s)):
            yield formula
        case Or(f1, f2) | And(f1, f2):
            yield from get_literals(f1)
            yield from get_literals(f2)
        case Impl(f1, f2):
            yield from get_literals(f1)
            yield from get_literals(f2)
        case BigOr(subforms) | BigAnd(subforms):
            for i in subforms:
                yield from get_literals(i)
        case Constant():
            pass  # Constants are not literals
        case _:
            raise TypeError(f"Unsupported formula type: {type(formula)}")


@custom_test(BigAnd(BigOr(X)), X)
def choose_literal(formula: CNF) -> LiteralFormula:
    """Chooses a literal from the formula, using an arbitrary heuristic.

    You do not need to optimize this heuristic in order to score full marks in this assignment.

    Args:
        formula: A CNF formula.
    Returns:
        A literal occurring in the formula.
    """
    from random import choice

    clauses = formula.subformulae
    
    # if there is a unit clause, choose that
    for c in clauses:
        if len(list(get_literals(c))) == 1: return next(get_literals(c))
    
    c = choice(clauses)
    lit = choice(list(get_literals(c)))
    return lit

def _assign(interpretation, literal, val):
    if type(literal).__name__ == 'Neg': ni = interpretation | {literal.subformula: not val}
    if type(literal).__name__ == 'Symbol': ni = interpretation | {literal: val}
    return ni

def _dpll(formula, interpretation):
    formula = make_clauses(formula)
    clauses = list(formula.subformulae)
    
    # Base case: if the formula is empty, we have a satisfying interpretation
    if len(clauses) == 0: return formula, interpretation
    
    # Base case: if the formula contains an empty clause, it is unsatisfiable
    if any(len(c.subformulae) == 0 for c in clauses): return formula, None
    
    # Choose a literal from the formula
    literal = choose_literal(formula)

    # Recursively try assigning the literal to True
    new_interpretation = _assign(interpretation, literal, True)
    p1 = [c for c in clauses if literal not in list(get_literals(c)) and neg_checker(Neg(literal)) not in list(get_literals(c))]
    p2 = [list(get_literals(c)) for c in clauses if neg_checker(Neg(literal)) in list(get_literals(c))]
    for c in p2: c.remove(neg_checker(Neg(literal)))
    p1.extend(p2)
    new_formula = BigAnd([BigOr(c) for c in p1])
    res_formula, res_interpretation = _dpll(new_formula, new_interpretation)
    return res_formula, res_interpretation

@custom_test(BigAnd(BigOr(X), BigOr(~X)), None)
@custom_test(BigAnd(BigOr(X)), {Symbol(label='X'): True})
@custom_test(BigAnd(BigOr(~X)), {Symbol(label='X'): False})
def dpll(formula: CNF) -> Interpretation | None:
    """The SAT solver DPLL.

    Args:
        formula: A CNF formula.
    Returns:
        A satisfying Interpretation if the formula is satisfiable. Or `None` if the formula is unsatisfiable.
    """

    interpretation: Interpretation = {}
    formula, interpretation = _dpll(formula, interpretation)
    
    return interpretation
