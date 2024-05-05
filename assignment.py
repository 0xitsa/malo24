"""Week 2 assignment."""

from propositional import BigAnd, BigOr, Formula

def to_nnf_neg(formula):
    sub = formula.subformula
    if type(sub).__name__ == 'Or':
        corr = And(Neg(sub.first), Neg(sub.second))
    elif type(sub).__name__ == 'And':
        corr = Or(Neg(sub.first), Neg(sub.second))
    elif type(sub).__name__ == 'Impl':
        corr = to_nnf_neg(Neg(to_nnf_impl(sub)))
    elif type(sub).__name__ == 'Neg':
        corr = sub.subformula
    elif type(sub).__name__ == 'Symbol':
        corr = formula
        return corr
    elif type(sub).__name__ == 'BigOr':
        corrs = [to_nnf(Neg(subi)) for subi in sub.subformulae]
        corr = BigAnd(corrs)
    elif type(sub).__name__ == 'BigAnd':
        corrs = [to_nnf(subi) for subi in sub.subformulae]
        corr = BigOr(corrs)
    return to_nnf(corr)

def to_nnf_impl(formula):
    corr = Or(to_nnf_neg(Neg(formula.first)), to_nnf(formula.second))
    return to_nnf(corr)

def to_nnf(formula):
    print('correcting :', formula)
    if type(formula).__name__ == 'Neg':
        corr = to_nnf_neg(formula)
    if type(formula).__name__ == 'Or':
        corr = Or(to_nnf(formula.first), to_nnf(formula.second))
    elif type(formula).__name__ == 'And':
        corr = And(to_nnf(formula.first), to_nnf(formula.second))
    elif type(formula).__name__ == 'Impl':
        corr = to_nnf_impl(formula)
    elif type(formula).__name__ == 'Symbol':
        corr = formula
    elif type(formula).__name__ == 'BigOr':
        corrs = [to_nnf(sub) for sub in formula.subformulae]
        corr = BigOr(corrs)
    elif type(formula).__name__ == 'BigAnd':
        corrs = [to_nnf(sub) for sub in formula.subformulae]
        corr = BigAnd(corrs)
    print('correctiON :', corr)
    return corr

def nnf_positive(formula: Formula) -> Formula:
    """Returns an equivalent Formula in negation normal form.
    
    The input will be an arbitrary formula f. 
    
    The output needs to be a formula np(f) satisfying the following conditions:
        1. f and np(f) are equivalent, i.e. their truth tables are identical,
        2. np(f) does not contain any implications (Impl),
        3. all negations (Neg) in np(f) must appear directly in front of symbols or constants.
    
    You may assume that input formulas do not contain BigAnd or BigOr.
    """

    to_nnf(formula)


def nnf_negative(formula: Formula) -> Formula:
    """Unlike the previous function nnf_positive, this function returns a
    Formula in negation normal form that is
    
    >>> equivalent to the negation of the input. <<<
    
    The input will be an arbitrary formula f. 
    
    The output needs to be a formula nn(f) satisfying the following conditions:
        1. ~f and nn(f) are equivalent, i.e. their truth tables are identical,
        2. nn(f) does not contain any implications (Impl),
        3. all negations (Neg) in nn(f) must appear directly in front of symbols or constants.
    
    Again, you may assume that input formulas do not contain BigAnd or BigOr.
    """

    to_nnf(Neg(formula))


def convert_to_dnf(formula: Formula) -> BigOr:
    """Returns an equivalent formula in disjunctive normal form.
    
    The input will be an arbitrary formula f.
    
    The output needs to be a formula dnf(f) satisfying the following conditions:
        1. f and dnf(f) are equivalent, i.e. their truth tables are identical,
        2. dnf(f) is a BigOr formula,
        3. dnf(f) contains only BigAnd formulae,
            which only contain Symbols, Constants, or their negations.
    
    BigAnd and BigOr are Formula objects labelled with "/\\" and "\\/", containing a list of subformulae.
    
    For example, consider the BigAnd (from the documentation of `flatten` in propositional.py):
    ```py
    BigAnd(
        subformulae=[
            Or(Symbol("X"), Symbol("Y)),
            Symbol("Z"),
            Constant("1"),
            Impl(Constant("0"), Constant("1")),
            Or(Symbol("X"), Symbol("X")),
            Symbol("Y"),
            Symbol("Z"),
        ]
    )
    ```
    
    You may assume that input formulas do not already contain BigAnd or BigOr.
    """

    ...  # your code here


def convert_to_cnf(formula: Formula) -> BigAnd:
    """Returns an equivalent formula in conjunctive normal form.
    
    The input will be an arbitrary formula f.
    
    The output needs to be a formula cnf(f) satisfying the following conditions:
        1. f and cnf(f) are equivalent, i.e. their truth tables are identical,
        2. cnf(f) is a BigAnd formula,
        3. cnf(f) contains only BigOr formulae,
            which only contain Symbols, Constants, or their negations.
            
    Blatt 02 contains a hint for this task that can prevent writing duplicate code.
    
   You may assume that input formulas do not already contain BigAnd or BigOr.
    """

    ...  # your code here
