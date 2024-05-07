"""Week 2 assignment."""

from propositional import *

def neg_checker(formula):
    if type(formula).__name__ != 'Neg': return formula
    #print(f'neg checking: {formula}')
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
    elif type(formula).__name__ == 'bool':
        return not formula
    else: return formula
    #print(f'neg correction: {corr}')    
    return corr

def to_nnf_neg(formula):
    formula = neg_checker(formula)
    if type(formula).__name__ != 'Neg': return to_nnf(formula)
    sub = formula.subformula
    if type(sub).__name__ == 'Or':
        corr = And(neg_checker(Neg(sub.first)), neg_checker(Neg(sub.second)))
    elif type(sub).__name__ == 'And':
        corr = Or(neg_checker(Neg(sub.first)), neg_checker(Neg(sub.second)))
    elif type(sub).__name__ == 'Impl':
        corr = to_nnf_neg(neg_checker(Neg(to_nnf_impl(sub))))
    elif type(sub).__name__ == 'Neg':
        corr = neg_checker(formula)
    elif type(sub).__name__ in ['Symbol', 'Constant', 'bool']:
        corr = neg_checker(formula)
        return corr
    elif type(sub).__name__ == 'BigOr':
        corrs = [to_nnf(neg_checker(Neg(subi))) for subi in sub.subformulae]
        corr = BigAnd(corrs)
    elif type(sub).__name__ == 'BigAnd':
        corrs = [to_nnf(neg_checker(Neg(subi))) for subi in sub.subformulae]
        corr = BigOr(corrs)
    return to_nnf(corr)

def to_nnf_impl(formula):
    corr = Or(to_nnf_neg(Neg(formula.first)), to_nnf(formula.second))
    return to_nnf(corr)

def to_nnf(formula):
    #print('correcting :', formula)
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
    elif type(formula).__name__ == 'bool' or type(formula).__name__ == 'Constant':
        corr = formula
    #print(formula, type(formula))
    #print('correctiON :', corr)
    return corr

def big_maker(formula):  
    if type(formula).__name__ == 'Neg':
        if type(formula.subformula).__name__ not in ['Symbol', 'Constant', 'bool']: return big_maker(neg_checker(formula))
        return formula
    elif type(formula).__name__ == 'Or':
        return BigOr([big_maker(formula.first), big_maker(formula.second)])
    elif type(formula).__name__ == 'And':
        return BigAnd([big_maker(formula.first), big_maker(formula.second)])
    elif type(formula).__name__ == 'Symbol':
        return formula
    elif type(formula).__name__ == 'BigOr':
        return BigOr([big_maker(sub) for sub in formula.subformulae])
    elif type(formula).__name__ == 'BigAnd':
        return BigAnd([big_maker(sub) for sub in formula.subformulae])
    elif type(formula).__name__ == 'bool' or type(formula).__name__ == 'Constant':
        return formula
    
def is_clause(formula):
    if type(formula).__name__ in ['And', 'BigAnd']: return False
    if type(formula).__name__ in ['Symbol', 'Constant', 'bool', 'Neg']: return True
    subs = formula.subformulae
    out = []
    for i in subs:
        if type(i).__name__ in ['And', 'BigAnd']: return False
        elif type(i).__name__ == 'BigOr': out.append(is_clause(i))
    for o in out: 
        if o != True: return False
    return True

def is_cnf(formula):
    #print(f'is it cnf ? {formula}')
    if type(formula).__name__ != 'BigAnd': return False
    subs = formula.subformulae
    for i in subs:
        if type(i).__name__ == 'BigOr' and not is_clause(i): return False
        if type(i).__name__ == 'BigAnd' and not is_term(i): return False
        if type(i).__name__ in ['Symbol', 'Constant', 'bool']: continue
        if type(i).__name__ == 'Neg': return is_clause(i.subformula)
    return True

def is_term(formula):
    if type(formula).__name__ in ['Or', 'BigOr']: return False
    if type(formula).__name__ in ['Symbol', 'Constant', 'bool', 'Neg']: return True
    subs = formula.subformulae
    out = []
    for i in subs:
        if type(i).__name__ in ['Or', 'BigOr']: return False
        elif type(i).__name__ == 'BigAnd': out.append(is_term(i))
    for o in out: 
        if o != True: return False
    return True

def is_dnf(formula):
    if type(formula).__name__ != 'BigOr': return False
    subs = formula.subformulae
    for i in subs:
        if type(i).__name__ == 'BigAnd' and not is_term(i): return False
        if type(i).__name__ == 'BigOr' and not is_clause(i): return False
        if type(i).__name__ in ['Symbol', 'Constant', 'bool']: continue
        if type(i).__name__ == 'Neg': return is_term(i.subformula)
    return True

def _or(big):
    print(f'correcting {big}')
    if type(big).__name__ != 'BigOr': return big
    for d, i in enumerate(big.subformulae):
        corr = BigOr([])
        if type(i).__name__ == 'BigAnd':
            cl = []
            for subel in i.subformulae:
                cl.append(BigOr([big.subformulae[:d] 
                                + big.subformulae[1+d:] 
                                + [subel]]))
            corr = BigAnd(subformulae = cl)
            print(f'correction: {is_cnf(corr)} == {corr}')
            return _or(corr)
        elif type(i).__name__ == 'BigOr':
            print(f'append to bigor? {i}')
            for sub in i:
                if not is_clause(sub):
                    sub = _or(sub)
                    print(f'correction** {sub}')
                    big.subformulae[d] = sub
                    return big
        else:
            print(f'appending {i} to {corr}')
            corr.subformulae.append(i)
        print(f'valid clause? {corr}, {is_clause(corr)}')
        return corr

def transform(formula):
    print(f'transforming {formula}')
    formula = to_nnf(formula)
    print(f'nnf {formula}')
    formula = big_maker(formula)
    print(f'big {formula}')
    if type(formula).__name__ == 'BigAnd': formula = big_maker(to_nnf(Neg(formula)))
    
    while not is_cnf(formula) and not is_dnf(formula):
        formula = _or(formula)
    return formula, is_cnf(formula), is_dnf(formula)

def nnf_positive(formula: Formula) -> Formula:
    """Returns an equivalent Formula in negation normal form.
    
    The input will be an arbitrary formula f. 
    
    The output needs to be a formula np(f) satisfying the following conditions:
        1. f and np(f) are equivalent, i.e. their truth tables are identical,
        2. np(f) does not contain any implications (Impl),
        3. all negations (Neg) in np(f) must appear directly in front of symbols or constants.
    
    You may assume that input formulas do not contain BigAnd or BigOr.
    """

    return to_nnf(formula)


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

    return to_nnf(Neg(formula))


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

    if is_clause(formula): return formula
    if is_term(formula): return neg_checker(Neg(formula))

    formula, cnf, dnf = transform(formula)
    
    if dnf: return formula
    elif cnf: return neg_checker(Neg(formula))
    else: 
        print('something went wrong')
        return formula
    
    


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

    if is_term(formula): return formula
    if is_clause(formula): return neg_checker(Neg(formula))

    formula, cnf, dnf = transform(formula)
    
    if cnf: return formula
    elif dnf: return neg_checker(Neg(formula))
    else: 
        print('something went wrong')
        return formula
