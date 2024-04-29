"""Week 1 assignment."""

from collections.abc import Iterable
from typing import Literal

from propositional import Formula

Digit = Literal[1, 2, 3, 4, 5, 6, 7, 8, 9]
Entry = Digit | None
Row = tuple[Entry, Entry, Entry, Entry, Entry, Entry, Entry, Entry, Entry]
Sudoku = tuple[Row, Row, Row, Row, Row, Row, Row, Row, Row]


def generate_sudoku_cnf(sudoku: Sudoku) -> Iterable[Formula]:
    """Generates a formula in CNF that models a 9x9 sudoku.

    The input will be a tuple containing 9 entries, each specifying a row of the sudoku. Each row contains nine entries
    that describe what the initial entry in that space of the sudoku is. If it is an `int`, it refers to the
    corresponding digit, if it is `None` it means that space is empty.

    The output needs to be a formula that is satisfiable if and only if the sudoku is solvable.
    Conceptually, this formula needs to be in CNF. But since they can get too big for the recursive structure of them
    to be well representable computationally, we don't return a single formula but an Iterable of the clauses in the
    conjunction. These clauses are represented as normal `Formula` objects.

    This means that each element yielded by the returned Iterable _must_ be a tree of Or formulae, with leaves that
    are either Symbols, Constants, or negations of a single Symbol or Constant.

    An Iterable is a Python value that can be iterated over. In particular, you can just return a plain list of such
    clauses or a generator function yielding clauses, whichever you are more comfortable with.

    For example, this sudoku:
    ```
    ┏━━━┯━━━┯━━━┳━━━┯━━━┯━━━┳━━━┯━━━┯━━━┓
    ┃   │   │ 5 ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │ 7 ┃   │   │   ┃   │   │   ┃
    ┣━━━┿━━━┿━━━╋━━━┿━━━┿━━━╋━━━┿━━━┿━━━┫
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │ 3 │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┣━━━┿━━━┿━━━╋━━━┿━━━┿━━━╋━━━┿━━━┿━━━┫
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │ 8 ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┗━━━┷━━━┷━━━┻━━━┷━━━┷━━━┻━━━┷━━━┷━━━┛
    ```
    Is represented in Python like so:
    ```py
    (
        (None, None,    5, None, None, None, None, None, None),
        (None, None, None, None, None, None, None, None, None),
        (None, None,    7, None, None, None, None, None, None),
        (None, None, None, None, None, None, None, None, None),
        (None, None, None, None,    3, None, None, None, None),
        (None, None, None, None, None, None, None, None, None),
        (None, None, None, None, None, None, None, None, None),
        (None, None, None, None, None,    8, None, None, None),
        (None, None, None, None, None, None, None, None, None),
    )
    ```

    And this is a valid output:
    ```py
    [
        Or(Symbol("X"), Or(Symbol("Y"), Symbol("Z"))),
        Or(Symbol("X"), Neg(Symbol("Y"))),
        Symbol("X"),
    ]
    ```
    But none of these may appear in the output Iterable:
    ```py
    - Or(Symbol("X"), And(Symbol("Y"), Symbol("Z")))
    - Neg(Or(Symbol("X"), Symbol("Y")))
    - Impl(Symbol("X"), Constant("0"))
    ```

    The above sudoku is solvable, so your function needs to output a satisfiable formula for it.
    On the other hand, the following sudoku has no valid solutions and thus needs to lead to an unsatisfiable formula:
    ```
    ┏━━━┯━━━┯━━━┳━━━┯━━━┯━━━┳━━━┯━━━┯━━━┓
    ┃   │   │ 5 ┃   │ 5 │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┣━━━┿━━━┿━━━╋━━━┿━━━┿━━━╋━━━┿━━━┿━━━┫
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┣━━━┿━━━┿━━━╋━━━┿━━━┿━━━╋━━━┿━━━┿━━━┫
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┠───┼───┼───╂───┼───┼───╂───┼───┼───┨
    ┃   │   │   ┃   │   │   ┃   │   │   ┃
    ┗━━━┷━━━┷━━━┻━━━┷━━━┷━━━┻━━━┷━━━┷━━━┛
    ```
    """

  
def generate_sudoku_cnf(sudoku):
    n = len(sudoku)
    if n != 9: raise Exception('Invalid sudoku format')
    formula = []
    
    # each cell has a number
    fstr = ''
    for i in range(n):
        for j in range(n):
            for num in range(n):
                if len(fstr)==0: fstr += f'X_{i+1}x{j+1}_{num+1}'
                else: fstr += f'\\/X_{i+1}x{j+1}_{num+1}'
    formula += [disj_parser(fstr)]
    
    # every cell has max one number

    f1str=''
    cl = []
    for i in range(n):
        for j in range(n):
            for num in range(n):
                if len(f1str)==0: f1str += f'¬X_{i+1}x{j+1}_{num+1}'
                else: f1str += f'\\/¬X_{i+1}x{j+1}_{num+1}'
            cl.append(f1str)
            f1str=''
    formula += [disj_parser(c) for c in cl]
    
    # every row contains every number

    f2str=''
    cl =[]
    for i in range(n):
        for num in range(n):
            for j in range(n):
                if len(f2str)==0: f2str += f'X_{i+1}x{j+1}_{num+1}'
                else: f2str += f'\\/X_{i+1}x{j+1}_{num+1}'
            cl.append(f2str)
            f2str=''
    formula += [disj_parser(c) for c in cl]
    
    # every column contains every number

    cl=[]
    f3str = ''
    for j in range(n):
        for num in range(n):
            for i in range(n):
                if len(f3str)==0: f3str += f'X_{i+1}x{j+1}_{num+1}'
                else: f3str += f'\\/X_{i+1}x{j+1}_{num+1}'
            cl.append(f3str)
            f3str = ''
    formula += [disj_parser(c) for c in cl]
    
    # every 3x3 box contains every number

    f4str = ''
    cl = []
    for r in range(3):
        for s in range(3):
            for num in range(n):
                for i in range(3):
                    for j in range(3):
                        if len(f4str)==0: f4str += f'X_{(3*r)+i+1}x{(3*s)+j+1}_{num+1}'
                        else: f4str += f'\\/X_{(3*r)+i+1}x{(3*s)+j+1}_{num+1}'
                cl.append(f4str)
                f4str=''
    formula += [disj_parser(c) for c in cl]
    
    #sudoku stuff 

    cl = []
    for i in range(n):
        for j in range(n):
            if sudoku[i][j]!=None: cl.append(f'X_{i+1}x{j+1}_{sudoku[i][j]}')
    formula += [Symbol(c) for c in cl]
    
    return formula

