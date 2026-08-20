from fractions import Fraction as F
from five_gaussian_ci.atoms import Atom, atoms, dual_structure
from five_gaussian_ci.exact import *

def test_determinant_and_pd():
    A=((2,1),(1,2)); assert determinant(A)==3 and is_positive_definite(A)
    assert inverse(A)==((F(2,3),F(-1,3)),(F(-1,3),F(2,3)))

def test_five_variable_extremes_and_duality():
    I=tuple(tuple(int(i==j) for j in range(5)) for i in range(5))
    assert ci_structure(I)==frozenset(atoms(range(1,6)))
    E=tuple(tuple(F(1) if i==j else F(1,2) for j in range(5)) for i in range(5))
    S=ci_structure(E); assert S==frozenset()
    assert ci_structure(inverse(E))==dual_structure(S,range(1,6))

def test_three_variable_chain_has_target_ci():
    A=((1,F(1,2),F(1,6)),(F(1,2),1,F(1,3)),(F(1,6),F(1,3),1))
    S=ci_structure(A)
    assert Atom(1,3,frozenset({2})) in S
    assert Atom(1,3) not in S
