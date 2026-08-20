from itertools import permutations
from five_gaussian_ci.atoms import *

def test_atom_counts_and_roundtrip():
    assert [len(atoms(range(1,n+1))) for n in (3,4,5)] == [6,24,80]
    for a in atoms(range(1,6)): assert parse_atom(a.text())==a

def test_official_four_variable_ordering():
    expected=['[12|]','[12|3]','[12|4]','[12|34]','[13|]','[13|2]','[13|4]','[13|24]']
    assert [a.text() for a in atoms((1,2,3,4))[:8]]==expected

def test_duality_permutation_and_minor_properties():
    U=(1,2,3,4,5); S=frozenset(atoms(U)[::7]); mp={1:5,2:3,3:1,4:4,5:2}
    assert dual_structure(dual_structure(S,U),U)==S
    assert permute_structure(permute_structure(S,mp),{v:k for k,v in mp.items()})==S
    assert minor_structure(S,U,marginalized=(5,)) == frozenset(a for a in S if 5 not in a.support)
    assert minor_structure(S,U,conditioned=(5,)) == frozenset(Atom(a.i,a.j,a.K-{5}) for a in S if 5 in a.K and a.i!=5 and a.j!=5)

def test_atom_orbits_under_valid_pd_symmetries():
    U=(1,2,3,4,5)
    assert orbit_and_stabilizer(frozenset({Atom(1,2)}),U)==(20,12)
    assert orbit_and_stabilizer(frozenset({Atom(1,2,frozenset({3}))}),U)==(60,4)
