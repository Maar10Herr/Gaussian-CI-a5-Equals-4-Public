"""Finite symmetry actions for five-variable CI rules."""
from itertools import permutations
from .atoms import atoms, atom_index

def symmetry_maps(universe, include_duality=True):
    U=tuple(sorted(universe)); A=atoms(U); idx=atom_index(U); out=[]
    for p in permutations(U):
        mp=dict(zip(U,p))
        base=tuple(idx[a.permute(mp)] for a in A)
        out.append(base)
        if include_duality:
            out.append(tuple(idx[a.permute(mp).dual(U)] for a in A))
    if len(set(out)) != len(out):
        raise ValueError("symmetry action produced duplicate permutations")
    return tuple(out)

def image(indices, mapping): return tuple(sorted(mapping[i] for i in indices))

def subset_orbit_representatives(natoms, size, maps):
    from itertools import combinations
    seen=set(); reps=[]
    for p in combinations(range(natoms),size):
        if p in seen: continue
        reps.append(p); seen.update(image(p,g) for g in maps)
    return tuple(reps)

def stabilizer(indices,maps):
    target=tuple(sorted(indices)); return tuple(g for g in maps if image(indices,g)==target)

def point_orbit_representatives(points,maps):
    remaining=set(points); reps=[]
    while remaining:
        x=min(remaining); orb={g[x] for g in maps}; remaining.difference_update(orb); reps.append(x)
    return tuple(reps)

def canonical_rule(premises,conclusion,maps):
    return min((image(premises,g),g[conclusion]) for g in maps)
