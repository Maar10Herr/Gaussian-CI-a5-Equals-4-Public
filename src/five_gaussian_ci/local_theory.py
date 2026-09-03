"""Exact finite T4-minor theory on five labels via Z3 bit-vectors."""
from pathlib import Path
from .atoms import Atom, atoms, atom_index


def _load_t4_rows(t4_path):
    rows = Path(t4_path).read_text(encoding="ascii").splitlines()
    if len(rows) != 629 or any(
        len(row) != 24 or set(row) - {"0", "1"} for row in rows
    ):
        raise ValueError("T4 catalogue must contain 629 binary 24-bit rows")
    if len(set(rows)) != len(rows):
        raise ValueError("T4 catalogue rows must be unique")
    return rows

class T4ArcTheory:
    """Iterated exact closure by the ten marginal/conditional four-faces."""
    def __init__(self,t4_path):
        self.U=(1,2,3,4,5); self.A=atoms(self.U); self.idx=atom_index(self.U)
        rows=_load_t4_rows(t4_path)
        self.masks=tuple(sum((b=='0')<<i for i,b in enumerate(row)) for row in rows)
        self.face_maps=[]
        for omitted in self.U:
            V=tuple(v for v in self.U if v!=omitted)
            for conditioned in (False,True):
                self.face_maps.append(tuple(self.idx[Atom(a.i,a.j,a.K|({omitted} if conditioned else set()))] for a in atoms(V)))
    def consequences(self,premises):
        S=set(premises)
        while True:
            old=len(S)
            for mapping in self.face_maps:
                inv={q:i for i,q in enumerate(mapping)}
                pm=sum(1<<inv[q] for q in S if q in inv)
                allowed=[m for m in self.masks if m&pm==pm]
                if not allowed:return None
                inter=(1<<24)-1
                for m in allowed:inter&=m
                S.update(q for j,q in enumerate(mapping) if inter>>j&1)
            if len(S)==old:return frozenset(S)

class T4MinorTheory:
    def __init__(self,t4_path):
        from z3 import BitVec,BitVecVal,Concat,Extract,Or,Solver
        self.U=(1,2,3,4,5); self.A=atoms(self.U); self.idx=atom_index(self.U)
        rows=_load_t4_rows(t4_path)
        masks=[]
        for row in rows:
            m=sum((b=='0')<<i for i,b in enumerate(row)); masks.append(m)
        self.x=BitVec('ci80',80); self.s=Solver(); self.face_maps=[]
        for omitted in self.U:
            V=tuple(v for v in self.U if v!=omitted)
            for conditioned in (False,True):
                mapping=[]
                for a in atoms(V):
                    b=Atom(a.i,a.j,a.K|({omitted} if conditioned else set()))
                    mapping.append(self.idx[b])
                self.face_maps.append(tuple(mapping))
                face=Concat(*[Extract(q,q,self.x) for q in reversed(mapping)])
                self.s.add(Or(*[face==BitVecVal(m,24) for m in masks]))
    def _bit(self,q):
        from z3 import Extract,BitVecVal
        return Extract(q,q,self.x)==BitVecVal(1,1)
    def consequences(self,premises):
        from z3 import sat
        P=tuple(premises); self.s.push()
        self.s.add(*(self._bit(q) for q in P))
        if self.s.check()!=sat:
            self.s.pop(); return None
        forced=set(P)
        for q in range(80):
            if q in forced: continue
            self.s.push(); self.s.add(self._bit(q)==False)
            if self.s.check()!=sat: forced.add(q)
            self.s.pop()
        self.s.pop(); return frozenset(forced)
    def witness(self,premises,false_conclusion):
        from z3 import sat
        self.s.push(); self.s.add(*(self._bit(q) for q in premises)); self.s.add(self._bit(false_conclusion)==False)
        ok=self.s.check()==sat
        if not ok: self.s.pop(); return None
        val=self.s.model().eval(self.x,model_completion=True).as_long(); self.s.pop(); return val
