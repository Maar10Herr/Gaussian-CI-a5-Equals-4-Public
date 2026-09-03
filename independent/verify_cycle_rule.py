#!/usr/bin/env python3
"""Standalone verifier for the five-variable correlation-cycle rule certificate."""
from itertools import combinations
from pathlib import Path
import runpy
R=Path(__file__).parents[1]
# Sparse integer polynomials in (a,b,c,d,p,q,r,s).
if not __debug__:
    raise SystemExit("verification requires assertions; run Python without -O")

def C(n):return {(0,)*8:n} if n else {}
def V(i):
 e=[0]*8;e[i]=1;return {tuple(e):1}
def add(*ps):
 out={}
 for p in ps:
  for m,c in p.items():out[m]=out.get(m,0)+c
 return {m:c for m,c in out.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def mul(p,q):
 out={}
 for m,c in p.items():
  for n,d in q.items():
   z=tuple(x+y for x,y in zip(m,n));out[z]=out.get(z,0)+c*d
 return {m:c for m,c in out.items() if c}
a,b,c,d,p,q,r,s=map(V,range(8))
f1=add(a,neg(mul(b,p)));f2=add(b,neg(mul(c,q)));f3=add(c,neg(mul(d,r)));f4=add(d,neg(mul(a,s)))

lhs=add(f1,mul(p,f2),mul(mul(p,q),f3),mul(mul(mul(p,q),r),f4))
rhs=add(a,neg(mul(mul(mul(mul(a,p),q),r),s)))
assert lhs==rhs
# Independent atom/face encoding.
def atoms(U):
 out=[]
 for i,j in combinations(U,2):
  rem=[x for x in U if x not in (i,j)]
  for mask in range(1<<len(rem)):out.append((i,j,frozenset(rem[t] for t in range(len(rem)) if mask>>t&1)))
 return out
A=atoms((1,2,3,4,5));idx={a:i for i,a in enumerate(A)}
prem=[1,10,20,25]
assert [A[x] for x in prem]==[(1,2,frozenset({3})),(1,3,frozenset({4})),(1,4,frozenset({5})),(1,5,frozenset({2}))]
T4_ROWS=runpy.run_path(R/'independent/catalogue.py')['build_catalogues']()[1]
T4={sum((ch=='0')<<i for i,ch in enumerate(row)) for row in T4_ROWS};assert len(T4)==629

def check_countermodel(bits):
 if len(bits)!=80 or any(ch not in '01' for ch in bits):return False
 if not all(bits[x]=='1' for x in prem) or bits[0]!='0':return False
 def has(i,j,K):return bits[idx[(min(i,j),max(i,j),frozenset(K))]]=='1'
 # Directly verify all four elementary gaussoid axioms.
 for i in range(1,6):
  for j in range(1,6):
   for k in range(1,6):
    if len({i,j,k})<3:continue
    rem=[x for x in range(1,6) if x not in (i,j,k)]
    for z in range(1<<len(rem)):
     L={rem[t] for t in range(len(rem)) if z>>t&1};jL=L|{j};kL=L|{k}
     if has(i,j,L) and has(i,k,jL) and not (has(i,k,L) and has(i,j,kL)):return False
     if has(i,j,kL) and has(i,k,jL) and not (has(i,j,L) and has(i,k,L)):return False
     if has(i,j,L) and has(i,k,L) and not (has(i,j,kL) and has(i,k,jL)):return False
     if has(i,j,L) and has(i,j,kL) and not (has(i,k,L) or has(j,k,L)):return False
 for omitted in range(1,6):
  U=tuple(x for x in range(1,6) if x!=omitted)
  for conditioned in (False,True):
   mapping=[idx[(i,j,K|({omitted} if conditioned else set()))] for i,j,K in atoms(U)]
   mask=sum((bits[q]=='1')<<i for i,q in enumerate(mapping))
   if mask not in T4:return False
 return True

def main():
 bits=(R/'certificates/cycle_rule_t4_countermodel.txt').read_text().strip()
 assert check_countermodel(bits)
 print('cycle_rule_ok identity=exact gaussoid_axioms=ok t4_faces=10 premise=[1,10,20,25] conclusion=0')
if __name__=='__main__':main()
