#!/usr/bin/env python3
"""Standalone stdlib verifier for the complete m=3 classification.

It does not import five_gaussian_ci or discovery code.  It reconstructs the
symmetry-orbit domain, T4 face closure, and every rational Krawczyk witness.
"""
from fractions import Fraction as F
from itertools import combinations,permutations
from pathlib import Path
import json,runpy,sys
R=Path(__file__).parents[1]
CATALOGUE=runpy.run_path(R/'independent/catalogue.py')['build_catalogues']
EDGES=tuple((i,j) for i in range(5) for j in range(i+1,5))

def atoms(U):
 U=tuple(sorted(U));out=[]
 for i,j in combinations(U,2):
  rem=tuple(x for x in U if x not in (i,j))
  for m in range(1<<len(rem)):out.append((i,j,frozenset(rem[k] for k in range(len(rem)) if m>>k&1)))
 return tuple(out)
A=atoms(range(1,6)); IDX={a:i for i,a in enumerate(A)}
def perm_atom(a,p):
 i,j,K=p[a[0]],p[a[1]],frozenset(p[x] for x in a[2]);return (min(i,j),max(i,j),K)
def dual(a):return (a[0],a[1],frozenset(range(1,6))-a[2]-{a[0],a[1]})
def maps():
 out=[]
 for pp in permutations(range(1,6)):
  p=dict(zip(range(1,6),pp));base=tuple(IDX[perm_atom(a,p)] for a in A);out.extend((base,tuple(IDX[dual(perm_atom(a,p))] for a in A)))
 assert len(set(out))==240;return tuple(out)
def image(P,g):return tuple(sorted(g[q] for q in P))
def stabilizer(P,G):return tuple(g for g in G if image(P,g)==tuple(sorted(P)))
def point_reps(points,G):
 rem=set(points);out=[]
 while rem:
  q=min(rem);out.append(q);rem.difference_update(g[q] for g in G)
 return tuple(out)
def premise_support(P):return set().union(*({A[q][0],A[q][1]}|set(A[q][2]) for q in P))
def premise_reps(G):
 rem=set(combinations(range(80),3));out=[];mixed=0
 while rem:
  p=min(rem);orb={image(p,g) for g in G};rem.difference_update(orb);out.append(p)
  mixed+=len({len(premise_support(q))==5 for q in orb})==2
 return out,mixed

def t4_data():
 raw,published,excluded=CATALOGUE()
 if len(raw)!=679 or len(published)!=629 or len(excluded)!=50:raise ValueError('T4 counts')
 return tuple(sum((b=='0')<<i for i,b in enumerate(row)) for row in published)
def face_maps():
 out=[]
 for x in range(1,6):
  V=tuple(v for v in range(1,6) if v!=x)
  for cond in (False,True):
   out.append(tuple(IDX[(a[0],a[1],a[2]|({x} if cond else set()))] for a in atoms(V)))
 return out
def closure(P,t4,faces):
 S=set(P)
 while True:
  old=len(S)
  for mp in faces:
   inv={q:i for i,q in enumerate(mp)};pm=sum(1<<inv[q] for q in S if q in inv);allowed=[m for m in t4 if m&pm==pm]
   if not allowed:return None
   inter=(1<<24)-1
   for m in allowed:inter&=m
   S.update(q for j,q in enumerate(mp) if inter>>j&1)
  if len(S)==old:return frozenset(S)

# Exact rational interval arithmetic.
def I(x):return x if isinstance(x,tuple) else (F(x),F(x))
def add(a,b):a,b=I(a),I(b);return (a[0]+b[0],a[1]+b[1])
def neg(a):a=I(a);return (-a[1],-a[0])
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 a,b=I(a),I(b);z=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]);return (min(z),max(z))
def smul(c,a):return mul(I(F(c)),a)
def det(M):
 n=len(M)
 if n==0:return I(1)
 out=I(0)
 for p in permutations(range(n)):
  t=I(-1 if sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2 else 1)
  for i,j in enumerate(p):t=mul(t,M[i][j])
  out=add(out,t)
 return out
def matrix(fixed,unknown,boxes):
 M=[[I(int(i==j)) for j in range(5)] for i in range(5)];pos={q:k for k,q in enumerate(unknown)}
 for q,(i,j) in enumerate(EDGES):M[i][j]=M[j][i]=boxes[pos[q]] if q in pos else I(fixed[q])
 return M
def ap_parts(M,a):
 r=[a[0]-1]+[k-1 for k in sorted(a[2])];c=[a[1]-1]+[k-1 for k in sorted(a[2])]
 return [[M[i][j] for j in c] for i in r],r,c
def ap(M,a):return det(ap_parts(M,a)[0])
def deriv(M,a,e):
 B,r,c=ap_parts(M,a);u,v=EDGES[e];out=I(0);n=len(B)
 for rr in range(n):
  for cc in range(n):
   if (r[rr],c[cc]) in ((u,v),(v,u)):
    Q=[[B[i][j] for j in range(n) if j!=cc] for i in range(n) if i!=rr]
    out=add(out,smul(-1 if (rr+cc)%2 else 1,det(Q)))
 return out
def frac(z):return F(z[0],z[1])
def verify_cert(c):
 P=tuple(c['premise_indices']);unknown=tuple(c['unknown']);fixed={int(k):frac(v) for k,v in c['fixed'].items()}
 boxes=tuple((frac(z[0]),frac(z[1])) for z in c['boxes']);C=tuple(tuple(frac(x) for x in row) for row in c['C']);n=len(P)
 if n!=3 or len(unknown)!=3 or len(set(unknown))!=3 or set(fixed)!=(set(range(10))-set(unknown)):return False
 if len(C)!=3 or any(len(r)!=3 for r in C) or det([[I(x) for x in r] for r in C])[0]==0:return False
 if any(lo>=hi for lo,hi in boxes):return False
 m=tuple((lo+hi)/2 for lo,hi in boxes);M0=matrix(fixed,unknown,[I(x) for x in m]);MX=matrix(fixed,unknown,boxes)
 f=[ap(M0,A[q])[0] for q in P];J=[[deriv(MX,A[q],e) for e in unknown] for q in P]
 for i in range(3):
  K=I(m[i]-sum(C[i][k]*f[k] for k in range(3)))
  for j in range(3):
   Q=I(int(i==j))
   for k in range(3):Q=sub(Q,smul(C[i][k],J[k][j]))
   K=add(K,mul(Q,(boxes[j][0]-m[j],boxes[j][1]-m[j])))
  if not(boxes[i][0]<K[0] and K[1]<boxes[i][1]):return False
 for k in range(1,6):
  if det([row[:k] for row in MX[:k]])[0]<=0:return False
 for q in c['covers']:
  lo,hi=ap(MX,A[q])
  if lo<=0<=hi:return False
 return True

def main():
 t4=t4_data();G=maps();reps,mixed_support=premise_reps(G);full=[p for p in reps if len(premise_support(p))==5]
 if (len(reps),len(full),mixed_support)!=(439,335,105):raise ValueError('orbit/support-stratum counts')
 D=json.loads((R/'certificates/m3_interval_certificates.json').read_text())
 if D['failures'] or len(D['certificates'])!=364:raise ValueError('certificate counts')
 groups={p:set() for p in full};cert_counts={p:0 for p in full};faces=face_maps();closures={}
 for z,c in enumerate(D['certificates']):
  p=tuple(c['premise_indices'])
  if p not in groups or not verify_cert(c):raise ValueError(f'certificate {z}')
  groups[p].update(c['covers']);cert_counts[p]+=1
 if max(cert_counts.values())!=2 or sum(q==2 for q in cert_counts.values())!=29:raise ValueError('branch counts')
 rule_orbits=forced_orbits=survivor_orbits=0
 for p in full:
  cl=closure(p,t4,faces)
  closures[p]=cl
  if cl is None or groups[p]!=(set(range(80))-set(cl)):raise ValueError(f'coverage {p}')
  cs=point_reps(set(range(80))-set(p),stabilizer(p,G));rule_orbits+=len(cs)
  forced_orbits+=sum(q in cl for q in cs);survivor_orbits+=sum(q not in cl for q in cs)
 if (rule_orbits,forced_orbits,survivor_orbits)!=(21357,190,21167):raise ValueError('rule-orbit counts')
 # Premise-minimality certificate for the four-premise cycle rule: each
 # three-premise deletion is outside T4 closure and is covered by an exact
 # Gaussian witness after canonicalization.
 P=(1,10,20,25);conclusion=0
 cycle_closure=closure(P,t4,faces)
 if cycle_closure is None or conclusion in cycle_closure:raise ValueError('cycle unexpectedly T4-local')
 for drop in range(4):
  Q=tuple(q for z,q in enumerate(P) if z!=drop)
  deletion_closure=closure(Q,t4,faces)
  if deletion_closure is None or conclusion in deletion_closure:raise ValueError('cycle deletion T4-local')
  images=[(image(Q,g),g[conclusion]) for g in G];rep=min(x[0] for x in images)
  mapped={c for p,c in images if p==rep}
  if rep not in groups or not mapped<=groups[rep]:raise ValueError('cycle deletion witness coverage')
 print('m3_classification_ok premise_orbits=439 canonical_full_support=335 mixed_support_orbits=105 rule_orbits=21357 nonlocal=21167 certificates=364 second_branches=29 T4=629 cycle_deletions=4')
if __name__=='__main__':main()
