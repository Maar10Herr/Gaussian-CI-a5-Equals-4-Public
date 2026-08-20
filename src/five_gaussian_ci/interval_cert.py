"""Exact rational interval/Krawczyk certificates for CI minor roots."""
from fractions import Fraction as F
from itertools import permutations
from .atoms import atoms
EDGES=tuple((i,j) for i in range(5) for j in range(i+1,5))

def I(x): return x if isinstance(x,tuple) else (F(x),F(x))
def add(a,b): a,b=I(a),I(b); return (a[0]+b[0],a[1]+b[1])
def neg(a): a=I(a); return (-a[1],-a[0])
def sub(a,b): return add(a,neg(b))
def mul(a,b):
 a,b=I(a),I(b); z=(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]); return (min(z),max(z))
def smul(c,a): return mul((F(c),F(c)),a)
def det_interval(M):
 n=len(M)
 if n==0:return I(1)
 out=I(0)
 for p in permutations(range(n)):
  inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n)); t=I(-1 if inv%2 else 1)
  for i,j in enumerate(p): t=mul(t,M[i][j])
  out=add(out,t)
 return out

def covariance_intervals(fixed,unknown,boxes):
 M=[[I(int(i==j)) for j in range(5)] for i in range(5)]
 for q,(i,j) in enumerate(EDGES):
  v=boxes[unknown.index(q)] if q in unknown else I(fixed[q])
  M[i][j]=M[j][i]=v
 return M

def ap_submatrix(M,a):
 r=[a.i-1]+[k-1 for k in sorted(a.K)]; c=[a.j-1]+[k-1 for k in sorted(a.K)]
 return [[M[i][j] for j in c] for i in r],r,c

def ap_interval(M,a): return det_interval(ap_submatrix(M,a)[0])
def derivative_interval(M,a,edge):
 B,r,c=ap_submatrix(M,a); u,v=EDGES[edge]; out=I(0); n=len(B)
 for rr in range(n):
  for cc in range(n):
   if (r[rr],c[cc]) in ((u,v),(v,u)):
    subm=[[B[i][j] for j in range(n) if j!=cc] for i in range(n) if i!=rr]
    out=add(out,smul(-1 if (rr+cc)%2 else 1,det_interval(subm)))
 return out

def krawczyk_check(premises,fixed,unknown,boxes,C):
 A=atoms(range(1,6)); m=tuple((lo+hi)/2 for lo,hi in boxes)
 Mmid=covariance_intervals(fixed,unknown,[I(x) for x in m]); MX=covariance_intervals(fixed,unknown,boxes)
 f=[ap_interval(Mmid,A[q])[0] for q in premises]
 J=[[derivative_interval(MX,A[q],edge) for edge in unknown] for q in premises]
 n=len(unknown); K=[]
 for i in range(n):
  base=m[i]-sum(C[i][k]*f[k] for k in range(n)); acc=I(base)
  for j in range(n):
   mij=I(int(i==j))
   for k in range(n): mij=sub(mij,smul(C[i][k],J[k][j]))
   acc=add(acc,mul(mij,(boxes[j][0]-m[j],boxes[j][1]-m[j])))
  K.append(acc)
 return all(boxes[i][0]<K[i][0] and K[i][1]<boxes[i][1] for i in range(n)),K,MX

def verify_witness(cert):
 A=atoms(range(1,6)); fr=lambda z:F(z[0],z[1])
 fixed={int(k):fr(v) for k,v in cert['fixed'].items()}; unknown=tuple(cert['unknown'])
 boxes=tuple((fr(z[0]),fr(z[1])) for z in cert['boxes']); C=tuple(tuple(fr(x) for x in row) for row in cert['C'])
 if len(unknown)!=len(cert['premise_indices']) or len(set(unknown))!=len(unknown): return False,'dimension'
 if any(q not in range(10) for q in unknown) or set(fixed)!=(set(range(10))-set(unknown)): return False,'coordinates'
 if len(C)!=len(unknown) or any(len(row)!=len(unknown) for row in C): return False,'preconditioner-shape'
 if det_interval([[I(x) for x in row] for row in C])[0]==0: return False,'singular-preconditioner'
 if any(lo>=hi for lo,hi in boxes): return False,'box'
 ok,K,M=krawczyk_check(cert['premise_indices'],fixed,unknown,boxes,C)
 if not ok:return False,'krawczyk'
 for k in range(1,6):
  d=det_interval([row[:k] for row in M[:k]])
  if d[0]<=0:return False,f'pd{k}'
 for q in cert['covers']:
  d=ap_interval(M,A[q])
  if d[0]<=0<=d[1]:return False,f'cover{q}'
 return True,'ok'
