"""Exact rational linear algebra and Gaussian CI extraction."""
from __future__ import annotations
from fractions import Fraction
from .atoms import Atom, atoms

Q=Fraction

def as_fraction_matrix(A):
    A=tuple(tuple(Q(x) for x in row) for row in A)
    if not A or any(len(r)!=len(A) for r in A): raise ValueError("matrix must be nonempty square")
    return A

def determinant(A) -> Fraction:
    A=[list(r) for r in as_fraction_matrix(A)]; n=len(A)
    if n==1: return A[0][0]
    sign=1; prev=Q(1)
    for k in range(n-1):
        if A[k][k]==0:
            q=next((r for r in range(k+1,n) if A[r][k]),None)
            if q is None:return Q(0)
            A[k],A[q]=A[q],A[k]; sign=-sign
        pivot=A[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                A[i][j]=(A[i][j]*pivot-A[i][k]*A[k][j])/prev
        prev=pivot
        for i in range(k+1,n): A[i][k]=Q(0)
    return sign*A[-1][-1]

def submatrix(A, rows, cols):
    A=as_fraction_matrix(A)
    return tuple(tuple(A[i][j] for j in cols) for i in rows)

def principal_minor(A, indices):
    I=tuple(indices); return determinant(submatrix(A,I,I))

def almost_principal_minor(A, atom: Atom, labels=None):
    A=as_fraction_matrix(A); labels=tuple(labels or range(1,len(A)+1)); pos={v:i for i,v in enumerate(labels)}
    K=tuple(sorted(atom.K)); rows=(pos[atom.i],)+tuple(pos[k] for k in K); cols=(pos[atom.j],)+tuple(pos[k] for k in K)
    return determinant(submatrix(A,rows,cols))

def is_positive_definite(A):
    A=as_fraction_matrix(A)
    if any(A[i][j]!=A[j][i] for i in range(len(A)) for j in range(len(A))): return False
    return all(principal_minor(A,range(k))>0 for k in range(1,len(A)+1))

def ci_structure(A, labels=None):
    A=as_fraction_matrix(A); labels=tuple(labels or range(1,len(A)+1))
    if not is_positive_definite(A): raise ValueError("matrix is not positive definite")
    return frozenset(a for a in atoms(labels) if almost_principal_minor(A,a,labels)==0)

def inverse(A):
    A=[list(r) for r in as_fraction_matrix(A)]; n=len(A); B=[r+[Q(int(i==j)) for j in range(n)] for i,r in enumerate(A)]
    for k in range(n):
        q=next((r for r in range(k,n) if B[r][k]),None)
        if q is None: raise ValueError("singular")
        B[k],B[q]=B[q],B[k]; p=B[k][k]; B[k]=[x/p for x in B[k]]
        for i in range(n):
            if i!=k:
                c=B[i][k]; B[i]=[x-c*y for x,y in zip(B[i],B[k])]
    return tuple(tuple(r[n:]) for r in B)
