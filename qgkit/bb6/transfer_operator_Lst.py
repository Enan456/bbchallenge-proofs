#!/usr/bin/env python3
"""L_{s,t} parametrised transfer operator + offset-cocycle aperiodicity check.
Method A crux: |lambda(s*,t)| < lambda(s*,0)=1 for all nontrivial characters t
(mod odd M) => offset equidistributes mod M with a spectral gap. Only degeneracy
is parity (offset always odd), which is structural and harmless."""
import numpy as np

def R(a,b):
    if b%2==0: return a+6,b-3,'T'
    al,be=(6,a-1) if a%2==1 else (9,a-2)
    if b<be: return al+3*(b-3),be-(b-3),'C'
    return al+3*be+3,b-be-4,'F'
def fatal(a,b):
    if b<=2 or (b%2==0 and b==4): return True
    be=(a-1) if a%2==1 else (a-2)
    return b%2==1 and b>be and b-be in (1,3,5)

NB=20
def spectrum(M, orbits=5000):
    T=np.zeros((NB*M,NB*M))
    for kk in range(orbits):
        a,b=6+4*kk,13+8*kk; prev=None
        for _ in range(4000):
            if fatal(a,b): break
            be=(a-1) if a%2==1 else (a-2)
            if b%2==1 and b>be:
                o=b-be; z=o/(o+be); st=min(int(z*NB),NB-1)*M+(o%M)
                if prev is not None: T[st,prev]+=1
                prev=st
            a,b,s=R(a,b)
            if a.bit_length()>300: break
    T/=np.maximum(T.sum(0),1)
    out={}
    for t in range(M):
        Lt=np.zeros((NB,NB),dtype=complex)
        w=np.exp(2j*np.pi*t*np.arange(M)/M)
        for zi in range(NB):
            for zj in range(NB):
                blk=T[zj*M:(zj+1)*M, zi*M:(zi+1)*M]
                Lt[zj,zi]=(w[:,None]*blk*np.conj(w)[None,:]).sum()/M
        out[t]=max(abs(np.linalg.eigvals(Lt)))
    return out

if __name__=="__main__":
    print("odd M: |lambda(0)|~1, max_{t!=0}|lambda(t)| << 1 => aperiodic")
    for M in (3,5,7,9,11,15):
        r=spectrum(M); mx=max(r[t] for t in range(1,M))
        print(f"  M={M:>2}: lam0={r[0]:.3f} max_{{t!=0}}={mx:.3f} gap={1-mx:.3f}")
