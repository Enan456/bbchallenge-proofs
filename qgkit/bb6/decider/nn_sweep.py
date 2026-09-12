import numpy as np, time
rng=np.random.default_rng(1); t0=time.time()
def R(a,b):
    if b%2==0: return a+6,b-3,'T'
    be=(a-1) if a%2==1 else (a-2); al=6 if a%2==1 else 9
    if b<be: return al+3*(b-3),be-(b-3),'C'
    return al+3*be+3,b-be-4,'F'
def fatal(a,b):
    if b<=2 or (b%2==0 and b==4): return True
    be=(a-1) if a%2==1 else (a-2)
    return b%2==1 and b>be and b-be in (1,3,5)
SYM={'C':0,'F':1,'T':2}
seqs=[]
for k in range(6000):
    a,b=6+4*k,13+8*k; s=[]
    for _ in range(220):
        if fatal(a,b): break
        a,b,sym=R(a,b); s.append(SYM[sym])
        if a.bit_length()>80: break
    if len(s)>30: seqs.append(s)
print(f"orbits {len(seqs)}",flush=True)
def make(offset,W,cap=120000):
    X=[];Y=[]
    for s in seqs:
        for i in range(W-1,len(s)-offset):
            oh=np.zeros(W*3,dtype=np.float32)
            for j,c in enumerate(s[i-W+1:i+1]): oh[j*3+c]=1
            X.append(oh);Y.append(s[i+offset])
            if len(X)>=cap: break
        if len(X)>=cap: break
    X=np.array(X,dtype=np.float32);Y=np.array(Y)
    idx=rng.permutation(len(X));X,Y=X[idx],Y[idx];tr=int(0.8*len(X))
    return X[:tr],Y[:tr],X[tr:],Y[tr:]
class MLP:  # arbitrary depth
    def __init__(s,din,hs,do=3):
        dims=[din]+hs+[do]; f=lambda a,b:(rng.standard_normal((a,b))*np.sqrt(2/a)).astype(np.float32)
        s.Ws=[f(dims[i],dims[i+1]) for i in range(len(dims)-1)]
        s.bs=[np.zeros(d,np.float32) for d in dims[1:]]
    def fwd(s,X):
        s.zs=[];s.as_=[X];a=X
        for i,(W,b) in enumerate(zip(s.Ws,s.bs)):
            z=a@W+b;s.zs.append(z)
            a=np.maximum(0,z) if i<len(s.Ws)-1 else z
            s.as_.append(a)
        e=np.exp(a-a.max(1,keepdims=True));s.p=e/e.sum(1,keepdims=True);return s.p
    def stp(s,X,Y,lr):
        n=len(X);p=s.fwd(X);g=p.copy();g[np.arange(n),Y]-=1;g/=n
        for i in reversed(range(len(s.Ws))):
            dW=s.as_[i].T@g;db=g.sum(0)
            if i>0: g=(g@s.Ws[i].T)*(s.zs[i-1]>0)
            s.Ws[i]-=lr*dW;s.bs[i]-=lr*db
    def acc(s,X,Y):return (s.fwd(X).argmax(1)==Y).mean()
def train(Xtr,Ytr,hs,ep=10,bs=512,lr=0.3):
    net=MLP(Xtr.shape[1],hs)
    for _ in range(ep):
        idx=rng.permutation(len(Xtr))
        for i in range(0,len(Xtr),bs): b=idx[i:i+bs];net.stp(Xtr[b],Ytr[b],lr)
    return net
def base(Y):v,c=np.unique(Y,return_counts=True);return c.max()/len(Y)
def run(hs,W,label):
    d1=make(1,W);d20=make(20,W)
    n1=train(d1[0],d1[1],hs);n20=train(d20[0],d20[1],hs)
    a1=n1.acc(d1[2],d1[3]);a20=n20.acc(d20[2],d20[3]);br=base(d20[3])
    print(f"  {label:<22} 1-step={a1:.3f}  20-step={a20:.3f}  base={br:.3f}  "
          f"{'WALL HOLDS' if a20<br+0.02 else 'BEATS BASE'}  [{time.time()-t0:.0f}s]",flush=True)
print("\n=== width sweep (depth 2, W=8) ===",flush=True)
for w in [16,48,128,384]: run([w,w],8,f"width {w}")
print("=== depth sweep (width 96, W=8) ===",flush=True)
for d in [1,2,3,4]: run([96]*d,8,f"depth {d}")
print("=== context sweep (width 96, depth 2) ===",flush=True)
for W in [2,4,8,16]: run([96,96],W,f"context W={W}")
print("DONE",flush=True)
