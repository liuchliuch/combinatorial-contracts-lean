#!/usr/bin/env python3
"""Exact-rational finite regression, supplementary to Lean proofs (not a proof)."""
from fractions import Fraction as F
from itertools import product
from random import Random
import json

def responses(f,c,a):
    u=[a*x-y for x,y in zip(f,c)]
    v=max(u)
    candidates=[s for s in range(len(f)) if u[s]==v]
    r=max(f[s] for s in candidates)
    return [s for s in candidates if f[s]==r]

def optimum(f,c):
    xs={F(0), F(1)}
    for i in range(len(f)):
        for j in range(i):
            if f[i]!=f[j]:
                a=(c[i]-c[j])/(f[i]-f[j])
                if 0<=a<=1: xs.add(a)
    a=max(xs,key=lambda x:(1-x)*f[responses(f,c,x)[0]])
    return a,(1-a)*f[responses(f,c,a)[0]]

def check(f,c,eps):
    n=(len(f)-1).bit_length()
    a,p=optimum(f,c)
    W=max(x-y for x,y in zip(f,c))
    assert 0<=p<=W<=n*p
    if not W:return 1
    assert n>0 and p>0
    q=1-eps; K=0
    while q**K>F(1,n*n): K+=1
    grid=[1-min(1,W/f[1<<i])*q**k for i in range(n) if f[1<<i]>0 for k in range(1,K+2)]
    assert grid and all(0<x<=1 for x in grid)
    best=max((1-x)*f[responses(f,c,x)[0]] for x in grid)
    assert best>=(1-eps)*p
    return len(grid)+1

rng=Random(260935803)
checked=0
# Includes arbitrary highly nonmonotone set costs and many tie/zero cases.
for n in range(5):
    for trial in range(24):
        weights=[F(rng.randrange(5)) for _ in range(n)]
        f=[sum((weights[i] for i in range(n) if s>>i&1),F(0)) for s in range(1<<n)]
        # A coverage reward is also monotone subadditive, and need not additive.
        if trial%2:
            masks=[rng.randrange(16) for _ in range(n)]
            f=[]
            for s in range(1<<n):
                union=0
                for i in range(n):
                    if s>>i&1:union|=masks[i]
                f.append(F(union.bit_count()))
        c=[F(0)]+[F(rng.randrange(24),3) for _ in range((1<<n)-1)]
        for eps in [F(1,4),F(1,2),F(3,4)]:check(f,c,eps);checked+=1
# Equal-revenue and all allowed hidden perturbations: exact endpoint handling.
perturbed=0
for n in range(2,6):
    N=2**n-1
    f=list(map(F,range(N+1)))
    H=[F(0)]
    for t in range(1,N+1):H.append(H[-1]+F(1,t))
    c=[F(t)-H[t] for t in range(N+1)]
    assert optimum(f,c)[1]==1 and max(x-y for x,y in zip(f,c))==H[N]
    for k in range((N+1)//2,N+1):
        z=F(1,8*N*N);cp=c.copy();cp[k]-=z
        a,p=optimum(f,cp)
        assert a==F(k-1,k)-z and p==1+z*k
        assert (1-F(1,32*N))*p>1
        for S,T in product(range(N+1),repeat=2):
            if S&T==S: assert cp[S]<=cp[T]
            assert cp[S]+cp[T]<=cp[S&T]+cp[S|T]
        perturbed+=1
# Shifted implementation endpoint: a closed inequality suffices; the paper's k=0 convention has a strict bound.
q=F(3,4); delta_star=q; delta=q**3
assert delta==q*q*delta_star
endpoint_example={'q':str(q),'delta_star':str(delta_star),'delta':str(delta)}

# Approximate responses may differ at repeated shares; choose an eligible set
# adversarially using the call index, retaining its realized reward in the run.
def approximate(f,c,a,tau,index):
    utilities=[a*x-y for x,y in zip(f,c)]
    threshold=max(utilities)-tau
    eligible=[i for i in range(len(f)) if utilities[i]>=threshold]
    eligible.sort(key=lambda i:(f[i],i))
    return eligible[0] if index%2==0 else eligible[index%len(eligible)]
robust_cases=0
for n in range(4):
    for trial in range(10):
        weights=[F(rng.randrange(5)) for _ in range(n)]
        f=[sum((weights[i] for i in range(n) if s>>i&1),F(0)) for s in range(1<<n)]
        c=[F(0)]+[F(rng.randrange(24),3) for _ in range((1<<n)-1)]
        _,P=optimum(f,c)
        for eps,tau in product([F(1,4),F(1,2)],[F(0),F(1,7),F(1)]):
            T=approximate(f,c,F(1),tau,0);L=max(F(0),f[T]-c[T]);best=F(0)
            if L>tau:
                q=1-eps/3;K=0
                while q**K>F(1,2*n*n):K+=1
                shares=[1-min(1,(L+tau)/f[1<<i])*q**k for i in range(n) if f[1<<i]>0 for k in range(K+2)]
                for index,a in enumerate(shares,1):
                    assert 0<=a<=1
                    response=approximate(f,c,a,tau,index)
                    best=max(best,(1-a)*f[response])
            assert best>=(1-eps)*P-3*tau/eps
            robust_cases+=1
# Both source tightness constructions, with all off-chain sets present.
tightness_cases=0
for m,eta in product([2,3],[F(1,3),F(2,3)]):
    P0=1+eta; weights=[F(1)]*m+[F(2**r*m) for r in range(1,m+1)]
    f=[sum((weights[i] for i in range(2*m) if s>>i&1),F(0)) for s in range(1<<(2*m))]
    c=[2*x for x in f];A=2**m-1;c[A]=m-P0;lastR=F(m);lastC=c[A]
    for r in range(m):
        R=weights[m+r];lastC=lastC+(1-1/R)*(R-lastR);lastR=R;c[1<<(m+r)]=lastC
    a,P=optimum(f,c);W=max(x-y for x,y in zip(f,c))
    assert a==1-P0/m and P==P0 and W==P0+F(m,2)
    assert W/(1-a)==F(m)*(P0+F(m,2))/P0
    tightness_cases+=1
for n,r in product(range(2,6),[F(3,2),F(2)]):
    Z=sum((r**h for h in range(n)),F(0));v=[r**i/Z for i in range(n)];d=[F(0)]
    for i in range(1,n):d.append(d[-1]+(1-v[0]/v[i])*(v[i]-v[i-1]))
    f=[sum((v[i] for i in range(n) if s>>i&1),F(0)) for s in range(1<<n)]
    c=[sum((d[i] for i in range(n) if s>>i&1),F(0))+s.bit_count()*(s.bit_count()-1) for s in range(1<<n)]
    _,P=optimum(f,c);W=max(x-y for x,y in zip(f,c))
    assert P==v[0] and W/P==n-F(n-1)/r
    tightness_cases+=1
print(json.dumps({'exact_finite_algorithm_cases':checked,'equal_revenue_perturbations':perturbed,
 'shifted_grid_closed_bound_equality':endpoint_example,
 'robust_inconsistent_oracle_cases':robust_cases,'all_set_tightness_cases':tightness_cases,
 'status':'PASS; regression only, not formal completeness'},indent=2))
