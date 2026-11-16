"""High-precision checks: Prop 9.3 Bernoulli asymptotics, the Thm 8.2 arithmetic, and the
limiting (E/H)·log2(1/lambda) constant for spike-plus-k-directions laws."""
import mpmath as mp, math, json
mp.mp.dps = 200
L2 = lambda x: mp.log(x, 2)
def h2(p): return (-p*mp.log(p) - (1-p)*mp.log1p(-p))/mp.log(2) if 0 < p < 1 else mp.mpf(0)
def Eb(p): return 2*h2(p) - h2(2*p*(1-p))
out = {}
# expansions with explicit remainders
rows = []
for k in [2, 4, 8, 16, 32, 64, 128, 256]:
    p = mp.mpf(2)**(-k)
    r1 = (h2(p) - p*L2(1/p) - p*L2(mp.e))/p**2
    r2 = (Eb(p) - 2*p)/(p**2*mp.log(1/p))
    rows.append((k, float(r1), float(r2), float(Eb(p)/h2(p)*L2(1/p))))
out["expansions(k: p=2^-k): [h2 rem/p^2, E rem/(p^2 log 1/p), (E/H)log2(1/p)]"] = rows
# Prop 9.3: for c<2, p=2^{-c/eps}: E/H > eps/(1+eps) for small eps; and eps*log2(1/h2(p)) -> c
for c in [1.0, 1.5, 1.9, 1.99]:
    tab = []
    for eps in [0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005, 0.002, 0.001]:
        p = mp.mpf(2)**(-c/eps)
        tab.append((eps, bool(Eb(p)/h2(p) > eps/(1+eps)), float(eps*L2(1/h2(p)))))
    out[f"c={c}: (eps, E/H > eps/(1+eps), eps*log2 C lower bound)"] = tab
# the exact crossing: where does E/H = theta for p = 2^{-c/eps}? find eps0(c)
def eps0(c):
    f = lambda e: Eb(mp.mpf(2)**(-c/e))/h2(mp.mpf(2)**(-c/e)) - e/(1+e)
    lo, hi = mp.mpf('1e-6'), mp.mpf(5)
    # scan for the largest eps with f>0 on (0, eps]
    es = [mp.mpf(10)**(-4 + 4.6*i/400) for i in range(401)]
    last = None
    for e in es:
        if f(e) > 0: last = e
        else: break
    return float(last) if last else None
out["eps0(c): largest eps such that Bernoulli witness works on (0,eps0]"] = {c: eps0(c) for c in [1.0, 1.5, 1.9, 1.99, 1.999]}
# Theorem 8.2 arithmetic: sup_{0<d<=1} d log2 1600 + 2 d log2(1/d) + 2 d ceil(149/d)
best = (0, None)
import numpy as np
for d in list(np.linspace(1e-4, 1, 200001)) + [149/k for k in range(149, 200000)]:
    if d <= 0 or d > 1: continue
    v = d*math.log2(1600) + 2*d*math.log2(1/d) + 2*d*math.ceil(149/d - 1e-12)
    if v > best[0]: best = (v, d)
out["Thm 8.2 arithmetic sup (claimed < 312)"] = best
# limiting constant in Thm 1.2 for spike + k independent directions with total mass p
def spike_k(p, k):
    # law: 0 w.p. 1-p, e_i w.p. p/k. H, H(X+X'), lambda* (by symmetry: max_j F(span of j dirs)/j)
    q = p/k
    H = -(1-p)*L2(1-p) - k*q*L2(q)
    # X+X': 0: (1-p)^2 + k q^2 ; e_i: 2(1-p)q ; e_i+e_j (i<j): 2 q^2
    m0 = (1-p)**2 + k*q*q; m1 = 2*(1-p)*q; m2 = 2*q*q
    HS = -m0*L2(m0) - k*m1*L2(m1) - (k*(k-1)//2)*m2*L2(m2) if k > 1 else -m0*L2(m0) - m1*L2(m1)
    E = 2*H - HS
    lam = 0
    for j in range(1, k+1):  # quotient by span(e_1..e_j): masses merge into 0
        m = 1 - p + j*q
        Hq = -m*L2(m) - (k-j)*q*L2(q)
        lam = max(lam, (H - Hq)/j)
    return E/H*L2(1/lam)
out["(E/H)log2(1/lambda*) for spike+k dirs, p=2^-K"] = {f"k={k}": [(K, float(spike_k(mp.mpf(2)**(-K), k))) for K in [10, 30, 100, 300, 1000, 10000]] for k in [1, 2, 4, 8]}
json.dump(out, open("prop93.json", "w"), indent=1, default=str)
for k, v in out.items(): print(k, "\n   ", v)
