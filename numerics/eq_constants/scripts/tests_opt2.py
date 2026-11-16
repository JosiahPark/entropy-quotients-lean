"""Constrained adversary for Thm 1.2 / 8.2: for a target sparsity lam0, maximise E/H subject to
lambda*(Z) <= lam0, and compare with the Bernoulli curve (h2(p) = lam0) and with the claimed
bound 320/log2(1/lam0)."""
import numpy as np, sys, json, eqlib
from eqlib import *
rng = np.random.default_rng(int(sys.argv[1]))
def law_from(z):
    z = np.clip(z, -60, 30); w = np.exp(z - z.max()); return w/w.sum()
def bern_EH(lam0):
    lo, hi = 1e-15, 0.5
    for _ in range(200):
        mid = (lo*hi)**0.5 if hi/lo > 10 else (lo+hi)/2
        if H([mid, 1-mid]) < lam0: lo = mid
        else: hi = mid
    p = lo; return E(np.array([1-p, p]))/H([p, 1-p])
out = {}
for lam0 in [0.5, 0.2, 0.05, 0.01, 1e-3]:
    bref = bern_EH(lam0)
    for n in [2, 3, 4, 5]:
        for m in [1, 2]:
            N = 2**n
            def obj(z):
                laws = [law_from(z[i*N:(i+1)*N]) for i in range(m)]
                w = law_from(z[m*N:]) if m > 1 else [1.0]
                fam = list(zip(laws, w)); h = h_fam(fam)
                if h < 1e-12: return -10
                lam = sparsity(fam, n)
                return e_fam(fam)/h - 50*max(0.0, lam/lam0 - 1)
            best = -np.inf
            dim = m*N + (m if m > 1 else 0)
            for st in range(4 if n < 5 else 2):
                z = rng.normal(0, 4, dim); f = obj(z); step = 2.0
                for it in range(1200 if n < 5 else 300):
                    z2 = z + rng.normal(0, step, dim)*(rng.random(dim) < 0.3)
                    f2 = obj(z2)
                    if f2 >= f: z, f, step = z2, f2, min(step*1.1, 8)
                    else: step = max(step*0.98, 0.02)
                best = max(best, f)
            key = f"lam0={lam0},n={n},m={m}"
            out[key] = dict(best_EH=best, bernoulli_EH=bref, ratio=best/bref,
                            claimed_bound=min(1, 320/np.log2(1/lam0)))
            print(key, out[key], flush=True)
json.dump(out, open(f"opt_constrained_{sys.argv[1]}.json", "w"), indent=1)
