"""Adversarial law generators on F_2^n."""
import numpy as np, eqlib

def gen_laws(n, rng, count=1):
    N = 2**n; subs = eqlib.subspaces(n); out = []
    def rsub(mind=0):
        c = [x for x in subs if x[1] >= mind]; return c[rng.integers(len(c))]
    kinds = ["dir0.05","dir0.3","dir1","subspace","coset","two_cosets","near_sub",
             "bern_small","bern_mid","spike","set2k+1","ball","sphere","even","support2","support3"]
    for _ in range(count):
        k = kinds[rng.integers(len(kinds))]
        if k.startswith("dir"): p = rng.dirichlet([float(k[3:])]*N)
        elif k == "subspace": el = rsub()[0]; p = eqlib.uniform_sub(el, N)
        elif k == "coset": el = rsub()[0]; p = np.zeros(N); p[el ^ rng.integers(N)] = 1/len(el)
        elif k == "two_cosets":
            el = rsub()[0]; p = np.zeros(N); c1, c2 = rng.integers(N, size=2)
            p[el ^ c1] += 0.5/len(el); p[el ^ c2] += 0.5/len(el)
        elif k == "near_sub":
            el = rsub(1)[0]; eta = 10**rng.uniform(-4, -0.5)
            p = (1-eta)*eqlib.uniform_sub(el, N) + eta*rng.dirichlet([0.5]*N)
        elif k == "bern_small": p = eqlib.bern_prod(n, 10**rng.uniform(-5, -1))
        elif k == "bern_mid": p = eqlib.bern_prod(n, rng.uniform(0.1, 0.5))
        elif k == "spike":
            eps = 10**rng.uniform(-5, -0.3); p = eps*rng.dirichlet([0.3]*N); p[rng.integers(N)] += 1-eps
        elif k == "set2k+1":
            kk = rng.integers(0, n); m = min(N, 2**kk+1); S = rng.choice(N, m, replace=False)
            p = np.zeros(N); p[S] = 1/m
        elif k in ("ball", "sphere"):
            w = np.array([bin(v).count("1") for v in range(N)]); r = rng.integers(0, n+1)
            S = (w <= r) if k == "ball" else (w == r); p = S/S.sum()
        elif k == "even":
            w = np.array([bin(v).count("1") for v in range(N)]); p = (w % 2 == 0)/(N/2)
        elif k == "support2":
            S = rng.choice(N, 2, replace=False); p = np.zeros(N); t = 10**rng.uniform(-6, np.log10(0.5)); p[S] = [t, 1-t]
        elif k == "support3":
            S = rng.choice(N, 3, replace=False); p = np.zeros(N); p[S] = rng.dirichlet([0.5]*3)
        out.append((k, np.asarray(p, float)))
    return out
