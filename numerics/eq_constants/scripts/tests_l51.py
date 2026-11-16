"""Exact worst case of Lemma 5.1 (28) over ALL subspace choices V(u,w): A and B are sums over
pairs, so max_V [A - rho*B*(N-1)/2] is attained pairwise. Check it is <= h/N, rho = lambda*(Q)."""
import numpy as np, sys, json, eqlib
from eqlib import *
from gens import gen_laws
from fib import joint_sW
rng = np.random.default_rng(int(sys.argv[1]))
worst = {"max_ratio": 0, "viol": 0, "tests": 0, "max_ratio_N>=2": 0}
rows = []
for n in [2, 3, 4]:
    subs = subspaces(n)
    for trial in range(30 if n < 4 else 10):
        m = int(rng.integers(1, 4)); laws = gen_laws(n, rng, m); w = rng.dirichlet([1.0]*m)
        fam = [(p, a) for (k, p), a in zip(laws, w)]
        if rng.random() < 0.3 and n <= 3: fam = posterior(fam)
        h = h_fam(fam)
        if h < 1e-6: continue
        rho = sparsity(fam, n)
        sWtab = [[[joint_sW(p, q, lab)[0] for el, d, lab in subs] for q, b in fam] for p, a in fam]
        dims = [d for el, d, lab in subs]
        for N in range(1, 12):
            c = rho*(N-1)/2
            val = sum(a*b*max(sWtab[i][j][k] - c*dims[k] for k in range(len(subs)))
                      for i, (p, a) in enumerate(fam) for j, (q, b) in enumerate(fam))
            worst["tests"] += 1
            r = val/(h/N)
            if r > worst["max_ratio"]: worst["max_ratio"] = r; worst["at"] = (n, N, [k for k, _ in laws], rho, h)
            if N >= 2 and r > worst["max_ratio_N>=2"]: worst["max_ratio_N>=2"] = r; worst["at_N>=2"] = (n, N, [k for k, _ in laws], rho, h)
            if val > h/N + 1e-9: worst["viol"] += 1; rows.append((n, N, val, h/N))
print(worst, rows[:5])
json.dump(worst, open(f"l51_{sys.argv[1]}.json", "w"), default=str)
