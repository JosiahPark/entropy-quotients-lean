"""Adversarial optimisation: hill-climb over the simplex for the worst ratio each theorem bounds."""
import numpy as np, sys, json, time, eqlib
from eqlib import *
task = sys.argv[1]; seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
rng = np.random.default_rng(seed)

def law_from(z):
    z = np.clip(z, -80, 30); w = np.exp(z - z.max()); return w/w.sum()

def hill(obj, dim, iters=3000, starts=8, init=None):
    best = (-np.inf, None)
    for st in range(starts):
        z = init(st) if init else rng.normal(0, 3, dim)
        f = obj(z); step = 2.0
        for it in range(iters):
            z2 = z + rng.normal(0, step, dim) * (rng.random(dim) < max(0.2, 2/dim))
            f2 = obj(z2)
            if f2 >= f: z, f = z2, f2; step = min(step*1.1, 8)
            else: step = max(step*0.98, 0.02)
        if f > best[0]: best = (f, z.copy())
    return best

def bern_init(n):
    def f(st):
        z = np.full(2**n, -60.0); z[0] = 0; z[1] = -rng.uniform(1, 40); return z + rng.normal(0, 0.5, 2**n)
    return f

out = {}
if task == "thm12":   # maximise (E/H) * log2(1/lambda*) over single laws with lambda* < 1
    for n in [1, 2, 3, 4, 5]:
        def obj(z):
            p = law_from(z); h = H(p)
            if h < 1e-12: return -1
            lam = sparsity([(p, 1.0)], n)
            if lam >= 1 or lam <= 0: return -1
            return E(p)/h * np.log2(1/lam)
        mixed = lambda st: (bern_init(n)(st) if st % 2 else rng.normal(0, 4, 2**n))
        f, z = hill(obj, 2**n, iters=1500 if n < 5 else 400, starts=6 if n < 5 else 3, init=mixed)
        p = law_from(z); lam = sparsity([(p, 1.0)], n)
        out[n] = dict(best=f, H=H(p), E=E(p), lam=lam, support=int((p > 1e-12).sum()),
                      top=sorted([(float(x), int(i)) for i, x in enumerate(p)], reverse=True)[:6])
        print(n, out[n], flush=True)
elif task == "thm82":  # families of 2 or 3 laws
    for n in [1, 2, 3]:
        for m in [2, 3]:
            N = 2**n
            def obj(z):
                laws = [law_from(z[i*N:(i+1)*N]) for i in range(m)]; w = law_from(z[m*N:])
                fam = list(zip(laws, w)); h = h_fam(fam)
                if h < 1e-12: return -1
                lam = sparsity(fam, n)
                if lam >= 1 or lam <= 0: return -1
                return e_fam(fam)/h * np.log2(1/lam)
            f, z = hill(obj, m*N + m, iters=1500, starts=4)
            out[f"{n},{m}"] = f; print(n, m, f, flush=True)
elif task == "marton":  # maximise min_V d(K,U_V) / D(K)
    for n in [1, 2, 3, 4]:
        subs = subspaces(n); N = 2**n
        def obj(z):
            p = law_from(z); dd = D(p)
            if dd < 1e-9: return -1
            return min(rdist(p, uniform_sub(el, N)) for el, d, lab in subs)/dd
        f, z = hill(obj, N, iters=2000, starts=6)
        p = law_from(z)
        out[n] = dict(best_ratio=f, H=H(p), D=D(p), top=sorted([(float(x), int(i)) for i, x in enumerate(p)], reverse=True)[:6])
        print(n, out[n], flush=True)
elif task == "l63":  # maximise E D(Qu*Qw) / (3J) and the BSG ratio over small families
    for n in [1, 2]:
        N = 2**n
        for m in [1, 2]:
            def obj(z):
                laws = [law_from(z[i*N:(i+1)*N]) for i in range(m)]; w = law_from(z[m*N:]) if m > 1 else [1.0]
                fam = list(zip(laws, w)); J = four_J(fam)
                if J < 1e-9: return -1
                Q = posterior(fam)
                return sum(a*b*D(conv(p, q)) for p, a in Q for q, b in Q)/(3*J)
            f, z = hill(obj, m*N + (m if m > 1 else 0), iters=600, starts=3)
            out[f"{n},{m}"] = f; print("L6.3 ratio", n, m, f, flush=True)
elif task == "thm11":  # empirical least coefficient: maximise dimG*/H(X)
    eps_list = [2.0, 1.0, 0.5, 1/3, 0.25]
    for eps in eps_list:
        th = eps/(1+eps)
        # Bernoulli reference: sup 1/h2(p) over p with E/H > theta
        ps = np.logspace(-12, np.log10(0.5), 20000)
        bern = [(1/H([p, 1-p])) for p in ps if E(np.array([1-p, p]))/H([p, 1-p]) > th]
        bref = max(bern) if bern else 0
        for n in [1, 2, 3, 4, 5]:
            subs = sorted(subspaces(n), key=lambda x: x[1])
            def dimstar(p, original=False):
                Dx = D(p)
                for el, d, lab in subs:
                    qp = quot(p, lab); hq = H(qp)
                    if hq <= (1+eps)*(Dx if original else D(qp)) + 1e-12: return d
            def obj(z, original=False):
                p = law_from(z); h = H(p)
                if h < 1e-14: return -1
                return dimstar(p, original)/h
            for orig in [False, True]:
                f, z = hill(lambda z: obj(z, orig), 2**n, iters=800 if n < 5 else 200,
                            starts=4 if n < 5 else 2, init=lambda st: bern_init(n)(st) if st % 2 == 0 else rng.normal(0, 4, 2**n))
                p = law_from(z)
                key = f"eps={eps:.3f},n={n},{'orig' if orig else 'intr'}"
                out[key] = dict(best=f, bern_ref=bref, ratio_to_bern=f/bref if bref else None,
                                eps_log2C=eps*np.log2(f) if f > 0 else None, H=H(p),
                                dimG=dimstar(p, orig), top=sorted([(float(x), int(i)) for i, x in enumerate(p)], reverse=True)[:5])
                print(key, out[key], flush=True)
json.dump(out, open(f"opt_{task}_{seed}.json", "w"), indent=1, default=str)
