"""Core exact-enumeration library for entropy on F_2^n (laws = numpy arrays of length 2^n)."""
import numpy as np
from functools import lru_cache

def H(p):
    p = np.asarray(p, float); p = p[p > 1e-300]
    return float(-(p * np.log2(p)).sum())

@lru_cache(None)
def xor_table(n):
    a = np.arange(2**n); return np.bitwise_xor.outer(a, a)

def conv(p, q):
    n = int(np.log2(len(p))); X = xor_table(n)
    return np.bincount(X.ravel(), weights=np.outer(p, q).ravel(), minlength=len(p))

def D(p):  return H(conv(p, p)) - H(p)
def E(p):  return 2*H(p) - H(conv(p, p))
def s(p, q): return H(p) + H(q) - H(conv(p, q))
def rdist(p, q): return H(conv(p, q)) - (H(p)+H(q))/2

@lru_cache(None)
def subspaces(n):
    """All subspaces of F_2^n as tuples (elements array, dim, coset-label array)."""
    N = 2**n; seen = {1: None}; frontier = [1]  # bitmask of elements, {0}
    allm = [1]
    while frontier:
        nf = []
        for m in frontier:
            el = [v for v in range(N) if m >> v & 1]
            for v in range(N):
                if m >> v & 1: continue
                m2 = m
                for w in el: m2 |= 1 << (w ^ v)
                if m2 not in seen:
                    seen[m2] = None; nf.append(m2); allm.append(m2)
        frontier = nf
    out = []
    ar = np.arange(N)
    for m in allm:
        el = np.array([v for v in range(N) if m >> v & 1])
        dim = int(round(np.log2(len(el))))
        lab = np.min(np.bitwise_xor.outer(ar, el), axis=1)
        out.append((el, dim, lab))
    return out

def quot(p, lab): return np.bincount(lab, weights=p, minlength=len(p))
def Hq(p, lab): return H(quot(p, lab))
def F(p, lab): return H(p) - Hq(p, lab)

def uniform_sub(el, N):
    u = np.zeros(N); u[el] = 1/len(el); return u

# ---------- families: list of (law, weight) ----------
def h_fam(fam): return sum(a*H(p) for p, a in fam)
def e_fam(fam): return sum(a*b*s(p, q) for p, a in fam for q, b in fam)
def F_fam(fam, lab): return sum(a*F(p, lab) for p, a in fam)
def quot_fam(fam, lab): return [(quot(p, lab), a) for p, a in fam]
def conv_fam(fam): return [(conv(p, q), a*b) for p, a in fam for q, b in fam]

def sparsity(fam, n):
    """lambda* = max over W != 0 of F_fam(W)/dim W."""
    best = 0.0
    for el, dim, lab in subspaces(n):
        if dim == 0: continue
        best = max(best, F_fam(fam, lab)/dim)
    return best

def posterior(fam):
    N = len(fam[0][0]); X = xor_table(int(np.log2(N))); out = []
    for p, a in fam:
        for q, b in fam:
            r = conv(p, q)
            for t in range(N):
                if r[t] <= 1e-300: continue
                law = p * q[X[:, t]] / r[t]   # Law(A | A+B=t): P(a)Q(a+t)/r(t)
                out.append((law, a*b*r[t]))
    return out

def four_J(fam):
    """J = I(A;B | S,T) for the four-sample construction, A=X1+X2, B=X1+X3, S=sum."""
    N = len(fam[0][0]); n = int(np.log2(N)); X = xor_table(n)
    J = 0.0
    import itertools
    ar = np.arange(N)
    for (p1,a1),(p2,a2),(p3,a3),(p4,a4) in itertools.product(fam, repeat=4):
        w = a1*a2*a3*a4
        # joint law of (A,B,S): sum_x1 P1(x1)P2(x1+A)P3(x1+B)P4(x1+S+A+B)
        jt = np.zeros((N, N, N))
        for x1 in range(N):
            if p1[x1] == 0: continue
            A = ar[:, None, None]; B = ar[None, :, None]; S = ar[None, None, :]
            jt += p1[x1] * p2[x1 ^ A] * p3[x1 ^ B] * p4[x1 ^ S ^ A ^ B]
        pS = jt.sum((0, 1)); pAS = jt.sum(1); pBS = jt.sum(0)
        J += w * (H(pAS.ravel()) + H(pBS.ravel()) - H(jt.ravel()) - H(pS))
    return J

def rand_law(N, rng, kind="dirichlet", alpha=0.3):
    if kind == "dirichlet": return rng.dirichlet([alpha]*N)
    raise ValueError

def bern_prod(n, p):
    N = 2**n; w = np.array([bin(v).count("1") for v in range(N)])
    return p**w * (1-p)**(n-w)
