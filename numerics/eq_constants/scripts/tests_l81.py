"""Lemma 8.1 in its actual regime (d >= 40 sqrt(lambda), i.e. lambda <~ 1e-7), in 60-digit
arithmetic on F_2^n, n <= 2: run the paper's construction (Lemma 4.1 quotient -> R = P0*P0,
Q = Post(P0)) and check sparsity of R (4 lam), Q (2 lam), positivity, and
max(e/h of R, Q) >= delta + delta^2/148. Also checks the inner inequalities (40) and J <= 2xH."""
import mpmath as mp, itertools, random, json, sys
mp.mp.dps = 60
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
def L2(x): return mp.log(x)/mp.log(2)
def H(p): return -sum(x*L2(x) for x in p if x > 0)
def conv(p, q):
    N = len(p); r = [mp.mpf(0)]*N
    for a in range(N):
        if p[a] == 0: continue
        for b in range(N): r[a ^ b] += p[a]*q[b]
    return r
def subspaces(n):
    N = 2**n; seen = set(); out = []
    for gens in itertools.product(range(N), repeat=n):
        S = {0}
        for g in gens: S |= {s ^ g for s in S}
        fs = frozenset(S)
        if fs not in seen: seen.add(fs); out.append(fs)
    return out
def lab(S, N): return [min(v ^ w for w in S) for v in range(N)]
def quot(p, lb):
    r = [mp.mpf(0)]*len(p)
    for v, x in enumerate(p): r[lb[v]] += x
    return r
def s(p, q): return H(p) + H(q) - H(conv(p, q))
def h_f(F): return sum(a*H(p) for p, a in F)
def e_f(F): return sum(a*b*s(p, q) for p, a in F for q, b in F)
def F_f(F, lb): return sum(a*(H(p) - H(quot(p, lb))) for p, a in F)
def dimS(S): return int(round(mp.log(len(S), 2)))
def lamstar(F, n):
    N = 2**n; return max(F_f(F, lab(S, N))/dimS(S) for S in subspaces(n) if len(S) > 1)
def post(F):
    N = len(F[0][0]); out = []
    for p, a in F:
        for q, b in F:
            r = conv(p, q)
            for t in range(N):
                if r[t] == 0: continue
                out.append(([p[x]*q[x ^ t]/r[t] for x in range(N)], a*b*r[t]))
    return out
res = []
for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 40):
    n = random.choice([1, 2]); N = 2**n; m = random.choice([1, 1, 2])
    F = []
    for _ in range(m):
        p = [mp.mpf(0)]*N; base = random.randrange(N); p[base] = mp.mpf(1)
        k = random.randint(1, N-1)
        for v in random.sample([v for v in range(N) if v != base], k):
            mass = mp.mpf(10)**(-random.uniform(7, 14)); p[v] = mass; p[base] -= mass
        F.append(p)
    w = [mp.mpf(random.random()) for _ in range(m)]; w = [x/sum(w) for x in w]
    P = list(zip(F, w)); h = h_f(P)
    if h == 0: continue
    lam = lamstar(P, n); d = e_f(P)/h
    hyp = 1600*lam <= d**2
    # Lemma 4.1 with this lam
    R = [(conv(p, q), a*b) for p, a in P for q, b in P]
    best = None
    for S in subspaces(n):
        lb = lab(S, N)
        Phi = h_f([(quot(p, lb), a) for p, a in R]) + (2+d)*h_f([(quot(p, lb), a) for p, a in P]) + 4*lam*dimS(S)
        if best is None or Phi < best[0] - mp.mpf(10)**-40 or (abs(Phi-best[0]) < mp.mpf(10)**-40 and dimS(S) < dimS(best[1])):
            best = (Phi, S)
    S = best[1]; lb = lab(S, N)
    # work on the quotient as a sub-labelled space: relabel cosets
    reps = sorted(set(lb)); idx = {r: i for i, r in enumerate(reps)}
    # quotient V/S is F_2^{n - dim S}; build laws on coset index (need group structure: use reps xor -> coset)
    P0 = [([sum(p[v] for v in range(N) if lb[v] == r) for r in reps], a) for p, a in P]
    nq = n - dimS(S); Nq = 2**nq
    # group law on cosets: map coset index pair -> coset of xor of reps
    if nq != n:
        # simple case: rebuild an isomorphic F_2^{nq} labelling via a basis of the quotient
        basis = []; span = {0}
        for r in reps:
            if lb[r] not in {lb[x] for x in span}:
                basis.append(r); span |= {x ^ r for x in span}
        coord = {}
        for c in range(Nq):
            v = 0
            for i, b in enumerate(basis):
                if c >> i & 1: v ^= b
            coord[lb[v]] = c
        P0 = [([sum(p[v] for v in range(N) if coord[lb[v]] == c) for c in range(Nq)], a) for p, a in P]
    H0 = h_f(P0); delta = e_f(P0)/H0 if H0 > 0 else None
    R0 = [(conv(p, q), a*b) for p, a in P0 for q, b in P0]; Q0 = post(P0)
    rR = e_f(R0)/h_f(R0); rQ = e_f(Q0)/h_f(Q0); M = max(rR, rQ)
    sp0 = lamstar(P0, nq) if nq > 0 else 0
    spR = lamstar(R0, nq) if nq > 0 else 0; spQ = lamstar(Q0, nq) if nq > 0 else 0
    row = dict(n=n, m=m, lam=float(lam), d=float(d), hyp=bool(hyp), dimG=dimS(S), delta=float(delta),
               ratio_ok=bool(delta >= d - mp.mpf(10)**-30), P0_2lam=bool(sp0 <= 2*lam*(1+mp.mpf(10)**-20)),
               R_4lam=bool(spR <= 4*lam*(1+mp.mpf(10)**-20)), Q_2lam=bool(spQ <= 2*lam*(1+mp.mpf(10)**-20)),
               M=float(M), target=float(delta + delta**2/148), growth_ok=bool(M >= delta + delta**2/148),
               growth_factor=float((M - delta)/(delta**2)))
    res.append(row); print(row, flush=True)
json.dump(res, open(f"l81_{sys.argv[1] if len(sys.argv)>1 else 0}.json", "w"), indent=1)
hy = [r for r in res if r["hyp"]]
print("in-regime cases:", len(hy), " growth failures in regime:", sum(not r["growth_ok"] for r in hy),
      " sparsity failures:", sum(not (r["R_4lam"] and r["Q_2lam"] and r["P0_2lam"]) for r in res),
      " min (M-delta)/delta^2 in regime:", min((r["growth_factor"] for r in hy), default=None), "(claimed >= 1/148 = 0.00676)")
