"""Lemma-by-lemma falsification on small F_2^n with adversarial families."""
import numpy as np, itertools, json, sys, time, eqlib
from eqlib import *
from gens import gen_laws
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
TOL = 1e-9
res = {}
def rec(name, slack, info=None):
    r = res.setdefault(name, {"tests": 0, "min_slack": np.inf, "worst": None, "violations": 0})
    r["tests"] += 1
    if slack < r["min_slack"]: r["min_slack"] = float(slack); r["worst"] = info
    if slack < -TOL: r["violations"] += 1

def joint_sW(p, q, lab):
    """s_W(P,Q) and the mutual-info term of (20)."""
    N = len(p); X = xor_table(int(np.log2(N)))
    pq = np.outer(p, q)
    la = np.repeat(lab[:, None], N, 1); lb = np.repeat(lab[None, :], N, 0)
    key = (X * N + la) * N + lb                       # (A+B, qA, qB)
    Hj = H(np.bincount(key.ravel(), weights=pq.ravel()))
    HqAqB = Hq(p, lab) + Hq(q, lab)
    HcondSum = Hj - HqAqB                              # H(A+B | qA,qB)
    sW = F(p, lab) + F(q, lab) - HcondSum
    # I(A+B ; qA,qB | q(A+B)) = H(A+B|q(A+B)) - H(A+B|qA,qB)
    r = conv(p, q); Ifib = F(r, lab) - HcondSum
    return sW, Ifib

def bsg_check(n):
    N = 2**n; X = xor_table(n)
    R = rng.dirichlet([rng.choice([0.05, 0.3, 1.0])]*(N*N)).reshape(N, N)   # joint of (U,V)
    if rng.random() < 0.3:  # structured: V = U + noise on subspace
        el = eqlib.subspaces(n)[rng.integers(len(eqlib.subspaces(n)))][0]
        pu = rng.dirichlet([0.3]*N); R = np.zeros((N, N))
        for u in range(N):
            for w in el: R[u, u ^ w] += pu[u]/len(el)
    pU = R.sum(1); pV = R.sum(0); Z = np.bincount(X.ravel(), weights=R.ravel(), minlength=N)
    I = H(pU) + H(pV) - H(R.ravel())
    lhs = 0.0
    for z in range(N):
        if Z[z] < 1e-300: continue
        cu = np.zeros(N); cv = np.zeros(N)
        for u in range(N): cu[u] = R[u, u ^ z]; cv[u ^ z] = R[u, u ^ z]
        lhs += Z[z] * rdist(cu/Z[z], cv/Z[z])
    return 3*I + 2*H(Z) - H(pU) - H(pV) - lhs

t0 = time.time()
# ---------------- single laws / pairs, n = 2..5 ----------------
for n in [2, 3, 4, 5]:
    subs = subspaces(n); N = 2**n
    for trial in range(60 if n < 5 else 20):
        (k1, p), (k2, q) = gen_laws(n, rng, 2)
        tag = f"n={n} {k1}/{k2}"
        sv = s(p, q); rec("(9) s>=0", sv, tag); rec("(9) s<=minH", min(H(p), H(q)) - sv, tag)
        rec("D>=0, E>=0", min(D(p), E(p)), tag)
        Kmin = min(rdist(p, uniform_sub(el, N)) for el, d, lab in subs)
        rec("(35) Marton min_V d(K,U_V) <= 6D(K)", 6*D(p) - Kmin, tag)
        rec("(35') Marton with 11/2", 5.5*D(p) - Kmin, tag)
        best36 = max(min(12*D(p) - Hq(p, lab), H(p) + 12*D(p) - d) for el, d, lab in subs)
        rec("(36)", best36, tag)
        for el, d, lab in subs:
            rec("B5 D(q_W X) <= D(X)", D(p) - D(quot(p, lab)), tag)
            sW, Ifib = joint_sW(p, q, lab)
            lhs20 = s(quot(p, lab), quot(q, lab)) + sW - Ifib
            rec("(20) fibring identity |err|", -abs(sv - lhs20), tag)
            rec("(19) 0<=s_W<=min F", min(sW, min(F(p, lab), F(q, lab)) - sW), tag)
            rec("(21)", sW - (sv - s(quot(p, lab), quot(q, lab))), tag)
        if n <= 4:
            for (elU, dU, labU), (elW, dW, labW) in itertools.product(subs, subs):
                mU = set(elU.tolist()); mW = set(elW.tolist())
                inter = mU & mW
                summ = set(a ^ b for a in mU for b in mW)
                labI = next(lab for el, d, lab in subs if set(el.tolist()) == inter)
                labS = next(lab for el, d, lab in subs if set(el.tolist()) == summ)
                rec("L2.1 supermodularity (11)", Hq(p, labU) + Hq(p, labW) - Hq(p, labI) - Hq(p, labS), tag)
                if mU <= mW:
                    sW, _ = joint_sW(p, q, labW)
                    rec("(22) nested", F(q, labU) - (sW - (Hq(p, labU) - Hq(p, labW))), tag)
    print("n", n, "done", time.time()-t0, flush=True)
    for n2 in [n]:
        if n2 <= 4:
            for _ in range(40): rec("L6.2 conditional BSG (33)", bsg_check(n2), f"n={n2}")

# ---------------- families, n = 2,3 ----------------
for n in [2, 3]:
    subs = subspaces(n)
    for trial in range(25 if n == 2 else 12):
        m = rng.integers(1, 4)
        laws = gen_laws(n, rng, m); w = rng.dirichlet([1.0]*m)
        fam = [(p, a) for (k, p), a in zip(laws, w)]; tag = f"n={n} " + "/".join(k for k, _ in laws)
        h = h_fam(fam); e = e_fam(fam)
        if h < 1e-6: continue
        rec("(14) 0<=e<=h", min(e, h - e), tag)
        R = conv_fam(fam); rec("(15) h(R)=2h-e |err|", -abs(h_fam(R) - (2*h - e)), tag)
        Q = posterior(fam)
        rec("L2.2 h(Post)=e |err|", -abs(h_fam(Q) - e), tag)
        for el, d, lab in subs:
            rec("L2.2 F_Post(W)<=F_P(W)", F_fam(fam, lab) - F_fam(Q, lab), tag)
        J = four_J(fam); delta = e/h
        rec("J>=0", J, tag)
        rec("L6.1 e(R)+e(Q)=2dH+J |err|", -abs(e_fam(R) + e_fam(Q) - 2*e - J), tag)
        # Lemma 6.3
        lhs = sum(a*b*D(conv(p, q)) for p, a in Q for q, b in Q)
        rec("L6.3 E D(Qu*Qw) <= 3J", 3*J - lhs, tag + f" J={J:.3g}")
        # Lemma 7.1 with true Marton subspaces and true sparsity of Q
        N = 2**n; rho = sparsity(Q, n)
        Vs = {}; A = 0.0; B = 0.0
        for iu, (pu, a) in enumerate(Q):
            for iw, (pw, b) in enumerate(Q):
                K = conv(pu, pw)
                el, d, lab = min(subs, key=lambda x: rdist(K, uniform_sub(x[0], N)))
                sW, _ = joint_sW(pu, pw, lab)
                A += a*b*sW; B += a*b*d
        hQ = h_fam(Q)
        rec("(38) E dim V <= 26 h(Q)", 26*hQ - B, tag)
        rec("L5.1 (29) A <= 14 sqrt(rho) h  [rho=lambda*(Q)]", 14*np.sqrt(rho)*hQ - A, tag)
        for Nn in range(1, 8):
            rec("L5.1 (28) A <= h/N + rho B (N-1)/2", hQ/Nn + rho*B*(Nn-1)/2 - A, tag)
        rec("L7.1 (37) e(Q) <= 36J + 14 sqrt(rho) dH", 36*J + 14*np.sqrt(rho)*delta*h - e_fam(Q), tag)
        # Lemma 4.1 at lambda = lambda*(P) and 2x that
        lamstar = sparsity(fam, n)
        for lam in [lamstar, 2*lamstar + 1e-3]:
            d0 = e/h
            Phi = []
            for el, d, lab in subs:
                Phi.append((h_fam(quot_fam(R, lab)) + (2+d0)*h_fam(quot_fam(fam, lab)) + 4*lam*d, d, lab))
            mn = min(x[0] for x in Phi)
            G = min([x for x in Phi if x[0] <= mn + 1e-12], key=lambda x: x[1])
            P0 = quot_fam(fam, G[2]); h0 = h_fam(P0)
            rec("L4.1 h(P0)>0", h0 - 1e-12, tag)
            if h0 > 1e-12:
                rec("L4.1 ratio e(P0)/h(P0) >= d", e_fam(P0)/h0 - d0, tag)
                # sparsity on the quotient: test via preimage subspaces W >= G in V
                Gset = set(subs[[id(x[2]) for x in subs].index(id(G[2]))][0].tolist())
                for el, d, lab in subs:
                    if not Gset <= set(el.tolist()): continue
                    dW = d - G[1]
                    # F_{qG P}(W) = h(qG P) - h(q_{W'} P)
                    FP = h0 - h_fam(quot_fam(fam, lab)); FR = h_fam(quot_fam(R, G[2])) - h_fam(quot_fam(R, lab))
                    rec("L4.1 P0 is 2lam-sparse", 2*lam*dW - FP, tag)
                    rec("L4.1 P0*P0 is 4lam-sparse", 4*lam*dW - FR, tag)
            # Lemma 9.1
            Ob = [(h_fam(quot_fam(fam, lab)) + lam*d, d, lab, el) for el, d, lab in subs]
            mn = min(x[0] for x in Ob); G9 = [x for x in Ob if x[0] <= mn + 1e-12][0]
            rec("L9.1 dim G <= h/lam", h/lam - G9[1], tag)
            Gset = set(G9[3].tolist()); hG = h_fam(quot_fam(fam, G9[2]))
            for el, d, lab in subs:
                if Gset <= set(el.tolist()):
                    rec("L9.1 qG P is lam-sparse", lam*(d - G9[1]) - (hG - h_fam(quot_fam(fam, lab))), tag)
    print("fam n", n, "done", time.time()-t0, flush=True)

out = {k: v for k, v in sorted(res.items())}
json.dump(out, open(f"results_lemmas_{sys.argv[1] if len(sys.argv)>1 else 0}.json", "w"), indent=1, default=str)
for k, v in out.items():
    print(f"{k:55s} tests={v['tests']:6d} viol={v['violations']} min_slack={v['min_slack']:.3e}  worst={v['worst']}")
