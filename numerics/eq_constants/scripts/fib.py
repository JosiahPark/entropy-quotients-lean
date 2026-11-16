import numpy as np
from eqlib import *
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

