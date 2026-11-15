# Numerical table: the single-bit lower bound of Proposition 9.3

Six rows of numerical values for arXiv:2610.38525, supplied by Josiah Park as a typeset table
(`table-entropy-quotients.html`, 2026-11-15), with what each column is as far as it could be
recomputed. Nothing here is formalized: the table is not part of the Lean library and is not
tracked in [ROADMAP.md](../ROADMAP.md) or [DEPENDENCIES.md](DEPENDENCIES.md).

## Table as supplied

| α | A(α) | B(α) | C(α) |
| :--- | :--- | :--- | :--- |
| 1.0 | 0.0795314 | 2.49672 | 1.0 |
| 0.5 | 0.0249421 | 5.93983 | 1.0 |
| 0.25 | 2.3145 × 10<sup>−3</sup> | 42.3749 | 1.00219 |
| 0.1 | 6.47959 × 10<sup>−7</sup> | 7.01494 × 10<sup>4</sup> | 1.96028 × 10<sup>2</sup> |
| 0.05 | 6.18066 × 10<sup>−13</sup> | 3.85226 × 10<sup>10</sup> | 2.61719 × 10<sup>7</sup> |
| 0.02 | 5.36087 × 10<sup>−31</sup> | 1.82879 × 10<sup>28</sup> | 1.95898 × 10<sup>24</sup> |

The source's caption is "Numerical results for varying parameter values"; it gives no definition
of the columns.

## What the columns are

| Column | Meaning | Check |
| --- | --- | --- |
| α | The parameter ε of Theorem 1.1 and Proposition 9.3 | fits columns A and B in all six rows |
| A(α) | p\*(ε): the root in (0, 1/2) of h₂(p) = (1 + ε)·(h₂(2p(1 − p)) − h₂(p)) | recomputed; agrees to all six digits in every row |
| B(α) | 1 / h₂(p\*(ε)) | recomputed; agrees to all six digits in every row |
| C(α) | **Not identified.** The source does not define it, and it is not one of the quantities above (it is smaller than B(α) in every row) | reproduced as supplied, unverified |

Here h₂(p) = −p log₂ p − (1 − p) log₂(1 − p), which is `binaryEntropy` in
`EntropyLean/Bernoulli.lean`.

### Why A and B matter

Take X to be one Bernoulli(p) bit, as in the paper's proof of Proposition 9.3. Then H(X) = h₂(p)
and D(X) = h₂(2p(1 − p)) − h₂(p) (`bernoulliIncrement`). The zero subspace satisfies
H(q_G X) ≤ (1 + ε) D(X) exactly when h₂(p) ≤ (1 + ε) D(X). On a grid of 4001 values of log₂(1/p)
between 1 and 2/ε + 60, this fails precisely for p > p\*(ε). For such p the only other subspace has
dimension one, so a coefficient C(ε) valid in Proposition 9.3 must satisfy 1 ≤ C(ε) h₂(p). Letting
p ↓ p\*(ε):

> C(ε) ≥ 1 / h₂(p\*(ε)) = B(ε).

So B is the paper's single-bit lower bound evaluated exactly instead of asymptotically. This is a
numerical illustration, not a proof: as of 2026-11-15 Proposition 9.3 is stated in Lean
(`exponential_scale_necessary`) but still `sorry`, and roadmap items E1–E3 are open.

### Recomputed values

| ε | p\*(ε) | 1 / h₂(p\*(ε)) | ε · log₂(1 / h₂(p\*(ε))) |
| :--- | :--- | :--- | :--- |
| 1.0 | 0.079531371 | 2.4967181 | 1.320 |
| 0.5 | 0.024942138 | 5.9398292 | 1.285 |
| 0.25 | 2.3144975 × 10<sup>−3</sup> | 42.374911 | 1.351 |
| 0.1 | 6.4795883 × 10<sup>−7</sup> | 7.0149438 × 10<sup>4</sup> | 1.610 |
| 0.05 | 6.1806573 × 10<sup>−13</sup> | 3.8522640 × 10<sup>10</sup> | 1.758 |
| 0.02 | 5.3608657 × 10<sup>−31</sup> | 1.8287945 × 10<sup>28</sup> | 1.878 |

The last column is ε log₂ of the lower bound. Since C(ε) ≥ B(ε), equation (4) of the paper
(lim inf ε log₂ C(ε) ≥ 2) follows if this column tends to 2; for small ε it climbs toward 2
slowly. Numerically log₂(1/p\*(ε)) − 2/ε is 0.5576, 0.5573, 0.5573 for ε = 0.1, 0.05,
0.02, and log₂(4/e) = 0.5573, consistent with p\*(ε) ≈ (e/4)·4<sup>−1/ε</sup> for small ε (the
value that the paper's two expansions give).

Script (Python with `mpmath`, 80 digits, bisection on log₂(1/p)):

```python
from mpmath import mp, mpf, log, nstr

mp.dps = 80
h2 = lambda p: -(p * log(p, 2) + (1 - p) * log(1 - p, 2))

def fails(t, eps):  # zero subspace fails for the Bernoulli(2^-t) bit
    p = mpf(2) ** (-t)
    return h2(p) > (1 + eps) * (h2(2 * p * (1 - p)) - h2(p))

for e in ["1.0", "0.5", "0.25", "0.1", "0.05", "0.02"]:
    eps, lo, hi = mpf(e), mpf(1), 2 / mpf(e) + 60  # fails at p = 1/2, passes at p = 2^-hi
    for _ in range(400):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if fails(mid, eps) else (lo, mid)
    p = mpf(2) ** (-lo)
    print(e, nstr(p, 8), nstr(1 / h2(p), 8), nstr(eps * log(1 / h2(p), 2), 4))
```

## LaTeX source

Compiles with `pdflatex` inside an `article` document (needs only `booktabs`); checked.

```latex
\begin{table}[ht]
\centering
\caption{Numerical results for varying parameter values.}
\begin{tabular}{@{}llll@{}}
\toprule
$\alpha$ & $A(\alpha)$ & $B(\alpha)$ & $C(\alpha)$ \\
\midrule
$1.0$  & $0.0795314$              & $2.49672$               & $1.0$ \\
$0.5$  & $0.0249421$              & $5.93983$               & $1.0$ \\
$0.25$ & $2.3145\times10^{-3}$    & $42.3749$               & $1.00219$ \\
$0.1$  & $6.47959\times10^{-7}$   & $7.01494\times10^{4}$   & $1.96028\times10^{2}$ \\
$0.05$ & $6.18066\times10^{-13}$  & $3.85226\times10^{10}$  & $2.61719\times10^{7}$ \\
$0.02$ & $5.36087\times10^{-31}$  & $1.82879\times10^{28}$  & $1.95898\times10^{24}$ \\
\bottomrule
\end{tabular}
\end{table}
```

## Provenance

The numbers in "Table as supplied" are Josiah Park's, copied from the final table shown in the
saved page. The page itself is not committed: it is a full browser save of a chat session, not a
standalone document. The column identification, the recomputation and the LaTeX above were done
with Claude Fable 5.2 (`claude-fable-5-2`), 2026-11-15.
