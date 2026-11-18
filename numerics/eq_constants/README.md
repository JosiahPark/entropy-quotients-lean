# Auxiliary constants and high-precision checks
For J. Park, "Dimension-free exponential entropy quotients over F_2", arXiv:2610.38525v1.
Generated 15 Nov 2026. Requires Python 3 with numpy and mpmath. Run every script from `scripts/`.

## 200-digit arithmetic (`mp.dps = 200`): `scripts/tests_prop93.py`
Rerunning this script reproduces `outputs/high_precision/prop93.log` exactly, in under 1 second.
- Prop 9.3 expansions at p = 2^-k (k = 2, ..., 256):
  - (h2 - p log2(1/p) - p log2 e)/p^2 -> -1/(2 ln 2) = -0.72134752...
  - (E - 2p)/(p^2 ln(1/p)) -> about 2.88
- Bernoulli witness for "c <= eps log2 C(eps)" for c in {1, 1.5, 1.9, 1.99}:
  - The largest working eps0 is 2.975 at c = 1 and 3.98 for c >= 1.9.
- (E/H) log2(1/lambda*) for a spike plus k directions (k = 1, 2, 4, 8), at p = 2^-K up to K = 10000:
  - The value climbs toward 2: 1.99734 at K = 10000, against the paper's constant of 320.
- Theorem 8.2 arithmetic: the supremum is 310.642, below the claimed 312.

## Lemma 8.1 in its regime (`mp.dps = 60`): `scripts/tests_l81.py`
- Regime: 1600 lambda <= d^2, with lambda about 1e-7 to 1e-14; 117 cases.
- Result: the growth factor (M - delta)/delta^2 was never below 0.511, against the claimed 1/148 ≈ 0.0068.
- Outputs: `outputs/high_precision/l81_*.{log,json}`.

## Worst-case constants (optimization over F_2^n, n <= 5): `scripts/tests_opt.py`, `scripts/tests_opt2.py`
| Quantity | Paper | Worst found | Outputs |
|---|---|---|---|
| Marton input (35): min_V d(K,U_V)/D(K) | 6 | 1.1708 (Bernoulli 0.110) | opt_marton |
| Lemma 6.3: E D/(3J) | 1 (constant 3) | 0.7294 (so 2.19 suffices) | opt_l63 |
| Thm 1.1 coefficient vs Bernoulli 1/h2(p_theta) | n/a | ratio <= 1.0009 (grid error) | opt_thm11 |
| Thm 1.2 ratio to Bernoulli curve | n/a | 0.99998 | opt_thm12 |
| Thm 8.2 arithmetic | < 312 | 310.64 | opt_thm82 |
| Lemma 5.1 (28) | equality at N = 2 (subspace-uniform laws) | tight | l51_* (via tests_l51.py) |

`tests_lemmas.py` is the exhaustive and adversarial check of Lemmas 2.1-9.1 (about 4.15M checks, 0 violations).
The full write-up is `REPORT.pdf`.

## Additional contents
- `scripts/`: the core library and generators (`eqlib.py`, `gens.py`, `fib.py`), every test script, and `lean_stats.py` (proof-size statistics).
- `outputs/lemmas/`: per-lemma check results (`results_lemmas_*.json`, `lemmas_*.log`).
- `outputs/constants/`: optimizer and Lemma 5.1 outputs, including the constrained Theorem 1.2 adversary (`opt_constrained*`).
- `outputs/high_precision/`: Proposition 9.3 at 200 digits and Lemma 8.1 at 60 digits.
- `lean/`: scratch files for the entropy-quotients-lean repo:
  - `Axioms2.lean` with its output `axioms.out`: `#print axioms` for 16 key results.
  - `Sanity.lean` with its output `sanity.out`: satisfiability witnesses, including `MartonInput` on the zero space.
