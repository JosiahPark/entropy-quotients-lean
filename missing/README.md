# Missing: draft items not yet in the library

Declarations from the original drafts in [`archive/`](../archive) that have no counterpart in
`EntropyLean/`. They are collected verbatim in [`DraftLeftovers.lean`](DraftLeftovers.lean) so they
are not lost. The other draft contents (definitions, families, Theorems 1.1, 1.2, 8.2,
Lemmas 2.1, 2.2, 4.1, 9.1, Proposition 9.3) already have counterparts in `EntropyLean/`, either
stated or proved.

This folder is **not built** (`lakefile.toml` builds only `EntropyLean/`), is **not scanned** by
`scripts/audit_sorries.py`, and is **not tracked** in [ROADMAP.md](../ROADMAP.md) or
[docs/DEPENDENCIES.md](../docs/DEPENDENCIES.md). Nothing here is proved.

Compiled and checked with Claude Fable 5.2 (`claude-fable-5-2`), 2026-11-15. The excerpts in
`DraftLeftovers.lean` are unchanged draft text and were not written by Fable 5.2; the table and
notes below were.

## Items

| Item | Source | What it states | Closest in `EntropyLean/` | Notes |
| --- | --- | --- | --- | --- |
| `binEntropyBits`, `binEntropy_bits_eq` | `archive/EntropyQuotients.lean` 142–146, 168–178 | On `(0, 1)`, binary entropy in bits equals Mathlib's `Real.binEntropy p / Real.log 2` | `binaryEntropy` (`Bernoulli.lean`) has the same formula, but no link to `Real.binEntropy` | Draft proof is `sorry` followed by `ring`, which fails (no goals left). The link would give access to Mathlib's `Real.binEntropy` lemmas. |
| `binEntropyBits_pos` | `archive/EntropyQuotients.lean` 148–150 | `0 < h₂(p)` for `0 < p < 1` | none | `sorry`. Should follow from the line above and Mathlib's positivity of `Real.binEntropy`. |
| `bernoulli_defect_ratio_exceeds` | `archive/EntropyQuotients.lean` 152–162 | For `p = 2^(−c/ε)`, `0 < c < 2`, eventually as `ε ↓ 0`: `0 < p < 1`, `h₂(p) > 0`, and `E/H > ε/(1+ε)` | `bernoulli_parameter_mem_Ioo` proves `0 < p < 1` | The ratio clause is `True` (placeholder); positivity is missing. |
| `binEntropyBits_asymp` | `archive/EntropyQuotients.lean` 180–184 | `h₂(p) = p log₂(1/p) + p log₂ e + o(p log₂(1/p))` | none (the intent matches roadmap item E2) | `o(…)` is not Lean syntax; E2 asks for explicit inequalities instead. |
| `bernoulli_necessity_example` | `archive/Entropy.lean` 147–159 | `h₂(2^(−c/ε)) > 0` for `0 < c < 2`, `ε > 0` | none | Uses that draft's own `binaryEntropy` (zero only at `p = 0, 1`, not outside `[0, 1]`). The ratio clause is `True`. |
| `h2`, `D_bern`, `prop_9_3_necessity` | `archive/EntropyQuotients_formalization.lean` 31–52 | Proposition 9.3 reduced to a statement about `h₂` alone: if the zero subspace failing forces `C(ε) ≥ 1/h₂(p)`, then `liminf ε log₂ C(ε) ≥ 2` | `exponential_scale_necessary` (`Statements.lean`) states Prop 9.3 in full form; `h2` is `binaryEntropy` | **Bug:** `D_bern` is documented as the increment `D` but computes the defect `E = 2h₂(p) − h₂(2p(1−p))` (that is `bernoulliDefect`). With `E`, for each `ε` the hypothesis `h2 p > (1 + ε) * D_bern p` holds for all sufficiently small `p` (since `E ≈ 2p` and `h₂(p) ≈ p log₂(1/p)`), and `1 / h2 p → ∞`, so no real-valued `C` satisfies `hvalid` and the theorem is vacuous. With `bernoulliIncrement` in place of `D_bern` it is the intended analytic core. It also uses `liminf`, which the repository's statement avoids (junk value for functions unbounded above). |

## Not collected here

- `archive/FeatureMap.lean` was deleted in 9fe40bc and is not restored.
- `h2_zero_at_extremes` (inside the excerpt, kept for context) duplicates
  `binaryEntropy_eq_zero_of_not_mem`; it is not a missing item.
- The uploads `entropy-lean-cleaned.zip` and `entropy-lean.git.bundle` contain the same 18 files,
  the v0.1 snapshot imported in a4c277b; they add nothing beyond the items above.
