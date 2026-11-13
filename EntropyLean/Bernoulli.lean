import EntropyLean.Basic

/-!
# Binary entropy and the Bernoulli example of Proposition 9.3

`binaryEntropy p = h₂(p)` in bits, and the increment / defect of a single Bernoulli(p) bit over
F₂ (the sum of two independent Bernoulli(p) bits is Bernoulli(2p(1-p))).

What this file does NOT prove: the asymptotic expansions of `h₂(p)` and `2h₂(p) - h₂(2p(1-p))`
used in the proof of Proposition 9.3, and the identification of `binaryEntropy` with
`entropyBits` of a Bernoulli law. Proved: `binaryEntropy_eq_zero_of_not_mem` and
`bernoulli_parameter_mem_Ioo` (the parameter `p = 2^{-c/ε}` lies in `(0, 1)` for every `ε > 0`).
-/

namespace EntropyLean

/-- Binary entropy in bits, set to zero outside the open unit interval. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then
    -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)
  else 0

theorem binaryEntropy_eq_zero_of_not_mem (p : ℝ)
    (h : ¬ (0 < p ∧ p < 1)) : binaryEntropy p = 0 := by
  simp [binaryEntropy, h]

/-- Entropy increment `D` of a Bernoulli(p) bit: `h₂(2p(1-p)) - h₂(p)`. -/
noncomputable def bernoulliIncrement (p : ℝ) : ℝ :=
  binaryEntropy (2 * p * (1 - p)) - binaryEntropy p

/-- Entropy defect `E` of a Bernoulli(p) bit: `2h₂(p) - h₂(2p(1-p))`. -/
noncomputable def bernoulliDefect (p : ℝ) : ℝ :=
  2 * binaryEntropy p - binaryEntropy (2 * p * (1 - p))

/-- The parameter `p = 2^{-c/ε}` of Proposition 9.3 lies in `(0, 1)` for all `ε > 0`. -/
theorem bernoulli_parameter_mem_Ioo (c : ℝ) (hc : 0 < c) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < (2 : ℝ) ^ (-c / ε) ∧ (2 : ℝ) ^ (-c / ε) < 1 := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0 : ℝ) < ε := Set.mem_Ioi.mp hε
  have hx : -c / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε'
  refine ⟨by positivity, ?_⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hx

end EntropyLean
