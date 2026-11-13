import EntropyLean.Basic

/-! A single Bernoulli entropy API, replacing three near-identical definitions. -/

namespace EntropyLean

/-- Binary entropy in bits, set to zero outside the open unit interval. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then
    -p * Real.logb 2 p - (1-p) * Real.logb 2 (1-p)
  else 0

/-- This lemma is fully proved by definition. -/
theorem binaryEntropy_eq_zero_of_not_mem (p : ℝ)
    (h : ¬ (0 < p ∧ p < 1)) : binaryEntropy p = 0 := by
  simp [binaryEntropy, h]

/-- Entropy increase of the sum of independent Bernoulli(p) bits over F₂. -/
noncomputable def bernoulliIncrement (p : ℝ) : ℝ :=
  binaryEntropy (2 * p * (1-p)) - binaryEntropy p

/-- Entropy defect `H - D`, not the entropy increment. -/
noncomputable def bernoulliDefect (p : ℝ) : ℝ :=
  2 * binaryEntropy p - binaryEntropy (2 * p * (1-p))

/-- This is only a target statement; the required asymptotic analysis is missing. -/
theorem bernoulli_asymptotic_target
    (c : ℝ) (hc : 0 < c ∧ c < 2) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      let p := (2 : ℝ) ^ (-c / ε)
      0 < p ∧ p < 1 := by
  sorry

end EntropyLean
