import Mathlib
import EntropyLean.Basic

/-!
# Elementary entropy facts

Roadmap item A1: the pointwise bound `0 ≤ -p * log₂ p` for `0 ≤ p ≤ 1`, and nonnegativity of
`entropyBits` (for a law on a finite type, and also for a law on an arbitrary type, since the
`tsum` of nonnegative terms is nonnegative whether or not it converges).

What this file does NOT prove: no upper bound on entropy, no data-processing inequality, and
nothing about convolutions or quotients (roadmap items A2–A5, B2–B6).
-/

namespace EntropyLean

open scoped BigOperators

/-- `0 ≤ -p log₂ p` for `0 ≤ p ≤ 1`. -/
theorem negMulLogb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ -p * Real.logb 2 p := by
  have h : Real.logb 2 p ≤ 0 := by
    first
    | exact Real.logb_nonpos (by norm_num) hp0 hp1
    | (rw [Real.logb]
       exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hp0 hp1)
         (Real.log_nonneg (by norm_num)))
  have e : -p * Real.logb 2 p = p * (-Real.logb 2 p) := by ring
  rw [e]
  exact mul_nonneg hp0 (neg_nonneg.mpr h)

/-- A probability mass, as a real number, lies in `[0, 1]`. -/
theorem pmf_toReal_le_one {α : Type*} (P : PMF α) (a : α) : (P a).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (P.coe_le_one a)
  simpa using h

/-- Each term of the entropy sum is nonnegative. -/
theorem entropyBits_term_nonneg {α : Type*} (P : PMF α) (a : α) :
    0 ≤ -(P a).toReal * Real.logb 2 (P a).toReal :=
  negMulLogb_nonneg ENNReal.toReal_nonneg (pmf_toReal_le_one P a)

/-- Entropy of a law on a finite type is nonnegative. -/
theorem entropyBits_nonneg {α : Type*} [Fintype α] (P : PMF α) : 0 ≤ entropyBits P := by
  rw [entropyBits_eq_sum]
  exact Finset.sum_nonneg fun a _ => entropyBits_term_nonneg P a

/-- Entropy of a law on any type is nonnegative (the `tsum` of nonnegative terms). -/
theorem entropyBits_nonneg' {α : Type*} (P : PMF α) : 0 ≤ entropyBits P := by
  unfold entropyBits
  exact tsum_nonneg fun a => entropyBits_term_nonneg P a

end EntropyLean
