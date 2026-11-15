import Mathlib
import EntropyLean.Bernoulli

/-!
# Bernoulli expansions for small `p` (roadmap item E2a)

Explicit two-sided bounds replacing the `O(·)` expansions used in the proof of Proposition 9.3.
For `0 < p < 1` (entropies in bits, `log` the natural logarithm):

* `binaryEntropy_ge`: `p logb 2 (1/p) + (p − p²) / log 2 ≤ h₂(p)`;
* `binaryEntropy_le`: `h₂(p) ≤ p logb 2 (1/p) + p / log 2` (that is, `+ p logb 2 e`);
* `bernoulliDefect_ge`: `2p − 2p² − 2p² / log 2 ≤ bernoulliDefect p = 2h₂(p) − h₂(2p(1−p))`.

Auxiliary: `bern_log_le_sub_one`, `one_sub_mul_log_one_sub_ge` (`−p ≤ (1−p) log(1−p)`),
`one_sub_mul_log_one_sub_le` (`(1−p) log(1−p) ≤ −p(1−p)`), `binaryEntropy_eq_nats`,
`bernoulliDefect_eq_nats`, `div_log2_le_div_log2`.

What this file does NOT prove: the upper bound `bernoulliDefect p ≤ 2p + O(p² log(1/p))`
(roadmap item E2b), and Proposition 9.3 itself (`exponential_scale_necessary`, item E3).
-/

namespace EntropyLean

/-- `log y ≤ y − 1` for `y > 0` (from `x + 1 ≤ exp x`). -/
theorem bern_log_le_sub_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y - 1 := by
  have h := Real.add_one_le_exp (Real.log y)
  rw [Real.exp_log hy] at h
  linarith

/-- `−p ≤ (1 − p) log(1 − p)` for `p < 1`. -/
theorem one_sub_mul_log_one_sub_ge {p : ℝ} (h1 : p < 1) :
    -p ≤ (1 - p) * Real.log (1 - p) := by
  have hq : 0 < 1 - p := by linarith
  have h := bern_log_le_sub_one (inv_pos.mpr hq)
  rw [Real.log_inv] at h
  have h2 := mul_le_mul_of_nonneg_left h hq.le
  rw [mul_sub, mul_inv_cancel₀ hq.ne'] at h2
  linarith

/-- `(1 − p) log(1 − p) ≤ −p(1 − p)` for `p < 1`. -/
theorem one_sub_mul_log_one_sub_le {p : ℝ} (h1 : p < 1) :
    (1 - p) * Real.log (1 - p) ≤ -(p * (1 - p)) := by
  have hq : 0 < 1 - p := by linarith
  have h := bern_log_le_sub_one hq
  have h2 := mul_le_mul_of_nonneg_left h hq.le
  linarith

/-- Dividing an inequality by `log 2 > 0`. -/
theorem div_log2_le_div_log2 {a b : ℝ} (h : a ≤ b) : a / Real.log 2 ≤ b / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hl.le)

/-- `h₂(p)` in natural logarithms, divided by `log 2`. -/
theorem binaryEntropy_eq_nats {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    binaryEntropy p = (-p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2 := by
  have hP : 0 < p ∧ p < 1 := ⟨h0, h1⟩
  unfold binaryEntropy
  rw [if_pos hP]
  simp only [Real.logb]
  ring

/-- **E2a, lower bound.** `p logb 2 (1/p) + (p − p²) / log 2 ≤ h₂(p)`. -/
theorem binaryEntropy_ge {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    p * Real.logb 2 (1 / p) + (p - p ^ 2) / Real.log 2 ≤ binaryEntropy p := by
  rw [binaryEntropy_eq_nats h0 h1]
  have e : p * Real.logb 2 (1 / p) + (p - p ^ 2) / Real.log 2 =
      (-(p * Real.log p) + (p - p ^ 2)) / Real.log 2 := by
    simp only [Real.logb, one_div, Real.log_inv]
    ring
  rw [e]
  apply div_log2_le_div_log2
  have F := one_sub_mul_log_one_sub_le h1
  linarith

/-- **E2a, upper bound.** `h₂(p) ≤ p logb 2 (1/p) + p / log 2`. -/
theorem binaryEntropy_le {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    binaryEntropy p ≤ p * Real.logb 2 (1 / p) + p / Real.log 2 := by
  rw [binaryEntropy_eq_nats h0 h1]
  have e : p * Real.logb 2 (1 / p) + p / Real.log 2 =
      (-(p * Real.log p) + p) / Real.log 2 := by
    simp only [Real.logb, one_div, Real.log_inv]
    ring
  rw [e]
  apply div_log2_le_div_log2
  have F := one_sub_mul_log_one_sub_ge h1
  linarith

theorem bernoulli_q_pos {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 0 < 2 * p * (1 - p) :=
  mul_pos (mul_pos (by norm_num) h0) (by linarith)

theorem bernoulli_q_lt_one {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : 2 * p * (1 - p) < 1 := by
  nlinarith [mul_pos h0 h0, sq_nonneg (1 - p)]

/-- The defect `2h₂(p) − h₂(2p(1−p))` in natural logarithms, divided by `log 2`. -/
theorem bernoulliDefect_eq_nats {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    bernoulliDefect p =
      (2 * (-p * Real.log p - (1 - p) * Real.log (1 - p)) -
        (-(2 * p * (1 - p)) * Real.log (2 * p * (1 - p)) -
          (1 - 2 * p * (1 - p)) * Real.log (1 - 2 * p * (1 - p)))) / Real.log 2 := by
  have hQ : 0 < 2 * p * (1 - p) ∧ 2 * p * (1 - p) < 1 :=
    ⟨bernoulli_q_pos h0 h1, bernoulli_q_lt_one h0 h1⟩
  unfold bernoulliDefect
  rw [binaryEntropy_eq_nats h0 h1, binaryEntropy_eq_nats hQ.1 hQ.2]
  ring

/-- **E2a, defect.** `2p − 2p² − 2p² / log 2 ≤ bernoulliDefect p` for `0 < p < 1`. -/
theorem bernoulliDefect_ge {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    2 * p - 2 * p ^ 2 - 2 * p ^ 2 / Real.log 2 ≤ bernoulliDefect p := by
  have hc : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [bernoulliDefect_eq_nats h0 h1]
  have e : 2 * p - 2 * p ^ 2 - 2 * p ^ 2 / Real.log 2 =
      ((2 * p - 2 * p ^ 2) * Real.log 2 - 2 * p ^ 2) / Real.log 2 := by
    first
      | (field_simp; ring)
      | field_simp
      | rw [sub_div, mul_div_cancel_right₀ _ hc]
  rw [e]
  apply div_log2_le_div_log2
  have hlog : Real.log (2 * p * (1 - p)) = Real.log 2 + Real.log p + Real.log (1 - p) := by
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 2) h0).ne' (sub_pos.2 h1).ne',
      Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) h0.ne']
  rw [hlog]
  have F1 := one_sub_mul_log_one_sub_ge h1
  have F2 := one_sub_mul_log_one_sub_le h1
  have F3 := one_sub_mul_log_one_sub_ge (bernoulli_q_lt_one h0 h1)
  have F4 : p * (-p) ≤ p * ((1 - p) * Real.log (1 - p)) := mul_le_mul_of_nonneg_left F1 h0.le
  have ha : Real.log p < 0 := Real.log_neg h0 h1
  have F5 : p ^ 2 * Real.log p ≤ p ^ 2 * 0 := mul_le_mul_of_nonneg_left ha.le (sq_nonneg p)
  linarith

end EntropyLean
