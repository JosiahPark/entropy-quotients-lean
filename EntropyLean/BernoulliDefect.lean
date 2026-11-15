import Mathlib
import EntropyLean.BernoulliExpansion

/-!
# Upper bound for the Bernoulli defect (roadmap item E2b)

For `0 < p < 1` let `q = 2p(1 − p)`, the parameter of the sum of two independent Bernoulli(p)
bits. The defect `bernoulliDefect p = 2h₂(p) − h₂(q)` (bits) satisfies

* `bernoulliDefect_le`: `bernoulliDefect p ≤ 2p + 2p² logb 2 (1/p) + 4p² / log 2`, the explicit
  form of `bernoulliDefect p ≤ 2p + O(p² log(1/p))`;
* `bernoulliDefect_sub_abs_le`: together with `bernoulliDefect_ge` (item E2a),
  `|bernoulliDefect p − 2p| ≤ 2p² logb 2 (1/p) + 4p² / log 2`, i.e. the expansion
  `bernoulliDefect p = 2p + O(p² log(1/p))` with explicit constants.

Proof: in natural logarithms, `log q = log 2 + log p + log(1 − p)` turns the defect into
`−2p² log p + q log 2 − 2(1 − p)² log(1 − p) + (1 − q) log(1 − q)`; then
`(1 − p) log(1 − p) ≥ −p` and `(1 − q) log(1 − q) ≤ −q(1 − q)` (both from `log y ≤ y − 1`),
`q² ≤ 4p²` and `q log 2 ≤ 2p log 2`.

Auxiliary: `bern_div_le_add_div`, `bern_logb_inv_nonneg` (`0 ≤ logb 2 (1/p)`),
`bern_sq_le_div_log_two` (`p² ≤ p² / log 2`).

What this file does NOT prove: Proposition 9.3 (`exponential_scale_necessary`, roadmap item E3).
-/

namespace EntropyLean

/-- `N / L ≤ a + M / L` from `N − M ≤ a L` when `L > 0`. -/
theorem bern_div_le_add_div {N M a L : ℝ} (hL : 0 < L) (h : N - M ≤ a * L) :
    N / L ≤ a + M / L := by
  have h2 : N / L - M / L ≤ a := by
    rw [← sub_div, div_le_iff₀ hL]
    exact h
  linarith

/-- **E2b.** `bernoulliDefect p ≤ 2p + 2p² logb 2 (1/p) + 4p² / log 2` for `0 < p < 1`. -/
theorem bernoulliDefect_le {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    bernoulliDefect p ≤ 2 * p + 2 * p ^ 2 * Real.logb 2 (1 / p) + 4 * p ^ 2 / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : 2 * p + 2 * p ^ 2 * Real.logb 2 (1 / p) + 4 * p ^ 2 / Real.log 2 =
      2 * p + (-(2 * p ^ 2 * Real.log p) + 4 * p ^ 2) / Real.log 2 := by
    simp only [Real.logb, one_div, Real.log_inv]
    ring
  rw [e, bernoulliDefect_eq_nats h0 h1]
  apply bern_div_le_add_div hl
  have hlog : Real.log (2 * p * (1 - p)) = Real.log 2 + Real.log p + Real.log (1 - p) := by
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 2) h0).ne' (sub_pos.2 h1).ne',
      Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) h0.ne']
  rw [hlog]
  have F1 := one_sub_mul_log_one_sub_ge h1
  have Fq := one_sub_mul_log_one_sub_le (bernoulli_q_lt_one h0 h1)
  have F4 : (1 - p) * (-p) ≤ (1 - p) * ((1 - p) * Real.log (1 - p)) :=
    mul_le_mul_of_nonneg_left F1 (by linarith)
  have F5 : 0 ≤ p ^ 3 * (2 - p) := mul_nonneg (pow_nonneg h0.le 3) (by linarith)
  have F6 : 0 ≤ p ^ 2 * Real.log 2 := mul_nonneg (sq_nonneg p) hl.le
  linarith

/-- `0 ≤ logb 2 (1/p)` for `0 < p < 1`. -/
theorem bern_logb_inv_nonneg {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    0 ≤ Real.logb 2 (1 / p) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [Real.logb, one_div, Real.log_inv]
  exact div_nonneg (neg_nonneg.mpr (Real.log_neg h0 h1).le) hl.le

/-- `p² ≤ p² / log 2`, since `log 2 ≤ 1`. -/
theorem bern_sq_le_div_log_two (p : ℝ) : p ^ 2 ≤ p ^ 2 / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    have h := bern_log_le_sub_one (show (0 : ℝ) < 2 by norm_num)
    linarith
  rw [le_div_iff₀ hl]
  have h2 := mul_le_mul_of_nonneg_left hL1 (sq_nonneg p)
  linarith

/-- **E2b, two-sided form.** `|bernoulliDefect p − 2p| ≤ 2p² logb 2 (1/p) + 4p² / log 2` for
`0 < p < 1`: the expansion `bernoulliDefect p = 2p + O(p² log(1/p))` with explicit constants. -/
theorem bernoulliDefect_sub_abs_le {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    |bernoulliDefect p - 2 * p| ≤
      2 * p ^ 2 * Real.logb 2 (1 / p) + 4 * p ^ 2 / Real.log 2 := by
  have hup := bernoulliDefect_le h0 h1
  have hlo := bernoulliDefect_ge h0 h1
  have hA := mul_nonneg (sq_nonneg p) (bern_logb_inv_nonneg h0 h1)
  have hB := bern_sq_le_div_log_two p
  have e2 : 2 * p ^ 2 / Real.log 2 = 2 * (p ^ 2 / Real.log 2) := by ring
  have e4 : 4 * p ^ 2 / Real.log 2 = 4 * (p ^ 2 / Real.log 2) := by ring
  rw [e2] at hlo
  rw [e4] at hup
  rw [e4, abs_le]
  constructor
  · linarith
  · linarith

end EntropyLean
