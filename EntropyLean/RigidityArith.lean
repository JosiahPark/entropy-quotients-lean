import Mathlib

/-!
# Iteration arithmetic of Theorem 8.2 (item D1)

This file proves the purely real-analytic part of the proof of Theorem 8.2 of
arXiv:2610.38525, equations (42)–(43):

* `inv_ratio_step` (42): if `0 < d ≤ 1` and `d' ≥ d + d²/148`, then `1/d' ≤ 1/d − 1/149`.
* `rigidity_arith_aux`: if `0 < d ≤ 1`, `N ≤ 149/d + 1` and `λ > d²/(1600 · 4^N)`, then
  `d · log₂(1/λ) < 320`.
* `rigidity_iteration_bound` (from (43)): the same with `N = ⌈149/d⌉`, i.e. if
  `λ > (d²/1600) · 4^(−⌈149/d⌉)` then `d · log₂(1/λ) < 320`.

The proof bounds `−d log d ≤ 1 − d` (from `log x ≤ x − 1`) instead of the paper's
`d log₂(1/d) ≤ 1/(e ln 2)`; this still gives a total below `311 + 2/ln 2 < 320`.

This file does NOT prove Theorem 8.2, Lemma 8.1, or anything about weighted families; it is
only the arithmetic used to turn Lemma 8.1 into the bound (41) (item D2).
-/

namespace EntropyLean

open Real

/-- Equation (42): one growth step `d' ≥ d + d²/148` with `d ≤ 1` lowers `1/d` by at least
`1/149`. -/
theorem inv_ratio_step {d d' : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) (hstep : d + d ^ 2 / 148 ≤ d') :
    1 / d' ≤ 1 / d - 1 / 149 := by
  have hpos : 0 < d + d ^ 2 / 148 := add_pos hd0 (div_pos (pow_pos hd0 2) (by norm_num))
  have h148 : (0 : ℝ) < 148 + d := by linarith
  have h1 : 1 / d' ≤ 1 / (d + d ^ 2 / 148) := one_div_le_one_div_of_le hpos hstep
  have h2 : 1 / (d + d ^ 2 / 148) = 1 / d - 1 / (148 + d) := by
    rw [eq_sub_iff_add_eq, div_add_div _ _ (ne_of_gt hpos) (ne_of_gt h148),
      div_eq_div_iff (mul_ne_zero (ne_of_gt hpos) (ne_of_gt h148)) (ne_of_gt hd0)]
    ring
  have h3 : 1 / (149 : ℝ) ≤ 1 / (148 + d) := one_div_le_one_div_of_le h148 (by linarith)
  linarith

/-- `−d log d ≤ 1 − d` for `d > 0`. -/
theorem neg_mul_log_le_one_sub {d : ℝ} (hd0 : 0 < d) : d * (-Real.log d) ≤ 1 - d := by
  have hinv : 0 < 1 / d := one_div_pos.mpr hd0
  have h1 : Real.log (1 / d) ≤ 1 / d - 1 := Real.log_le_sub_one_of_pos hinv
  have h2 : Real.log (1 / d) = -Real.log d := by rw [one_div, Real.log_inv]
  rw [h2] at h1
  have h3 : d * (-Real.log d) ≤ d * (1 / d - 1) := mul_le_mul_of_nonneg_left h1 hd0.le
  have h4 : d * (1 / d - 1) = 1 - d := by
    rw [mul_sub, mul_one_div_cancel (ne_of_gt hd0), mul_one]
  linarith

/-- `1/2 ≤ log 2`, from `log x ≤ x − 1` at `x = 1/2`. -/
theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h1 : Real.log (1 / 2 : ℝ) ≤ 1 / 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  linarith

/-- `log 1600 < 11 log 2`. -/
theorem log_1600_lt : Real.log 1600 < 11 * Real.log 2 := by
  have h : Real.log 1600 < Real.log ((2 : ℝ) ^ 11) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- The arithmetic of (43) with an explicit step count `N ≤ 149/d + 1`. -/
theorem rigidity_arith_aux {d lam : ℝ} {N : ℕ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hN : (N : ℝ) ≤ 149 / d + 1) (hlam : d ^ 2 / (1600 * (4 : ℝ) ^ N) < lam) :
    d * Real.logb 2 (1 / lam) < 320 := by
  have hL : (1 : ℝ) / 2 ≤ Real.log 2 := half_le_log_two
  have hLpos : 0 < Real.log 2 := by linarith
  have hd2 : 0 < d ^ 2 := pow_pos hd0 2
  have h4N : (0 : ℝ) < (4 : ℝ) ^ N := pow_pos (by norm_num) N
  have hA : (0 : ℝ) < 1600 * (4 : ℝ) ^ N := mul_pos (by norm_num) h4N
  have hlow : 0 < d ^ 2 / (1600 * (4 : ℝ) ^ N) := div_pos hd2 hA
  have hlam0 : 0 < lam := lt_trans hlow hlam
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 1600 * (4 : ℝ) ^ N / d ^ 2 := ⟨_, rfl⟩
  have hYpos : 0 < Y := by rw [hY]; exact div_pos hA hd2
  -- `1/λ < Y`
  have hinv : 1 / lam < Y := by
    rw [one_div_lt hlam0 hYpos, hY, one_div_div]
    exact hlam
  have hlogb : Real.logb 2 (1 / lam) < Real.logb 2 Y :=
    Real.logb_lt_logb (by norm_num) (one_div_pos.mpr hlam0) hinv
  -- `log Y = log 1600 + N · 2 log 2 − 2 log d`
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]
    push_cast
    ring
  have hlogY : Real.log Y = Real.log 1600 + (N : ℝ) * (2 * Real.log 2) - 2 * Real.log d := by
    rw [hY, Real.log_div (ne_of_gt hA) (ne_of_gt hd2),
      Real.log_mul (by norm_num : (1600 : ℝ) ≠ 0) (ne_of_gt h4N), Real.log_pow, Real.log_pow, h4]
    push_cast
    ring
  -- bounds
  have hdN : d * (N : ℝ) ≤ 149 + d := by
    have h' : (N : ℝ) - 1 ≤ 149 / d := by linarith
    rw [le_div_iff₀ hd0] at h'
    linarith
  have h1600 : 0 ≤ Real.log 1600 := Real.log_nonneg (by norm_num)
  have hB : d * Real.log 1600 ≤ Real.log 1600 := mul_le_of_le_one_left h1600 hd1
  have hC : Real.log 2 * (d * (N : ℝ)) ≤ Real.log 2 * (149 + d) :=
    mul_le_mul_of_nonneg_left hdN hLpos.le
  have hD : Real.log 2 * d ≤ Real.log 2 := mul_le_of_le_one_right hLpos.le hd1
  have hE : d * (-Real.log d) ≤ 1 - d := neg_mul_log_le_one_sub hd0
  have h11 : Real.log 1600 < 11 * Real.log 2 := log_1600_lt
  have key : d * Real.log Y < 320 * Real.log 2 := by
    rw [hlogY]
    linarith
  have hY' : d * Real.logb 2 Y < 320 := by
    have e : d * Real.logb 2 Y = d * Real.log Y / Real.log 2 := by
      unfold Real.logb
      ring
    rw [e, div_lt_iff₀ hLpos]
    exact key
  have := mul_lt_mul_of_pos_left hlogb hd0
  linarith

/-- Item D1, from (43): if `0 < d ≤ 1` and `λ > (d²/1600) · 4^(−⌈149/d⌉)`, written as
`λ > d² / (1600 · 4^⌈149/d⌉)`, then `d · log₂(1/λ) < 320`. -/
theorem rigidity_iteration_bound {d lam : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hlam : d ^ 2 / (1600 * (4 : ℝ) ^ ⌈149 / d⌉₊) < lam) :
    d * Real.logb 2 (1 / lam) < 320 := by
  have hN : ((⌈149 / d⌉₊ : ℕ) : ℝ) ≤ 149 / d + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (by norm_num) hd0.le)).le
  exact rigidity_arith_aux hd0 hd1 hN hlam

end EntropyLean
