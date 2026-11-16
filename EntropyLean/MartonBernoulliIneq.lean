import Mathlib
import EntropyLean.BernoulliExpansion
import EntropyLean.BernoulliLaw
import EntropyLean.MartonInput

/-!
# The Bernoulli inequality behind (35) on one-bit spaces (roadmap item H4b)

Proved here, for `0 ≤ p ≤ 1` (entropies in bits):

* `bernoulli_marton_ineq`: `min(h₂(p), 1 − h₂(p)) ≤ 12 (h₂(2p(1−p)) − h₂(p))`.

Auxiliary results:
* `binaryEntropy_one_sub`, `bernoulliIncrement_one_sub`: symmetry under `p ↦ 1 − p`;
* `negMulLog_mix`: the concavity inequality for `−x log x` (from `Real.concaveOn_negMulLog`);
* `bernoulli_concave_step`: `h₂(2p(1−p)) − h₂(p) ≥ 2p(1 − h₂(p))` for `0 < p ≤ 1/2`, since
  `2p(1−p) = (1−2p)·p + 2p·(1/2)` (concavity at the points `p` and `1/2`);
* `bernoulli_marton_small_nats`: for `0 < p ≤ 1/8`, `13 H(p) ≤ 12 H(2p(1−p))` in nats, from the
  elementary bounds of `EntropyLean/BernoulliExpansion.lean` and `log p ≤ −3 log 2`;
* `bernoulli_marton_ineq_le_half`: the inequality for `0 ≤ p ≤ 1/2` (cases `p = 0`, `p ≤ 1/8`,
  `1/8 < p ≤ 1/2`).

What this file does NOT prove: `martonInput_of_finrank_le_one` (roadmap item H4c, which combines
this inequality with `martonInput_of_finrank_eq_one_of_bernoulli`), and the entropic Marton bound
(35) in any dimension `≥ 2`.
-/

namespace EntropyLean

/-- Binary entropy is symmetric under `p ↦ 1 − p`. -/
theorem binaryEntropy_one_sub (p : ℝ) : binaryEntropy (1 - p) = binaryEntropy p := by
  unfold binaryEntropy
  by_cases h : 0 < p ∧ p < 1
  · rw [if_pos h, if_pos ⟨by linarith [h.2], by linarith [h.1]⟩, sub_sub_cancel]
    ring
  · rw [if_neg h, if_neg]
    rintro ⟨ha, hb⟩
    exact h ⟨by linarith, by linarith⟩

/-- The Bernoulli increment is symmetric under `p ↦ 1 − p`. -/
theorem bernoulliIncrement_one_sub (p : ℝ) :
    bernoulliIncrement (1 - p) = bernoulliIncrement p := by
  unfold bernoulliIncrement
  rw [show (2 : ℝ) * (1 - p) * (1 - (1 - p)) = 2 * p * (1 - p) by ring, binaryEntropy_one_sub]

/-- Concavity of `−x log x` on `[0, ∞)`, with the mixed point named `z`. -/
theorem negMulLog_mix {x y a b z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hz : a * x + b * y = z) :
    a * (-x * Real.log x) + b * (-y * Real.log y) ≤ -z * Real.log z := by
  have hc : ConcaveOn ℝ (Set.Ici (0 : ℝ)) Real.negMulLog := by
    first
      | exact Real.concaveOn_negMulLog
      | exact Real.strictConcaveOn_negMulLog.concaveOn
  have h := hc.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) ha hb hab
  simp only [smul_eq_mul] at h
  rw [hz] at h
  first
    | (simp only [Real.negMulLog] at h; linarith)
    | (unfold Real.negMulLog at h; linarith)

/-- `H(p) ≤ 12 (H(2p(1−p)) − H(p))` in nats for `0 < p ≤ 1/8`. -/
theorem bernoulli_marton_small_nats {p : ℝ} (h0 : 0 < p) (h8 : p ≤ 1 / 8) :
    -p * Real.log p - (1 - p) * Real.log (1 - p) ≤
      12 * ((-(2 * p * (1 - p)) * Real.log (2 * p * (1 - p)) -
          (1 - 2 * p * (1 - p)) * Real.log (1 - 2 * p * (1 - p))) -
        (-p * Real.log p - (1 - p) * Real.log (1 - p))) := by
  have h1 : p < 1 := by linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlq : Real.log (2 * p * (1 - p)) = Real.log 2 + Real.log p + Real.log (1 - p) := by
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 2) h0).ne' (sub_pos.2 h1).ne',
      Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) h0.ne']
  have hlp : Real.log p ≤ -(3 * Real.log 2) := by
    have h : Real.log p ≤ Real.log (1 / 8) := by
      first
        | exact Real.log_le_log h0 h8
        | exact Real.log_le_log_of_le h0 h8
    have e : Real.log ((1 : ℝ) / 8) = -(3 * Real.log 2) := by
      rw [show (1 : ℝ) / 8 = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      first
        | norm_num
        | (push_cast; ring)
    linarith
  have F1 := one_sub_mul_log_one_sub_ge h1
  have F3 := one_sub_mul_log_one_sub_le (bernoulli_q_lt_one h0 h1)
  have P2 : (11 * p - 24 * p ^ 2) * (3 * Real.log 2) ≤ (11 * p - 24 * p ^ 2) * (-Real.log p) :=
    mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
  have P3 : 0 ≤ p * (3 - 16 * p) * Real.log 2 :=
    mul_nonneg (mul_nonneg h0.le (by linarith)) hl.le
  have P4 : (1 - 2 * p) * (-p) ≤ (1 - 2 * p) * ((1 - p) * Real.log (1 - p)) :=
    mul_le_mul_of_nonneg_left F1 (by linarith)
  have P5 : 48 * p ^ 2 * (1 - p) ^ 2 ≤ 11 * p := by
    have a : (1 - p) ^ 2 ≤ 1 := by nlinarith
    have b := mul_le_mul_of_nonneg_left a (sq_nonneg p)
    have c := mul_le_mul_of_nonneg_left h8 h0.le
    nlinarith
  rw [hlq]
  linarith

/-- Concavity step: `h₂(2p(1−p)) − h₂(p) ≥ 2p(1 − h₂(p))` for `0 < p ≤ 1/2`. -/
theorem bernoulli_concave_step {p : ℝ} (hp : 0 < p) (h2 : p ≤ 1 / 2) :
    2 * p * (1 - binaryEntropy p) ≤ binaryEntropy (2 * p * (1 - p)) - binaryEntropy p := by
  have h1 : p < 1 := by linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl' : Real.log 2 ≠ 0 := hl.ne'
  have hq0 := bernoulli_q_pos hp h1
  have hq1 := bernoulli_q_lt_one hp h1
  have hl2 : Real.log 2⁻¹ = -Real.log 2 := Real.log_inv 2
  have k1 := negMulLog_mix hp.le (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
    (show 0 ≤ 1 - 2 * p by linarith) (show 0 ≤ 2 * p by linarith) (by ring)
    (show (1 - 2 * p) * p + 2 * p * 2⁻¹ = 2 * p * (1 - p) by ring)
  have k2 := negMulLog_mix (show 0 ≤ 1 - p by linarith) (show (0 : ℝ) ≤ 2⁻¹ by norm_num)
    (show 0 ≤ 1 - 2 * p by linarith) (show 0 ≤ 2 * p by linarith) (by ring)
    (show (1 - 2 * p) * (1 - p) + 2 * p * 2⁻¹ = 1 - 2 * p * (1 - p) by ring)
  rw [hl2] at k1 k2
  have hHp : binaryEntropy p * Real.log 2 = -p * Real.log p - (1 - p) * Real.log (1 - p) := by
    rw [binaryEntropy_eq_nats hp h1]
    first
      | exact div_mul_cancel₀ _ hl'
      | field_simp
  have hHq : binaryEntropy (2 * p * (1 - p)) * Real.log 2 =
      -(2 * p * (1 - p)) * Real.log (2 * p * (1 - p)) -
        (1 - 2 * p * (1 - p)) * Real.log (1 - 2 * p * (1 - p)) := by
    rw [binaryEntropy_eq_nats hq0 hq1]
    first
      | exact div_mul_cancel₀ _ hl'
      | field_simp
  have hconc : (1 - 2 * p) * (binaryEntropy p * Real.log 2) + 2 * p * Real.log 2 ≤
      binaryEntropy (2 * p * (1 - p)) * Real.log 2 := by
    rw [hHp, hHq]
    linarith
  by_contra hc
  push_neg at hc
  have := mul_lt_mul_of_pos_right hc hl
  linarith

/-- The Bernoulli inequality on `[0, 1/2]`. -/
theorem bernoulli_marton_ineq_le_half {p : ℝ} (h0 : 0 ≤ p) (h2 : p ≤ 1 / 2) :
    min (binaryEntropy p) (1 - binaryEntropy p) ≤ 12 * bernoulliIncrement p := by
  rcases eq_or_lt_of_le h0 with h | hp
  · subst h
    have hz : binaryEntropy 0 = 0 := binaryEntropy_eq_zero_of_not_mem 0 (fun h => lt_irrefl _ h.1)
    have hq : (2 : ℝ) * 0 * (1 - 0) = 0 := by ring
    unfold bernoulliIncrement
    rw [hq, hz]
    exact min_le_of_left_le (by norm_num)
  have h1 : p < 1 := by linarith
  rcases le_or_lt p (1 / 8) with h8 | h8
  · apply min_le_of_left_le
    unfold bernoulliIncrement
    rw [binaryEntropy_eq_nats hp h1,
      binaryEntropy_eq_nats (bernoulli_q_pos hp h1) (bernoulli_q_lt_one hp h1),
      ← sub_div, ← mul_div_assoc]
    apply div_log2_le_div_log2
    linarith [bernoulli_marton_small_nats hp h8]
  · have hD := bernoulli_concave_step hp h2
    have hDnn : 0 ≤ bernoulliIncrement p := by
      rw [← entropyIncrement_bernoulliBit p hp.le h1.le]
      exact entropyIncrement_nonneg _
    unfold bernoulliIncrement at hDnn ⊢
    apply min_le_of_right_le
    rcases le_or_lt (binaryEntropy p) 1 with hh | hh
    · have := mul_le_mul_of_nonneg_right h8.le (sub_nonneg.2 hh)
      linarith
    · linarith

/-- **H4b.** `min(h₂(p), 1 − h₂(p)) ≤ 12 (h₂(2p(1−p)) − h₂(p))` for `0 ≤ p ≤ 1`. -/
theorem bernoulli_marton_ineq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    min (binaryEntropy p) (1 - binaryEntropy p) ≤ 12 * bernoulliIncrement p := by
  rcases le_total p (1 / 2) with h | h
  · exact bernoulli_marton_ineq_le_half h0 h
  · have := bernoulli_marton_ineq_le_half (p := 1 - p) (by linarith) (by linarith)
    rw [binaryEntropy_one_sub, bernoulliIncrement_one_sub] at this
    exact this

end EntropyLean
