import Mathlib
import EntropyLean.ScaleNecessary
import EntropyLean.ScaleNecessaryLimit

/-!
# Proposition 9.3, analytic step: the logarithmic bound (roadmap item E3b2)

With `p = scaleParam a ε = 2^(−a/ε)` (item E3b1, `EntropyLean/ScaleNecessaryLimit.lean`), proved
here for `a > 0` and `ε > 0`:

* `slog_logb_scaleParam`: `log₂ p = −a/ε`;
* `slog_entropy_pos`, `slog_entropy_le`: `0 < h₂(p) ≤ p (a/ε + 2)` (from `binaryEntropy_ge`,
  `binaryEntropy_le` and `1/2 ≤ log 2`);
* `slog_small`: for `g > 0`, `0 < ε ≤ 1` and `16 (a + 2) ε ≤ g²`, `ε log₂(a/ε + 2) ≤ g`
  (from `log x ≤ x − 1` at `x = y/T` and at `x = T`, with `y = a/ε + 2`, `T = 4(a + 2)/g`);
* `scale_log_of_le`: for `c < a`, `0 < ε ≤ 1` and `16 (a + 2) ε ≤ (a − c)²`,
  `c ≤ −ε log₂ h₂(p)`;
* `scale_log_eventually` (E3b2): for `0 < a` and `c < a`, eventually as `ε ↓ 0`,
  `c ≤ −ε log₂ h₂(2^(−a/ε))`.

The argument is the one in `EntropyLean/ScaleNecessaryProof.lean` on branch `formalize-efg`
(commit 38f8074); the declaration names here are different, so both files can coexist after a
merge.

What this file does NOT prove: Proposition 9.3 itself (`exponential_scale_necessary`, item E3c),
which combines `scale_log_eventually` with `scale_gap_eventually` (E3b1) and
`one_le_C_mul_binaryEntropy` (E3a). Nothing here concerns Theorems 1.1, 1.2 or 8.2.
-/

namespace EntropyLean

open Filter

/-- `log₂ p = −a/ε` for `p = 2^(−a/ε)`. -/
theorem slog_logb_scaleParam (a ε : ℝ) : Real.logb 2 (scaleParam a ε) = -(a / ε) := by
  unfold scaleParam
  exact Real.logb_rpow (by norm_num) (by norm_num)

/-- `h₂(p) ≤ p (a/ε + 2)` for `p = 2^(−a/ε)`. -/
theorem slog_entropy_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    binaryEntropy (scaleParam a ε) ≤ scaleParam a ε * (a / ε + 2) := by
  have hL : (1 : ℝ) / 2 ≤ Real.log 2 := half_le_log_two
  have hLpos : 0 < Real.log 2 := by linarith
  have hp0 := scaleParam_pos a ε
  have hp1 := scaleParam_lt_one ha hε
  have h := binaryEntropy_le hp0 hp1
  rw [logb_inv_scaleParam] at h
  have h2 : scaleParam a ε / Real.log 2 ≤ 2 * scaleParam a ε := by
    rw [div_le_iff₀ hLpos]
    nlinarith [mul_nonneg hp0.le (sub_nonneg.2 hL)]
  have e : scaleParam a ε * (a / ε + 2) = scaleParam a ε * (a / ε) + 2 * scaleParam a ε := by
    ring
  rw [e]
  linarith

/-- `h₂(p) > 0` for `p = 2^(−a/ε)`. -/
theorem slog_entropy_pos {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    0 < binaryEntropy (scaleParam a ε) := by
  have hLpos : 0 < Real.log 2 := by linarith [half_le_log_two]
  have hp0 := scaleParam_pos a ε
  have hp1 := scaleParam_lt_one ha hε
  have h := binaryEntropy_ge hp0 hp1
  rw [logb_inv_scaleParam] at h
  have h1 : 0 < scaleParam a ε * (a / ε) := mul_pos hp0 (div_pos ha hε)
  have hpp : 0 ≤ scaleParam a ε - scaleParam a ε ^ 2 := by
    nlinarith [mul_nonneg hp0.le (sub_nonneg.2 hp1.le)]
  have h2 : 0 ≤ (scaleParam a ε - scaleParam a ε ^ 2) / Real.log 2 := div_nonneg hpp hLpos.le
  linarith

/-- For `a, g > 0`, `0 < ε ≤ 1` and `16 (a + 2) ε ≤ g²`: `ε log₂(a/ε + 2) ≤ g`. -/
theorem slog_small {a g ε : ℝ} (ha : 0 < a) (hg : 0 < g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεg : 16 * (a + 2) * ε ≤ g ^ 2) : ε * Real.logb 2 (a / ε + 2) ≤ g := by
  have hL : (1 : ℝ) / 2 ≤ Real.log 2 := half_le_log_two
  have hLpos : 0 < Real.log 2 := by linarith
  have hε' : ε ≠ 0 := hε.ne'
  have ha2 : (0 : ℝ) < 4 * (a + 2) := by linarith
  have hy : 0 < a / ε + 2 := add_pos (div_pos ha hε) (by norm_num)
  have hT : 0 < 4 * (a + 2) / g := div_pos ha2 hg
  have h1 : Real.log ((a / ε + 2) / (4 * (a + 2) / g)) ≤ (a / ε + 2) / (4 * (a + 2) / g) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hy hT)
  rw [Real.log_div hy.ne' hT.ne'] at h1
  have h2 : Real.log (4 * (a + 2) / g) ≤ 4 * (a + 2) / g - 1 := Real.log_le_sub_one_of_pos hT
  have hlogy : Real.log (a / ε + 2) ≤ (a / ε + 2) / (4 * (a + 2) / g) + 4 * (a + 2) / g := by
    linarith
  have hεa : ε * (a / ε) = a := by
    rw [mul_comm, div_mul_cancel₀ _ hε']
  have e1 : ε * ((a / ε + 2) / (4 * (a + 2) / g)) = (a + 2 * ε) * g / (4 * (a + 2)) := by
    calc ε * ((a / ε + 2) / (4 * (a + 2) / g))
        = (ε * (a / ε) + 2 * ε) / (4 * (a + 2) / g) := by ring
      _ = (a + 2 * ε) / (4 * (a + 2) / g) := by rw [hεa]
      _ = (a + 2 * ε) * g / (4 * (a + 2)) := by rw [div_div_eq_mul_div]
  have h3 : (a + 2 * ε) * g / (4 * (a + 2)) ≤ g / 4 := by
    rw [div_le_iff₀ ha2]
    nlinarith [mul_nonneg hg.le (sub_nonneg.2 hε1)]
  have h4 : ε * (4 * (a + 2) / g) ≤ g / 4 := by
    have e4 : ε * (4 * (a + 2) / g) = 4 * (a + 2) * ε / g := by ring
    rw [e4, div_le_iff₀ hg]
    nlinarith
  have h5 : ε * Real.log (a / ε + 2) ≤ g / 2 := by
    have h := mul_le_mul_of_nonneg_left hlogy hε.le
    rw [mul_add, e1] at h
    linarith
  have e : ε * Real.logb 2 (a / ε + 2) = ε * Real.log (a / ε + 2) / Real.log 2 := by
    unfold Real.logb
    ring
  rw [e, div_le_iff₀ hLpos]
  nlinarith [mul_nonneg hg.le (sub_nonneg.2 hL)]

/-- **E3b2, explicit form.** For `0 < a`, `c < a`, `0 < ε ≤ 1` and `16 (a + 2) ε ≤ (a − c)²`:
`c ≤ −ε log₂ h₂(2^(−a/ε))`. -/
theorem scale_log_of_le {a c ε : ℝ} (ha : 0 < a) (hca : c < a) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεg : 16 * (a + 2) * ε ≤ (a - c) ^ 2) :
    c ≤ -(ε * Real.logb 2 (binaryEntropy (scaleParam a ε))) := by
  have hp0 := scaleParam_pos a ε
  have hh0 := slog_entropy_pos ha hε
  have hhU := slog_entropy_le ha hε
  have hy : 0 < a / ε + 2 := add_pos (div_pos ha hε) (by norm_num)
  have hlog : Real.logb 2 (binaryEntropy (scaleParam a ε)) ≤
      Real.logb 2 (scaleParam a ε * (a / ε + 2)) :=
    Real.logb_le_logb_of_le (by norm_num) hh0 hhU
  rw [Real.logb_mul hp0.ne' hy.ne', slog_logb_scaleParam] at hlog
  have hsm := slog_small ha (by linarith : 0 < a - c) hε hε1 hεg
  have hmul := mul_le_mul_of_nonneg_left hlog hε.le
  have hεa : ε * (a / ε) = a := by
    rw [mul_comm, div_mul_cancel₀ _ hε.ne']
  rw [mul_add, mul_neg, hεa] at hmul
  linarith

/-- **E3b2.** For `0 < a` and `c < a`, eventually as `ε ↓ 0`,
`c ≤ −ε log₂ h₂(2^(−a/ε))`. -/
theorem scale_log_eventually {a c : ℝ} (ha : 0 < a) (hca : c < a) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c ≤ -(ε * Real.logb 2 (binaryEntropy (scaleParam a ε))) := by
  have ha2 : (0 : ℝ) < 16 * (a + 2) := by linarith
  have hg : 0 < (a - c) ^ 2 / (16 * (a + 2)) := div_pos (pow_pos (by linarith) 2) ha2
  refine scale_eventually_of_lt (lt_min one_pos hg) ?_
  intro ε hε hεlt
  have h1 : ε < 1 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have h2 : ε < (a - c) ^ 2 / (16 * (a + 2)) := lt_of_lt_of_le hεlt (min_le_right _ _)
  have h3 : ε * (16 * (a + 2)) < (a - c) ^ 2 := (lt_div_iff₀ ha2).mp h2
  refine scale_log_of_le ha hca hε h1.le ?_
  linarith

end EntropyLean
