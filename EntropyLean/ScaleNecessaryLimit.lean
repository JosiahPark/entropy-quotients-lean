import Mathlib
import EntropyLean.BernoulliExpansion
import EntropyLean.RigidityArith

/-!
# Proposition 9.3, analytic step: the gap at `p = 2^(−a/ε)` (roadmap item E3b1)

`scaleParam a ε = 2^(−a/ε)` is the Bernoulli parameter of the proof of Proposition 9.3. Proved
here, for `a > 0` and `ε > 0` (write `p = scaleParam a ε`):

* `scaleParam_pos`, `scaleParam_lt_one`, `log_scaleParam` (`log p = −(a/ε) log 2`) and
  `logb_inv_scaleParam` (`log₂(1/p) = a/ε`);
* `scaleParam_mul_le`: `p · a · log 2 ≤ ε` (from `1 + x ≤ eˣ`), so `p → 0` as `ε ↓ 0`;
* `scale_gap_of_le`: if `ε < (2 − a)/4` and `p ≤ (2 − a)/12`, then
  `ε h₂(p) < (1+ε) bernoulliDefect p` (from `binaryEntropy_le`, `bernoulliDefect_ge` and
  `1/2 ≤ log 2`);
* `scale_gap_eventually`: for `0 < a < 2`, eventually as `ε ↓ 0`,
  `ε h₂(2^(−a/ε)) < (1+ε) bernoulliDefect (2^(−a/ε))`.

Auxiliary: `scale_eventually_of_lt` (a property of every `ε ∈ (0, ε₀)` holds eventually in
`𝓝[>] 0`).

What this file does NOT prove: the logarithmic bound `c ≤ −ε log₂ h₂(2^(−a/ε))` for `c < a`
(roadmap item E3b2), and Proposition 9.3 itself (`exponential_scale_necessary`, item E3c).
-/

namespace EntropyLean

open Filter

/-- The Bernoulli parameter `p = 2^(−a/ε)` of the proof of Proposition 9.3. -/
noncomputable def scaleParam (a ε : ℝ) : ℝ := (2 : ℝ) ^ (-(a / ε))

theorem scaleParam_pos (a ε : ℝ) : 0 < scaleParam a ε := by
  unfold scaleParam
  positivity

theorem log_scaleParam (a ε : ℝ) : Real.log (scaleParam a ε) = -(a / ε) * Real.log 2 := by
  unfold scaleParam
  exact Real.log_rpow (by norm_num) _

theorem scaleParam_lt_one {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) : scaleParam a ε < 1 := by
  by_contra h
  push_neg at h
  have h1 := Real.log_nonneg h
  rw [log_scaleParam] at h1
  have h2 : 0 < a / ε * Real.log 2 := mul_pos (div_pos ha hε) (Real.log_pos (by norm_num))
  linarith

/-- `log₂(1/p) = a/ε` for `p = 2^(−a/ε)`. -/
theorem logb_inv_scaleParam (a ε : ℝ) : Real.logb 2 (1 / scaleParam a ε) = a / ε := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [Real.logb]
  first
    | rw [one_div, Real.log_inv, log_scaleParam, neg_mul, neg_neg, mul_div_assoc, div_self hl,
        mul_one]
    | (rw [one_div, Real.log_inv, log_scaleParam]; field_simp)

/-- `2^(−a/ε) · a · log 2 ≤ ε`, from `1 + x ≤ eˣ` at `x = (a/ε) log 2`. -/
theorem scaleParam_mul_le {a ε : ℝ} (hε : 0 < ε) : scaleParam a ε * a * Real.log 2 ≤ ε := by
  have hε' : ε ≠ 0 := hε.ne'
  have hp := scaleParam_pos a ε
  have hexp := Real.add_one_le_exp (-Real.log (scaleParam a ε))
  rw [Real.exp_neg, Real.exp_log hp, log_scaleParam] at hexp
  have h1 := mul_le_mul_of_nonneg_left hexp hp.le
  rw [mul_inv_cancel₀ hp.ne'] at h1
  have h2 : scaleParam a ε * (a / ε * Real.log 2) ≤ 1 := by linarith
  have hq : a / ε * ε = a := by
    first
      | exact div_mul_cancel₀ a hε'
      | field_simp
  have h3 := mul_le_mul_of_nonneg_right h2 hε.le
  have e : scaleParam a ε * (a / ε * Real.log 2) * ε = scaleParam a ε * a * Real.log 2 := by
    rw [show scaleParam a ε * (a / ε * Real.log 2) * ε =
      scaleParam a ε * (a / ε * ε) * Real.log 2 by ring, hq]
  linarith

/-- A property of every `ε ∈ (0, ε₀)` holds eventually as `ε ↓ 0`. -/
theorem scale_eventually_of_lt {P : ℝ → Prop} {ε₀ : ℝ} (h0 : 0 < ε₀)
    (h : ∀ ε, 0 < ε → ε < ε₀ → P ε) : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), P ε := by
  have h1 : Set.Iio ε₀ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    first
      | exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h0)
      | exact nhdsWithin_le_nhds (Iio_mem_nhds h0)
  filter_upwards [h1, self_mem_nhdsWithin] with ε hε1 hε2
  exact h ε (Set.mem_Ioi.mp hε2) (Set.mem_Iio.mp hε1)

/-- **E3b1, explicit form.** If `0 < ε < (2 − a)/4` and `p = 2^(−a/ε) ≤ (2 − a)/12`, then
`ε h₂(p) < (1+ε) bernoulliDefect p`. -/
theorem scale_gap_of_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hεa : ε < (2 - a) / 4)
    (hpa : scaleParam a ε ≤ (2 - a) / 12) :
    ε * binaryEntropy (scaleParam a ε) < (1 + ε) * bernoulliDefect (scaleParam a ε) := by
  have hε' : ε ≠ 0 := hε.ne'
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := half_le_log_two
  have hp0 := scaleParam_pos a ε
  have hp1 := scaleParam_lt_one ha hε
  have hup := binaryEntropy_le hp0 hp1
  have hlo := bernoulliDefect_ge hp0 hp1
  rw [logb_inv_scaleParam] at hup
  have hq : a / ε * ε = a := by
    first
      | exact div_mul_cancel₀ a hε'
      | field_simp
  set p := scaleParam a ε
  have hpL : p / Real.log 2 ≤ 2 * p := by
    rw [div_le_iff₀ hl]
    linarith [mul_le_mul_of_nonneg_left hL hp0.le]
  have hp2L : 2 * p ^ 2 / Real.log 2 ≤ 4 * p ^ 2 := by
    rw [div_le_iff₀ hl]
    linarith [mul_le_mul_of_nonneg_left hL (sq_nonneg p)]
  have h3 := mul_le_mul_of_nonneg_left hup hε.le
  have e3 : ε * (p * (a / ε) + p / Real.log 2) = p * (a / ε * ε) + ε * (p / Real.log 2) := by
    ring
  rw [e3, hq] at h3
  have h4 : ε * (p / Real.log 2) ≤ ε * (2 * p) := mul_le_mul_of_nonneg_left hpL hε.le
  have hp6 : p ≤ 1 / 6 := by linarith
  have hpp := mul_le_mul_of_nonneg_left hp6 hp0.le
  have hD : 0 ≤ bernoulliDefect p := by linarith
  have h5 : 0 ≤ ε * bernoulliDefect p := mul_nonneg hε.le hD
  have hpos : 0 < 2 - a - 2 * ε - 6 * p := by linarith
  have h6 := mul_pos hp0 hpos
  linarith

/-- **E3b1.** For `0 < a < 2`, eventually as `ε ↓ 0`, the parameter `p = 2^(−a/ε)` satisfies
`ε h₂(p) < (1+ε) bernoulliDefect p`, the gap hypothesis of `one_le_C_mul_binaryEntropy`. -/
theorem scale_gap_eventually {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε * binaryEntropy (scaleParam a ε) < (1 + ε) * bernoulliDefect (scaleParam a ε) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < 2 - a := by linarith
  have hk : 0 < (2 - a) * a * Real.log 2 / 12 :=
    div_pos (mul_pos (mul_pos hδ ha) hl) (by norm_num)
  refine scale_eventually_of_lt (lt_min (div_pos hδ (by norm_num : (0 : ℝ) < 4)) hk) ?_
  intro ε hε hεlt
  have h1 : ε < (2 - a) / 4 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have h2 : ε < (2 - a) * a * Real.log 2 / 12 := lt_of_lt_of_le hεlt (min_le_right _ _)
  refine scale_gap_of_le ha hε h1 ?_
  have h3 := scaleParam_mul_le (a := a) hε
  by_contra hcon
  push_neg at hcon
  have h4 := mul_lt_mul_of_pos_right hcon (mul_pos ha hl)
  linarith

end EntropyLean
