import Mathlib
import EntropyLean.MartonInput

/-!
# Entropy of the uniform law on a subspace (roadmap item D7b1, Section 7)

For a subspace `W` of a finite F₂-space `V`, the uniform law `U_W = uniformSub W` gives mass
`1 / |W|` to each point of `W` and `0` elsewhere, and `|W| = 2 ^ dim W`, so `H(U_W) = dim W`.

This file proves
* `tsum_subIndicator`, `subCard_pos`, `uniformSub_toReal`: the masses of `U_W`, with
  `subCard W` the number of points of `W`;
* `subCard_eq`: `|W| = 2 ^ dim W`;
* `entropyBits_uniformSub_card`, `entropyBits_uniformSub`: `H(U_W) = log₂ |W| = dim W`.

What this file does NOT prove: the smoothing identity `H(K * U_W) = H(q_W K) + dim W`, the formula
`d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2` and the lower bound `|dim W − H(K)| / 2 ≤ d(K, U_W)`
(roadmap items D7b2, D7c), nor the entropic Marton bound (35), which stays a hypothesis.
-/

namespace EntropyLean

open scoped ENNReal

section UniformSub

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

open Classical in
/-- The number of points of a subspace `W`. -/
noncomputable def subCard (W : Submodule (ZMod 2) V) : ℕ :=
  (Finset.univ.filter fun v : V => v ∈ W).card

theorem tsum_subIndicator (W : Submodule (ZMod 2) V) :
    ∑' v, subIndicator W v = (subCard W : ℝ≥0∞) := by
  rw [tsum_fintype]
  unfold subIndicator subCard
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem subCard_pos (W : Submodule (ZMod 2) V) : 0 < subCard W := by
  unfold subCard
  exact Finset.card_pos.mpr ⟨0, by simp⟩

open Classical in
/-- The masses of the uniform law: `U_W(v) = 1 / |W|` on `W` and `0` off `W`. -/
theorem uniformSub_toReal (W : Submodule (ZMod 2) V) (v : V) :
    (uniformSub W v).toReal = if v ∈ W then ((subCard W : ℕ) : ℝ)⁻¹ else 0 := by
  unfold uniformSub
  rw [PMF.normalize_apply, tsum_subIndicator]
  unfold subIndicator
  split_ifs
  · simp [ENNReal.toReal_inv]
  · simp

open Classical in
/-- `H(U_W) = log₂ |W|`. -/
theorem entropyBits_uniformSub_card (W : Submodule (ZMod 2) V) :
    entropyBits (uniformSub W) = Real.logb 2 (subCard W : ℝ) := by
  rw [entropyBits_eq_sum]
  have hN : (0 : ℝ) < (subCard W : ℝ) := by exact_mod_cast subCard_pos W
  have hterm : ∀ v, -(uniformSub W v).toReal * Real.logb 2 (uniformSub W v).toReal =
      if v ∈ W then (subCard W : ℝ)⁻¹ * Real.logb 2 (subCard W : ℝ) else 0 := by
    intro v
    rw [uniformSub_toReal]
    split_ifs
    · first
        | rw [Real.logb_inv]
        | simp only [Real.logb, Real.log_inv, neg_div]
      ring
    · simp
  rw [Finset.sum_congr rfl fun v _ => hterm v]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  change (subCard W : ℝ) * _ = _
  rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]

/-- `|W| = 2 ^ dim W`. -/
theorem subCard_eq (W : Submodule (ZMod 2) V) :
    subCard W = 2 ^ Module.finrank (ZMod 2) W := by
  classical
  have h1 : subCard W = Fintype.card W := by
    unfold subCard
    convert (Fintype.card_subtype (fun v : V => v ∈ W)).symm
  have h2 : Fintype.card W = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) W := by
    first
      | exact Module.card_eq_pow_finrank
      | exact card_eq_pow_finrank
      | exact FiniteDimensional.card_eq_pow_finrank
  rw [h1, h2, ZMod.card]

/-- `H(U_W) = dim W`. -/
theorem entropyBits_uniformSub (W : Submodule (ZMod 2) V) :
    entropyBits (uniformSub W) = (Module.finrank (ZMod 2) W : ℝ) := by
  rw [entropyBits_uniformSub_card, subCard_eq]
  push_cast
  unfold Real.logb
  rw [Real.log_pow]
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [mul_div_assoc, div_self h2, mul_one]

end UniformSub

end EntropyLean
