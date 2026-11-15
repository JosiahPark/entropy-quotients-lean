import Mathlib
import EntropyLean.RatioGrowth
import EntropyLean.SparsePosterior
import EntropyLean.FourSampleSplitting
import EntropyLean.RatioSparsification

/-!
# Lemma 8.1 (ratio growth) from the Marton bound (roadmap item D9, Section 8)

Proof of Lemma 8.1 of arXiv:2610.38525, following Section 8. Given a `λ`-sparse family `𝒫` with
`h(𝒫) > 0`, ratio `d = e/h > 0` and `d ≥ 40√λ`, Lemma 4.1 gives a quotient family `𝒫'` with
`H = h(𝒫') > 0`, ratio `δ ≥ d`, `𝒫'` `2λ`-sparse and `ℛ = 𝒫' * 𝒫'` `4λ`-sparse. The posterior family
`𝒬 = Post 𝒫'` is `2λ`-sparse (Lemma 2.2), `h(ℛ) = (2 − δ)H`, `h(𝒬) = δH` ((15), (17)),
`e(ℛ) + e(𝒬) = 2δH + J` (Lemma 6.1) and `e(𝒬) ≤ 36J + 14√(2λ) δH` (Lemma 7.1). The arithmetic of
the paper then shows that `ℛ` or `𝒬` has ratio at least `δ + δ²/148 ≥ d + d²/148`.

This file proves
* `ratio_growth_arith`: the real-number step (if neither `ℛ` nor `𝒬` reaches `δ + δ²/148`, then
  `δ³H < 0`);
* `ratio_growth_of_marton`: **Lemma 8.1** (`RatioGrowth.{0}`) from the entropic Marton bound (35)
  on all finite F₂-spaces in `Type` (`MartonBound.{0}`);
* `weighted_family_rigidity_of_marton`: Theorem 8.2 (`WeightedFamilyRigidity.{0}`) from the same
  hypothesis, via `weighted_family_rigidity_of_growth` (item D2).

What this file does NOT prove: the entropic Marton bound (35) itself, which enters only as the
hypothesis `hM : MartonBound.{0}`; hence NOT Theorem 8.2, 1.1 or 1.2 unconditionally. The results
are for spaces in `Type` (the posterior family is built for `V : Type`).
-/

namespace EntropyLean

open scoped BigOperators

/-- The arithmetic of Lemma 8.1. With `H > 0`, `δ > 0`, `1600 λ ≤ δ²`, `J ≥ 0`,
`e(ℛ) + e(𝒬) = 2δH + J` (Lemma 6.1) and `e(𝒬) ≤ 36J + 14√(2λ) δH` (Lemma 7.1), either
`e(ℛ) ≥ (δ + δ²/148)(2 − δ)H` or `e(𝒬) ≥ (δ + δ²/148) δH`. -/
theorem ratio_growth_arith {H δ eR eQ J lam : ℝ} (hH : 0 < H) (hδ0 : 0 < δ) (hlam : 0 ≤ lam)
    (hsmall : 1600 * lam ≤ δ ^ 2) (hJ : 0 ≤ J) (hsplit : eR + eQ = 2 * (δ * H) + J)
    (h7 : eQ ≤ 36 * J + 14 * Real.sqrt (2 * lam) * (δ * H)) :
    (δ + δ ^ 2 / 148) * ((2 - δ) * H) ≤ eR ∨ (δ + δ ^ 2 / 148) * (δ * H) ≤ eQ := by
  have hs0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg lam
  have hss : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam
  have h40 : 40 * Real.sqrt lam ≤ δ := by nlinarith [hss, hs0, hδ0, hsmall]
  have hsq2 : Real.sqrt (2 * lam) = Real.sqrt 2 * Real.sqrt lam := Real.sqrt_mul (by norm_num) lam
  have hr2 : Real.sqrt 2 ≤ 10 / 7 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hc : 14 * Real.sqrt (2 * lam) ≤ δ / 2 := by
    rw [hsq2]
    nlinarith [hr2, hs0, h40]
  have hδH : 0 ≤ δ * H := mul_nonneg hδ0.le hH.le
  have hA : 14 * Real.sqrt (2 * lam) * (δ * H) ≤ δ / 2 * (δ * H) :=
    mul_le_mul_of_nonneg_right hc hδH
  have hpos3 : 0 < δ * δ * δ * H := mul_pos (mul_pos (mul_pos hδ0 hδ0) hδ0) hH
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  first
    | linarith
    | nlinarith [h1, h2, hsplit, hJ, h7, hA, hpos3]

namespace WeightedFamily

/-- Sparsity is monotone in the parameter. -/
theorem isSparse_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {a b : ℝ}
    (P : WeightedFamily V) (h : P.IsSparse a) (hab : a ≤ b) : P.IsSparse b :=
  fun U => (h U).trans (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg _))

/-- **Lemma 8.1** (ratio growth), equation (39), for all finite F₂-spaces in `Type`, from the
entropic Marton bound (35) on those spaces. -/
theorem ratio_growth_of_marton (hM : MartonBound.{0}) : RatioGrowth.{0} := by
  unfold RatioGrowth
  intro W _ _ _ lam P hlam hsp hpos hd hsmall
  obtain ⟨G, hGpos, hratio, hsp2, hsp4⟩ := P.ratio_preserving_sparsification_proof lam hsp hpos
  haveI : Finite (W ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (W ⧸ G) := Fintype.ofFinite _
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = P.meanInteraction / P.meanEntropy := ⟨_, rfl⟩
  rw [← hd_def] at hd hsmall ⊢
  rw [← hd_def] at hratio
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = (P.quotient G).meanEntropy := ⟨_, rfl⟩
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ,
      δ = (P.quotient G).meanInteraction / (P.quotient G).meanEntropy := ⟨_, rfl⟩
  rw [← hδ_def] at hratio
  rw [← hH_def] at hGpos
  have hne : (P.quotient G).meanEntropy ≠ 0 := by
    rw [← hH_def]
    exact hGpos.ne'
  have heP : (P.quotient G).meanInteraction = δ * H := by
    rw [hδ_def, hH_def]
    field_simp
  have hδ0 : 0 < δ := lt_of_lt_of_le hd hratio
  have hle : (P.quotient G).meanInteraction ≤ (P.quotient G).meanEntropy :=
    (P.quotient G).meanInteraction_le
  rw [heP, ← hH_def] at hle
  have hδ1 : δ ≤ 1 := by nlinarith [hle, hGpos]
  have hR : (P.quotient G).convFamily.meanEntropy = (2 - δ) * H := by
    rw [WeightedFamily.meanEntropy_convFamily, heP, ← hH_def]
    ring
  have hQ : (P.quotient G).posterior.meanEntropy = δ * H := by
    rw [meanEntropy_posterior, heP]
  have hsplit := (P.quotient G).four_sample_splitting
  rw [heP] at hsplit
  have hJ := (P.quotient G).fourSampleJ_nonneg
  have h7 := (P.quotient G).sparse_posterior_estimate (hM (W ⧸ G))
    (posterior_closure (2 * lam) (P.quotient G) hsp2) (by linarith)
  rw [heP] at h7
  have hsmall' : 1600 * lam ≤ δ ^ 2 := by nlinarith [hsmall, hratio, hd]
  have hgrow : d + d ^ 2 / 148 ≤ δ + δ ^ 2 / 148 := by nlinarith [hratio, hd]
  have hRpos : 0 < (2 - δ) * H := by
    have h2δ : 0 < 2 - δ := by linarith
    exact mul_pos h2δ hGpos
  have hQpos : 0 < δ * H := mul_pos hδ0 hGpos
  rcases ratio_growth_arith hGpos hδ0 hlam.le hsmall' hJ hsplit h7 with hcase | hcase
  · refine ⟨{ carrier := W ⧸ G, fam := (P.quotient G).convFamily }, hsp4, ?_, ?_⟩
    · show 0 < (P.quotient G).convFamily.meanEntropy
      rw [hR]
      exact hRpos
    · show d + d ^ 2 / 148 ≤
        (P.quotient G).convFamily.meanInteraction / (P.quotient G).convFamily.meanEntropy
      rw [hR, le_div_iff₀ hRpos]
      calc (d + d ^ 2 / 148) * ((2 - δ) * H) ≤ (δ + δ ^ 2 / 148) * ((2 - δ) * H) :=
            mul_le_mul_of_nonneg_right hgrow hRpos.le
        _ ≤ _ := hcase
  · refine ⟨{ carrier := W ⧸ G, fam := (P.quotient G).posterior },
      (P.quotient G).posterior.isSparse_of_le (posterior_closure (2 * lam) (P.quotient G) hsp2)
        (by linarith), ?_, ?_⟩
    · show 0 < (P.quotient G).posterior.meanEntropy
      rw [hQ]
      exact hQpos
    · show d + d ^ 2 / 148 ≤
        (P.quotient G).posterior.meanInteraction / (P.quotient G).posterior.meanEntropy
      rw [hQ, le_div_iff₀ hQpos]
      calc (d + d ^ 2 / 148) * (δ * H) ≤ (δ + δ ^ 2 / 148) * (δ * H) :=
            mul_le_mul_of_nonneg_right hgrow hQpos.le
        _ ≤ _ := hcase

end WeightedFamily

/-- Theorem 8.2 (`WeightedFamilyRigidity.{0}`) from the entropic Marton bound (35) on all finite
F₂-spaces in `Type`, via Lemma 8.1 and `weighted_family_rigidity_of_growth`. -/
theorem weighted_family_rigidity_of_marton (hM : MartonBound.{0}) :
    WeightedFamilyRigidity.{0} :=
  weighted_family_rigidity_of_growth (WeightedFamily.ratio_growth_of_marton hM)

end EntropyLean
