import Mathlib
import EntropyLean.QuotientFacts

/-!
# Variational sparsification (Lemma 9.1, roadmap item C1)

For `λ > 0` and a finite weighted family `𝒫` on a finite `F₂`-space `V`, a subspace `G`
minimizing the objective `Φ(G) = h(q_G 𝒫) + λ dim G` (`WeightedFamily.variationalObjective`)
satisfies `dim G ≤ h(𝒫)/λ` and `q_G 𝒫` is `λ`-sparse
(`WeightedFamily.variational_sparsification_proof`, equation (44)). Comparing with `G = 0`
gives the dimension bound; comparing with the inverse image `W.comap G.mkQ` of a subspace
`W ≤ V ⧸ G`, using `F_{q_G 𝒫}(W) = F_𝒫(W.comap G.mkQ) - F_𝒫(G)` (item A5) and
`dim (W.comap G.mkQ) = dim G + dim W` (`finrank_comap_mkQ`), gives sparsity.

Auxiliary results: `quotientLoss_bot`, `WeightedFamily.averagedLoss_bot`,
`WeightedFamily.meanEntropy_nonneg`.

What this file does NOT prove: nothing about Theorem 1.1, Theorem 1.2 or Theorem 8.2; the
minimizer is only shown to exist (by finiteness of the set of subspaces), not computed.
-/

namespace EntropyLean

open scoped BigOperators

section Bot

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Quotienting by the zero subspace loses no entropy: `F_P(0) = 0`. -/
theorem quotientLoss_bot (Q : PMF V) : quotientLoss Q ⊥ = 0 := by
  have hinj : Function.Injective fun v : V => (⊥ : Submodule (ZMod 2) V).mkQ v := by
    intro a b h
    have h' : (⊥ : Submodule (ZMod 2) V).mkQ (a - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ, Submodule.mem_bot] at h'
    exact sub_eq_zero.mp h'
  unfold quotientLoss
  rw [entropyBits_map_of_injective Q hinj, sub_self]

/-- `dim (W.comap G.mkQ) = dim G + dim W` for `W ≤ V ⧸ G`. -/
theorem finrank_comap_mkQ [Fintype V] (G : Submodule (ZMod 2) V)
    (W : Submodule (ZMod 2) (V ⧸ G)) :
    Module.finrank (ZMod 2) (W.comap G.mkQ) =
      Module.finrank (ZMod 2) G + Module.finrank (ZMod 2) W := by
  have hle : G ≤ W.comap G.mkQ := by
    intro x hx
    have h0 : G.mkQ x = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hx
    rw [Submodule.mem_comap, h0]
    exact W.zero_mem
  have hmap : (W.comap G.mkQ).map G.mkQ = W :=
    Submodule.map_comap_eq_of_surjective G.mkQ_surjective W
  have e := ((Submodule.quotEquivOfEq _ _ hmap).symm.trans
    (Submodule.quotientQuotientEquivQuotient G (W.comap G.mkQ) hle)).finrank_eq
  have h1 := Submodule.finrank_quotient_add_finrank G
  have h2 := Submodule.finrank_quotient_add_finrank W
  have h3 := Submodule.finrank_quotient_add_finrank (W.comap G.mkQ)
  omega

end Bot

namespace WeightedFamily

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `h(𝒫) ≥ 0`. -/
theorem meanEntropy_nonneg (P : WeightedFamily V) : 0 ≤ P.meanEntropy := by
  unfold meanEntropy
  exact Finset.sum_nonneg fun i _ => mul_nonneg (P.weights_pos i).le (entropyBits_nonneg' _)

/-- `F_𝒫(0) = 0`. -/
theorem averagedLoss_bot (P : WeightedFamily V) : P.averagedLoss ⊥ = 0 := by
  unfold averagedLoss
  simp only [quotientLoss_bot, mul_zero, Finset.sum_const_zero]

/-- The objective `Φ(G) = h(q_G 𝒫) + λ dim G` of Lemma 9.1. -/
noncomputable def variationalObjective (P : WeightedFamily V) (lam : ℝ)
    (G : Submodule (ZMod 2) V) : ℝ :=
  (P.quotient G).meanEntropy + lam * (Module.finrank (ZMod 2) G : ℝ)

/-- `Φ(0) = h(𝒫)`. -/
theorem variationalObjective_bot (P : WeightedFamily V) (lam : ℝ) :
    P.variationalObjective lam ⊥ = P.meanEntropy := by
  unfold variationalObjective
  rw [meanEntropy_quotient, averagedLoss_bot]
  simp

/-- **Lemma 9.1** (variational sparsification), equation (44): a minimizer `G` of
`h(q_G 𝒫) + λ dim G` has `dim G ≤ h(𝒫)/λ`, and `q_G 𝒫` is `λ`-sparse. -/
theorem variational_sparsification_proof [Fintype V] (lam : ℝ) (hlam : 0 < lam)
    (P : WeightedFamily V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ P.meanEntropy / lam ∧
      (P.quotient G).IsSparse lam := by
  haveI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun G : Submodule (ZMod 2) V => (G : Set V))
      (fun _ _ h => SetLike.ext' h)
  obtain ⟨G, hG⟩ := Finite.exists_min (P.variationalObjective lam)
  refine ⟨G, ?_, ?_⟩
  · have h0 := hG ⊥
    rw [variationalObjective_bot] at h0
    unfold variationalObjective at h0
    have hnn := (P.quotient G).meanEntropy_nonneg
    rw [le_div_iff₀ hlam]
    nlinarith
  · unfold WeightedFamily.IsSparse
    intro W
    have h1 := hG (W.comap G.mkQ)
    unfold variationalObjective at h1
    rw [meanEntropy_quotient, meanEntropy_quotient, finrank_comap_mkQ G W] at h1
    rw [averagedLoss_quotient]
    push_cast at h1
    linarith

end WeightedFamily
end EntropyLean
