import Mathlib
import EntropyLean.QuotientFacts
import EntropyLean.RatioGrowthProof

/-!
# Universe transport of Lemma 8.1 (roadmap item D10)

`WeightedFamily.ratio_growth_of_marton` (item D9) proves Lemma 8.1 only as `RatioGrowth.{0}`,
because the posterior family is built for spaces in `Type`. This file lifts it to every universe.

* Single laws: entropy, interaction and the subspace defect are invariant under a linear
  equivalence `e : V ≃ₗ[ZMod 2] V'` between spaces in possibly different universes
  (`entropyBits_map_linearEquiv`, `interaction_map_linearEquiv`, and
  `quotientLoss_map_linearEquiv : F_{e P}(U) = F_P(e⁻¹ U)`), and `dim e⁻¹ U = dim U`
  (`finrank_comap_linearEquiv`).
* Families: the pushed-forward family `WeightedFamily.mapLinearEquiv` has the same `h` and `e`,
  `F_{e 𝒫}(U) = F_𝒫(e⁻¹ U)`, and is `λ`-sparse when `𝒫` is.
* `ratioGrowth_lift : RatioGrowth.{0} → RatioGrowth.{u}`: move `W` to `Fin (dim W) → ZMod 2` by
  a basis, apply `RatioGrowth.{0}`, and carry the output family back to universe `u` along
  `ULift`.
* Corollaries with the entropic Marton bound (35) on spaces in `Type` (`MartonBound.{0}`) as the
  only hypothesis, in every universe: Lemma 8.1 (`ratio_growth_of_marton_univ`), Theorem 8.2
  (`weighted_family_rigidity_of_marton_univ`), and the statements of Theorems 1.1 and 1.2
  (`exponential_entropy_quotient_of_marton`, `sparse_rigidity_of_marton`).

What this file does NOT prove: the entropic Marton bound (35), which stays the hypothesis
`hM : MartonBound.{0}`; hence NOT Theorem 8.2, 1.1 or 1.2 unconditionally (the open statements
in `EntropyLean/Statements.lean` are untouched).
-/

universe u v

namespace EntropyLean

open scoped BigOperators

section Transport

variable {V : Type u} {V' : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V'] [Module (ZMod 2) V']

/-- Entropy is invariant under a linear equivalence. -/
theorem entropyBits_map_linearEquiv (e : V ≃ₗ[ZMod 2] V') (P : PMF V) :
    entropyBits (P.map e) = entropyBits P :=
  entropyBits_map_of_injective P e.injective

/-- Interaction is invariant under a linear equivalence. -/
theorem interaction_map_linearEquiv (e : V ≃ₗ[ZMod 2] V') (P Q : PMF V) :
    interaction (P.map e) (Q.map e) = interaction P Q := by
  unfold interaction
  rw [← conv_map_of_add e (map_add e) P Q, entropyBits_map_linearEquiv,
    entropyBits_map_linearEquiv, entropyBits_map_linearEquiv]

/-- The inverse image of a subspace under a linear equivalence has the same dimension. -/
theorem finrank_comap_linearEquiv (e : V ≃ₗ[ZMod 2] V') (U : Submodule (ZMod 2) V') :
    Module.finrank (ZMod 2) (U.comap (e : V →ₗ[ZMod 2] V')) = Module.finrank (ZMod 2) U :=
  (e.ofSubmodule' U).finrank_eq

/-- The subspace defect is invariant under a linear equivalence: `F_{e P}(U) = F_P(e⁻¹ U)`. -/
theorem quotientLoss_map_linearEquiv (e : V ≃ₗ[ZMod 2] V') (P : PMF V)
    (U : Submodule (ZMod 2) V') :
    quotientLoss (P.map e) U = quotientLoss P (U.comap (e : V →ₗ[ZMod 2] V')) := by
  unfold quotientLoss
  rw [entropyBits_map_linearEquiv, PMF.map_comp]
  congr 1
  refine entropyBits_map_eq_of_fibres P (Submodule.mkQ_surjective _) fun a a' => ?_
  show (U.comap (e : V →ₗ[ZMod 2] V')).mkQ a = (U.comap (e : V →ₗ[ZMod 2] V')).mkQ a' ↔
    U.mkQ (e a) = U.mkQ (e a')
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap, ← map_sub]
  exact Iff.rfl

end Transport

namespace WeightedFamily

variable {V : Type u} {V' : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup V'] [Module (ZMod 2) V']

/-- The family pushed forward along a linear equivalence (same index type and weights). -/
noncomputable def mapLinearEquiv (P : WeightedFamily V) (e : V ≃ₗ[ZMod 2] V') :
    WeightedFamily V' where
  index := P.index
  laws := fun i => (P.laws i).map e
  weights := P.weights
  weights_pos := P.weights_pos
  weights_sum := P.weights_sum

/-- `h(e 𝒫) = h(𝒫)`. -/
theorem meanEntropy_mapLinearEquiv (P : WeightedFamily V) (e : V ≃ₗ[ZMod 2] V') :
    (P.mapLinearEquiv e).meanEntropy = P.meanEntropy := by
  show ∑ i, P.weights i * entropyBits ((P.laws i).map e) =
    ∑ i, P.weights i * entropyBits (P.laws i)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [entropyBits_map_linearEquiv]

/-- `e(e 𝒫) = e(𝒫)`. -/
theorem meanInteraction_mapLinearEquiv (P : WeightedFamily V) (e : V ≃ₗ[ZMod 2] V') :
    (P.mapLinearEquiv e).meanInteraction = P.meanInteraction := by
  show ∑ i, ∑ j, P.weights i * P.weights j *
      interaction ((P.laws i).map e) ((P.laws j).map e) =
    ∑ i, ∑ j, P.weights i * P.weights j * interaction (P.laws i) (P.laws j)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [interaction_map_linearEquiv]

/-- `F_{e 𝒫}(U) = F_𝒫(e⁻¹ U)`. -/
theorem averagedLoss_mapLinearEquiv (P : WeightedFamily V) (e : V ≃ₗ[ZMod 2] V')
    (U : Submodule (ZMod 2) V') :
    (P.mapLinearEquiv e).averagedLoss U = P.averagedLoss (U.comap (e : V →ₗ[ZMod 2] V')) := by
  show ∑ i, P.weights i * quotientLoss ((P.laws i).map e) U =
    ∑ i, P.weights i * quotientLoss (P.laws i) (U.comap (e : V →ₗ[ZMod 2] V'))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [quotientLoss_map_linearEquiv]

/-- A `λ`-sparse family stays `λ`-sparse after a linear equivalence. -/
theorem isSparse_mapLinearEquiv {lam : ℝ} (P : WeightedFamily V) (e : V ≃ₗ[ZMod 2] V')
    (h : P.IsSparse lam) : (P.mapLinearEquiv e).IsSparse lam := by
  intro U
  rw [averagedLoss_mapLinearEquiv, ← finrank_comap_linearEquiv e U]
  exact h _

end WeightedFamily

/-- **Universe transport of Lemma 8.1** (item D10): `RatioGrowth` for all finite F₂-spaces in
`Type` implies it for all finite F₂-spaces in universe `u`. -/
theorem ratioGrowth_lift (h0 : RatioGrowth.{0}) : RatioGrowth.{u} := by
  unfold RatioGrowth
  intro W _ _ _ lam P hlam hsp hpos hd hsmall
  have hne : Nonempty (W ≃ₗ[ZMod 2] F2Vec (Module.finrank (ZMod 2) W)) := by
    first
      | exact ⟨(Module.finBasis (ZMod 2) W).equivFun⟩
      | exact ⟨LinearEquiv.ofFinrankEq _ _ (by simp)⟩
  obtain ⟨e⟩ := hne
  obtain ⟨F, hFsp, hFpos, hFr⟩ := h0 (F2Vec (Module.finrank (ZMod 2) W)) lam
    (P.mapLinearEquiv e) hlam (P.isSparse_mapLinearEquiv e hsp)
    (by rw [P.meanEntropy_mapLinearEquiv e]; exact hpos)
    (by rw [P.meanInteraction_mapLinearEquiv e, P.meanEntropy_mapLinearEquiv e]; exact hd)
    (by rw [P.meanInteraction_mapLinearEquiv e, P.meanEntropy_mapLinearEquiv e]; exact hsmall)
  rw [P.meanInteraction_mapLinearEquiv e, P.meanEntropy_mapLinearEquiv e] at hFr
  have hne' : Nonempty (F.carrier ≃ₗ[ZMod 2] ULift.{u} F.carrier) := by
    first
      | exact ⟨ULift.moduleEquiv.symm⟩
      | exact ⟨{ toFun := ULift.up, invFun := ULift.down, map_add' := fun _ _ => rfl,
                 map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl,
                 right_inv := fun _ => rfl }⟩
  obtain ⟨E⟩ := hne'
  refine ⟨{ carrier := ULift.{u} F.carrier, fam := F.fam.mapLinearEquiv E }, ?_, ?_, ?_⟩
  · exact F.fam.isSparse_mapLinearEquiv E hFsp
  · show 0 < (F.fam.mapLinearEquiv E).meanEntropy
    rw [F.fam.meanEntropy_mapLinearEquiv E]
    exact hFpos
  · show _ ≤ (F.fam.mapLinearEquiv E).meanInteraction / (F.fam.mapLinearEquiv E).meanEntropy
    rw [F.fam.meanInteraction_mapLinearEquiv E, F.fam.meanEntropy_mapLinearEquiv E]
    exact hFr

/-- **Lemma 8.1** in every universe, from the entropic Marton bound (35) on spaces in `Type`. -/
theorem ratio_growth_of_marton_univ (hM : MartonBound.{0}) : RatioGrowth.{u} :=
  ratioGrowth_lift (WeightedFamily.ratio_growth_of_marton hM)

/-- **Theorem 8.2** in every universe, from the entropic Marton bound (35) on spaces in `Type`. -/
theorem weighted_family_rigidity_of_marton_univ (hM : MartonBound.{0}) :
    WeightedFamilyRigidity.{u} :=
  weighted_family_rigidity_of_growth (ratio_growth_of_marton_univ hM)

/-- The statement of **Theorem 1.1** (`exponential_entropy_quotient`) with the entropic Marton
bound (35) on spaces in `Type` as the only hypothesis. -/
theorem exponential_entropy_quotient_of_marton {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hM : MartonBound.{0}) (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (320 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_growth (ratio_growth_of_marton_univ hM) ε hε X

/-- The statement of **Theorem 1.2** (`sparse_rigidity`) with the entropic Marton bound (35) on
spaces in `Type` as the only hypothesis. -/
theorem sparse_rigidity_of_marton {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (hM : MartonBound.{0}) (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (Z : PMF V)
    (hsparse : IsSparse lam Z) (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (320 / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_of_growth (ratio_growth_of_marton_univ hM) lam hlam Z hsparse hpos

end EntropyLean
