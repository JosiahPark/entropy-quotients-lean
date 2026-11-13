import Mathlib
import EntropyLean.Families
import EntropyLean.EntropyFacts

/-!
# Iterated quotients (roadmap item A5)

Quotienting a weighted family by `G` and then by `W ≤ V ⧸ G` gives the same mean entropy as
quotienting once by the inverse image `W.comap G.mkQ` (`WeightedFamily.quotient_quotient`), and
the averaged defects satisfy `F_{q_G 𝒫}(W) = F_𝒫(W.comap G.mkQ) - F_𝒫(G)`
(`WeightedFamily.averagedLoss_quotient`); both are used in Lemma 9.1.

The proof works for laws on arbitrary types (no `Fintype` instance on the quotients is needed):
entropy, written as a `tsum`, is invariant under an injective map
(`entropyBits_map_of_injective`), and two maps out of the same space with the same fibres, one
of them surjective, give laws of equal entropy (`entropyBits_map_eq_of_fibres`).

What this file does NOT prove: no inequality between entropies of quotients (data processing
for `D`, Lemma 2.1 supermodularity), and no statement at the level of `PMF` equality of the
iterated and single quotient laws (they live on different types; only their entropies agree).
-/

namespace EntropyLean

open scoped BigOperators

/-- For injective `f`, `PMF.map f P` gives `f a` the mass of `a`. -/
theorem pmf_map_apply_injective {α β : Type*} (P : PMF α) {f : α → β}
    (hf : Function.Injective f) (a : α) : (P.map f) (f a) = P a := by
  rw [PMF.map_apply]
  rw [tsum_eq_single a]
  · exact if_pos rfl
  · intro a' ha'
    first
    | exact if_neg fun h => ha' (hf h).symm
    | exact if_neg fun h => ha' (hf h)

/-- `PMF.map f P` gives no mass outside the range of `f`. -/
theorem pmf_map_apply_of_not_mem_range {α β : Type*} (P : PMF α) (f : α → β) {b : β}
    (hb : b ∉ Set.range f) : (P.map f) b = 0 := by
  rw [PMF.map_apply]
  refine ENNReal.tsum_eq_zero.mpr fun a' => ?_
  first
  | exact if_neg fun h => hb ⟨a', h.symm⟩
  | exact if_neg fun h => hb ⟨a', h⟩

/-- An injective map preserves entropy, for laws on arbitrary types. -/
theorem entropyBits_map_of_injective {α β : Type*} (P : PMF α) {f : α → β}
    (hf : Function.Injective f) : entropyBits (P.map f) = entropyBits P := by
  unfold entropyBits
  have hsupp : Function.support
      (fun b => -((P.map f) b).toReal * Real.logb 2 ((P.map f) b).toReal) ⊆ Set.range f := by
    intro b hb
    by_contra hr
    rw [Function.mem_support] at hb
    apply hb
    simp [pmf_map_apply_of_not_mem_range P f hr]
  calc ∑' b, -((P.map f) b).toReal * Real.logb 2 ((P.map f) b).toReal
      = ∑' a, -((P.map f) (f a)).toReal * Real.logb 2 ((P.map f) (f a)).toReal :=
        (hf.tsum_eq hsupp).symm
    _ = ∑' a, -(P a).toReal * Real.logb 2 (P a).toReal := by
        simp only [pmf_map_apply_injective P hf]

/-- Two maps with the same fibres, the first surjective, give laws of equal entropy. -/
theorem entropyBits_map_eq_of_fibres {α β γ : Type*} (P : PMF α) {f : α → β} {g : α → γ}
    (hf : Function.Surjective f) (hfg : ∀ a a', f a = f a' ↔ g a = g a') :
    entropyBits (P.map g) = entropyBits (P.map f) := by
  have hcomp : (fun b => g (Function.surjInv hf b)) ∘ f = g := by
    funext a
    exact (hfg _ _).mp (Function.surjInv_eq hf (f a))
  have hinj : Function.Injective (fun b => g (Function.surjInv hf b)) := by
    intro b b' h
    rw [← Function.surjInv_eq hf b, ← Function.surjInv_eq hf b']
    exact (hfg _ _).mpr h
  rw [← hcomp, ← PMF.map_comp]
  exact entropyBits_map_of_injective _ hinj

section Quotients

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The iterated quotient map `v ↦ q_W (q_G v)` is surjective. -/
theorem mkQ_mkQ_surjective (G : Submodule (ZMod 2) V) (W : Submodule (ZMod 2) (V ⧸ G)) :
    Function.Surjective fun v => W.mkQ (G.mkQ v) := by
  intro x
  obtain ⟨y, rfl⟩ := W.mkQ_surjective x
  obtain ⟨v, rfl⟩ := G.mkQ_surjective y
  exact ⟨v, rfl⟩

/-- The iterated quotient map and `q_{W.comap G.mkQ}` have the same fibres. -/
theorem mkQ_mkQ_fibres (G : Submodule (ZMod 2) V) (W : Submodule (ZMod 2) (V ⧸ G)) (a a' : V) :
    W.mkQ (G.mkQ a) = W.mkQ (G.mkQ a') ↔
      (W.comap G.mkQ).mkQ a = (W.comap G.mkQ).mkQ a' := by
  first
  | (simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      ← Submodule.Quotient.mk_sub]; done)
  | (simp only [Submodule.mkQ_apply]
     rw [Submodule.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_comap,
       Submodule.mkQ_apply, Submodule.Quotient.mk_sub])
  | (simp [Submodule.Quotient.eq]; done)

/-- Entropy of a law after quotienting by `G` and then by `W` equals its entropy after
quotienting once by `W.comap G.mkQ`. -/
theorem entropyBits_map_mkQ_mkQ (P : PMF V) (G : Submodule (ZMod 2) V)
    (W : Submodule (ZMod 2) (V ⧸ G)) :
    entropyBits ((P.map fun v => G.mkQ v).map fun u => W.mkQ u) =
      entropyBits (P.map fun v => (W.comap G.mkQ).mkQ v) := by
  rw [PMF.map_comp]
  exact (entropyBits_map_eq_of_fibres P (mkQ_mkQ_surjective G W)
    (fun a a' => mkQ_mkQ_fibres G W a a')).symm

end Quotients

namespace WeightedFamily

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `h(q_W (q_G 𝒫)) = h(q_{W.comap G.mkQ} 𝒫)`: quotienting by `G` and then by `W ≤ V ⧸ G`
has the same mean entropy as quotienting by the inverse image of `W`. -/
theorem quotient_quotient (P : WeightedFamily V) (G : Submodule (ZMod 2) V)
    (W : Submodule (ZMod 2) (V ⧸ G)) :
    ((P.quotient G).quotient W).meanEntropy = (P.quotient (W.comap G.mkQ)).meanEntropy := by
  show ∑ i : P.index, P.weights i *
        entropyBits (((P.laws i).map fun v => G.mkQ v).map fun u => W.mkQ u) =
      ∑ i : P.index, P.weights i * entropyBits ((P.laws i).map fun v => (W.comap G.mkQ).mkQ v)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [entropyBits_map_mkQ_mkQ]

/-- `F_{q_G 𝒫}(W) = F_𝒫(W.comap G.mkQ) - F_𝒫(G)`. -/
theorem averagedLoss_quotient (P : WeightedFamily V) (G : Submodule (ZMod 2) V)
    (W : Submodule (ZMod 2) (V ⧸ G)) :
    (P.quotient G).averagedLoss W = P.averagedLoss (W.comap G.mkQ) - P.averagedLoss G := by
  have h1 := (P.quotient G).meanEntropy_quotient W
  have h2 := P.meanEntropy_quotient (W.comap G.mkQ)
  have h3 := P.meanEntropy_quotient G
  have h4 := P.quotient_quotient G W
  linarith

end WeightedFamily
end EntropyLean
