import Mathlib
import EntropyLean.MartonOneBit
import EntropyLean.MartonSmoothing

/-!
# Transport of the entropic Marton bound along linear equivalences (roadmap item I1)

Proved here, for finite F₂-spaces `V`, `V'`:
* `ruzsaDist_map_of_add_injective`, `entropyIncrement_map_of_add_injective`: an injective additive
  map preserves the Ruzsa distance and the entropy increment; `ruzsaDist_map_addEquiv` is the case
  of an additive equivalence `e : V ≃+ V'`;
* `subCard_map_linearEquiv`, `uniformSub_map_linearEquiv`: for a linear equivalence
  `e : V ≃ₗ[ZMod 2] V'`, `|e W| = |W|` and `(U_W).map e = U_{e W}`;
* `MartonInput.of_linearEquiv`: (35) on `V` gives (35) on `V'` (witness `e W`);
* `MartonInput.of_finrank_eq`: hence (35) on `V` gives (35) on every space of the same dimension;
* `entropyIncrement_map_add_const`: translating a law does not change `D` (roadmap item I2a);
* `uniformSub_map_subtype`: for a subspace `U` of `V` and a subspace `W` of `U`, pushing `U_W`
  forward along `U ↪ V` gives the uniform law on the image of `W` (roadmap item I2a).

What this file does NOT prove: the entropic Marton bound (35) itself in any dimension `≥ 2`, nor
the coset and two-point cases (roadmap items I2b, I3).
-/

namespace EntropyLean

section Transport

variable {V V' : Type*} [AddCommGroup V] [Fintype V] [AddCommGroup V'] [Fintype V']

/-- An injective additive map preserves the Ruzsa distance. -/
theorem ruzsaDist_map_of_add_injective (f : V → V') (hf : ∀ a b, f (a + b) = f a + f b)
    (hinj : Function.Injective f) (K L : PMF V) :
    ruzsaDist (K.map f) (L.map f) = ruzsaDist K L := by
  unfold ruzsaDist
  rw [← conv_map_of_add f hf K L, entropyBits_map_injective _ hinj,
    entropyBits_map_injective _ hinj, entropyBits_map_injective _ hinj]

/-- An injective additive map preserves the entropy increment. -/
theorem entropyIncrement_map_of_add_injective (f : V → V') (hf : ∀ a b, f (a + b) = f a + f b)
    (hinj : Function.Injective f) (K : PMF V) :
    entropyIncrement (K.map f) = entropyIncrement K := by
  unfold entropyIncrement
  rw [← conv_map_of_add f hf K K, entropyBits_map_injective _ hinj,
    entropyBits_map_injective _ hinj]

/-- The Ruzsa distance is invariant under an additive equivalence. -/
theorem ruzsaDist_map_addEquiv (e : V ≃+ V') (K L : PMF V) :
    ruzsaDist (K.map e) (L.map e) = ruzsaDist K L :=
  ruzsaDist_map_of_add_injective e (map_add e) e.injective K L

variable [Module (ZMod 2) V] [Module (ZMod 2) V']

/-- A linear equivalence preserves the number of points of a subspace. -/
theorem subCard_map_linearEquiv (e : V ≃ₗ[ZMod 2] V') (W : Submodule (ZMod 2) V) :
    subCard (W.map (e : V →ₗ[ZMod 2] V')) = subCard W := by
  rw [subCard_eq, subCard_eq]
  congr 1
  exact LinearEquiv.finrank_map_eq e W

/-- The image of the uniform law on `W` under a linear equivalence `e` is uniform on `e W`. -/
theorem uniformSub_map_linearEquiv (e : V ≃ₗ[ZMod 2] V') (W : Submodule (ZMod 2) V) :
    (uniformSub W).map e = uniformSub (W.map (e : V →ₗ[ZMod 2] V')) := by
  classical
  apply pmf_ext_toReal
  intro v'
  obtain ⟨v, rfl⟩ := e.surjective v'
  have hmem : e v ∈ W.map (e : V →ₗ[ZMod 2] V') ↔ v ∈ W := by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [pmf_map_apply_injective _ e.injective, uniformSub_toReal, uniformSub_toReal,
    subCard_map_linearEquiv]
  by_cases hv : v ∈ W
  · rw [if_pos hv, if_pos (hmem.mpr hv)]
  · rw [if_neg hv, if_neg (fun h => hv (hmem.mp h))]

/-- **I1.** The entropic Marton bound (35) transfers along a linear equivalence. -/
theorem MartonInput.of_linearEquiv (e : V ≃ₗ[ZMod 2] V') (hM : MartonInput V) :
    MartonInput V' := by
  refine ⟨fun K' => ?_⟩
  obtain ⟨W, hW⟩ := hM.marton (K'.map e.symm)
  refine ⟨W.map (e : V →ₗ[ZMod 2] V'), ?_⟩
  have hK : (K'.map e.symm).map e = K' := by
    rw [PMF.map_comp]
    have hc : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
    rw [hc, PMF.map_id]
  have hD : entropyIncrement (K'.map e.symm) = entropyIncrement K' :=
    entropyIncrement_map_of_add_injective e.symm (map_add e.symm) e.symm.injective K'
  calc ruzsaDist K' (uniformSub (W.map (e : V →ₗ[ZMod 2] V')))
      = ruzsaDist ((K'.map e.symm).map e) ((uniformSub W).map e) := by
        rw [hK, uniformSub_map_linearEquiv]
    _ = ruzsaDist (K'.map e.symm) (uniformSub W) :=
        ruzsaDist_map_of_add_injective e (map_add e) e.injective _ _
    _ ≤ 6 * entropyIncrement (K'.map e.symm) := hW
    _ = 6 * entropyIncrement K' := by rw [hD]

/-- (35) depends only on the dimension: it transfers between spaces of equal dimension. -/
theorem MartonInput.of_finrank_eq
    (h : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) V') (hM : MartonInput V) :
    MartonInput V' :=
  hM.of_linearEquiv (LinearEquiv.ofFinrankEq V V' h)

/-- Translating a law does not change its entropy increment: `D(K + c) = D(K)`. -/
theorem entropyIncrement_map_add_const (K : PMF V) (c : V) :
    entropyIncrement (K.map fun v => v + c) = entropyIncrement K := by
  rw [← ruzsaDist_self, ← ruzsaDist_self, ruzsaDist_map_add_const, ruzsaDist_comm,
    ruzsaDist_map_add_const]

/-- Pushing the uniform law on a subspace `W` of `U` forward along `U ↪ V` gives the uniform law
on the image of `W` in `V`. -/
theorem uniformSub_map_subtype (U : Submodule (ZMod 2) V) [Fintype U]
    (W : Submodule (ZMod 2) U) :
    (uniformSub W).map U.subtype = uniformSub (W.map U.subtype) := by
  classical
  have hcard : subCard (W.map U.subtype) = subCard W := by
    rw [subCard_eq, subCard_eq]
    congr 1
    first
      | exact (Submodule.equivMapOfInjective U.subtype U.injective_subtype W).finrank_eq.symm
      | exact Submodule.finrank_map_subtype_eq U W
  apply pmf_ext_toReal
  intro v
  by_cases hv : v ∈ U
  · have hmem : v ∈ W.map U.subtype ↔ (⟨v, hv⟩ : U) ∈ W := by
      constructor
      · rintro ⟨y, hy, hyv⟩
        have hy' : y = ⟨v, hv⟩ := Subtype.ext hyv
        rwa [← hy']
      · intro h
        exact ⟨⟨v, hv⟩, h, rfl⟩
    have hval : ((uniformSub W).map U.subtype) v = uniformSub W ⟨v, hv⟩ :=
      pmf_map_apply_injective (uniformSub W) U.injective_subtype ⟨v, hv⟩
    rw [hval, uniformSub_toReal, uniformSub_toReal, hcard]
    by_cases hw : (⟨v, hv⟩ : U) ∈ W
    · rw [if_pos hw, if_pos (hmem.mpr hw)]
    · rw [if_neg hw, if_neg (fun h => hw (hmem.mp h))]
  · have hval : ((uniformSub W).map U.subtype) v = 0 := by
      rw [PMF.map_apply]
      exact ENNReal.tsum_eq_zero.mpr fun a => if_neg (fun h => hv (by rw [h]; exact a.2))
    have hnot : v ∉ W.map U.subtype := by
      rintro ⟨y, _, hyv⟩
      exact hv (by rw [← hyv]; exact y.2)
    rw [hval, uniformSub_toReal, if_neg hnot, ENNReal.zero_toReal]

end Transport

end EntropyLean
