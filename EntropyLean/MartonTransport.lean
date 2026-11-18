import EntropyLean.MathlibForPFR
import EntropyLean.MartonOneBit
import EntropyLean.MartonSmoothing
import EntropyLean.MartonFinrankLeOne

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
  forward along `U ↪ V` gives the uniform law on the image of `W` (roadmap item I2a);
* `pmf_map_congr_support`, `cosetRetract`, `restrictLaw`, `restrictLaw_map_subtype_add`: a law `K`
  carried by a coset `x + U` is the image of a law on `U` (`restrictLaw U K x`) under `U ↪ V`
  followed by translation by `x` (roadmap item I2b);
* `marton_of_support_subset_coset`: (35) on `U` gives (35) for every law carried by a coset of `U`
  (roadmap item I2b);
* `marton_of_card_lawSupport_le_two`: (35) for every law with at most two points in its support,
  on every finite F₂-space (roadmap item I3; the support lies in a coset of a subspace of dimension
  at most one, where (35) holds by `martonInput_of_finrank_le_one`).

What this file does NOT prove: the entropic Marton bound (35) itself in any dimension `≥ 2`, only
the special cases above; nor the product cases (roadmap items I4, I5).
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

omit [Fintype V] [Module (ZMod 2) V] in
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
    rw [hval, uniformSub_toReal, if_neg hnot]
    simp

end Transport

section Coset

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Two maps that agree on the support of a law push it forward to the same law. -/
theorem pmf_map_congr_support {α β : Type*} (K : PMF α) {g g' : α → β}
    (h : ∀ a, K a ≠ 0 → g a = g' a) : K.map g = K.map g' := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : K a = 0
  · simp [ha]
  · rw [h a ha]

open Classical in
/-- The retraction `v ↦ v − x` of the coset `x + U` onto `U` (everything else goes to `0`). -/
noncomputable def cosetRetract (U : Submodule (ZMod 2) V) (x v : V) : U :=
  if h : v - x ∈ U then ⟨v - x, h⟩ else 0

theorem subtype_cosetRetract (U : Submodule (ZMod 2) V) (x : V) {v : V} (hv : v - x ∈ U) :
    U.subtype (cosetRetract U x v) = v - x := by
  first
    | simp [cosetRetract, hv]
    | (unfold cosetRetract; rw [dif_pos hv]; rfl)

/-- The law on `U` of `K − x`, for a law `K` carried by the coset `x + U`. -/
noncomputable def restrictLaw (U : Submodule (ZMod 2) V) (K : PMF V) (x : V) : PMF U :=
  K.map (cosetRetract U x)

theorem restrictLaw_map_subtype (U : Submodule (ZMod 2) V) (K : PMF V) (x : V)
    (hK : ∀ v, K v ≠ 0 → v - x ∈ U) :
    (restrictLaw U K x).map U.subtype = K.map fun v => v - x := by
  unfold restrictLaw
  rw [PMF.map_comp]
  exact pmf_map_congr_support K fun v hv => subtype_cosetRetract U x (hK v hv)

/-- A law carried by `x + U` is `restrictLaw U K x`, pushed into `V` and translated by `x`. -/
theorem restrictLaw_map_subtype_add (U : Submodule (ZMod 2) V) (K : PMF V) (x : V)
    (hK : ∀ v, K v ≠ 0 → v - x ∈ U) :
    ((restrictLaw U K x).map U.subtype).map (fun v => v + x) = K := by
  rw [restrictLaw_map_subtype U K x hK, PMF.map_comp]
  have hc : ((fun v => v + x) ∘ fun v => v - x) = (id : V → V) := by
    funext v
    simp
  rw [hc, PMF.map_id]

/-- **I2b.** The entropic Marton bound (35) for a law carried by a coset `x + U` of a subspace
`U`, from (35) on `U` (witness: the image in `V` of the witness on `U`). -/
theorem marton_of_support_subset_coset (U : Submodule (ZMod 2) V) [Fintype U]
    (hU : MartonInput U) (K : PMF V) (x : V) (hK : ∀ v, K v ≠ 0 → v - x ∈ U) :
    ∃ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K := by
  obtain ⟨W, hW⟩ := hU.marton (restrictLaw U K x)
  refine ⟨W.map U.subtype, ?_⟩
  have hKeq := restrictLaw_map_subtype_add U K x hK
  have hD : entropyIncrement K = entropyIncrement (restrictLaw U K x) := by
    calc entropyIncrement K
        = entropyIncrement (((restrictLaw U K x).map U.subtype).map fun v => v + x) := by
          rw [hKeq]
      _ = entropyIncrement ((restrictLaw U K x).map U.subtype) :=
          entropyIncrement_map_add_const _ x
      _ = entropyIncrement (restrictLaw U K x) :=
          entropyIncrement_map_of_add_injective U.subtype (map_add U.subtype)
            U.injective_subtype _
  calc ruzsaDist K (uniformSub (W.map U.subtype))
      = ruzsaDist (uniformSub (W.map U.subtype))
          (((restrictLaw U K x).map U.subtype).map fun v => v + x) := by
        rw [hKeq, ruzsaDist_comm]
    _ = ruzsaDist (uniformSub (W.map U.subtype)) ((restrictLaw U K x).map U.subtype) :=
        ruzsaDist_map_add_const _ _ x
    _ = ruzsaDist ((restrictLaw U K x).map U.subtype) ((uniformSub W).map U.subtype) := by
        rw [ruzsaDist_comm, uniformSub_map_subtype]
    _ = ruzsaDist (restrictLaw U K x) (uniformSub W) :=
        ruzsaDist_map_of_add_injective U.subtype (map_add U.subtype) U.injective_subtype _ _
    _ ≤ 6 * entropyIncrement (restrictLaw U K x) := hW
    _ = 6 * entropyIncrement K := by rw [hD]

end Coset

/-- A finset with at most two elements that contains `a` lies in `{a, b}` for some `b`. -/
theorem exists_pair_of_card_le_two {α : Type*} {s : Finset α} (hs : s.card ≤ 2) {a : α}
    (ha : a ∈ s) : ∃ b, ∀ v ∈ s, v = a ∨ v = b := by
  classical
  by_cases h : ∃ b ∈ s, b ≠ a
  · obtain ⟨b, hb, hba⟩ := h
    refine ⟨b, fun v hv => ?_⟩
    by_contra hne
    have hne' := not_or.mp hne
    have h3 : 2 < s.card := by
      first
        | exact Finset.two_lt_card.mpr ⟨a, ha, b, hb, v, hv, hba.symm, Ne.symm hne'.1, Ne.symm hne'.2⟩
        | exact Finset.two_lt_card_iff.mpr
            ⟨a, b, v, ha, hb, hv, hba.symm, Ne.symm hne'.1, Ne.symm hne'.2⟩
    omega
  · exact ⟨a, fun v hv => Or.inl (Classical.byContradiction fun hva => h ⟨v, hv, hva⟩)⟩

section TwoPoint

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

omit [Fintype V] in
/-- The span of one vector has dimension at most one. -/
theorem finrank_span_singleton_le_one (w : V) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({w} : Set V)) ≤ 1 := by
  first
    | exact (finrank_span_le_card ({w} : Set V)).trans (by simp)
    | simpa using finrank_span_finset_le_card ({w} : Finset V)
    | (by_cases h0 : w = 0 <;> simp_all [finrank_span_singleton])

/-- **I3.** The entropic Marton bound (35) for every law with at most two points in its support,
on every finite F₂-space: the support `{a, b}` lies in the coset `a + span {b − a}`. -/
theorem marton_of_card_lawSupport_le_two (K : PMF V) (hK : (lawSupport K).card ≤ 2) :
    ∃ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K := by
  classical
  obtain ⟨a, ha⟩ := lawSupport_nonempty K
  obtain ⟨b, hb⟩ := exists_pair_of_card_le_two hK ha
  haveI : Fintype (Submodule.span (ZMod 2) ({b - a} : Set V)) := Fintype.ofFinite _
  refine marton_of_support_subset_coset (Submodule.span (ZMod 2) ({b - a} : Set V))
    (martonInput_of_finrank_le_one (finrank_span_singleton_le_one (b - a))) K a ?_
  intro v hv
  rcases hb v ((mem_lawSupport K v).mpr hv) with h | h
  · rw [h, sub_self]
    exact Submodule.zero_mem _
  · rw [h]
    exact Submodule.subset_span (Set.mem_singleton _)

end TwoPoint

end EntropyLean
