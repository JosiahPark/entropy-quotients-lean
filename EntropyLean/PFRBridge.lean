import EntropyLean.MathlibForPFR
import EntropyLean.Information
import EntropyLean.ConditionalBSG
import EntropyLean.MartonSmoothing
import EntropyLean.MartonConst
import PFR.ImprovedPFR

/-!
# The entropic Marton bound (35) from the PFR project

This file is the library's entropy backend (roadmap item B1). It proves

    martonBound : MartonBound.{0}

that is, the entropic Marton bound (35) with the paper's constant 6, with no hypothesis. The rest
of the library takes (35) as a hypothesis; `EntropyLean/Statements.lean` supplies it from here and
so proves Theorems 1.1, 1.2 and 8.2.

The proof of the bound is not this repository's. The PFR project (github.com/teorth/pfr) proves it
in Lean, with constant 5, as `entropic_PFR_conjecture_improv`. This file imports that theorem and
translates it, in three steps.

1. **PFR's theorem for one variable** (`pfr_single_variable`, B1c). For a measurable `X` with
   values in a finite F₂-space there is a variable `U`, uniform on a subspace, with
   `d[X # U] ≤ 5 * d[X # X]`. This is PFR's bound `d[X₁ # U] + d[X₂ # U] ≤ 10 * d[X₁ # X₂]` with
   `X₁ = X₂ = X`.
2. **Translation** (B1d, B1e). PFR works with random variables on probability spaces and entropy
   in nats; the library works with laws (`PMF`) and entropy in bits. For laws `K` and `L`:
   * `measureEntropy_toMeasure`: `Hm[K.toMeasure] = entropyBits K * log 2`;
   * `rdist_toMeasure`: `rdist id id K.toMeasure L.toMeasure = ruzsaDist K L * log 2`, through
     `toMeasure_prod_toMeasure` and `map_sub_prod_toMeasure` (over F₂, `A − B = A + B`);
   * `isUniform_uniformSub` and `identDistrib_uniformSub`: a variable that is uniform on a
     subspace `W` has the law `uniformSub W`.
3. **The bound for laws** (B1f). `martonBoundConst_five` applies step 1 to the identity map on `V`
   under the measure `K.toMeasure` and translates with step 2. Both sides of (35) scale by
   `log 2`, so the constant stays 5; `martonBound` weakens it to the paper's 6.

What this file does NOT prove: Theorems 1.1, 1.2 and 8.2 themselves, which `Statements.lean`
derives from `martonBound`; and the Marton bound itself, whose proof is PFR's.

Imports. `EntropyLean.MathlibForPFR` is Mathlib without the six modules that declare names PFR
also declares (that file lists them). Importing it together with `PFR.ImprovedPFR` checks that
nothing else clashes. The other four imports supply `entropyBits_eq_div_log` (`Information`),
`sub_eq_add_of_zmod2` (`ConditionalBSG`), `uniformSub_toReal` (`MartonSmoothing`) and
`MartonBoundConst` (`MartonConst`).
-/

open MeasureTheory ProbabilityTheory

namespace EntropyLean

universe uG

/-! ## Step 1: PFR's theorem for one random variable -/

/-- **B1c.** PFR's improved entropic theorem for a single random variable: a measurable `X` with
values in a finite F₂-space is within Ruzsa distance `5 * d[X # X]` of a variable `U` that is
uniform on a subspace `H`. -/
theorem pfr_single_variable {Ω₀ : Type*} [MeasureSpace Ω₀]
    [IsProbabilityMeasure (ℙ : Measure Ω₀)] {G : Type uG} [AddCommGroup G] [Module (ZMod 2) G]
    [Finite G] [MeasurableSpace G] [MeasurableSingletonClass G] (X : Ω₀ → G)
    (hX : Measurable X) :
    ∃ (H : Submodule (ZMod 2) G) (Ω : Type uG) (mΩ : MeasureSpace Ω) (U : Ω → G),
      IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧
        d[X # U] ≤ 5 * d[X # X] := by
  obtain ⟨H, Ω, mΩ, U, hP, hU, hunif, hsum, -, -⟩ :=
    entropic_PFR_conjecture_improv
      (⟨X, X, hX, hX, 1 / 8, by norm_num, by norm_num⟩ : refPackage Ω₀ Ω₀ G) rfl
  refine ⟨H, Ω, mΩ, U, hP, hU, hunif, ?_⟩
  have h : d[X # U] + d[X # U] ≤ 10 * d[X # X] := hsum
  linarith

/-! ## Step 2: translation between PFR's language and the library's -/

/-- The mass that the measure of a law `K` gives to a point, as a real number. -/
theorem toMeasure_real_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : PMF α) (a : α) : K.toMeasure.real {a} = (K a).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton K a (measurableSet_singleton a)]

/-- **B1d2.** Entropy agreement: for a law `K` on a finite type, PFR's entropy of the measure
`K.toMeasure`, which is in nats, is the library's entropy of `K`, which is in bits, times
`log 2`. -/
theorem measureEntropy_toMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (K : PMF α) :
    Hm[K.toMeasure] = entropyBits K * Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [(eq_div_iff hlog).mp (entropyBits_eq_div_log K),
    measureEntropy_of_isProbabilityMeasure K.toMeasure, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [toMeasure_real_singleton K a, Real.negMulLog]

/-- The product of the measures of two laws is the measure of their product law. -/
theorem toMeasure_prod_toMeasure {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (K : PMF α) (L : PMF β) :
    K.toMeasure.prod L.toMeasure = (prodLaw K L).toMeasure := by
  refine Measure.ext_of_singleton fun x => ?_
  obtain ⟨a, b⟩ := x
  have h1 : (K.toMeasure.prod L.toMeasure) {(a, b)} = K a * L b := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      PMF.toMeasure_apply_singleton K a (measurableSet_singleton a),
      PMF.toMeasure_apply_singleton L b (measurableSet_singleton b)]
  rw [h1, PMF.toMeasure_apply_singleton (prodLaw K L) (a, b) (measurableSet_singleton (a, b)),
    prodLaw_apply]

/-- Over F₂ the law of `A − B`, for independent `A ∼ K` and `B ∼ L`, is the convolution
`conv K L`, because `A − B = A + B`. -/
theorem map_sub_prod_toMeasure {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (K L : PMF V) :
    (K.toMeasure.prod L.toMeasure).map (fun x : V × V => x.1 - x.2) = (conv K L).toMeasure := by
  have hf : (fun x : V × V => x.1 - x.2) = fun x => x.1 + x.2 :=
    funext fun x => (sub_eq_add_of_zmod2 x.1 x.2).trans (add_comm _ _)
  have hmeas : Measurable (fun x : V × V => x.1 + x.2) := Measurable.of_discrete
  rw [hf, toMeasure_prod_toMeasure, PMF.toMeasure_map _ _ hmeas, prodLaw_map_add]

/-- **B1e.** Distance agreement: for laws `K`, `L` on a finite F₂-space, PFR's Ruzsa distance of
the measures `K.toMeasure` and `L.toMeasure`, which is in nats, is the library's `ruzsaDist K L`,
which is in bits, times `log 2`. -/
theorem rdist_toMeasure {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (K L : PMF V) :
    rdist (id : V → V) (id : V → V) K.toMeasure L.toMeasure = ruzsaDist K L * Real.log 2 := by
  simp only [rdist_def, entropy_def, Measure.map_id]
  rw [map_sub_prod_toMeasure]
  simp only [measureEntropy_toMeasure]
  unfold ruzsaDist
  ring

/-- **B1e.** The measure of the uniform law `uniformSub W` is uniform on `W` in PFR's sense. -/
theorem isUniform_uniformSub {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (W : Submodule (ZMod 2) V) :
    IsUniform (W : Set V) (id : V → V) (uniformSub W).toMeasure := by
  constructor
  · intro x hx y hy
    have hx' : x ∈ W := hx
    have hy' : y ∈ W := hy
    simp only [Set.preimage_id]
    rw [PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x),
      PMF.toMeasure_apply_singleton _ y (measurableSet_singleton y)]
    refine (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp ?_
    rw [uniformSub_toReal, uniformSub_toReal, if_pos hx', if_pos hy']
  · rw [Set.preimage_id, PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete,
      Set.disjoint_compl_right_iff_subset]
    intro v hv
    by_contra hvW
    have hvW' : v ∉ W := hvW
    have h0 : (uniformSub W v).toReal = 0 := by rw [uniformSub_toReal, if_neg hvW']
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
    · exact (PMF.mem_support_iff _ _).mp hv h
    · exact PMF.apply_ne_top _ _ h

/-- **B1e.** A measurable variable that is uniform on a subspace `W` in PFR's sense has the law
`uniformSub W`. -/
theorem identDistrib_uniformSub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V] (W : Submodule (ZMod 2) V) {U : Ω → V}
    (hU : Measurable U) (hunif : IsUniform (W : Set V) U μ) :
    IdentDistrib U (id : V → V) μ (uniformSub W).toMeasure :=
  IdentDistrib.of_isUniform (H := (W : Set V)) hU measurable_id hunif (isUniform_uniformSub W)

/-! ## Step 3: the bound for laws -/

/-- **B1f.** The entropic Marton bound (35) with constant 5, for every law `K` on every finite
F₂-space `V` in `Type`: some subspace `W` has `d(K, U_W) ≤ 5 D(K)`. No hypothesis: this is PFR's
theorem (`pfr_single_variable`) for the identity map on `V` with the measure `K.toMeasure`,
translated by `rdist_toMeasure` and `identDistrib_uniformSub`. -/
theorem martonBoundConst_five : MartonBoundConst.{0} 5 := by
  intro V _ _ _
  refine ⟨fun K => ?_⟩
  letI : MeasureSpace V := @MeasureSpace.mk V ⊤ (@PMF.toMeasure V ⊤ K)
  haveI : MeasurableSingletonClass V := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : IsProbabilityMeasure (ℙ : Measure V) := PMF.toMeasure.isProbabilityMeasure K
  obtain ⟨H, Ω, mΩ, U, hP, hU, hunif, hbound⟩ :=
    pfr_single_variable (id : V → V) measurable_id
  refine ⟨H, ?_⟩
  have hb : rdist (id : V → V) U K.toMeasure ℙ ≤
      5 * rdist (id : V → V) (id : V → V) K.toMeasure K.toMeasure := hbound
  have h1 : rdist (id : V → V) U K.toMeasure ℙ = ruzsaDist K (uniformSub H) * Real.log 2 := by
    rw [ProbabilityTheory.IdentDistrib.rdist_congr_right measurable_id.aemeasurable
      (identDistrib_uniformSub H hU hunif), rdist_toMeasure]
  have h2 : rdist (id : V → V) (id : V → V) K.toMeasure K.toMeasure =
      entropyIncrement K * Real.log 2 := by
    rw [rdist_toMeasure, ruzsaDist_self]
  rw [h1, h2, ← mul_assoc] at hb
  exact le_of_mul_le_mul_right hb (Real.log_pos one_lt_two)

/-- **B1f.** The entropic Marton bound (35) as the rest of the library uses it (constant 6), with
no hypothesis. -/
theorem martonBound : MartonBound.{0} :=
  martonBoundConst_five.toMartonBound (by norm_num)

end EntropyLean
