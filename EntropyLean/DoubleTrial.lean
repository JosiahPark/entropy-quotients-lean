import Mathlib
import EntropyLean.ConditionalBSG

/-!
# The conditionally independent double trial (roadmap items D6b2a–D6b2b, towards Lemma 6.2)

For a joint law `R` of `(U, V)` on a finite F₂-space, with `Z = U + V` and conditional laws
`K_z = Law(U | Z = z)` (`fibreLaw`, from `EntropyLean/ConditionalBSG.lean`):

* a general joint law from a kernel, `kernelJoint c K` with masses `c(t) K_t(a)`
  (`kernelJoint_apply`, `kernelJoint_toReal`, `entropyBits_kernelJoint`), and equality of laws
  from equality of real masses (`pmf_ext_toReal`);
* the double trial `doubleTrial R`, the law of `((U₁, U₂), Z)` with masses `R_Z(z) K_z(a) K_z(b)`
  (two conditionally independent copies of `U` given `Z`), and
  `H(U₁, U₂, Z) = 2H(U, V) − H(Z)` (`entropyBits_doubleTrial`);
* `(U₁, Z)` and `(U₂, Z)` both have the law of `(U, U + V)` (`doubleTrial_map_fst_pair`,
  `doubleTrial_map_snd_pair`); hence `U₁, U₂ ∼ U` and, over F₂, `V₁ = U₁ + Z`, `V₂ = U₂ + Z ∼ V`
  (`doubleTrial_map_U1`, `doubleTrial_map_U2`, `doubleTrial_map_V1`, `doubleTrial_map_V2`);
* `H(U₁, V₂) ≤ H(U) + H(V)` and `H(V₁, U₂) ≤ H(U) + H(V)` (`entropyBits_dtPair1_le`,
  `entropyBits_dtPair2_le`);
* with `W = U₁ + V₂ = V₁ + U₂` (`dtSum`), submodularity applied to `((U₁, V₂), (V₁, U₂), W)`
  (`dtTriple`, an injective image of the double trial) gives `H(W) ≤ 2I(U ; V) + H(Z)`
  (`double_trial_sum_le`).

What this file does NOT prove: the bound `∑_z R_Z(z) H(K_z * K_z) ≤ H(W)` (roadmap item D6b3) or
Lemma 6.2 (33) itself.
-/

namespace EntropyLean

open scoped BigOperators

/-- Joint law of `(A, T)` with `T ∼ c` and `A ∼ K_T` given `T`. -/
noncomputable def kernelJoint {α T : Type*} (c : PMF T) (K : T → PMF α) : PMF (α × T) :=
  c.bind fun t => (K t).map fun a => (a, t)

/-- Masses of `kernelJoint c K`: `c(t) K_t(a)`. -/
theorem kernelJoint_apply {α T : Type*} [Fintype α] [Fintype T] (c : PMF T) (K : T → PMF α)
    (a : α) (t : T) : kernelJoint c K (a, t) = c t * K t a := by
  classical
  unfold kernelJoint
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single t]
  · rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single a]
    · simp
    · intro a' _ ha'
      simp [Ne.symm ha']
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  · intro t' _ ht'
    rw [PMF.map_apply, tsum_fintype]
    simp [Ne.symm ht']
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- Masses of `kernelJoint c K`, as real numbers. -/
theorem kernelJoint_toReal {α T : Type*} [Fintype α] [Fintype T] (c : PMF T) (K : T → PMF α)
    (a : α) (t : T) : (kernelJoint c K (a, t)).toReal = (c t).toReal * (K t a).toReal := by
  rw [kernelJoint_apply, ENNReal.toReal_mul]

/-- `H(kernelJoint c K) = H(c) + ∑ₜ c(t) H(K_t)`. -/
theorem entropyBits_kernelJoint {α T : Type*} [Fintype α] [Fintype T] (c : PMF T)
    (K : T → PMF α) :
    entropyBits (kernelJoint c K) = entropyBits c + ∑ t, (c t).toReal * entropyBits (K t) :=
  entropyBits_of_kernel _ c K (kernelJoint_toReal c K)

/-- Two laws with the same real masses are equal. -/
theorem pmf_ext_toReal {α : Type*} (P Q : PMF α) (h : ∀ x, (P x).toReal = (Q x).toReal) :
    P = Q :=
  PMF.ext fun x =>
    calc P x = ENNReal.ofReal (P x).toReal := (ENNReal.ofReal_toReal (PMF.apply_ne_top P x)).symm
      _ = ENNReal.ofReal (Q x).toReal := by rw [h x]
      _ = Q x := ENNReal.ofReal_toReal (PMF.apply_ne_top Q x)

section DoubleTrial

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

/-- The conditionally independent double trial: the law of `((U₁, U₂), Z)` with
`Z ∼ R_Z` and `U₁, U₂` independent with law `Law(U | Z)` given `Z`. -/
noncomputable def doubleTrial (R : PMF (V × V)) : PMF ((V × V) × V) :=
  kernelJoint (sumLaw R) fun z => prodLaw (fibreLaw R z) (fibreLaw R z)

/-- `H(U₁, U₂, Z) = 2H(U, V) − H(Z)`. -/
theorem entropyBits_doubleTrial (R : PMF (V × V)) :
    entropyBits (doubleTrial R) = 2 * entropyBits R - entropyBits (sumLaw R) := by
  have hc := entropyBits_fibre_chain R
  unfold doubleTrial
  rw [entropyBits_kernelJoint]
  simp only [entropyBits_prodLaw]
  have e : ∑ z, (sumLaw R z).toReal * (entropyBits (fibreLaw R z) + entropyBits (fibreLaw R z)) =
      2 * ∑ z, (sumLaw R z).toReal * entropyBits (fibreLaw R z) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [e]
  linarith

/-- `(U₁, Z)` has the law of `(U, U + V)`. -/
theorem doubleTrial_map_fst_pair (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => (x.1.1, x.2)) = R.map (fun x => (x.1, x.1 + x.2)) := by
  classical
  refine pmf_ext_toReal _ _ fun p => ?_
  obtain ⟨u, t⟩ := p
  rw [fibrePair_masses]
  have h := kernel_masses_map
    (kernelJoint (sumLaw R) fun z => prodLaw (fibreLaw R z) (fibreLaw R z))
    (sumLaw R) (fun z => prodLaw (fibreLaw R z) (fibreLaw R z)) Prod.fst
    (kernelJoint_toReal _ _) u t
  simp only [prodLaw_map_fst] at h
  exact h

/-- `(U₂, Z)` has the law of `(U, U + V)`. -/
theorem doubleTrial_map_snd_pair (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => (x.1.2, x.2)) = R.map (fun x => (x.1, x.1 + x.2)) := by
  classical
  refine pmf_ext_toReal _ _ fun p => ?_
  obtain ⟨u, t⟩ := p
  rw [fibrePair_masses]
  have h := kernel_masses_map
    (kernelJoint (sumLaw R) fun z => prodLaw (fibreLaw R z) (fibreLaw R z))
    (sumLaw R) (fun z => prodLaw (fibreLaw R z) (fibreLaw R z)) Prod.snd
    (kernelJoint_toReal _ _) u t
  simp only [prodLaw_map_snd] at h
  exact h

omit [Fintype V] in
/-- In a `ZMod 2`-module, `a + (a + b) = b`. -/
theorem zmod2_add_add_self (a b : V) : a + (a + b) = b := by
  have h := sub_eq_add_of_zmod2 (a + b) a
  rw [← h]
  abel

omit [Fintype V] in
/-- Over F₂, `(a, z) ↦ a + z` recovers `V` from `(U, U + V)`. -/
theorem add_comp_fst_add :
    ((fun p : V × V => p.1 + p.2) ∘ fun x : V × V => (x.1, x.1 + x.2)) = Prod.snd := by
  funext x
  exact zmod2_add_add_self x.1 x.2

/-- `U₁ ∼ U`. -/
theorem doubleTrial_map_U1 (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => x.1.1) = R.map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (doubleTrial_map_fst_pair R)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

/-- `U₂ ∼ U`. -/
theorem doubleTrial_map_U2 (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => x.1.2) = R.map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (doubleTrial_map_snd_pair R)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

/-- `V₁ = U₁ + Z ∼ V`. -/
theorem doubleTrial_map_V1 (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => x.1.1 + x.2) = R.map Prod.snd := by
  have h := congrArg (PMF.map fun p : V × V => p.1 + p.2) (doubleTrial_map_fst_pair R)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h.trans (congrArg (fun f => PMF.map f R) (add_comp_fst_add (V := V)))

/-- `V₂ = U₂ + Z ∼ V`. -/
theorem doubleTrial_map_V2 (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => x.1.2 + x.2) = R.map Prod.snd := by
  have h := congrArg (PMF.map fun p : V × V => p.1 + p.2) (doubleTrial_map_snd_pair R)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h.trans (congrArg (fun f => PMF.map f R) (add_comp_fst_add (V := V)))

omit [Fintype V] [Module (ZMod 2) V] in
/-- The pair `(U₁, V₂) = (U₁, U₂ + Z)`. -/
def dtPair1 (x : (V × V) × V) : V × V := (x.1.1, x.1.2 + x.2)

omit [Fintype V] [Module (ZMod 2) V] in
/-- The pair `(V₁, U₂) = (U₁ + Z, U₂)`. -/
def dtPair2 (x : (V × V) × V) : V × V := (x.1.1 + x.2, x.1.2)

/-- `H(U₁, V₂) ≤ H(U) + H(V)`. -/
theorem entropyBits_dtPair1_le (R : PMF (V × V)) :
    entropyBits ((doubleTrial R).map dtPair1) ≤
      entropyBits (R.map Prod.fst) + entropyBits (R.map Prod.snd) := by
  have h := entropyBits_subadditive ((doubleTrial R).map dtPair1)
  rw [PMF.map_comp, PMF.map_comp] at h
  have e1 : (Prod.fst ∘ dtPair1 : (V × V) × V → V) = fun x => x.1.1 := rfl
  have e2 : (Prod.snd ∘ dtPair1 : (V × V) × V → V) = fun x => x.1.2 + x.2 := rfl
  rw [e1, e2, doubleTrial_map_U1, doubleTrial_map_V2] at h
  exact h

/-- `H(V₁, U₂) ≤ H(U) + H(V)`. -/
theorem entropyBits_dtPair2_le (R : PMF (V × V)) :
    entropyBits ((doubleTrial R).map dtPair2) ≤
      entropyBits (R.map Prod.fst) + entropyBits (R.map Prod.snd) := by
  have h := entropyBits_subadditive ((doubleTrial R).map dtPair2)
  rw [PMF.map_comp, PMF.map_comp] at h
  have e1 : (Prod.fst ∘ dtPair2 : (V × V) × V → V) = fun x => x.1.1 + x.2 := rfl
  have e2 : (Prod.snd ∘ dtPair2 : (V × V) × V → V) = fun x => x.1.2 := rfl
  rw [e1, e2, doubleTrial_map_V1, doubleTrial_map_U2] at h
  linarith

omit [Fintype V] [Module (ZMod 2) V] in
/-- `W = U₁ + V₂ = U₁ + U₂ + Z`. -/
def dtSum (x : (V × V) × V) : V := x.1.1 + (x.1.2 + x.2)

omit [Fintype V] [Module (ZMod 2) V] in
/-- The triple `((U₁, V₂), (V₁, U₂), W)`. -/
def dtTriple (x : (V × V) × V) : (V × V) × (V × V) × V := (dtPair1 x, dtPair2 x, dtSum x)

omit [Fintype V] [Module (ZMod 2) V] in
/-- A pair together with its sum. -/
def withSum (p : V × V) : (V × V) × V := (p, p.1 + p.2)

omit [Fintype V] [Module (ZMod 2) V] in
theorem withSum_injective : Function.Injective (withSum (V := V)) := by
  intro p q h
  have h' : (p, p.1 + p.2) = (q, q.1 + q.2) := h
  exact (Prod.mk.inj h').1

omit [Fintype V] [Module (ZMod 2) V] in
/-- The double trial is recovered from `((U₁, V₂), (V₁, U₂), W)`. -/
theorem dtTriple_injective : Function.Injective (dtTriple (V := V)) := by
  intro x y h
  have h' : ((x.1.1, x.1.2 + x.2), (x.1.1 + x.2, x.1.2), dtSum x) =
      ((y.1.1, y.1.2 + y.2), (y.1.1 + y.2, y.1.2), dtSum y) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨h3, -⟩ := Prod.mk.inj h2
  obtain ⟨ha, -⟩ := Prod.mk.inj h1
  obtain ⟨hc, hb⟩ := Prod.mk.inj h3
  rw [ha] at hc
  exact Prod.ext (Prod.ext ha hb) (add_left_cancel hc)

/-- `H(U₁ + V₂) ≤ 2I(U ; V) + H(Z)`: submodularity for `((U₁, V₂), (V₁, U₂), W)`, where each
pair determines `W` and all three determine the double trial. -/
theorem double_trial_sum_le (R : PMF (V × V)) :
    entropyBits ((doubleTrial R).map dtSum) ≤ 2 * mutualInfo R + entropyBits (sumLaw R) := by
  have hs := entropyBits_submodular ((doubleTrial R).map dtTriple)
  have e0 : entropyBits ((doubleTrial R).map dtTriple) = entropyBits (doubleTrial R) :=
    entropyBits_map_of_injective _ dtTriple_injective
  have eC : ((doubleTrial R).map dtTriple).map tripleC = (doubleTrial R).map dtSum := by
    rw [PMF.map_comp]
    try rfl
  have eA : ((doubleTrial R).map dtTriple).map tripleAC =
      ((doubleTrial R).map dtPair1).map withSum := by
    rw [PMF.map_comp, PMF.map_comp]
    try rfl
  have eB : ((doubleTrial R).map dtTriple).map Prod.snd =
      ((doubleTrial R).map dtPair2).map withSum := by
    rw [PMF.map_comp, PMF.map_comp]
    have hf : (Prod.snd ∘ dtTriple : (V × V) × V → (V × V) × V) = withSum ∘ dtPair2 := by
      funext x
      show (dtPair2 x, dtSum x) = (dtPair2 x, x.1.1 + x.2 + x.1.2)
      rw [show x.1.1 + x.2 + x.1.2 = dtSum x by unfold dtSum; abel]
    rw [hf]
  rw [e0, eC, eA, eB, entropyBits_map_of_injective _ withSum_injective,
    entropyBits_map_of_injective _ withSum_injective, entropyBits_doubleTrial] at hs
  have h1 := entropyBits_dtPair1_le R
  have h2 := entropyBits_dtPair2_le R
  unfold mutualInfo
  linarith

end DoubleTrial

end EntropyLean
