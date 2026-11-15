import Mathlib
import EntropyLean.FourSample
import EntropyLean.Posterior

/-!
# The posterior term of the four-sample setup (roadmap item D6c2)

With the notation of `EntropyLean/FourSample.lean` (four fixed laws `P₁, …, P₄`, independent
`Xᵣ ∼ Pᵣ`, `A = X₁ + X₂`, `B = X₁ + X₃`, `S = A + X₃ + X₄`), put `C = X₃ + X₄`. Given `A = a` and
`C = c`, the coordinates `X₁ ∼ Q_{12,a} = posteriorLaw P₁ P₂ a` and `X₃ ∼ Q_{34,c}` are independent.
This file proves:

* the law `fourPostJoint` of `((X₁, X₃), (A, C))` has masses
  `(P₁ * P₂)(a) (P₃ * P₄)(c) Q_{12,a}(x₁) Q_{34,c}(x₃)` (`fourPostJoint_kernel`);
* hence the law of `(B, (A, C))` is the kernel law `(P₁ * P₂)(a) (P₃ * P₄)(c) (Q_{12,a} * Q_{34,c})(b)`
  (`fourPost_masses`) and `H(B, A, C) = H(A, C) + ∑ (P₁ * P₂)(a) (P₃ * P₄)(c) H(Q_{12,a} * Q_{34,c})`
  (`entropyBits_fourPost`);
* `fourLaw` (the law of `(A, B, S)`) is an injective image of the law of `(B, (A, C))`
  (`fourLaw_eq_map_post`), and the law of `(A, S)` has the entropy of `(P₁ * P₂) ⊗ (P₃ * P₄)`
  (`entropyBits_fourLaw_AC`);
* `H(B | A, S) = H(A, B, S) − H(A, S) = ∑_{a,c} (P₁ * P₂)(a) (P₃ * P₄)(c) H(Q_{12,a} * Q_{34,c})`
  (`fourLaw_condEntropy_B_given_AS`).

What this file does NOT prove: the averaging over index tuples and Lemma 6.1 (32) itself (roadmap
item D6c3).
-/

namespace EntropyLean

open scoped BigOperators

section FourSamplePosterior

variable {V : Type*} [Fintype V] [AddCommGroup V]

omit [Fintype V] in
/-- Law of `((X₁, X₃), (A, C))`, with `A = X₁ + X₂` and `C = X₃ + X₄`. -/
noncomputable def fourPostJoint (P₁ P₂ P₃ P₄ : PMF V) : PMF ((V × V) × (V × V)) :=
  (prodLaw ((prodLaw P₁ P₂).map fun x => (x.1, x.1 + x.2))
    ((prodLaw P₃ P₄).map fun x => (x.1, x.1 + x.2))).map fourSwap

/-- Masses of `((X₁, X₃), (A, C))`: `(P₁ * P₂ ⊗ P₃ * P₄)(a, c) · (Q_{12,a} ⊗ Q_{34,c})(x₁, x₃)`. -/
theorem fourPostJoint_kernel (P₁ P₂ P₃ P₄ : PMF V) (u v : V × V) :
    (fourPostJoint P₁ P₂ P₃ P₄ (u, v)).toReal =
      (prodLaw (conv P₁ P₂) (conv P₃ P₄) v).toReal *
        (prodLaw (posteriorLaw P₁ P₂ v.1) (posteriorLaw P₃ P₄ v.2) u).toReal := by
  obtain ⟨x₁, x₃⟩ := u
  obtain ⟨a, c⟩ := v
  show _ = (prodLaw (conv P₁ P₂) (conv P₃ P₄) (a, c)).toReal *
      (prodLaw (posteriorLaw P₁ P₂ a) (posteriorLaw P₃ P₄ c) (x₁, x₃)).toReal
  have e : (((x₁, x₃), (a, c)) : (V × V) × (V × V)) = fourSwap ((x₁, a), (x₃, c)) := rfl
  unfold fourPostJoint
  rw [e, pmf_map_apply_injective _ fourSwap_injective]
  simp only [prodLaw_apply, ENNReal.toReal_mul]
  rw [pair_sum_masses, pair_sum_masses]
  ring

/-- Masses of `(B, (A, C))`. -/
theorem fourPost_masses (P₁ P₂ P₃ P₄ : PMF V) (b : V) (v : V × V) :
    (((fourPostJoint P₁ P₂ P₃ P₄).map fun x => (x.1.1 + x.1.2, x.2)) (b, v)).toReal =
      (prodLaw (conv P₁ P₂) (conv P₃ P₄) v).toReal *
        (conv (posteriorLaw P₁ P₂ v.1) (posteriorLaw P₃ P₄ v.2) b).toReal := by
  classical
  have h : (((fourPostJoint P₁ P₂ P₃ P₄).map
      fun x => ((fun p : V × V => p.1 + p.2) x.1, x.2)) (b, v)).toReal =
      (prodLaw (conv P₁ P₂) (conv P₃ P₄) v).toReal *
        (((prodLaw (posteriorLaw P₁ P₂ v.1) (posteriorLaw P₃ P₄ v.2)).map
          fun p : V × V => p.1 + p.2) b).toReal :=
    kernel_masses_map (fourPostJoint P₁ P₂ P₃ P₄) (prodLaw (conv P₁ P₂) (conv P₃ P₄))
      (fun v => prodLaw (posteriorLaw P₁ P₂ v.1) (posteriorLaw P₃ P₄ v.2))
      (fun p : V × V => p.1 + p.2) (fourPostJoint_kernel P₁ P₂ P₃ P₄) b v
  rw [prodLaw_map_add] at h
  exact h

/-- `H(B, A, C) = H(A, C) + ∑_{(a, c)} (P₁ * P₂)(a) (P₃ * P₄)(c) H(Q_{12,a} * Q_{34,c})`. -/
theorem entropyBits_fourPost (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits ((fourPostJoint P₁ P₂ P₃ P₄).map fun x => (x.1.1 + x.1.2, x.2)) =
      entropyBits (prodLaw (conv P₁ P₂) (conv P₃ P₄)) +
        ∑ v, (prodLaw (conv P₁ P₂) (conv P₃ P₄) v).toReal *
          entropyBits (conv (posteriorLaw P₁ P₂ v.1) (posteriorLaw P₃ P₄ v.2)) := by
  have h := entropyBits_of_kernel (α := V) (T := V × V)
    ((fourPostJoint P₁ P₂ P₃ P₄).map fun x => (x.1.1 + x.1.2, x.2))
    (prodLaw (conv P₁ P₂) (conv P₃ P₄))
    (fun v : V × V => conv (posteriorLaw P₁ P₂ v.1) (posteriorLaw P₃ P₄ v.2))
    (fun b v => fourPost_masses P₁ P₂ P₃ P₄ b v)
  exact h

omit [Fintype V] in
/-- `(b, (a, c)) ↦ (a, b, a + c)` is injective. -/
theorem fourPhi_injective :
    Function.Injective (fun y : V × V × V => (y.2.1, y.1, y.2.1 + y.2.2)) := by
  intro y z h
  have h' : (y.2.1, y.1, y.2.1 + y.2.2) = (z.2.1, z.1, z.2.1 + z.2.2) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨h3, h4⟩ := Prod.mk.inj h2
  rw [h1] at h4
  exact Prod.ext h3 (Prod.ext h1 (add_left_cancel h4))

omit [Fintype V] in
/-- `(A, B, S)` is the image of `(B, (A, C))` under `(b, (a, c)) ↦ (a, b, a + c)`. -/
theorem fourLaw_eq_map_post (P₁ P₂ P₃ P₄ : PMF V) :
    fourLaw P₁ P₂ P₃ P₄ =
      ((fourPostJoint P₁ P₂ P₃ P₄).map fun x => (x.1.1 + x.1.2, x.2)).map
        fun y => (y.2.1, y.1, y.2.1 + y.2.2) := by
  unfold fourLaw fourPostJoint fourProd
  rw [← prodLaw_map_both, PMF.map_comp, PMF.map_comp, PMF.map_comp]
  try rfl

omit [Fintype V] in
/-- `H(A, S) = H((P₁ * P₂) ⊗ (P₃ * P₄))`. -/
theorem entropyBits_fourLaw_AC (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleAC) =
      entropyBits (prodLaw (conv P₁ P₂) (conv P₃ P₄)) := by
  have h1 : (fourProd P₁ P₂ P₃ P₄).map fourAS =
      (prodLaw (conv P₁ P₂) (conv P₃ P₄)).map (fun x => (x.1, x.1 + x.2)) := by
    rw [← fourProd_map_pairSums P₁ P₂ P₃ P₄, PMF.map_comp]
    try rfl
  rw [fourLaw_map_AC, h1, entropyBits_map_of_injective _ (fst_add_injective (V := V))]

/-- `H(B | A, S) = ∑_{a,c} (P₁ * P₂)(a) (P₃ * P₄)(c) H(Q_{12,a} * Q_{34,c})`. -/
theorem fourLaw_condEntropy_B_given_AS (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits (fourLaw P₁ P₂ P₃ P₄) - entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleAC) =
      ∑ a, ∑ c, (conv P₁ P₂ a).toReal * (conv P₃ P₄ c).toReal *
        entropyBits (conv (posteriorLaw P₁ P₂ a) (posteriorLaw P₃ P₄ c)) := by
  rw [entropyBits_fourLaw_AC, fourLaw_eq_map_post,
    entropyBits_map_of_injective _ (fourPhi_injective (V := V)), entropyBits_fourPost,
    Fintype.sum_prod_type]
  simp only [prodLaw_apply, ENNReal.toReal_mul]
  ring

end FourSamplePosterior

end EntropyLean
