import Mathlib
import EntropyLean.Interaction
import EntropyLean.Fibring
import EntropyLean.CondInformation
import EntropyLean.QuotientFacts

/-!
# The four-sample setup of Section 6 at fixed indices (roadmap item D6c1)

For four laws `P₁, P₂, P₃, P₄` on a finite additive group `V` (the component laws at a fixed index
tuple `T = (I₁, I₂, I₃, I₄)`), let `Xᵣ ∼ Pᵣ` be independent and put
`A = X₁ + X₂`, `B = X₁ + X₃`, `S = X₁ + X₂ + X₃ + X₄`. This file defines

* `fourProd P₁ P₂ P₃ P₄`, the law of `((X₁, X₂), (X₃, X₄))`;
* `fourLaw P₁ P₂ P₃ P₄`, the law of `(A, B, S)`, and
  `fourJ P₁ P₂ P₃ P₄ = I(A ; B | S)` (`fourJ_nonneg`);

and proves the first step of Lemma 6.1 at fixed indices:

* `H(A | S) = s(P₁ * P₂, P₃ * P₄)` (`fourLaw_condEntropy_A`), because `A` and `S − A = X₃ + X₄`
  are independent;
* `H(B | S) = s(P₁ * P₃, P₂ * P₄)` (`fourLaw_condEntropy_B`), by exchanging `X₂` and `X₃`
  (`fourProd_swap`);
* `J = H(B | S) − H(B | A, S)` in the form
  `fourJ = s(P₁ * P₃, P₂ * P₄) − (H(A, B, S) − H(A, S))` (`fourJ_eq`).

What this file does NOT prove: the posterior formula for `H(B | A, S)` (roadmap item D6c2), the
averaging over index tuples, or Lemma 6.1 (32) itself (roadmap item D6c3).
-/

namespace EntropyLean

open scoped BigOperators

section FourSample

variable {V : Type*} [Fintype V] [AddCommGroup V]

omit [Fintype V] [AddCommGroup V] in
/-- Law of `((X₁, X₂), (X₃, X₄))` for independent `Xᵣ ∼ Pᵣ`. -/
noncomputable def fourProd (P₁ P₂ P₃ P₄ : PMF V) : PMF ((V × V) × (V × V)) :=
  prodLaw (prodLaw P₁ P₂) (prodLaw P₃ P₄)

omit [Fintype V] in
/-- `((X₁, X₂), (X₃, X₄)) ↦ (A, B, S) = (X₁ + X₂, X₁ + X₃, X₁ + X₂ + (X₃ + X₄))`. -/
def fourABS (x : (V × V) × (V × V)) : V × V × V :=
  (x.1.1 + x.1.2, x.1.1 + x.2.1, x.1.1 + x.1.2 + (x.2.1 + x.2.2))

omit [Fintype V] in
/-- Law of `(A, B, S)`. -/
noncomputable def fourLaw (P₁ P₂ P₃ P₄ : PMF V) : PMF (V × V × V) :=
  (fourProd P₁ P₂ P₃ P₄).map fourABS

omit [Fintype V] in
/-- `J = I(A ; B | S)` at fixed indices. -/
noncomputable def fourJ (P₁ P₂ P₃ P₄ : PMF V) : ℝ :=
  condMutualInfo (fourLaw P₁ P₂ P₃ P₄)

theorem fourJ_nonneg (P₁ P₂ P₃ P₄ : PMF V) : 0 ≤ fourJ P₁ P₂ P₃ P₄ :=
  condMutualInfo_nonneg _

omit [Fintype V] [AddCommGroup V] in
/-- Exchange of the middle coordinates, `((x₁, x₂), (x₃, x₄)) ↦ ((x₁, x₃), (x₂, x₄))`. -/
def fourSwap (x : (V × V) × (V × V)) : (V × V) × (V × V) := ((x.1.1, x.2.1), (x.1.2, x.2.2))

omit [Fintype V] [AddCommGroup V] in
theorem fourSwap_injective : Function.Injective (fourSwap (V := V)) := by
  intro x y h
  have h' : ((x.1.1, x.2.1), (x.1.2, x.2.2)) = ((y.1.1, y.2.1), (y.1.2, y.2.2)) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨a1, a2⟩ := Prod.mk.inj h1
  obtain ⟨b1, b2⟩ := Prod.mk.inj h2
  exact Prod.ext (Prod.ext a1 b1) (Prod.ext a2 b2)

/-- Exchanging `X₂` and `X₃`. -/
theorem fourProd_swap (P₁ P₂ P₃ P₄ : PMF V) :
    (fourProd P₁ P₂ P₃ P₄).map fourSwap = fourProd P₁ P₃ P₂ P₄ := by
  refine PMF.ext fun y => ?_
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := y
  have e : (((a, b), (c, d)) : (V × V) × (V × V)) = fourSwap ((a, c), (b, d)) := rfl
  rw [e, pmf_map_apply_injective _ fourSwap_injective]
  simp only [fourProd, fourSwap, prodLaw_apply]
  ring

omit [Fintype V] in
/-- `((X₁, X₂), (X₃, X₄)) ↦ (X₁ + X₂, X₃ + X₄)`. -/
def fourPairSums (x : (V × V) × (V × V)) : V × V := (x.1.1 + x.1.2, x.2.1 + x.2.2)

omit [Fintype V] in
/-- `((X₁, X₂), (X₃, X₄)) ↦ (X₁ + X₂, S)`. -/
def fourAS (x : (V × V) × (V × V)) : V × V := (x.1.1 + x.1.2, x.1.1 + x.1.2 + (x.2.1 + x.2.2))

omit [Fintype V] in
/-- `((X₁, X₂), (X₃, X₄)) ↦ S`. -/
def fourS (x : (V × V) × (V × V)) : V := x.1.1 + x.1.2 + (x.2.1 + x.2.2)

omit [Fintype V] in
/-- `(X₁ + X₂, X₃ + X₄) ∼ (P₁ * P₂) ⊗ (P₃ * P₄)`. -/
theorem fourProd_map_pairSums (P₁ P₂ P₃ P₄ : PMF V) :
    (fourProd P₁ P₂ P₃ P₄).map fourPairSums = prodLaw (conv P₁ P₂) (conv P₃ P₄) := by
  unfold fourProd
  rw [← prodLaw_map_add P₁ P₂, ← prodLaw_map_add P₃ P₄, ← prodLaw_map_both]
  try rfl

/-- `H(X₁ + X₂, S) − H(S) = s(P₁ * P₂, P₃ * P₄)`. -/
theorem entropyBits_fourAS_sub (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits ((fourProd P₁ P₂ P₃ P₄).map fourAS) -
        entropyBits ((fourProd P₁ P₂ P₃ P₄).map fourS) =
      interaction (conv P₁ P₂) (conv P₃ P₄) := by
  have h1 : (fourProd P₁ P₂ P₃ P₄).map fourAS =
      (prodLaw (conv P₁ P₂) (conv P₃ P₄)).map (fun x => (x.1, x.1 + x.2)) := by
    rw [← fourProd_map_pairSums P₁ P₂ P₃ P₄, PMF.map_comp]
    try rfl
  have h2 : (fourProd P₁ P₂ P₃ P₄).map fourS = conv (conv P₁ P₂) (conv P₃ P₄) := by
    rw [← prodLaw_map_add (conv P₁ P₂) (conv P₃ P₄), ← fourProd_map_pairSums P₁ P₂ P₃ P₄,
      PMF.map_comp]
    try rfl
  rw [h1, h2, entropyBits_map_of_injective _ (fst_add_injective (V := V)), entropyBits_prodLaw]
  unfold interaction
  ring

omit [Fintype V] in
/-- The law of `(A, S)`. -/
theorem fourLaw_map_AC (P₁ P₂ P₃ P₄ : PMF V) :
    (fourLaw P₁ P₂ P₃ P₄).map tripleAC = (fourProd P₁ P₂ P₃ P₄).map fourAS := by
  unfold fourLaw
  rw [PMF.map_comp]
  try rfl

omit [Fintype V] in
/-- The law of `S`. -/
theorem fourLaw_map_C (P₁ P₂ P₃ P₄ : PMF V) :
    (fourLaw P₁ P₂ P₃ P₄).map tripleC = (fourProd P₁ P₂ P₃ P₄).map fourS := by
  unfold fourLaw
  rw [PMF.map_comp]
  try rfl

omit [Fintype V] in
/-- The law of `(B, S)` is the law of `(X₁ + X₃, S)` after exchanging `X₂` and `X₃`. -/
theorem fourLaw_map_BC (P₁ P₂ P₃ P₄ : PMF V) :
    (fourLaw P₁ P₂ P₃ P₄).map Prod.snd = (fourProd P₁ P₃ P₂ P₄).map fourAS := by
  unfold fourLaw
  rw [← fourProd_swap P₁ P₂ P₃ P₄, PMF.map_comp, PMF.map_comp]
  congr 1
  funext x
  refine Prod.ext rfl ?_
  show x.1.1 + x.1.2 + (x.2.1 + x.2.2) = x.1.1 + x.2.1 + (x.1.2 + x.2.2)
  abel

omit [Fintype V] in
/-- The law of `S`, after exchanging `X₂` and `X₃`. -/
theorem fourLaw_map_C_swap (P₁ P₂ P₃ P₄ : PMF V) :
    (fourLaw P₁ P₂ P₃ P₄).map tripleC = (fourProd P₁ P₃ P₂ P₄).map fourS := by
  unfold fourLaw
  rw [← fourProd_swap P₁ P₂ P₃ P₄, PMF.map_comp, PMF.map_comp]
  congr 1
  funext x
  show x.1.1 + x.1.2 + (x.2.1 + x.2.2) = x.1.1 + x.2.1 + (x.1.2 + x.2.2)
  abel

/-- `H(A | S) = H(A, S) − H(S) = s(P₁ * P₂, P₃ * P₄)`. -/
theorem fourLaw_condEntropy_A (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleAC) -
        entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC) =
      interaction (conv P₁ P₂) (conv P₃ P₄) := by
  rw [fourLaw_map_AC, fourLaw_map_C]
  exact entropyBits_fourAS_sub P₁ P₂ P₃ P₄

/-- `H(B | S) = H(B, S) − H(S) = s(P₁ * P₃, P₂ * P₄)`. -/
theorem fourLaw_condEntropy_B (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits ((fourLaw P₁ P₂ P₃ P₄).map Prod.snd) -
        entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC) =
      interaction (conv P₁ P₃) (conv P₂ P₄) := by
  rw [fourLaw_map_BC, fourLaw_map_C_swap]
  exact entropyBits_fourAS_sub P₁ P₃ P₂ P₄

/-- `J = H(B | S) − H(B | A, S) = s(P₁ * P₃, P₂ * P₄) − (H(A, B, S) − H(A, S))`. -/
theorem fourJ_eq (P₁ P₂ P₃ P₄ : PMF V) :
    fourJ P₁ P₂ P₃ P₄ = interaction (conv P₁ P₃) (conv P₂ P₄) -
      (entropyBits (fourLaw P₁ P₂ P₃ P₄) - entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleAC)) := by
  have hB := fourLaw_condEntropy_B P₁ P₂ P₃ P₄
  unfold fourJ condMutualInfo
  linarith

end FourSample

end EntropyLean
