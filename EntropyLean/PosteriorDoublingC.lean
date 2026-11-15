import Mathlib
import EntropyLean.PosteriorDoublingFixed

/-!
# Lemma 6.3 at fixed laws: `H(C | S)` (roadmap item D6d3c)

With the notation of `EntropyLean/FourSample.lean` and `EntropyLean/PosteriorDoubling.lean`
(fixed laws `P₁, …, P₄` on a finite F₂-space, `A = X₁ + X₂`, `B = X₁ + X₃`,
`S = X₁ + X₂ + X₃ + X₄`, `C = A + B`), over F₂ we have `C = X₂ + X₃`. Relabelling
`(X₁, X₂, X₃, X₄) ↦ (X₂, X₃, X₁, X₄)` (`fourProd_rot`) turns `(C, S)` into `(X₂ + X₃, S)`, so
as in `fourLaw_condEntropy_A` this file proves

* `fourLaw_condEntropy_C : H(C | S) = s(P₂ * P₃, P₁ * P₄)`;
* `four_posterior_doubling_interaction`: the fixed-law bound of `four_posterior_doubling_bound`
  with all conditional entropies written as interactions,
  `∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d})
     ≤ 3 J + 2 s(P₂ * P₃, P₁ * P₄) − s(P₁ * P₃, P₂ * P₄) − s(P₁ * P₂, P₃ * P₄)`.

What this file does NOT prove: the averaging over index tuples, or Lemma 6.3 (34) itself
(roadmap item D6d4).
-/

namespace EntropyLean

open scoped BigOperators

section PosteriorDoublingC

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

omit [Fintype V] [AddCommGroup V] [Module (ZMod 2) V] in
/-- Relabelling `((x₁, x₂), (x₃, x₄)) ↦ ((x₂, x₃), (x₁, x₄))`. -/
def fourRot (x : (V × V) × (V × V)) : (V × V) × (V × V) := ((x.1.2, x.2.1), (x.1.1, x.2.2))

omit [Fintype V] [AddCommGroup V] [Module (ZMod 2) V] in
theorem fourRot_injective : Function.Injective (fourRot (V := V)) := by
  intro x y h
  have h' : ((x.1.2, x.2.1), (x.1.1, x.2.2)) = ((y.1.2, y.2.1), (y.1.1, y.2.2)) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨a1, a2⟩ := Prod.mk.inj h1
  obtain ⟨b1, b2⟩ := Prod.mk.inj h2
  exact Prod.ext (Prod.ext b1 a1) (Prod.ext a2 b2)

omit [AddCommGroup V] [Module (ZMod 2) V] in
/-- The relabelled samples have laws `(P₂, P₃, P₁, P₄)`. -/
theorem fourProd_rot (P₁ P₂ P₃ P₄ : PMF V) :
    (fourProd P₁ P₂ P₃ P₄).map fourRot = fourProd P₂ P₃ P₁ P₄ := by
  refine PMF.ext fun y => ?_
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := y
  have e : (((a, b), (c, d)) : (V × V) × (V × V)) = fourRot ((c, a), (b, d)) := rfl
  rw [e, pmf_map_apply_injective _ fourRot_injective]
  simp only [fourProd, fourRot, prodLaw_apply]
  ring

/-- Over F₂, the law of `(C, S)` is the law of `(X₂ + X₃, S)`, i.e. of `fourAS` for
`(P₂, P₃, P₁, P₄)`. -/
theorem fourLaw_map_CS (P₁ P₂ P₃ P₄ : PMF V) :
    (fourLaw P₁ P₂ P₃ P₄).map fourCS = (fourProd P₂ P₃ P₁ P₄).map fourAS := by
  unfold fourLaw
  rw [← fourProd_rot P₁ P₂ P₃ P₄, PMF.map_comp, PMF.map_comp]
  congr 1
  funext x
  show (x.1.1 + x.1.2 + (x.1.1 + x.2.1), x.1.1 + x.1.2 + (x.2.1 + x.2.2)) =
    (x.1.2 + x.2.1, x.1.2 + x.2.1 + (x.1.1 + x.2.2))
  refine Prod.ext ?_ ?_
  · show x.1.1 + x.1.2 + (x.1.1 + x.2.1) = x.1.2 + x.2.1
    calc x.1.1 + x.1.2 + (x.1.1 + x.2.1) = x.1.1 + (x.1.1 + (x.1.2 + x.2.1)) := by abel
      _ = x.1.2 + x.2.1 := zmod2_add_add_self _ _
  · show x.1.1 + x.1.2 + (x.2.1 + x.2.2) = x.1.2 + x.2.1 + (x.1.1 + x.2.2)
    abel

omit [Module (ZMod 2) V] in
/-- The law of `S`, after the relabelling. -/
theorem fourLaw_map_C_rot (P₁ P₂ P₃ P₄ : PMF V) :
    (fourLaw P₁ P₂ P₃ P₄).map tripleC = (fourProd P₂ P₃ P₁ P₄).map fourS := by
  unfold fourLaw
  rw [← fourProd_rot P₁ P₂ P₃ P₄, PMF.map_comp, PMF.map_comp]
  congr 1
  funext x
  show x.1.1 + x.1.2 + (x.2.1 + x.2.2) = x.1.2 + x.2.1 + (x.1.1 + x.2.2)
  abel

/-- `H(C | S) = H(C, S) − H(S) = s(P₂ * P₃, P₁ * P₄)` over F₂. -/
theorem fourLaw_condEntropy_C (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits ((fourLaw P₁ P₂ P₃ P₄).map fourCS) -
        entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC) =
      interaction (conv P₂ P₃) (conv P₁ P₄) := by
  rw [fourLaw_map_CS, fourLaw_map_C_rot]
  exact entropyBits_fourAS_sub P₂ P₃ P₁ P₄

/-- **Lemma 6.3 at fixed laws, interaction form**:
`∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d})
   ≤ 3 J + 2 s(P₂ * P₃, P₁ * P₄) − s(P₁ * P₃, P₂ * P₄) − s(P₁ * P₂, P₃ * P₄)`. -/
theorem four_posterior_doubling_interaction (P₁ P₂ P₃ P₄ : PMF V) :
    ∑ b, ∑ d, (conv P₁ P₃ b).toReal * (conv P₂ P₄ d).toReal *
        entropyIncrement (conv (posteriorLaw P₁ P₃ b) (posteriorLaw P₂ P₄ d)) ≤
      3 * fourJ P₁ P₂ P₃ P₄ + 2 * interaction (conv P₂ P₃) (conv P₁ P₄) -
        interaction (conv P₁ P₃) (conv P₂ P₄) - interaction (conv P₁ P₂) (conv P₃ P₄) := by
  have h := four_posterior_doubling_bound P₁ P₂ P₃ P₄
  have hC := fourLaw_condEntropy_C P₁ P₂ P₃ P₄
  have hB := fourLaw_condEntropy_B P₁ P₂ P₃ P₄
  have hA := fourLaw_condEntropy_A P₁ P₂ P₃ P₄
  linarith

end PosteriorDoublingC

end EntropyLean
