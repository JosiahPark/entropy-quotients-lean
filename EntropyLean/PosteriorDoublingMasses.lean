import Mathlib
import EntropyLean.FourSamplePosterior
import EntropyLean.PosteriorDoubling

/-!
# Masses for Lemma 6.3 at fixed laws (roadmap item D6d3a)

With the notation of `EntropyLean/FourSample.lean` and `EntropyLean/PosteriorDoubling.lean`
(fixed laws `P₁, …, P₄`, `A = X₁ + X₂`, `B = X₁ + X₃`, `S = X₁ + X₂ + X₃ + X₄`), put `D = X₂ + X₄`,
so `S = B + D`. Given `B = b` and `D = d`, the pairs `(X₁, X₃)` and `(X₂, X₄)` are independent with
`X₁ ∼ Q_{13,b} = posteriorLaw P₁ P₃ b` and `X₂ ∼ Q_{24,d}`, so `A ∼ Q_{13,b} * Q_{24,d}`. This file
proves:

* `sum_kernel_congr`: two kernel descriptions `c(t) M_t(a) = c'(t) M'_t(a)` of the same masses
  give the same averages `∑ₜ c(t) f(M_t) = ∑ₜ c'(t) f(M'_t)`, for any `f`;
* `fourLaw_eq_swap`: the law of `(A, B, S)` is the law of `(B, A, S)` for `(P₁, P₃, P₂, P₄)`;
* `fourLaw_post_toReal`: `P(A = a, B = b, S = b + d) = (P₁ * P₃)(b) (P₂ * P₄)(d) (Q_{13,b} * Q_{24,d})(a)`;
* `acsLaw_fibre_toReal`: in the left side of `four_conditional_bsg`, the weight of `(s, z)` times
  `Law(A | B = z, S = s)(a)` is `P(A = a, B = z, S = s)` (over F₂).

What this file does NOT prove: the rewriting of the left side of `four_conditional_bsg` as
`∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d})` (roadmap item D6d3b), the identity
`H(C | S) = s(P₂ * P₃, P₁ * P₄)`, or Lemma 6.3 (34) itself (roadmap item D6d4).
-/

namespace EntropyLean

open scoped BigOperators

/-- Two kernel descriptions of the same masses give the same averages. -/
theorem sum_kernel_congr {α T : Type*} [Fintype α] [Fintype T] (c c' : T → ℝ)
    (M M' : T → PMF α) (f : PMF α → ℝ)
    (h : ∀ a t, c t * (M t a).toReal = c' t * (M' t a).toReal) :
    ∑ t, c t * f (M t) = ∑ t, c' t * f (M' t) := by
  refine Finset.sum_congr rfl fun t _ => ?_
  have hs : ∑ a, c t * (M t a).toReal = ∑ a, c' t * (M' t a).toReal :=
    Finset.sum_congr rfl fun a _ => h a t
  rw [← Finset.mul_sum, ← Finset.mul_sum, pmf_sum_toReal, pmf_sum_toReal, mul_one,
    mul_one] at hs
  rcases eq_or_ne (c t) 0 with h0 | h0
  · rw [← hs, h0]
    simp
  · have hM : M t = M' t := pmf_ext_toReal _ _ fun a => by
      have e := h a t
      rw [← hs] at e
      exact mul_left_cancel₀ h0 e
    rw [hs, hM]

section PosteriorDoublingMasses

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

omit [Fintype V] [AddCommGroup V] [Module (ZMod 2) V] in
/-- `(x, y, z) ↦ (y, x, z)`. -/
def tripleSwap12 (x : V × V × V) : V × V × V := (x.2.1, x.1, x.2.2)

omit [Fintype V] [AddCommGroup V] [Module (ZMod 2) V] in
theorem tripleSwap12_injective : Function.Injective (tripleSwap12 (V := V)) := by
  intro x y h
  have h' : (x.2.1, x.1, x.2.2) = (y.2.1, y.1, y.2.2) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨h3, h4⟩ := Prod.mk.inj h2
  exact Prod.ext h3 (Prod.ext h1 h4)

omit [Module (ZMod 2) V] in
/-- The law of `(A, B, S)` is the law of `(B, A, S)` for the laws `(P₁, P₃, P₂, P₄)`. -/
theorem fourLaw_eq_swap (P₁ P₂ P₃ P₄ : PMF V) :
    fourLaw P₁ P₂ P₃ P₄ = (fourLaw P₁ P₃ P₂ P₄).map tripleSwap12 := by
  unfold fourLaw
  rw [← fourProd_swap P₁ P₂ P₃ P₄, PMF.map_comp, PMF.map_comp]
  congr 1
  funext x
  show (x.1.1 + x.1.2, x.1.1 + x.2.1, x.1.1 + x.1.2 + (x.2.1 + x.2.2)) =
    (x.1.1 + x.1.2, x.1.1 + x.2.1, x.1.1 + x.2.1 + (x.1.2 + x.2.2))
  refine Prod.ext rfl (Prod.ext rfl ?_)
  show x.1.1 + x.1.2 + (x.2.1 + x.2.2) = x.1.1 + x.2.1 + (x.1.2 + x.2.2)
  abel

omit [Module (ZMod 2) V] in
/-- `P(A = a, B = b, S = b + d) = (P₁ * P₃)(b) (P₂ * P₄)(d) (Q_{13,b} * Q_{24,d})(a)`. -/
theorem fourLaw_post_toReal (P₁ P₂ P₃ P₄ : PMF V) (a b d : V) :
    (fourLaw P₁ P₂ P₃ P₄ (a, b, b + d)).toReal =
      (conv P₁ P₃ b).toReal * (conv P₂ P₄ d).toReal *
        (conv (posteriorLaw P₁ P₃ b) (posteriorLaw P₂ P₄ d) a).toReal := by
  have h1 : fourLaw P₁ P₂ P₃ P₄ (a, b, b + d) = fourLaw P₁ P₃ P₂ P₄ (b, a, b + d) := by
    rw [fourLaw_eq_swap P₁ P₂ P₃ P₄]
    exact pmf_map_apply_injective _ tripleSwap12_injective (b, a, b + d)
  have h2 : fourLaw P₁ P₃ P₂ P₄ (b, a, b + d) =
      ((fourPostJoint P₁ P₃ P₂ P₄).map fun x => (x.1.1 + x.1.2, x.2)) (a, (b, d)) := by
    rw [fourLaw_eq_map_post P₁ P₃ P₂ P₄]
    exact pmf_map_apply_injective _ (fourPhi_injective (V := V)) (a, (b, d))
  rw [h1, h2, fourPost_masses]
  simp only [prodLaw_apply, ENNReal.toReal_mul]

/-- Over F₂: the weight `R_S(s) K_{s,Z}(z)` of `(s, z)` in `four_conditional_bsg` times
`Law(A | B = z, S = s)(a)` is `P(A = a, B = z, S = s)`. -/
theorem acsLaw_fibre_toReal (P₁ P₂ P₃ P₄ : PMF V) (s z a : V) :
    (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) s).toReal *
        ((sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z).toReal *
          (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z a).toReal) =
      (fourLaw P₁ P₂ P₃ P₄ (a, z, s)).toReal := by
  rw [sumLaw_mul_fibreLaw_toReal, condKernel_toReal_mul, sub_eq_add_of_zmod2]
  have e : (((a, a + z), s) : (V × V) × V) = acsMap (a, z, s) := rfl
  rw [e, acsLaw, pmf_map_apply_injective _ acsMap_injective]

end PosteriorDoublingMasses

end EntropyLean
