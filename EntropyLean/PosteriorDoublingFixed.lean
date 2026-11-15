import Mathlib
import EntropyLean.PosteriorDoublingMasses

/-!
# Lemma 6.3 at fixed laws: the posterior form of the left side (roadmap item D6d3b)

With the notation of `EntropyLean/PosteriorDoubling.lean` and
`EntropyLean/PosteriorDoublingMasses.lean` (fixed laws `P₁, …, P₄` on a finite F₂-space,
`A = X₁ + X₂`, `B = X₁ + X₃`, `C = A + B`, `S = X₁ + X₂ + X₃ + X₄`, `Q_{13,b} = posteriorLaw P₁ P₃ b`),
this file proves

* `four_posterior_doubling_fixed`: the left side of `four_conditional_bsg` equals
  `∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d})`. Proof: over F₂ the Ruzsa term is
  `D(Law(A | B = z, S = s))` (`ruzsaDist_fibreLaw`); reindex `(s, z) = (b + d, b)`; the two kernel
  descriptions of `P(A = a, B = b, S = b + d)` (`acsLaw_fibre_toReal`, `fourLaw_post_toReal`) give the
  same averages (`sum_kernel_congr`);
* `four_posterior_doubling_bound`: hence
  `∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d}) ≤ 3 J + 2 H(C | S) − H(B | S) − H(A | S)`.

What this file does NOT prove: `H(C | S) = s(P₂ * P₃, P₁ * P₄)` (roadmap item D6d3c), the averaging
over index tuples, or Lemma 6.3 (34) itself (roadmap item D6d4).
-/

namespace EntropyLean

open scoped BigOperators

section PosteriorDoublingFixed

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

/-- **Left side of Lemma 6.2 for `(A, C)` given `S`, in posterior form**: it equals
`∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d})`. -/
theorem four_posterior_doubling_fixed (P₁ P₂ P₃ P₄ : PMF V) :
    ∑ s, (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) s).toReal *
        ∑ z, (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z).toReal *
          ruzsaDist (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z)
            (fibreLawSnd (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z) =
      ∑ b, ∑ d, (conv P₁ P₃ b).toReal * (conv P₂ P₄ d).toReal *
        entropyIncrement (conv (posteriorLaw P₁ P₃ b) (posteriorLaw P₂ P₄ d)) := by
  have h1 : ∑ s, (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) s).toReal *
        ∑ z, (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z).toReal *
          ruzsaDist (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z)
            (fibreLawSnd (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z) =
      ∑ s, ∑ z, (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) s).toReal *
          (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z).toReal *
          entropyIncrement (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ruzsaDist_fibreLaw]
    ring
  rw [h1]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine (Equiv.sum_comp (Equiv.addLeft b) (fun s =>
    (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) s).toReal *
      (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) b).toReal *
      entropyIncrement (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) b))).symm.trans ?_
  refine sum_kernel_congr
    (fun d => (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) (b + d)).toReal *
      (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) (b + d)) b).toReal)
    (fun d => (conv P₁ P₃ b).toReal * (conv P₂ P₄ d).toReal)
    (fun d => fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) (b + d)) b)
    (fun d => conv (posteriorLaw P₁ P₃ b) (posteriorLaw P₂ P₄ d))
    entropyIncrement (fun a d => ?_)
  show (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) (b + d)).toReal *
        (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) (b + d)) b).toReal *
        (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) (b + d)) b a).toReal =
      (conv P₁ P₃ b).toReal * (conv P₂ P₄ d).toReal *
        (conv (posteriorLaw P₁ P₃ b) (posteriorLaw P₂ P₄ d) a).toReal
  rw [← fourLaw_post_toReal, ← acsLaw_fibre_toReal]
  ring

/-- **Lemma 6.3 at fixed laws, posterior form**:
`∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d}) ≤ 3 J + 2 H(C | S) − H(B | S) − H(A | S)`. -/
theorem four_posterior_doubling_bound (P₁ P₂ P₃ P₄ : PMF V) :
    ∑ b, ∑ d, (conv P₁ P₃ b).toReal * (conv P₂ P₄ d).toReal *
        entropyIncrement (conv (posteriorLaw P₁ P₃ b) (posteriorLaw P₂ P₄ d)) ≤
      3 * fourJ P₁ P₂ P₃ P₄ +
        2 * (entropyBits ((fourLaw P₁ P₂ P₃ P₄).map fourCS) -
          entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC)) -
        (entropyBits ((fourLaw P₁ P₂ P₃ P₄).map Prod.snd) -
          entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC)) -
        (entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleAC) -
          entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC)) := by
  rw [← four_posterior_doubling_fixed]
  exact four_conditional_bsg P₁ P₂ P₃ P₄

end PosteriorDoublingFixed

end EntropyLean
