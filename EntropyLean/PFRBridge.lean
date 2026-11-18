import PFR.ImprovedPFR

/-!
# Bridge to the PFR project (roadmap item B1)

The paper's one external input is the entropic Marton bound (35). Roadmap item B1 takes it from
the PFR project (github.com/teorth/pfr), where it is the theorem `entropic_PFR_conjecture_improv`,
stated for random variables on probability spaces with entropy in nats.

Proved here, in PFR's language:
* `pfr_single_variable` (roadmap item B1c): for a measurable `X : Ω₀ → G` with values in a finite
  F₂-space `G` there are a subspace `H` of `G` and a random variable `U`, uniform on `H`, with
  `d[X # U] ≤ 5 * d[X # X]`. This is PFR's bound `d[X₁ # U] + d[X₂ # U] ≤ 10 * d[X₁ # X₂]` with
  `X₁ = X₂ = X`.

What this file does NOT prove: the bound (35) for the `PMF`-based definitions of this library
(`MartonInput`, `MartonBound`). That needs the agreement of PFR's entropy and Ruzsa distance with
`entropyBits` and `ruzsaDist` (roadmap items B1d–B1f). Theorems 1.1, 1.2 and 8.2 are NOT proved
by this file.

This file does not start with `import Mathlib`, unlike the rest of the library: importing all of
Mathlib together with PFR fails, because `ProbabilityTheory.IdentDistrib.prodMk` is declared both
in `Mathlib.Probability.IdentDistribIndep` and in `PFR.Mathlib.Probability.IdentDistrib`. The
Mathlib modules that PFR itself imports are enough here.
-/

open MeasureTheory ProbabilityTheory

namespace EntropyLean

universe uG

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

end EntropyLean
