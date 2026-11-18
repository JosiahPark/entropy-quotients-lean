import EntropyLean.MathlibForPFR
import EntropyLean.Information
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

Proved here, between PFR's language and the library's:
* `measureEntropy_toMeasure` (roadmap item B1d2): for a law `K : PMF α` on a finite type, PFR's
  entropy of the measure `K.toMeasure` is the library's entropy of `K`, in nats instead of bits:
  `Hm[K.toMeasure] = entropyBits K * log 2`. The helper `toMeasure_real_singleton` gives the mass
  of a point.

What this file does NOT prove: the bound (35) for the `PMF`-based definitions of this library
(`MartonInput`, `MartonBound`). That still needs the agreement of PFR's Ruzsa distance with
`ruzsaDist` and of PFR's uniform variables with `uniformSub` (roadmap items B1e–B1f). Theorems
1.1, 1.2 and 8.2 are NOT proved by this file.

Imports. `EntropyLean.MathlibForPFR` is Mathlib without the six modules whose declarations have
the same names as declarations of PFR; that file gives the list and the reasons. It is imported
here together with `PFR.ImprovedPFR`, so the build of this file checks that the rest of Mathlib
and the part of PFR used here have no other name in common. `EntropyLean.Information` is imported
for `entropyBits_eq_div_log`.
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

end EntropyLean
