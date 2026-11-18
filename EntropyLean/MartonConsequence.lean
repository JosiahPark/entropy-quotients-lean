import EntropyLean.MathlibForPFR
import EntropyLean.MartonConvEntropy

/-!
# The consequence (36) of the entropic Marton bound (roadmap item D7c, Section 7)

For a law `K` on a finite F₂-space `V` and a subspace `W`, `H(K * U_W) ≥ H(K)` and
`H(K * U_W) ≥ H(U_W) = dim W`, so `|dim W − H(K)| / 2 ≤ d(K, U_W)`. Together with
`d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2` (`ruzsaDist_uniformSub`), the entropic Marton bound
(35) gives (36).

This file proves
* `ruzsaDist_uniformSub_ge`: `|dim W − H(K)| / 2 ≤ d(K, U_W)`;
* `MartonInput.consequence`: (36) from (35), i.e. some subspace `W` has `H(q_W K) ≤ 12 D(K)` and
  `dim W ≤ H(K) + 12 D(K) ≤ 13 H(K)`, with no further hypotheses.

What this file does NOT prove: the entropic Marton bound (35) itself. It enters only as the
hypothesis `hM : MartonInput V` and is not proved anywhere in this repository.
-/

namespace EntropyLean

section MartonConsequence

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- `|dim W − H(K)| / 2 ≤ d(K, U_W)`, from `H(K * U_W) ≥ max(H(K), dim W)`. -/
theorem ruzsaDist_uniformSub_ge (K : PMF V) (W : Submodule (ZMod 2) V) :
    |(Module.finrank (ZMod 2) W : ℝ) - entropyBits K| / 2 ≤ ruzsaDist K (uniformSub W) := by
  have h1 := entropyBits_le_conv_left K (uniformSub W)
  have h2 := entropyBits_le_conv_right K (uniformSub W)
  rw [entropyBits_uniformSub] at h2
  unfold ruzsaDist
  rw [entropyBits_uniformSub]
  rcases abs_cases ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;> linarith

/-- Equation (36) from the entropic Marton bound (35): some subspace `W` has
`H(q_W K) ≤ 12 D(K)` and `dim W ≤ H(K) + 12 D(K) ≤ 13 H(K)`. -/
theorem MartonInput.consequence (hM : MartonInput V) (K : PMF V) :
    ∃ W : Submodule (ZMod 2) V,
      entropyBits (K.map fun v => W.mkQ v) ≤ 12 * entropyIncrement K ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ entropyBits K + 12 * entropyIncrement K ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ 13 * entropyBits K :=
  hM.consequence_of_smoothing K (fun W => ruzsaDist_uniformSub K W)
    (fun W => ruzsaDist_uniformSub_ge K W)

end MartonConsequence

end EntropyLean
