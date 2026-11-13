import EntropyLean.Basic

/-!
# Finite weighted families (Section 2.2)

A finite weighted family `𝒫 = (P_i, a_i)` of laws on one space with positive weights summing to
one; the mean entropy `h(𝒫)`, mean interaction `e(𝒫)`, averaged subspace defect `F_𝒫(W)` and
averaged λ-sparsity (equations (12)–(13)); the componentwise quotient family `q_G 𝒫` and the
convolution family `𝒫 * 𝒫` with components `P_i * P_j` and weights `a_i a_j`.

What this file does NOT prove: none of the inequalities (14), (15) or the posterior closure
Lemma 2.2; the only proofs are that the convolution weights sum to one and the definitional
identity `h(q_G 𝒫) = h(𝒫) - F_𝒫(G)`.
-/

namespace EntropyLean

open scoped BigOperators

/-- A finite weighted family of laws on `V`. -/
structure WeightedFamily (V : Type*) where
  index : Type
  [indexFintype : Fintype index]
  laws : index → PMF V
  weights : index → ℝ
  weights_pos : ∀ i, 0 < weights i
  weights_sum : ∑ i, weights i = 1

attribute [instance] WeightedFamily.indexFintype

namespace WeightedFamily

variable {V : Type*}

/-- Mean component entropy `h(𝒫) = ∑ a_i H(P_i)`. -/
noncomputable def meanEntropy (P : WeightedFamily V) : ℝ :=
  ∑ i, P.weights i * entropyBits (P.laws i)

/-- Mean interaction `e(𝒫) = ∑ a_i a_j s(P_i, P_j)`. -/
noncomputable def meanInteraction [Add V] (P : WeightedFamily V) : ℝ :=
  ∑ i, ∑ j, P.weights i * P.weights j * interaction (P.laws i) (P.laws j)

/-- Averaged subspace defect `F_𝒫(W) = ∑ a_i F_{P_i}(W)`. -/
noncomputable def averagedLoss [AddCommGroup V] [Module (ZMod 2) V]
    (P : WeightedFamily V) (W : Submodule (ZMod 2) V) : ℝ :=
  ∑ i, P.weights i * quotientLoss (P.laws i) W

/-- Averaged λ-sparsity (equation (13)). -/
def IsSparse [AddCommGroup V] [Module (ZMod 2) V] (lam : ℝ) (P : WeightedFamily V) : Prop :=
  ∀ W : Submodule (ZMod 2) V, P.averagedLoss W ≤ lam * (Module.finrank (ZMod 2) W : ℝ)

/-- The componentwise quotient family `q_G 𝒫`, with the same weights. -/
noncomputable def quotient [AddCommGroup V] [Module (ZMod 2) V]
    (P : WeightedFamily V) (G : Submodule (ZMod 2) V) : WeightedFamily (V ⧸ G) where
  index := P.index
  laws := fun i => (P.laws i).map fun v => G.mkQ v
  weights := P.weights
  weights_pos := P.weights_pos
  weights_sum := P.weights_sum

/-- `h(q_G 𝒫) = h(𝒫) - F_𝒫(G)` (equation (12)). -/
theorem meanEntropy_quotient [AddCommGroup V] [Module (ZMod 2) V]
    (P : WeightedFamily V) (G : Submodule (ZMod 2) V) :
    (P.quotient G).meanEntropy = P.meanEntropy - P.averagedLoss G := by
  show ∑ i, P.weights i * entropyBits ((P.laws i).map fun v => G.mkQ v) = _
  unfold meanEntropy averagedLoss quotientLoss
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Weights `a_i a_j` of the convolution family sum to one. -/
theorem conv_weights_sum (P : WeightedFamily V) :
    ∑ p : P.index × P.index, P.weights p.1 * P.weights p.2 = 1 := by
  have h := P.weights_sum
  calc ∑ p : P.index × P.index, P.weights p.1 * P.weights p.2
      = ∑ i, ∑ j, P.weights i * P.weights j := Fintype.sum_prod_type _
    _ = ∑ i, P.weights i * ∑ j, P.weights j := by simp only [Finset.mul_sum]
    _ = 1 := by
        rw [h]
        simp only [mul_one]
        exact h

/-- The convolution family `𝒫 * 𝒫`: components `P_i * P_j`, weights `a_i a_j`. -/
noncomputable def convFamily [Add V] (P : WeightedFamily V) : WeightedFamily V where
  index := P.index × P.index
  laws := fun p => conv (P.laws p.1) (P.laws p.2)
  weights := fun p => P.weights p.1 * P.weights p.2
  weights_pos := fun p => mul_pos (P.weights_pos p.1) (P.weights_pos p.2)
  weights_sum := P.conv_weights_sum

end WeightedFamily
end EntropyLean
