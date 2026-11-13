import EntropyLean.Basic

/-! Finite weighted families, their interactions, and averaged sparsity. -/

namespace EntropyLean

open scoped BigOperators

structure WeightedFamily (V : Type*) [Fintype V] where
  index : Type*
  [indexFintype : Fintype index]
  laws : index → PMF V
  weights : index → ℝ
  weights_pos : ∀ i, 0 < weights i
  weights_sum : ∑ i, weights i = 1

attribute [instance] WeightedFamily.indexFintype

namespace WeightedFamily

variable {V : Type*} [Fintype V]

noncomputable def meanEntropy (P : WeightedFamily V) : ℝ :=
  ∑ i, P.weights i * entropyBits (P.laws i)

noncomputable def meanInteraction [AddCommMonoid V] (P : WeightedFamily V) : ℝ :=
  ∑ i, ∑ j, P.weights i * P.weights j *
    (entropyBits (P.laws i) + entropyBits (P.laws j) -
      entropyBits ((P.laws i).convolve (P.laws j)))

noncomputable def averagedLoss [AddCommGroup V] [Module (ZMod 2) V]
    (P : WeightedFamily V) (W : Submodule (ZMod 2) V) : ℝ :=
  ∑ i, P.weights i * quotientLoss (P.laws i) W

def IsSparse [AddCommGroup V] [Module (ZMod 2) V]
    (λ : ℝ) (P : WeightedFamily V) : Prop :=
  ∀ W : Submodule (ZMod 2) V,
    P.averagedLoss W ≤ λ * (Module.finrank (ZMod 2) W : ℝ)

end WeightedFamily
end EntropyLean
