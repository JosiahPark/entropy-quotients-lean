import Mathlib

/-! Core entropy definitions for finite probability mass functions. -/

namespace EntropyLean

open scoped BigOperators

/-- Finite-dimensional vector space over F₂. -/
abbrev F2Vec (m : ℕ) := Fin m → ZMod 2

/-- Shannon entropy in bits; the zero-mass convention is provided by `Real.log 0 = 0`. -/
noncomputable def entropyBits {α : Type*} [Fintype α] (P : PMF α) : ℝ :=
  ∑ a, - (P a).toReal * Real.logb 2 (P a).toReal

/-- Entropy increase under addition of two independent, identically distributed samples. -/
noncomputable def entropyIncrement {V : Type*} [AddCommMonoid V] [Fintype V]
    (P : PMF V) : ℝ :=
  entropyBits (P.convolve P) - entropyBits P

/-- Complementary entropy defect, `H(X) - entropyIncrement(X)`. -/
noncomputable def entropyDefect {V : Type*} [AddCommMonoid V] [Fintype V]
    (P : PMF V) : ℝ :=
  2 * entropyBits P - entropyBits (P.convolve P)

/-- Quotient entropy loss associated with a subspace. -/
noncomputable def quotientLoss {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (P : PMF V) (W : Submodule (ZMod 2) V) : ℝ :=
  entropyBits P - entropyBits (P.map (Submodule.mkQ W))

/-- Sparsity of a single law against every linear quotient. -/
def IsSparse {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (λ : ℝ) (P : PMF V) : Prop :=
  ∀ W : Submodule (ZMod 2) V,
    quotientLoss P W ≤ λ * (Module.finrank (ZMod 2) W : ℝ)

end EntropyLean
