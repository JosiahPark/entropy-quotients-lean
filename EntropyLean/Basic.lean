import Mathlib

/-!
# Core entropy definitions

Shannon entropy in bits, convolution of laws, the entropy increment `D` and defect `E` of
arXiv:2610.38525 (equation (1)), the subspace defect `F_P(W) = H(P) - H(q_W P)` (equation (10)),
and λ-sparsity of a single law (equation (6)).

Entropy is written as a `tsum`, so it is defined for laws on any type (in particular on the
quotients `V ⧸ W`, without needing a `Fintype` instance there); on a finite type it agrees with
the finite sum (`entropyBits_eq_sum`).

What this file does NOT prove: no entropy inequality (nonnegativity, data processing,
Lemma 2.1) is proved here.
-/

namespace EntropyLean

open scoped BigOperators

/-- Finite-dimensional vector space over F₂. -/
abbrev F2Vec (m : ℕ) := Fin m → ZMod 2

/-- Shannon entropy in bits, `H(P) = -∑ p(a) log₂ p(a)`, with `0 log 0 = 0`
(Mathlib's `Real.logb 2 0 = 0`). -/
noncomputable def entropyBits {α : Type*} (P : PMF α) : ℝ :=
  ∑' a, -(P a).toReal * Real.logb 2 (P a).toReal

/-- On a finite type the entropy is the usual finite sum. -/
theorem entropyBits_eq_sum {α : Type*} [Fintype α] (P : PMF α) :
    entropyBits P = ∑ a, -(P a).toReal * Real.logb 2 (P a).toReal := by
  unfold entropyBits
  exact tsum_fintype _

/-- Law of `A + B` for independent `A ∼ P`, `B ∼ Q`. -/
noncomputable def conv {V : Type*} [Add V] (P Q : PMF V) : PMF V :=
  P.bind fun a => Q.map fun b => a + b

/-- Entropy increment `D(X) = H(X + X') - H(X)`. -/
noncomputable def entropyIncrement {V : Type*} [Add V] (P : PMF V) : ℝ :=
  entropyBits (conv P P) - entropyBits P

/-- Entropy defect `E(X) = 2H(X) - H(X + X')`. -/
noncomputable def entropyDefect {V : Type*} [Add V] (P : PMF V) : ℝ :=
  2 * entropyBits P - entropyBits (conv P P)

/-- `E(X) = H(X) - D(X)` (equation (1)). -/
theorem entropyDefect_eq {V : Type*} [Add V] (P : PMF V) :
    entropyDefect P = entropyBits P - entropyIncrement P := by
  unfold entropyDefect entropyIncrement
  ring

/-- Interaction `s(P, Q) = H(P) + H(Q) - H(P * Q)` (equation (8)). -/
noncomputable def interaction {V : Type*} [Add V] (P Q : PMF V) : ℝ :=
  entropyBits P + entropyBits Q - entropyBits (conv P Q)

/-- `s(P, P) = E(P)`. -/
theorem interaction_self {V : Type*} [Add V] (P : PMF V) :
    interaction P P = entropyDefect P := by
  unfold interaction entropyDefect
  ring

/-- Subspace defect `F_P(W) = H(P) - H(q_W P)` (equation (10)); for `A ∼ P` this is
`H(A | q_W A)`. -/
noncomputable def quotientLoss {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (P : PMF V) (W : Submodule (ZMod 2) V) : ℝ :=
  entropyBits P - entropyBits (P.map fun v => W.mkQ v)

/-- λ-sparsity of a single law (equation (6)): `H(Z | q_W Z) ≤ λ dim W` for every `W`. -/
def IsSparse {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (lam : ℝ) (P : PMF V) : Prop :=
  ∀ W : Submodule (ZMod 2) V, quotientLoss P W ≤ lam * (Module.finrank (ZMod 2) W : ℝ)

end EntropyLean
