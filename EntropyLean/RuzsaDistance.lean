import Mathlib
import EntropyLean.TwoInput
import EntropyLean.CondInformation
import EntropyLean.QuotientFacts

/-!
# Entropic Ruzsa distance (roadmap item D6a, equation (8))

Preliminaries for Section 6 (Lemmas 6.1–6.3):

* the entropic Ruzsa distance `d(P, Q) = H(P * Q) − (H(P) + H(Q)) / 2` of equation (8)
  (`ruzsaDist`), with `d(P, P) = D(P)` (`ruzsaDist_self`), `d = (H(P) + H(Q)) / 2 − s(P, Q)`
  (`ruzsaDist_eq_sub_interaction`), symmetry (`ruzsaDist_comm`) and `d(P, Q) ≥ 0` on a finite
  group (`ruzsaDist_nonneg`);
* translation invariance: `P * (Q + c) = (P * Q) + c` (`conv_map_add_const`), hence
  `d(P, Q + c) = d(P, Q)` (`ruzsaDist_map_add_const`) and `d(P, P + c) = D(P)`
  (`ruzsaDist_translate_self`), the step "the law of `C = A + B` is a translate of the law of
  `A`" in the proof of Lemma 6.3;
* entropy submodularity `H(A, B, C) + H(C) ≤ H(A, C) + H(B, C)` (`entropyBits_submodular`), the
  inequality used in the proof of Lemma 6.2.

What this file does NOT prove: Lemma 6.1, Lemma 6.2 (no conditional laws or conditionally
independent couplings are built here) or Lemma 6.3.
-/

namespace EntropyLean

/-- Entropic Ruzsa distance `d(P, Q) = H(P * Q) − (H(P) + H(Q)) / 2` (equation (8)). -/
noncomputable def ruzsaDist {V : Type*} [Add V] (P Q : PMF V) : ℝ :=
  entropyBits (conv P Q) - (entropyBits P + entropyBits Q) / 2

/-- `d(P, P) = D(P)`. -/
theorem ruzsaDist_self {V : Type*} [Add V] (P : PMF V) :
    ruzsaDist P P = entropyIncrement P := by
  unfold ruzsaDist entropyIncrement
  ring

/-- `d(P, Q) = (H(P) + H(Q)) / 2 − s(P, Q)`. -/
theorem ruzsaDist_eq_sub_interaction {V : Type*} [Add V] (P Q : PMF V) :
    ruzsaDist P Q = (entropyBits P + entropyBits Q) / 2 - interaction P Q := by
  unfold ruzsaDist interaction
  ring

/-- `d(P, Q) = d(Q, P)`. -/
theorem ruzsaDist_comm {V : Type*} [AddCommMonoid V] (P Q : PMF V) :
    ruzsaDist P Q = ruzsaDist Q P := by
  unfold ruzsaDist
  rw [conv_comm_law P Q]
  ring

/-- `d(P, Q) ≥ 0` on a finite group, since `H(P * Q) ≥ max(H(P), H(Q))`. -/
theorem ruzsaDist_nonneg {V : Type*} [Fintype V] [AddGroup V] (P Q : PMF V) :
    0 ≤ ruzsaDist P Q := by
  have h1 := entropyBits_le_conv_left P Q
  have h2 := entropyBits_le_conv_right P Q
  unfold ruzsaDist
  linarith

/-- Translating the second factor translates the convolution: `P * (Q + c) = (P * Q) + c`. -/
theorem conv_map_add_const {V : Type*} [AddCommGroup V] (P Q : PMF V) (c : V) :
    conv P (Q.map fun b => b + c) = (conv P Q).map fun x => x + c := by
  unfold conv
  rw [PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext b
  exact (add_assoc a b c).symm

/-- Translation invariance of the Ruzsa distance: `d(P, Q + c) = d(P, Q)`. -/
theorem ruzsaDist_map_add_const {V : Type*} [AddCommGroup V] (P Q : PMF V) (c : V) :
    ruzsaDist P (Q.map fun b => b + c) = ruzsaDist P Q := by
  have hinj : Function.Injective fun x : V => x + c := add_left_injective c
  unfold ruzsaDist
  rw [conv_map_add_const, entropyBits_map_of_injective _ hinj,
    entropyBits_map_of_injective _ hinj]

/-- `d(P, P + c) = D(P)`: the Ruzsa distance of a law to a translate of itself is its
entropy increment (used in the proof of Lemma 6.3). -/
theorem ruzsaDist_translate_self {V : Type*} [AddCommGroup V] (P : PMF V) (c : V) :
    ruzsaDist P (P.map fun b => b + c) = entropyIncrement P := by
  rw [ruzsaDist_map_add_const, ruzsaDist_self]

/-- Entropy submodularity: `H(A, B, C) + H(C) ≤ H(A, C) + H(B, C)` for a law of `(A, B, C)`
on finite types, i.e. `I(A ; B | C) ≥ 0`. -/
theorem entropyBits_submodular {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : PMF (α × β × γ)) :
    entropyBits P + entropyBits (P.map tripleC) ≤
      entropyBits (P.map tripleAC) + entropyBits (P.map Prod.snd) := by
  have h := condMutualInfo_nonneg P
  unfold condMutualInfo at h
  linarith

end EntropyLean
