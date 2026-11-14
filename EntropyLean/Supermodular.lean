import Mathlib
import EntropyLean.CondInformation
import EntropyLean.QuotientFacts

/-!
# Lemma 2.1: supermodularity of the subspace defect (roadmap item B6)

For a law `P` on a space `V` over `F₂` with finite quotients (we assume `Finite V`) and
subspaces `U, W ≤ V`, equation (11) of arXiv:2610.38525:
`H(q_{U ⊓ W} P) + H(q_{U ⊔ W} P) ≤ H(q_U P) + H(q_W P)` (`quotient_entropy_supermodular`).

Proof, as in the paper: apply `I(B₁ ; B₂ | C) ≥ 0` (`condMutualInfo_nonneg`) to
`B₁ = q_U A`, `B₂ = q_W A`, `C = q_{U ⊔ W} A`. The triple `(B₁, B₂, C)` has the same fibres as
`q_{U ⊓ W}`, and each pair `(B_k, C)` has the same fibres as `B_k`, so every joint entropy is an
entropy of a quotient (`entropyBits_map_eq_of_fibres`).

Consequences: `quotientLoss_supermodular` (`F_P` is supermodular) and its averaged form
`WeightedFamily.averagedLoss_supermodular`.

What this file does NOT prove: any statement for laws with infinite support on infinite
quotients, Lemma 2.2 (posterior closure), or Lemma 3.1.
-/

namespace EntropyLean

section Supermodular

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Two points have the same image in `V ⧸ S` iff their difference lies in `S`. -/
theorem quot_mkQ_eq_iff (S : Submodule (ZMod 2) V) (a b : V) :
    S.mkQ a = S.mkQ b ↔ a - b ∈ S := by
  first
  | exact Submodule.Quotient.eq S
  | exact Submodule.Quotient.eq
  | simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]

/-- The triple `(q_U v, q_W v, q_{U ⊔ W} v)`. -/
noncomputable def quotTriple (U W : Submodule (ZMod 2) V) (v : V) :
    (V ⧸ U) × (V ⧸ W) × (V ⧸ (U ⊔ W)) :=
  (U.mkQ v, W.mkQ v, (U ⊔ W).mkQ v)

/-- The triple map has the same fibres as `q_{U ⊓ W}`. -/
theorem quotTriple_fibres (U W : Submodule (ZMod 2) V) (a b : V) :
    (U ⊓ W).mkQ a = (U ⊓ W).mkQ b ↔ quotTriple U W a = quotTriple U W b := by
  constructor
  · intro h
    obtain ⟨hU, hW⟩ := Submodule.mem_inf.mp ((quot_mkQ_eq_iff (U ⊓ W) a b).mp h)
    have h1 : U.mkQ a = U.mkQ b := (quot_mkQ_eq_iff U a b).mpr hU
    have h2 : W.mkQ a = W.mkQ b := (quot_mkQ_eq_iff W a b).mpr hW
    have h3 : (U ⊔ W).mkQ a = (U ⊔ W).mkQ b :=
      (quot_mkQ_eq_iff (U ⊔ W) a b).mpr (Submodule.mem_sup_left hU)
    show (U.mkQ a, W.mkQ a, (U ⊔ W).mkQ a) = (U.mkQ b, W.mkQ b, (U ⊔ W).mkQ b)
    rw [h1, h2, h3]
  · intro h
    have h' : (U.mkQ a, W.mkQ a, (U ⊔ W).mkQ a) = (U.mkQ b, W.mkQ b, (U ⊔ W).mkQ b) := h
    have h1 : U.mkQ a = U.mkQ b := congrArg Prod.fst h'
    have h2 : W.mkQ a = W.mkQ b :=
      congrArg (fun z : (V ⧸ U) × (V ⧸ W) × (V ⧸ (U ⊔ W)) => z.2.1) h'
    exact (quot_mkQ_eq_iff (U ⊓ W) a b).mpr (Submodule.mem_inf.mpr
      ⟨(quot_mkQ_eq_iff U a b).mp h1, (quot_mkQ_eq_iff W a b).mp h2⟩)

/-- The pair `(q_U v, q_{U ⊔ W} v)` has the same fibres as `q_U`. -/
theorem quotTriple_AC_fibres (U W : Submodule (ZMod 2) V) (a b : V) :
    U.mkQ a = U.mkQ b ↔ (tripleAC ∘ quotTriple U W) a = (tripleAC ∘ quotTriple U W) b := by
  constructor
  · intro h
    have h3 : (U ⊔ W).mkQ a = (U ⊔ W).mkQ b :=
      (quot_mkQ_eq_iff (U ⊔ W) a b).mpr
        (Submodule.mem_sup_left ((quot_mkQ_eq_iff U a b).mp h))
    show (U.mkQ a, (U ⊔ W).mkQ a) = (U.mkQ b, (U ⊔ W).mkQ b)
    rw [h, h3]
  · intro h
    have h' : (U.mkQ a, (U ⊔ W).mkQ a) = (U.mkQ b, (U ⊔ W).mkQ b) := h
    exact congrArg Prod.fst h'

/-- The pair `(q_W v, q_{U ⊔ W} v)` has the same fibres as `q_W`. -/
theorem quotTriple_BC_fibres (U W : Submodule (ZMod 2) V) (a b : V) :
    W.mkQ a = W.mkQ b ↔ (Prod.snd ∘ quotTriple U W) a = (Prod.snd ∘ quotTriple U W) b := by
  constructor
  · intro h
    have h3 : (U ⊔ W).mkQ a = (U ⊔ W).mkQ b :=
      (quot_mkQ_eq_iff (U ⊔ W) a b).mpr
        (Submodule.mem_sup_right ((quot_mkQ_eq_iff W a b).mp h))
    show (W.mkQ a, (U ⊔ W).mkQ a) = (W.mkQ b, (U ⊔ W).mkQ b)
    rw [h, h3]
  · intro h
    have h' : (W.mkQ a, (U ⊔ W).mkQ a) = (W.mkQ b, (U ⊔ W).mkQ b) := h
    exact congrArg Prod.fst h'

/-- Lemma 2.1, equation (11): `H(q_{U ⊓ W} P) + H(q_{U ⊔ W} P) ≤ H(q_U P) + H(q_W P)`. -/
theorem quotient_entropy_supermodular [Finite V] (P : PMF V) (U W : Submodule (ZMod 2) V) :
    entropyBits (P.map fun v => (U ⊓ W).mkQ v) + entropyBits (P.map fun v => (U ⊔ W).mkQ v) ≤
      entropyBits (P.map fun v => U.mkQ v) + entropyBits (P.map fun v => W.mkQ v) := by
  haveI : Finite (V ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  haveI : Finite (V ⧸ (U ⊔ W)) := Finite.of_surjective _ (Submodule.mkQ_surjective (U ⊔ W))
  letI : Fintype (V ⧸ U) := Fintype.ofFinite _
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  letI : Fintype (V ⧸ (U ⊔ W)) := Fintype.ofFinite _
  have hc := condMutualInfo_nonneg (P.map (quotTriple U W))
  unfold condMutualInfo at hc
  have e1 : entropyBits ((P.map (quotTriple U W)).map tripleAC) =
      entropyBits (P.map fun v => U.mkQ v) := by
    rw [PMF.map_comp]
    exact entropyBits_map_eq_of_fibres P (Submodule.mkQ_surjective U) (quotTriple_AC_fibres U W)
  have e2 : entropyBits ((P.map (quotTriple U W)).map Prod.snd) =
      entropyBits (P.map fun v => W.mkQ v) := by
    rw [PMF.map_comp]
    exact entropyBits_map_eq_of_fibres P (Submodule.mkQ_surjective W) (quotTriple_BC_fibres U W)
  have e3 : entropyBits (P.map (quotTriple U W)) = entropyBits (P.map fun v => (U ⊓ W).mkQ v) :=
    entropyBits_map_eq_of_fibres P (Submodule.mkQ_surjective (U ⊓ W)) (quotTriple_fibres U W)
  have e4 : entropyBits ((P.map (quotTriple U W)).map tripleC) =
      entropyBits (P.map fun v => (U ⊔ W).mkQ v) := by
    exact congrArg entropyBits (PMF.map_comp _ _ _)
  rw [e1, e2, e4, e3] at hc
  linarith

/-- `F_P` is supermodular: `F_P(U) + F_P(W) ≤ F_P(U ⊔ W) + F_P(U ⊓ W)`. -/
theorem quotientLoss_supermodular [Finite V] (P : PMF V) (U W : Submodule (ZMod 2) V) :
    quotientLoss P U + quotientLoss P W ≤ quotientLoss P (U ⊔ W) + quotientLoss P (U ⊓ W) := by
  have h := quotient_entropy_supermodular P U W
  unfold quotientLoss
  linarith

/-- The averaged defect `F_𝒫` is supermodular. -/
theorem WeightedFamily.averagedLoss_supermodular [Finite V] (P : WeightedFamily V)
    (U W : Submodule (ZMod 2) V) :
    P.averagedLoss U + P.averagedLoss W ≤ P.averagedLoss (U ⊔ W) + P.averagedLoss (U ⊓ W) := by
  unfold WeightedFamily.averagedLoss
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (quotientLoss_supermodular (P.laws i) U W)
    (P.weights_pos i).le

end Supermodular

end EntropyLean
