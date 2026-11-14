import Mathlib
import EntropyLean.Fibring
import EntropyLean.Supermodular

/-!
# Averaged density estimate, first step (roadmap item D5a, Lemma 5.1)

The one-step inequality behind Lemma 5.1 of arXiv:2610.38525:

* `quotientLoss_mono`: `F_P(U) ≤ F_P(W)` for `U ≤ W`;
* `subspaceInteraction_step` (equation (30)): for subspaces `S`, `W`,
  `s_W(P, Q) ≤ F_Q(S) + (H(q_S P) − H(q_{S ⊔ W} P))`, from the nested inequality (22) with
  `U = S ⊓ W`, monotonicity of `F_Q` and the supermodularity (11);
* `WeightedFamily.averaged_density_step`: for a `λ`-sparse family `𝒬`, a fixed index `u`, subspaces
  `V(u, w)` and a subspace `S` not depending on the fresh index `w`,
  `∑_w b_w s_{V(u,w)}(Q_u, Q_w) ≤ λ dim S + H(q_S Q_u) − ∑_w b_w H(q_{S ⊔ V(u,w)} Q_u)`.

What this file does NOT prove: the iteration over `N` samples and the bounds (28), (29) of
Lemma 5.1 (later items D5b, D5c).
-/

namespace EntropyLean

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Monotonicity of the subspace defect: `F_P(U) ≤ F_P(W)` for `U ≤ W`. -/
theorem quotientLoss_mono [Fintype V] (P : PMF V) {U W : Submodule (ZMod 2) V} (hUW : U ≤ W) :
    quotientLoss P U ≤ quotientLoss P W := by
  haveI : Finite (V ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  letI : Fintype (V ⧸ U) := Fintype.ofFinite _
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  have h' : U ≤ LinearMap.ker W.mkQ := by
    rw [Submodule.ker_mkQ]
    exact hUW
  have hmap : (P.map fun v => W.mkQ v) = (P.map fun v => U.mkQ v).map (U.liftQ W.mkQ h') := by
    rw [PMF.map_comp]
    try rfl
  have hle := entropyBits_map_le (P.map fun v => U.mkQ v) (U.liftQ W.mkQ h')
  rw [← hmap] at hle
  unfold quotientLoss
  linarith

/-- Equation (30): `s_W(P, Q) ≤ F_Q(S) + (H(q_S P) − H(q_{S ⊔ W} P))`. -/
theorem subspaceInteraction_step [Fintype V] (P Q : PMF V) (S W : Submodule (ZMod 2) V) :
    subspaceInteraction P Q W ≤ quotientLoss Q S +
      (entropyBits (P.map fun v => S.mkQ v) - entropyBits (P.map fun v => (S ⊔ W).mkQ v)) := by
  have h1 := subspaceInteraction_nested P Q (inf_le_right : S ⊓ W ≤ W)
  have h2 := quotientLoss_mono Q (inf_le_left : S ⊓ W ≤ S)
  have h3 := quotient_entropy_supermodular P S W
  linarith

/-- One averaged step of the proof of Lemma 5.1: the subspace `S` does not depend on the fresh
index `w`, so averaged `λ`-sparsity applies to `∑_w b_w F_{Q_w}(S)`. -/
theorem WeightedFamily.averaged_density_step [Fintype V] {lam : ℝ} (Q : WeightedFamily V)
    (hsp : Q.IsSparse lam) (u : Q.index) (Vf : Q.index → Submodule (ZMod 2) V)
    (S : Submodule (ZMod 2) V) :
    ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf w) ≤
      lam * (Module.finrank (ZMod 2) S : ℝ) + (entropyBits ((Q.laws u).map fun v => S.mkQ v) -
        ∑ w, Q.weights w * entropyBits ((Q.laws u).map fun v => (S ⊔ Vf w).mkQ v)) := by
  have h : ∀ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf w) ≤
      Q.weights w * quotientLoss (Q.laws w) S +
        Q.weights w * entropyBits ((Q.laws u).map fun v => S.mkQ v) -
        Q.weights w * entropyBits ((Q.laws u).map fun v => (S ⊔ Vf w).mkQ v) := by
    intro w
    have hs := subspaceInteraction_step (Q.laws u) (Q.laws w) S (Vf w)
    have hm := mul_le_mul_of_nonneg_left hs (Q.weights_pos w).le
    rw [mul_add, mul_sub] at hm
    linarith
  have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => h w
  have e : ∑ w, (Q.weights w * quotientLoss (Q.laws w) S +
        Q.weights w * entropyBits ((Q.laws u).map fun v => S.mkQ v) -
        Q.weights w * entropyBits ((Q.laws u).map fun v => (S ⊔ Vf w).mkQ v)) =
      ∑ w, Q.weights w * quotientLoss (Q.laws w) S +
        entropyBits ((Q.laws u).map fun v => S.mkQ v) -
        ∑ w, Q.weights w * entropyBits ((Q.laws u).map fun v => (S ⊔ Vf w).mkQ v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, Q.weights_sum, one_mul]
  have hS : ∑ w, Q.weights w * quotientLoss (Q.laws w) S ≤
      lam * (Module.finrank (ZMod 2) S : ℝ) := hsp S
  linarith

end EntropyLean
