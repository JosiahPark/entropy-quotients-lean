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

Roadmap item D5b iterates the step over `N` fresh samples without product measures: for fixed `u`,
`Φ₀(S) = H(q_S Q_u)`, `Φ_{k+1}(S) = ∑_w b_w Φ_k(S ⊔ V(u, w))` (`densPhi`) and `D₀(S) = dim S`,
`D_{k+1}(S) = ∑_w b_w D_k(S ⊔ V(u, w))` (`densDim`); then `N A_u ≤ Φ₀(S) − Φ_N(S) + λ ∑_{k<N} D_k(S)`
(`densPhi_induction`), `D_k(S) ≤ dim S + k B_u` (`densDim_le`), and averaging over `u` gives
inequality (28) `A ≤ h/N + λ B (N − 1)/2` for `λ ≥ 0`, `N ≥ 1` (`averaged_density_estimate`), with
`A = ∑_u b_u ∑_w b_w s_{V(u,w)}(Q_u, Q_w)` and `B = ∑_u b_u ∑_w b_w dim V(u, w)`.

What this file does NOT prove: inequality (29) of Lemma 5.1 (later item D5c).
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

/-- `dim (S ⊔ W) ≤ dim S + dim W`. -/
theorem finrank_sup_le_add [Fintype V] (S W : Submodule (ZMod 2) V) :
    (Module.finrank (ZMod 2) ↥(S ⊔ W) : ℝ) ≤
      (Module.finrank (ZMod 2) S : ℝ) + (Module.finrank (ZMod 2) W : ℝ) := by
  have h : Module.finrank (ZMod 2) ↥(S ⊔ W) ≤
      Module.finrank (ZMod 2) S + Module.finrank (ZMod 2) W := by
    first
    | exact Submodule.finrank_add_le_finrank_add_finrank S W
    | (have h' := Submodule.finrank_sup_add_finrank_inf_eq S W; omega)
  exact_mod_cast h

/-- `(∑_{k<N} k) · 2 = N (N − 1)` in `ℝ`. -/
theorem sum_range_cast_mul_two (N : ℕ) :
    (∑ k ∈ Finset.range N, (k : ℝ)) * 2 = (N : ℝ) * ((N : ℝ) - 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast
    ring

namespace WeightedFamily

/-- Row average `A_u = ∑_w b_w s_{V(u,w)}(Q_u, Q_w)`. -/
noncomputable def rowInteraction (Q : WeightedFamily V) (u : Q.index)
    (Vf : Q.index → Submodule (ZMod 2) V) : ℝ :=
  ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf w)

/-- Expected entropy `E H(q_{S ⊔ V(u,w₁) ⊔ ⋯ ⊔ V(u,w_k)} Q_u)` over `k` fresh samples, by recursion. -/
noncomputable def densPhi (Q : WeightedFamily V) (u : Q.index)
    (Vf : Q.index → Submodule (ZMod 2) V) : ℕ → Submodule (ZMod 2) V → ℝ
  | 0, S => entropyBits ((Q.laws u).map fun v => S.mkQ v)
  | k + 1, S => ∑ w, Q.weights w * densPhi Q u Vf k (S ⊔ Vf w)

/-- Expected dimension `E dim (S ⊔ V(u,w₁) ⊔ ⋯ ⊔ V(u,w_k))`, by recursion. -/
noncomputable def densDim (Q : WeightedFamily V) (u : Q.index)
    (Vf : Q.index → Submodule (ZMod 2) V) : ℕ → Submodule (ZMod 2) V → ℝ
  | 0, S => (Module.finrank (ZMod 2) S : ℝ)
  | k + 1, S => ∑ w, Q.weights w * densDim Q u Vf k (S ⊔ Vf w)

theorem densPhi_zero (Q : WeightedFamily V) (u : Q.index) (Vf : Q.index → Submodule (ZMod 2) V)
    (S : Submodule (ZMod 2) V) :
    Q.densPhi u Vf 0 S = entropyBits ((Q.laws u).map fun v => S.mkQ v) := by
  first
  | rfl
  | simp only [densPhi]

theorem densPhi_succ (Q : WeightedFamily V) (u : Q.index) (Vf : Q.index → Submodule (ZMod 2) V)
    (k : ℕ) (S : Submodule (ZMod 2) V) :
    Q.densPhi u Vf (k + 1) S = ∑ w, Q.weights w * Q.densPhi u Vf k (S ⊔ Vf w) := by
  first
  | rfl
  | simp only [densPhi]

theorem densDim_zero (Q : WeightedFamily V) (u : Q.index) (Vf : Q.index → Submodule (ZMod 2) V)
    (S : Submodule (ZMod 2) V) :
    Q.densDim u Vf 0 S = (Module.finrank (ZMod 2) S : ℝ) := by
  first
  | rfl
  | simp only [densDim]

theorem densDim_succ (Q : WeightedFamily V) (u : Q.index) (Vf : Q.index → Submodule (ZMod 2) V)
    (k : ℕ) (S : Submodule (ZMod 2) V) :
    Q.densDim u Vf (k + 1) S = ∑ w, Q.weights w * Q.densDim u Vf k (S ⊔ Vf w) := by
  first
  | rfl
  | simp only [densDim]

theorem densPhi_nonneg (Q : WeightedFamily V) (u : Q.index)
    (Vf : Q.index → Submodule (ZMod 2) V) (k : ℕ) : ∀ S, 0 ≤ Q.densPhi u Vf k S := by
  induction k with
  | zero =>
    intro S
    rw [densPhi_zero]
    exact entropyBits_nonneg' _
  | succ k ih =>
    intro S
    rw [densPhi_succ]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (Q.weights_pos w).le (ih _)

/-- `D_k(S) ≤ dim S + k B_u` with `B_u = ∑_w b_w dim V(u, w)`. -/
theorem densDim_le [Fintype V] (Q : WeightedFamily V) (u : Q.index)
    (Vf : Q.index → Submodule (ZMod 2) V) (k : ℕ) :
    ∀ S, Q.densDim u Vf k S ≤ (Module.finrank (ZMod 2) S : ℝ) +
      (k : ℝ) * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf w) : ℝ) := by
  induction k with
  | zero =>
    intro S
    rw [densDim_zero]
    simp
  | succ k ih =>
    intro S
    rw [densDim_succ]
    have h : ∀ w, Q.weights w * Q.densDim u Vf k (S ⊔ Vf w) ≤
        Q.weights w * (Module.finrank (ZMod 2) S : ℝ) +
        Q.weights w * (Module.finrank (ZMod 2) (Vf w) : ℝ) +
        Q.weights w * ((k : ℝ) * ∑ w', Q.weights w' * (Module.finrank (ZMod 2) (Vf w') : ℝ)) := by
      intro w
      have h1 := ih (S ⊔ Vf w)
      have h2 := finrank_sup_le_add S (Vf w)
      have h3 : Q.densDim u Vf k (S ⊔ Vf w) ≤ (Module.finrank (ZMod 2) S : ℝ) +
          (Module.finrank (ZMod 2) (Vf w) : ℝ) +
          (k : ℝ) * ∑ w', Q.weights w' * (Module.finrank (ZMod 2) (Vf w') : ℝ) := by
        linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (Q.weights_pos w).le
      rw [mul_add, mul_add] at h4
      linarith
    have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => h w
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      Q.weights_sum] at hsum
    push_cast
    linarith

/-- `N A_u ≤ Φ₀(S) − Φ_N(S) + λ ∑_{k<N} D_k(S)`, by induction on `N` from
`averaged_density_step`. -/
theorem densPhi_induction [Fintype V] {lam : ℝ} (Q : WeightedFamily V) (hsp : Q.IsSparse lam)
    (u : Q.index) (Vf : Q.index → Submodule (ZMod 2) V) (N : ℕ) :
    ∀ S, (N : ℝ) * Q.rowInteraction u Vf ≤ Q.densPhi u Vf 0 S - Q.densPhi u Vf N S +
      lam * ∑ k ∈ Finset.range N, Q.densDim u Vf k S := by
  induction N with
  | zero =>
    intro S
    simp
  | succ N ih =>
    intro S
    have hstep := Q.averaged_density_step hsp u Vf S
    have hw : ∀ w, Q.weights w * ((N : ℝ) * Q.rowInteraction u Vf) ≤
        Q.weights w * (Q.densPhi u Vf 0 (S ⊔ Vf w) - Q.densPhi u Vf N (S ⊔ Vf w) +
          lam * ∑ k ∈ Finset.range N, Q.densDim u Vf k (S ⊔ Vf w)) :=
      fun w => mul_le_mul_of_nonneg_left (ih (S ⊔ Vf w)) (Q.weights_pos w).le
    have hsum := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hw w
    have e1 : ∑ w, Q.weights w * ((N : ℝ) * Q.rowInteraction u Vf) =
        (N : ℝ) * Q.rowInteraction u Vf := by
      rw [← Finset.sum_mul, Q.weights_sum, one_mul]
    have e2 : ∑ w, Q.weights w * (Q.densPhi u Vf 0 (S ⊔ Vf w) - Q.densPhi u Vf N (S ⊔ Vf w) +
          lam * ∑ k ∈ Finset.range N, Q.densDim u Vf k (S ⊔ Vf w)) =
        ∑ w, Q.weights w * Q.densPhi u Vf 0 (S ⊔ Vf w) -
          ∑ w, Q.weights w * Q.densPhi u Vf N (S ⊔ Vf w) +
          lam * ∑ w, Q.weights w * ∑ k ∈ Finset.range N, Q.densDim u Vf k (S ⊔ Vf w) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring
    have e3 : ∑ w, Q.weights w * Q.densPhi u Vf N (S ⊔ Vf w) = Q.densPhi u Vf (N + 1) S :=
      (Q.densPhi_succ u Vf N S).symm
    have e4 : ∑ w, Q.weights w * ∑ k ∈ Finset.range N, Q.densDim u Vf k (S ⊔ Vf w) =
        ∑ k ∈ Finset.range N, Q.densDim u Vf (k + 1) S := by
      calc ∑ w, Q.weights w * ∑ k ∈ Finset.range N, Q.densDim u Vf k (S ⊔ Vf w)
          = ∑ w, ∑ k ∈ Finset.range N, Q.weights w * Q.densDim u Vf k (S ⊔ Vf w) :=
            Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
        _ = ∑ k ∈ Finset.range N, ∑ w, Q.weights w * Q.densDim u Vf k (S ⊔ Vf w) :=
            Finset.sum_comm
        _ = ∑ k ∈ Finset.range N, Q.densDim u Vf (k + 1) S :=
            Finset.sum_congr rfl fun k _ => (Q.densDim_succ u Vf k S).symm
    have e5 : ∑ k ∈ Finset.range (N + 1), Q.densDim u Vf k S =
        ∑ k ∈ Finset.range N, Q.densDim u Vf (k + 1) S + Q.densDim u Vf 0 S :=
      Finset.sum_range_succ' _ _
    have e6 : Q.densDim u Vf 0 S = (Module.finrank (ZMod 2) S : ℝ) := Q.densDim_zero u Vf S
    have e7 : Q.densPhi u Vf 0 S = entropyBits ((Q.laws u).map fun v => S.mkQ v) :=
      Q.densPhi_zero u Vf S
    have e8 : ∑ w, Q.weights w * Q.densPhi u Vf 0 (S ⊔ Vf w) =
        ∑ w, Q.weights w * entropyBits ((Q.laws u).map fun v => (S ⊔ Vf w).mkQ v) :=
      Finset.sum_congr rfl fun w _ => by rw [Q.densPhi_zero u Vf (S ⊔ Vf w)]
    have e9 : Q.rowInteraction u Vf =
        ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf w) := rfl
    rw [e1, e2, e3, e4] at hsum
    rw [e5, e6]
    push_cast
    linarith [hsum, hstep, e7, e8, e9]

/-- Lemma 5.1, inequality (28): for a `λ`-sparse family (`λ ≥ 0`), subspaces `V(u, w)` and `N ≥ 1`,
`A ≤ h/N + λ B (N − 1)/2` with `A = E_{u,w} s_{V(u,w)}(Q_u, Q_w)` and `B = E_{u,w} dim V(u, w)`. -/
theorem averaged_density_estimate [Fintype V] {lam : ℝ} (Q : WeightedFamily V)
    (hsp : Q.IsSparse lam) (hlam : 0 ≤ lam) (Vf : Q.index → Q.index → Submodule (ZMod 2) V)
    (N : ℕ) (hN : 0 < N) :
    ∑ u, Q.weights u * ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf u w) ≤
      Q.meanEntropy / N +
        lam * (∑ u, Q.weights u * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ)) *
          ((N : ℝ) - 1) / 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : (Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) : ℝ) = 0 := by simp
  have hc := sum_range_cast_mul_two N
  have hu : ∀ u, (N : ℝ) * Q.rowInteraction u (Vf u) ≤ entropyBits (Q.laws u) +
      lam * ((∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ)) *
        ((N : ℝ) * ((N : ℝ) - 1) / 2)) := by
    intro u
    have h1 := Q.densPhi_induction hsp u (Vf u) N ⊥
    have h2 := Q.densPhi_nonneg u (Vf u) N ⊥
    have h3 : Q.densPhi u (Vf u) 0 ⊥ = entropyBits (Q.laws u) := by
      have h := quotientLoss_bot (Q.laws u)
      unfold quotientLoss at h
      rw [Q.densPhi_zero u (Vf u) ⊥]
      linarith
    have h4 : ∑ k ∈ Finset.range N, Q.densDim u (Vf u) k ⊥ ≤
        (∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ)) *
          ((N : ℝ) * ((N : ℝ) - 1) / 2) := by
      have hk : ∀ k ∈ Finset.range N, Q.densDim u (Vf u) k ⊥ ≤
          (k : ℝ) * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ) := by
        intro k _
        have h := Q.densDim_le u (Vf u) k ⊥
        linarith
      have hs := Finset.sum_le_sum hk
      rw [← Finset.sum_mul] at hs
      have hc' : ∑ k ∈ Finset.range N, (k : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by linarith
      rw [hc'] at hs
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hlam
    linarith
  have hsum := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hu u) (Q.weights_pos u).le
  have e1 : ∑ u, Q.weights u * ((N : ℝ) * Q.rowInteraction u (Vf u)) =
      (N : ℝ) * ∑ u, Q.weights u * ∑ w, Q.weights w *
        subspaceInteraction (Q.laws u) (Q.laws w) (Vf u w) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold rowInteraction
    ring
  have e2 : ∑ u, Q.weights u * (entropyBits (Q.laws u) +
      lam * ((∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ)) *
        ((N : ℝ) * ((N : ℝ) - 1) / 2))) =
      Q.meanEntropy + lam * (∑ u, Q.weights u * ∑ w, Q.weights w *
        (Module.finrank (ZMod 2) (Vf u w) : ℝ)) * ((N : ℝ) * ((N : ℝ) - 1) / 2) := by
    unfold meanEntropy
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [e1, e2] at hsum
  have key : (N : ℝ) * (Q.meanEntropy / N + lam * (∑ u, Q.weights u * ∑ w, Q.weights w *
      (Module.finrank (ZMod 2) (Vf u w) : ℝ)) * ((N : ℝ) - 1) / 2) =
      Q.meanEntropy + lam * (∑ u, Q.weights u * ∑ w, Q.weights w *
        (Module.finrank (ZMod 2) (Vf u w) : ℝ)) * ((N : ℝ) * ((N : ℝ) - 1) / 2) := by
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNr
    first
    | (field_simp; ring)
    | field_simp
  refine le_of_mul_le_mul_left ?_ hNr
  rw [key]
  exact hsum

end WeightedFamily

end EntropyLean
