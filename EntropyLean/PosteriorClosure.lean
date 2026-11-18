import EntropyLean.MathlibForPFR
import EntropyLean.Posterior
import EntropyLean.CondInformation

/-!
# Lemma 2.2 (posterior closure), roadmap item D3c2

Second half of equation (17): for a weighted family `𝒫` on a finite `F₂`-space and any
`W ≤ V`, `F_{Post 𝒫}(W) ≤ F_𝒫(W)` (`WeightedFamily.averagedLoss_posterior_le`), hence
posterior formation preserves averaged λ-sparsity (`WeightedFamily.posterior_closure`).
Together with `WeightedFamily.meanEntropy_posterior` (D3b) this is Lemma 2.2
(`WeightedFamily.posterior_lemma`).

Proof, as in the paper: `I(A ; A + B | g A) ≥ 0` (`condMutualInfo_nonneg`) gives
`H(A, A + B) − H(g A, A + B) ≤ H(A) − H(g A)` (`joint_loss_le`); the disintegrations of D3c1
turn the left side into `∑ₜ (P * Q)(t) F_{Q_t}(W)` for `g = q_W`
(`sum_conv_mul_quotientLoss_posterior_le`), and averaging over the indices gives the result.

What this file does NOT prove: anything beyond Lemma 2.2 (Lemma 3.1 and later are open).
-/

namespace EntropyLean

open scoped BigOperators

/-- `H(A, T) − H(g A, T) ≤ H(A) − H(g A)` for a joint law of `(A, T)`, from
`I(A ; T | g A) ≥ 0`. -/
theorem joint_loss_le {α β T : Type*} [Fintype α] [Fintype β] [Fintype T] (g : α → β)
    (R : PMF (α × T)) :
    entropyBits R - entropyBits (R.map fun y => (g y.1, y.2)) ≤
      entropyBits (R.map Prod.fst) - entropyBits ((R.map Prod.fst).map g) := by
  have hc := condMutualInfo_nonneg (R.map fun y : α × T => (y.1, y.2, g y.1))
  unfold condMutualInfo at hc
  have hinj1 : Function.Injective (fun a : α => (a, g a)) := by
    intro a b h
    have h' : (a, g a) = (b, g b) := h
    exact (Prod.mk.inj h').1
  have hinj3 : Function.Injective (fun y : α × T => (y.1, y.2, g y.1)) := by
    intro x y h
    have h' : (x.1, x.2, g x.1) = (y.1, y.2, g y.1) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext h1 (Prod.mk.inj h2).1
  have e1 : entropyBits ((R.map fun y : α × T => (y.1, y.2, g y.1)).map tripleAC) =
      entropyBits (R.map Prod.fst) := by
    have h : (R.map fun y : α × T => (y.1, y.2, g y.1)).map tripleAC =
        (R.map Prod.fst).map (fun a : α => (a, g a)) := by
      rw [PMF.map_comp, PMF.map_comp]
      try rfl
    rw [h, entropyBits_map_of_injective _ hinj1]
  have e2 : entropyBits ((R.map fun y : α × T => (y.1, y.2, g y.1)).map Prod.snd) =
      entropyBits (R.map fun y => (g y.1, y.2)) := by
    have h : (R.map fun y : α × T => (y.1, y.2, g y.1)).map Prod.snd =
        (R.map fun y : α × T => (g y.1, y.2)).map Prod.swap := by
      rw [PMF.map_comp, PMF.map_comp]
      try rfl
    rw [h, entropyBits_map_swap]
  have e3 : entropyBits (R.map fun y : α × T => (y.1, y.2, g y.1)) = entropyBits R :=
    entropyBits_map_of_injective _ hinj3
  have e4 : entropyBits ((R.map fun y : α × T => (y.1, y.2, g y.1)).map tripleC) =
      entropyBits ((R.map Prod.fst).map g) := by
    have h : (R.map fun y : α × T => (y.1, y.2, g y.1)).map tripleC = (R.map Prod.fst).map g := by
      rw [PMF.map_comp, PMF.map_comp]
      try rfl
    rw [h]
  rw [e1, e2, e3, e4] at hc
  linarith

/-- Per pair of components: `∑ₜ (P * Q)(t) F_{Q_t}(W) ≤ F_P(W)`, i.e.
`H(A | A + B, q_W A) ≤ H(A | q_W A)`. -/
theorem sum_conv_mul_quotientLoss_posterior_le {V : Type*} [Fintype V] [AddCommGroup V]
    [Module (ZMod 2) V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    ∑ t, (conv P Q t).toReal * quotientLoss (posteriorLaw P Q t) W ≤ quotientLoss P W := by
  classical
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  have h1 := entropyBits_pair_sum P Q
  have h2 := entropyBits_map_pair_sum (fun v => W.mkQ v) P Q
  have h3 := joint_loss_le (fun v => W.mkQ v)
    ((prodLaw P Q).map fun x : V × V => (x.1, x.1 + x.2))
  have hfst : ((prodLaw P Q).map fun x : V × V => (x.1, x.1 + x.2)).map Prod.fst = P := by
    rw [PMF.map_comp]
    exact prodLaw_map_fst P Q
  rw [hfst] at h3
  have hsum : ∑ t, (conv P Q t).toReal * quotientLoss (posteriorLaw P Q t) W =
      ∑ t, (conv P Q t).toReal * entropyBits (posteriorLaw P Q t) -
        ∑ t, (conv P Q t).toReal * entropyBits ((posteriorLaw P Q t).map fun v => W.mkQ v) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold quotientLoss
    ring
  rw [hsum]
  unfold quotientLoss
  linarith

namespace WeightedFamily

open Classical in
/-- Second half of Lemma 2.2 (equation (17)): `F_{Post 𝒫}(W) ≤ F_𝒫(W)`. -/
theorem averagedLoss_posterior_le {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]
    (P : WeightedFamily V) (W : Submodule (ZMod 2) V) :
    P.posterior.averagedLoss W ≤ P.averagedLoss W := by
  have hij : ∀ i j, ∑ t, P.weights i * P.weights j * (conv (P.laws i) (P.laws j) t).toReal *
      quotientLoss (posteriorLaw (P.laws i) (P.laws j) t) W ≤
        P.weights i * P.weights j * quotientLoss (P.laws i) W := by
    intro i j
    have hle := sum_conv_mul_quotientLoss_posterior_le (P.laws i) (P.laws j) W
    have heq : ∑ t, P.weights i * P.weights j * (conv (P.laws i) (P.laws j) t).toReal *
        quotientLoss (posteriorLaw (P.laws i) (P.laws j) t) W =
          P.weights i * P.weights j * ∑ t, (conv (P.laws i) (P.laws j) t).toReal *
            quotientLoss (posteriorLaw (P.laws i) (P.laws j) t) W := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hle (mul_nonneg (P.weights_pos i).le (P.weights_pos j).le)
  have hrow : ∀ i, ∑ j, P.weights i * P.weights j * quotientLoss (P.laws i) W =
      P.weights i * quotientLoss (P.laws i) W := by
    intro i
    calc ∑ j, P.weights i * P.weights j * quotientLoss (P.laws i) W
        = P.weights i * quotientLoss (P.laws i) W * ∑ j, P.weights j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = P.weights i * quotientLoss (P.laws i) W := by rw [P.weights_sum, mul_one]
  have hall : ∑ x : P.index × P.index × V,
      P.postMass x * quotientLoss (posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2) W ≤
        P.averagedLoss W := by
    calc ∑ x : P.index × P.index × V,
        P.postMass x * quotientLoss (posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2) W
        = ∑ i, ∑ j, ∑ t, P.weights i * P.weights j * (conv (P.laws i) (P.laws j) t).toReal *
            quotientLoss (posteriorLaw (P.laws i) (P.laws j) t) W := by
          unfold postMass
          simp only [Fintype.sum_prod_type]
      _ ≤ ∑ i, ∑ j, P.weights i * P.weights j * quotientLoss (P.laws i) W :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = P.averagedLoss W := by
          unfold averagedLoss
          exact Finset.sum_congr rfl fun i _ => hrow i
  have hz : ∑ x : {x : P.index × P.index × V //
      ¬ conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
        P.postMass x.1 * quotientLoss (posteriorLaw (P.laws x.1.1) (P.laws x.1.2.1) x.1.2.2) W =
          0 :=
    Finset.sum_eq_zero fun x _ => by simp [postMass, not_not.mp x.2]
  have key : ∑ x : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
      P.postMass x.1 * quotientLoss (posteriorLaw (P.laws x.1.1) (P.laws x.1.2.1) x.1.2.2) W =
        ∑ x : P.index × P.index × V,
          P.postMass x * quotientLoss (posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2) W := by
    rw [← Fintype.sum_subtype_add_sum_subtype
      (fun x : P.index × P.index × V => conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0)
      (fun x => P.postMass x * quotientLoss (posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2) W),
      hz, add_zero]
  have h := key.trans_le hall
  exact h

/-- Posterior formation preserves averaged λ-sparsity. -/
theorem posterior_closure {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]
    (lam : ℝ) (P : WeightedFamily V) (h : P.IsSparse lam) : P.posterior.IsSparse lam :=
  fun W => (P.averagedLoss_posterior_le W).trans (h W)

/-- **Lemma 2.2** (posterior closure), equation (17): `h(Post 𝒫) = e(𝒫)` and
`F_{Post 𝒫}(W) ≤ F_𝒫(W)` for every `W ≤ V`. -/
theorem posterior_lemma {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]
    (P : WeightedFamily V) :
    P.posterior.meanEntropy = P.meanInteraction ∧
      ∀ W : Submodule (ZMod 2) V, P.posterior.averagedLoss W ≤ P.averagedLoss W :=
  ⟨P.meanEntropy_posterior, P.averagedLoss_posterior_le⟩

end WeightedFamily
end EntropyLean
