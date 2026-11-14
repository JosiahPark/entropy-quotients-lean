import Mathlib
import EntropyLean.Families
import EntropyLean.Interaction

/-!
# Posterior families (Section 2.3), roadmap item D3a

For independent `A ∼ P`, `B ∼ Q` on a finite abelian group, the masses of `A + B` are
`(P * Q)(t) = ∑ₐ P(a) Q(t - a)` (`conv_apply`), and the posterior law of `A` given `A + B = t` is
`a ↦ P(a) Q(t - a) / (P * Q)(t)` (`posteriorLaw`, `posteriorLaw_apply`, `posteriorLaw_toReal`).

For a weighted family `𝒫 = (P_i, a_i)` the posterior family `Post(𝒫)` (equation (16)) has the
components `Q_{i,j,t} = Law(A | I = i, J = j, A + B = t)` with weights `a_i a_j (P_i * P_j)(t)`,
indexed by the triples with `(P_i * P_j)(t) ≠ 0` (`postMass`, `postMass_sum`,
`WeightedFamily.posterior`). The index type of a `WeightedFamily` lives in `Type`, so the
posterior family is built for `V : Type`.

Roadmap item D3b proves the first half of Lemma 2.2 (equation (17)):
`∑ₜ (P * Q)(t) H(Law(A | A + B = t)) = s(P, Q)` (`sum_conv_mul_entropy_posterior`), hence
`h(Post 𝒫) = e(𝒫)` (`WeightedFamily.meanEntropy_posterior`).

Roadmap item D3c1 adds the disintegration of the joint law of `(A, A + B)` along `A + B`: a joint
law with masses `R(a, t) = c(t) K_t(a)` has `H(R) = H(c) + ∑ₜ c(t) H(K_t)`
(`entropyBits_of_kernel`), images `(a, t) ↦ (g a, t)` keep this form (`kernel_masses_map`), and
`H(A, A + B) = H(A + B) + ∑ₜ (P * Q)(t) H(Q_t)` and
`H(g A, A + B) = H(A + B) + ∑ₜ (P * Q)(t) H(g_* Q_t)` for the posterior laws `Q_t`
(`entropyBits_pair_sum`, `entropyBits_map_pair_sum`).

What this file does NOT prove: the second half of Lemma 2.2, `F_{Post 𝒫}(W) ≤ F_𝒫(W)`, nor
`posterior_closure` (roadmap item D3c2).
-/

namespace EntropyLean

open scoped BigOperators

/-- Masses of the law of `A + B`: `(P * Q)(t) = ∑ₐ P(a) Q(t - a)`. -/
theorem conv_apply {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) (t : V) :
    conv P Q t = ∑ a, P a * Q (t - a) := by
  classical
  unfold conv
  simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Finset.sum_eq_single (t - a)]
  · rw [if_pos (show t = a + (t - a) by abel)]
  · intro b _ hb
    have hne : ¬ t = a + b := by
      intro h
      apply hb
      rw [h]
      abel
    rw [if_neg hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Posterior law of `A` given `A + B = t`, for independent `A ∼ P`, `B ∼ Q`. When
`(P * Q)(t) = 0` it is set to `P` (such `t` never index a posterior component). -/
noncomputable def posteriorLaw {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) (t : V) :
    PMF V :=
  if h : conv P Q t = 0 then P else
    PMF.ofFintype (fun a => P a * Q (t - a) / conv P Q t) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← conv_apply P Q t,
        ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _)])

/-- Masses of the posterior law. -/
theorem posteriorLaw_apply {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) {t : V}
    (h : conv P Q t ≠ 0) (a : V) :
    posteriorLaw P Q t a = P a * Q (t - a) / conv P Q t := by
  unfold posteriorLaw
  rw [dif_neg h, PMF.ofFintype_apply]

/-- Masses of the posterior law, as real numbers. -/
theorem posteriorLaw_toReal {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) {t : V}
    (h : conv P Q t ≠ 0) (a : V) :
    (posteriorLaw P Q t a).toReal = (P a).toReal * (Q (t - a)).toReal / (conv P Q t).toReal := by
  rw [posteriorLaw_apply P Q h, ENNReal.toReal_div, ENNReal.toReal_mul]

namespace WeightedFamily

/-- Weight `a_i a_j (P_i * P_j)(t)` of the posterior index `(i, j, t)`. -/
noncomputable def postMass {V : Type} [AddCommGroup V] (P : WeightedFamily V)
    (x : P.index × P.index × V) : ℝ :=
  P.weights x.1 * P.weights x.2.1 * (conv (P.laws x.1) (P.laws x.2.1) x.2.2).toReal

/-- The posterior weights, before omitting zero-weight indices, sum to one. -/
theorem postMass_sum {V : Type} [Fintype V] [AddCommGroup V] (P : WeightedFamily V) :
    ∑ x, P.postMass x = 1 := by
  unfold postMass
  first
  | (simp only [Fintype.sum_prod_type, ← Finset.mul_sum, pmf_sum_toReal, mul_one, P.weights_sum];
     done)
  | (simp [Fintype.sum_prod_type, ← Finset.mul_sum, pmf_sum_toReal, P.weights_sum])

/-- A posterior weight is positive when `(P_i * P_j)(t) ≠ 0`. -/
theorem postMass_pos {V : Type} [AddCommGroup V] (P : WeightedFamily V)
    {x : P.index × P.index × V} (hx : conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0) :
    0 < P.postMass x :=
  mul_pos (mul_pos (P.weights_pos _) (P.weights_pos _))
    (ENNReal.toReal_pos hx (PMF.apply_ne_top _ _))

open Classical in
/-- The posterior family `Post(𝒫)` (equation (16)): components
`Q_{i,j,t} = Law(A | I = i, J = j, A + B = t)` with weights `a_i a_j (P_i * P_j)(t)`, over the
indices with `(P_i * P_j)(t) ≠ 0`. -/
noncomputable def posterior {V : Type} [Fintype V] [AddCommGroup V] (P : WeightedFamily V) :
    WeightedFamily V where
  index := {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0}
  laws := fun x => posteriorLaw (P.laws x.1.1) (P.laws x.1.2.1) x.1.2.2
  weights := fun x => P.postMass x.1
  weights_pos := fun x => P.postMass_pos x.2
  weights_sum := by
    rw [← P.postMass_sum,
      ← Fintype.sum_subtype_add_sum_subtype
        (fun x : P.index × P.index × V => conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0)
        P.postMass]
    have hz : ∑ x : {x : P.index × P.index × V //
        ¬ conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0}, P.postMass x.1 = 0 :=
      Finset.sum_eq_zero fun x _ => by simp [postMass, not_not.mp x.2]
    rw [hz, add_zero]

end WeightedFamily

/-! ## First half of Lemma 2.2: `h(Post 𝒫) = e(𝒫)` (roadmap item D3b) -/

/-- Pointwise identity behind the chain rule: for `x, y ≥ 0` and `C > 0`,
`C · (-(xy/C) log(xy/C)) = -xy log x - xy log y + xy log C`. -/
theorem posterior_term_eq {x y C : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 < C) :
    C * (-(x * y / C) * Real.logb 2 (x * y / C)) =
      -(x * y) * Real.logb 2 x - x * y * Real.logb 2 y + x * y * Real.logb 2 C := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    ring
  rcases hy.eq_or_lt with h' | h'
  · rw [← h']
    ring
  have hC' : C ≠ 0 := hC.ne'
  rw [Real.logb_div (mul_pos h h').ne' hC', Real.logb_mul h.ne' h'.ne']
  have e : C * (x * y / C) = x * y := by
    first
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [mul_comm]; exact div_mul_cancel₀ _ hC')
  calc C * (-(x * y / C) * (Real.logb 2 x + Real.logb 2 y - Real.logb 2 C))
      = -(C * (x * y / C)) * (Real.logb 2 x + Real.logb 2 y - Real.logb 2 C) := by ring
    _ = _ := by
        rw [e]
        ring

/-- Masses of `P * Q` as real numbers. -/
theorem conv_toReal_eq_sum {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) (t : V) :
    (conv P Q t).toReal = ∑ a, (P a).toReal * (Q (t - a)).toReal := by
  rw [conv_apply, ENNReal.toReal_sum fun a _ =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [ENNReal.toReal_mul]

/-- Shifting the summation variable of a finite sum over a group. -/
theorem fintype_sum_shift {V : Type*} [Fintype V] [AddCommGroup V] (f : V → ℝ) (a : V) :
    ∑ t, f (t - a) = ∑ s, f s :=
  Fintype.sum_equiv (Equiv.subRight a) _ _ fun _ => rfl

/-- `(P * Q)(t) · H(Law(A | A + B = t))`, written as a sum over `a`. -/
theorem conv_mul_entropy_posterior {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V)
    (t : V) :
    (conv P Q t).toReal * entropyBits (posteriorLaw P Q t) =
      ∑ a, (-((P a).toReal * (Q (t - a)).toReal) * Real.logb 2 (P a).toReal -
        (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (Q (t - a)).toReal +
        (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (conv P Q t).toReal) := by
  by_cases h : conv P Q t = 0
  · have hs : (0 : ℝ) = ∑ a, (P a).toReal * (Q (t - a)).toReal := by
      rw [← conv_toReal_eq_sum, h]
      simp
    have h0 : ∀ a, (P a).toReal * (Q (t - a)).toReal = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp hs.symm a (Finset.mem_univ a)
    rw [h]
    first
    | (simp [h0]; done)
    | (simp only [h0, neg_zero, zero_mul, sub_self, sub_zero, add_zero, Finset.sum_const_zero];
       simp)
  · have hC : 0 < (conv P Q t).toReal := ENNReal.toReal_pos h (PMF.apply_ne_top _ _)
    rw [entropyBits_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [posteriorLaw_toReal P Q h]
    exact posterior_term_eq ENNReal.toReal_nonneg ENNReal.toReal_nonneg hC

/-- Chain rule for the posterior: `∑ₜ (P * Q)(t) H(Law(A | A + B = t)) = s(P, Q)`, i.e.
`H(A | A + B) = H(A) + H(B) - H(A + B)`. -/
theorem sum_conv_mul_entropy_posterior {V : Type*} [Fintype V] [AddCommGroup V]
    (P Q : PMF V) :
    ∑ t, (conv P Q t).toReal * entropyBits (posteriorLaw P Q t) = interaction P Q := by
  have hsplit : ∑ t, (conv P Q t).toReal * entropyBits (posteriorLaw P Q t) =
      ∑ t, ∑ a, -((P a).toReal * (Q (t - a)).toReal) * Real.logb 2 (P a).toReal -
      ∑ t, ∑ a, (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (Q (t - a)).toReal +
      ∑ t, ∑ a, (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (conv P Q t).toReal := by
    simp only [conv_mul_entropy_posterior, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have T1 : ∑ t, ∑ a, -((P a).toReal * (Q (t - a)).toReal) * Real.logb 2 (P a).toReal =
      entropyBits P := by
    rw [Finset.sum_comm, entropyBits_eq_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h1 : ∑ t, (Q (t - a)).toReal = 1 :=
      (fintype_sum_shift (fun s => (Q s).toReal) a).trans (pmf_sum_toReal Q)
    calc ∑ t, -((P a).toReal * (Q (t - a)).toReal) * Real.logb 2 (P a).toReal
        = (-(P a).toReal * Real.logb 2 (P a).toReal) * ∑ t, (Q (t - a)).toReal := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          ring
      _ = -(P a).toReal * Real.logb 2 (P a).toReal := by rw [h1, mul_one]
  have hQ : ∑ s, (Q s).toReal * Real.logb 2 (Q s).toReal = -entropyBits Q := by
    rw [entropyBits_eq_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have T2 : ∑ t, ∑ a, (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (Q (t - a)).toReal =
      -entropyBits Q := by
    rw [Finset.sum_comm]
    have hin : ∀ a, ∑ t, (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (Q (t - a)).toReal =
        (P a).toReal * (-entropyBits Q) := by
      intro a
      calc ∑ t, (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (Q (t - a)).toReal
          = ∑ t, (P a).toReal * ((Q (t - a)).toReal * Real.logb 2 (Q (t - a)).toReal) :=
            Finset.sum_congr rfl fun t _ => by ring
        _ = (P a).toReal * ∑ s, (Q s).toReal * Real.logb 2 (Q s).toReal := by
            rw [← Finset.mul_sum]
            congr 1
            exact fintype_sum_shift (fun s => (Q s).toReal * Real.logb 2 (Q s).toReal) a
        _ = (P a).toReal * (-entropyBits Q) := by rw [hQ]
    rw [Finset.sum_congr rfl fun a _ => hin a, ← Finset.sum_mul, pmf_sum_toReal, one_mul]
  have T3 : ∑ t, ∑ a, (P a).toReal * (Q (t - a)).toReal * Real.logb 2 (conv P Q t).toReal =
      -entropyBits (conv P Q) := by
    rw [entropyBits_eq_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul, ← conv_toReal_eq_sum]
    ring
  rw [hsplit, T1, T2, T3]
  unfold interaction
  ring

namespace WeightedFamily

open Classical in
/-- First half of Lemma 2.2 (equation (17)): `h(Post 𝒫) = e(𝒫)`. -/
theorem meanEntropy_posterior {V : Type} [Fintype V] [AddCommGroup V] (P : WeightedFamily V) :
    P.posterior.meanEntropy = P.meanInteraction := by
  have hall : ∑ x : P.index × P.index × V,
      P.postMass x * entropyBits (posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2) =
        P.meanInteraction := by
    unfold postMass meanInteraction
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_conv_mul_entropy_posterior, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  have hz : ∑ x : {x : P.index × P.index × V //
      ¬ conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
        P.postMass x.1 * entropyBits (posteriorLaw (P.laws x.1.1) (P.laws x.1.2.1) x.1.2.2) =
          0 :=
    Finset.sum_eq_zero fun x _ => by simp [postMass, not_not.mp x.2]
  have key : ∑ x : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
      P.postMass x.1 * entropyBits (posteriorLaw (P.laws x.1.1) (P.laws x.1.2.1) x.1.2.2) =
        P.meanInteraction := by
    rw [← hall, ← Fintype.sum_subtype_add_sum_subtype
      (fun x : P.index × P.index × V => conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0)
      (fun x => P.postMass x * entropyBits (posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2)),
      hz, add_zero]
  exact key

end WeightedFamily

/-! ## Disintegration along `A + B` (roadmap item D3c1) -/

/-- Entropy of a joint law given by a kernel: if `R(a, t) = c(t) K_t(a)`, then
`H(R) = H(c) + ∑ₜ c(t) H(K_t)`. -/
theorem entropyBits_of_kernel {α T : Type*} [Fintype α] [Fintype T] (R : PMF (α × T))
    (c : PMF T) (K : T → PMF α)
    (h : ∀ a t, (R (a, t)).toReal = (c t).toReal * (K t a).toReal) :
    entropyBits R = entropyBits c + ∑ t, (c t).toReal * entropyBits (K t) := by
  have hpt : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      -(x * y) * Real.logb 2 (x * y) =
        y * (-x * Real.logb 2 x) + x * (-y * Real.logb 2 y) := by
    intro x y hx hy
    rcases hx.eq_or_lt with h | h
    · rw [← h]
      ring
    rcases hy.eq_or_lt with h' | h'
    · rw [← h']
      ring
    rw [Real.logb_mul h.ne' h'.ne']
    ring
  rw [entropyBits_eq_sum R, Fintype.sum_prod_type, Finset.sum_comm, entropyBits_eq_sum c]
  simp only [entropyBits_eq_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : ∀ a, -(R (a, t)).toReal * Real.logb 2 (R (a, t)).toReal =
      (K t a).toReal * (-(c t).toReal * Real.logb 2 (c t).toReal) +
        (c t).toReal * (-(K t a).toReal * Real.logb 2 (K t a).toReal) := by
    intro a
    rw [h]
    exact hpt _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_add_distrib, ← Finset.sum_mul,
    pmf_sum_toReal, one_mul, ← Finset.mul_sum]

/-- If `R(a, t) = c(t) K_t(a)`, the image of `R` under `(a, t) ↦ (g a, t)` has masses
`c(t) (g_* K_t)(u)`. -/
theorem kernel_masses_map {α β T : Type*} [Fintype α] [Fintype T] [DecidableEq β]
    [DecidableEq T] (R : PMF (α × T)) (c : PMF T) (K : T → PMF α) (g : α → β)
    (h : ∀ a t, (R (a, t)).toReal = (c t).toReal * (K t a).toReal) (u : β) (t : T) :
    ((R.map fun x => (g x.1, x.2)) (u, t)).toReal = (c t).toReal * (((K t).map g) u).toReal := by
  rw [pmf_map_toReal, pmf_map_toReal, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single t]
  · by_cases ha : g a = u
    · simp [ha, h]
    · simp [ha]
  · intro t' _ ht'
    simp [ht']
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- `(P * Q)(t) Q_t(a) = P(a) Q(t - a)` for the posterior law `Q_t`, including when
`(P * Q)(t) = 0`. -/
theorem conv_mul_posteriorLaw_toReal {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V)
    (t a : V) :
    (conv P Q t).toReal * (posteriorLaw P Q t a).toReal = (P a).toReal * (Q (t - a)).toReal := by
  by_cases h : conv P Q t = 0
  · have hs : (0 : ℝ) = ∑ b, (P b).toReal * (Q (t - b)).toReal := by
      rw [← conv_toReal_eq_sum, h]
      simp
    have h0 : (P a).toReal * (Q (t - a)).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ =>
        mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mp hs.symm a (Finset.mem_univ a)
    rw [h0, h]
    simp
  · have hC' : (conv P Q t).toReal ≠ 0 := (ENNReal.toReal_pos h (PMF.apply_ne_top _ _)).ne'
    rw [posteriorLaw_toReal P Q h]
    first
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [mul_comm]; exact div_mul_cancel₀ _ hC')

/-- Masses of the joint law of `(A, A + B)`: `R(a, t) = (P * Q)(t) Q_t(a)`. -/
theorem pair_sum_masses {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) (a t : V) :
    (((prodLaw P Q).map fun x => (x.1, x.1 + x.2)) (a, t)).toReal =
      (conv P Q t).toReal * (posteriorLaw P Q t a).toReal := by
  have e : (a, t) = (fun x : V × V => (x.1, x.1 + x.2)) (a, t - a) := by
    first
    | simp
    | exact Prod.ext rfl (by simp)
  have hm := pmf_map_apply_injective (prodLaw P Q) (fst_add_injective (V := V)) (a, t - a)
  rw [e, hm, prodLaw_apply, ENNReal.toReal_mul, conv_mul_posteriorLaw_toReal]

/-- `H(A, A + B) = H(A + B) + ∑ₜ (P * Q)(t) H(Q_t)`. -/
theorem entropyBits_pair_sum {V : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V) :
    entropyBits ((prodLaw P Q).map fun x => (x.1, x.1 + x.2)) =
      entropyBits (conv P Q) + ∑ t, (conv P Q t).toReal * entropyBits (posteriorLaw P Q t) :=
  entropyBits_of_kernel _ _ _ (pair_sum_masses P Q)

/-- `H(g A, A + B) = H(A + B) + ∑ₜ (P * Q)(t) H(g_* Q_t)`. -/
theorem entropyBits_map_pair_sum {V β : Type*} [Fintype V] [AddCommGroup V] [Fintype β]
    [DecidableEq β] (g : V → β) (P Q : PMF V) :
    entropyBits (((prodLaw P Q).map fun x => (x.1, x.1 + x.2)).map fun y => (g y.1, y.2)) =
      entropyBits (conv P Q) +
        ∑ t, (conv P Q t).toReal * entropyBits ((posteriorLaw P Q t).map g) := by
  classical
  exact entropyBits_of_kernel _ _ _ (kernel_masses_map _ _ _ g (pair_sum_masses P Q))

end EntropyLean
