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

What this file does NOT prove: Lemma 2.2 itself, i.e. `h(Post 𝒫) = e(𝒫)` and
`F_{Post 𝒫}(W) ≤ F_𝒫(W)` (roadmap items D3b, D3c).
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
end EntropyLean
