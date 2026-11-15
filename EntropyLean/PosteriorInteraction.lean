import Mathlib
import EntropyLean.Posterior

/-!
# Mean interaction of the posterior family (roadmap item D6c3a)

For a weighted family `𝒫` with posterior family `Post 𝒫` (equation (16)), write
`m(i, j, t) = a_i a_j (P_i * P_j)(t)` (`postMass`) and `Q_{i,j,t} = posteriorLaw P_i P_j t`
(`postLawAt`, defined also when `(P_i * P_j)(t) = 0`). This file proves:

* sums over the posterior index (the triples with `(P_i * P_j)(t) ≠ 0`) of terms that vanish when
  `(P_i * P_j)(t) = 0` are sums over all triples (`sum_posterior_index`);
* `∑_x m(x) H(Q_x) = e(𝒫)` over all triples (`sum_postMass_mul_entropy`, from
  `meanEntropy_posterior`);
* `e(Post 𝒫) = ∑_{x,y} m(x) m(y) s(Q_x, Q_y)` over all triples (`meanInteraction_posterior_full`);
* `e(Post 𝒫) = 2e(𝒫) − ∑_{x,y} m(x) m(y) H(Q_x * Q_y)` (`meanInteraction_posterior_eq`).

What this file does NOT prove: the four-sample identity (32) itself (roadmap item D6c3b).
-/

namespace EntropyLean

open scoped BigOperators

namespace WeightedFamily

variable {V : Type} [Fintype V] [AddCommGroup V]

/-- The posterior law `Q_{i,j,t} = Law(A | I = i, J = j, A + B = t)` at any triple. -/
noncomputable def postLawAt (P : WeightedFamily V) (x : P.index × P.index × V) : PMF V :=
  posteriorLaw (P.laws x.1) (P.laws x.2.1) x.2.2

omit [Fintype V] in
theorem postMass_eq_zero (P : WeightedFamily V) {x : P.index × P.index × V}
    (hx : conv (P.laws x.1) (P.laws x.2.1) x.2.2 = 0) : P.postMass x = 0 := by
  simp [postMass, hx]

open Classical in
/-- A sum over the posterior index of a term vanishing off it is a sum over all triples. -/
theorem sum_posterior_index (P : WeightedFamily V) (g : P.index × P.index × V → ℝ)
    (hg : ∀ x, conv (P.laws x.1) (P.laws x.2.1) x.2.2 = 0 → g x = 0) :
    ∑ x : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0}, g x.1 =
      ∑ x, g x := by
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun x : P.index × P.index × V => conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0) g]
  have hz : ∑ x : {x : P.index × P.index × V //
      ¬ conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0}, g x.1 = 0 :=
    Finset.sum_eq_zero fun x _ => hg x.1 (not_not.mp x.2)
  rw [hz, add_zero]

open Classical in
/-- `∑_x m(x) H(Q_x) = e(𝒫)`, summed over all triples. -/
theorem sum_postMass_mul_entropy (P : WeightedFamily V) :
    ∑ x, P.postMass x * entropyBits (P.postLawAt x) = P.meanInteraction := by
  rw [← meanEntropy_posterior P]
  exact (sum_posterior_index P _ fun x hx => by rw [postMass_eq_zero P hx, zero_mul]).symm

/-- The summand `m(x) m(y) s(Q_x, Q_y)` of `e(Post 𝒫)`. -/
noncomputable def postPairTerm (P : WeightedFamily V) (x y : P.index × P.index × V) : ℝ :=
  P.postMass x * P.postMass y * interaction (P.postLawAt x) (P.postLawAt y)

open Classical in
/-- `e(Post 𝒫) = ∑_{x,y} m(x) m(y) s(Q_x, Q_y)`, summed over all triples. -/
theorem meanInteraction_posterior_full (P : WeightedFamily V) :
    P.posterior.meanInteraction = ∑ x, ∑ y, P.postPairTerm x y := by
  show ∑ x : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
      ∑ y : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
        P.postPairTerm x.1 y.1 = _
  have inner : ∀ x : P.index × P.index × V,
      ∑ y : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
        P.postPairTerm x y.1 = ∑ y, P.postPairTerm x y := fun x =>
    sum_posterior_index P (P.postPairTerm x) fun y hy => by
      unfold postPairTerm
      rw [postMass_eq_zero P hy, mul_zero, zero_mul]
  simp only [inner]
  exact sum_posterior_index P (fun x => ∑ y, P.postPairTerm x y) fun x hx =>
    Finset.sum_eq_zero fun y _ => by
      unfold postPairTerm
      rw [postMass_eq_zero P hx, zero_mul, zero_mul]

/-- `e(Post 𝒫) = 2e(𝒫) − ∑_{x,y} m(x) m(y) H(Q_x * Q_y)`. -/
theorem meanInteraction_posterior_eq (P : WeightedFamily V) :
    P.posterior.meanInteraction = 2 * P.meanInteraction -
      ∑ x, ∑ y, P.postMass x * P.postMass y *
        entropyBits (conv (P.postLawAt x) (P.postLawAt y)) := by
  have e1 : ∀ x y, P.postPairTerm x y =
      P.postMass x * entropyBits (P.postLawAt x) * P.postMass y +
        P.postMass x * (P.postMass y * entropyBits (P.postLawAt y)) -
          P.postMass x * P.postMass y * entropyBits (conv (P.postLawAt x) (P.postLawAt y)) := by
    intro x y
    unfold postPairTerm interaction
    ring
  have hs : ∑ x, ∑ y, P.postPairTerm x y =
      (∑ x, P.postMass x * entropyBits (P.postLawAt x)) * ∑ y, P.postMass y +
        (∑ x, P.postMass x) * ∑ y, P.postMass y * entropyBits (P.postLawAt y) -
          ∑ x, ∑ y, P.postMass x * P.postMass y *
            entropyBits (conv (P.postLawAt x) (P.postLawAt y)) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    simp only [Finset.mul_sum, e1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [meanInteraction_posterior_full, hs, sum_postMass_mul_entropy, P.postMass_sum]
  ring

end WeightedFamily

end EntropyLean
