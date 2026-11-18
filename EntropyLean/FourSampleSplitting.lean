import EntropyLean.MathlibForPFR
import EntropyLean.FourSamplePosterior
import EntropyLean.PosteriorInteraction

/-!
# Lemma 6.1: four-sample splitting (roadmap item D6c3b)

For a weighted family `𝒫 = (P_i, a_i)` draw four independent indexed pairs `(I_r, X_r)` and put
`T = (I₁, I₂, I₃, I₄)`, `A = X₁ + X₂`, `B = X₁ + X₃`, `S = X₁ + X₂ + X₃ + X₄`. Conditioning on `T`
is the weighted sum over index tuples with weights `a_{i₁} a_{i₂} a_{i₃} a_{i₄}`, so
`J = I(A ; B | S, T)` is `WeightedFamily.fourSampleJ` (the average of `fourJ` from
`EntropyLean/FourSample.lean`, `fourSampleJ_nonneg`). This file proves:

* `J = ∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄}) − ∑_T ∑_{a,c} (P_{i₁} * P_{i₂})(a) (P_{i₃} * P_{i₄})(c)
  H(Q_{i₁ i₂ a} * Q_{i₃ i₄ c})` (`fourSampleJ_eq`, from `fourJ_eq` and
  `fourLaw_condEntropy_B_given_AS`);
* `e(𝒫 * 𝒫) = ∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄})` (`meanInteraction_convFamily_four`);
* the posterior double sum of `EntropyLean/PosteriorInteraction.lean` is the second sum above
  (`sum_postMass_conv_eq`);
* **Lemma 6.1** (32): `e(𝒫 * 𝒫) + e(Post 𝒫) = 2e(𝒫) + J` (`four_sample_splitting`); with
  `H = h(𝒫)` and `δ = e(𝒫)/H` this is `e(R) + e(Q) = 2δH + J`.

What this file does NOT prove: Lemma 6.3 (34) (roadmap item D6d), or anything depending on the
entropic Marton bound (35).
-/

namespace EntropyLean

open scoped BigOperators

/-- Reordering a triple sum: `∑_a ∑_k ∑_l f = ∑_k ∑_l ∑_a f`. -/
theorem sum_reorder3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    ∑ a, ∑ k, ∑ l, f a k l = ∑ k, ∑ l, ∑ a, f a k l := by
  calc ∑ a, ∑ k, ∑ l, f a k l = ∑ k, ∑ a, ∑ l, f a k l := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, f a k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm

namespace WeightedFamily

variable {V : Type} [Fintype V] [AddCommGroup V]

/-- `J = I(A ; B | S, T)`: the average of `fourJ` over index tuples `T`. -/
noncomputable def fourSampleJ (P : WeightedFamily V) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
    fourJ (P.laws i) (P.laws j) (P.laws k) (P.laws l)

theorem fourSampleJ_nonneg (P : WeightedFamily V) : 0 ≤ P.fourSampleJ :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (P.weights_pos i).le (P.weights_pos j).le) (P.weights_pos k).le) (P.weights_pos l).le)
      (fourJ_nonneg _ _ _ _)

/-- The posterior summand `(P_i * P_j)(a) (P_k * P_l)(c) H(Q_{i j a} * Q_{k l c})`. -/
noncomputable def fourPostTerm (P : WeightedFamily V) (i j k l : P.index) (a c : V) : ℝ :=
  (conv (P.laws i) (P.laws j) a).toReal * (conv (P.laws k) (P.laws l) c).toReal *
    entropyBits (conv (posteriorLaw (P.laws i) (P.laws j) a) (posteriorLaw (P.laws k) (P.laws l) c))

/-- `J = ∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄}) − ∑_T ∑_{a,c} (posterior summand)`. -/
theorem fourSampleJ_eq (P : WeightedFamily V) :
    P.fourSampleJ =
      (∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l))) -
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c, P.weights i * P.weights j * P.weights k * P.weights l *
        P.fourPostTerm i j k l a c := by
  unfold fourSampleJ
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [fourJ_eq, fourLaw_condEntropy_B_given_AS]
  simp only [fourPostTerm, mul_sub, Finset.mul_sum]

/-- `e(𝒫 * 𝒫) = ∑_{i,j,k,l} a_i a_j a_k a_l s(P_i * P_k, P_j * P_l)`. -/
theorem meanInteraction_convFamily_four (P : WeightedFamily V) :
    P.convFamily.meanInteraction =
      ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l)) := by
  show ∑ p : P.index × P.index, ∑ q : P.index × P.index,
      P.weights p.1 * P.weights p.2 * (P.weights q.1 * P.weights q.2) *
        interaction (conv (P.laws p.1) (P.laws p.2)) (conv (P.laws q.1) (P.laws q.2)) = _
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

/-- The posterior double sum, reindexed over index tuples. -/
theorem sum_postMass_conv_eq (P : WeightedFamily V) :
    ∑ x, ∑ y, P.postMass x * P.postMass y * entropyBits (conv (P.postLawAt x) (P.postLawAt y)) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c, P.weights i * P.weights j * P.weights k * P.weights l *
        P.fourPostTerm i j k l a c := by
  simp only [Fintype.sum_prod_type, postMass, postLawAt]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine (sum_reorder3 _).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  unfold fourPostTerm
  ring

/-- **Lemma 6.1** (32), four-sample splitting: `e(𝒫 * 𝒫) + e(Post 𝒫) = 2e(𝒫) + J` with
`J = I(A ; B | S, T)` (`fourSampleJ`). With `H = h(𝒫)` and `δ = e(𝒫)/H` this reads
`e(R) + e(Q) = 2δH + J`. -/
theorem four_sample_splitting (P : WeightedFamily V) :
    P.convFamily.meanInteraction + P.posterior.meanInteraction =
      2 * P.meanInteraction + P.fourSampleJ := by
  rw [meanInteraction_posterior_eq, sum_postMass_conv_eq, fourSampleJ_eq,
    meanInteraction_convFamily_four]
  ring

end WeightedFamily

end EntropyLean
