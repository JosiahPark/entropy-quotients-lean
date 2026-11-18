import EntropyLean.MathlibForPFR
import EntropyLean.PosteriorDoublingC
import EntropyLean.FourSampleSplitting

/-!
# Lemma 6.3: posterior doubling (roadmap item D6d4)

For a weighted family `𝒫 = (P_i, a_i)` on a finite F₂-space, with posterior triples
`x = (i, j, t)`, weights `m(x) = a_i a_j (P_i * P_j)(t)` (`postMass`) and posterior laws
`Q_x = posteriorLaw P_i P_j t` (`postLawAt`), and with `J = I(A ; B | S, T)` (`fourSampleJ`),
this file proves **Lemma 6.3** (34):

`∑_{x,y} m(x) m(y) D(Q_x * Q_y) ≤ 3 J` (`WeightedFamily.posterior_doubling`).

The sum runs over all triples, as in `meanInteraction_posterior_full`; triples with `m(x) = 0`
(omitted from the posterior family `Post 𝒫`) contribute nothing, so this is `E_{u,w} D(Q_u * Q_w)`
for independent `u, w` drawn from `Post 𝒫`. Proof: reindex the left side over index tuples
`(i, j, k, l)` (`sum_postMass_conv_inc`); at each tuple apply the fixed-law bound
`four_posterior_doubling_interaction` to the laws `(P_i, P_k, P_j, P_l)`; after averaging, the
three interaction sums are all equal to `∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄})` (relabelling the
summation indices, `sum4_swap23`, `sum4_swap34`), so `2s − s − s` cancels and the averaged `J` term
is `fourSampleJ`.

What this file does NOT prove: anything depending on the entropic Marton bound (35)
(roadmap items D7–D9).
-/

namespace EntropyLean

open scoped BigOperators

/-- Exchanging the second and third summation indices. -/
theorem sum4_swap23 {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i k j l :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Exchanging the third and fourth summation indices. -/
theorem sum4_swap34 {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ j, ∑ k, ∑ l, f i j l k :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

namespace WeightedFamily

variable {V : Type} [Fintype V] [AddCommGroup V]

/-- The posterior double sum of `D(Q_x * Q_y)`, reindexed over index tuples. -/
theorem sum_postMass_conv_inc (P : WeightedFamily V) :
    ∑ x, ∑ y, P.postMass x * P.postMass y *
        entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ a, ∑ c, P.weights i * P.weights j * P.weights k * P.weights l *
        ((conv (P.laws i) (P.laws j) a).toReal * (conv (P.laws k) (P.laws l) c).toReal *
          entropyIncrement (conv (posteriorLaw (P.laws i) (P.laws j) a)
            (posteriorLaw (P.laws k) (P.laws l) c))) := by
  simp only [Fintype.sum_prod_type, postMass, postLawAt]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine (sum_reorder3 _).trans ?_
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The averaged `I(A ; B | S)` for the laws `(P_i, P_k, P_j, P_l)` is `J`. -/
theorem fourSampleJ_swap (P : WeightedFamily V) :
    ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        fourJ (P.laws i) (P.laws k) (P.laws j) (P.laws l) = P.fourSampleJ := by
  refine (sum4_swap23 _).trans ?_
  unfold fourSampleJ
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `∑_T s(P_{i₁} * P_{i₂}, P_{i₃} * P_{i₄}) = ∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄})`. -/
theorem sum_interaction_swap23 (P : WeightedFamily V) :
    ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws i) (P.laws j)) (conv (P.laws k) (P.laws l)) =
      ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l)) := by
  refine (sum4_swap23 _).trans ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- `∑_T s(P_{i₃} * P_{i₂}, P_{i₁} * P_{i₄}) = ∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄})`. -/
theorem sum_interaction_rot (P : WeightedFamily V) :
    ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws k) (P.laws j)) (conv (P.laws i) (P.laws l)) =
      ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l)) := by
  calc ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws k) (P.laws j)) (conv (P.laws i) (P.laws l)) =
      ∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
        interaction (conv (P.laws i) (P.laws l)) (conv (P.laws j) (P.laws k)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [conv_comm_law (P.laws k) (P.laws j), interaction_comm]
    _ = _ := by
        refine (sum4_swap34 _).trans ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        ring

/-- **Lemma 6.3** (34), posterior doubling: `∑_{x,y} m(x) m(y) D(Q_x * Q_y) ≤ 3 J`, i.e.
`E_{u,w} D(Q_u * Q_w) ≤ 3 I(A ; B | S, T)`. -/
theorem posterior_doubling [Module (ZMod 2) V] (P : WeightedFamily V) :
    ∑ x, ∑ y, P.postMass x * P.postMass y *
        entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) ≤ 3 * P.fourSampleJ := by
  have hpt : ∀ i j k l,
      ∑ a, ∑ c, P.weights i * P.weights j * P.weights k * P.weights l *
        ((conv (P.laws i) (P.laws j) a).toReal * (conv (P.laws k) (P.laws l) c).toReal *
          entropyIncrement (conv (posteriorLaw (P.laws i) (P.laws j) a)
            (posteriorLaw (P.laws k) (P.laws l) c))) ≤
      3 * (P.weights i * P.weights j * P.weights k * P.weights l *
          fourJ (P.laws i) (P.laws k) (P.laws j) (P.laws l)) +
        2 * (P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws k) (P.laws j)) (conv (P.laws i) (P.laws l))) -
        P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws i) (P.laws j)) (conv (P.laws k) (P.laws l)) -
        P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l)) := by
    intro i j k l
    have hW : 0 ≤ P.weights i * P.weights j * P.weights k * P.weights l :=
      mul_nonneg (mul_nonneg (mul_nonneg (P.weights_pos i).le (P.weights_pos j).le)
        (P.weights_pos k).le) (P.weights_pos l).le
    have e : ∑ a, ∑ c, P.weights i * P.weights j * P.weights k * P.weights l *
        ((conv (P.laws i) (P.laws j) a).toReal * (conv (P.laws k) (P.laws l) c).toReal *
          entropyIncrement (conv (posteriorLaw (P.laws i) (P.laws j) a)
            (posteriorLaw (P.laws k) (P.laws l) c))) =
        P.weights i * P.weights j * P.weights k * P.weights l *
          ∑ a, ∑ c, (conv (P.laws i) (P.laws j) a).toReal *
            (conv (P.laws k) (P.laws l) c).toReal *
            entropyIncrement (conv (posteriorLaw (P.laws i) (P.laws j) a)
              (posteriorLaw (P.laws k) (P.laws l) c)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
    rw [e]
    exact (mul_le_mul_of_nonneg_left
      (four_posterior_doubling_interaction (P.laws i) (P.laws k) (P.laws j) (P.laws l)) hW).trans_eq
      (by ring)
  rw [sum_postMass_conv_inc]
  calc _ ≤ ∑ i, ∑ j, ∑ k, ∑ l,
        (3 * (P.weights i * P.weights j * P.weights k * P.weights l *
          fourJ (P.laws i) (P.laws k) (P.laws j) (P.laws l)) +
        2 * (P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws k) (P.laws j)) (conv (P.laws i) (P.laws l))) -
        P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws i) (P.laws j)) (conv (P.laws k) (P.laws l)) -
        P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l))) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hpt i j k l
    _ = 3 * (∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
          fourJ (P.laws i) (P.laws k) (P.laws j) (P.laws l)) +
        2 * (∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws k) (P.laws j)) (conv (P.laws i) (P.laws l))) -
        (∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws i) (P.laws j)) (conv (P.laws k) (P.laws l))) -
        (∑ i, ∑ j, ∑ k, ∑ l, P.weights i * P.weights j * P.weights k * P.weights l *
          interaction (conv (P.laws i) (P.laws k)) (conv (P.laws j) (P.laws l))) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 3 * P.fourSampleJ := by
        rw [fourSampleJ_swap, sum_interaction_rot, sum_interaction_swap23]
        ring

end WeightedFamily

end EntropyLean
