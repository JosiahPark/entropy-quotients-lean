import Mathlib
import EntropyLean.MartonStep
import EntropyLean.PosteriorDoublingAvg

/-!
# Lemma 7.1, averaged Marton step over posterior pairs (roadmap item D8b, Section 7)

For a weighted family `𝒫` on a finite F₂-space `V`, with posterior triples `x = (i, j, t)`,
weights `m(x) = a_i a_j (P_i * P_j)(t)` (`postMass`) and posterior laws `Q_x` (`postLawAt`),
apply the two-law Marton step `interaction_le_subspace_add_increment` (roadmap item D8a) to each
pair `(Q_x, Q_y)` and choose the subspace `W(x, y)` it gives (`postSubspace`). This file proves

* `postMass_nonneg`: `0 ≤ m(x)`;
* `posterior_interaction_le_subspace`: with `𝒬 = Post 𝒫`,
  `e(𝒬) ≤ ∑_{x,y} m(x) m(y) s_{W(x,y)}(Q_x, Q_y) + 36 J`, from (34) (`posterior_doubling`);
* `posterior_mean_dim_le`: (38) `∑_{x,y} m(x) m(y) dim W(x, y) ≤ 26 h(𝒬)`.

All sums run over all triples, as in `meanInteraction_posterior_full`.

What this file does NOT prove: the bound of the first term by `14 √ρ h(𝒬)` through Lemma 5.1, nor
Lemma 7.1 (37) itself (roadmap item D8c); nor the entropic Marton bound (35), which enters only as
the hypothesis `hM : MartonInput V`.
-/

namespace EntropyLean

open scoped BigOperators

namespace WeightedFamily

variable {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

omit [Fintype V] [Module (ZMod 2) V] in
/-- Posterior weights are nonnegative. -/
theorem postMass_nonneg (P : WeightedFamily V) (x : P.index × P.index × V) :
    0 ≤ P.postMass x :=
  mul_nonneg (mul_nonneg (le_of_lt (P.weights_pos _)) (le_of_lt (P.weights_pos _)))
    ENNReal.toReal_nonneg

/-- The subspace `W(x, y)` given by the Marton step for the pair `(Q_x, Q_y)`. -/
noncomputable def postSubspace (P : WeightedFamily V) (hM : MartonInput V)
    (x y : P.index × P.index × V) : Submodule (ZMod 2) V :=
  Classical.choose (interaction_le_subspace_add_increment hM (P.postLawAt x) (P.postLawAt y))

theorem postSubspace_spec (P : WeightedFamily V) (hM : MartonInput V)
    (x y : P.index × P.index × V) :
    interaction (P.postLawAt x) (P.postLawAt y) ≤
        subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
          12 * entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) ∧
      (Module.finrank (ZMod 2) (P.postSubspace hM x y) : ℝ) ≤
        13 * (entropyBits (P.postLawAt x) + entropyBits (P.postLawAt y)) :=
  Classical.choose_spec
    (interaction_le_subspace_add_increment hM (P.postLawAt x) (P.postLawAt y))

/-- `e(Post 𝒫) ≤ ∑_{x,y} m(x) m(y) s_{W(x,y)}(Q_x, Q_y) + 36 J`. -/
theorem posterior_interaction_le_subspace (P : WeightedFamily V) (hM : MartonInput V) :
    P.posterior.meanInteraction ≤
      ∑ x, ∑ y, P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
        36 * P.fourSampleJ := by
  have hpd := P.posterior_doubling
  have hterm : ∀ x y, P.postPairTerm x y ≤
      P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
        12 * (P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y))) := by
    intro x y
    have h := (P.postSubspace_spec hM x y).1
    have hm : 0 ≤ P.postMass x * P.postMass y :=
      mul_nonneg (P.postMass_nonneg x) (P.postMass_nonneg y)
    unfold postPairTerm
    calc P.postMass x * P.postMass y * interaction (P.postLawAt x) (P.postLawAt y)
        ≤ P.postMass x * P.postMass y *
            (subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
              12 * entropyIncrement (conv (P.postLawAt x) (P.postLawAt y))) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  have hsum : ∑ x, ∑ y, P.postPairTerm x y ≤
      ∑ x, ∑ y, (P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
        12 * (P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)))) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hsplit : ∑ x, ∑ y, (P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
        12 * (P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)))) =
      ∑ x, ∑ y, P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) +
        12 * ∑ x, ∑ y, P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [meanInteraction_posterior_full]
  linarith

/-- Equation (38): `∑_{x,y} m(x) m(y) dim W(x, y) ≤ 26 h(Post 𝒫)`. -/
theorem posterior_mean_dim_le (P : WeightedFamily V) (hM : MartonInput V) :
    ∑ x, ∑ y, P.postMass x * P.postMass y *
        (Module.finrank (ZMod 2) (P.postSubspace hM x y) : ℝ) ≤
      26 * P.posterior.meanEntropy := by
  have hterm : ∀ x y, P.postMass x * P.postMass y *
      (Module.finrank (ZMod 2) (P.postSubspace hM x y) : ℝ) ≤
      13 * (P.postMass x * entropyBits (P.postLawAt x) * P.postMass y) +
        13 * (P.postMass x * (P.postMass y * entropyBits (P.postLawAt y))) := by
    intro x y
    have h := (P.postSubspace_spec hM x y).2
    have hm : 0 ≤ P.postMass x * P.postMass y :=
      mul_nonneg (P.postMass_nonneg x) (P.postMass_nonneg y)
    calc P.postMass x * P.postMass y * (Module.finrank (ZMod 2) (P.postSubspace hM x y) : ℝ)
        ≤ P.postMass x * P.postMass y *
            (13 * (entropyBits (P.postLawAt x) + entropyBits (P.postLawAt y))) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  have hsum : ∑ x, ∑ y, P.postMass x * P.postMass y *
        (Module.finrank (ZMod 2) (P.postSubspace hM x y) : ℝ) ≤
      ∑ x, ∑ y, (13 * (P.postMass x * entropyBits (P.postLawAt x) * P.postMass y) +
        13 * (P.postMass x * (P.postMass y * entropyBits (P.postLawAt y)))) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hs : ∑ x, ∑ y, (13 * (P.postMass x * entropyBits (P.postLawAt x) * P.postMass y) +
        13 * (P.postMass x * (P.postMass y * entropyBits (P.postLawAt y)))) =
      13 * ((∑ x, P.postMass x * entropyBits (P.postLawAt x)) * ∑ y, P.postMass y) +
        13 * ((∑ x, P.postMass x) * ∑ y, P.postMass y * entropyBits (P.postLawAt y)) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [P.sum_postMass_mul_entropy, P.postMass_sum] at hs
  rw [meanEntropy_posterior]
  linarith

end WeightedFamily

end EntropyLean
