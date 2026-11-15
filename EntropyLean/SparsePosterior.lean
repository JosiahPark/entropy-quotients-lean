import Mathlib
import EntropyLean.MartonStep
import EntropyLean.PosteriorDoublingAvg
import EntropyLean.PosteriorClosure
import EntropyLean.DensitySqrt

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

Roadmap item D8c adds
* `posterior_double_sum`: an average over pairs of posterior indices is the sum over all pairs of
  triples with weights `m(x) m(y)`;
* `sparse_posterior_estimate`: **Lemma 7.1** (37), `e(𝒬) ≤ 36 J + 14 √ρ δH` with `δH = e(𝒫)`,
  for a `ρ`-sparse posterior family `𝒬` (`ρ ≥ 0`), via Lemma 5.1 (29) (`averaged_density_sqrt`);
* `sparse_posterior_estimate_of_sparse`: the same when `𝒫` itself is `ρ`-sparse (Lemma 2.2).

What this file does NOT prove: the entropic Marton bound (35), which enters only as the hypothesis
`hM : MartonInput V`; nor Lemma 8.1 or Theorem 8.2.
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

open Classical in
/-- An average over pairs of posterior indices, as a sum over all pairs of triples:
`∑_{u,w} m(u) m(w) g(u, w)` (the terms with `m = 0` vanish). -/
theorem posterior_double_sum (P : WeightedFamily V)
    (g : P.index × P.index × V → P.index × P.index × V → ℝ) :
    ∑ u : P.posterior.index, P.posterior.weights u *
        ∑ w : P.posterior.index, P.posterior.weights w * g (Subtype.val u) (Subtype.val w) =
      ∑ x, ∑ y, P.postMass x * P.postMass y * g x y := by
  show ∑ x : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
      P.postMass x.1 *
        ∑ y : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
          P.postMass y.1 * g x.1 y.1 = _
  have inner : ∀ x : P.index × P.index × V,
      ∑ y : {x : P.index × P.index × V // conv (P.laws x.1) (P.laws x.2.1) x.2.2 ≠ 0},
        P.postMass y.1 * g x y.1 = ∑ y, P.postMass y * g x y := fun x =>
    sum_posterior_index P (fun y => P.postMass y * g x y) fun y hy => by
      simp only [postMass_eq_zero P hy, zero_mul]
  simp only [inner]
  refine (sum_posterior_index P (fun x => P.postMass x * ∑ y, P.postMass y * g x y)
    fun x hx => by simp only [postMass_eq_zero P hx, zero_mul]).trans ?_
  simp only [Finset.mul_sum, mul_assoc]

/-- **Lemma 7.1** (37), sparse posterior estimate: if the posterior family `𝒬 = Post 𝒫` is
`ρ`-sparse (`ρ ≥ 0`), then `e(𝒬) ≤ 36 J + 14 √ρ δH`, where `δH = e(𝒫) = h(𝒬)` and
`J = I(A ; B | S, T)` (`fourSampleJ`). The Marton bound (35) is the hypothesis `hM`. -/
theorem sparse_posterior_estimate (P : WeightedFamily V) (hM : MartonInput V) {rho : ℝ}
    (hsp : P.posterior.IsSparse rho) (hrho : 0 ≤ rho) :
    P.posterior.meanInteraction ≤
      36 * P.fourSampleJ + 14 * Real.sqrt rho * P.meanInteraction := by
  have h1 := P.posterior_interaction_le_subspace hM
  have hB := P.posterior_mean_dim_le hM
  have hBQ := (posterior_double_sum P fun x y =>
    (Module.finrank (ZMod 2) (P.postSubspace hM x y) : ℝ)).le.trans hB
  have hA := P.posterior.averaged_density_sqrt hsp hrho
    (fun u w => P.postSubspace hM (Subtype.val u) (Subtype.val w)) hBQ
  have hA' : ∑ x, ∑ y, P.postMass x * P.postMass y *
        subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspace hM x y) ≤
      14 * Real.sqrt rho * P.posterior.meanEntropy :=
    (posterior_double_sum P fun x y => subspaceInteraction (P.postLawAt x) (P.postLawAt y)
      (P.postSubspace hM x y)).symm.le.trans hA
  rw [meanEntropy_posterior] at hA'
  linarith

/-- **Lemma 7.1** for a `ρ`-sparse family `𝒫`: its posterior family is `ρ`-sparse by Lemma 2.2
(`posterior_closure`), so `e(Post 𝒫) ≤ 36 J + 14 √ρ e(𝒫)`. -/
theorem sparse_posterior_estimate_of_sparse (P : WeightedFamily V) (hM : MartonInput V)
    {rho : ℝ} (hsp : P.IsSparse rho) (hrho : 0 ≤ rho) :
    P.posterior.meanInteraction ≤
      36 * P.fourSampleJ + 14 * Real.sqrt rho * P.meanInteraction :=
  P.sparse_posterior_estimate hM (posterior_closure rho P hsp) hrho

end WeightedFamily

end EntropyLean
