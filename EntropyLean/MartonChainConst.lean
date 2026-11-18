import EntropyLean.MathlibForPFR
import EntropyLean.MartonConst
import EntropyLean.RigidityArithParam
import EntropyLean.UniverseTransport

/-!
# Lemmas 7.1 and 8.1 and Theorems 8.2, 1.1, 1.2 with the Marton constant as a parameter
(roadmap item G2)

The paper's constants 12, 13, 36, 14, 148, 1600 and 320 all come from the constant 6 of the
entropic Marton bound (35). This file repeats Sections 7 and 8 of arXiv:2610.38525 with (35)
assumed for a constant `C ≥ 0` (`MartonInputConst C`, `MartonBoundConst C`), keeping track of how
each constant depends on `C`:

| paper (`C = 6`) | here |
| --- | --- |
| (36): `12`, `13` | `2C`, `1 + 2C` (`MartonInputConst.consequence`) |
| Lemma 7.1: `36 J + 14 √ρ δH` | `6C J + (2 + 2C) √ρ δH` (`sparse_posterior_estimate_const`) |
| Lemma 8.1: `d + d²/148` if `1600 λ ≤ d²` | `d + d²/(24C + 4)` if `32 (1 + C)² λ ≤ d²` |
| Theorem 8.2: `320` | `martonRigidityConst C = 48C + 17 + 2 log₂(1 + C)` |

At `C = 6` the hypothesis of Lemma 8.1 becomes `1568 λ ≤ d²` (the paper rounds `14√2` up to 20,
giving 1600), and `martonRigidityConst 6 = 305 + 2 log₂ 7 < 311`.

Proved here:

* `interaction_le_subspace_add_increment_const` (D8a with `C`);
* `density_sqrt_arith_param`, `WeightedFamily.averaged_density_sqrt_param`: Lemma 5.1 (29) in
  the form `B ≤ β h ⇒ A ≤ (1 + β/2) √λ h` (the paper's case is `β = 26`);
* `WeightedFamily.posterior_interaction_le_subspace_const`,
  `WeightedFamily.posterior_mean_dim_le_const`, `WeightedFamily.sparse_posterior_estimate_const`:
  Lemma 7.1 with `C`;
* `ratio_growth_arith_const`, `WeightedFamily.ratio_growth_of_marton_const`: Lemma 8.1 with `C`,
  as `RatioGrowthConst.{0} (24C + 4) (32 (1 + C)²)`;
* `ratioGrowthConst_lift`: the universe transport of item D10 for `RatioGrowthConst`;
* `weighted_family_rigidity_of_marton_const`: Theorem 8.2 with constant `martonRigidityConst C`;
* `exponential_entropy_quotient_of_marton_const`, `sparse_rigidity_of_marton_const`: the
  conclusions of Theorems 1.1 and 1.2 with that constant, in every universe, from
  `MartonBoundConst.{0} C`;
* `martonRigidityConst_eq`, `martonRigidityConst_six_lt`: the closed form and the value at 6.

So a Marton bound with a smaller constant gives Theorem 1.1 with a smaller exponent with no
further work.

What this file does NOT prove: the entropic Marton bound for any constant `C` (it is the
hypothesis `hM`), hence none of Theorems 1.1, 1.2, 8.2 unconditionally. It does not claim that
any `C < 6` is available: the only input cited by the paper is `C = 6`.
-/

universe u

namespace EntropyLean

open scoped BigOperators

section MartonStepConst

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The Marton step of Lemma 7.1 for two laws, with constant `C ≥ 0`: some subspace `W` has
`s(P, Q) ≤ s_W(P, Q) + 2C · D(P * Q)` and `dim W ≤ (1 + 2C)(H(P) + H(Q))`. -/
theorem interaction_le_subspace_add_increment_const {C : ℝ} (hM : MartonInputConst C V)
    (hC : 0 ≤ C) (P Q : PMF V) :
    ∃ W : Submodule (ZMod 2) V,
      interaction P Q ≤ subspaceInteraction P Q W + 2 * C * entropyIncrement (conv P Q) ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ (1 + 2 * C) * (entropyBits P + entropyBits Q) := by
  obtain ⟨W, h1, _, h3⟩ := hM.consequence hC (conv P Q)
  refine ⟨W, ?_, ?_⟩
  · have hfib := interaction_sub_le_subspace P Q W
    have hq := interaction_quot_le_entropyBits_conv P Q W
    linarith
  · have hc := entropyBits_conv_le P Q
    have h4 : (1 + 2 * C) * entropyBits (conv P Q) ≤
        (1 + 2 * C) * (entropyBits P + entropyBits Q) :=
      mul_le_mul_of_nonneg_left hc (by linarith)
    linarith

end MartonStepConst

/-- The arithmetic of (29) from (28) with a general constant: if
`A ≤ h/N + λ B (N − 1)/2` for every `N ≥ 1`, `h ≥ 0`, `λ ≥ 0`, `β ≥ 0` and `B ≤ β h`, then
`A ≤ (1 + β/2) √λ h`. -/
theorem density_sqrt_arith_param {A B h lam β : ℝ} (h0 : 0 ≤ h) (hlam : 0 ≤ lam) (hβ : 0 ≤ β)
    (hB : B ≤ β * h)
    (hest : ∀ N : ℕ, 0 < N → A ≤ h / N + lam * B * ((N : ℝ) - 1) / 2) :
    A ≤ (1 + β / 2) * Real.sqrt lam * h := by
  rcases hlam.eq_or_lt with hl0 | hlpos
  · -- `λ = 0`: `A ≤ h/N` for every `N ≥ 1`, hence `A ≤ 0`.
    rw [← hl0, Real.sqrt_zero]
    have hz : (1 + β / 2) * 0 * h = 0 := by ring
    rw [hz]
    by_contra hA
    push_neg at hA
    obtain ⟨N, hN⟩ := exists_nat_gt (h / A)
    have hq : 0 ≤ h / A := div_nonneg h0 hA.le
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt hq hN
    have hN' : 0 < N := by exact_mod_cast hNpos
    have h1 : h < N * A := (div_lt_iff₀ hA).mp hN
    have h2 : h / N < A := (div_lt_iff₀ hNpos).mpr (by linarith)
    have h3 := hest N hN'
    have h4 : lam * B * ((N : ℝ) - 1) / 2 = 0 := by rw [← hl0]; ring
    linarith
  · -- `λ > 0`: take `N = ⌈1/√λ⌉`.
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
    rw [← hs]
    have hspos : 0 < s := by
      rw [hs]
      exact Real.sqrt_pos.mpr hlpos
    have hsne : s ≠ 0 := hspos.ne'
    have hss : s * s = lam := by
      rw [hs]
      exact Real.mul_self_sqrt hlam
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈1 / s⌉₊ := ⟨_, rfl⟩
    have hinv : 0 < 1 / s := div_pos one_pos hspos
    have hle : 1 / s ≤ (N : ℝ) := by
      rw [hNdef]
      exact Nat.le_ceil _
    have hlt : (N : ℝ) < 1 / s + 1 := by
      rw [hNdef]
      exact Nat.ceil_lt_add_one hinv.le
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hinv hle
    have hN' : 0 < N := by exact_mod_cast hNpos
    have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN'
    have hsinv : s * (1 / s) = 1 := mul_one_div_cancel hsne
    have hNs : 1 ≤ s * N := by
      have := mul_le_mul_of_nonneg_left hle hspos.le
      linarith
    have hsN : s * ((N : ℝ) - 1) ≤ 1 := by
      have h' : (N : ℝ) - 1 < 1 / s := by linarith
      have := mul_lt_mul_of_pos_left h' hspos
      linarith
    have hfirst : h / N ≤ s * h := by
      rw [div_le_iff₀ hNpos]
      have := mul_le_mul_of_nonneg_left hNs h0
      linarith
    have ht0 : 0 ≤ lam * ((N : ℝ) - 1) := mul_nonneg hlam (by linarith)
    have hts : lam * ((N : ℝ) - 1) ≤ s := by
      have e : lam * ((N : ℝ) - 1) = s * (s * ((N : ℝ) - 1)) := by rw [← hss]; ring
      have := mul_le_mul_of_nonneg_left hsN hspos.le
      linarith
    have hsecond : lam * B * ((N : ℝ) - 1) / 2 ≤ β / 2 * (s * h) := by
      have e : lam * B * ((N : ℝ) - 1) / 2 = B * (lam * ((N : ℝ) - 1)) / 2 := by ring
      have h1 := mul_le_mul_of_nonneg_right hB ht0
      have h2 := mul_le_mul_of_nonneg_left hts (mul_nonneg hβ h0)
      have e2 : β / 2 * (s * h) = β * h * s / 2 := by ring
      rw [e, e2]
      linarith
    have h3 := hest N hN'
    have e3 : (1 + β / 2) * s * h = s * h + β / 2 * (s * h) := by ring
    rw [e3]
    linarith

namespace WeightedFamily

section DensityParam

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Lemma 5.1, inequality (29), with a general constant: for a `λ`-sparse family (`λ ≥ 0`) and
subspaces `V(u, w)` with `B = E_{u,w} dim V(u, w) ≤ β h(𝒬)` (`β ≥ 0`),
`A = E_{u,w} s_{V(u,w)}(Q_u, Q_w) ≤ (1 + β/2) √λ h(𝒬)`. -/
theorem averaged_density_sqrt_param [Fintype V] {lam β : ℝ} (Q : WeightedFamily V)
    (hsp : Q.IsSparse lam) (hlam : 0 ≤ lam) (hβ : 0 ≤ β)
    (Vf : Q.index → Q.index → Submodule (ZMod 2) V)
    (hB : ∑ u, Q.weights u * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ) ≤
      β * Q.meanEntropy) :
    ∑ u, Q.weights u * ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf u w) ≤
      (1 + β / 2) * Real.sqrt lam * Q.meanEntropy :=
  density_sqrt_arith_param Q.meanEntropy_nonneg hlam hβ hB
    (fun N hN => Q.averaged_density_estimate hsp hlam Vf N hN)

end DensityParam

section PosteriorConst

variable {V : Type} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

/-- The subspace `W(x, y)` given by the Marton step with constant `C` for the pair
`(Q_x, Q_y)`. -/
noncomputable def postSubspaceConst (P : WeightedFamily V) {C : ℝ} (hM : MartonInputConst C V)
    (hC : 0 ≤ C) (x y : P.index × P.index × V) : Submodule (ZMod 2) V :=
  Classical.choose
    (interaction_le_subspace_add_increment_const hM hC (P.postLawAt x) (P.postLawAt y))

theorem postSubspaceConst_spec (P : WeightedFamily V) {C : ℝ} (hM : MartonInputConst C V)
    (hC : 0 ≤ C) (x y : P.index × P.index × V) :
    interaction (P.postLawAt x) (P.postLawAt y) ≤
        subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) +
          2 * C * entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) ∧
      (Module.finrank (ZMod 2) (P.postSubspaceConst hM hC x y) : ℝ) ≤
        (1 + 2 * C) * (entropyBits (P.postLawAt x) + entropyBits (P.postLawAt y)) :=
  Classical.choose_spec
    (interaction_le_subspace_add_increment_const hM hC (P.postLawAt x) (P.postLawAt y))

/-- `e(Post 𝒫) ≤ ∑_{x,y} m(x) m(y) s_{W(x,y)}(Q_x, Q_y) + 6C · J`. -/
theorem posterior_interaction_le_subspace_const (P : WeightedFamily V) {C : ℝ}
    (hM : MartonInputConst C V) (hC : 0 ≤ C) :
    P.posterior.meanInteraction ≤
      ∑ x, ∑ y, P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) +
        6 * C * P.fourSampleJ := by
  have hpd := P.posterior_doubling
  have hterm : ∀ x y, P.postPairTerm x y ≤
      P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) +
        2 * C * (P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y))) := by
    intro x y
    have h := (P.postSubspaceConst_spec hM hC x y).1
    have hm : 0 ≤ P.postMass x * P.postMass y :=
      mul_nonneg (P.postMass_nonneg x) (P.postMass_nonneg y)
    unfold postPairTerm
    calc P.postMass x * P.postMass y * interaction (P.postLawAt x) (P.postLawAt y)
        ≤ P.postMass x * P.postMass y *
            (subspaceInteraction (P.postLawAt x) (P.postLawAt y)
                (P.postSubspaceConst hM hC x y) +
              2 * C * entropyIncrement (conv (P.postLawAt x) (P.postLawAt y))) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  have hsum : ∑ x, ∑ y, P.postPairTerm x y ≤
      ∑ x, ∑ y, (P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) +
        2 * C * (P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)))) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hsplit : ∑ x, ∑ y, (P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) +
        2 * C * (P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)))) =
      ∑ x, ∑ y, P.postMass x * P.postMass y *
          subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) +
        2 * C * ∑ x, ∑ y, P.postMass x * P.postMass y *
          entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h2C : 2 * C * ∑ x, ∑ y, P.postMass x * P.postMass y *
        entropyIncrement (conv (P.postLawAt x) (P.postLawAt y)) ≤
      2 * C * (3 * P.fourSampleJ) := mul_le_mul_of_nonneg_left hpd (by linarith)
  rw [meanInteraction_posterior_full]
  linarith

/-- Equation (38) with constant `C`:
`∑_{x,y} m(x) m(y) dim W(x, y) ≤ 2 (1 + 2C) h(Post 𝒫)`. -/
theorem posterior_mean_dim_le_const (P : WeightedFamily V) {C : ℝ} (hM : MartonInputConst C V)
    (hC : 0 ≤ C) :
    ∑ x, ∑ y, P.postMass x * P.postMass y *
        (Module.finrank (ZMod 2) (P.postSubspaceConst hM hC x y) : ℝ) ≤
      2 * (1 + 2 * C) * P.posterior.meanEntropy := by
  have hterm : ∀ x y, P.postMass x * P.postMass y *
      (Module.finrank (ZMod 2) (P.postSubspaceConst hM hC x y) : ℝ) ≤
      (1 + 2 * C) * (P.postMass x * entropyBits (P.postLawAt x) * P.postMass y) +
        (1 + 2 * C) * (P.postMass x * (P.postMass y * entropyBits (P.postLawAt y))) := by
    intro x y
    have h := (P.postSubspaceConst_spec hM hC x y).2
    have hm : 0 ≤ P.postMass x * P.postMass y :=
      mul_nonneg (P.postMass_nonneg x) (P.postMass_nonneg y)
    calc P.postMass x * P.postMass y *
          (Module.finrank (ZMod 2) (P.postSubspaceConst hM hC x y) : ℝ)
        ≤ P.postMass x * P.postMass y *
            ((1 + 2 * C) * (entropyBits (P.postLawAt x) + entropyBits (P.postLawAt y))) :=
          mul_le_mul_of_nonneg_left h hm
      _ = _ := by ring
  have hsum : ∑ x, ∑ y, P.postMass x * P.postMass y *
        (Module.finrank (ZMod 2) (P.postSubspaceConst hM hC x y) : ℝ) ≤
      ∑ x, ∑ y, ((1 + 2 * C) * (P.postMass x * entropyBits (P.postLawAt x) * P.postMass y) +
        (1 + 2 * C) * (P.postMass x * (P.postMass y * entropyBits (P.postLawAt y)))) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  have hs : ∑ x, ∑ y, ((1 + 2 * C) * (P.postMass x * entropyBits (P.postLawAt x) * P.postMass y) +
        (1 + 2 * C) * (P.postMass x * (P.postMass y * entropyBits (P.postLawAt y)))) =
      (1 + 2 * C) * ((∑ x, P.postMass x * entropyBits (P.postLawAt x)) * ∑ y, P.postMass y) +
        (1 + 2 * C) *
          ((∑ x, P.postMass x) * ∑ y, P.postMass y * entropyBits (P.postLawAt y)) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [P.sum_postMass_mul_entropy, P.postMass_sum] at hs
  rw [meanEntropy_posterior]
  linarith

/-- **Lemma 7.1 with Marton constant `C ≥ 0`**: if the posterior family `𝒬 = Post 𝒫` is
`ρ`-sparse (`ρ ≥ 0`), then `e(𝒬) ≤ 6C · J + (2 + 2C) √ρ · e(𝒫)`. At `C = 6` this is
`36 J + 14 √ρ δH`. -/
theorem sparse_posterior_estimate_const (P : WeightedFamily V) {C : ℝ}
    (hM : MartonInputConst C V) (hC : 0 ≤ C) {rho : ℝ}
    (hsp : P.posterior.IsSparse rho) (hrho : 0 ≤ rho) :
    P.posterior.meanInteraction ≤
      6 * C * P.fourSampleJ + (2 + 2 * C) * Real.sqrt rho * P.meanInteraction := by
  have h1 := P.posterior_interaction_le_subspace_const hM hC
  have hB := P.posterior_mean_dim_le_const hM hC
  have hBQ := (posterior_double_sum P fun x y =>
    (Module.finrank (ZMod 2) (P.postSubspaceConst hM hC x y) : ℝ)).le.trans hB
  have hβ : (0 : ℝ) ≤ 2 * (1 + 2 * C) := by linarith
  have hA := P.posterior.averaged_density_sqrt_param hsp hrho hβ
    (fun u w => P.postSubspaceConst hM hC (Subtype.val u) (Subtype.val w)) hBQ
  have hA' : ∑ x, ∑ y, P.postMass x * P.postMass y *
        subspaceInteraction (P.postLawAt x) (P.postLawAt y) (P.postSubspaceConst hM hC x y) ≤
      (1 + 2 * (1 + 2 * C) / 2) * Real.sqrt rho * P.posterior.meanEntropy :=
    (posterior_double_sum P fun x y => subspaceInteraction (P.postLawAt x) (P.postLawAt y)
      (P.postSubspaceConst hM hC x y)).symm.le.trans hA
  rw [meanEntropy_posterior] at hA'
  have e : (1 + 2 * (1 + 2 * C) / 2) * Real.sqrt rho * P.meanInteraction =
      (2 + 2 * C) * Real.sqrt rho * P.meanInteraction := by ring
  rw [e] at hA'
  linarith

end PosteriorConst

end WeightedFamily

/-- The arithmetic of Lemma 8.1 with Marton constant `C ≥ 0`. With `H > 0`, `δ > 0`,
`32 (1 + C)² λ ≤ δ²`, `J ≥ 0`, `e(ℛ) + e(𝒬) = 2δH + J` (Lemma 6.1) and
`e(𝒬) ≤ 6C · J + (2 + 2C) √(2λ) δH` (Lemma 7.1), either
`e(ℛ) ≥ (δ + δ²/(24C + 4))(2 − δ)H` or `e(𝒬) ≥ (δ + δ²/(24C + 4)) δH`. -/
theorem ratio_growth_arith_const {C H δ eR eQ J lam : ℝ} (hC : 0 ≤ C) (hH : 0 < H)
    (hδ0 : 0 < δ) (hlam : 0 ≤ lam) (hsmall : 32 * (1 + C) ^ 2 * lam ≤ δ ^ 2) (hJ : 0 ≤ J)
    (hsplit : eR + eQ = 2 * (δ * H) + J)
    (h7 : eQ ≤ 6 * C * J + (2 + 2 * C) * Real.sqrt (2 * lam) * (δ * H)) :
    (δ + δ ^ 2 / (24 * C + 4)) * ((2 - δ) * H) ≤ eR ∨
      (δ + δ ^ 2 / (24 * C + 4)) * (δ * H) ≤ eQ := by
  have ha : (0 : ℝ) < 24 * C + 4 := by linarith
  have hs0 : 0 ≤ Real.sqrt (2 * lam) := Real.sqrt_nonneg _
  have hss : Real.sqrt (2 * lam) * Real.sqrt (2 * lam) = 2 * lam :=
    Real.mul_self_sqrt (by linarith)
  -- `(2 + 2C) √(2λ) ≤ δ/2`
  have hc : (2 + 2 * C) * Real.sqrt (2 * lam) ≤ δ / 2 := by
    by_contra h
    push_neg at h
    have hpos : 0 < δ / 2 := by linarith
    have h2 : δ / 2 * (δ / 2) <
        (2 + 2 * C) * Real.sqrt (2 * lam) * ((2 + 2 * C) * Real.sqrt (2 * lam)) :=
      mul_lt_mul'' h h hpos.le hpos.le
    have e : (2 + 2 * C) * Real.sqrt (2 * lam) * ((2 + 2 * C) * Real.sqrt (2 * lam)) =
        (2 + 2 * C) ^ 2 * (Real.sqrt (2 * lam) * Real.sqrt (2 * lam)) := by ring
    rw [e, hss] at h2
    have e2 : (2 + 2 * C) ^ 2 * (2 * lam) = 32 * (1 + C) ^ 2 * lam / 4 := by ring
    rw [e2] at h2
    have e3 : δ / 2 * (δ / 2) = δ ^ 2 / 4 := by ring
    rw [e3] at h2
    linarith
  have hδH : 0 ≤ δ * H := mul_nonneg hδ0.le hH.le
  have hA : (2 + 2 * C) * Real.sqrt (2 * lam) * (δ * H) ≤ δ / 2 * (δ * H) :=
    mul_le_mul_of_nonneg_right hc hδH
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = δ ^ 2 / (24 * C + 4) := ⟨_, rfl⟩
  rw [← hg]
  have hgpos : 0 < g := by
    rw [hg]
    exact div_pos (pow_pos hδ0 2) ha
  have hag : (24 * C + 4) * g = δ ^ 2 := by
    rw [hg, mul_comm, div_mul_cancel₀ _ ha.ne']
  have hagH : (24 * C + 4) * (g * H) = δ ^ 2 * H := by
    rw [← mul_assoc, hag]
  have hpos3 : 0 < g * δ * H := mul_pos (mul_pos hgpos hδ0) hH
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- `J < 2 g H`
  have hJ2 : J < 2 * (g * H) := by
    have e1 : (δ + g) * ((2 - δ) * H) + (δ + g) * (δ * H) = 2 * (δ * H) + 2 * (g * H) := by ring
    linarith
  have h6CJ : 6 * C * J ≤ 6 * C * (2 * (g * H)) :=
    mul_le_mul_of_nonneg_left hJ2.le (by linarith)
  have e4 : (δ + g) * ((2 - δ) * H) = 2 * (δ * H) - δ ^ 2 * H + 2 * (g * H) - g * δ * H := by
    ring
  have e5 : δ / 2 * (δ * H) = δ ^ 2 * H / 2 := by ring
  have e6 : 6 * C * (2 * (g * H)) = (24 * C + 4) * (g * H) / 2 - 2 * (g * H) := by ring
  rw [e4] at h1
  rw [e5] at hA
  rw [e6, hagH] at h6CJ
  linarith

namespace WeightedFamily

/-- **Lemma 8.1 with Marton constant `C ≥ 0`**, for all finite F₂-spaces in `Type`: growth
`d + d²/(24C + 4)` under the hypothesis `32 (1 + C)² λ ≤ d²`. -/
theorem ratio_growth_of_marton_const {C : ℝ} (hM : MartonBoundConst.{0} C) (hC : 0 ≤ C) :
    RatioGrowthConst.{0} (24 * C + 4) (32 * (1 + C) ^ 2) := by
  intro W _ _ _ lam P hlam hsp hpos hd hsmall
  have ha : (0 : ℝ) < 24 * C + 4 := by linarith
  obtain ⟨G, hGpos, hratio, hsp2, hsp4⟩ := P.ratio_preserving_sparsification_proof lam hsp hpos
  haveI : Finite (W ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (W ⧸ G) := Fintype.ofFinite _
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = P.meanInteraction / P.meanEntropy := ⟨_, rfl⟩
  rw [← hd_def] at hd hsmall ⊢
  rw [← hd_def] at hratio
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = (P.quotient G).meanEntropy := ⟨_, rfl⟩
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ,
      δ = (P.quotient G).meanInteraction / (P.quotient G).meanEntropy := ⟨_, rfl⟩
  rw [← hδ_def] at hratio
  rw [← hH_def] at hGpos
  have hne : (P.quotient G).meanEntropy ≠ 0 := by
    rw [← hH_def]
    exact hGpos.ne'
  have heP : (P.quotient G).meanInteraction = δ * H := by
    rw [hδ_def, hH_def]
    field_simp
  have hδ0 : 0 < δ := lt_of_lt_of_le hd hratio
  have hle : (P.quotient G).meanInteraction ≤ (P.quotient G).meanEntropy :=
    (P.quotient G).meanInteraction_le
  rw [heP, ← hH_def] at hle
  have hδ1 : δ ≤ 1 := by nlinarith [hle, hGpos]
  have hR : (P.quotient G).convFamily.meanEntropy = (2 - δ) * H := by
    rw [WeightedFamily.meanEntropy_convFamily, heP, ← hH_def]
    ring
  have hQ : (P.quotient G).posterior.meanEntropy = δ * H := by
    rw [meanEntropy_posterior, heP]
  have hsplit := (P.quotient G).four_sample_splitting
  rw [heP] at hsplit
  have hJ := (P.quotient G).fourSampleJ_nonneg
  have h7 := (P.quotient G).sparse_posterior_estimate_const (hM (W ⧸ G)) hC
    (posterior_closure (2 * lam) (P.quotient G) hsp2) (by linarith)
  rw [heP] at h7
  have hdd : d ^ 2 ≤ δ ^ 2 := by nlinarith [hratio, hd]
  have hsmall' : 32 * (1 + C) ^ 2 * lam ≤ δ ^ 2 := hsmall.trans hdd
  have hgrow : d + d ^ 2 / (24 * C + 4) ≤ δ + δ ^ 2 / (24 * C + 4) := by
    have h := div_le_div_of_nonneg_right hdd ha.le
    linarith
  have hRpos : 0 < (2 - δ) * H := by
    have h2δ : 0 < 2 - δ := by linarith
    exact mul_pos h2δ hGpos
  have hQpos : 0 < δ * H := mul_pos hδ0 hGpos
  rcases ratio_growth_arith_const hC hGpos hδ0 hlam.le hsmall' hJ hsplit h7 with hcase | hcase
  · refine ⟨{ carrier := W ⧸ G, fam := (P.quotient G).convFamily }, hsp4, ?_, ?_⟩
    · show 0 < (P.quotient G).convFamily.meanEntropy
      rw [hR]
      exact hRpos
    · show d + d ^ 2 / (24 * C + 4) ≤
        (P.quotient G).convFamily.meanInteraction / (P.quotient G).convFamily.meanEntropy
      rw [hR, le_div_iff₀ hRpos]
      calc (d + d ^ 2 / (24 * C + 4)) * ((2 - δ) * H)
          ≤ (δ + δ ^ 2 / (24 * C + 4)) * ((2 - δ) * H) :=
            mul_le_mul_of_nonneg_right hgrow hRpos.le
        _ ≤ _ := hcase
  · refine ⟨{ carrier := W ⧸ G, fam := (P.quotient G).posterior },
      (P.quotient G).posterior.isSparse_of_le (posterior_closure (2 * lam) (P.quotient G) hsp2)
        (by linarith), ?_, ?_⟩
    · show 0 < (P.quotient G).posterior.meanEntropy
      rw [hQ]
      exact hQpos
    · show d + d ^ 2 / (24 * C + 4) ≤
        (P.quotient G).posterior.meanInteraction / (P.quotient G).posterior.meanEntropy
      rw [hQ, le_div_iff₀ hQpos]
      calc (d + d ^ 2 / (24 * C + 4)) * (δ * H)
          ≤ (δ + δ ^ 2 / (24 * C + 4)) * (δ * H) :=
            mul_le_mul_of_nonneg_right hgrow hQpos.le
        _ ≤ _ := hcase

end WeightedFamily

/-- **Universe transport of Lemma 8.1 with constants** (item D10 for `RatioGrowthConst`). -/
theorem ratioGrowthConst_lift {a b : ℝ} (h0 : RatioGrowthConst.{0} a b) :
    RatioGrowthConst.{u} a b := by
  intro W _ _ _ lam P hlam hsp hpos hd hsmall
  have hne : Nonempty (W ≃ₗ[ZMod 2] F2Vec (Module.finrank (ZMod 2) W)) :=
    ⟨(Module.finBasis (ZMod 2) W).equivFun⟩
  obtain ⟨e⟩ := hne
  obtain ⟨F, hFsp, hFpos, hFr⟩ := h0 (F2Vec (Module.finrank (ZMod 2) W)) lam
    (P.mapLinearEquiv e) hlam (P.isSparse_mapLinearEquiv e hsp)
    (by rw [P.meanEntropy_mapLinearEquiv e]; exact hpos)
    (by rw [P.meanInteraction_mapLinearEquiv e, P.meanEntropy_mapLinearEquiv e]; exact hd)
    (by rw [P.meanInteraction_mapLinearEquiv e, P.meanEntropy_mapLinearEquiv e]; exact hsmall)
  rw [P.meanInteraction_mapLinearEquiv e, P.meanEntropy_mapLinearEquiv e] at hFr
  have hne' : Nonempty (F.carrier ≃ₗ[ZMod 2] ULift.{u} F.carrier) := ⟨ULift.moduleEquiv.symm⟩
  obtain ⟨E⟩ := hne'
  refine ⟨{ carrier := ULift.{u} F.carrier, fam := F.fam.mapLinearEquiv E }, ?_, ?_, ?_⟩
  · exact F.fam.isSparse_mapLinearEquiv E hFsp
  · show 0 < (F.fam.mapLinearEquiv E).meanEntropy
    rw [F.fam.meanEntropy_mapLinearEquiv E]
    exact hFpos
  · show _ ≤ (F.fam.mapLinearEquiv E).meanInteraction / (F.fam.mapLinearEquiv E).meanEntropy
    rw [F.fam.meanInteraction_mapLinearEquiv E, F.fam.meanEntropy_mapLinearEquiv E]
    exact hFr

/-- The constant of Theorem 8.2 as a function of the Marton constant `C`:
`K(C) = rigidityConst (24C + 4) (32 (1 + C)²) = 48C + 17 + 2 log₂(1 + C)`. -/
noncomputable def martonRigidityConst (C : ℝ) : ℝ :=
  rigidityConst (24 * C + 4) (32 * (1 + C) ^ 2)

/-- `32 (1 + C)² ≥ 4` for `C ≥ 0`. -/
theorem four_le_marton_threshold {C : ℝ} (hC : 0 ≤ C) : (4 : ℝ) ≤ 32 * (1 + C) ^ 2 := by
  nlinarith [sq_nonneg C]

/-- Closed form: `K(C) = 48C + 17 + 2 log₂(1 + C)` for `C ≥ 0`. -/
theorem martonRigidityConst_eq {C : ℝ} (hC : 0 ≤ C) :
    martonRigidityConst C = 48 * C + 17 + 2 * Real.logb 2 (1 + C) := by
  have h1C : (0 : ℝ) < 1 + C := by linarith
  have h32 : Real.logb 2 (32 : ℝ) = 5 := by
    have e : (32 : ℝ) = (2 : ℝ) ^ (5 : ℕ) := by norm_num
    rw [e, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hlog : Real.logb 2 (32 * (1 + C) ^ 2) = 5 + 2 * Real.logb 2 (1 + C) := by
    rw [Real.logb_mul (by norm_num) (pow_pos h1C 2).ne', h32, Real.logb_pow]
    push_cast
    ring
  unfold martonRigidityConst rigidityConst
  rw [hlog]
  ring

/-- `K(C) > 0` for `C ≥ 0`. -/
theorem martonRigidityConst_pos {C : ℝ} (hC : 0 ≤ C) : 0 < martonRigidityConst C :=
  rigidityConst_pos (by linarith) (four_le_marton_threshold hC)

/-- At the paper's value `C = 6`: `K(6) = 305 + 2 log₂ 7 < 311`. -/
theorem martonRigidityConst_six_lt : martonRigidityConst 6 < 311 := by
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    have e : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [e, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h7 : Real.logb 2 (7 : ℝ) < Real.logb 2 (8 : ℝ) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [martonRigidityConst_eq (by norm_num : (0 : ℝ) ≤ 6)]
  have e : (1 : ℝ) + 6 = 7 := by norm_num
  rw [e]
  linarith

/-- **Lemma 8.1 with Marton constant `C`** in every universe. -/
theorem ratio_growth_of_marton_const_univ {C : ℝ} (hM : MartonBoundConst.{0} C) (hC : 0 ≤ C) :
    RatioGrowthConst.{u} (24 * C + 4) (32 * (1 + C) ^ 2) :=
  ratioGrowthConst_lift (WeightedFamily.ratio_growth_of_marton_const hM hC)

/-- **Theorem 8.2 with constant `K(C)`** in every universe, from the entropic Marton bound with
constant `C ≥ 0` on spaces in `Type`. -/
theorem weighted_family_rigidity_of_marton_const {C : ℝ} (hM : MartonBoundConst.{0} C)
    (hC : 0 ≤ C) : WeightedFamilyRigidityConst.{u} (martonRigidityConst C) :=
  weighted_family_rigidity_of_growth_param (by linarith) (four_le_marton_threshold hC)
    (ratio_growth_of_marton_const_univ hM hC)

/-- The conclusion of **Theorem 1.1 with exponent `K(C)(1+ε)/ε`**, from the entropic Marton
bound with constant `C ≥ 0` on spaces in `Type`. -/
theorem exponential_entropy_quotient_of_marton_const {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {C : ℝ} (hM : MartonBoundConst.{0} C) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤
        (2 : ℝ) ^ (martonRigidityConst C * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_rigidity_const (martonRigidityConst_pos hC)
    (weighted_family_rigidity_of_marton_const hM hC) ε hε X

/-- The conclusion of **Theorem 1.2 with constant `K(C)`**, from the entropic Marton bound with
constant `C ≥ 0` on spaces in `Type`. -/
theorem sparse_rigidity_of_marton_const {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] {C : ℝ} (hM : MartonBoundConst.{0} C) (hC : 0 ≤ C) (lam : ℝ)
    (hlam : 0 < lam ∧ lam < 1) (Z : PMF V) (hsparse : IsSparse lam Z)
    (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤
      min 1 (martonRigidityConst C / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_of_family_rigidity_const (weighted_family_rigidity_of_marton_const hM hC) lam
    hlam Z hsparse hpos

end EntropyLean
