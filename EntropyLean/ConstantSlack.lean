import Mathlib
import EntropyLean.RigidityArithParam
import EntropyLean.UniverseTransport
import EntropyLean.MartonConst

/-!
# Slack in the constant 320 (roadmap item G3)

The paper proves Theorem 8.2 with the constant 320: its arithmetic (43) bounds
`d · log₂(1/λ)` by `298 + (log₂ 1600 + 2) d + 2 d log₂(1/d) < 312 < 320`, estimating the last two
terms separately. Estimating them together (`rigidity_arith_param`, item G1: for `d ≤ 1` they are
at most `log₂ 1600 + 2`, the value at `d = 1`) gives the constant

  `c₀ = rigidityConst 148 1600 = 300 + log₂ 1600`, with `310 < c₀ < 311`.

Nothing else changes: Lemma 8.1 is used with the paper's constants 148 and 1600.

Proved here:

* `rigidityConst_paper_eq`, `rigidityConst_paper_gt`: `c₀ = 300 + log₂ 1600 > 310`
  (`rigidityConst_paper_lt : c₀ < 311` is in `EntropyLean/RigidityArithParam.lean`);
* `weighted_family_rigidity_slack_of_growth`: Theorem 8.2 with constant `c₀` from Lemma 8.1
  (`RatioGrowth`), and with the integer constant 311 (`weighted_family_rigidity_311_of_growth`);
* with the entropic Marton bound (35) on spaces in `Type` (`MartonBound.{0}`) as the only
  hypothesis, in every universe: Theorem 8.2 with 311 (`weighted_family_rigidity_311_of_marton`),
  the conclusion of Theorem 1.1 with `dim G ≤ 2^(311(1+ε)/ε) H(X)`
  (`exponential_entropy_quotient_311_of_marton`), and the conclusion of Theorem 1.2 with
  `min(1, 311 / log₂(1/λ))` (`sparse_rigidity_311_of_marton`);
* the same three under a Marton bound with any constant `C ≤ 6`
  (`exponential_entropy_quotient_311_of_marton_const` and its companions).

What this file does NOT prove: the entropic Marton bound (35), which stays a hypothesis, so none
of Theorems 1.1, 1.2, 8.2 is proved unconditionally. It does not prove that `c₀` is the least
constant the hypothesis of (43) allows (on paper the supremum of `d · log₂(1/λ)` under that
hypothesis is `c₀`, approached as `d ↑ 1`; this is not formalized). No constant below 311 is
claimed for Theorem 1.1.
-/

universe u

namespace EntropyLean

/-- `c₀ = rigidityConst 148 1600 = 300 + log₂ 1600`. -/
theorem rigidityConst_paper_eq : rigidityConst 148 1600 = 300 + Real.logb 2 1600 := by
  unfold rigidityConst
  ring

/-- `c₀ > 310`, since `1600 > 2^10`. So 311 is the least integer constant this arithmetic
gives. -/
theorem rigidityConst_paper_gt : 310 < rigidityConst 148 1600 := by
  have h10 : Real.logb 2 ((2 : ℝ) ^ (10 : ℕ)) = 10 := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have hlt : Real.logb 2 ((2 : ℝ) ^ (10 : ℕ)) < Real.logb 2 1600 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [rigidityConst_paper_eq]
  linarith

/-- **Theorem 8.2 with constant `c₀ = 300 + log₂ 1600`**, from Lemma 8.1 as stated in the
paper. -/
theorem weighted_family_rigidity_slack_of_growth (hgrowth : RatioGrowth.{u}) :
    WeightedFamilyRigidityConst.{u} (rigidityConst 148 1600) :=
  weighted_family_rigidity_of_growth_param (by norm_num) (by norm_num)
    (ratioGrowthConst_paper_iff.mpr hgrowth)

/-- **Theorem 8.2 with constant 311**, from Lemma 8.1 as stated in the paper. -/
theorem weighted_family_rigidity_311_of_growth (hgrowth : RatioGrowth.{u}) :
    WeightedFamilyRigidityConst.{u} 311 :=
  (weighted_family_rigidity_slack_of_growth hgrowth).mono rigidityConst_paper_lt.le

/-- **Theorem 8.2 with constant 311** in every universe, from the entropic Marton bound (35) on
spaces in `Type`. -/
theorem weighted_family_rigidity_311_of_marton (hM : MartonBound.{0}) :
    WeightedFamilyRigidityConst.{u} 311 :=
  weighted_family_rigidity_311_of_growth (ratio_growth_of_marton_univ hM)

/-- The conclusion of **Theorem 1.1 with 311 in place of 320**, with the entropic Marton bound
(35) on spaces in `Type` as the only hypothesis. -/
theorem exponential_entropy_quotient_311_of_marton {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hM : MartonBound.{0}) (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (311 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_rigidity_const (by norm_num)
    (weighted_family_rigidity_311_of_marton hM) ε hε X

/-- The conclusion of **Theorem 1.2 with 311 in place of 320**, with the entropic Marton bound
(35) on spaces in `Type` as the only hypothesis. -/
theorem sparse_rigidity_311_of_marton {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (hM : MartonBound.{0}) (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (Z : PMF V)
    (hsparse : IsSparse lam Z) (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (311 / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_of_family_rigidity_const (weighted_family_rigidity_311_of_marton hM) lam hlam Z
    hsparse hpos

/-- Theorem 8.2 with constant 311 from a Marton bound with any constant `C ≤ 6`. -/
theorem weighted_family_rigidity_311_of_marton_const {C : ℝ} (hM : MartonBoundConst.{0} C)
    (hC : C ≤ 6) : WeightedFamilyRigidityConst.{u} 311 :=
  weighted_family_rigidity_311_of_marton (hM.toMartonBound hC)

/-- The conclusion of Theorem 1.1 with 311, from a Marton bound with any constant `C ≤ 6`. -/
theorem exponential_entropy_quotient_311_of_marton_const {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {C : ℝ} (hM : MartonBoundConst.{0} C) (hC : C ≤ 6)
    (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (311 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_311_of_marton (hM.toMartonBound hC) ε hε X

/-- The conclusion of Theorem 1.2 with 311, from a Marton bound with any constant `C ≤ 6`. -/
theorem sparse_rigidity_311_of_marton_const {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] {C : ℝ} (hM : MartonBoundConst.{0} C) (hC : C ≤ 6) (lam : ℝ)
    (hlam : 0 < lam ∧ lam < 1) (Z : PMF V) (hsparse : IsSparse lam Z)
    (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (311 / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_311_of_marton (hM.toMartonBound hC) lam hlam Z hsparse hpos

end EntropyLean
