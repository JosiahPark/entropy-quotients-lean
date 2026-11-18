import EntropyLean.MathlibForPFR
import EntropyLean.RatioGrowth
import EntropyLean.RigidityConst

/-!
# Parametric iteration arithmetic and Theorem 8.2 with explicit constant (roadmap item G1)

Section 8 of arXiv:2610.38525 turns Lemma 8.1 into Theorem 8.2 by the arithmetic (42)–(43). The
numbers 148 and 1600 there are the two constants of Lemma 8.1: growth `d ↦ d + d²/148` under the
hypothesis `1600 λ ≤ d²`. This file redoes that step with both constants as real parameters
`a` (growth `d + d²/a`) and `b` (hypothesis `b λ ≤ d²`).

* `rigidityConst a b = 2(a + 1) + 2 + log₂ b`: the resulting constant of Theorem 8.2.
* `inv_ratio_step_param` (42): `d' ≥ d + d²/a` and `d ≤ 1` give `1/d' ≤ 1/d − 1/(a + 1)`.
* `rigidity_arith_param` (from (43)): if `0 < d ≤ 1`, `b ≥ 4` and
  `λ > d² / (b · 4^⌈(a+1)/d⌉)`, then `d · log₂(1/λ) < rigidityConst a b`.
* `RatioGrowthConst a b`: the statement of Lemma 8.1 with constants `a`, `b`
  (`RatioGrowth` is `RatioGrowthConst 148 1600`).
* `weighted_family_rigidity_of_growth_param`: `RatioGrowthConst a b` implies Theorem 8.2 with
  constant `rigidityConst a b` (`WeightedFamilyRigidityConst`), for `a > 0`, `b ≥ 4`.
* `exponential_entropy_quotient_of_growth_param`, `sparse_rigidity_of_growth_param`: the
  conclusions of Theorems 1.1 and 1.2 with that constant.
* `rigidityConst_paper_lt`: `rigidityConst 148 1600 = 300 + log₂ 1600 < 311`, and
  `rigidity_arith_param_six`: the hypothesis of item D1 gives `d · log₂(1/λ) < 311`, which
  recovers and sharpens `rigidity_iteration_bound` (`< 320`).

The bound uses `−d log d ≤ 1 − d` and `log b + 2 log 2 ≥ 2` (from `b ≥ 4`) to absorb the terms
`d log₂ b + 2d + 2d log₂(1/d)` into `log₂ b + 2`.

What this file does NOT prove: Lemma 8.1 for any constants (`RatioGrowthConst a b` is only a
hypothesis), and nothing about how `a`, `b` depend on the constant of the entropic Marton bound
(35) beyond the paper's values `a = 148`, `b = 1600`.
-/

universe u

namespace EntropyLean

open Real

/-- The constant of Theorem 8.2 given by the iteration arithmetic (42)–(43) when Lemma 8.1 holds
with growth `d + d²/a` under the hypothesis `b λ ≤ d²`. -/
noncomputable def rigidityConst (a b : ℝ) : ℝ := 2 * (a + 1) + 2 + Real.logb 2 b

/-- `log 4 = 2 log 2`. -/
theorem log_four_eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, Real.log_pow]
  push_cast
  ring

/-- Equation (42) with growth constant `a`: one growth step `d' ≥ d + d²/a` with `d ≤ 1` lowers
`1/d` by at least `1/(a + 1)`. -/
theorem inv_ratio_step_param {a d d' : ℝ} (ha : 0 < a) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hstep : d + d ^ 2 / a ≤ d') : 1 / d' ≤ 1 / d - 1 / (a + 1) := by
  have hpos : 0 < d + d ^ 2 / a := add_pos hd0 (div_pos (pow_pos hd0 2) ha)
  have had : (0 : ℝ) < a + d := by linarith
  have h1 : 1 / d' ≤ 1 / (d + d ^ 2 / a) := one_div_le_one_div_of_le hpos hstep
  have ha' : a ≠ 0 := ha.ne'
  have hd' : d ≠ 0 := hd0.ne'
  have had' : a + d ≠ 0 := had.ne'
  have e : d + d ^ 2 / a = d * (a + d) / a := by
    rw [eq_div_iff ha', add_mul, div_mul_cancel₀ _ ha']
    ring
  have h2 : 1 / (d + d ^ 2 / a) = 1 / d - 1 / (a + d) := by
    rw [e, one_div_div, div_sub_div _ _ hd' had',
      div_eq_div_iff (mul_ne_zero hd' had') (mul_ne_zero hd' had')]
    ring
  have h3 : 1 / (a + 1) ≤ 1 / (a + d) := one_div_le_one_div_of_le had (by linarith)
  linarith

/-- The arithmetic of (43) with constants `a`, `b` and an explicit step count
`N ≤ (a + 1)/d + 1`. -/
theorem rigidity_arith_param_aux {a b d lam : ℝ} {N : ℕ} (hb : 4 ≤ b) (hd0 : 0 < d)
    (hd1 : d ≤ 1) (hN : (N : ℝ) ≤ (a + 1) / d + 1) (hlam : d ^ 2 / (b * (4 : ℝ) ^ N) < lam) :
    d * Real.logb 2 (1 / lam) < rigidityConst a b := by
  have hL : (1 : ℝ) / 2 ≤ Real.log 2 := half_le_log_two
  have hLpos : 0 < Real.log 2 := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hd2 : 0 < d ^ 2 := pow_pos hd0 2
  have h4N : (0 : ℝ) < (4 : ℝ) ^ N := pow_pos (by norm_num) N
  have hA : (0 : ℝ) < b * (4 : ℝ) ^ N := mul_pos hb0 h4N
  have hlow : 0 < d ^ 2 / (b * (4 : ℝ) ^ N) := div_pos hd2 hA
  have hlam0 : 0 < lam := lt_trans hlow hlam
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = b * (4 : ℝ) ^ N / d ^ 2 := ⟨_, rfl⟩
  have hYpos : 0 < Y := by rw [hY]; exact div_pos hA hd2
  -- `1/λ < Y`
  have hinv : 1 / lam < Y := by
    rw [one_div_lt hlam0 hYpos, hY, one_div_div]
    exact hlam
  have hlogb : Real.logb 2 (1 / lam) < Real.logb 2 Y :=
    Real.logb_lt_logb (by norm_num) (one_div_pos.mpr hlam0) hinv
  -- `log Y = log b + N · 2 log 2 − 2 log d`
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := log_four_eq
  have hlogY : Real.log Y = Real.log b + (N : ℝ) * (2 * Real.log 2) - 2 * Real.log d := by
    rw [hY, Real.log_div (ne_of_gt hA) (ne_of_gt hd2),
      Real.log_mul (ne_of_gt hb0) (ne_of_gt h4N), Real.log_pow, Real.log_pow, h4]
    push_cast
    ring
  -- bounds
  have hdN : d * (N : ℝ) ≤ a + 1 + d := by
    have h' : (N : ℝ) - 1 ≤ (a + 1) / d := by linarith
    rw [le_div_iff₀ hd0] at h'
    linarith
  have hlogb4 : 2 * Real.log 2 ≤ Real.log b := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hb
    rw [h4] at h
    exact h
  have hC : Real.log 2 * (d * (N : ℝ)) ≤ Real.log 2 * (a + 1 + d) :=
    mul_le_mul_of_nonneg_left hdN hLpos.le
  have hE : d * (-Real.log d) ≤ 1 - d := neg_mul_log_le_one_sub hd0
  have hprod : 0 ≤ (1 - d) * (Real.log b + 2 * Real.log 2 - 2) :=
    mul_nonneg (by linarith) (by linarith)
  have key : d * Real.log Y ≤ (2 * (a + 1) + 2) * Real.log 2 + Real.log b := by
    rw [hlogY]
    nlinarith [hC, hE, hprod]
  have hY' : d * Real.logb 2 Y ≤ rigidityConst a b := by
    have e : d * Real.logb 2 Y = d * Real.log Y / Real.log 2 := by
      unfold Real.logb
      ring
    have hLne : Real.log 2 ≠ 0 := hLpos.ne'
    have e2 : rigidityConst a b =
        ((2 * (a + 1) + 2) * Real.log 2 + Real.log b) / Real.log 2 := by
      unfold rigidityConst Real.logb
      rw [eq_div_iff hLne, add_mul, div_mul_cancel₀ _ hLne]
    rw [e, e2, div_le_div_iff_of_pos_right hLpos]
    exact key
  have := mul_lt_mul_of_pos_left hlogb hd0
  linarith

/-- **Item G1**, from (43) with constants `a`, `b`: if `0 < d ≤ 1`, `b ≥ 4` and
`λ > d² / (b · 4^⌈(a+1)/d⌉)`, then `d · log₂(1/λ) < 2(a + 1) + 2 + log₂ b`. -/
theorem rigidity_arith_param {a b d lam : ℝ} (ha : 0 ≤ a) (hb : 4 ≤ b) (hd0 : 0 < d)
    (hd1 : d ≤ 1) (hlam : d ^ 2 / (b * (4 : ℝ) ^ ⌈(a + 1) / d⌉₊) < lam) :
    d * Real.logb 2 (1 / lam) < rigidityConst a b := by
  have hN : ((⌈(a + 1) / d⌉₊ : ℕ) : ℝ) ≤ (a + 1) / d + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (by linarith) hd0.le)).le
  exact rigidity_arith_param_aux hb hd0 hd1 hN hlam

/-- The paper's constants `a = 148`, `b = 1600` give `300 + log₂ 1600 < 311`. -/
theorem rigidityConst_paper_lt : rigidityConst 148 1600 < 311 := by
  have hLpos : 0 < Real.log 2 := by linarith [half_le_log_two]
  have h : Real.logb 2 1600 < 11 := by
    unfold Real.logb
    rw [div_lt_iff₀ hLpos]
    exact log_1600_lt
  unfold rigidityConst
  linarith

/-- Item D1 recovered from the parametric form, with the sharper constant 311: if `0 < d ≤ 1`
and `λ > d² / (1600 · 4^⌈149/d⌉)`, then `d · log₂(1/λ) < 311`. -/
theorem rigidity_arith_param_six {d lam : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hlam : d ^ 2 / (1600 * (4 : ℝ) ^ ⌈149 / d⌉₊) < lam) :
    d * Real.logb 2 (1 / lam) < 311 := by
  have h149 : (148 : ℝ) + 1 = 149 := by norm_num
  have h := rigidity_arith_param (a := 148) (b := 1600) (by norm_num) (by norm_num) hd0 hd1
    (by rw [h149]; exact hlam)
  linarith [rigidityConst_paper_lt]

/-- **Lemma 8.1 with constants `a`, `b`** as a proposition, for all finite `F₂`-spaces in
universe `u`: a `λ`-sparse family with positive mean entropy and ratio `d = e/h > 0` with
`b λ ≤ d²` yields a `4λ`-sparse family with positive mean entropy and ratio at least
`d + d²/a`. Not proved here; used only as a hypothesis. -/
def RatioGrowthConst (a b : ℝ) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] (lam : ℝ)
    (P : WeightedFamily W), 0 < lam → P.IsSparse lam → 0 < P.meanEntropy →
    0 < P.meanInteraction / P.meanEntropy →
    b * lam ≤ (P.meanInteraction / P.meanEntropy) ^ 2 →
    ∃ F : FiniteF2Family.{u}, F.fam.IsSparse (4 * lam) ∧ 0 < F.fam.meanEntropy ∧
      P.meanInteraction / P.meanEntropy + (P.meanInteraction / P.meanEntropy) ^ 2 / a ≤
        F.fam.meanInteraction / F.fam.meanEntropy

/-- `RatioGrowth` (Lemma 8.1 as stated in the paper) is the case `a = 148`, `b = 1600`. -/
theorem ratioGrowthConst_paper_iff : RatioGrowthConst.{u} 148 1600 ↔ RatioGrowth.{u} :=
  Iff.rfl

/-- The iteration in the proof of Theorem 8.2 with constants `a`, `b`: as long as
`b · 4^N · λ ≤ d²`, Lemma 8.1 can be applied `N` times; after `j ≤ N` steps the family is
`4^j λ`-sparse, has ratio at least `d`, and its inverse ratio has dropped by at least
`j/(a + 1)`. -/
theorem ratio_iteration_param {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hgrowth : RatioGrowthConst.{u} a b) {d lam : ℝ} {N : ℕ} (hd0 : 0 < d)
    (hlam0 : 0 < lam) (hsmall : b * (4 : ℝ) ^ N * lam ≤ d ^ 2) (F0 : FiniteF2Family.{u})
    (hsp0 : F0.fam.IsSparse lam) (hpos0 : 0 < F0.fam.meanEntropy)
    (hr0 : F0.fam.meanInteraction / F0.fam.meanEntropy = d) :
    ∀ j : ℕ, j ≤ N → ∃ F : FiniteF2Family.{u}, F.fam.IsSparse ((4 : ℝ) ^ j * lam) ∧
      0 < F.fam.meanEntropy ∧ d ≤ F.fam.meanInteraction / F.fam.meanEntropy ∧
      1 / (F.fam.meanInteraction / F.fam.meanEntropy) ≤ 1 / d - (j : ℝ) / (a + 1) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨F0, ?_, hpos0, ?_, ?_⟩
    · rw [pow_zero, one_mul]
      exact hsp0
    · exact hr0.ge
    · rw [hr0]
      simp
  | succ j ih =>
    intro hj
    obtain ⟨F, hsp, hpos, hdr, hinv⟩ := ih (Nat.le_of_succ_le hj)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = F.fam.meanInteraction / F.fam.meanEntropy := ⟨_, rfl⟩
    rw [← hr] at hdr hinv
    have hr0' : 0 < r := lt_of_lt_of_le hd0 hdr
    have hr1 : r ≤ 1 := by
      rw [hr]
      exact ratio_le_one_aux hpos F.fam.meanInteraction_le
    have hjN : j ≤ N := Nat.le_of_succ_le hj
    have h4 : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hjN
    have hlamj : 0 < (4 : ℝ) ^ j * lam := mul_pos (pow_pos (by norm_num) j) hlam0
    have hdd : d * d ≤ r * r := mul_le_mul hdr hdr hd0.le hr0'.le
    have h4l : (4 : ℝ) ^ j * lam ≤ (4 : ℝ) ^ N * lam := mul_le_mul_of_nonneg_right h4 hlam0.le
    have hbl : b * ((4 : ℝ) ^ j * lam) ≤ b * ((4 : ℝ) ^ N * lam) :=
      mul_le_mul_of_nonneg_left h4l hb
    have hsm : b * ((4 : ℝ) ^ j * lam) ≤ r ^ 2 := by
      have e1 : r ^ 2 = r * r := sq r
      have e2 : d ^ 2 = d * d := sq d
      have e3 : b * (4 : ℝ) ^ N * lam = b * ((4 : ℝ) ^ N * lam) := by ring
      rw [e3, e2] at hsmall
      rw [e1]
      linarith
    obtain ⟨F', hsp', hpos', hstep⟩ := hgrowth F.carrier ((4 : ℝ) ^ j * lam) F.fam hlamj hsp hpos
      (by rw [← hr]; exact hr0') (by rw [← hr]; exact hsm)
    rw [← hr] at hstep
    have hsq : 0 ≤ r ^ 2 / a := div_nonneg (sq_nonneg r) ha.le
    have hstep' := inv_ratio_step_param ha hr0' hr1 hstep
    refine ⟨F', ?_, hpos', ?_, ?_⟩
    · have e : (4 : ℝ) ^ (j + 1) * lam = 4 * ((4 : ℝ) ^ j * lam) := by ring
      rw [e]
      exact hsp'
    · linarith
    · have e : ((j + 1 : ℕ) : ℝ) / (a + 1) = (j : ℝ) / (a + 1) + 1 / (a + 1) := by
        push_cast
        ring
      rw [e]
      linarith

/-- **Theorem 8.2 with constant `rigidityConst a b`, from Lemma 8.1 with constants `a`, `b`**
(`a > 0`, `b ≥ 4`): the proof of Section 8 with `N = ⌈(a+1)/d⌉` steps. -/
theorem weighted_family_rigidity_of_growth_param {a b : ℝ} (ha : 0 < a) (hb : 4 ≤ b)
    (hgrowth : RatioGrowthConst.{u} a b) :
    WeightedFamilyRigidityConst.{u} (rigidityConst a b) := by
  intro W _ _ _ lam hlam P hsparse hpos
  have hb0 : (0 : ℝ) < b := by linarith
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hle : P.meanInteraction ≤ P.meanEntropy := P.meanInteraction_le
  have hnn : 0 ≤ P.meanInteraction := P.meanInteraction_nonneg
  have hL : 0 < Real.logb 2 (1 / lam) := logb_one_div_pos hlam
  refine le_min (ratio_le_one_aux hpos hle) ?_
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = P.meanInteraction / P.meanEntropy := ⟨_, rfl⟩
  rw [← hd]
  have hd0' : 0 ≤ d := by
    rw [hd]
    exact div_nonneg hnn hpos.le
  rcases hd0'.lt_or_eq with hd0 | hd0
  · have hd1 : d ≤ 1 := by
      rw [hd]
      exact ratio_le_one_aux hpos hle
    have hbig : d ^ 2 / (b * (4 : ℝ) ^ ⌈(a + 1) / d⌉₊) < lam := by
      by_contra hcon
      push_neg at hcon
      have hA : (0 : ℝ) < b * (4 : ℝ) ^ ⌈(a + 1) / d⌉₊ :=
        mul_pos hb0 (pow_pos (by norm_num) _)
      have hcon' : lam * (b * (4 : ℝ) ^ ⌈(a + 1) / d⌉₊) ≤ d ^ 2 := (le_div_iff₀ hA).mp hcon
      have hsmall : b * (4 : ℝ) ^ ⌈(a + 1) / d⌉₊ * lam ≤ d ^ 2 := by
        rw [mul_comm]
        exact hcon'
      obtain ⟨F, -, -, hdF, hinvF⟩ := ratio_iteration_param ha hb0.le hgrowth hd0 hlam.1 hsmall
        (FiniteF2Family.mk W P) hsparse hpos hd.symm ⌈(a + 1) / d⌉₊ le_rfl
      have hrpos : 0 < 1 / (F.fam.meanInteraction / F.fam.meanEntropy) :=
        one_div_pos.mpr (lt_of_lt_of_le hd0 hdF)
      have hN : (a + 1) / d ≤ ((⌈(a + 1) / d⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h1 : 1 / d ≤ ((⌈(a + 1) / d⌉₊ : ℕ) : ℝ) / (a + 1) := by
        rw [le_div_iff₀ ha1]
        calc 1 / d * (a + 1) = (a + 1) / d := by ring
          _ ≤ _ := hN
      linarith
    have hbnd := rigidity_arith_param ha.le hb hd0 hd1 hbig
    rw [le_div_iff₀ hL]
    linarith
  · rw [← hd0]
    have hlogb : 0 ≤ Real.logb 2 b := Real.logb_nonneg (by norm_num) (by linarith)
    have hK : 0 ≤ rigidityConst a b := by
      unfold rigidityConst
      linarith
    exact div_nonneg hK hL.le

/-- `rigidityConst a b > 0` for `a > 0`, `b ≥ 4`. -/
theorem rigidityConst_pos {a b : ℝ} (ha : 0 < a) (hb : 4 ≤ b) : 0 < rigidityConst a b := by
  have hlogb : 0 ≤ Real.logb 2 b := Real.logb_nonneg (by norm_num) (by linarith)
  unfold rigidityConst
  linarith

/-- The conclusion of **Theorem 1.1** with exponent `rigidityConst a b · (1+ε)/ε`, from
Lemma 8.1 with constants `a`, `b`. -/
theorem exponential_entropy_quotient_of_growth_param {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {a b : ℝ} (ha : 0 < a) (hb : 4 ≤ b)
    (hgrowth : RatioGrowthConst.{u} a b) (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤
        (2 : ℝ) ^ (rigidityConst a b * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_rigidity_const (rigidityConst_pos ha hb)
    (weighted_family_rigidity_of_growth_param ha hb hgrowth) ε hε X

/-- The conclusion of **Theorem 1.2** with constant `rigidityConst a b`, from Lemma 8.1 with
constants `a`, `b`. -/
theorem sparse_rigidity_of_growth_param {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {a b : ℝ} (ha : 0 < a) (hb : 4 ≤ b)
    (hgrowth : RatioGrowthConst.{u} a b) (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (Z : PMF V)
    (hsparse : IsSparse lam Z) (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (rigidityConst a b / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_of_family_rigidity_const
    (weighted_family_rigidity_of_growth_param ha hb hgrowth) lam hlam Z hsparse hpos

end EntropyLean
