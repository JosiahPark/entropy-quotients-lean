import Mathlib
import EntropyLean.Conditional
import EntropyLean.RigidityArith

/-!
# Theorem 8.2 from Lemma 8.1 (roadmap item D2)

`RatioGrowth` is the statement of Lemma 8.1 (fixed-cost ratio growth) of arXiv:2610.38525 as a
`Prop`, quantified over all finite `F₂`-spaces of one universe: a `λ`-sparse family with positive
mean entropy and ratio `d = e/h > 0` with `d ≥ 40√λ` (written `1600 λ ≤ d²`, equivalent for
`d, λ ≥ 0`) yields a `4λ`-sparse family, on some possibly different finite `F₂`-space, with
positive mean entropy and ratio at least `d + d²/148` (equation (39)). The output family is
packaged in the structure `FiniteF2Family`.

`weighted_family_rigidity_of_growth` proves `WeightedFamilyRigidity` (the statement of
Theorem 8.2, equation (41)) from `RatioGrowth`, following the proof in Section 8: iterate
Lemma 8.1 `N = ⌈149/d⌉` times (`ratio_iteration`, using (42) via `inv_ratio_step`); if
`λ ≤ (d²/1600)·4^(−N)` this would force `1/d_N ≤ 1/d − N/149 ≤ 0`, so (43) holds and
`rigidity_iteration_bound` (item D1) gives `d · log₂(1/λ) < 320`. The bound `e/h ≤ 1` is
`WeightedFamily.meanInteraction_le` (14).

Corollaries: `exponential_entropy_quotient_of_growth` and `sparse_rigidity_of_growth`, the
statements of Theorems 1.1 and 1.2 with Lemma 8.1 as the explicit hypothesis.

What this file does NOT prove: Lemma 8.1 (it enters only as the hypothesis `hgrowth`), and hence
NOT Theorem 8.2, Theorem 1.1 or Theorem 1.2 themselves.
-/

universe u

namespace EntropyLean

open scoped BigOperators

/-- A weighted family on some finite `F₂`-vector space (the carrier is part of the data). -/
structure FiniteF2Family where
  carrier : Type u
  [acg : AddCommGroup carrier]
  [mod : Module (ZMod 2) carrier]
  [fin : Fintype carrier]
  fam : WeightedFamily carrier

attribute [instance] FiniteF2Family.acg FiniteF2Family.mod FiniteF2Family.fin

/-- **Lemma 8.1** (ratio growth), equation (39), as a proposition for all finite `F₂`-spaces in
universe `u`. The hypothesis `d ≥ 40√λ` is written `1600 λ ≤ d²`. Not proved here; used only
as a hypothesis. -/
def RatioGrowth : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] (lam : ℝ)
    (P : WeightedFamily W), 0 < lam → P.IsSparse lam → 0 < P.meanEntropy →
    0 < P.meanInteraction / P.meanEntropy →
    1600 * lam ≤ (P.meanInteraction / P.meanEntropy) ^ 2 →
    ∃ F : FiniteF2Family.{u}, F.fam.IsSparse (4 * lam) ∧ 0 < F.fam.meanEntropy ∧
      P.meanInteraction / P.meanEntropy + (P.meanInteraction / P.meanEntropy) ^ 2 / 148 ≤
        F.fam.meanInteraction / F.fam.meanEntropy

/-- `a / b ≤ 1` from `a ≤ b` and `0 < b`. -/
theorem ratio_le_one_aux {a b : ℝ} (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  rw [div_le_iff₀ hb, one_mul]
  exact h

/-- The iteration in the proof of Theorem 8.2: as long as `1600 · 4^N · λ ≤ d²`, Lemma 8.1 can be
applied `N` times; after `j ≤ N` steps the family is `4^j λ`-sparse, has ratio at least `d`, and
its inverse ratio has dropped by at least `j/149` (equation (42)). -/
theorem ratio_iteration (hgrowth : RatioGrowth.{u}) {d lam : ℝ} {N : ℕ} (hd0 : 0 < d)
    (hlam0 : 0 < lam) (hsmall : 1600 * (4 : ℝ) ^ N * lam ≤ d ^ 2) (F0 : FiniteF2Family.{u})
    (hsp0 : F0.fam.IsSparse lam) (hpos0 : 0 < F0.fam.meanEntropy)
    (hr0 : F0.fam.meanInteraction / F0.fam.meanEntropy = d) :
    ∀ j : ℕ, j ≤ N → ∃ F : FiniteF2Family.{u}, F.fam.IsSparse ((4 : ℝ) ^ j * lam) ∧
      0 < F.fam.meanEntropy ∧ d ≤ F.fam.meanInteraction / F.fam.meanEntropy ∧
      1 / (F.fam.meanInteraction / F.fam.meanEntropy) ≤ 1 / d - (j : ℝ) / 149 := by
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
    have h4 : (4 : ℝ) ^ j ≤ (4 : ℝ) ^ N := by
      first
        | exact pow_le_pow_right₀ (by norm_num) hjN
        | (gcongr <;> norm_num)
    have hlamj : 0 < (4 : ℝ) ^ j * lam := mul_pos (pow_pos (by norm_num) j) hlam0
    have hdd : d * d ≤ r * r := mul_le_mul hdr hdr hd0.le hr0'.le
    have h4l : (4 : ℝ) ^ j * lam ≤ (4 : ℝ) ^ N * lam := mul_le_mul_of_nonneg_right h4 hlam0.le
    have hsm : 1600 * ((4 : ℝ) ^ j * lam) ≤ r ^ 2 := by
      have e1 : r ^ 2 = r * r := sq r
      have e2 : d ^ 2 = d * d := sq d
      have e3 : 1600 * (4 : ℝ) ^ N * lam = 1600 * ((4 : ℝ) ^ N * lam) := by ring
      rw [e3, e2] at hsmall
      rw [e1]
      linarith
    obtain ⟨F', hsp', hpos', hstep⟩ := hgrowth F.carrier ((4 : ℝ) ^ j * lam) F.fam hlamj hsp hpos
      (by rw [← hr]; exact hr0') (by rw [← hr]; exact hsm)
    rw [← hr] at hstep
    have hsq : 0 ≤ r ^ 2 / 148 := div_nonneg (sq_nonneg r) (by norm_num)
    have hstep' := inv_ratio_step hr0' hr1 hstep
    refine ⟨F', ?_, hpos', ?_, ?_⟩
    · have e : (4 : ℝ) ^ (j + 1) * lam = 4 * ((4 : ℝ) ^ j * lam) := by ring
      rw [e]
      exact hsp'
    · linarith
    · have e : ((j + 1 : ℕ) : ℝ) / 149 = (j : ℝ) / 149 + 1 / 149 := by
        push_cast
        ring
      rw [e]
      linarith

/-- **Theorem 8.2 from Lemma 8.1** (item D2): the statement of `weighted_family_rigidity`
(equation (41)), with Lemma 8.1 as the explicit hypothesis `hgrowth`. -/
theorem weighted_family_rigidity_of_growth (hgrowth : RatioGrowth.{u}) :
    WeightedFamilyRigidity.{u} := by
  unfold WeightedFamilyRigidity
  intro W _ _ _ lam hlam P hsparse hpos
  have hle : P.meanInteraction ≤ P.meanEntropy := P.meanInteraction_le
  have hnn : 0 ≤ P.meanInteraction := P.meanInteraction_nonneg
  have hL : 0 < Real.logb 2 (1 / lam) :=
    Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hlam.1, one_mul]; exact hlam.2)
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
    have hbig : d ^ 2 / (1600 * (4 : ℝ) ^ ⌈149 / d⌉₊) < lam := by
      by_contra hcon
      push_neg at hcon
      have hA : (0 : ℝ) < 1600 * (4 : ℝ) ^ ⌈149 / d⌉₊ := by positivity
      have hcon' : lam * (1600 * (4 : ℝ) ^ ⌈149 / d⌉₊) ≤ d ^ 2 := (le_div_iff₀ hA).mp hcon
      have hsmall : 1600 * (4 : ℝ) ^ ⌈149 / d⌉₊ * lam ≤ d ^ 2 := by
        rw [mul_comm]
        exact hcon'
      obtain ⟨F, -, -, hdF, hinvF⟩ := ratio_iteration hgrowth hd0 hlam.1 hsmall
        (FiniteF2Family.mk W P) hsparse hpos hd.symm ⌈149 / d⌉₊ le_rfl
      have hrpos : 0 < 1 / (F.fam.meanInteraction / F.fam.meanEntropy) :=
        one_div_pos.mpr (lt_of_lt_of_le hd0 hdF)
      have hN : 149 / d ≤ ((⌈149 / d⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      have h1 : (149 : ℝ) / d = 149 * (1 / d) := by ring
      linarith
    have hb := rigidity_iteration_bound hd0 hd1 hbig
    rw [le_div_iff₀ hL]
    linarith
  · rw [← hd0]
    exact div_nonneg (by norm_num) hL.le

/-- **Theorem 1.1 from Lemma 8.1**: the statement of `exponential_entropy_quotient`, with
Lemma 8.1 as the explicit hypothesis `hgrowth`. -/
theorem exponential_entropy_quotient_of_growth {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hgrowth : RatioGrowth.{u})
    (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (320 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_rigidity (weighted_family_rigidity_of_growth hgrowth) ε hε X

/-- **Theorem 1.2 from Lemma 8.1**: the statement of `sparse_rigidity`, with Lemma 8.1 as the
explicit hypothesis `hgrowth`. -/
theorem sparse_rigidity_of_growth {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hgrowth : RatioGrowth.{u})
    (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (Z : PMF V)
    (hsparse : IsSparse lam Z) (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (320 / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_of_family_rigidity (weighted_family_rigidity_of_growth hgrowth) lam hlam Z
    hsparse hpos

end EntropyLean
