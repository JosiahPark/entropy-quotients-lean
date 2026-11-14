import Mathlib
import EntropyLean.Variational
import EntropyLean.Increment

/-!
# Theorem 1.1 conditional on Theorem 8.2 (roadmap item C2)

`WeightedFamilyRigidity` is the statement of Theorem 8.2 (weighted-family logarithmic rigidity
with constant 320) as a `Prop`, quantified over all finite `F₂`-spaces of one universe. It is
**not** proved here; it enters only as the explicit hypothesis `hrig`.

`exponential_entropy_quotient_of_rigidity` proves the conclusion of Theorem 1.1
(`exponential_entropy_quotient` in `EntropyLean/Statements.lean`) from `hrig`, following
Section 9 of the paper: take `λ = 2^(-320(1+ε)/ε)`, apply Lemma 9.1
(`WeightedFamily.variational_sparsification_proof`) to the singleton family `{X}` to get `G`
with `dim G ≤ 2^(320(1+ε)/ε) H(X)` and `q_G X` `λ`-sparse, apply Theorem 8.2 to the singleton
family `{q_G X}` to get `E(q_G X) ≤ (ε/(1+ε)) H(q_G X)`, hence `H(q_G X) ≤ (1+ε) D(q_G X)`;
finally `D(q_G X) ≤ D(X)` is `entropyIncrement_quotient_le` (item B5).

Also: the singleton family `WeightedFamily.singleton` with `meanEntropy_singleton`,
`meanInteraction_singleton`, `averagedLoss_singleton`, `isSparse_singleton_iff` and the
quotient versions `meanEntropy_singleton_quotient`, `meanInteraction_singleton_quotient`.

What this file does NOT prove: Theorem 8.2, and hence NOT Theorem 1.1 itself; the open proof
obligation in `exponential_entropy_quotient` remains.
-/

universe u

namespace EntropyLean

open scoped BigOperators

namespace WeightedFamily

variable {V : Type*}

/-- The family with one component `Q` of weight `1`. -/
noncomputable def singleton (Q : PMF V) : WeightedFamily V where
  index := Unit
  laws := fun _ => Q
  weights := fun _ => 1
  weights_pos := fun _ => one_pos
  weights_sum := by simp

theorem meanEntropy_singleton (Q : PMF V) :
    (WeightedFamily.singleton Q).meanEntropy = entropyBits Q := by
  show ∑ _i : Unit, (1 : ℝ) * entropyBits Q = entropyBits Q
  simp

theorem meanInteraction_singleton [Add V] (Q : PMF V) :
    (WeightedFamily.singleton Q).meanInteraction = entropyDefect Q := by
  show ∑ _i : Unit, ∑ _j : Unit, (1 : ℝ) * 1 * interaction Q Q = entropyDefect Q
  simp [interaction_self]

theorem averagedLoss_singleton [AddCommGroup V] [Module (ZMod 2) V] (Q : PMF V)
    (W : Submodule (ZMod 2) V) :
    (WeightedFamily.singleton Q).averagedLoss W = quotientLoss Q W := by
  show ∑ _i : Unit, (1 : ℝ) * quotientLoss Q W = quotientLoss Q W
  simp

theorem isSparse_singleton_iff [AddCommGroup V] [Module (ZMod 2) V] (lam : ℝ) (Q : PMF V) :
    (WeightedFamily.singleton Q).IsSparse lam ↔ EntropyLean.IsSparse lam Q := by
  constructor
  · intro h W
    have h1 := h W
    rwa [averagedLoss_singleton] at h1
  · intro h W
    rw [averagedLoss_singleton]
    exact h W

theorem meanEntropy_singleton_quotient [AddCommGroup V] [Module (ZMod 2) V] (Q : PMF V)
    (G : Submodule (ZMod 2) V) :
    ((WeightedFamily.singleton Q).quotient G).meanEntropy =
      entropyBits (Q.map fun v => G.mkQ v) := by
  show ∑ _i : Unit, (1 : ℝ) * entropyBits (Q.map fun v => G.mkQ v) = _
  simp

theorem meanInteraction_singleton_quotient [AddCommGroup V] [Module (ZMod 2) V] (Q : PMF V)
    (G : Submodule (ZMod 2) V) :
    ((WeightedFamily.singleton Q).quotient G).meanInteraction =
      entropyDefect (Q.map fun v => G.mkQ v) := by
  show ∑ _i : Unit, ∑ _j : Unit, (1 : ℝ) * 1 *
      interaction (Q.map fun v => G.mkQ v) (Q.map fun v => G.mkQ v) = _
  simp [interaction_self]

end WeightedFamily

/-- **Theorem 8.2** (weighted-family logarithmic rigidity, constant 320) as a proposition, for
all finite `F₂`-spaces in universe `u`. Not proved here; used only as a hypothesis. -/
def WeightedFamilyRigidity : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] (lam : ℝ),
    0 < lam ∧ lam < 1 → ∀ P : WeightedFamily W, P.IsSparse lam → 0 < P.meanEntropy →
      P.meanInteraction / P.meanEntropy ≤ min 1 (320 / Real.logb 2 (1 / lam))

/-- The algebraic step `H - D ≤ (ε/(1+ε)) H ⇒ H ≤ (1+ε) D` (copy of
`entropy_le_of_defect_le`, kept here so this file does not import `Statements`). -/
theorem entropy_le_of_defect_le_aux (ε : ℝ) (hε : 0 < ε) (H D : ℝ)
    (h : H - D ≤ ε / (1 + ε) * H) : H ≤ (1 + ε) * D := by
  have h1 : 0 < 1 + ε := by linarith
  have hne : (1 + ε) ≠ 0 := ne_of_gt h1
  have h2 : ε / (1 + ε) * H * (1 + ε) = ε * H := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_right h h1.le
  nlinarith [h2, h3]

/-- **Theorem 1.1 from Theorem 8.2**: the statement of `exponential_entropy_quotient`, with
Theorem 8.2 as the explicit hypothesis `hrig`. -/
theorem exponential_entropy_quotient_of_rigidity {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hrig : WeightedFamilyRigidity.{u})
    (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (320 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 320 * (1 + ε) / ε := ⟨_, rfl⟩
  rw [← hKdef]
  have h1ε : 0 < 1 + ε := by linarith
  have hK : 0 < K := by
    rw [hKdef]
    exact div_pos (mul_pos (by norm_num) h1ε) hε
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = (2 : ℝ) ^ (-K) := ⟨_, rfl⟩
  have hlam_pos : 0 < lam := by
    rw [hlam]
    positivity
  have hlam_lt : lam < 1 := by
    rw [hlam]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hinv : lam⁻¹ = (2 : ℝ) ^ K := by
    rw [hlam, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  have hlog : Real.logb 2 (1 / lam) = K := by
    rw [one_div, hinv, Real.logb_rpow (by norm_num) (by norm_num)]
  have hratio : 320 / Real.logb 2 (1 / lam) = ε / (1 + ε) := by
    rw [hlog, hKdef, div_div_eq_mul_div,
      mul_div_mul_left ε (1 + ε) (by norm_num : (320 : ℝ) ≠ 0)]
  obtain ⟨G, hdim, hsp⟩ :=
    WeightedFamily.variational_sparsification_proof lam hlam_pos (WeightedFamily.singleton X)
  rw [WeightedFamily.meanEntropy_singleton] at hdim
  refine ⟨G, ?_, ?_, entropyIncrement_quotient_le X G⟩
  · calc (Module.finrank (ZMod 2) G : ℝ) ≤ entropyBits X / lam := hdim
      _ = (2 : ℝ) ^ K * entropyBits X := by
        rw [div_eq_mul_inv, hinv]
        ring
  · haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
    letI : Fintype (V ⧸ G) := Fintype.ofFinite _
    rcases (entropyBits_nonneg' (X.map fun v => G.mkQ v)).lt_or_eq with hpos | hzero
    · have hF := hrig (V ⧸ G) lam ⟨hlam_pos, hlam_lt⟩ ((WeightedFamily.singleton X).quotient G)
        hsp (by rw [WeightedFamily.meanEntropy_singleton_quotient]; exact hpos)
      rw [WeightedFamily.meanInteraction_singleton_quotient,
        WeightedFamily.meanEntropy_singleton_quotient, hratio] at hF
      have hE := hF.trans (min_le_right _ _)
      rw [div_le_iff₀ hpos, entropyDefect_eq] at hE
      exact entropy_le_of_defect_le_aux ε hε _ _ hE
    · have hc := entropyBits_le_conv_right (X.map fun v => G.mkQ v) (X.map fun v => G.mkQ v)
      have hD : 0 ≤ entropyIncrement (X.map fun v => G.mkQ v) := by
        unfold entropyIncrement
        exact sub_nonneg.mpr hc
      rw [← hzero]
      exact mul_nonneg h1ε.le hD

end EntropyLean
