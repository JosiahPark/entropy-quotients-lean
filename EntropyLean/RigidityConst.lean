import EntropyLean.MathlibForPFR
import EntropyLean.Conditional

/-!
# Theorems 1.1 and 1.2 from Theorem 8.2 with an arbitrary constant (roadmap item G2)

`WeightedFamilyRigidityConst K` is the statement of Theorem 8.2 of arXiv:2610.38525 (equation
(41)) with the constant 320 replaced by a real parameter `K`:
`e(𝒫)/h(𝒫) ≤ min(1, K / log₂(1/λ))` for every `λ`-sparse family with positive mean entropy.
`WeightedFamilyRigidity` is the case `K = 320` (`weightedFamilyRigidityConst_320_iff`).

Proved here, with `hrig : WeightedFamilyRigidityConst K` as the explicit hypothesis:

* `WeightedFamilyRigidityConst.mono`: the statement is monotone in `K`;
* `exponential_entropy_quotient_of_rigidity_const`: the conclusion of Theorem 1.1 with dimension
  bound `dim G ≤ 2^(K(1+ε)/ε) H(X)` (for `K > 0`), by the proof of Section 9 with
  `λ = 2^(−K(1+ε)/ε)`;
* `sparse_rigidity_of_family_rigidity_const`: the conclusion of Theorem 1.2 with constant `K`.

So any proof of Theorem 8.2 with a smaller constant gives Theorem 1.1 with a smaller exponent.

What this file does NOT prove: Theorem 8.2 for any constant (it is only a hypothesis here), and
hence not Theorem 1.1 or Theorem 1.2.
-/

universe u

namespace EntropyLean

/-- **Theorem 8.2 with constant `K`** as a proposition, for all finite `F₂`-spaces in universe
`u`. Not proved here; used only as a hypothesis. -/
def WeightedFamilyRigidityConst (K : ℝ) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] (lam : ℝ),
    0 < lam ∧ lam < 1 → ∀ P : WeightedFamily W, P.IsSparse lam → 0 < P.meanEntropy →
      P.meanInteraction / P.meanEntropy ≤ min 1 (K / Real.logb 2 (1 / lam))

/-- `WeightedFamilyRigidity` is the case `K = 320`. -/
theorem weightedFamilyRigidityConst_320_iff :
    WeightedFamilyRigidityConst.{u} 320 ↔ WeightedFamilyRigidity.{u} :=
  Iff.rfl

/-- `log₂(1/λ) > 0` for `0 < λ < 1`. -/
theorem logb_one_div_pos {lam : ℝ} (hlam : 0 < lam ∧ lam < 1) :
    0 < Real.logb 2 (1 / lam) :=
  Real.logb_pos (by norm_num) (by rw [lt_div_iff₀ hlam.1, one_mul]; exact hlam.2)

/-- Theorem 8.2 with constant `K` implies it with any larger constant. -/
theorem WeightedFamilyRigidityConst.mono {K K' : ℝ} (h : WeightedFamilyRigidityConst.{u} K)
    (hKK : K ≤ K') : WeightedFamilyRigidityConst.{u} K' := by
  intro W _ _ _ lam hlam P hsp hpos
  have hL : 0 < Real.logb 2 (1 / lam) := logb_one_div_pos hlam
  have h1 : K / Real.logb 2 (1 / lam) ≤ K' / Real.logb 2 (1 / lam) := by
    rw [div_le_div_iff_of_pos_right hL]
    exact hKK
  exact (h W lam hlam P hsp hpos).trans (min_le_min le_rfl h1)

/-- **Theorem 1.1 from Theorem 8.2 with constant `K`**: the conclusion of Theorem 1.1 with
exponent `K(1+ε)/ε` in place of `320(1+ε)/ε`. -/
theorem exponential_entropy_quotient_of_rigidity_const {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {K₀ : ℝ} (hK₀ : 0 < K₀)
    (hrig : WeightedFamilyRigidityConst.{u} K₀) (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (K₀ * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = K₀ * (1 + ε) / ε := ⟨_, rfl⟩
  rw [← hKdef]
  have h1ε : 0 < 1 + ε := by linarith
  have hK : 0 < K := by
    rw [hKdef]
    exact div_pos (mul_pos hK₀ h1ε) hε
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
  have hratio : K₀ / Real.logb 2 (1 / lam) = ε / (1 + ε) := by
    rw [hlog, hKdef, div_div_eq_mul_div, mul_div_mul_left ε (1 + ε) hK₀.ne']
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

/-- **Theorem 1.2 from Theorem 8.2 with constant `K`**, applied to the singleton family `{Z}`. -/
theorem sparse_rigidity_of_family_rigidity_const {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] {K₀ : ℝ} (hrig : WeightedFamilyRigidityConst.{u} K₀)
    (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (Z : PMF V)
    (hsparse : IsSparse lam Z) (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (K₀ / Real.logb 2 (1 / lam)) := by
  have h := hrig V lam hlam (WeightedFamily.singleton Z)
    ((WeightedFamily.isSparse_singleton_iff lam Z).mpr hsparse)
    (by rw [WeightedFamily.meanEntropy_singleton]; exact hpos)
  rwa [WeightedFamily.meanInteraction_singleton, WeightedFamily.meanEntropy_singleton] at h

end EntropyLean
