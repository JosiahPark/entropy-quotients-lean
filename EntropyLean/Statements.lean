import EntropyLean.Families

/-!
# Main results of arXiv:2610.38525: statements (open) and the elementary steps (proved)

Every `sorry` below is an open proof obligation, **not** a certified theorem. The statements are
checked against the paper (v1, 28 Oct 2026) but have not been independently reviewed.

Open (statement only): Theorem 1.1, Theorem 1.2, Theorem 8.2, Lemma 4.1, Lemma 9.1,
Proposition 9.3.

Proved here: `entropy_le_of_defect_le` and `entropy_le_increment_of_defect_le`, the algebraic step
in the proof of Theorem 1.1 turning `E(Z) ≤ θ H(Z)` with `θ = ε/(1+ε)` into
`H(Z) ≤ (1+ε) D(Z)`.

What this file does NOT prove: no `sorry`-free result about entropy quotients beyond that
algebraic step; in particular Theorem 1.1 is NOT proved. The entropic Marton theorem
(Gowers–Green–Manners–Tao) on which the paper relies is not formalized here.
-/

namespace EntropyLean

open Filter

/-- **Theorem 1.1** (exponential entropy quotient), equations (2)–(3).
`H(q_G X) ≤ (1+ε) D(q_G X) ≤ (1+ε) D(X)`; the second inequality is stated as
`D(q_G X) ≤ D(X)`. -/
theorem exponential_entropy_quotient
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (320 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X := by
  sorry

/-- **Theorem 1.2** (sparse-law rigidity), equation (7). -/
theorem sparse_rigidity
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (Z : PMF V)
    (hsparse : IsSparse lam Z) (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (320 / Real.logb 2 (1 / lam)) := by
  sorry

/-- **Theorem 8.2** (weighted-family logarithmic rigidity). -/
theorem weighted_family_rigidity
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (lam : ℝ) (hlam : 0 < lam ∧ lam < 1) (P : WeightedFamily V)
    (hsparse : P.IsSparse lam) (hpos : 0 < P.meanEntropy) :
    P.meanInteraction / P.meanEntropy ≤ min 1 (320 / Real.logb 2 (1 / lam)) := by
  sorry

/-- **Lemma 4.1** (ratio-preserving sparsification). The quotient family `𝒫₀ = q_G 𝒫` has
positive mean entropy, ratio `e(𝒫₀)/h(𝒫₀) ≥ e(𝒫)/h(𝒫)`, is `2λ`-sparse, and `𝒫₀ * 𝒫₀` is
`4λ`-sparse. -/
theorem ratio_preserving_sparsification
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (lam : ℝ) (hlam : 0 < lam) (P : WeightedFamily V)
    (hsparse : P.IsSparse lam) (hpos : 0 < P.meanEntropy) :
    ∃ G : Submodule (ZMod 2) V,
      0 < (P.quotient G).meanEntropy ∧
      P.meanInteraction / P.meanEntropy ≤
        (P.quotient G).meanInteraction / (P.quotient G).meanEntropy ∧
      (P.quotient G).IsSparse (2 * lam) ∧
      (P.quotient G).convFamily.IsSparse (4 * lam) := by
  sorry

/-- **Lemma 9.1** (variational sparsification), equation (44). -/
theorem variational_sparsification
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (lam : ℝ) (hlam : 0 < lam) (P : WeightedFamily V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ P.meanEntropy / lam ∧
      (P.quotient G).IsSparse lam := by
  sorry

/-- **Proposition 9.3** (exponential scale is necessary). If `C ε` is valid for every law on
every `F₂^m` in the original-input form `dim G ≤ C(ε) H(X)`, `H(q_G X) ≤ (1+ε) D(X)`, then
`liminf_{ε↓0} ε log₂ C(ε) ≥ 2`, stated without `liminf` as: for every `c < 2`, eventually
`c ≤ ε log₂ C(ε)` (this avoids `liminf`'s junk value for functions unbounded above). -/
theorem exponential_scale_necessary (C : ℝ → ℝ)
    (hC : ∀ ε > 0, ∀ (m : ℕ) (X : PMF (F2Vec m)), ∃ G : Submodule (ZMod 2) (F2Vec m),
      (Module.finrank (ZMod 2) G : ℝ) ≤ C ε * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤ (1 + ε) * entropyIncrement X) :
    ∀ c : ℝ, c < 2 → ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), c ≤ ε * Real.logb 2 (C ε) := by
  sorry

/-- Algebraic step in the proof of Theorem 1.1: from `H - D ≤ (ε/(1+ε)) H` get
`H ≤ (1+ε) D`. -/
theorem entropy_le_of_defect_le (ε : ℝ) (hε : 0 < ε) (H D : ℝ)
    (h : H - D ≤ ε / (1 + ε) * H) : H ≤ (1 + ε) * D := by
  have h1 : 0 < 1 + ε := by linarith
  have hne : (1 + ε) ≠ 0 := ne_of_gt h1
  have h2 : ε / (1 + ε) * H * (1 + ε) = ε * H := by
    first
      | (field_simp; done)
      | (field_simp; ring)
  have h3 := mul_le_mul_of_nonneg_right h h1.le
  nlinarith [h2, h3]

/-- The step of `entropy_le_of_defect_le` for a law: `E(Z) ≤ θ H(Z)` with `θ = ε/(1+ε)`
gives `H(Z) ≤ (1+ε) D(Z)`. -/
theorem entropy_le_increment_of_defect_le {V : Type*} [Add V] (ε : ℝ) (hε : 0 < ε)
    (Z : PMF V) (h : entropyDefect Z ≤ ε / (1 + ε) * entropyBits Z) :
    entropyBits Z ≤ (1 + ε) * entropyIncrement Z := by
  rw [entropyDefect_eq] at h
  exact entropy_le_of_defect_le ε hε _ _ h

end EntropyLean
