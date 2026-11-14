import Mathlib
import EntropyLean.Variational
import EntropyLean.Interaction

/-!
# Lemma 4.1, first half: the common objective and sparsity at a minimizer (roadmap item C4a)

For a finite weighted family `𝒫` on a finite `F₂`-space `V`, with `ℛ = 𝒫 * 𝒫`, the objective
(24) of arXiv:2610.38525 is
`Φ(G) = h(q_G ℛ) + (2 + d) h(q_G 𝒫) + 4λ dim G` (`WeightedFamily.ratioObjective`).

Proved here:
* `quotientLoss_nonneg`, `WeightedFamily.averagedLoss_nonneg`: `F_P(W) ≥ 0`, `F_𝒫(W) ≥ 0`.
* `WeightedFamily.quotient_convFamily_averagedLoss`,
  `WeightedFamily.quotient_convFamily_meanEntropy`: quotienting commutes with forming the
  convolution family, `q_G 𝒫 * q_G 𝒫 = q_G (𝒫 * 𝒫)` (at the level of `F` and `h`).
* `WeightedFamily.ratioObjective_bot`: `Φ(0) = h(ℛ) + (2 + d) h(𝒫)`.
* `WeightedFamily.ratioObjective_min_loss`: equation (26) at any global minimizer `G`:
  `F_{q_G ℛ}(W) + (2 + d) F_{q_G 𝒫}(W) ≤ 4λ dim W` for every `W ≤ V ⧸ G`.
* `WeightedFamily.ratioObjective_min_sparse`: for `d ≥ 0`, at a minimizer `q_G 𝒫` is
  `2λ`-sparse and `q_G 𝒫 * q_G 𝒫` is `4λ`-sparse (items 2 and 3 of Lemma 4.1).

Roadmap item C4b (second half of Lemma 4.1):
* `WeightedFamily.ratioObjective_eq`: by (15) on `q_G 𝒫`,
  `Φ(G) = (4 + d) h(q_G 𝒫) - e(q_G 𝒫) + 4λ dim G`.
* `WeightedFamily.ratioObjective_bot_of`: `Φ(0) = 4 h(𝒫)` when `d h(𝒫) = e(𝒫)`.
* `WeightedFamily.ratioObjective_min_ratio`: equation (25), `d h(q_G 𝒫) ≤ e(q_G 𝒫)` at a
  minimizer, using the `λ`-sparsity of `𝒫` at `G`.
* `WeightedFamily.ratioObjective_min_pos`: `h(q_G 𝒫) > 0` at a minimizer of least dimension.
* `WeightedFamily.ratio_preserving_sparsification_proof`: **Lemma 4.1**, with `d = e(𝒫)/h(𝒫)`;
  it discharges `ratio_preserving_sparsification` in `EntropyLean/Statements.lean`.

What this file does NOT prove: nothing about Theorem 1.1, 1.2 or 8.2 beyond supplying Lemma 4.1,
one of the inputs of Lemma 8.1 (which is not formalized).
-/

namespace EntropyLean

open scoped BigOperators

section Loss

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `F_P(W) = H(P) - H(q_W P) ≥ 0` on a finite space. -/
theorem quotientLoss_nonneg [Fintype V] (Q : PMF V) (W : Submodule (ZMod 2) V) :
    0 ≤ quotientLoss Q W := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  have h := entropyBits_map_le Q (fun v => W.mkQ v)
  unfold quotientLoss
  linarith

end Loss

namespace WeightedFamily

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `F_𝒫(W) ≥ 0` on a finite space. -/
theorem averagedLoss_nonneg [Fintype V] (P : WeightedFamily V) (W : Submodule (ZMod 2) V) :
    0 ≤ P.averagedLoss W := by
  unfold averagedLoss
  exact Finset.sum_nonneg fun i _ => mul_nonneg (P.weights_pos i).le (quotientLoss_nonneg _ _)

/-- `F_{q_G 𝒫 * q_G 𝒫}(W) = F_{q_G (𝒫 * 𝒫)}(W)`: quotienting commutes with convolution. -/
theorem quotient_convFamily_averagedLoss (P : WeightedFamily V) (G : Submodule (ZMod 2) V)
    (W : Submodule (ZMod 2) (V ⧸ G)) :
    (P.quotient G).convFamily.averagedLoss W = (P.convFamily.quotient G).averagedLoss W := by
  show ∑ p : P.index × P.index, P.weights p.1 * P.weights p.2 *
        quotientLoss (conv ((P.laws p.1).map fun v => G.mkQ v)
          ((P.laws p.2).map fun v => G.mkQ v)) W =
      ∑ p : P.index × P.index, P.weights p.1 * P.weights p.2 *
        quotientLoss ((conv (P.laws p.1) (P.laws p.2)).map fun v => G.mkQ v) W
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conv_map_mkQ]

/-- `h(q_G 𝒫 * q_G 𝒫) = h(q_G (𝒫 * 𝒫))`. -/
theorem quotient_convFamily_meanEntropy (P : WeightedFamily V) (G : Submodule (ZMod 2) V) :
    (P.quotient G).convFamily.meanEntropy = (P.convFamily.quotient G).meanEntropy := by
  show ∑ p : P.index × P.index, P.weights p.1 * P.weights p.2 *
        entropyBits (conv ((P.laws p.1).map fun v => G.mkQ v)
          ((P.laws p.2).map fun v => G.mkQ v)) =
      ∑ p : P.index × P.index, P.weights p.1 * P.weights p.2 *
        entropyBits ((conv (P.laws p.1) (P.laws p.2)).map fun v => G.mkQ v)
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conv_map_mkQ]

/-- The objective (24) of Lemma 4.1: `Φ(G) = h(q_G ℛ) + (2 + d) h(q_G 𝒫) + 4λ dim G` with
`ℛ = 𝒫 * 𝒫`. -/
noncomputable def ratioObjective (P : WeightedFamily V) (lam d : ℝ)
    (G : Submodule (ZMod 2) V) : ℝ :=
  (P.convFamily.quotient G).meanEntropy + (2 + d) * (P.quotient G).meanEntropy +
    4 * lam * (Module.finrank (ZMod 2) G : ℝ)

/-- `Φ(0) = h(ℛ) + (2 + d) h(𝒫)`. -/
theorem ratioObjective_bot (P : WeightedFamily V) (lam d : ℝ) :
    P.ratioObjective lam d ⊥ = P.convFamily.meanEntropy + (2 + d) * P.meanEntropy := by
  unfold ratioObjective
  rw [meanEntropy_quotient, meanEntropy_quotient, averagedLoss_bot, averagedLoss_bot]
  simp

/-- Equation (26): at a global minimizer `G` of `Φ`, for every `W ≤ V ⧸ G`,
`F_{q_G ℛ}(W) + (2 + d) F_{q_G 𝒫}(W) ≤ 4λ dim W` (compare `G` with `W.comap G.mkQ`). -/
theorem ratioObjective_min_loss [Fintype V] (P : WeightedFamily V) (lam d : ℝ)
    (G : Submodule (ZMod 2) V)
    (hG : ∀ G' : Submodule (ZMod 2) V, P.ratioObjective lam d G ≤ P.ratioObjective lam d G')
    (W : Submodule (ZMod 2) (V ⧸ G)) :
    (P.convFamily.quotient G).averagedLoss W + (2 + d) * (P.quotient G).averagedLoss W ≤
      4 * lam * (Module.finrank (ZMod 2) W : ℝ) := by
  have h1 := hG (W.comap G.mkQ)
  unfold ratioObjective at h1
  simp only [meanEntropy_quotient, finrank_comap_mkQ G W] at h1
  simp only [averagedLoss_quotient]
  push_cast at h1
  nlinarith [h1]

/-- Items 2 and 3 of Lemma 4.1 at a global minimizer `G` of `Φ`, for `d ≥ 0`: `q_G 𝒫` is
`2λ`-sparse and `q_G 𝒫 * q_G 𝒫` is `4λ`-sparse. -/
theorem ratioObjective_min_sparse [Fintype V] (P : WeightedFamily V) (lam d : ℝ) (hd : 0 ≤ d)
    (G : Submodule (ZMod 2) V)
    (hG : ∀ G' : Submodule (ZMod 2) V, P.ratioObjective lam d G ≤ P.ratioObjective lam d G') :
    (P.quotient G).IsSparse (2 * lam) ∧ (P.quotient G).convFamily.IsSparse (4 * lam) := by
  haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (V ⧸ G) := Fintype.ofFinite _
  constructor
  · unfold WeightedFamily.IsSparse
    intro W
    have h := P.ratioObjective_min_loss lam d G hG W
    have hR := (P.convFamily.quotient G).averagedLoss_nonneg W
    have hP := (P.quotient G).averagedLoss_nonneg W
    nlinarith [mul_nonneg hd hP]
  · unfold WeightedFamily.IsSparse
    intro W
    rw [quotient_convFamily_averagedLoss]
    have h := P.ratioObjective_min_loss lam d G hG W
    have hP := (P.quotient G).averagedLoss_nonneg W
    nlinarith [mul_nonneg hd hP]

/-- By (15) on `q_G 𝒫`: `Φ(G) = (4 + d) h(q_G 𝒫) - e(q_G 𝒫) + 4λ dim G`. -/
theorem ratioObjective_eq (P : WeightedFamily V) (lam d : ℝ) (G : Submodule (ZMod 2) V) :
    P.ratioObjective lam d G = (4 + d) * (P.quotient G).meanEntropy -
      (P.quotient G).meanInteraction + 4 * lam * (Module.finrank (ZMod 2) G : ℝ) := by
  unfold ratioObjective
  rw [← quotient_convFamily_meanEntropy, meanEntropy_convFamily]
  ring

/-- `Φ(0) = 4 h(𝒫)` when `d h(𝒫) = e(𝒫)`. -/
theorem ratioObjective_bot_of (P : WeightedFamily V) (lam d : ℝ)
    (hd : d * P.meanEntropy = P.meanInteraction) :
    P.ratioObjective lam d ⊥ = 4 * P.meanEntropy := by
  rw [ratioObjective_bot, meanEntropy_convFamily]
  linear_combination hd

/-- Equation (25): if `d h(𝒫) = e(𝒫)` and `𝒫` is `λ`-sparse, then at a global minimizer `G` of
`Φ`, `d h(q_G 𝒫) ≤ e(q_G 𝒫)` (compare `G` with `0`, and use `F_𝒫(G) ≤ λ dim G`). -/
theorem ratioObjective_min_ratio (P : WeightedFamily V) (lam d : ℝ)
    (hd : d * P.meanEntropy = P.meanInteraction) (hsparse : P.IsSparse lam)
    (G : Submodule (ZMod 2) V)
    (hG : ∀ G' : Submodule (ZMod 2) V, P.ratioObjective lam d G ≤ P.ratioObjective lam d G') :
    d * (P.quotient G).meanEntropy ≤ (P.quotient G).meanInteraction := by
  have h0 := hG ⊥
  rw [ratioObjective_bot_of P lam d hd, ratioObjective_eq] at h0
  have hs := hsparse G
  have hq := P.meanEntropy_quotient G
  nlinarith

/-- Positivity in Lemma 4.1: at a global minimizer `G` of `Φ` of least dimension among the
global minimizers, `h(q_G 𝒫) > 0` (if `h(q_G 𝒫) = 0` then `Φ(0) ≤ Φ(G)`, so `dim G = 0`, and
sparsity forces `h(𝒫) = 0`). -/
theorem ratioObjective_min_pos [Fintype V] (P : WeightedFamily V) (lam d : ℝ)
    (hd : d * P.meanEntropy = P.meanInteraction) (hsparse : P.IsSparse lam)
    (hpos : 0 < P.meanEntropy) (G : Submodule (ZMod 2) V)
    (hG : ∀ G' : Submodule (ZMod 2) V, P.ratioObjective lam d G ≤ P.ratioObjective lam d G')
    (hmin : ∀ G' : Submodule (ZMod 2) V, P.ratioObjective lam d G' ≤ P.ratioObjective lam d G →
      Module.finrank (ZMod 2) G ≤ Module.finrank (ZMod 2) G') :
    0 < (P.quotient G).meanEntropy := by
  haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (V ⧸ G) := Fintype.ofFinite _
  by_contra hcon
  have hnn := (P.quotient G).meanEntropy_nonneg
  have h0 : (P.quotient G).meanEntropy = 0 := le_antisymm (not_lt.mp hcon) hnn
  have he0 : 0 ≤ (P.quotient G).meanInteraction := (P.quotient G).meanInteraction_nonneg
  have he1 : (P.quotient G).meanInteraction ≤ (P.quotient G).meanEntropy :=
    (P.quotient G).meanInteraction_le
  have hs := hsparse G
  have hq := P.meanEntropy_quotient G
  have hle : P.ratioObjective lam d ⊥ ≤ P.ratioObjective lam d G := by
    rw [ratioObjective_bot_of P lam d hd, ratioObjective_eq, h0]
    nlinarith
  have hdim0 : (Module.finrank (ZMod 2) G : ℝ) ≤ 0 := by
    have h1 : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = 0 := by simp
    have h2 := hmin ⊥ hle
    rw [h1] at h2
    exact_mod_cast h2
  have hn : (Module.finrank (ZMod 2) G : ℝ) = 0 := le_antisymm hdim0 (Nat.cast_nonneg _)
  rw [hn, mul_zero] at hs
  linarith

/-- **Lemma 4.1** (ratio-preserving sparsification): for `𝒫` `λ`-sparse with `h(𝒫) > 0`, a
least-dimensional global minimizer `G` of `Φ` with `d = e(𝒫)/h(𝒫)` has `h(q_G 𝒫) > 0`,
`e(q_G 𝒫)/h(q_G 𝒫) ≥ e(𝒫)/h(𝒫)`, `q_G 𝒫` `2λ`-sparse and `q_G 𝒫 * q_G 𝒫` `4λ`-sparse. -/
theorem ratio_preserving_sparsification_proof [Fintype V] (lam : ℝ) (P : WeightedFamily V)
    (hsparse : P.IsSparse lam) (hpos : 0 < P.meanEntropy) :
    ∃ G : Submodule (ZMod 2) V,
      0 < (P.quotient G).meanEntropy ∧
      P.meanInteraction / P.meanEntropy ≤
        (P.quotient G).meanInteraction / (P.quotient G).meanEntropy ∧
      (P.quotient G).IsSparse (2 * lam) ∧
      (P.quotient G).convFamily.IsSparse (4 * lam) := by
  haveI : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun G : Submodule (ZMod 2) V => (G : Set V))
      (fun _ _ h => SetLike.ext' h)
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = P.meanInteraction / P.meanEntropy := ⟨_, rfl⟩
  have hne : P.meanEntropy ≠ 0 := hpos.ne'
  have hd : d * P.meanEntropy = P.meanInteraction := by
    rw [hd_def]
    field_simp
  have hd0 : 0 ≤ d := by
    rw [hd_def]
    exact div_nonneg P.meanInteraction_nonneg hpos.le
  obtain ⟨G0, hG0⟩ := Finite.exists_min (P.ratioObjective lam d)
  obtain ⟨G, hGmem, hGmin⟩ := Set.exists_min_image
    {G : Submodule (ZMod 2) V | ∀ G', P.ratioObjective lam d G ≤ P.ratioObjective lam d G'}
    (fun G => Module.finrank (ZMod 2) G) (Set.toFinite _) ⟨G0, hG0⟩
  have hG : ∀ G' : Submodule (ZMod 2) V,
      P.ratioObjective lam d G ≤ P.ratioObjective lam d G' := hGmem
  have hmin : ∀ G' : Submodule (ZMod 2) V,
      P.ratioObjective lam d G' ≤ P.ratioObjective lam d G →
        Module.finrank (ZMod 2) G ≤ Module.finrank (ZMod 2) G' :=
    fun G' h' => hGmin G' (show ∀ G'' : Submodule (ZMod 2) V,
      P.ratioObjective lam d G' ≤ P.ratioObjective lam d G'' from fun G'' => h'.trans (hG G''))
  have hpos0 := ratioObjective_min_pos P lam d hd hsparse hpos G hG hmin
  have hrat := ratioObjective_min_ratio P lam d hd hsparse G hG
  obtain ⟨hs2, hs4⟩ := P.ratioObjective_min_sparse lam d hd0 G hG
  refine ⟨G, hpos0, ?_, hs2, hs4⟩
  rw [le_div_iff₀ hpos0, ← hd_def]
  exact hrat

end WeightedFamily
end EntropyLean
