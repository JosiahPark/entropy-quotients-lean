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

What this file does NOT prove: items 1 (ratio `e/h` does not decrease, equation (25)) and the
positivity `h(q_G 𝒫) > 0` of Lemma 4.1, nor Lemma 4.1 itself (`ratio_preserving_sparsification`
in `EntropyLean/Statements.lean` remains an open obligation); those are roadmap item C4b. Nothing here
concerns Theorem 1.1, 1.2 or 8.2.
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

end WeightedFamily
end EntropyLean
