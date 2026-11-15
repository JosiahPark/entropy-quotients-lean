import Mathlib
import EntropyLean.ScaleNecessary
import EntropyLean.ScaleNecessaryLimit
import EntropyLean.ScaleNecessaryLog

/-!
# Proposition 9.3 (roadmap item E3c)

`exponential_scale_necessary_proof`: **Proposition 9.3** of arXiv:2610.38525, in the form of
`exponential_scale_necessary` in `EntropyLean/Statements.lean`: if `C ε` is valid for every law on
every `F₂^m` in the original-input form `dim G ≤ C(ε) H(X)`, `H(q_G X) ≤ (1+ε) D(X)`, then for
every `c < 2`, eventually as `ε ↓ 0`, `c ≤ ε log₂ C(ε)`.

Proof: take `a = (max(c, 1) + 2)/2`, so `c < a < 2`, and `p = scaleParam a ε = 2^(−a/ε)`.
Eventually as `ε ↓ 0`, `ε h₂(p) < (1+ε) bernoulliDefect p` (E3b1, `scale_gap_eventually`), so
E3a (`one_le_C_mul_binaryEntropy`) gives `C(ε) ≥ 1/h₂(p) > 0`, and
`ε log₂ C(ε) ≥ −ε log₂ h₂(p) ≥ c` (E3b2, `scale_log_eventually`).

What this file does NOT prove: anything about Theorem 1.1, 1.2 or 8.2. Proposition 9.3 is a
lower bound on any valid coefficient `C(ε)`; the hypothesis `hC` that some `C` is valid is not
proved here.
-/

namespace EntropyLean

open Filter

/-- **Proposition 9.3** (exponential scale is necessary), in the form of
`exponential_scale_necessary`: if `C ε` is valid for every law on every `F₂^m` in the
original-input form, then for every `c < 2`, eventually as `ε ↓ 0`, `c ≤ ε log₂ C(ε)`. -/
theorem exponential_scale_necessary_proof (C : ℝ → ℝ)
    (hC : ∀ ε > 0, ∀ (m : ℕ) (X : PMF (F2Vec m)), ∃ G : Submodule (ZMod 2) (F2Vec m),
      (Module.finrank (ZMod 2) G : ℝ) ≤ C ε * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤ (1 + ε) * entropyIncrement X) :
    ∀ c : ℝ, c < 2 → ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), c ≤ ε * Real.logb 2 (C ε) := by
  intro c hc
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (max c 1 + 2) / 2 := ⟨_, rfl⟩
  have hmax : max c 1 < 2 := max_lt hc (by norm_num)
  have hm1 : (1 : ℝ) ≤ max c 1 := le_max_right c 1
  have hm0 : c ≤ max c 1 := le_max_left c 1
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have ha2 : a < 2 := by rw [ha_def]; linarith
  have hca : c < a := by rw [ha_def]; linarith
  filter_upwards [scale_gap_eventually ha0 ha2, scale_log_eventually ha0 hca,
    self_mem_nhdsWithin] with ε hgap hlog hεpos
  have hε : (0 : ℝ) < ε := Set.mem_Ioi.mp hεpos
  have hp0 := scaleParam_pos a ε
  have hp1 := scaleParam_lt_one ha0 hε
  have h1 := one_le_C_mul_binaryEntropy C hC hε hp0 hp1 hgap
  have hh0 := slog_entropy_pos ha0 hε
  have hlow : 1 / binaryEntropy (scaleParam a ε) ≤ C ε := by
    rw [div_le_iff₀ hh0]
    exact h1
  have hlogC : Real.logb 2 (1 / binaryEntropy (scaleParam a ε)) ≤ Real.logb 2 (C ε) :=
    Real.logb_le_logb_of_le (by norm_num) (one_div_pos.mpr hh0) hlow
  rw [one_div, Real.logb_inv] at hlogC
  have hmul := mul_le_mul_of_nonneg_left hlogC hε.le
  rw [mul_neg] at hmul
  linarith

end EntropyLean
