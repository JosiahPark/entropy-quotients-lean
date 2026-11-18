import EntropyLean.MathlibForPFR
import EntropyLean.MartonConv

/-!
# Entropy of a law smoothed by the uniform law on a subspace (roadmap item D7b2b, Section 7)

For a law `K` on a finite F₂-space `V` and a subspace `W`, the law `K * U_W` of `A + U`
(`A ∼ K`, `U` uniform on `W`, independent) has masses `c(v) = (q_W K)(q_W v) / |W|`
(`conv_uniformSub_toReal`). Splitting `−c log₂ c` and summing over each coset gives
`H(K * U_W) = H(q_W K) + log₂ |W| = H(q_W K) + dim W`.

This file proves
* `uniformSmooth_term_eq`: `N · (−(p/N) log₂(p/N)) = −p log₂ p + p log₂ N` for `N > 0`;
* `sum_smooth_comp_mkQ`: `∑_v −c(v) log₂ c(v) = ∑_x −p(x) log₂ p(x) + dim W` for
  `c(v) = p(q_W v) / |W|` and `∑_x p(x) = 1`;
* `entropyBits_conv_uniformSub`: `H(K * U_W) = H(q_W K) + dim W`;
* `ruzsaDist_uniformSub`: `d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2`, which is the hypothesis
  `hsmooth` of `MartonInput.consequence_of_smoothing`.

What this file does NOT prove: the lower bound `|dim W − H(K)| / 2 ≤ d(K, U_W)` (roadmap item
D7c; the hypothesis `hlow` of `MartonInput.consequence_of_smoothing`), equation (36) without
hypotheses, nor the entropic Marton bound (35), which stays a hypothesis.
-/

namespace EntropyLean

/-- Splitting one entropy term: `N · (−(p/N) log₂(p/N)) = −p log₂ p + p log₂ N` for `N > 0`
(both sides vanish at `p = 0`). -/
theorem uniformSmooth_term_eq (p N : ℝ) (hN : 0 < N) :
    N * (-(p / N) * Real.logb 2 (p / N)) = -p * Real.logb 2 p + p * Real.logb 2 N := by
  by_cases hp : p = 0
  · rw [hp]
    simp
  · have h : N * (p / N) = p := by
      rw [div_eq_mul_inv, mul_comm p, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
    rw [Real.logb_div hp hN.ne']
    calc N * (-(p / N) * (Real.logb 2 p - Real.logb 2 N))
        = -(N * (p / N)) * (Real.logb 2 p - Real.logb 2 N) := by ring
      _ = -p * Real.logb 2 p + p * Real.logb 2 N := by rw [h]; ring

section UniformConvEntropy

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- For `c(v) = p(q_W v) / |W|` with `∑_x p(x) = 1`:
`∑_v −c(v) log₂ c(v) = ∑_x −p(x) log₂ p(x) + dim W`. -/
theorem sum_smooth_comp_mkQ (W : Submodule (ZMod 2) V) [Fintype (V ⧸ W)]
    [DecidableEq (V ⧸ W)] (p : V ⧸ W → ℝ) (hp : ∑ x, p x = 1) :
    ∑ v, -(p (W.mkQ v) / (subCard W : ℝ)) * Real.logb 2 (p (W.mkQ v) / (subCard W : ℝ)) =
      ∑ x, -p x * Real.logb 2 (p x) + (Module.finrank (ZMod 2) W : ℝ) := by
  have hN : (0 : ℝ) < (subCard W : ℝ) := by exact_mod_cast subCard_pos W
  have hlog : Real.logb 2 (subCard W : ℝ) = (Module.finrank (ZMod 2) W : ℝ) :=
    (entropyBits_uniformSub_card W).symm.trans (entropyBits_uniformSub W)
  rw [sum_comp_mkQ W
      (fun x => -(p x / (subCard W : ℝ)) * Real.logb 2 (p x / (subCard W : ℝ))),
    Finset.mul_sum]
  simp only [uniformSmooth_term_eq _ _ hN]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul, hlog]

/-- Smoothing by the uniform law on `W`: `H(K * U_W) = H(q_W K) + dim W`. -/
theorem entropyBits_conv_uniformSub (K : PMF V) (W : Submodule (ZMod 2) V) :
    entropyBits (conv K (uniformSub W)) =
      entropyBits (K.map fun v => W.mkQ v) + (Module.finrank (ZMod 2) W : ℝ) := by
  classical
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  rw [entropyBits_eq_sum, entropyBits_eq_sum]
  have h1 : ∀ v : V, -(conv K (uniformSub W) v).toReal *
      Real.logb 2 (conv K (uniformSub W) v).toReal =
      -(((K.map fun a => W.mkQ a) (W.mkQ v)).toReal / (subCard W : ℝ)) *
        Real.logb 2 (((K.map fun a => W.mkQ a) (W.mkQ v)).toReal / (subCard W : ℝ)) := by
    intro v
    rw [conv_uniformSub_toReal]
  rw [Finset.sum_congr rfl fun v _ => h1 v]
  exact sum_smooth_comp_mkQ W (fun x => ((K.map fun a => W.mkQ a) x).toReal)
    (pmf_sum_toReal _)

/-- The uniform-smoothing formula for the Ruzsa distance:
`d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2`. -/
theorem ruzsaDist_uniformSub (K : PMF V) (W : Submodule (ZMod 2) V) :
    ruzsaDist K (uniformSub W) =
      entropyBits (K.map fun v => W.mkQ v) +
        ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K) / 2 := by
  unfold ruzsaDist
  rw [entropyBits_conv_uniformSub, entropyBits_uniformSub]
  ring

end UniformConvEntropy

end EntropyLean
