import EntropyLean.MathlibForPFR
import EntropyLean.DensityEstimate
import EntropyLean.Variational

/-!
# Averaged density estimate, square-root form (roadmap item D5c, Lemma 5.1)

Inequality (29) of Lemma 5.1 of arXiv:2610.38525: for an averaged `λ`-sparse family `𝒬`
(`λ ≥ 0`) and subspaces `V(u, w)`, with `A = E_{u,w} s_{V(u,w)}(Q_u, Q_w)`,
`B = E_{u,w} dim V(u, w)` and `h = h(𝒬)`,
`B ≤ 26 h ⇒ A ≤ 14 √λ h`.

* `density_sqrt_arith`: the real-number step. From (28) `A ≤ h/N + λ B (N − 1)/2` for every
  `N ≥ 1`: for `λ > 0` take `N = ⌈λ^{-1/2}⌉`, so `h/N ≤ √λ h` and `λ (N − 1) ≤ √λ`; for `λ = 0`
  let `N → ∞`. (No separate case `λ > 1` is needed.)
* `WeightedFamily.averaged_density_sqrt`: inequality (29), from `averaged_density_estimate` (D5b).
* `WeightedFamily.averaged_density_lemma`: Lemma 5.1, both (28) and (29).

What this file does NOT prove: nothing about Lemmas 6.1–8.1 or Theorems 1.1, 1.2, 8.2.
-/

namespace EntropyLean

/-- The arithmetic of (29) from (28): if `A ≤ h/N + λ B (N − 1)/2` for every `N ≥ 1`,
`h ≥ 0`, `λ ≥ 0` and `B ≤ 26 h`, then `A ≤ 14 √λ h`. -/
theorem density_sqrt_arith {A B h lam : ℝ} (h0 : 0 ≤ h) (hlam : 0 ≤ lam) (hB : B ≤ 26 * h)
    (hest : ∀ N : ℕ, 0 < N → A ≤ h / N + lam * B * ((N : ℝ) - 1) / 2) :
    A ≤ 14 * Real.sqrt lam * h := by
  rcases hlam.eq_or_lt with hl0 | hlpos
  · -- `λ = 0`: `A ≤ h/N` for every `N ≥ 1`, hence `A ≤ 0`.
    rw [← hl0, Real.sqrt_zero]
    have hz : (14 : ℝ) * 0 * h = 0 := by ring
    rw [hz]
    by_contra hA
    push_neg at hA
    obtain ⟨N, hN⟩ := exists_nat_gt (h / A)
    have hq : 0 ≤ h / A := div_nonneg h0 hA.le
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt hq hN
    have hN' : 0 < N := by exact_mod_cast hNpos
    have h1 : h < N * A := (div_lt_iff₀ hA).mp hN
    have h2 : h / N < A := (div_lt_iff₀ hNpos).mpr (by linarith)
    have h3 := hest N hN'
    have h4 : lam * B * ((N : ℝ) - 1) / 2 = 0 := by rw [← hl0]; ring
    linarith
  · -- `λ > 0`: take `N = ⌈1/√λ⌉`.
    obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt lam := ⟨_, rfl⟩
    rw [← hs]
    have hspos : 0 < s := by
      rw [hs]
      exact Real.sqrt_pos.mpr hlpos
    have hsne : s ≠ 0 := hspos.ne'
    have hss : s * s = lam := by
      rw [hs]
      exact Real.mul_self_sqrt hlam
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈1 / s⌉₊ := ⟨_, rfl⟩
    have hinv : 0 < 1 / s := div_pos one_pos hspos
    have hle : 1 / s ≤ (N : ℝ) := by
      rw [hNdef]
      exact Nat.le_ceil _
    have hlt : (N : ℝ) < 1 / s + 1 := by
      rw [hNdef]
      exact Nat.ceil_lt_add_one hinv.le
    have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hinv hle
    have hN' : 0 < N := by exact_mod_cast hNpos
    have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr hN'
    have hsinv : s * (1 / s) = 1 := mul_one_div_cancel hsne
    have hNs : 1 ≤ s * N := by
      have := mul_le_mul_of_nonneg_left hle hspos.le
      linarith
    have hsN : s * ((N : ℝ) - 1) ≤ 1 := by
      have h' : (N : ℝ) - 1 < 1 / s := by linarith
      have := mul_lt_mul_of_pos_left h' hspos
      linarith
    have hfirst : h / N ≤ s * h := by
      rw [div_le_iff₀ hNpos]
      have := mul_le_mul_of_nonneg_left hNs h0
      linarith
    have ht0 : 0 ≤ lam * ((N : ℝ) - 1) := mul_nonneg hlam (by linarith)
    have hts : lam * ((N : ℝ) - 1) ≤ s := by
      have e : lam * ((N : ℝ) - 1) = s * (s * ((N : ℝ) - 1)) := by rw [← hss]; ring
      have := mul_le_mul_of_nonneg_left hsN hspos.le
      linarith
    have hsecond : lam * B * ((N : ℝ) - 1) / 2 ≤ 13 * (s * h) := by
      have e : lam * B * ((N : ℝ) - 1) / 2 = B * (lam * ((N : ℝ) - 1)) / 2 := by ring
      have h1 := mul_le_mul_of_nonneg_right hB ht0
      have h2 := mul_le_mul_of_nonneg_left hts (by linarith : (0 : ℝ) ≤ 26 * h)
      linarith
    have h3 := hest N hN'
    linarith

namespace WeightedFamily

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Lemma 5.1, inequality (29): for a `λ`-sparse family (`λ ≥ 0`) and subspaces `V(u, w)` with
`B = E_{u,w} dim V(u, w) ≤ 26 h(𝒬)`, `A = E_{u,w} s_{V(u,w)}(Q_u, Q_w) ≤ 14 √λ h(𝒬)`. -/
theorem averaged_density_sqrt [Fintype V] {lam : ℝ} (Q : WeightedFamily V)
    (hsp : Q.IsSparse lam) (hlam : 0 ≤ lam) (Vf : Q.index → Q.index → Submodule (ZMod 2) V)
    (hB : ∑ u, Q.weights u * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ) ≤
      26 * Q.meanEntropy) :
    ∑ u, Q.weights u * ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf u w) ≤
      14 * Real.sqrt lam * Q.meanEntropy :=
  density_sqrt_arith Q.meanEntropy_nonneg hlam hB
    (fun N hN => Q.averaged_density_estimate hsp hlam Vf N hN)

/-- Lemma 5.1 (averaged density estimate): inequalities (28) and (29) together. -/
theorem averaged_density_lemma [Fintype V] {lam : ℝ} (Q : WeightedFamily V)
    (hsp : Q.IsSparse lam) (hlam : 0 ≤ lam) (Vf : Q.index → Q.index → Submodule (ZMod 2) V) :
    (∀ N : ℕ, 0 < N →
      ∑ u, Q.weights u * ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf u w) ≤
        Q.meanEntropy / N +
          lam * (∑ u, Q.weights u * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ)) *
            ((N : ℝ) - 1) / 2) ∧
    (∑ u, Q.weights u * ∑ w, Q.weights w * (Module.finrank (ZMod 2) (Vf u w) : ℝ) ≤
        26 * Q.meanEntropy →
      ∑ u, Q.weights u * ∑ w, Q.weights w * subspaceInteraction (Q.laws u) (Q.laws w) (Vf u w) ≤
        14 * Real.sqrt lam * Q.meanEntropy) :=
  ⟨fun N hN => Q.averaged_density_estimate hsp hlam Vf N hN,
    fun hB => Q.averaged_density_sqrt hsp hlam Vf hB⟩

end WeightedFamily

end EntropyLean
