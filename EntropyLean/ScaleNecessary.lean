import EntropyLean.MathlibForPFR
import EntropyLean.BernoulliLaw
import EntropyLean.Variational

/-!
# Proposition 9.3, first step: the one-bit example forces `dim G ≥ 1` (roadmap item E3a)

`bernoulliVec p` is the law on `F2Vec 1` of the Bernoulli(p) bit `bernoulliBit p`, embedded by the
injective additive map `bitEmbed : b ↦ (fun _ => b)`. Proved here:

* `entropyBits_bernoulliVec`, `entropyDefect_bernoulliVec`: `H = h₂(p)` and `E = bernoulliDefect p`;
* `dim_pos_of_defect_gt`: if `H(q_G X) ≤ (1+ε) D(X)` and `ε H(X) < (1+ε) E(X)`, then `dim G ≥ 1`
  (for `G = 0` the quotient map is injective, so the first inequality reads
  `H(X) ≤ (1+ε)(H(X) − E(X))`, contradicting the second);
* `one_le_C_mul_binaryEntropy`: under the hypothesis `hC` of `exponential_scale_necessary`, for
  `0 < p < 1` with `ε h₂(p) < (1+ε) bernoulliDefect p`, one has `1 ≤ C(ε) h₂(p)`.

What this file does NOT prove: Proposition 9.3 itself (`exponential_scale_necessary`). The choice
`p = 2^(−c/ε)` and the limit `ε log₂ C(ε) → c` (items E3b, E3c) are not done here.
-/

namespace EntropyLean

/-- The injective additive map `ZMod 2 → F2Vec 1`, `b ↦ (fun _ => b)`. -/
def bitEmbed : ZMod 2 →+ F2Vec 1 where
  toFun b := fun _ => b
  map_zero' := by
    funext i
    rfl
  map_add' a b := by
    funext i
    rfl

theorem bitEmbed_injective : Function.Injective bitEmbed := by
  intro a b h
  first
    | exact congrFun h 0
    | simpa [bitEmbed] using congrFun h 0

/-- A Bernoulli(p) bit as a law on `F2Vec 1`. -/
noncomputable def bernoulliVec (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF (F2Vec 1) :=
  (bernoulliBit p h0 h1).map bitEmbed

theorem entropyBits_bernoulliVec (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropyBits (bernoulliVec p h0 h1) = binaryEntropy p := by
  unfold bernoulliVec
  rw [entropyBits_map_of_injective _ bitEmbed_injective]
  exact entropyBits_bernoulliBit p h0 h1

theorem entropyDefect_bernoulliVec (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropyDefect (bernoulliVec p h0 h1) = bernoulliDefect p := by
  have h := entropyDefect_bernoulliBit p h0 h1
  unfold entropyDefect at h ⊢
  unfold bernoulliVec
  rw [← conv_map_hom bitEmbed, entropyBits_map_of_injective _ bitEmbed_injective,
    entropyBits_map_of_injective _ bitEmbed_injective]
  linarith

/-- If `H(q_G X) ≤ (1+ε) D(X)` while `ε H(X) < (1+ε) E(X)`, then `G ≠ 0`, i.e. `dim G ≥ 1`. -/
theorem dim_pos_of_defect_gt {m : ℕ} (ε : ℝ) (X : PMF (F2Vec m))
    (G : Submodule (ZMod 2) (F2Vec m))
    (hG : entropyBits (X.map fun v => G.mkQ v) ≤ (1 + ε) * entropyIncrement X)
    (hgap : ε * entropyBits X < (1 + ε) * entropyDefect X) :
    1 ≤ (Module.finrank (ZMod 2) G : ℝ) := by
  rcases Nat.eq_zero_or_pos (Module.finrank (ZMod 2) G) with h0 | hpos
  · exfalso
    have hbot : G = ⊥ := by
      first
        | exact Submodule.finrank_eq_zero.mp h0
        | exact finrank_eq_zero.mp h0
    subst hbot
    have hq := quotientLoss_bot X
    unfold quotientLoss at hq
    rw [entropyDefect_eq] at hgap
    nlinarith [hq, hG, hgap]
  · have h1 : 1 ≤ Module.finrank (ZMod 2) G := hpos
    exact_mod_cast h1

/-- **E3a.** Under the hypothesis of Proposition 9.3, a Bernoulli parameter `p ∈ (0, 1)` with
`ε h₂(p) < (1+ε) bernoulliDefect p` forces `1 ≤ C(ε) h₂(p)`. -/
theorem one_le_C_mul_binaryEntropy (C : ℝ → ℝ)
    (hC : ∀ ε > 0, ∀ (m : ℕ) (X : PMF (F2Vec m)), ∃ G : Submodule (ZMod 2) (F2Vec m),
      (Module.finrank (ZMod 2) G : ℝ) ≤ C ε * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤ (1 + ε) * entropyIncrement X)
    {ε p : ℝ} (hε : 0 < ε) (h0 : 0 < p) (h1 : p < 1)
    (hgap : ε * binaryEntropy p < (1 + ε) * bernoulliDefect p) :
    1 ≤ C ε * binaryEntropy p := by
  obtain ⟨G, hdim, hG⟩ := hC ε hε 1 (bernoulliVec p h0.le h1.le)
  rw [entropyBits_bernoulliVec] at hdim
  have hgap' : ε * entropyBits (bernoulliVec p h0.le h1.le) <
      (1 + ε) * entropyDefect (bernoulliVec p h0.le h1.le) := by
    rw [entropyBits_bernoulliVec, entropyDefect_bernoulliVec]
    exact hgap
  have h := dim_pos_of_defect_gt ε _ G hG hgap'
  linarith

end EntropyLean
