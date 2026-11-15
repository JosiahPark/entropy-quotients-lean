/-
Draft items not yet in the library: verbatim excerpts from the original drafts in `archive/`.

NOT BUILT. This file is outside `EntropyLean/`, so `lake build` and `scripts/audit_sorries.py`
ignore it, and it is not tracked in ROADMAP.md or docs/DEPENDENCIES.md. It does not compile as is
(no imports, and the drafts contain errors listed in `missing/README.md`). Nothing here is proved.
The excerpts below are copied unchanged; only the `-- From ...` separator lines are added.

Compiled with Claude Fable 5.2 (claude-fable-5-2), 2026-11-15. The excerpts themselves are draft
text from `archive/` and were not written by Fable 5.2.
-/

-- From archive/EntropyQuotients.lean, lines 142-184
-- (the same file was uploaded again as `EntropyQuotients (2).lean`)

/-- Binary entropy in bits. -/
noncomputable def binEntropyBits (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then
    -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)
  else 0

lemma binEntropyBits_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < binEntropyBits p := by
  sorry

/-- Asymptotic used in the proof of Prop. 9.3:
For p = 2^{-c/ε} with c < 2, the ratio E/H exceeds ε/(1+ε) for small ε. -/
lemma bernoulli_defect_ratio_exceeds
    (c : ℝ) (hc : 0 < c) (hc2 : c < 2) :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      let p := (2 : ℝ) ^ (-c / ε)
      0 < p ∧ p < 1 ∧
      binEntropyBits p > 0 ∧
      -- E(X)/H(X) > ε/(1+ε) for the Bernoulli law with parameter p
      True := by  -- placeholder for the full calculation
  sorry



/-! ## Auxiliary lemmas for the necessity argument -/

/-- Conversion between mathlib's Real.binEntropy (nats) and bit-entropy. -/
lemma binEntropy_bits_eq (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    binEntropyBits p = Real.binEntropy p / Real.log 2 := by
  unfold binEntropyBits
  rw [if_pos ⟨hp0, hp1⟩]
  have hlog : Real.logb 2 = fun x => Real.log x / Real.log 2 := funext Real.logb
  -- Real.binEntropy p = -p * log p - (1-p) * log (1-p)
  -- so dividing by log 2 gives the bit version.
  -- rw [Real.binEntropy] -- needs adjustment
  sorry
  ring

/-- For small p the binary entropy is asymptotically p log₂(1/p). -/
lemma binEntropyBits_asymp (p : ℝ) (hp : 0 < p) (hp1 : p < 1/2) :
    binEntropyBits p = p * Real.logb 2 (1 / p) + p * Real.logb 2 (Real.exp 1) +
      o(p * Real.logb 2 (1 / p)) := by
  sorry  -- standard expansion; can be extracted from known asymptotics of binEntropy

-- From archive/EntropyQuotients_formalization.lean, lines 31-52
-- (the same file was uploaded again as `EntropyQuotients_formalization (1).lean`)

/-- Binary Shannon entropy (base 2). -/
noncomputable def h2 (p : ℝ) : ℝ :=
  if 0 < p ∧ p < 1 then -p * logb 2 p - (1 - p) * logb 2 (1 - p) else 0

lemma h2_zero_at_extremes (p : ℝ) (h : ¬ (0 < p ∧ p < 1)) : h2 p = 0 := by
  simp [h2, h]

/-- Entropy increment for a Bernoulli(p) bit. -/
noncomputable def D_bern (p : ℝ) : ℝ := 2 * h2 p - h2 (2 * p * (1 - p))

/-- Proposition 9.3 (Necessity of the exponential scale).
If C(ε) is a universal coefficient for the entropy quotient statement, then
liminf_{ε ↓ 0} ε log₂ C(ε) ≥ 2. -/
theorem prop_9_3_necessity
    (C : ℝ → ℝ)
    (hvalid : ∀ ε > 0, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
      h2 p > (1 + ε) * D_bern p → C ε ≥ 1 / h2 p) :
    liminf (fun ε => ε * logb 2 (C ε)) (nhdsWithin 0 (Set.Ioi 0)) ≥ 2 := by
  -- Construction: for c < 2 set p := 2^{-c/ε}. Asymptotics give E/H > ε/(1+ε)
  -- for small ε, forcing the 0-subspace to fail and thus C(ε) ≥ 1/h2(p).
  -- Then ε log2 C(ε) ≥ ε log2 (1/h2(p)) → c. Let c ↑ 2.
  sorry

-- From archive/Entropy.lean, lines 147-159

/-- Auxiliary: binary entropy function. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if p = 0 ∨ p = 1 then 0 else -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

/-- The single-bit Bernoulli example shows the exponential necessity.
As p = 2^{-c/ε} ↓ 0, h₂(p) ∼ p log₂(1/p), and E(X)/H(X) ∼ 2ε/c.
For small ε this exceeds ε/(1+ε), forcing the dimension coefficient to be at least ~1/h₂(p) which is exponential in 1/ε. -/
theorem bernoulli_necessity_example (c : ℝ) (hc : 0 < c ∧ c < 2) (ε : ℝ) (hε : 0 < ε) :
    let p := (2 : ℝ) ^ (-c / ε)
    binaryEntropy p > 0 ∧
    -- Further expansion and comparison to be formalized
    True :=
  sorry
