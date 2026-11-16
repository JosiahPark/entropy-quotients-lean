import Mathlib
import EntropyLean.MartonPartial
import EntropyLean.BernoulliLaw

/-!
# The entropic Marton bound on spaces of dimension at most one (roadmap item H4a)

Proved here:
* `martonInput_of_finrank_eq_zero`: (35) holds on a zero-dimensional F₂-space (witness `⊤`,
  since `dim V − H(K) = −H(K) ≤ 0 ≤ 12 D(K)`);
* `entropyBits_map_addEquiv`, `entropyIncrement_map_addEquiv`: `H` and `D` are invariant under
  an additive equivalence;
* `eq_bernoulliBit`: every law on `ZMod 2` is the Bernoulli law with parameter its mass at `1`;
* `martonInput_of_finrank_eq_one_of_bernoulli`: on a one-dimensional F₂-space, (35) follows from
  the one-variable inequality `min(h₂(p), 1 − h₂(p)) ≤ 12 (h₂(2p(1−p)) − h₂(p))` for
  `0 ≤ p ≤ 1`, which enters as the explicit hypothesis `hB` (witness `⊥` or `⊤`).

What this file does NOT prove: the Bernoulli inequality `hB` itself (roadmap item H4b), hence
not yet `martonInput_of_finrank_le_one` without hypotheses (item H4c); and not the entropic
Marton bound (35) in any dimension `≥ 2`.
-/

namespace EntropyLean

section MartonOneBit

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- (35) on a zero-dimensional space: `dim V − H(K) = −H(K) ≤ 0 ≤ 12 D(K)`. -/
theorem martonInput_of_finrank_eq_zero (h : Module.finrank (ZMod 2) V = 0) :
    MartonInput V := by
  refine ⟨fun K => marton_of_codim_le K ?_⟩
  have hH := entropyBits_nonneg K
  have hD := entropyIncrement_nonneg K
  rw [h, Nat.cast_zero]
  linarith

omit [Module (ZMod 2) V] in
/-- Entropy is invariant under an additive equivalence. -/
theorem entropyBits_map_addEquiv {V' : Type*} [AddCommGroup V'] [Fintype V'] (e : V ≃+ V')
    (K : PMF V) : entropyBits (K.map e) = entropyBits K :=
  entropyBits_map_injective K e.injective

omit [Module (ZMod 2) V] in
/-- The entropy increment is invariant under an additive equivalence. -/
theorem entropyIncrement_map_addEquiv {V' : Type*} [AddCommGroup V'] [Fintype V']
    (e : V ≃+ V') (K : PMF V) : entropyIncrement (K.map e) = entropyIncrement K := by
  unfold entropyIncrement
  rw [← conv_map_of_add e (map_add e) K K, entropyBits_map_addEquiv e (conv K K),
    entropyBits_map_addEquiv e K]

/-- Every law on `ZMod 2` is the Bernoulli law with parameter its mass at `1`. -/
theorem eq_bernoulliBit (P : PMF (ZMod 2)) :
    P = bernoulliBit (P 1).toReal ENNReal.toReal_nonneg (pmf_toReal_le_one P 1) := by
  apply pmf_ext_toReal
  intro x
  have hs := pmf_sum_toReal P
  simp only [sum_zmod2_eq] at hs
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · rw [bernoulliBit_toReal_zero]
    linarith
  · rw [bernoulliBit_toReal_one]

/-- (35) on a one-dimensional space, from the Bernoulli inequality
`min(h₂(p), 1 − h₂(p)) ≤ 12 (h₂(2p(1−p)) − h₂(p))` (an explicit hypothesis here). -/
theorem martonInput_of_finrank_eq_one_of_bernoulli (h : Module.finrank (ZMod 2) V = 1)
    (hB : ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      min (binaryEntropy p) (1 - binaryEntropy p) ≤ 12 * bernoulliIncrement p) :
    MartonInput V := by
  haveI : Module.Finite (ZMod 2) V := by
    first
      | infer_instance
      | exact Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) (ZMod 2) := by
    rw [h, Module.finrank_self]
  obtain ⟨e⟩ : Nonempty (V ≃+ ZMod 2) := by
    first
      | exact ⟨(LinearEquiv.ofFinrankEq V (ZMod 2) hdim).toAddEquiv⟩
      | exact ⟨(LinearEquiv.ofFinrankEq hdim).toAddEquiv⟩
      | exact ⟨(FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hdim).some.toAddEquiv⟩
  refine ⟨fun K => ?_⟩
  have h0 : 0 ≤ ((K.map e) 1).toReal := ENNReal.toReal_nonneg
  have h1 : ((K.map e) 1).toReal ≤ 1 := pmf_toReal_le_one _ 1
  have hBern : K.map e = bernoulliBit _ h0 h1 := eq_bernoulliBit (K.map e)
  have hH : entropyBits K = binaryEntropy ((K.map e) 1).toReal := by
    calc entropyBits K = entropyBits (K.map e) := (entropyBits_map_addEquiv e K).symm
      _ = entropyBits (bernoulliBit _ h0 h1) := congrArg entropyBits hBern
      _ = binaryEntropy ((K.map e) 1).toReal := entropyBits_bernoulliBit _ h0 h1
  have hD : entropyIncrement K = bernoulliIncrement ((K.map e) 1).toReal := by
    calc entropyIncrement K = entropyIncrement (K.map e) :=
          (entropyIncrement_map_addEquiv e K).symm
      _ = entropyIncrement (bernoulliBit _ h0 h1) := congrArg entropyIncrement hBern
      _ = bernoulliIncrement ((K.map e) 1).toReal := entropyIncrement_bernoulliBit _ h0 h1
  rcases min_le_iff.mp (hB _ h0 h1) with hb | hb
  · refine marton_of_entropy_le K ?_
    rw [hH, hD]
    exact hb
  · refine marton_of_codim_le K ?_
    rw [h, Nat.cast_one, hH, hD]
    exact hb

end MartonOneBit

end EntropyLean
