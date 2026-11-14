import Mathlib
import EntropyLean.Conditional

/-!
# Corollary 9.2 conditional on Theorem 8.2 (roadmap item C5)

Two-input almost-additivity. For `0 < α < 1` and independent laws `U`, `Y` on a finite
`F₂`-space, `two_input_almost_additivity_of_rigidity` gives a subspace `G` with
`dim G ≤ 2^(320/α) (H(U) + H(Y))/2` (45) such that
`H(q_G U + q_G Y) ≥ (1 − α)(H(q_G U) + H(q_G Y))` (46), the additive error
`s(q_G U, q_G Y) ≤ α (H(U) + H(Y))`, and the two mixed-input bounds
`H(q_G U) ≤ H(U + Y) − H(Y) + α (H(q_G U) + H(q_G Y))` and its mirror image.

Proof (Section 9.2 of the paper): Lemma 9.1 (`WeightedFamily.variational_sparsification_proof`)
for the family `{U, Y}` with weights `1/2` (`WeightedFamily.pair`) and `λ = 2^(-320/α)`;
Theorem 8.2 for the quotient family gives `e ≤ α h`; the self-interactions are nonnegative and
`s` is symmetric (`conv_comm_law`), so `s(q_G U, q_G Y) ≤ α (H(q_G U) + H(q_G Y))`; data
processing (`entropyBits_sub_map_le_conv`) gives the mixed-input bounds.

Also: `conv_comm_law`, `interaction_comm`, `WeightedFamily.pair` with `meanEntropy_pair`,
`meanInteraction_pair` and their quotient versions.

What this file does NOT prove: Theorem 8.2, which enters only as the explicit hypothesis
`hrig : WeightedFamilyRigidity`; hence Corollary 9.2 itself is NOT proved unconditionally.
-/

universe u

namespace EntropyLean

/-- Convolution of laws is commutative on an additive commutative monoid. -/
theorem conv_comm_law {V : Type*} [AddCommMonoid V] (P Q : PMF V) : conv P Q = conv Q P := by
  calc conv P Q = Q.bind fun b => P.bind fun a => PMF.pure (a + b) :=
        PMF.bind_comm P Q (fun a b => PMF.pure (a + b))
    _ = conv Q P := by
        show _ = Q.bind fun a => P.bind fun b => PMF.pure (a + b)
        congr 1
        funext b
        congr 1
        funext a
        rw [add_comm]

/-- The interaction is symmetric: `s(P, Q) = s(Q, P)`. -/
theorem interaction_comm {V : Type*} [AddCommMonoid V] (P Q : PMF V) :
    interaction P Q = interaction Q P := by
  unfold interaction
  rw [conv_comm_law P Q]
  ring

namespace WeightedFamily

variable {V : Type*}

/-- The family `{U, Y}` with weights `1/2, 1/2`. -/
noncomputable def pair (U Y : PMF V) : WeightedFamily V where
  index := Bool
  laws := fun b => cond b U Y
  weights := fun _ => 1 / 2
  weights_pos := fun _ => by norm_num
  weights_sum := by
    rw [Fintype.sum_bool]
    norm_num

theorem meanEntropy_pair (U Y : PMF V) :
    (pair U Y).meanEntropy = (entropyBits U + entropyBits Y) / 2 := by
  show ∑ b : Bool, (1 / 2 : ℝ) * entropyBits (cond b U Y) = _
  rw [Fintype.sum_bool]
  show (1 / 2 : ℝ) * entropyBits U + 1 / 2 * entropyBits Y = _
  ring

theorem meanInteraction_pair [AddCommMonoid V] (U Y : PMF V) :
    (pair U Y).meanInteraction =
      (entropyDefect U + entropyDefect Y) / 4 + interaction U Y / 2 := by
  show ∑ a : Bool, ∑ b : Bool, (1 / 2 : ℝ) * (1 / 2) * interaction (cond a U Y) (cond b U Y) = _
  simp only [Fintype.sum_bool, cond_true, cond_false]
  rw [interaction_comm Y U, interaction_self, interaction_self]
  ring

theorem meanEntropy_pair_quotient [AddCommGroup V] [Module (ZMod 2) V] (U Y : PMF V)
    (G : Submodule (ZMod 2) V) :
    ((pair U Y).quotient G).meanEntropy =
      (entropyBits (U.map fun v => G.mkQ v) + entropyBits (Y.map fun v => G.mkQ v)) / 2 := by
  show ∑ b : Bool, (1 / 2 : ℝ) * entropyBits ((cond b U Y).map fun v => G.mkQ v) = _
  rw [Fintype.sum_bool]
  show (1 / 2 : ℝ) * entropyBits (U.map fun v => G.mkQ v) +
    1 / 2 * entropyBits (Y.map fun v => G.mkQ v) = _
  ring

theorem meanInteraction_pair_quotient [AddCommGroup V] [Module (ZMod 2) V] (U Y : PMF V)
    (G : Submodule (ZMod 2) V) :
    ((pair U Y).quotient G).meanInteraction =
      (entropyDefect (U.map fun v => G.mkQ v) + entropyDefect (Y.map fun v => G.mkQ v)) / 4 +
        interaction (U.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v) / 2 := by
  show ∑ a : Bool, ∑ b : Bool, (1 / 2 : ℝ) * (1 / 2) *
      interaction ((cond a U Y).map fun v => G.mkQ v) ((cond b U Y).map fun v => G.mkQ v) = _
  simp only [Fintype.sum_bool, cond_true, cond_false]
  rw [interaction_comm (Y.map fun v => G.mkQ v) (U.map fun v => G.mkQ v), interaction_self,
    interaction_self]
  ring

end WeightedFamily

/-- **Corollary 9.2 from Theorem 8.2** (two-input almost-additivity, (45)–(46) and the
mixed-input bounds), with Theorem 8.2 as the explicit hypothesis `hrig`. -/
theorem two_input_almost_additivity_of_rigidity {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hrig : WeightedFamilyRigidity.{u})
    (α : ℝ) (hα : 0 < α ∧ α < 1) (U Y : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤
        (2 : ℝ) ^ (320 / α) * ((entropyBits U + entropyBits Y) / 2) ∧
      (1 - α) * (entropyBits (U.map fun v => G.mkQ v) + entropyBits (Y.map fun v => G.mkQ v)) ≤
        entropyBits (conv (U.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v)) ∧
      interaction (U.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v) ≤
        α * (entropyBits U + entropyBits Y) ∧
      entropyBits (U.map fun v => G.mkQ v) ≤ entropyBits (conv U Y) - entropyBits Y +
        α * (entropyBits (U.map fun v => G.mkQ v) + entropyBits (Y.map fun v => G.mkQ v)) ∧
      entropyBits (Y.map fun v => G.mkQ v) ≤ entropyBits (conv U Y) - entropyBits U +
        α * (entropyBits (U.map fun v => G.mkQ v) + entropyBits (Y.map fun v => G.mkQ v)) := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 320 / α := ⟨_, rfl⟩
  rw [← hKdef]
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  have hK : 0 < K := by
    rw [hKdef]
    exact div_pos (by norm_num) hα.1
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
  have hratio : 320 / Real.logb 2 (1 / lam) = α := by
    rw [hlog, hKdef]
    first
    | (field_simp; done)
    | (field_simp; ring)
  obtain ⟨G, hdim, hsp⟩ :=
    WeightedFamily.variational_sparsification_proof lam hlam_pos (WeightedFamily.pair U Y)
  rw [WeightedFamily.meanEntropy_pair] at hdim
  haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (V ⧸ G) := Fintype.ofFinite _
  -- `s(q_G U, q_G Y) ≤ α (H(q_G U) + H(q_G Y))`
  have hs : interaction (U.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v) ≤
      α * (entropyBits (U.map fun v => G.mkQ v) + entropyBits (Y.map fun v => G.mkQ v)) := by
    have hU0 := entropyBits_nonneg' (U.map fun v => G.mkQ v)
    have hY0 := entropyBits_nonneg' (Y.map fun v => G.mkQ v)
    rcases (add_nonneg hU0 hY0).lt_or_eq with hpos | hzero
    · have hposQ : 0 < ((WeightedFamily.pair U Y).quotient G).meanEntropy := by
        rw [WeightedFamily.meanEntropy_pair_quotient]
        linarith
      have hF := hrig (V ⧸ G) lam ⟨hlam_pos, hlam_lt⟩ ((WeightedFamily.pair U Y).quotient G)
        hsp hposQ
      rw [hratio] at hF
      have hE := hF.trans (min_le_right _ _)
      rw [div_le_iff₀ hposQ, WeightedFamily.meanInteraction_pair_quotient,
        WeightedFamily.meanEntropy_pair_quotient] at hE
      have hEU := interaction_nonneg (U.map fun v => G.mkQ v) (U.map fun v => G.mkQ v)
      have hEY := interaction_nonneg (Y.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v)
      rw [interaction_self] at hEU hEY
      linarith
    · have hc := interaction_le_left (U.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v)
      have hU : entropyBits (U.map fun v => G.mkQ v) = 0 := by linarith
      rw [← hzero, mul_zero]
      linarith
  -- data processing: `H(q_G U + q_G Y) − H(q_G Y) ≤ H(U + Y) − H(Y)` and its mirror
  have hdpY : entropyBits Y - entropyBits (Y.map fun v => G.mkQ v) ≤
      entropyBits (conv Y U) - entropyBits ((conv Y U).map fun v => G.mkQ v) :=
    entropyBits_sub_map_le_conv G.mkQ.toAddMonoidHom Y U
  have hdpU : entropyBits U - entropyBits (U.map fun v => G.mkQ v) ≤
      entropyBits (conv U Y) - entropyBits ((conv U Y).map fun v => G.mkQ v) :=
    entropyBits_sub_map_le_conv G.mkQ.toAddMonoidHom U Y
  have e1 : (conv Y U).map (fun v => G.mkQ v) =
      conv (U.map fun v => G.mkQ v) (Y.map fun v => G.mkQ v) := by
    rw [conv_map_mkQ G Y U, conv_comm_law]
  rw [e1, conv_comm_law Y U] at hdpY
  rw [conv_map_mkQ G U Y] at hdpU
  have hqU := entropyBits_map_le U (fun v => G.mkQ v)
  have hqY := entropyBits_map_le Y (fun v => G.mkQ v)
  have hmono := mul_le_mul_of_nonneg_left (add_le_add hqU hqY) hα.1.le
  unfold interaction at hs
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · calc (Module.finrank (ZMod 2) G : ℝ) ≤ (entropyBits U + entropyBits Y) / 2 / lam := hdim
      _ = (2 : ℝ) ^ K * ((entropyBits U + entropyBits Y) / 2) := by
        rw [div_eq_mul_inv, hinv]
        ring
  · linarith
  · unfold interaction
    linarith
  · linarith
  · linarith

end EntropyLean
