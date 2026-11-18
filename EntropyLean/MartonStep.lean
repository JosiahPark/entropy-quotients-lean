import EntropyLean.MathlibForPFR
import EntropyLean.MartonConsequence
import EntropyLean.Fibring

/-!
# The Marton step of Lemma 7.1 for two laws (roadmap item D8a, Section 7)

For two laws `P`, `Q` on a finite F₂-space `V`, apply (36) to `K = P * Q` and let `W` be the
subspace it gives. By the fibring inequality (21), `s(P, Q) ≤ s_W(P, Q) + s(q_W P, q_W Q)`, and
`s(q_W P, q_W Q) ≤ H(q_W (P * Q)) ≤ 12 D(P * Q)`, while `dim W ≤ 13 H(P * Q) ≤ 13 (H(P) + H(Q))`.

This file proves
* `interaction_quot_le_entropyBits_conv`: `s(q_W P, q_W Q) ≤ H(q_W (P * Q))`;
* `interaction_le_subspace_add_increment`: under the Marton hypothesis `MartonInput V`, some
  subspace `W` has `s(P, Q) ≤ s_W(P, Q) + 12 D(P * Q)` and `dim W ≤ 13 (H(P) + H(Q))`.

What this file does NOT prove: the averaged statement of Lemma 7.1 (37) (roadmap items D8b, D8c),
nor the entropic Marton bound (35), which enters only as the hypothesis `hM : MartonInput V`.
-/

namespace EntropyLean

section MartonStep

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- `s(q_W P, q_W Q) ≤ H(q_W (P * Q))`: by (9) both `H(q_W P)` and `H(q_W Q)` are at most
`H(q_W P * q_W Q) = H(q_W (P * Q))`. -/
theorem interaction_quot_le_entropyBits_conv (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    interaction (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v) ≤
      entropyBits ((conv P Q).map fun v => W.mkQ v) := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  rw [conv_map_mkQ]
  have ha := entropyBits_le_conv_left (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v)
  have hb := entropyBits_le_conv_right (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v)
  unfold interaction
  linarith

/-- The Marton step of Lemma 7.1 for two laws: some subspace `W` has
`s(P, Q) ≤ s_W(P, Q) + 12 D(P * Q)` and `dim W ≤ 13 (H(P) + H(Q))`. -/
theorem interaction_le_subspace_add_increment (hM : MartonInput V) (P Q : PMF V) :
    ∃ W : Submodule (ZMod 2) V,
      interaction P Q ≤ subspaceInteraction P Q W + 12 * entropyIncrement (conv P Q) ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ 13 * (entropyBits P + entropyBits Q) := by
  obtain ⟨W, h1, _, h3⟩ := hM.consequence (conv P Q)
  refine ⟨W, ?_, ?_⟩
  · have hfib := interaction_sub_le_subspace P Q W
    have hq := interaction_quot_le_entropyBits_conv P Q W
    linarith
  · have hc := entropyBits_conv_le P Q
    linarith

end MartonStep

end EntropyLean
