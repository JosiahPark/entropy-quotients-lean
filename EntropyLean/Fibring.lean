import Mathlib
import EntropyLean.Interaction
import EntropyLean.CondInformation

/-!
# Lemma 3.1: fibring identity (roadmap item D4a)

For independent `A ∼ P`, `B ∼ Q` and a subspace `W`, the fibre interaction (18)
`s_W(P, Q) = H(A | q_W A) + H(B | q_W B) − H(A + B | q_W A, q_W B)` (`fiberInteraction`, with
`H(A + B | q_W A, q_W B)` written as `H(A + B, q_W A, q_W B) − H(q_W A, q_W B)`), the fibring
identity (20)
`s(P, Q) = s(q_W P, q_W Q) + s_W(P, Q) − I(A + B ; q_W A, q_W B | q_W (A + B))`
(`interaction_fibring`, with the conditional mutual information `fibringDefect`), and its
consequence (21) `s_W(P, Q) ≥ s(P, Q) − s(q_W P, q_W Q)` on finite spaces
(`interaction_sub_le_fiberInteraction`).

What this file does NOT prove: the bounds (19) `0 ≤ s_W(P, Q) ≤ min(F_P(W), F_Q(W))` and the
nested inequality (22) (roadmap items D4b, D4c).
-/

namespace EntropyLean

open scoped BigOperators

section Fibring

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Joint law of `(A + B, q_W A, q_W B)` for independent `A ∼ P`, `B ∼ Q`. -/
noncomputable def sumQuotLaw (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    PMF (V × (V ⧸ W) × (V ⧸ W)) :=
  (prodLaw P Q).map fun x => (x.1 + x.2, W.mkQ x.1, W.mkQ x.2)

/-- Joint law of `(q_W A, q_W B)` for independent `A ∼ P`, `B ∼ Q`. -/
noncomputable def quotPairLaw (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    PMF ((V ⧸ W) × (V ⧸ W)) :=
  (prodLaw P Q).map fun x => (W.mkQ x.1, W.mkQ x.2)

/-- Fibre interaction (18):
`s_W(P, Q) = H(A | q_W A) + H(B | q_W B) − H(A + B | q_W A, q_W B)`. -/
noncomputable def fiberInteraction (P Q : PMF V) (W : Submodule (ZMod 2) V) : ℝ :=
  quotientLoss P W + quotientLoss Q W -
    (entropyBits (sumQuotLaw P Q W) - entropyBits (quotPairLaw P Q W))

/-- Joint law of `(A + B, (q_W A, q_W B), q_W (A + B))`. -/
noncomputable def fibringLaw (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    PMF (V × ((V ⧸ W) × (V ⧸ W)) × (V ⧸ W)) :=
  (prodLaw P Q).map fun x => (x.1 + x.2, (W.mkQ x.1, W.mkQ x.2), W.mkQ (x.1 + x.2))

/-- `I(A + B ; q_W A, q_W B | q_W (A + B))`, the correction term in (20). -/
noncomputable def fibringDefect (P Q : PMF V) (W : Submodule (ZMod 2) V) : ℝ :=
  condMutualInfo (fibringLaw P Q W)

/-- **Lemma 3.1**, equation (20):
`s(P, Q) = s(q_W P, q_W Q) + s_W(P, Q) − I(A + B ; q_W A, q_W B | q_W (A + B))`. -/
theorem interaction_fibring (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    interaction P Q =
      interaction (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v) + fiberInteraction P Q W -
        fibringDefect P Q W := by
  have hadd : (prodLaw P Q).map (fun x => x.1 + x.2) = conv P Q := prodLaw_map_add P Q
  have hinj1 : Function.Injective (fun t : V => (t, W.mkQ t)) := by
    intro a b h
    have h' : (a, W.mkQ a) = (b, W.mkQ b) := h
    exact (Prod.mk.inj h').1
  have hinj2 : Function.Injective
      (fun c : (V ⧸ W) × (V ⧸ W) => (c, c.1 + c.2)) := by
    intro a b h
    have h' : (a, a.1 + a.2) = (b, b.1 + b.2) := h
    exact (Prod.mk.inj h').1
  have hinj3 : Function.Injective
      (fun y : V × (V ⧸ W) × (V ⧸ W) => (y.1, y.2, y.2.1 + y.2.2)) := by
    intro y z h
    have h' : (y.1, y.2, y.2.1 + y.2.2) = (z.1, z.2, z.2.1 + z.2.2) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    exact Prod.ext h1 (Prod.mk.inj h2).1
  have e1 : entropyBits ((fibringLaw P Q W).map tripleAC) = entropyBits (conv P Q) := by
    have h : (fibringLaw P Q W).map tripleAC = (conv P Q).map (fun t : V => (t, W.mkQ t)) := by
      rw [← hadd]
      unfold fibringLaw
      rw [PMF.map_comp, PMF.map_comp]
      try rfl
    rw [h, entropyBits_map_of_injective _ hinj1]
  have e2 : entropyBits ((fibringLaw P Q W).map Prod.snd) = entropyBits (quotPairLaw P Q W) := by
    have h : (fibringLaw P Q W).map Prod.snd =
        (quotPairLaw P Q W).map (fun c : (V ⧸ W) × (V ⧸ W) => (c, c.1 + c.2)) := by
      unfold fibringLaw quotPairLaw
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
      funext x
      simp [map_add]
    rw [h, entropyBits_map_of_injective _ hinj2]
  have e3 : entropyBits (fibringLaw P Q W) = entropyBits (sumQuotLaw P Q W) := by
    have h : fibringLaw P Q W =
        (sumQuotLaw P Q W).map
          (fun y : V × (V ⧸ W) × (V ⧸ W) => (y.1, y.2, y.2.1 + y.2.2)) := by
      unfold fibringLaw sumQuotLaw
      rw [PMF.map_comp]
      congr 1
      funext x
      simp [map_add]
    rw [h, entropyBits_map_of_injective _ hinj3]
  have e4 : entropyBits ((fibringLaw P Q W).map tripleC) =
      entropyBits ((conv P Q).map fun v => W.mkQ v) := by
    have h : (fibringLaw P Q W).map tripleC = (conv P Q).map fun v => W.mkQ v := by
      rw [← hadd]
      unfold fibringLaw
      rw [PMF.map_comp, PMF.map_comp]
      try rfl
    rw [h]
  have hq := conv_map_mkQ W P Q
  unfold fibringDefect condMutualInfo fiberInteraction interaction quotientLoss
  rw [e1, e2, e3, e4, ← hq]
  ring

/-- Equation (21): `s(P, Q) − s(q_W P, q_W Q) ≤ s_W(P, Q)` on finite spaces. -/
theorem interaction_sub_le_fiberInteraction [Fintype V] (P Q : PMF V)
    (W : Submodule (ZMod 2) V) :
    interaction P Q - interaction (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v) ≤
      fiberInteraction P Q W := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  have h := interaction_fibring P Q W
  have hI : 0 ≤ fibringDefect P Q W := condMutualInfo_nonneg (fibringLaw P Q W)
  linarith

end Fibring

end EntropyLean
