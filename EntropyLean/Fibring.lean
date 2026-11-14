import Mathlib
import EntropyLean.Increment

/-!
# Fibring identity (roadmap item D4a, Lemma 3.1, equations (18), (20), (21))

For independent `A ∼ P`, `B ∼ Q` on a finite abelian group `V` and an additive map `f : V →+ T`
(for Lemma 3.1, `f = q_W`), we define

* the fibre joint law `fibreJoint f P Q`, the law of `(A + B, (f A, f B))`;
* the fibre interaction (18) (`fibreInteraction`)
  `s_f(P, Q) = H(A | f A) + H(B | f B) − H(A + B | f A, f B)`, where
  `H(A + B | f A, f B) = H(A + B, f A, f B) − H(f A, f B)` and `(f A, f B) ∼ (f P) ⊗ (f Q)`;
* the mutual information `I(A + B ; (f A, f B) | f (A + B))` (`fibreMutualInfo`).

We prove the fibring identity (20)
`s(P, Q) = s(f P, f Q) + s_f(P, Q) − I(A + B ; f A, f B | f (A + B))` (`interaction_fibring`)
and its consequence (21) `s_f(P, Q) ≥ s(P, Q) − s(f P, f Q)` (`interaction_sub_le_fibre`), plus
the subspace versions `interaction_fibring_quot`, `interaction_sub_le_subspace` for
`s_W = subspaceInteraction P Q W`.

What this file does NOT prove: the bounds (19) `0 ≤ s_W(P, Q) ≤ min(F_P(W), F_Q(W))`, the nested
inequality (22), or any statement about weighted families (later items D4b, D4c).
-/

namespace EntropyLean

/-- Applying `g` to the second coordinate of `P ⊗ Q` gives `P ⊗ (g Q)`. -/
theorem prodLaw_map_right {α β γ : Type*} (P : PMF α) (Q : PMF β) (g : β → γ) :
    (prodLaw P Q).map (fun x => (x.1, g x.2)) = prodLaw P (Q.map g) := by
  unfold prodLaw
  rw [PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp, PMF.map_comp]
  try rfl

/-- Applying `g` and `k` coordinatewise to `P ⊗ Q` gives `(g P) ⊗ (k Q)`. -/
theorem prodLaw_map_both {α β γ δ : Type*} (P : PMF α) (Q : PMF β) (g : α → γ)
    (k : β → δ) :
    (prodLaw P Q).map (fun x => (g x.1, k x.2)) = prodLaw (P.map g) (Q.map k) := by
  rw [← prodLaw_map_right (P.map g) Q k, ← prodLaw_map_left P Q g, PMF.map_comp]
  try rfl

section Fibring

variable {V T : Type*} [AddCommGroup V] [AddCommGroup T]

/-- Law of `(A + B, (f A, f B))` for independent `A ∼ P`, `B ∼ Q`. -/
noncomputable def fibreJoint (f : V →+ T) (P Q : PMF V) : PMF (V × (T × T)) :=
  (prodLaw P Q).map fun x => (x.1 + x.2, (f x.1, f x.2))

/-- The fibre interaction (18):
`s_f(P, Q) = H(A | f A) + H(B | f B) − (H(A + B, f A, f B) − H(f A, f B))`. -/
noncomputable def fibreInteraction (f : V →+ T) (P Q : PMF V) : ℝ :=
  (entropyBits P - entropyBits (P.map f)) + (entropyBits Q - entropyBits (Q.map f)) -
    (entropyBits (fibreJoint f P Q) - entropyBits (prodLaw (P.map f) (Q.map f)))

/-- The map `(x, y) ↦ (x + y, (f x, f y), f (x + y))`, giving the triple `(A, B, C)`. -/
def fibreTriple (f : V →+ T) : V × V → V × (T × T) × T :=
  fun x => (x.1 + x.2, (f x.1, f x.2), f (x.1 + x.2))

/-- `I(A + B ; (f A, f B) | f (A + B))`. -/
noncomputable def fibreMutualInfo (f : V →+ T) (P Q : PMF V) : ℝ :=
  condMutualInfo ((prodLaw P Q).map (fibreTriple f))

theorem fibreMutualInfo_nonneg [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    0 ≤ fibreMutualInfo f P Q :=
  condMutualInfo_nonneg _

/-- `s_f(P, Q) = H(P) + H(Q) − H(A + B, f A, f B)`. -/
theorem fibreInteraction_eq [Fintype T] (f : V →+ T) (P Q : PMF V) :
    fibreInteraction f P Q = entropyBits P + entropyBits Q - entropyBits (fibreJoint f P Q) := by
  unfold fibreInteraction
  rw [entropyBits_prodLaw]
  ring

/-- `I(A + B ; (f A, f B) | f (A + B))`
`= H(A + B) + H(f A, f B) − H(A + B, f A, f B) − H(f (A + B))`. -/
theorem fibreMutualInfo_eq [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    fibreMutualInfo f P Q = entropyBits (conv P Q) + (entropyBits (P.map f) +
      entropyBits (Q.map f)) - entropyBits (fibreJoint f P Q) -
      entropyBits ((conv P Q).map f) := by
  have h1 : ((prodLaw P Q).map (fibreTriple f)).map tripleAC =
      (conv P Q).map (fun s => (s, f s)) := by
    rw [← prodLaw_map_add, PMF.map_comp, PMF.map_comp]
    try rfl
  have h2 : ((prodLaw P Q).map (fibreTriple f)).map Prod.snd =
      (prodLaw (P.map f) (Q.map f)).map (fun z : T × T => (z, z.1 + z.2)) := by
    rw [← prodLaw_map_both P Q (⇑f) (⇑f), PMF.map_comp, PMF.map_comp]
    congr 1
    funext x
    show ((f x.1, f x.2), f (x.1 + x.2)) = ((f x.1, f x.2), f x.1 + f x.2)
    rw [map_add]
  have h3 : ((prodLaw P Q).map (fibreTriple f)).map tripleC = (conv P Q).map f := by
    rw [← prodLaw_map_add, PMF.map_comp, PMF.map_comp]
    try rfl
  have h4 : (prodLaw P Q).map (fibreTriple f) =
      (fibreJoint f P Q).map (fun y : V × (T × T) => (y.1, y.2, f y.1)) := by
    unfold fibreJoint
    rw [PMF.map_comp]
    try rfl
  have hinj : Function.Injective (fun y : V × (T × T) => (y.1, y.2, f y.1)) := by
    intro y z h
    have h' : (y.1, y.2, f y.1) = (z.1, z.2, f z.1) := h
    exact Prod.ext (congrArg Prod.fst h') (congrArg (fun t : V × (T × T) × T => t.2.1) h')
  have e1 : entropyBits (((prodLaw P Q).map (fibreTriple f)).map tripleAC) =
      entropyBits (conv P Q) := by
    rw [h1]
    exact entropyBits_map_of_injective _ (pair_self_injective _)
  have e2 : entropyBits (((prodLaw P Q).map (fibreTriple f)).map Prod.snd) =
      entropyBits (P.map f) + entropyBits (Q.map f) := by
    rw [h2]
    exact (entropyBits_map_of_injective _ (pair_self_injective _)).trans
      (entropyBits_prodLaw _ _)
  have e3 : entropyBits (((prodLaw P Q).map (fibreTriple f)).map tripleC) =
      entropyBits ((conv P Q).map f) := by
    rw [h3]
  have e4 : entropyBits ((prodLaw P Q).map (fibreTriple f)) =
      entropyBits (fibreJoint f P Q) := by
    rw [h4]
    exact entropyBits_map_of_injective _ hinj
  unfold fibreMutualInfo condMutualInfo
  linarith [e1, e2, e3, e4]

/-- Fibring identity (20):
`s(P, Q) = s(f P, f Q) + s_f(P, Q) − I(A + B ; f A, f B | f (A + B))`. -/
theorem interaction_fibring [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    interaction P Q = interaction (P.map f) (Q.map f) + fibreInteraction f P Q -
      fibreMutualInfo f P Q := by
  rw [fibreMutualInfo_eq, fibreInteraction_eq]
  unfold interaction
  rw [← conv_map_hom]
  ring

/-- Equation (21): `s_f(P, Q) ≥ s(P, Q) − s(f P, f Q)`. -/
theorem interaction_sub_le_fibre [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    interaction P Q - interaction (P.map f) (Q.map f) ≤ fibreInteraction f P Q := by
  have h := interaction_fibring f P Q
  have hI := fibreMutualInfo_nonneg f P Q
  linarith

end Fibring

section Subspace

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- `s_W(P, Q)` of (18) for a subspace `W`: the fibre interaction along `q_W`. -/
noncomputable def subspaceInteraction (P Q : PMF V) (W : Submodule (ZMod 2) V) : ℝ :=
  fibreInteraction W.mkQ.toAddMonoidHom P Q

/-- Lemma 3.1, equation (20), for a subspace `W`. -/
theorem interaction_fibring_quot [Fintype V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    interaction P Q = interaction (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v) +
      subspaceInteraction P Q W - fibreMutualInfo W.mkQ.toAddMonoidHom P Q := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  exact interaction_fibring W.mkQ.toAddMonoidHom P Q

/-- Lemma 3.1, equation (21): `s_W(P, Q) ≥ s(P, Q) − s(q_W P, q_W Q)`. -/
theorem interaction_sub_le_subspace [Fintype V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    interaction P Q - interaction (P.map fun v => W.mkQ v) (Q.map fun v => W.mkQ v) ≤
      subspaceInteraction P Q W := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  exact interaction_sub_le_fibre W.mkQ.toAddMonoidHom P Q

end Subspace

end EntropyLean
