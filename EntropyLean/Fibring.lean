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

Roadmap item D4b adds the bounds (19) `0 ≤ s_f(P, Q) ≤ min(H(A | f A), H(B | f B))`
(`fibreInteraction_nonneg`, `fibreInteraction_le_left`, `fibreInteraction_le_right`) and their
subspace versions `0 ≤ s_W(P, Q) ≤ min(F_P(W), F_Q(W))` (`subspaceInteraction_nonneg`,
`subspaceInteraction_le_left`, `subspaceInteraction_le_right`, `subspaceInteraction_le_min`).
The upper bounds come from `I(A + B ; A | f A, f B) ≥ 0` (resp. with `B`).

Roadmap item D4c adds the nested inequality (22) via (23): for additive maps `f : V →+ T`,
`g : T →+ T₂` and `k = g ∘ f`, `s_k(P, Q) ≤ s_f(P, Q) + H(f A) − H(k A)` (`fibreInteraction_nested`,
from `I(A + B ; f A | k A, k B) ≥ 0`), hence `s_k(P, Q) − (H(f A) − H(k A)) ≤ H(B | f B)`
(`fibreInteraction_nested_loss`); for subspaces `U ≤ W` this is
`F_Q(U) ≥ s_W(P, Q) − (H(q_U P) − H(q_W P))` (`subspaceInteraction_nested`).

What this file does NOT prove: any statement about weighted families (Lemma 5.1 onward).
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
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨h3, -⟩ := Prod.mk.inj h2
    exact Prod.ext h1 h3
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

/-- Equation (19), lower bound: `0 ≤ s_f(P, Q)`, since `(A + B, f A, f B)` is a function of
`(A, B)`. -/
theorem fibreInteraction_nonneg [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    0 ≤ fibreInteraction f P Q := by
  rw [fibreInteraction_eq]
  have h : entropyBits (fibreJoint f P Q) ≤ entropyBits (prodLaw P Q) :=
    entropyBits_map_le _ _
  rw [entropyBits_prodLaw] at h
  linarith

/-- Equation (19): `s_f(P, Q) ≤ H(A | f A)`, from `I(A + B ; A | f A, f B) ≥ 0`. -/
theorem fibreInteraction_le_left [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    fibreInteraction f P Q ≤ entropyBits P - entropyBits (P.map f) := by
  obtain ⟨R, hR⟩ : ∃ R : PMF (V × V × (T × T)),
      R = (prodLaw P Q).map (fun x : V × V => (x.1 + x.2, x.1, (f x.1, f x.2))) := ⟨_, rfl⟩
  have hI : 0 ≤ condMutualInfo R := condMutualInfo_nonneg R
  have hinj2 : Function.Injective (fun y : V × T => (y.1, (f y.1, y.2))) := by
    intro y z h
    have h' : (y.1, (f y.1, y.2)) = (z.1, (f z.1, z.2)) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨-, h3⟩ := Prod.mk.inj h2
    exact Prod.ext h1 h3
  have hinj3 : Function.Injective (fun x : V × V => (x.1 + x.2, x.1, (f x.1, f x.2))) := by
    intro x y h
    have h' : (x.1 + x.2, x.1, (f x.1, f x.2)) = (y.1 + y.2, y.1, (f y.1, f y.2)) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨h3, -⟩ := Prod.mk.inj h2
    rw [h3] at h1
    exact Prod.ext h3 (add_left_cancel h1)
  have e1 : entropyBits (R.map tripleAC) = entropyBits (fibreJoint f P Q) := by
    rw [hR, PMF.map_comp]
    try rfl
  have h2 : R.map Prod.snd =
      (prodLaw P (Q.map f)).map (fun y : V × T => (y.1, (f y.1, y.2))) := by
    rw [hR, ← prodLaw_map_right P Q (⇑f), PMF.map_comp, PMF.map_comp]
    try rfl
  have e2 : entropyBits (R.map Prod.snd) = entropyBits P + entropyBits (Q.map f) := by
    rw [h2, entropyBits_map_of_injective _ hinj2, entropyBits_prodLaw]
  have e3 : entropyBits R = entropyBits P + entropyBits Q := by
    rw [hR, entropyBits_map_of_injective _ hinj3, entropyBits_prodLaw]
  have h4 : R.map tripleC = prodLaw (P.map f) (Q.map f) := by
    rw [hR, ← prodLaw_map_both P Q (⇑f) (⇑f), PMF.map_comp]
    try rfl
  have e4 : entropyBits (R.map tripleC) = entropyBits (P.map f) + entropyBits (Q.map f) := by
    rw [h4, entropyBits_prodLaw]
  unfold condMutualInfo at hI
  rw [fibreInteraction_eq]
  linarith [e1, e2, e3, e4]

/-- Equation (19): `s_f(P, Q) ≤ H(B | f B)`, from `I(A + B ; B | f A, f B) ≥ 0`. -/
theorem fibreInteraction_le_right [Fintype V] [Fintype T] (f : V →+ T) (P Q : PMF V) :
    fibreInteraction f P Q ≤ entropyBits Q - entropyBits (Q.map f) := by
  obtain ⟨R, hR⟩ : ∃ R : PMF (V × V × (T × T)),
      R = (prodLaw P Q).map (fun x : V × V => (x.1 + x.2, x.2, (f x.1, f x.2))) := ⟨_, rfl⟩
  have hI : 0 ≤ condMutualInfo R := condMutualInfo_nonneg R
  have hinj2 : Function.Injective (fun y : T × V => (y.2, (y.1, f y.2))) := by
    intro y z h
    have h' : (y.2, (y.1, f y.2)) = (z.2, (z.1, f z.2)) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨h3, -⟩ := Prod.mk.inj h2
    exact Prod.ext h3 h1
  have hinj3 : Function.Injective (fun x : V × V => (x.1 + x.2, x.2, (f x.1, f x.2))) := by
    intro x y h
    have h' : (x.1 + x.2, x.2, (f x.1, f x.2)) = (y.1 + y.2, y.2, (f y.1, f y.2)) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨h3, -⟩ := Prod.mk.inj h2
    rw [h3] at h1
    exact Prod.ext (add_right_cancel h1) h3
  have e1 : entropyBits (R.map tripleAC) = entropyBits (fibreJoint f P Q) := by
    rw [hR, PMF.map_comp]
    try rfl
  have h2 : R.map Prod.snd =
      (prodLaw (P.map f) Q).map (fun y : T × V => (y.2, (y.1, f y.2))) := by
    rw [hR, ← prodLaw_map_left P Q (⇑f), PMF.map_comp, PMF.map_comp]
    try rfl
  have e2 : entropyBits (R.map Prod.snd) = entropyBits (P.map f) + entropyBits Q := by
    rw [h2, entropyBits_map_of_injective _ hinj2, entropyBits_prodLaw]
  have e3 : entropyBits R = entropyBits P + entropyBits Q := by
    rw [hR, entropyBits_map_of_injective _ hinj3, entropyBits_prodLaw]
  have h4 : R.map tripleC = prodLaw (P.map f) (Q.map f) := by
    rw [hR, ← prodLaw_map_both P Q (⇑f) (⇑f), PMF.map_comp]
    try rfl
  have e4 : entropyBits (R.map tripleC) = entropyBits (P.map f) + entropyBits (Q.map f) := by
    rw [h4, entropyBits_prodLaw]
  unfold condMutualInfo at hI
  rw [fibreInteraction_eq]
  linarith [e1, e2, e3, e4]

/-- Equation (23) along a factorisation `k = g ∘ f`:
`s_k(P, Q) ≤ s_f(P, Q) + (H(f A) − H(k A))`, from `I(A + B ; f A | k A, k B) ≥ 0`. -/
theorem fibreInteraction_nested {T₂ : Type*} [AddCommGroup T₂] [Fintype V] [Fintype T]
    [Fintype T₂] (f : V →+ T) (g : T →+ T₂) (k : V →+ T₂) (hk : ∀ v, g (f v) = k v)
    (P Q : PMF V) :
    fibreInteraction k P Q ≤
      fibreInteraction f P Q + (entropyBits (P.map f) - entropyBits (P.map k)) := by
  obtain ⟨R, hR⟩ : ∃ R : PMF (V × T × (T₂ × T₂)),
      R = (prodLaw P Q).map (fun x : V × V => (x.1 + x.2, f x.1, (g (f x.1), g (f x.2)))) :=
    ⟨_, rfl⟩
  have hI : 0 ≤ condMutualInfo R := condMutualInfo_nonneg R
  have e1 : entropyBits (R.map tripleAC) = entropyBits (fibreJoint k P Q) := by
    have h1 : R.map tripleAC = fibreJoint k P Q := by
      rw [hR, PMF.map_comp]
      unfold fibreJoint
      congr 1
      funext x
      show (x.1 + x.2, (g (f x.1), g (f x.2))) = (x.1 + x.2, (k x.1, k x.2))
      rw [hk, hk]
    rw [h1]
  have hinj2 : Function.Injective (fun y : T × T₂ => (y.1, (g y.1, y.2))) := by
    intro y z h
    have h' : (y.1, (g y.1, y.2)) = (z.1, (g z.1, z.2)) := h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h'
    obtain ⟨-, h3⟩ := Prod.mk.inj h2
    exact Prod.ext h1 h3
  have h2 : R.map Prod.snd =
      (prodLaw (P.map f) (Q.map k)).map (fun y : T × T₂ => (y.1, (g y.1, y.2))) := by
    rw [hR, ← prodLaw_map_both P Q (⇑f) (⇑k), PMF.map_comp, PMF.map_comp]
    congr 1
    funext x
    show (f x.1, (g (f x.1), g (f x.2))) = (f x.1, (g (f x.1), k x.2))
    rw [hk x.2]
  have e2 : entropyBits (R.map Prod.snd) = entropyBits (P.map f) + entropyBits (Q.map k) := by
    rw [h2, entropyBits_map_of_injective _ hinj2, entropyBits_prodLaw]
  have hRf : R = (fibreJoint f P Q).map
      (fun y : V × (T × T) => (y.1, y.2.1, (g y.2.1, g y.2.2))) := by
    rw [hR]
    unfold fibreJoint
    rw [PMF.map_comp]
    try rfl
  have hfR : fibreJoint f P Q =
      R.map (fun z : V × T × (T₂ × T₂) => (z.1, (z.2.1, f z.1 - z.2.1))) := by
    rw [hR, PMF.map_comp]
    unfold fibreJoint
    congr 1
    funext x
    simp [map_add]
  have a1 : entropyBits R ≤ entropyBits (fibreJoint f P Q) := by
    rw [hRf]
    exact entropyBits_map_le _ _
  have a2 : entropyBits (fibreJoint f P Q) ≤ entropyBits R := by
    rw [hfR]
    exact entropyBits_map_le _ _
  have h4 : R.map tripleC = prodLaw (P.map k) (Q.map k) := by
    rw [hR, ← prodLaw_map_both P Q (⇑k) (⇑k), PMF.map_comp]
    congr 1
    funext x
    show (g (f x.1), g (f x.2)) = (k x.1, k x.2)
    rw [hk, hk]
  have e4 : entropyBits (R.map tripleC) = entropyBits (P.map k) + entropyBits (Q.map k) := by
    rw [h4, entropyBits_prodLaw]
  unfold condMutualInfo at hI
  rw [fibreInteraction_eq, fibreInteraction_eq]
  linarith [e1, e2, e4, a1, a2]

/-- Nested inequality (22) along `k = g ∘ f`: `s_k(P, Q) − (H(f A) − H(k A)) ≤ H(B | f B)`. -/
theorem fibreInteraction_nested_loss {T₂ : Type*} [AddCommGroup T₂] [Fintype V] [Fintype T]
    [Fintype T₂] (f : V →+ T) (g : T →+ T₂) (k : V →+ T₂) (hk : ∀ v, g (f v) = k v)
    (P Q : PMF V) :
    fibreInteraction k P Q - (entropyBits (P.map f) - entropyBits (P.map k)) ≤
      entropyBits Q - entropyBits (Q.map f) := by
  have h1 := fibreInteraction_nested f g k hk P Q
  have h2 := fibreInteraction_le_right f P Q
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

/-- Equation (19), lower bound: `0 ≤ s_W(P, Q)`. -/
theorem subspaceInteraction_nonneg [Fintype V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    0 ≤ subspaceInteraction P Q W := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  exact fibreInteraction_nonneg W.mkQ.toAddMonoidHom P Q

/-- Equation (19): `s_W(P, Q) ≤ F_P(W)`. -/
theorem subspaceInteraction_le_left [Fintype V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    subspaceInteraction P Q W ≤ quotientLoss P W := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  exact fibreInteraction_le_left W.mkQ.toAddMonoidHom P Q

/-- Equation (19): `s_W(P, Q) ≤ F_Q(W)`. -/
theorem subspaceInteraction_le_right [Fintype V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    subspaceInteraction P Q W ≤ quotientLoss Q W := by
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  exact fibreInteraction_le_right W.mkQ.toAddMonoidHom P Q

/-- Lemma 3.1, nested inequality (22): for `U ≤ W`,
`F_Q(U) ≥ s_W(P, Q) − (H(q_U P) − H(q_W P))`. -/
theorem subspaceInteraction_nested [Fintype V] (P Q : PMF V) {U W : Submodule (ZMod 2) V}
    (hUW : U ≤ W) :
    subspaceInteraction P Q W -
      (entropyBits (P.map fun v => U.mkQ v) - entropyBits (P.map fun v => W.mkQ v)) ≤
      quotientLoss Q U := by
  haveI : Finite (V ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  letI : Fintype (V ⧸ U) := Fintype.ofFinite _
  haveI : Finite (V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective W)
  letI : Fintype (V ⧸ W) := Fintype.ofFinite _
  have h' : U ≤ LinearMap.ker W.mkQ := by
    rw [Submodule.ker_mkQ]
    exact hUW
  exact fibreInteraction_nested_loss U.mkQ.toAddMonoidHom (U.liftQ W.mkQ h').toAddMonoidHom
    W.mkQ.toAddMonoidHom (fun v => rfl) P Q

/-- Equation (19): `s_W(P, Q) ≤ min(F_P(W), F_Q(W))`. -/
theorem subspaceInteraction_le_min [Fintype V] (P Q : PMF V) (W : Submodule (ZMod 2) V) :
    subspaceInteraction P Q W ≤ min (quotientLoss P W) (quotientLoss Q W) :=
  le_min (subspaceInteraction_le_left P Q W) (subspaceInteraction_le_right P Q W)

end Subspace

end EntropyLean
