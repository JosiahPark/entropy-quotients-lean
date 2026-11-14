import Mathlib
import EntropyLean.Interaction
import EntropyLean.CondInformation

/-!
# Data processing for the entropy increment (roadmap item B5)

For independent `X ∼ P`, `Y ∼ Q` on a finite abelian group `V` and an additive map
`f : V →+ W` to a finite abelian group, we prove
`H(X) − H(f X) ≤ H(X + Y) − H(f (X + Y))` (`entropyBits_sub_map_le_conv`), i.e.
`H(X | f X) ≤ H(X + Y | f (X + Y))`. The proof is one application of `I(A ; B | C) ≥ 0`
(`condMutualInfo_nonneg`) to `A = X + Y`, `B = (f X, Y)`, `C = f (X + Y)`, where every joint
entropy is computed by injectivity and `H(P ⊗ Q) = H(P) + H(Q)`.

Consequences:
* `entropyIncrement_map_le : D(f X) ≤ D(X)` (take `Y` an independent copy of `X`);
* `entropyIncrement_quotient_le : D(q_G X) ≤ D(X)` for a subspace `G` of an `F₂`-space;
* `quotientLoss_le_conv : F_P(G) ≤ F_{P * Q}(G)`.

What this file does NOT prove: Lemma 2.1 (supermodularity of `F_P`), any statement about
weighted families, or any infinite-support version.
-/

namespace EntropyLean

/-- The map `(x, y) ↦ (x + y, (f x, y), f (x + y))`, giving the triple `(A, B, C)`. -/
def incTriple {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) :
    V × V → V × (W × V) × W :=
  fun x => (x.1 + x.2, (f x.1, x.2), f (x.1 + x.2))

theorem incTriple_injective {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) :
    Function.Injective (incTriple f) := by
  intro x y h
  have h' : (x.1 + x.2, (f x.1, x.2), f (x.1 + x.2)) =
      (y.1 + y.2, (f y.1, y.2), f (y.1 + y.2)) := h
  have h1 : x.1 + x.2 = y.1 + y.2 := congrArg Prod.fst h'
  have h2 : x.2 = y.2 := congrArg (fun z : V × (W × V) × W => z.2.1.2) h'
  rw [h2] at h1
  exact Prod.ext (add_right_cancel h1) h2

/-- `s ↦ (s, g s)` is injective. -/
theorem pair_self_injective {α β : Type*} (g : α → β) :
    Function.Injective (fun s : α => (s, g s)) := by
  intro s t h
  exact congrArg Prod.fst h

/-- Applying `g` to the first coordinate of `P ⊗ Q` gives `(g P) ⊗ Q`. -/
theorem prodLaw_map_left {α β γ : Type*} (P : PMF α) (Q : PMF β) (g : α → γ) :
    (prodLaw P Q).map (fun x => (g x.1, x.2)) = prodLaw (P.map g) Q := by
  unfold prodLaw
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext a
  exact (PMF.map_comp _ _ _).trans rfl

/-- `H(X) − H(f X) ≤ H(X + Y) − H(f (X + Y))` for independent `X ∼ P`, `Y ∼ Q`. -/
theorem entropyBits_sub_map_le_conv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Fintype V] [Fintype W] (f : V →+ W) (P Q : PMF V) :
    entropyBits P - entropyBits (P.map f) ≤
      entropyBits (conv P Q) - entropyBits ((conv P Q).map f) := by
  have h1 : ((prodLaw P Q).map (incTriple f)).map tripleAC =
      (conv P Q).map (fun s => (s, f s)) := by
    rw [← prodLaw_map_add, PMF.map_comp, PMF.map_comp]
    rfl
  have h2 : ((prodLaw P Q).map (incTriple f)).map Prod.snd =
      (prodLaw (P.map f) Q).map (fun z : W × V => (z, z.1 + f z.2)) := by
    rw [← prodLaw_map_left, PMF.map_comp, PMF.map_comp]
    congr 1
    funext x
    show ((f x.1, x.2), f (x.1 + x.2)) = ((f x.1, x.2), f x.1 + f x.2)
    rw [map_add]
  have h3 : ((prodLaw P Q).map (incTriple f)).map tripleC = (conv P Q).map f := by
    rw [← prodLaw_map_add, PMF.map_comp, PMF.map_comp]
    rfl
  have e1 : entropyBits ((prodLaw P Q).map (incTriple f)) = entropyBits P + entropyBits Q :=
    (entropyBits_map_of_injective _ (incTriple_injective f)).trans (entropyBits_prodLaw P Q)
  have e2 : entropyBits (((prodLaw P Q).map (incTriple f)).map tripleAC) =
      entropyBits (conv P Q) := by
    rw [h1]
    exact entropyBits_map_of_injective _ (pair_self_injective _)
  have e3 : entropyBits (((prodLaw P Q).map (incTriple f)).map Prod.snd) =
      entropyBits (P.map f) + entropyBits Q := by
    rw [h2]
    exact (entropyBits_map_of_injective _ (pair_self_injective _)).trans
      (entropyBits_prodLaw _ _)
  have e4 : entropyBits (((prodLaw P Q).map (incTriple f)).map tripleC) =
      entropyBits ((conv P Q).map f) := by
    rw [h3]
  have hc := condMutualInfo_nonneg ((prodLaw P Q).map (incTriple f))
  unfold condMutualInfo at hc
  linarith [e1, e2, e3, e4]

/-- Data processing for the increment along an additive map: `D(f X) ≤ D(X)`. -/
theorem entropyIncrement_map_le {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Fintype V] [Fintype W] (f : V →+ W) (P : PMF V) :
    entropyIncrement (P.map f) ≤ entropyIncrement P := by
  have h := entropyBits_sub_map_le_conv f P P
  rw [conv_map_hom] at h
  unfold entropyIncrement
  linarith

/-- Roadmap item B5: `D(q_G X) ≤ D(X)`. -/
theorem entropyIncrement_quotient_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (P : PMF V) (G : Submodule (ZMod 2) V) :
    entropyIncrement (P.map fun v => G.mkQ v) ≤ entropyIncrement P := by
  haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (V ⧸ G) := Fintype.ofFinite _
  exact entropyIncrement_map_le G.mkQ.toAddMonoidHom P

/-- `F_P(G) ≤ F_{P * Q}(G)`: the subspace defect does not decrease under convolution. -/
theorem quotientLoss_le_conv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (P Q : PMF V) (G : Submodule (ZMod 2) V) :
    quotientLoss P G ≤ quotientLoss (conv P Q) G := by
  haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (V ⧸ G) := Fintype.ofFinite _
  unfold quotientLoss
  exact entropyBits_sub_map_le_conv G.mkQ.toAddMonoidHom P Q

end EntropyLean
