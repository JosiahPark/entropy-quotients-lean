import Mathlib
import EntropyLean.Information

/-!
# Nonnegativity of the interaction (lower half of equations (9) and (14))

For independent `A ∼ P`, `B ∼ Q` we build their joint law `prodLaw P Q` on `V × V`, show that
its marginals are `P` and `Q` and that its image under `(a, b) ↦ a + b` is `conv P Q`. Data
processing (`entropyBits_map_le`) and subadditivity (`entropyBits_subadditive`) then give
`H(P * Q) ≤ H(P) + H(Q)`, i.e. `interaction_nonneg : 0 ≤ s(P, Q)`, and averaging gives
`meanInteraction_nonneg : 0 ≤ e(𝒫)`.

What this file does NOT prove: the upper bounds `s(P, Q) ≤ min(H(P), H(Q))` of (9) and
`e(𝒫) ≤ h(𝒫)` of (14) (roadmap items B3b, B3c); those need `H(A + B) ≥ H(B)` for independent
`A`, `B` in a group.
-/

namespace EntropyLean

open scoped BigOperators

/-- Joint law of independent `A ∼ P` and `B ∼ Q`. -/
noncomputable def prodLaw {α β : Type*} (P : PMF α) (Q : PMF β) : PMF (α × β) :=
  P.bind fun a => Q.map fun b => (a, b)

/-- The first marginal of `prodLaw P Q` is `P`. -/
theorem prodLaw_map_fst {α β : Type*} (P : PMF α) (Q : PMF β) :
    (prodLaw P Q).map Prod.fst = P := by
  unfold prodLaw
  rw [PMF.map_bind]
  have h : ∀ a : α, (Q.map fun b => (a, b)).map Prod.fst = PMF.pure a := by
    intro a
    rw [PMF.map_comp]
    show Q.map (Function.const β a) = PMF.pure a
    rw [PMF.map_const]
  simp only [h]
  first
    | exact PMF.bind_pure _
    | exact PMF.bind_pure

/-- The second marginal of `prodLaw P Q` is `Q`. -/
theorem prodLaw_map_snd {α β : Type*} (P : PMF α) (Q : PMF β) :
    (prodLaw P Q).map Prod.snd = Q := by
  unfold prodLaw
  rw [PMF.map_bind]
  have h : ∀ a : α, (Q.map fun b => (a, b)).map Prod.snd = Q := by
    intro a
    rw [PMF.map_comp]
    show Q.map id = Q
    rw [PMF.map_id]
  simp only [h]
  rw [PMF.bind_const]

/-- The law of `A + B` is the image of the joint law under addition. -/
theorem prodLaw_map_add {V : Type*} [Add V] (P Q : PMF V) :
    (prodLaw P Q).map (fun x => x.1 + x.2) = conv P Q := by
  unfold prodLaw conv
  rw [PMF.map_bind]
  congr 1
  funext a
  first
    | exact (PMF.map_comp _ _ _).trans rfl
    | (simp only [PMF.map_comp, Function.comp_def]; done)

/-- `H(P * Q) ≤ H(P) + H(Q)`. -/
theorem entropyBits_conv_le {V : Type*} [Fintype V] [Add V] (P Q : PMF V) :
    entropyBits (conv P Q) ≤ entropyBits P + entropyBits Q := by
  have h1 : entropyBits (conv P Q) ≤ entropyBits (prodLaw P Q) := by
    rw [← prodLaw_map_add]
    exact entropyBits_map_le _ _
  have h2 := entropyBits_subadditive (prodLaw P Q)
  rw [prodLaw_map_fst, prodLaw_map_snd] at h2
  linarith

/-- Lower half of equation (9): `0 ≤ s(P, Q)`. -/
theorem interaction_nonneg {V : Type*} [Fintype V] [Add V] (P Q : PMF V) :
    0 ≤ interaction P Q := by
  have h := entropyBits_conv_le P Q
  unfold interaction
  linarith

/-- Lower half of equation (14): `0 ≤ e(𝒫)`. -/
theorem WeightedFamily.meanInteraction_nonneg {V : Type*} [Fintype V] [Add V]
    (P : WeightedFamily V) : 0 ≤ P.meanInteraction := by
  unfold WeightedFamily.meanInteraction
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  exact mul_nonneg (mul_nonneg (P.weights_pos i).le (P.weights_pos j).le)
    (interaction_nonneg _ _)

end EntropyLean
