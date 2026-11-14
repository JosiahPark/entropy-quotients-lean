import Mathlib
import EntropyLean.Information

/-!
# Nonnegativity of the interaction (lower half of equations (9) and (14))

For independent `A ∼ P`, `B ∼ Q` we build their joint law `prodLaw P Q` on `V × V`, show that
its marginals are `P` and `Q` and that its image under `(a, b) ↦ a + b` is `conv P Q`. Data
processing (`entropyBits_map_le`) and subadditivity (`entropyBits_subadditive`) then give
`H(P * Q) ≤ H(P) + H(Q)`, i.e. `interaction_nonneg : 0 ≤ s(P, Q)`, and averaging gives
`meanInteraction_nonneg : 0 ≤ e(𝒫)`.

Roadmap item B3b adds the upper bounds of (9): `H(P ⊗ Q) = H(P) + H(Q)` (`entropyBits_prodLaw`),
hence `H(A + B) ≥ H(B)` and `H(A + B) ≥ H(A)` for independent `A`, `B` in a finite group
(`entropyBits_le_conv_right`, `entropyBits_le_conv_left`), and `interaction_le_left`,
`interaction_le_right`. Roadmap item B3c averages these: `meanInteraction_le : e(𝒫) ≤ h(𝒫)`, the
upper half of (14).

What this file does NOT prove: equation (15), or anything about quotients.
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
  exact PMF.bind_pure _

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
  exact (PMF.map_comp _ _ _).trans rfl

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

/-! ## Upper bounds `s(P, Q) ≤ min(H(P), H(Q))` (roadmap item B3b) -/

/-- Masses of the product law: `(P ⊗ Q)(a, b) = P(a) Q(b)`. -/
theorem prodLaw_apply {α β : Type*} [Fintype α] [Fintype β] (P : PMF α) (Q : PMF β)
    (a : α) (b : β) : prodLaw P Q (a, b) = P a * Q b := by
  classical
  unfold prodLaw
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Ne.symm hb']
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro a' _ ha'
    rw [PMF.map_apply, tsum_fintype]
    simp [Ne.symm ha']
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Entropy is additive on independent pairs: `H(P ⊗ Q) = H(P) + H(Q)`. -/
theorem entropyBits_prodLaw {α β : Type*} [Fintype α] [Fintype β] (P : PMF α) (Q : PMF β) :
    entropyBits (prodLaw P Q) = entropyBits P + entropyBits Q := by
  have hpt : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      -(x * y) * Real.logb 2 (x * y) =
        y * (-x * Real.logb 2 x) + x * (-y * Real.logb 2 y) := by
    intro x y hx hy
    rcases hx.eq_or_lt with h | h
    · rw [← h]
      ring
    rcases hy.eq_or_lt with h' | h'
    · rw [← h']
      ring
    rw [Real.logb_mul h.ne' h'.ne']
    ring
  have e : ∀ (a : α) (b : β),
      -((prodLaw P Q) (a, b)).toReal * Real.logb 2 ((prodLaw P Q) (a, b)).toReal =
        (Q b).toReal * (-(P a).toReal * Real.logb 2 (P a).toReal) +
          (P a).toReal * (-(Q b).toReal * Real.logb 2 (Q b).toReal) := by
    intro a b
    rw [prodLaw_apply, ENNReal.toReal_mul]
    exact hpt _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hP1 := pmf_sum_toReal P
  have hQ1 := pmf_sum_toReal Q
  rw [entropyBits_eq_sum (prodLaw P Q), entropyBits_eq_sum P, entropyBits_eq_sum Q,
    Fintype.sum_prod_type]
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hP1, hQ1, one_mul]

/-- `(a, b) ↦ (a, a + b)` is injective in a group. -/
theorem fst_add_injective {V : Type*} [AddGroup V] :
    Function.Injective (fun x : V × V => (x.1, x.1 + x.2)) := by
  intro x y h
  have h' : (x.1, x.1 + x.2) = (y.1, y.1 + y.2) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  rw [h1] at h2
  exact Prod.ext h1 (add_left_cancel h2)

/-- `(a, b) ↦ (b, a + b)` is injective in a group. -/
theorem snd_add_injective {V : Type*} [AddGroup V] :
    Function.Injective (fun x : V × V => (x.2, x.1 + x.2)) := by
  intro x y h
  have h1 : x.2 = y.2 := congrArg Prod.fst h
  have h2 : x.1 + x.2 = y.1 + y.2 := congrArg Prod.snd h
  rw [h1] at h2
  exact Prod.ext (add_right_cancel h2) h1

/-- `H(B) ≤ H(A + B)` for independent `A ∼ P`, `B ∼ Q` in a finite group:
`H(A) + H(B) = H(A, A + B) ≤ H(A) + H(A + B)`. -/
theorem entropyBits_le_conv_right {V : Type*} [Fintype V] [AddGroup V] (P Q : PMF V) :
    entropyBits Q ≤ entropyBits (conv P Q) := by
  have hfst : ((prodLaw P Q).map (fun x : V × V => (x.1, x.1 + x.2))).map Prod.fst = P := by
    rw [PMF.map_comp]
    exact prodLaw_map_fst P Q
  have hsnd : ((prodLaw P Q).map (fun x : V × V => (x.1, x.1 + x.2))).map Prod.snd =
      conv P Q := by
    rw [PMF.map_comp]
    exact prodLaw_map_add P Q
  have hR : entropyBits ((prodLaw P Q).map (fun x : V × V => (x.1, x.1 + x.2))) =
      entropyBits P + entropyBits Q := by
    rw [entropyBits_map_injective _ fst_add_injective, entropyBits_prodLaw]
  have hsub := entropyBits_subadditive ((prodLaw P Q).map (fun x : V × V => (x.1, x.1 + x.2)))
  rw [hfst, hsnd, hR] at hsub
  linarith

/-- `H(A) ≤ H(A + B)` for independent `A ∼ P`, `B ∼ Q` in a finite group:
`H(A) + H(B) = H(B, A + B) ≤ H(B) + H(A + B)`. -/
theorem entropyBits_le_conv_left {V : Type*} [Fintype V] [AddGroup V] (P Q : PMF V) :
    entropyBits P ≤ entropyBits (conv P Q) := by
  have hfst : ((prodLaw P Q).map (fun x : V × V => (x.2, x.1 + x.2))).map Prod.fst = Q := by
    rw [PMF.map_comp]
    exact prodLaw_map_snd P Q
  have hsnd : ((prodLaw P Q).map (fun x : V × V => (x.2, x.1 + x.2))).map Prod.snd =
      conv P Q := by
    rw [PMF.map_comp]
    exact prodLaw_map_add P Q
  have hR : entropyBits ((prodLaw P Q).map (fun x : V × V => (x.2, x.1 + x.2))) =
      entropyBits P + entropyBits Q := by
    rw [entropyBits_map_injective _ snd_add_injective, entropyBits_prodLaw]
  have hsub := entropyBits_subadditive ((prodLaw P Q).map (fun x : V × V => (x.2, x.1 + x.2)))
  rw [hfst, hsnd, hR] at hsub
  linarith

/-- Upper half of equation (9), first bound: `s(P, Q) ≤ H(P)`. -/
theorem interaction_le_left {V : Type*} [Fintype V] [AddGroup V] (P Q : PMF V) :
    interaction P Q ≤ entropyBits P := by
  have h := entropyBits_le_conv_right P Q
  unfold interaction
  linarith

/-- Upper half of equation (9), second bound: `s(P, Q) ≤ H(Q)`. -/
theorem interaction_le_right {V : Type*} [Fintype V] [AddGroup V] (P Q : PMF V) :
    interaction P Q ≤ entropyBits Q := by
  have h := entropyBits_le_conv_left P Q
  unfold interaction
  linarith

/-! ## Averaged upper bound `e(𝒫) ≤ h(𝒫)` (roadmap item B3c) -/

/-- Upper half of equation (14): `e(𝒫) ≤ h(𝒫)`, by averaging `s(P_i, P_j) ≤ H(P_i)`. -/
theorem WeightedFamily.meanInteraction_le {V : Type*} [Fintype V] [AddGroup V]
    (P : WeightedFamily V) : P.meanInteraction ≤ P.meanEntropy := by
  have hrow : ∀ i, ∑ j, P.weights i * P.weights j * interaction (P.laws i) (P.laws j) ≤
      P.weights i * entropyBits (P.laws i) := by
    intro i
    calc ∑ j, P.weights i * P.weights j * interaction (P.laws i) (P.laws j)
        ≤ ∑ j, P.weights i * P.weights j * entropyBits (P.laws i) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (interaction_le_left _ _)
            (mul_nonneg (P.weights_pos i).le (P.weights_pos j).le)
      _ = P.weights i * entropyBits (P.laws i) * ∑ j, P.weights j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = P.weights i * entropyBits (P.laws i) := by
          rw [P.weights_sum, mul_one]
  unfold WeightedFamily.meanInteraction WeightedFamily.meanEntropy
  exact Finset.sum_le_sum fun i _ => hrow i

end EntropyLean
