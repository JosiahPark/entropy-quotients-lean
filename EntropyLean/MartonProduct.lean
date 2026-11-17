import Mathlib
import EntropyLean.Interaction
import EntropyLean.DoubleTrial
import EntropyLean.MartonTransport

/-!
# The entropic Marton bound (35) for product laws (roadmap items I4, I5)

For laws `K₁` on `V₁` and `K₂` on `V₂`, `K₁ ⊗ K₂ = prodLaw K₁ K₂` is the law of an independent
pair. This file proves
* `conv_prodLaw`: `(K₁ ⊗ K₂) * (L₁ ⊗ L₂) = (K₁ * L₁) ⊗ (K₂ * L₂)`;
* `entropyIncrement_prodLaw : D(K₁ ⊗ K₂) = D(K₁) + D(K₂)` and
  `ruzsaDist_prodLaw : d(K₁ ⊗ K₂, L₁ ⊗ L₂) = d(K₁, L₁) + d(K₂, L₂)` (from `entropyBits_prodLaw`);
* `subCard_prod : |W₁ × W₂| = |W₁| |W₂|` and `uniformSub_prod : U_{W₁ × W₂} = U_{W₁} ⊗ U_{W₂}`;
* `marton_prodLaw`: if `d(K₁, U_{W₁}) ≤ 6 D(K₁)` and `d(K₂, U_{W₂}) ≤ 6 D(K₂)`, then
  `d(K₁ ⊗ K₂, U_{W₁ × W₂}) ≤ 6 D(K₁ ⊗ K₂)`, with the existential form `marton_prodLaw_of_exists`
  and `MartonInput.marton_prodLaw` ((35) on `V₁` and on `V₂` gives (35) for every product law
  on `V₁ × V₂`);
* `finConsEquiv : F₂ × F₂ⁿ ≃ₗ F₂ⁿ⁺¹`, `piLaw n P` (the law of `n` independent bits with laws
  `P i`), `IndepCoords` (a law on `Fin n → ZMod 2` is `piLaw n P` for some `P`),
  `marton_map_linearEquiv` ((35) for one law transfers along a linear equivalence) and
  `marton_of_indep_coords`: (35) for every law on `Fin n → ZMod 2` with independent coordinates
  (roadmap item I5, by induction on `n` from `martonInput_zmod2` and `marton_prodLaw`);
* `finConsEquiv_apply` and `piLaw_apply : piLaw n P v = ∏ i, P i (v i)` (roadmap item J1), so
  `piLaw n P` is the law of independent coordinates with laws `P i` in the usual sense.

What this file does NOT prove: the entropic Marton bound (35) itself, nor (35) for laws on
`V₁ × V₂` that are not products (so `MartonInput (V₁ × V₂)` is NOT derived from `MartonInput V₁`
and `MartonInput V₂`); nor (35) for laws on `Fin n → ZMod 2` with dependent coordinates.
-/

namespace EntropyLean

/-- The sum of two independent pairs: `(K₁ ⊗ K₂) * (L₁ ⊗ L₂) = (K₁ * L₁) ⊗ (K₂ * L₂)`. -/
theorem conv_prodLaw {α β : Type*} [Add α] [Add β] (K₁ L₁ : PMF α) (K₂ L₂ : PMF β) :
    conv (prodLaw K₁ K₂) (prodLaw L₁ L₂) = prodLaw (conv K₁ L₁) (conv K₂ L₂) := by
  first
    | (simp only [conv, prodLaw, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind,
        Function.comp_apply, Prod.mk_add_mk]
       refine congrArg (PMF.bind K₁) (funext fun a₁ => ?_)
       exact PMF.bind_comm K₂ L₁ _)
    | (simp only [conv, prodLaw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_apply,
        Prod.mk_add_mk]
       refine congrArg (PMF.bind K₁) (funext fun a₁ => ?_)
       exact PMF.bind_comm K₂ L₁ _)
    | (simp only [conv, prodLaw, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind,
        Function.comp_apply, Prod.mk_add_mk]
       congr 1
       funext a₁
       rw [PMF.bind_comm K₂ L₁])

/-- The entropy increment is additive on independent pairs: `D(K₁ ⊗ K₂) = D(K₁) + D(K₂)`. -/
theorem entropyIncrement_prodLaw {α β : Type*} [Fintype α] [Fintype β] [Add α] [Add β]
    (K₁ : PMF α) (K₂ : PMF β) :
    entropyIncrement (prodLaw K₁ K₂) = entropyIncrement K₁ + entropyIncrement K₂ := by
  unfold entropyIncrement
  rw [conv_prodLaw]
  simp only [entropyBits_prodLaw]
  ring

/-- The Ruzsa distance is additive on independent pairs:
`d(K₁ ⊗ K₂, L₁ ⊗ L₂) = d(K₁, L₁) + d(K₂, L₂)`. -/
theorem ruzsaDist_prodLaw {α β : Type*} [Fintype α] [Fintype β] [Add α] [Add β]
    (K₁ L₁ : PMF α) (K₂ L₂ : PMF β) :
    ruzsaDist (prodLaw K₁ K₂) (prodLaw L₁ L₂) = ruzsaDist K₁ L₁ + ruzsaDist K₂ L₂ := by
  unfold ruzsaDist
  rw [conv_prodLaw]
  simp only [entropyBits_prodLaw]
  ring

section Product

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁] [Fintype V₁]
  [AddCommGroup V₂] [Module (ZMod 2) V₂] [Fintype V₂]

/-- `|W₁ × W₂| = |W₁| |W₂|`. -/
theorem subCard_prod (W₁ : Submodule (ZMod 2) V₁) (W₂ : Submodule (ZMod 2) V₂) :
    subCard (W₁.prod W₂) = subCard W₁ * subCard W₂ := by
  classical
  unfold subCard
  rw [← Finset.card_product]
  refine congrArg Finset.card ?_
  ext x
  simp [Submodule.mem_prod]

/-- The uniform law on `W₁ × W₂` is the product of the uniform laws:
`U_{W₁ × W₂} = U_{W₁} ⊗ U_{W₂}`. -/
theorem uniformSub_prod (W₁ : Submodule (ZMod 2) V₁) (W₂ : Submodule (ZMod 2) V₂) :
    uniformSub (W₁.prod W₂) = prodLaw (uniformSub W₁) (uniformSub W₂) := by
  classical
  apply pmf_ext_toReal
  rintro ⟨v₁, v₂⟩
  rw [prodLaw_apply, ENNReal.toReal_mul, uniformSub_toReal, uniformSub_toReal, uniformSub_toReal,
    subCard_prod]
  have hmem : (v₁, v₂) ∈ W₁.prod W₂ ↔ v₁ ∈ W₁ ∧ v₂ ∈ W₂ := Submodule.mem_prod
  by_cases h₁ : v₁ ∈ W₁ <;> by_cases h₂ : v₂ ∈ W₂
  · rw [if_pos (hmem.mpr ⟨h₁, h₂⟩), if_pos h₁, if_pos h₂, Nat.cast_mul, mul_inv]
  · rw [if_neg (fun h => h₂ (hmem.mp h).2), if_neg h₂, mul_zero]
  · rw [if_neg (fun h => h₁ (hmem.mp h).1), if_neg h₁, zero_mul]
  · rw [if_neg (fun h => h₁ (hmem.mp h).1), if_neg h₁, zero_mul]

/-- **I4.** (35) for `K₁` with witness `W₁` and for `K₂` with witness `W₂` gives (35) for
`K₁ ⊗ K₂` with witness `W₁ × W₂`. -/
theorem marton_prodLaw (K₁ : PMF V₁) (K₂ : PMF V₂) {W₁ : Submodule (ZMod 2) V₁}
    {W₂ : Submodule (ZMod 2) V₂} (h₁ : ruzsaDist K₁ (uniformSub W₁) ≤ 6 * entropyIncrement K₁)
    (h₂ : ruzsaDist K₂ (uniformSub W₂) ≤ 6 * entropyIncrement K₂) :
    ruzsaDist (prodLaw K₁ K₂) (uniformSub (W₁.prod W₂)) ≤
      6 * entropyIncrement (prodLaw K₁ K₂) := by
  rw [uniformSub_prod, ruzsaDist_prodLaw, entropyIncrement_prodLaw]
  linarith

/-- **I4**, existential form: if (35) holds for `K₁` and for `K₂`, it holds for `K₁ ⊗ K₂`. -/
theorem marton_prodLaw_of_exists (K₁ : PMF V₁) (K₂ : PMF V₂)
    (h₁ : ∃ W₁ : Submodule (ZMod 2) V₁, ruzsaDist K₁ (uniformSub W₁) ≤ 6 * entropyIncrement K₁)
    (h₂ : ∃ W₂ : Submodule (ZMod 2) V₂, ruzsaDist K₂ (uniformSub W₂) ≤ 6 * entropyIncrement K₂) :
    ∃ W : Submodule (ZMod 2) (V₁ × V₂),
      ruzsaDist (prodLaw K₁ K₂) (uniformSub W) ≤ 6 * entropyIncrement (prodLaw K₁ K₂) := by
  obtain ⟨W₁, hW₁⟩ := h₁
  obtain ⟨W₂, hW₂⟩ := h₂
  exact ⟨W₁.prod W₂, marton_prodLaw K₁ K₂ hW₁ hW₂⟩

/-- (35) on `V₁` and on `V₂` gives (35) for every product law on `V₁ × V₂`. -/
theorem MartonInput.marton_prodLaw (hM₁ : MartonInput V₁) (hM₂ : MartonInput V₂)
    (K₁ : PMF V₁) (K₂ : PMF V₂) :
    ∃ W : Submodule (ZMod 2) (V₁ × V₂),
      ruzsaDist (prodLaw K₁ K₂) (uniformSub W) ≤ 6 * entropyIncrement (prodLaw K₁ K₂) :=
  marton_prodLaw_of_exists K₁ K₂ (hM₁.marton K₁) (hM₂.marton K₂)

end Product

/-! ## Independent bits (roadmap item I5) -/

/-- `(a, w) ↦ Fin.cons a w`, the linear equivalence `F₂ × F₂ⁿ ≃ F₂ⁿ⁺¹`. -/
def finConsEquiv (n : ℕ) : (ZMod 2 × (Fin n → ZMod 2)) ≃ₗ[ZMod 2] (Fin (n + 1) → ZMod 2) where
  toFun x := (Fin.cons x.1 x.2 : Fin (n + 1) → ZMod 2)
  invFun v := (v 0, Fin.tail v)
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv x := by simp
  right_inv v := by simp

/-- The law of `n` independent bits with laws `P 0, …, P (n − 1)`, as a law on `Fin n → ZMod 2`
(the iterated product `P 0 ⊗ (P 1 ⊗ ⋯)`, read through `finConsEquiv`). -/
noncomputable def piLaw : (n : ℕ) → (Fin n → PMF (ZMod 2)) → PMF (Fin n → ZMod 2)
  | 0, _ => PMF.pure 0
  | n + 1, P => (prodLaw (P 0) (piLaw n fun i => P i.succ)).map (finConsEquiv n)

theorem piLaw_succ (n : ℕ) (P : Fin (n + 1) → PMF (ZMod 2)) :
    piLaw (n + 1) P = (prodLaw (P 0) (piLaw n fun i => P i.succ)).map (finConsEquiv n) := by
  first
    | rfl
    | simp only [piLaw]
    | rw [piLaw]

/-- A law on `Fin n → ZMod 2` has independent coordinates if it is a product `piLaw n P` of laws
`P i` on the coordinates. -/
def IndepCoords {n : ℕ} (K : PMF (Fin n → ZMod 2)) : Prop :=
  ∃ P : Fin n → PMF (ZMod 2), K = piLaw n P

/-- (35) for one law transfers along a linear equivalence `e`, with witness `e W`. -/
theorem marton_map_linearEquiv {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [AddCommGroup V'] [Module (ZMod 2) V'] [Fintype V'] (e : V ≃ₗ[ZMod 2] V') (K : PMF V)
    {W : Submodule (ZMod 2) V} (h : ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K) :
    ruzsaDist (K.map e) (uniformSub (W.map (e : V →ₗ[ZMod 2] V'))) ≤
      6 * entropyIncrement (K.map e) := by
  rw [← uniformSub_map_linearEquiv, ruzsaDist_map_of_add_injective e (map_add e) e.injective,
    entropyIncrement_map_of_add_injective e (map_add e) e.injective]
  exact h

/-- (35) on `Fin 0 → ZMod 2`, a space of dimension `0`. -/
theorem martonInput_fin_zero : MartonInput (Fin 0 → ZMod 2) :=
  martonInput_of_finrank_eq_zero (by
    first
      | exact Module.finrank_fin_fun (ZMod 2)
      | exact Module.finrank_zero_of_subsingleton
      | simp)

/-- (35) for `piLaw n P`, by induction on `n` from `martonInput_zmod2` (H4c), `marton_prodLaw` (I4)
and `marton_map_linearEquiv`. -/
theorem marton_piLaw (n : ℕ) : ∀ P : Fin n → PMF (ZMod 2),
    ∃ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      ruzsaDist (piLaw n P) (uniformSub W) ≤ 6 * entropyIncrement (piLaw n P) := by
  induction n with
  | zero => exact fun P => martonInput_fin_zero.marton (piLaw 0 P)
  | succ n ih =>
    intro P
    obtain ⟨W₀, h₀⟩ := martonInput_zmod2.marton (P 0)
    obtain ⟨W', h'⟩ := ih fun i => P i.succ
    rw [piLaw_succ]
    exact ⟨_, marton_map_linearEquiv (finConsEquiv n) _ (marton_prodLaw _ _ h₀ h')⟩

/-- **I5.** The entropic Marton bound (35) for every law on `Fin n → ZMod 2` whose coordinates
are independent. -/
theorem marton_of_indep_coords {n : ℕ} (K : PMF (Fin n → ZMod 2)) (hK : IndepCoords K) :
    ∃ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K := by
  obtain ⟨P, rfl⟩ := hK
  exact marton_piLaw n P

/-! ## Masses of `piLaw` (roadmap item J1) -/

open scoped BigOperators

theorem finConsEquiv_apply (n : ℕ) (x : ZMod 2 × (Fin n → ZMod 2)) :
    finConsEquiv n x = (Fin.cons x.1 x.2 : Fin (n + 1) → ZMod 2) :=
  rfl

/-- **J1.** `piLaw n P` gives each point the product of its coordinate masses:
`piLaw n P v = ∏ i, P i (v i)`. -/
theorem piLaw_apply (n : ℕ) :
    ∀ (P : Fin n → PMF (ZMod 2)) (v : Fin n → ZMod 2), piLaw n P v = ∏ i, P i (v i) := by
  induction n with
  | zero =>
    intro P v
    have hv : v = 0 := Subsingleton.elim v 0
    have h0 : piLaw 0 P = PMF.pure 0 := by
      first
        | rfl
        | simp only [piLaw]
    rw [h0, hv]
    simp [PMF.pure_apply]
  | succ n ih =>
    intro P v
    have hv : finConsEquiv n (v 0, Fin.tail v) = v := by
      rw [finConsEquiv_apply]
      exact Fin.cons_self_tail v
    calc piLaw (n + 1) P v
        = ((prodLaw (P 0) (piLaw n fun i => P i.succ)).map (finConsEquiv n))
            (finConsEquiv n (v 0, Fin.tail v)) := by rw [piLaw_succ, hv]
      _ = prodLaw (P 0) (piLaw n fun i => P i.succ) (v 0, Fin.tail v) :=
          pmf_map_apply_injective _ (finConsEquiv n).injective _
      _ = P 0 (v 0) * ∏ i : Fin n, P i.succ (v i.succ) := by
          rw [prodLaw_apply, ih]
          try rfl
      _ = ∏ i, P i (v i) := (Fin.prod_univ_succ fun i => P i (v i)).symm

end EntropyLean
