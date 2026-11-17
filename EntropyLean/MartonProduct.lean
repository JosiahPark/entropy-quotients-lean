import Mathlib
import EntropyLean.Interaction
import EntropyLean.DoubleTrial
import EntropyLean.MartonTransport

/-!
# The entropic Marton bound (35) for product laws (roadmap item I4)

For laws `K₁` on `V₁` and `K₂` on `V₂`, `K₁ ⊗ K₂ = prodLaw K₁ K₂` is the law of an independent
pair. This file proves
* `conv_prodLaw`: `(K₁ ⊗ K₂) * (L₁ ⊗ L₂) = (K₁ * L₁) ⊗ (K₂ * L₂)`;
* `entropyIncrement_prodLaw : D(K₁ ⊗ K₂) = D(K₁) + D(K₂)` and
  `ruzsaDist_prodLaw : d(K₁ ⊗ K₂, L₁ ⊗ L₂) = d(K₁, L₁) + d(K₂, L₂)` (from `entropyBits_prodLaw`);
* `subCard_prod : |W₁ × W₂| = |W₁| |W₂|` and `uniformSub_prod : U_{W₁ × W₂} = U_{W₁} ⊗ U_{W₂}`;
* `marton_prodLaw`: if `d(K₁, U_{W₁}) ≤ 6 D(K₁)` and `d(K₂, U_{W₂}) ≤ 6 D(K₂)`, then
  `d(K₁ ⊗ K₂, U_{W₁ × W₂}) ≤ 6 D(K₁ ⊗ K₂)`, with the existential form `marton_prodLaw_of_exists`
  and `MartonInput.marton_prodLaw` ((35) on `V₁` and on `V₂` gives (35) for every product law
  on `V₁ × V₂`).

What this file does NOT prove: the entropic Marton bound (35) itself, nor (35) for laws on
`V₁ × V₂` that are not products (so `MartonInput (V₁ × V₂)` is NOT derived from `MartonInput V₁`
and `MartonInput V₂`); nor the independent-bits case (roadmap item I5).
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

end EntropyLean
