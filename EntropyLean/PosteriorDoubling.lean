import EntropyLean.MathlibForPFR
import EntropyLean.FourSample
import EntropyLean.KernelBSG

/-!
# Lemma 6.3 at fixed laws: Lemma 6.2 for `(A, C)` given `S` (roadmap item D6d2)

For four laws `P₁, …, P₄` on a finite F₂-space (a fixed index tuple `T`), with `A = X₁ + X₂`,
`B = X₁ + X₃`, `S = X₁ + X₂ + X₃ + X₄` as in `EntropyLean/FourSample.lean` and `C = A + B`
(`= X₂ + X₃` over F₂), this file

* defines, for any joint law `R` of `(A, T)`, the conditional law `condKernel R t` of `A` given
  `T = t`, with `R(a, t) = R_T(t) condKernel R t a` (`condKernel_toReal_mul`);
* defines `acsLaw`, the law of `((A, C), S)`, and identifies the laws of `(A, S)`, `(C, S)`,
  `(A + C, S) = (B, S)` and `S` under it, and `H(A, C, S) = H(A, B, S)`;
* applies Lemma 6.2 conditioned on `S` (`kernel_conditional_bsg`) to get
  `∑_s R_S(s) ∑_b … d(Law(A | B = b, S = s), Law(C | B = b, S = s))
     ≤ 3 J + 2 H(C | S) − H(B | S) − H(A | S)` (`four_conditional_bsg`), where
  `J = I(A ; B | S)` (`fourJ`); the identity `I(A ; C | S) = J + H(C | S) − H(B | S)` is used.

What this file does NOT prove: `H(C | S) = s(P₂ * P₃, P₁ * P₄)`, the identification
`Law(A | B = b, S = s) = Q_{13,b} * Q_{24,s+b}` (roadmap item D6d3), the averaging over index
tuples, or Lemma 6.3 (34) itself (roadmap item D6d4).
-/

namespace EntropyLean

open scoped BigOperators

/-- Summing a joint law of `(A, T)` over `A` gives the law of `T` (in `ℝ≥0∞`). -/
theorem sum_fst_apply {α T : Type*} [Fintype α] [Fintype T] (R : PMF (α × T)) (t : T) :
    ∑ a, R (a, t) = (R.map Prod.snd) t := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' _ ht'
    simp [Ne.symm ht']
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- Conditional law of `A` given `T = t` for a joint law `R` of `(A, T)`. When `R_T(t) = 0` it is
set to the law of `A` (such `t` carry no weight). -/
noncomputable def condKernel {α T : Type*} [Fintype α] [Fintype T] (R : PMF (α × T)) (t : T) :
    PMF α :=
  if h : (R.map Prod.snd) t = 0 then R.map Prod.fst else
    PMF.ofFintype (fun a => R (a, t) / (R.map Prod.snd) t) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, sum_fst_apply R t,
        ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _)])

/-- `R_T(t) condKernel R t (a) = R(a, t)`, including when `R_T(t) = 0`. -/
theorem condKernel_toReal_mul {α T : Type*} [Fintype α] [Fintype T] (R : PMF (α × T))
    (a : α) (t : T) :
    ((R.map Prod.snd) t).toReal * (condKernel R t a).toReal = (R (a, t)).toReal := by
  by_cases h : (R.map Prod.snd) t = 0
  · have hs : (0 : ℝ) = ∑ b, (R (b, t)).toReal := by
      simp only [sum_fst_toReal, h, ENNReal.toReal_zero]
    have h0 : (R (a, t)).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => ENNReal.toReal_nonneg).mp hs.symm a
        (Finset.mem_univ a)
    rw [h0, h]
    simp
  · have hC' : ((R.map Prod.snd) t).toReal ≠ 0 :=
      (ENNReal.toReal_pos h (PMF.apply_ne_top _ _)).ne'
    have e : (condKernel R t a).toReal = (R (a, t)).toReal / ((R.map Prod.snd) t).toReal := by
      unfold condKernel
      rw [dif_neg h, PMF.ofFintype_apply, ENNReal.toReal_div]
    rw [e]
    first
    | (field_simp; done)
    | (rw [mul_comm]; exact div_mul_cancel₀ _ hC')
    | (field_simp; ring)

section PosteriorDoubling

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

omit [Fintype V] [Module (ZMod 2) V] in
/-- `(A, B, S) ↦ ((A, A + B), S)`. -/
def acsMap (x : V × V × V) : (V × V) × V := ((x.1, x.1 + x.2.1), x.2.2)

omit [Fintype V] [Module (ZMod 2) V] in
theorem acsMap_injective : Function.Injective (acsMap (V := V)) := by
  intro x y h
  have h' : ((x.1, x.1 + x.2.1), x.2.2) = ((y.1, y.1 + y.2.1), y.2.2) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨ha, hb⟩ := Prod.mk.inj h1
  rw [ha] at hb
  exact Prod.ext ha (Prod.ext (add_left_cancel hb) h2)

omit [Fintype V] [Module (ZMod 2) V] in
/-- `(A, B, S) ↦ (C, S)` with `C = A + B`. -/
def fourCS (x : V × V × V) : V × V := (x.1 + x.2.1, x.2.2)

omit [Fintype V] [Module (ZMod 2) V] in
/-- Law of `((A, C), S)`. -/
noncomputable def acsLaw (P₁ P₂ P₃ P₄ : PMF V) : PMF ((V × V) × V) :=
  (fourLaw P₁ P₂ P₃ P₄).map acsMap

omit [Fintype V] [Module (ZMod 2) V] in
theorem acs_map_A (P₁ P₂ P₃ P₄ : PMF V) :
    (acsLaw P₁ P₂ P₃ P₄).map (fun x => (x.1.1, x.2)) = (fourLaw P₁ P₂ P₃ P₄).map tripleAC := by
  unfold acsLaw
  rw [PMF.map_comp]
  try rfl

omit [Fintype V] [Module (ZMod 2) V] in
theorem acs_map_C (P₁ P₂ P₃ P₄ : PMF V) :
    (acsLaw P₁ P₂ P₃ P₄).map (fun x => (x.1.2, x.2)) = (fourLaw P₁ P₂ P₃ P₄).map fourCS := by
  unfold acsLaw
  rw [PMF.map_comp]
  try rfl

omit [Fintype V] [Module (ZMod 2) V] in
theorem acs_map_S (P₁ P₂ P₃ P₄ : PMF V) :
    (acsLaw P₁ P₂ P₃ P₄).map Prod.snd = (fourLaw P₁ P₂ P₃ P₄).map tripleC := by
  unfold acsLaw
  rw [PMF.map_comp]
  try rfl

omit [Fintype V] in
/-- Over F₂, `A + C = B`, so `(A + C, S)` has the law of `(B, S)`. -/
theorem acs_map_B (P₁ P₂ P₃ P₄ : PMF V) :
    (acsLaw P₁ P₂ P₃ P₄).map (fun x => (x.1.1 + x.1.2, x.2)) =
      (fourLaw P₁ P₂ P₃ P₄).map Prod.snd := by
  unfold acsLaw
  rw [PMF.map_comp]
  congr 1
  funext x
  show (x.1 + (x.1 + x.2.1), x.2.2) = x.2
  exact Prod.ext (zmod2_add_add_self _ _) rfl

omit [Fintype V] [Module (ZMod 2) V] in
theorem entropyBits_acsLaw (P₁ P₂ P₃ P₄ : PMF V) :
    entropyBits (acsLaw P₁ P₂ P₃ P₄) = entropyBits (fourLaw P₁ P₂ P₃ P₄) :=
  entropyBits_map_of_injective _ acsMap_injective

/-- **Lemma 6.2 for `(A, C)` given `S`, at fixed laws**:
`∑_s R_S(s) ∑_b K_{s,B}(b) d(Law(A | b, s), Law(C | b, s)) ≤ 3 J + 2 H(C | S) − H(B | S) − H(A | S)`,
with `K_s = Law((A, C) | S = s)` and `J = I(A ; B | S)`. -/
theorem four_conditional_bsg (P₁ P₂ P₃ P₄ : PMF V) :
    ∑ s, (((acsLaw P₁ P₂ P₃ P₄).map Prod.snd) s).toReal *
        ∑ z, (sumLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z).toReal *
          ruzsaDist (fibreLaw (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z)
            (fibreLawSnd (condKernel (acsLaw P₁ P₂ P₃ P₄) s) z) ≤
      3 * fourJ P₁ P₂ P₃ P₄ +
        2 * (entropyBits ((fourLaw P₁ P₂ P₃ P₄).map fourCS) -
          entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC)) -
        (entropyBits ((fourLaw P₁ P₂ P₃ P₄).map Prod.snd) -
          entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC)) -
        (entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleAC) -
          entropyBits ((fourLaw P₁ P₂ P₃ P₄).map tripleC)) := by
  have key := kernel_conditional_bsg (acsLaw P₁ P₂ P₃ P₄) ((acsLaw P₁ P₂ P₃ P₄).map Prod.snd)
    (condKernel (acsLaw P₁ P₂ P₃ P₄)) fun p t => (condKernel_toReal_mul _ p t).symm
  have eA := congrArg entropyBits (acs_map_A P₁ P₂ P₃ P₄)
  have eC := congrArg entropyBits (acs_map_C P₁ P₂ P₃ P₄)
  have eS := congrArg entropyBits (acs_map_S P₁ P₂ P₃ P₄)
  have eB := congrArg entropyBits (acs_map_B P₁ P₂ P₃ P₄)
  have eR := entropyBits_acsLaw P₁ P₂ P₃ P₄
  unfold fourJ condMutualInfo
  linarith

end PosteriorDoubling

end EntropyLean
