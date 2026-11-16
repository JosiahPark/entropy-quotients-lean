import Mathlib
import EntropyLean.MartonConvEntropy
import EntropyLean.QuotientFacts
import EntropyLean.EntropyFacts
import EntropyLean.MutualInfoZero

/-!
# Trivial cases of the entropic Marton bound (roadmap item H2, Section 7)

For a law `K` on a finite F₂-space `V`, the uniform-smoothing formula
`d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2` (`ruzsaDist_uniformSub`) specialises at the two
trivial subspaces:
* `W = ⊥`: `q_⊥` is injective, so `d(K, U_⊥) = H(K) / 2` (`ruzsaDist_uniformSub_bot`);
* `W = ⊤`: `q_⊤ K` is a point mass, so `d(K, U_⊤) = (dim V − H(K)) / 2`
  (`ruzsaDist_uniformSub_top`).

Hence (35) holds for `K` whenever `H(K) ≤ 12 D(K)` (`marton_of_entropy_le`, witness `⊥`) or
`dim V − H(K) ≤ 12 D(K)` (`marton_of_codim_le`, witness `⊤`).

It also records the support of a convolution (roadmap item H3a): with `lawSupport K` the finset
`{v : K v ≠ 0}`, `lawSupport (P * Q) = lawSupport P + lawSupport Q` (`lawSupport_conv`), the
first step toward the zero-doubling case `D(K) = 0` of (35). Roadmap item H3c adds the second
step: `I(B ; A + B) = D(K)` for independent `A, B ∼ K` (`mutualInfo_snd_add`), so by the equality
case of subadditivity (`eq_prodLaw_of_mutualInfo_eq_zero`) `D(K) = 0` forces
`K.map (· + b) = K * K` for every `b` in the support (`map_add_eq_conv_of_increment_zero`).

What this file does NOT prove: the entropic Marton bound (35) in general (it remains the
hypothesis `MartonInput V` / `MartonBound` elsewhere), nor that a law with `D(K) = 0` is
uniform on a coset (roadmap item H3d), nor the one-bit case (H4).
-/

namespace EntropyLean

section MartonPartial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

omit [Fintype V] in
/-- `q_⊥` is injective, so `H(q_⊥ K) = H(K)`. -/
theorem entropyBits_map_mkQ_bot (K : PMF V) :
    entropyBits (K.map fun v => (⊥ : Submodule (ZMod 2) V).mkQ v) = entropyBits K := by
  apply entropyBits_map_of_injective
  intro a b h
  exact LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ (⊥ : Submodule (ZMod 2) V)) h

omit [Fintype V] in
/-- `q_⊤ K` is a point mass, so `H(q_⊤ K) = 0`. -/
theorem entropyBits_map_mkQ_top (K : PMF V) :
    entropyBits (K.map fun v => (⊤ : Submodule (ZMod 2) V).mkQ v) = 0 := by
  have hc : (fun v : V => (⊤ : Submodule (ZMod 2) V).mkQ v) = Function.const V 0 := by
    funext v
    show (⊤ : Submodule (ZMod 2) V).mkQ v = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_top
  rw [hc, PMF.map_const, entropyBits_pure]

/-- `d(K, U_⊥) = H(K) / 2`. -/
theorem ruzsaDist_uniformSub_bot (K : PMF V) :
    ruzsaDist K (uniformSub (⊥ : Submodule (ZMod 2) V)) = entropyBits K / 2 := by
  have h0 : (Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) : ℝ) = 0 := by simp
  rw [ruzsaDist_uniformSub, entropyBits_map_mkQ_bot, h0]
  ring

/-- `d(K, U_⊤) = (dim V − H(K)) / 2`. -/
theorem ruzsaDist_uniformSub_top (K : PMF V) :
    ruzsaDist K (uniformSub (⊤ : Submodule (ZMod 2) V)) =
      ((Module.finrank (ZMod 2) V : ℝ) - entropyBits K) / 2 := by
  have ht : (Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) : ℝ) =
      (Module.finrank (ZMod 2) V : ℝ) := by simp
  rw [ruzsaDist_uniformSub, entropyBits_map_mkQ_top, ht]
  ring

/-- (35) for laws of small entropy: if `H(K) ≤ 12 D(K)` then `d(K, U_⊥) ≤ 6 D(K)`. -/
theorem marton_of_entropy_le (K : PMF V) (h : entropyBits K ≤ 12 * entropyIncrement K) :
    ∃ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K :=
  ⟨⊥, by rw [ruzsaDist_uniformSub_bot]; linarith⟩

/-- (35) for laws of nearly full entropy: if `dim V − H(K) ≤ 12 D(K)` then
`d(K, U_⊤) ≤ 6 D(K)`. -/
theorem marton_of_codim_le (K : PMF V)
    (h : (Module.finrank (ZMod 2) V : ℝ) - entropyBits K ≤ 12 * entropyIncrement K) :
    ∃ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K :=
  ⟨⊤, by rw [ruzsaDist_uniformSub_top]; linarith⟩

end MartonPartial

/-- The support of a convolution: `t` is charged by `P * Q` iff `t = a + b` with `a` charged by
`P` and `b` charged by `Q`. -/
theorem mem_support_conv_iff {W : Type*} [Add W] (P Q : PMF W) (t : W) :
    t ∈ (conv P Q).support ↔ ∃ a ∈ P.support, ∃ b ∈ Q.support, a + b = t := by
  unfold conv
  simp only [PMF.mem_support_bind_iff, PMF.mem_support_map_iff]

section SupportConv

variable {V : Type*} [Fintype V]

open Classical in
/-- The support `{v : K v ≠ 0}` of a law on a finite type, as a finset. -/
noncomputable def lawSupport (K : PMF V) : Finset V :=
  Finset.univ.filter fun v => K v ≠ 0

theorem mem_lawSupport (K : PMF V) (v : V) : v ∈ lawSupport K ↔ K v ≠ 0 := by
  unfold lawSupport
  simp

theorem lawSupport_nonempty (K : PMF V) : (lawSupport K).Nonempty := by
  obtain ⟨v, hv⟩ := K.support_nonempty
  exact ⟨v, (mem_lawSupport K v).mpr ((K.mem_support_iff v).mp hv)⟩

open Pointwise in
/-- `supp (P * Q) = supp P + supp Q` (roadmap item H3a). -/
theorem lawSupport_conv [Add V] [DecidableEq V] (P Q : PMF V) :
    lawSupport (conv P Q) = lawSupport P + lawSupport Q := by
  ext t
  rw [Finset.mem_add, mem_lawSupport, ← PMF.mem_support_iff, mem_support_conv_iff]
  simp only [mem_lawSupport, PMF.mem_support_iff]

end SupportConv

/-! ## Zero doubling: translates (roadmap item H3c) -/

section ZeroDoublingTranslates

variable {V : Type*} [Fintype V] [AddCommGroup V]

/-- The mutual information of the pair `(B, A + B)` for independent `A, B ∼ K` is the entropy
increment: `I(B ; A + B) = H(K) + H(K * K) − 2H(K) = D(K)`. -/
theorem mutualInfo_snd_add (K : PMF V) :
    mutualInfo ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)) = entropyIncrement K := by
  have hfst : ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)).map Prod.fst = K := by
    rw [PMF.map_comp]
    exact prodLaw_map_snd K K
  have hsnd : ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)).map Prod.snd =
      conv K K := by
    rw [PMF.map_comp]
    exact prodLaw_map_add K K
  have hR : entropyBits ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)) =
      entropyBits K + entropyBits K := by
    rw [entropyBits_map_injective _ snd_add_injective, entropyBits_prodLaw]
  unfold mutualInfo entropyIncrement
  rw [hfst, hsnd, hR]
  ring

/-- If `D(K) = 0` and `K(b) ≠ 0`, then `K(t − b) = (K * K)(t)` for every `t` (in `ℝ`). -/
theorem toReal_sub_eq_conv_of_increment_zero (K : PMF V) (hD : entropyIncrement K = 0)
    {b : V} (hb : K b ≠ 0) (t : V) :
    (K (t - b)).toReal = (conv K K t).toReal := by
  have hfst : ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)).map Prod.fst = K := by
    rw [PMF.map_comp]
    exact prodLaw_map_snd K K
  have hsnd : ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)).map Prod.snd =
      conv K K := by
    rw [PMF.map_comp]
    exact prodLaw_map_add K K
  have hI : mutualInfo ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)) = 0 := by
    rw [mutualInfo_snd_add, hD]
  have heq := eq_prodLaw_of_mutualInfo_eq_zero _ hI
  rw [hfst, hsnd] at heq
  have e : ((b, t) : V × V) = (fun x : V × V => (x.2, x.1 + x.2)) (t - b, b) :=
    Prod.ext rfl (sub_add_cancel t b).symm
  have h1 : ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)) (b, t) =
      prodLaw K K (t - b, b) :=
    (congrArg (fun y => ((prodLaw K K).map fun x : V × V => (x.2, x.1 + x.2)) y) e).trans
      (pmf_map_apply_injective (prodLaw K K) (snd_add_injective (V := V)) (t - b, b))
  have h2 : prodLaw K K (t - b, b) = prodLaw K (conv K K) (b, t) := by
    rw [← h1, heq]
  have h3 := congrArg ENNReal.toReal h2
  rw [prodLaw_apply, prodLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_mul] at h3
  have hpos : 0 < (K b).toReal := ENNReal.toReal_pos hb (PMF.apply_ne_top K b)
  exact mul_right_cancel₀ hpos.ne' (h3.trans (mul_comm _ _))

/-- Roadmap item H3c: if `D(K) = 0`, every translate of `K` by a point `b` of its support is
`K * K`, i.e. `K.map (· + b) = K * K`. -/
theorem map_add_eq_conv_of_increment_zero (K : PMF V) (hD : entropyIncrement K = 0)
    {b : V} (hb : K b ≠ 0) : K.map (fun a => a + b) = conv K K := by
  refine PMF.ext fun t => ?_
  have e : t = (fun a : V => a + b) (t - b) := (sub_add_cancel t b).symm
  have hm : (K.map fun a => a + b) t = K (t - b) :=
    (congrArg (fun y => (K.map fun a : V => a + b) y) e).trans
      (pmf_map_apply_injective K (add_left_injective b) (t - b))
  rw [hm]
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    (toReal_sub_eq_conv_of_increment_zero K hD hb t)

end ZeroDoublingTranslates

end EntropyLean
