import EntropyLean.MathlibForPFR
import EntropyLean.RuzsaDistance
import EntropyLean.Posterior

/-!
# Conditional laws given a sum (roadmap item D6b1, towards Lemma 6.2)

For a joint law `R` of a pair `(U, V)` on a finite abelian group:

* the law `R_Z` of `Z = U + V` (`sumLaw`), with masses `R_Z(z) = ∑ₐ R(a, z − a)`
  (`sumLaw_apply`, `sumLaw_toReal`);
* the conditional law `Law(U | Z = z)`, `a ↦ R(a, z − a) / R_Z(z)` (`fibreLaw`,
  `fibreLaw_toReal`, `sumLaw_mul_fibreLaw_toReal`), and `Law(V | Z = z)` as its image under
  `a ↦ z − a` (`fibreLawSnd`);
* the chain rule `H(U, V) = H(Z) + ∑_z R_Z(z) H(Law(U | Z = z))` (`fibrePair_masses`,
  `entropyBits_fibre_chain`);
* over F₂ (a `ZMod 2`-module), `z − a = a + z` (`sub_eq_add_of_zmod2`), so `Law(V | Z = z)` is a
  translate of `Law(U | Z = z)` and `d(Law(U | z), Law(V | z)) = D(Law(U | z))`
  (`ruzsaDist_fibreLaw`); averaging, the left side of (33) equals
  `∑_z R_Z(z) H(K_z * K_z) − (H(U, V) − H(Z))` with `K_z = Law(U | Z = z)`
  (`sum_ruzsaDist_fibreLaw`).

What this file does NOT prove: Lemma 6.2 itself (inequality (33)); the conditionally independent
double trial and the submodularity step are roadmap items D6b2–D6b3.
-/

namespace EntropyLean

open scoped BigOperators

/-- Law of `Z = U + V` for a joint law `R` of `(U, V)`. -/
noncomputable def sumLaw {V : Type*} [Add V] (R : PMF (V × V)) : PMF V :=
  R.map fun x => x.1 + x.2

/-- Masses of the law of `U + V`: `R_Z(z) = ∑ₐ R(a, z − a)`. -/
theorem sumLaw_apply {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V)) (z : V) :
    sumLaw R z = ∑ a, R (a, z - a) := by
  classical
  unfold sumLaw
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single (z - a)]
  · rw [if_pos (show z = a + (z - a) by abel)]
  · intro b _ hb
    have hne : ¬ z = a + b := by
      intro h
      apply hb
      rw [h]
      abel
    rw [if_neg hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Masses of the law of `U + V`, as real numbers. -/
theorem sumLaw_toReal {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V)) (z : V) :
    (sumLaw R z).toReal = ∑ a, (R (a, z - a)).toReal := by
  rw [sumLaw_apply, ENNReal.toReal_sum fun a _ => PMF.apply_ne_top _ _]

/-- Conditional law of `U` given `U + V = z`: `a ↦ R(a, z − a) / R_Z(z)`. When `R_Z(z) = 0` it
is set to the law of `U` (such `z` carry no weight). -/
noncomputable def fibreLaw {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V)) (z : V) :
    PMF V :=
  if h : sumLaw R z = 0 then R.map Prod.fst else
    PMF.ofFintype (fun a => R (a, z - a) / sumLaw R z) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← sumLaw_apply R z,
        ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _)])

/-- Conditional law of `V` given `U + V = z`, the image of `Law(U | Z = z)` under `a ↦ z − a`. -/
noncomputable def fibreLawSnd {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V))
    (z : V) : PMF V :=
  (fibreLaw R z).map fun a => z - a

/-- Masses of the conditional law, as real numbers. -/
theorem fibreLaw_toReal {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V)) {z : V}
    (h : sumLaw R z ≠ 0) (a : V) :
    (fibreLaw R z a).toReal = (R (a, z - a)).toReal / (sumLaw R z).toReal := by
  unfold fibreLaw
  rw [dif_neg h, PMF.ofFintype_apply, ENNReal.toReal_div]

/-- `R_Z(z) Law(U | Z = z)(a) = R(a, z − a)`, including when `R_Z(z) = 0`. -/
theorem sumLaw_mul_fibreLaw_toReal {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V))
    (z a : V) :
    (sumLaw R z).toReal * (fibreLaw R z a).toReal = (R (a, z - a)).toReal := by
  by_cases h : sumLaw R z = 0
  · have hs : (0 : ℝ) = ∑ b, (R (b, z - b)).toReal := by
      rw [← sumLaw_toReal, h]
      simp
    have h0 : (R (a, z - a)).toReal = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => ENNReal.toReal_nonneg).mp hs.symm a
        (Finset.mem_univ a)
    rw [h0, h]
    simp
  · have hC' : (sumLaw R z).toReal ≠ 0 := (ENNReal.toReal_pos h (PMF.apply_ne_top _ _)).ne'
    rw [fibreLaw_toReal R h]
    first
    | (field_simp; done)
    | (rw [mul_comm]; exact div_mul_cancel₀ _ hC')
    | (field_simp; ring)

/-- Masses of the joint law of `(U, Z)`: `R_{U,Z}(a, z) = R_Z(z) Law(U | Z = z)(a)`. -/
theorem fibrePair_masses {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V)) (a z : V) :
    ((R.map fun x => (x.1, x.1 + x.2)) (a, z)).toReal =
      (sumLaw R z).toReal * (fibreLaw R z a).toReal := by
  have e : (a, z) = (fun x : V × V => (x.1, x.1 + x.2)) (a, z - a) := by
    first
    | simp
    | exact Prod.ext rfl (by simp)
  have hm := pmf_map_apply_injective R (fst_add_injective (V := V)) (a, z - a)
  rw [e, hm, sumLaw_mul_fibreLaw_toReal]

/-- Chain rule along `Z = U + V`: `H(U, V) = H(Z) + ∑_z R_Z(z) H(Law(U | Z = z))`. -/
theorem entropyBits_fibre_chain {V : Type*} [Fintype V] [AddCommGroup V] (R : PMF (V × V)) :
    entropyBits R =
      entropyBits (sumLaw R) + ∑ z, (sumLaw R z).toReal * entropyBits (fibreLaw R z) := by
  have h := entropyBits_of_kernel (R.map fun x => (x.1, x.1 + x.2)) (sumLaw R) (fibreLaw R)
    (fibrePair_masses R)
  rwa [entropyBits_map_of_injective R (fst_add_injective (V := V))] at h

/-- In a `ZMod 2`-module, `z − a = a + z`. -/
theorem sub_eq_add_of_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (z a : V) :
    z - a = a + z := by
  have h2 : a + a = 0 := by
    rw [← two_smul (ZMod 2) a]
    have h20 : (2 : ZMod 2) = 0 := by
      first
      | rfl
      | decide
    rw [h20, zero_smul]
  have hn : -a = a := by
    first
    | exact neg_eq_of_add_eq_zero_right h2
    | exact neg_eq_iff_add_eq_zero.mpr h2
  rw [sub_eq_add_neg, hn, add_comm]

/-- Over F₂, `d(Law(U | Z = z), Law(V | Z = z)) = D(Law(U | Z = z))`, since
`Law(V | Z = z)` is the translate of `Law(U | Z = z)` by `z`. -/
theorem ruzsaDist_fibreLaw {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]
    (R : PMF (V × V)) (z : V) :
    ruzsaDist (fibreLaw R z) (fibreLawSnd R z) = entropyIncrement (fibreLaw R z) := by
  have e : fibreLawSnd R z = (fibreLaw R z).map fun b => b + z := by
    unfold fibreLawSnd
    congr 1
    funext a
    exact sub_eq_add_of_zmod2 z a
  rw [e, ruzsaDist_translate_self]

/-- Over F₂, the left side of (33):
`∑_z R_Z(z) d(Law(U | z), Law(V | z)) = ∑_z R_Z(z) H(K_z * K_z) − (H(U, V) − H(Z))`. -/
theorem sum_ruzsaDist_fibreLaw {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]
    (R : PMF (V × V)) :
    ∑ z, (sumLaw R z).toReal * ruzsaDist (fibreLaw R z) (fibreLawSnd R z) =
      ∑ z, (sumLaw R z).toReal * entropyBits (conv (fibreLaw R z) (fibreLaw R z)) -
        (entropyBits R - entropyBits (sumLaw R)) := by
  rw [entropyBits_fibre_chain R]
  simp only [ruzsaDist_fibreLaw, entropyIncrement, mul_sub, Finset.sum_sub_distrib]
  ring

end EntropyLean
