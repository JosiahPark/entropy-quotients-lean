import EntropyLean.MathlibForPFR
import EntropyLean.DoubleTrial

/-!
# Lemma 6.2: the conditional Balog–Szemerédi–Gowers bound (roadmap item D6b3)

For a joint law `R` of `(U, V)` on a finite F₂-space, with `Z = U + V`, conditional laws
`K_z = Law(U | Z = z)` (`fibreLaw`) and `L_z = Law(V | Z = z)` (`fibreLawSnd`), and the
conditionally independent double trial `doubleTrial R` with `W = U₁ + U₂ + Z` (`dtSum`), this file
proves:

* the law of `(U₁ + U₂, Z)` is the kernel law `c(z) (K_z * K_z)(a)`, so
  `H(U₁ + U₂, Z) = H(Z) + ∑_z R_Z(z) H(K_z * K_z)` (`entropyBits_dtSumPair`);
* `Z ∼ R_Z` under the double trial (`doubleTrial_map_Z`);
* `∑_z R_Z(z) H(K_z * K_z) ≤ H(W)` (`sum_conv_fibreLaw_le`), since `(U₁ + U₂, Z)` and `(W, Z)`
  determine each other and `H(W, Z) ≤ H(W) + H(Z)`;
* Lemma 6.2, inequality (33):
  `∑_z R_Z(z) d(K_z, L_z) ≤ 3 I(U ; V) + 2 H(Z) − H(U) − H(V)` (`conditional_bsg`).

What this file does NOT prove: the four-sample setup of Section 6, Lemma 6.1 or Lemma 6.3
(roadmap items D6c, D6d), nor anything depending on the entropic Marton bound (35).
-/

namespace EntropyLean

open scoped BigOperators

section ConditionalBSGLemma

variable {V : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V]

omit [Fintype V] [Module (ZMod 2) V] in
/-- The pair `(U₁ + U₂, Z)`. -/
def dtSumPair (x : (V × V) × V) : V × V := (x.1.1 + x.1.2, x.2)

omit [Fintype V] [Module (ZMod 2) V] in
/-- The map `(a, z) ↦ (a + z, z)`. -/
def shiftPair (p : V × V) : V × V := (p.1 + p.2, p.2)

omit [Fintype V] [Module (ZMod 2) V] in
theorem shiftPair_injective : Function.Injective (shiftPair (V := V)) := by
  intro p q h
  have h' : (p.1 + p.2, p.2) = (q.1 + q.2, q.2) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  rw [h2] at h1
  exact Prod.ext (add_right_cancel h1) h2

/-- `H(U₁ + U₂, Z) = H(Z) + ∑_z R_Z(z) H(K_z * K_z)`. -/
theorem entropyBits_dtSumPair (R : PMF (V × V)) :
    entropyBits ((doubleTrial R).map dtSumPair) =
      entropyBits (sumLaw R) +
        ∑ z, (sumLaw R z).toReal * entropyBits (conv (fibreLaw R z) (fibreLaw R z)) := by
  classical
  refine entropyBits_of_kernel ((doubleTrial R).map dtSumPair) (sumLaw R)
    (fun z => conv (fibreLaw R z) (fibreLaw R z)) fun a t => ?_
  have h : (((kernelJoint (sumLaw R) fun z => prodLaw (fibreLaw R z) (fibreLaw R z)).map
      fun x => ((fun p : V × V => p.1 + p.2) x.1, x.2)) (a, t)).toReal =
      (sumLaw R t).toReal *
        (((prodLaw (fibreLaw R t) (fibreLaw R t)).map fun p : V × V => p.1 + p.2) a).toReal :=
    kernel_masses_map
      (kernelJoint (sumLaw R) fun z => prodLaw (fibreLaw R z) (fibreLaw R z))
      (sumLaw R) (fun z => prodLaw (fibreLaw R z) (fibreLaw R z)) (fun p : V × V => p.1 + p.2)
      (kernelJoint_toReal _ _) a t
  rw [prodLaw_map_add] at h
  exact h

/-- `Z ∼ R_Z` under the double trial. -/
theorem doubleTrial_map_Z (R : PMF (V × V)) :
    (doubleTrial R).map (fun x => x.2) = sumLaw R := by
  have h := congrArg (PMF.map Prod.snd) (doubleTrial_map_fst_pair R)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

/-- `∑_z R_Z(z) H(K_z * K_z) ≤ H(W)` with `W = U₁ + U₂ + Z`. -/
theorem sum_conv_fibreLaw_le (R : PMF (V × V)) :
    ∑ z, (sumLaw R z).toReal * entropyBits (conv (fibreLaw R z) (fibreLaw R z)) ≤
      entropyBits ((doubleTrial R).map dtSum) := by
  have hk := entropyBits_dtSumPair R
  have e1 : entropyBits (((doubleTrial R).map dtSumPair).map shiftPair) =
      entropyBits ((doubleTrial R).map dtSumPair) :=
    entropyBits_map_of_injective _ shiftPair_injective
  have hs := entropyBits_subadditive (((doubleTrial R).map dtSumPair).map shiftPair)
  have eW : (((doubleTrial R).map dtSumPair).map shiftPair).map Prod.fst =
      (doubleTrial R).map dtSum := by
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext x
    show x.1.1 + x.1.2 + x.2 = x.1.1 + (x.1.2 + x.2)
    exact add_assoc _ _ _
  have eZ : (((doubleTrial R).map dtSumPair).map shiftPair).map Prod.snd = sumLaw R := by
    rw [PMF.map_comp, PMF.map_comp]
    exact doubleTrial_map_Z R
  rw [e1, eW, eZ] at hs
  linarith

/-- **Lemma 6.2**, inequality (33): for a joint law `R` of `(U, V)` on a finite F₂-space,
`∑_z R_Z(z) d(Law(U | Z = z), Law(V | Z = z)) ≤ 3 I(U ; V) + 2 H(Z) − H(U) − H(V)`. -/
theorem conditional_bsg (R : PMF (V × V)) :
    ∑ z, (sumLaw R z).toReal * ruzsaDist (fibreLaw R z) (fibreLawSnd R z) ≤
      3 * mutualInfo R + 2 * entropyBits (sumLaw R) -
        entropyBits (R.map Prod.fst) - entropyBits (R.map Prod.snd) := by
  rw [sum_ruzsaDist_fibreLaw R]
  have h1 := sum_conv_fibreLaw_le R
  have h2 := double_trial_sum_le R
  unfold mutualInfo at h2 ⊢
  linarith

end ConditionalBSGLemma

end EntropyLean
