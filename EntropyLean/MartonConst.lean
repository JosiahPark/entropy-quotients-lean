import Mathlib
import EntropyLean.MartonConsequence

/-!
# The entropic Marton input with its constant as a parameter (roadmap item G2)

`MartonInput V` records the entropic Marton bound (35) of arXiv:2610.38525 with the constant 6:
every law `K` on `V` has a subspace `W` with `d(K, U_W) ≤ 6 D(K)`. Here the constant is a real
parameter `C`.

* `MartonInputConst C V`: (35) with constant `C` on `V`, a named hypothesis; `MartonBoundConst C`
  is the same on every finite F₂-space of a universe.
* `martonInputConst_six_iff`, `martonBoundConst_six_iff`: the case `C = 6` is `MartonInput`,
  `MartonBound`.
* `MartonInputConst.mono`, `MartonBoundConst.mono`: the hypothesis is monotone in `C`
  (since `D(K) ≥ 0`); in particular a bound with constant `C ≤ 6` gives `MartonInput`, so every
  result of this repository stated under `MartonInput` or `MartonBound` holds under it
  (`MartonInputConst.toMartonInput`, `MartonBoundConst.toMartonBound`).
* `marton_consequence_arith_const`, `MartonInputConst.consequence`: (36) in terms of `C`: some
  subspace `W` has `H(q_W K) ≤ 2C · D(K)` and `dim W ≤ H(K) + 2C · D(K) ≤ (1 + 2C) H(K)`
  (`C ≥ 0`). At `C = 6` these are the constants 12 and 13 of (36).

What this file does NOT prove: the entropic Marton bound for any constant (it is a hypothesis
here), and no version of Lemma 7.1, Lemma 8.1 or Theorem 8.2 with constants depending on `C`:
those results are proved in this repository only with the paper's constants, which come from
`C = 6`.
-/

namespace EntropyLean

universe u

/-- The entropic Marton bound (35) with constant `C` on a finite F₂-space `V`, as a named
hypothesis: every law `K` on `V` has a subspace `W` with `d(K, U_W) ≤ C · D(K)`. -/
structure MartonInputConst (C : ℝ) (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] : Prop where
  /-- Equation (35) with constant `C`. -/
  marton : ∀ K : PMF V, ∃ W : Submodule (ZMod 2) V,
    ruzsaDist K (uniformSub W) ≤ C * entropyIncrement K

/-- The entropic Marton bound (35) with constant `C` on every finite F₂-space in universe `u`. -/
def MartonBoundConst (C : ℝ) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V], MartonInputConst C V

section

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- `MartonInput V` is the case `C = 6`. -/
theorem martonInputConst_six_iff : MartonInputConst 6 V ↔ MartonInput V :=
  ⟨fun h => ⟨h.marton⟩, fun h => ⟨h.marton⟩⟩

/-- The Marton hypothesis is monotone in its constant. -/
theorem MartonInputConst.mono {C C' : ℝ} (hM : MartonInputConst C V) (hCC : C ≤ C') :
    MartonInputConst C' V := by
  refine ⟨fun K => ?_⟩
  obtain ⟨W, hW⟩ := hM.marton K
  exact ⟨W, hW.trans (mul_le_mul_of_nonneg_right hCC (entropyIncrement_nonneg K))⟩

/-- A Marton bound with constant `C ≤ 6` gives `MartonInput V`. -/
theorem MartonInputConst.toMartonInput {C : ℝ} (hM : MartonInputConst C V) (hC : C ≤ 6) :
    MartonInput V :=
  martonInputConst_six_iff.mp (hM.mono hC)

/-- The arithmetic of Section 7 with constant `C`: if `d = q + (n − h) / 2`, `|n − h| ≤ 2d` and
`d ≤ C · D`, then `q ≤ 2C · D` and `n ≤ h + 2C · D`. -/
theorem marton_consequence_arith_const {C d q h n D : ℝ} (hd : d = q + (n - h) / 2)
    (hlow1 : h - n ≤ 2 * d) (hlow2 : n - h ≤ 2 * d) (hup : d ≤ C * D) :
    q ≤ 2 * C * D ∧ n ≤ h + 2 * C * D := by
  constructor <;> linarith

/-- Equation (36) in terms of the Marton constant `C ≥ 0`: some subspace `W` has
`H(q_W K) ≤ 2C · D(K)` and `dim W ≤ H(K) + 2C · D(K) ≤ (1 + 2C) H(K)`. -/
theorem MartonInputConst.consequence {C : ℝ} (hM : MartonInputConst C V) (hC : 0 ≤ C)
    (K : PMF V) :
    ∃ W : Submodule (ZMod 2) V,
      entropyBits (K.map fun v => W.mkQ v) ≤ 2 * C * entropyIncrement K ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ entropyBits K + 2 * C * entropyIncrement K ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ (1 + 2 * C) * entropyBits K := by
  obtain ⟨W, hW⟩ := hM.marton K
  refine ⟨W, ?_⟩
  have h1 := ruzsaDist_uniformSub K W
  have h2 := ruzsaDist_uniformSub_ge K W
  have ha := le_abs_self ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K)
  have hb := neg_abs_le ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K)
  have hDH := entropyIncrement_le_entropyBits K
  obtain ⟨hq, hn⟩ := marton_consequence_arith_const h1 (by linarith) (by linarith) hW
  have h2C : 2 * C * entropyIncrement K ≤ 2 * C * entropyBits K :=
    mul_le_mul_of_nonneg_left hDH (by linarith)
  exact ⟨hq, hn, by linarith⟩

end

/-- `MartonBound` is the case `C = 6`. -/
theorem martonBoundConst_six_iff : MartonBoundConst.{u} 6 ↔ MartonBound.{u} :=
  ⟨fun h V _ _ _ => martonInputConst_six_iff.mp (h V),
    fun h V _ _ _ => martonInputConst_six_iff.mpr (h V)⟩

/-- The Marton bound on all spaces of a universe is monotone in its constant. -/
theorem MartonBoundConst.mono {C C' : ℝ} (hM : MartonBoundConst.{u} C) (hCC : C ≤ C') :
    MartonBoundConst.{u} C' :=
  fun V _ _ _ => (hM V).mono hCC

/-- A Marton bound with constant `C ≤ 6` on all spaces of a universe gives `MartonBound`. -/
theorem MartonBoundConst.toMartonBound {C : ℝ} (hM : MartonBoundConst.{u} C) (hC : C ≤ 6) :
    MartonBound.{u} :=
  martonBoundConst_six_iff.mp (hM.mono hC)

end EntropyLean
