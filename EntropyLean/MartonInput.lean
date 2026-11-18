import EntropyLean.MathlibForPFR
import EntropyLean.RuzsaDistance

/-!
# The entropic Marton input (roadmap item D7a, Section 7, equations (35)–(36))

The paper's one external input is the entropic Marton theorem of Gowers–Green–Manners–Tao
(arXiv:2311.05762, Theorem 1.2), used in the form (35): for every law `K` on a finite F₂-space
there is a subspace `W` with `d(K, U_W) ≤ 6 D(K)`, where `U_W` is uniform on `W`.

This file
* defines the uniform law `uniformSub W` on a subspace `W`;
* records (35) as the field `marton` of the structure `MartonInput V` (and `MartonBound`, the
  same for every finite F₂-space in a universe); it is a named hypothesis, never an axiom;
* proves `0 ≤ D(K) ≤ H(K)` on a finite group (`entropyIncrement_nonneg`,
  `entropyIncrement_le_entropyBits`);
* proves the arithmetic deriving (36) from (35) (`marton_consequence_arith`) and
  `MartonInput.consequence_of_smoothing`: (36), i.e. `H(q_W K) ≤ 12 D(K)` and
  `dim W ≤ H(K) + 12 D(K) ≤ 13 H(K)`, from (35) and the two uniform-smoothing facts
  `d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2` and `d(K, U_W) ≥ |dim W − H(K)| / 2`.

What this file does NOT prove: the entropic Marton theorem (35) itself (it is a hypothesis here;
`martonBound` in `EntropyLean/PFRBridge.lean` proves it from the PFR project), and the two
uniform-smoothing facts, which
enter `MartonInput.consequence_of_smoothing` as explicit hypotheses `hsmooth`, `hlow`
(roadmap items D7b, D7c prove them and remove these hypotheses).
-/

namespace EntropyLean

universe u

open scoped ENNReal

open Classical in
/-- The indicator weights `1_W` of a subspace, before normalisation. -/
noncomputable def subIndicator {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (v : V) : ℝ≥0∞ :=
  if v ∈ W then 1 else 0

theorem subIndicator_le_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (v : V) : subIndicator W v ≤ 1 := by
  unfold subIndicator
  split_ifs <;> simp

theorem tsum_subIndicator_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) : ∑' v, subIndicator W v ≠ 0 := by
  intro h
  have h0 := ENNReal.tsum_eq_zero.mp h 0
  simp [subIndicator] at h0

theorem tsum_subIndicator_ne_top {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W : Submodule (ZMod 2) V) : ∑' v, subIndicator W v ≠ ∞ := by
  have hle : ∑' v, subIndicator W v ≤ ∑' _ : V, (1 : ℝ≥0∞) :=
    ENNReal.tsum_le_tsum (subIndicator_le_one W)
  have h1 : ∑' _ : V, (1 : ℝ≥0∞) = (Fintype.card V : ℝ≥0∞) := by
    rw [tsum_fintype]
    simp
  have h2 : ∑' _ : V, (1 : ℝ≥0∞) ≠ ∞ := by
    rw [h1]
    exact ENNReal.natCast_ne_top _
  exact ne_top_of_le_ne_top h2 hle

/-- The uniform law `U_W` on a subspace `W` of a finite F₂-space (the normalised indicator of
`W`; Mathlib no longer has a uniform `PMF` on a finset). -/
noncomputable def uniformSub {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W : Submodule (ZMod 2) V) : PMF V :=
  PMF.normalize (subIndicator W) (tsum_subIndicator_ne_zero W) (tsum_subIndicator_ne_top W)

/-- The entropic Marton bound (35) on a finite F₂-space `V`, as a named hypothesis: every law
`K` on `V` has a subspace `W` with `d(K, U_W) ≤ 6 D(K)`. -/
structure MartonInput (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] : Prop where
  /-- Equation (35). -/
  marton : ∀ K : PMF V, ∃ W : Submodule (ZMod 2) V,
    ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K

/-- The entropic Marton bound (35) on every finite F₂-space in universe `u`. -/
def MartonBound : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V], MartonInput V

/-- `D(K) ≥ 0` on a finite group. -/
theorem entropyIncrement_nonneg {V : Type*} [Fintype V] [AddGroup V] (K : PMF V) :
    0 ≤ entropyIncrement K := by
  have h := entropyBits_le_conv_left K K
  unfold entropyIncrement
  linarith

/-- `D(K) ≤ H(K)`, from `H(K * K) ≤ 2 H(K)`. -/
theorem entropyIncrement_le_entropyBits {V : Type*} [Fintype V] [Add V] (K : PMF V) :
    entropyIncrement K ≤ entropyBits K := by
  have h := entropyBits_conv_le K K
  unfold entropyIncrement
  linarith

/-- The arithmetic of Section 7: if `d = q + (n − h) / 2`, `|n − h| ≤ 2d` and `d ≤ 6D`, then
`q ≤ 12 D` and `n ≤ h + 12 D`. -/
theorem marton_consequence_arith {d q h n D : ℝ} (hd : d = q + (n - h) / 2)
    (hlow1 : h - n ≤ 2 * d) (hlow2 : n - h ≤ 2 * d) (hup : d ≤ 6 * D) :
    q ≤ 12 * D ∧ n ≤ h + 12 * D := by
  constructor <;> linarith

/-- Equation (36) from (35), with the two uniform-smoothing facts as explicit hypotheses:
some subspace `W` has `H(q_W K) ≤ 12 D(K)` and `dim W ≤ H(K) + 12 D(K) ≤ 13 H(K)`. -/
theorem MartonInput.consequence_of_smoothing {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (hM : MartonInput V) (K : PMF V)
    (hsmooth : ∀ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) =
      entropyBits (K.map fun v => W.mkQ v) +
        ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K) / 2)
    (hlow : ∀ W : Submodule (ZMod 2) V,
      |(Module.finrank (ZMod 2) W : ℝ) - entropyBits K| / 2 ≤ ruzsaDist K (uniformSub W)) :
    ∃ W : Submodule (ZMod 2) V,
      entropyBits (K.map fun v => W.mkQ v) ≤ 12 * entropyIncrement K ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ entropyBits K + 12 * entropyIncrement K ∧
      (Module.finrank (ZMod 2) W : ℝ) ≤ 13 * entropyBits K := by
  obtain ⟨W, hW⟩ := hM.marton K
  refine ⟨W, ?_⟩
  have h1 := hsmooth W
  have h2 := hlow W
  have ha := le_abs_self ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K)
  have hb := neg_abs_le ((Module.finrank (ZMod 2) W : ℝ) - entropyBits K)
  have hDH := entropyIncrement_le_entropyBits K
  obtain ⟨hq, hn⟩ := marton_consequence_arith h1 (by linarith) (by linarith) hW
  exact ⟨hq, hn, by linarith⟩

end EntropyLean
