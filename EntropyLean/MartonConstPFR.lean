import EntropyLean.MathlibForPFR
import EntropyLean.MartonChainConst

/-!
# The exponent from a Marton bound with constant 11/2 (roadmap item H5)

Arithmetic only. With the entropic Marton bound (35) assumed with constant `C`
(`MartonBoundConst C`), Theorem 8.2 holds with `martonRigidityConst C = 48C + 17 + 2 log₂(1 + C)`
(item G2). At `C = 11/2` this is `281 + 2 log₂(13/2) < 287`.

Proved here:
* `martonRigidityConst_eleven_half_lt`: `martonRigidityConst (11/2) < 287`;
* from `MartonBoundConst.{0} (11/2)` as the only hypothesis, in every universe: Theorem 8.2 with
  constant 287 (`weighted_family_rigidity_287_of_marton_const`), the conclusion of Theorem 1.1
  with `dim G ≤ 2^(287(1+ε)/ε) H(X)` (`exponential_entropy_quotient_287_of_marton_const`), and the
  conclusion of Theorem 1.2 with `min(1, 287 / log₂(1/λ))` (`sparse_rigidity_287_of_marton_const`).

What this file does NOT prove: the entropic Marton bound with constant `11/2`, or with any
constant; it is the hypothesis `hM`. It does not claim that such a bound is available: it only
records what one would give. None of Theorems 1.1, 1.2, 8.2 is proved unconditionally.
-/

universe u

namespace EntropyLean

/-- `K(11/2) = 281 + 2 log₂(13/2) < 287`, since `13/2 < 8`. -/
theorem martonRigidityConst_eleven_half_lt : martonRigidityConst (11 / 2) < 287 := by
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    have e : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
    rw [e, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  have h13 : Real.logb 2 (13 / 2 : ℝ) < Real.logb 2 (8 : ℝ) :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [martonRigidityConst_eq (by norm_num : (0 : ℝ) ≤ 11 / 2)]
  have e : (1 : ℝ) + 11 / 2 = 13 / 2 := by norm_num
  rw [e]
  linarith

/-- Theorem 8.2 with constant 287, from the entropic Marton bound with constant `11/2` on spaces
in `Type`. -/
theorem weighted_family_rigidity_287_of_marton_const (hM : MartonBoundConst.{0} (11 / 2)) :
    WeightedFamilyRigidityConst.{u} 287 :=
  (weighted_family_rigidity_of_marton_const hM (by norm_num)).mono
    martonRigidityConst_eleven_half_lt.le

/-- **H5.** The conclusion of Theorem 1.1 with `dim G ≤ 2^(287(1+ε)/ε) H(X)`, from the entropic
Marton bound with constant `11/2` on spaces in `Type`. -/
theorem exponential_entropy_quotient_287_of_marton_const {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V] [Fintype V] (hM : MartonBoundConst.{0} (11 / 2))
    (ε : ℝ) (hε : 0 < ε) (X : PMF V) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (287 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_rigidity_const (by norm_num)
    (weighted_family_rigidity_287_of_marton_const hM) ε hε X

/-- The conclusion of Theorem 1.2 with constant 287, from the entropic Marton bound with constant
`11/2` on spaces in `Type`. -/
theorem sparse_rigidity_287_of_marton_const {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (hM : MartonBoundConst.{0} (11 / 2)) (lam : ℝ)
    (hlam : 0 < lam ∧ lam < 1) (Z : PMF V) (hsparse : IsSparse lam Z)
    (hpos : 0 < entropyBits Z) :
    entropyDefect Z / entropyBits Z ≤ min 1 (287 / Real.logb 2 (1 / lam)) :=
  sparse_rigidity_of_family_rigidity_const (weighted_family_rigidity_287_of_marton_const hM) lam
    hlam Z hsparse hpos

end EntropyLean
