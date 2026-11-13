import Mathlib
import EntropyLean.Basic

/-!
# Elementary entropy facts

Roadmap item A1: the pointwise bound `0 ≤ -p * log₂ p` for `0 ≤ p ≤ 1`, and nonnegativity of
`entropyBits` (for a law on a finite type, and also for a law on an arbitrary type, since the
`tsum` of nonnegative terms is nonnegative whether or not it converges).

Roadmap item A2: a point mass has entropy zero (`entropyBits_pure`), and a law on a finite type
has entropy at most `log₂` of the cardinality (`entropyBits_le_log_card`), via the pointwise
Gibbs bound `-p log p ≤ p log c + (1/c - p)` (`neg_mul_log_le_gibbs`).

Roadmap item A3: data processing for a function, `H(f(X)) ≤ H(X)` for `PMF.map f` on finite
types (`entropyBits_map_le`), with equality for injective `f` (`entropyBits_map_injective`).
It rests on the elementary bound `-(∑ xᵢ) log₂ (∑ xᵢ) ≤ ∑ -xᵢ log₂ xᵢ` for `xᵢ ≥ 0`
(`neg_mul_logb_sum_le`) and the fibre formula for the masses of `PMF.map f` (`pmf_map_toReal`).

What this file does NOT prove: no equality case of the cardinality bound, no conditional
entropy or data processing for the increment `D` (B5), and nothing about convolutions or
quotients (roadmap items A4–A5, B2–B6). The map lemmas need a `Fintype` on the target, so they
do not yet apply to quotients `V ⧸ W` without such an instance.
-/

namespace EntropyLean

open scoped BigOperators

/-- `0 ≤ -p log₂ p` for `0 ≤ p ≤ 1`. -/
theorem negMulLogb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ -p * Real.logb 2 p := by
  have h : Real.logb 2 p ≤ 0 := Real.logb_nonpos (by norm_num) hp0 hp1
  have e : -p * Real.logb 2 p = p * (-Real.logb 2 p) := by ring
  rw [e]
  exact mul_nonneg hp0 (neg_nonneg.mpr h)

/-- A probability mass, as a real number, lies in `[0, 1]`. -/
theorem pmf_toReal_le_one {α : Type*} (P : PMF α) (a : α) : (P a).toReal ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top (P.coe_le_one a)
  simpa using h

/-- Each term of the entropy sum is nonnegative. -/
theorem entropyBits_term_nonneg {α : Type*} (P : PMF α) (a : α) :
    0 ≤ -(P a).toReal * Real.logb 2 (P a).toReal :=
  negMulLogb_nonneg ENNReal.toReal_nonneg (pmf_toReal_le_one P a)

/-- Entropy of a law on a finite type is nonnegative. -/
theorem entropyBits_nonneg {α : Type*} [Fintype α] (P : PMF α) : 0 ≤ entropyBits P := by
  rw [entropyBits_eq_sum]
  exact Finset.sum_nonneg fun a _ => entropyBits_term_nonneg P a

/-- Entropy of a law on any type is nonnegative (the `tsum` of nonnegative terms). -/
theorem entropyBits_nonneg' {α : Type*} (P : PMF α) : 0 ≤ entropyBits P := by
  unfold entropyBits
  exact tsum_nonneg fun a => entropyBits_term_nonneg P a

/-- A point mass has entropy zero. -/
theorem entropyBits_pure {α : Type*} (a : α) : entropyBits (PMF.pure a) = 0 := by
  unfold entropyBits
  have h : ∀ b, -((PMF.pure a) b).toReal * Real.logb 2 ((PMF.pure a) b).toReal = 0 := by
    intro b
    rw [PMF.pure_apply]
    split_ifs <;> simp
  simp only [h, tsum_zero]

/-- Pointwise Gibbs bound (natural log): `-p log p ≤ p log c + (1/c - p)` for `p ≥ 0`, `c > 0`.
It comes from `log x ≤ x - 1` at `x = 1/(c p)`. -/
theorem neg_mul_log_le_gibbs {p c : ℝ} (hp : 0 ≤ p) (hc : 0 < c) :
    -p * Real.log p ≤ p * Real.log c + (1 / c - p) := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]
    have h1 : (0 : ℝ) < 1 / c := one_div_pos.mpr hc
    simp only [neg_zero, zero_mul, zero_add, sub_zero]
    exact h1.le
  · have hx : (0 : ℝ) < 1 / (c * p) := one_div_pos.mpr (mul_pos hc h)
    have key : Real.log (1 / (c * p)) ≤ 1 / (c * p) - 1 := Real.log_le_sub_one_of_pos hx
    have e : Real.log (1 / (c * p)) = -(Real.log c + Real.log p) := by
      rw [one_div, Real.log_inv, Real.log_mul hc.ne' h.ne']
    have h2 : p * (1 / (c * p)) = 1 / c := by
      rw [mul_one_div, mul_comm c p, div_mul_eq_div_div, div_self h.ne']
    have h4 : p * (1 / (c * p) - 1) = 1 / c - p := by
      rw [mul_sub, h2, mul_one]
    have h3 := mul_le_mul_of_nonneg_left key h.le
    rw [e, h4] at h3
    have h5 : -p * Real.log p = p * -(Real.log c + Real.log p) + p * Real.log c := by ring
    rw [h5]
    linarith

/-- The masses of a law on a finite type sum to one (as reals). -/
theorem pmf_sum_toReal {α : Type*} [Fintype α] (P : PMF α) : ∑ a, (P a).toReal = 1 := by
  have h1 : ∑ a, P a = 1 :=
    calc ∑ a, P a = ∑' a, P a := (tsum_fintype _).symm
      _ = 1 := P.tsum_coe
  rw [← ENNReal.toReal_sum (fun a _ => P.apply_ne_top a), h1]
  simp

/-- Entropy of a law on a finite type is at most `log₂ |α|`. -/
theorem entropyBits_le_log_card {α : Type*} [Fintype α] (P : PMF α) :
    entropyBits P ≤ Real.logb 2 (Fintype.card α) := by
  obtain ⟨a0, _⟩ := P.support_nonempty
  have hn : (0 : ℝ) < (Fintype.card α : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨a0⟩)
  have hsum := pmf_sum_toReal P
  have hS : ∑ a, -(P a).toReal * Real.log (P a).toReal ≤ Real.log (Fintype.card α : ℝ) := by
    calc ∑ a, -(P a).toReal * Real.log (P a).toReal
        ≤ ∑ a, ((P a).toReal * Real.log (Fintype.card α : ℝ)
            + (1 / (Fintype.card α : ℝ) - (P a).toReal)) :=
          Finset.sum_le_sum fun a _ => neg_mul_log_le_gibbs ENNReal.toReal_nonneg hn
      _ = (∑ a, (P a).toReal) * Real.log (Fintype.card α : ℝ)
            + ((Fintype.card α : ℝ) * (1 / (Fintype.card α : ℝ)) - ∑ a, (P a).toReal) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
      _ = Real.log (Fintype.card α : ℝ) := by
          rw [hsum, mul_one_div_cancel hn.ne', one_mul, sub_self, add_zero]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : ∑ a, -(P a).toReal * Real.logb 2 (P a).toReal =
      (∑ a, -(P a).toReal * Real.log (P a).toReal) / Real.log 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Real.log_div_log]
    ring
  rw [entropyBits_eq_sum, e, ← Real.log_div_log]
  exact div_le_div_of_nonneg_right hS hl.le

/-- `-(∑ xᵢ) log₂ (∑ xᵢ) ≤ ∑ -xᵢ log₂ xᵢ` for nonnegative `xᵢ`: merging masses does not
increase entropy. -/
theorem neg_mul_logb_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    -(∑ i ∈ s, x i) * Real.logb 2 (∑ i ∈ s, x i) ≤ ∑ i ∈ s, -x i * Real.logb 2 (x i) := by
  have h : ∀ i ∈ s, -x i * Real.logb 2 (∑ j ∈ s, x j) ≤ -x i * Real.logb 2 (x i) := by
    intro i hi
    have hxi : 0 ≤ x i := hx i hi
    have hle : x i ≤ ∑ j ∈ s, x j := Finset.single_le_sum hx hi
    rcases hxi.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp
    · have hl : Real.logb 2 (x i) ≤ Real.logb 2 (∑ j ∈ s, x j) := by
        first
        | exact Real.logb_le_logb_of_le (by norm_num) hpos hle
        | exact (Real.logb_le_logb (by norm_num) hpos (lt_of_lt_of_le hpos hle)).mpr hle
      have hm := mul_le_mul_of_nonneg_left hl hxi
      linarith
  calc -(∑ i ∈ s, x i) * Real.logb 2 (∑ i ∈ s, x i)
      = ∑ i ∈ s, -x i * Real.logb 2 (∑ j ∈ s, x j) := by
        rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ ≤ ∑ i ∈ s, -x i * Real.logb 2 (x i) := Finset.sum_le_sum h

/-- The mass of `PMF.map f P` at `b` is the total mass of the fibre `f⁻¹(b)`. -/
theorem pmf_map_toReal {α β : Type*} [Fintype α] [DecidableEq β] (P : PMF α) (f : α → β)
    (b : β) :
    ((P.map f) b).toReal = ∑ a ∈ Finset.univ.filter (fun a => f a = b), (P a).toReal := by
  have h1 : (P.map f) b = ∑ a ∈ Finset.univ.filter (fun a => f a = b), P a := by
    rw [PMF.map_apply, tsum_fintype, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : f a = b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [h1, ENNReal.toReal_sum (fun a _ => P.apply_ne_top a)]

/-- Data processing for a function: `H(f(X)) ≤ H(X)` on finite types. -/
theorem entropyBits_map_le {α β : Type*} [Fintype α] [Fintype β] (P : PMF α) (f : α → β) :
    entropyBits (P.map f) ≤ entropyBits P := by
  classical
  rw [entropyBits_eq_sum (P.map f), entropyBits_eq_sum P]
  have key : ∀ b, -((P.map f) b).toReal * Real.logb 2 ((P.map f) b).toReal ≤
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), -(P a).toReal * Real.logb 2 (P a).toReal := by
    intro b
    rw [pmf_map_toReal P f b]
    exact neg_mul_logb_sum_le _ (fun a => (P a).toReal) (fun a _ => ENNReal.toReal_nonneg)
  calc ∑ b, -((P.map f) b).toReal * Real.logb 2 ((P.map f) b).toReal
      ≤ ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b),
          -(P a).toReal * Real.logb 2 (P a).toReal := Finset.sum_le_sum fun b _ => key b
    _ = ∑ a, -(P a).toReal * Real.logb 2 (P a).toReal := by
        first
        | exact Finset.sum_fiberwise Finset.univ f _
        | exact Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_univ (f a))

/-- An injective map preserves entropy: `H(f(X)) = H(X)` for injective `f` on finite types. -/
theorem entropyBits_map_injective {α β : Type*} [Fintype α] [Fintype β] (P : PMF α)
    {f : α → β} (hf : Function.Injective f) :
    entropyBits (P.map f) = entropyBits P := by
  obtain ⟨a0, _⟩ := P.support_nonempty
  haveI : Nonempty α := ⟨a0⟩
  apply le_antisymm (entropyBits_map_le P f)
  have h : (P.map f).map (Function.invFun f) = P := by
    rw [PMF.map_comp, Function.invFun_comp hf, PMF.map_id]
  calc entropyBits P = entropyBits ((P.map f).map (Function.invFun f)) := by rw [h]
    _ ≤ entropyBits (P.map f) := entropyBits_map_le _ _

end EntropyLean
