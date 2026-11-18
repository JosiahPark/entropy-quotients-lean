import EntropyLean.MathlibForPFR
import EntropyLean.Bernoulli
import EntropyLean.Posterior
import EntropyLean.DoubleTrial

/-!
# Bernoulli bits over F₂ (roadmap item E1)

`bernoulliBit p` is the law on `ZMod 2` with mass `1 - p` at `0` and `p` at `1`, for `0 ≤ p ≤ 1`.

Proved here:
* `sum_zmod2_eq`: a sum over `ZMod 2` is the value at `0` plus the value at `1`;
* `bernoulliBit_toReal_zero`, `bernoulliBit_toReal_one`: the masses;
* `entropyBits_bernoulliBit`: `H(Bernoulli(p)) = binaryEntropy p` (also at `p = 0` and `p = 1`);
* `conv_bernoulliBit`: the sum of two independent Bernoulli(p) bits is Bernoulli(2p(1−p));
* `entropyIncrement_bernoulliBit`, `entropyDefect_bernoulliBit`: `D` and `E` of a Bernoulli(p) bit
  are `bernoulliIncrement p` and `bernoulliDefect p`.

What this file does NOT prove: the expansions of `binaryEntropy p` and `bernoulliDefect p` for
small `p` (roadmap item E2), and Proposition 9.3 (`exponential_scale_necessary`, item E3).
-/

namespace EntropyLean

open scoped BigOperators

/-- `ZMod 2` has exactly the two elements `0` and `1`. -/
theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

/-- A sum over `ZMod 2` is the value at `0` plus the value at `1`. -/
theorem sum_zmod2_eq {M : Type*} [AddCommMonoid M] (g : ZMod 2 → M) :
    ∑ x : ZMod 2, g x = g 0 + g 1 := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact zmod2_eq_zero_or_one x
  rw [huniv, Finset.sum_pair (show (0 : ZMod 2) ≠ 1 by decide)]

/-- The Bernoulli(p) law on `ZMod 2`: mass `1 - p` at `0` and `p` at `1`. -/
noncomputable def bernoulliBit (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : PMF (ZMod 2) :=
  PMF.ofFintype (fun x => if x = 0 then ENNReal.ofReal (1 - p) else ENNReal.ofReal p) (by
    rw [sum_zmod2_eq, if_pos rfl, if_neg (show (1 : ZMod 2) ≠ 0 by decide),
      ← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 - p by linarith) h0, sub_add_cancel, ENNReal.ofReal_one])

theorem bernoulliBit_toReal_zero (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (bernoulliBit p h0 h1 0).toReal = 1 - p := by
  unfold bernoulliBit
  rw [PMF.ofFintype_apply, if_pos rfl, ENNReal.toReal_ofReal (show (0 : ℝ) ≤ 1 - p by linarith)]

theorem bernoulliBit_toReal_one (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (bernoulliBit p h0 h1 1).toReal = p := by
  unfold bernoulliBit
  rw [PMF.ofFintype_apply, if_neg (show (1 : ZMod 2) ≠ 0 by decide), ENNReal.toReal_ofReal h0]

/-- **E1, first half.** The entropy of a Bernoulli(p) bit is the binary entropy `h₂(p)`. -/
theorem entropyBits_bernoulliBit (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropyBits (bernoulliBit p h0 h1) = binaryEntropy p := by
  rw [entropyBits_eq_sum]
  simp only [sum_zmod2_eq, bernoulliBit_toReal_zero, bernoulliBit_toReal_one]
  unfold binaryEntropy
  split_ifs with h
  · ring
  · rcases lt_or_eq_of_le h0 with hp | hp
    · have hp1 : p = 1 := by
        by_contra hne
        exact h ⟨hp, lt_of_le_of_ne h1 hne⟩
      subst hp1
      simp
    · subst hp
      simp

theorem bernoulliBit_param_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ 2 * p * (1 - p) :=
  mul_nonneg (mul_nonneg (by norm_num) h0) (by linarith)

theorem bernoulliBit_param_le_one {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    2 * p * (1 - p) ≤ 1 := by
  nlinarith [sq_nonneg p, sq_nonneg (1 - p)]

/-- **E1, second half.** The sum of two independent Bernoulli(p) bits is Bernoulli(2p(1−p)). -/
theorem conv_bernoulliBit (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    conv (bernoulliBit p h0 h1) (bernoulliBit p h0 h1) =
      bernoulliBit (2 * p * (1 - p)) (bernoulliBit_param_nonneg h0 h1)
        (bernoulliBit_param_le_one h0 h1) := by
  apply pmf_ext_toReal
  intro x
  rw [conv_toReal_eq_sum]
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · have h01 : (0 : ZMod 2) - 1 = 1 := by decide
    simp only [sum_zmod2_eq, sub_zero, h01, bernoulliBit_toReal_zero, bernoulliBit_toReal_one]
    ring
  · have h11 : (1 : ZMod 2) - 1 = 0 := by decide
    simp only [sum_zmod2_eq, sub_zero, h11, bernoulliBit_toReal_zero, bernoulliBit_toReal_one]
    ring

/-- The entropy increment of a Bernoulli(p) bit is `h₂(2p(1−p)) − h₂(p)`. -/
theorem entropyIncrement_bernoulliBit (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropyIncrement (bernoulliBit p h0 h1) = bernoulliIncrement p := by
  unfold entropyIncrement bernoulliIncrement
  rw [conv_bernoulliBit, entropyBits_bernoulliBit, entropyBits_bernoulliBit]

/-- The entropy defect of a Bernoulli(p) bit is `2h₂(p) − h₂(2p(1−p))`. -/
theorem entropyDefect_bernoulliBit (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropyDefect (bernoulliBit p h0 h1) = bernoulliDefect p := by
  unfold entropyDefect bernoulliDefect
  rw [conv_bernoulliBit, entropyBits_bernoulliBit, entropyBits_bernoulliBit]

end EntropyLean
