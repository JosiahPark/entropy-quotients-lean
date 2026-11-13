import Mathlib
import EntropyLean.Information

/-!
# Conditional mutual information (roadmap item B2c)

For a joint law `P` of a triple `(A, B, C)` (a `PMF (α × β × γ)`), the conditional mutual
information `I(A ; B | C) = H(A, C) + H(B, C) - H(A, B, C) - H(C)` (`condMutualInfo`) and its
nonnegativity on finite types (`condMutualInfo_nonneg`). The proof is the cross-entropy Gibbs bound
`neg_mul_log_le_cross` against `q(a, b, c) = p(a, c) p(b, c) / p(c)`, whose total mass is at most
one (`sum_cond_ratio_le_one`).

What this file does NOT prove: the identity of `I(A ; B | C)` with an average of mutual
informations of conditional laws (no conditional `PMF`s are built), and no data-processing
inequality for Markov chains.
-/

namespace EntropyLean

variable {α β γ : Type*}

/-- The projection `(a, b, c) ↦ (a, c)`. -/
def tripleAC : α × β × γ → α × γ := fun x => (x.1, x.2.2)

/-- The projection `(a, b, c) ↦ c`. -/
def tripleC : α × β × γ → γ := fun x => x.2.2

/-- Conditional mutual information `I(A ; B | C) = H(A, C) + H(B, C) - H(A, B, C) - H(C)`. -/
noncomputable def condMutualInfo (P : PMF (α × β × γ)) : ℝ :=
  entropyBits (P.map tripleAC) + entropyBits (P.map Prod.snd) - entropyBits P -
    entropyBits (P.map tripleC)

/-- Summing a joint law of `(B, C)` over `B` gives the law of `C`. -/
theorem sum_fst_toReal [Fintype β] [Fintype γ] (Q : PMF (β × γ)) (c : γ) :
    ∑ b, (Q (b, c)).toReal = ((Q.map Prod.snd) c).toReal := by
  classical
  rw [pmf_map_toReal, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

/-- `∑_{a,b,c} p(a,c) p(b,c) / p(c) ≤ 1`. -/
theorem sum_cond_ratio_le_one [Fintype α] [Fintype β] [Fintype γ] (P : PMF (α × β × γ)) :
    ∑ x : α × β × γ, ((P.map tripleAC) (tripleAC x)).toReal * ((P.map Prod.snd) x.2).toReal /
      ((P.map tripleC) (tripleC x)).toReal ≤ 1 := by
  classical
  have hmarg : ∀ c : γ, ∑ b, ((P.map Prod.snd) (b, c)).toReal = ((P.map tripleC) c).toReal := by
    intro c
    rw [sum_fst_toReal (P.map Prod.snd) c, PMF.map_comp]
    try rfl
  calc ∑ x : α × β × γ, ((P.map tripleAC) (tripleAC x)).toReal * ((P.map Prod.snd) x.2).toReal /
        ((P.map tripleC) (tripleC x)).toReal
      = ∑ a, ∑ y : β × γ, ((P.map tripleAC) (a, y.2)).toReal * ((P.map Prod.snd) y).toReal /
          ((P.map tripleC) y.2).toReal := by
        rw [Fintype.sum_prod_type]
        try rfl
    _ = ∑ a, ∑ b, ∑ c, ((P.map tripleAC) (a, c)).toReal * ((P.map Prod.snd) (b, c)).toReal /
          ((P.map tripleC) c).toReal := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Fintype.sum_prod_type]
        try rfl
    _ = ∑ a, ∑ c, ((P.map tripleAC) (a, c)).toReal * ((P.map tripleC) c).toReal /
          ((P.map tripleC) c).toReal := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_div, ← Finset.mul_sum, hmarg c]
    _ ≤ ∑ a, ∑ c, ((P.map tripleAC) (a, c)).toReal := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
        rw [mul_div_assoc]
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg (div_self_le_one _)
    _ = 1 :=
        (Fintype.sum_prod_type (fun z => ((P.map tripleAC) z).toReal)).symm.trans
          (pmf_sum_toReal (P.map tripleAC))

/-- `I(A ; B | C) ≥ 0` in nats. -/
theorem condMutualInfo_nats_nonneg [Fintype α] [Fintype β] [Fintype γ] (P : PMF (α × β × γ)) :
    ∑ x, -(P x).toReal * Real.log (P x).toReal ≤
      ∑ z, -((P.map tripleAC) z).toReal * Real.log ((P.map tripleAC) z).toReal +
      ∑ y, -((P.map Prod.snd) y).toReal * Real.log ((P.map Prod.snd) y).toReal -
      ∑ c, -((P.map tripleC) c).toReal * Real.log ((P.map tripleC) c).toReal := by
  classical
  have hpt : ∀ x : α × β × γ, -(P x).toReal * Real.log (P x).toReal ≤
      -((P x).toReal * Real.log ((P.map tripleAC) (tripleAC x)).toReal +
        (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal -
        (P x).toReal * Real.log ((P.map tripleC) (tripleC x)).toReal) +
      (((P.map tripleAC) (tripleAC x)).toReal * ((P.map Prod.snd) x.2).toReal /
        ((P.map tripleC) (tripleC x)).toReal - (P x).toReal) := by
    intro x
    have hA := pmf_toReal_le_map P tripleAC x
    have hB := pmf_toReal_le_map P Prod.snd x
    have hC := pmf_toReal_le_map P tripleC x
    have h0 : 0 ≤ (P x).toReal := ENNReal.toReal_nonneg
    have hg := neg_mul_log_le_cross h0
      (div_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
      (fun hp => div_pos (mul_pos (lt_of_lt_of_le hp hA) (lt_of_lt_of_le hp hB))
        (lt_of_lt_of_le hp hC))
    have hsplit : (P x).toReal * Real.log
          (((P.map tripleAC) (tripleAC x)).toReal * ((P.map Prod.snd) x.2).toReal /
            ((P.map tripleC) (tripleC x)).toReal) =
        (P x).toReal * Real.log ((P.map tripleAC) (tripleAC x)).toReal +
          (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal -
          (P x).toReal * Real.log ((P.map tripleC) (tripleC x)).toReal := by
      rcases h0.eq_or_lt with hz | hpos
      · rw [← hz]
        ring
      · have hA' := (lt_of_lt_of_le hpos hA).ne'
        have hB' := (lt_of_lt_of_le hpos hB).ne'
        have hC' := (lt_of_lt_of_le hpos hC).ne'
        rw [Real.log_div (mul_ne_zero hA' hB') hC', Real.log_mul hA' hB']
        ring
    linarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hsum
  have S1 : ∑ x : α × β × γ, (P x).toReal * Real.log ((P.map tripleAC) (tripleAC x)).toReal =
      ∑ z, ((P.map tripleAC) z).toReal * Real.log ((P.map tripleAC) z).toReal :=
    sum_toReal_mul_comp P tripleAC (fun z => Real.log ((P.map tripleAC) z).toReal)
  have S2 : ∑ x : α × β × γ, (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal =
      ∑ y, ((P.map Prod.snd) y).toReal * Real.log ((P.map Prod.snd) y).toReal :=
    sum_toReal_mul_comp P Prod.snd (fun y => Real.log ((P.map Prod.snd) y).toReal)
  have S3 : ∑ x : α × β × γ, (P x).toReal * Real.log ((P.map tripleC) (tripleC x)).toReal =
      ∑ c, ((P.map tripleC) c).toReal * Real.log ((P.map tripleC) c).toReal :=
    sum_toReal_mul_comp P tripleC (fun c => Real.log ((P.map tripleC) c).toReal)
  have SQ := sum_cond_ratio_le_one P
  have S4 := pmf_sum_toReal P
  have N1 : ∑ z, -((P.map tripleAC) z).toReal * Real.log ((P.map tripleAC) z).toReal =
      -∑ z, ((P.map tripleAC) z).toReal * Real.log ((P.map tripleAC) z).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  have N2 : ∑ y, -((P.map Prod.snd) y).toReal * Real.log ((P.map Prod.snd) y).toReal =
      -∑ y, ((P.map Prod.snd) y).toReal * Real.log ((P.map Prod.snd) y).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have N3 : ∑ c, -((P.map tripleC) c).toReal * Real.log ((P.map tripleC) c).toReal =
      -∑ c, ((P.map tripleC) c).toReal * Real.log ((P.map tripleC) c).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  linarith

/-- `I(A ; B | C) ≥ 0` on finite types. -/
theorem condMutualInfo_nonneg [Fintype α] [Fintype β] [Fintype γ] (P : PMF (α × β × γ)) :
    0 ≤ condMutualInfo P := by
  have h := condMutualInfo_nats_nonneg P
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold condMutualInfo
  rw [entropyBits_eq_div_log P, entropyBits_eq_div_log (P.map tripleAC),
    entropyBits_eq_div_log (P.map Prod.snd), entropyBits_eq_div_log (P.map tripleC),
    ← add_div, ← sub_div, ← sub_div]
  exact div_nonneg (by linarith) hl.le

end EntropyLean
