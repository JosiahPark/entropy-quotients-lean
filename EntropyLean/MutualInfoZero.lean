import EntropyLean.MathlibForPFR
import EntropyLean.Information
import EntropyLean.Interaction

/-!
# Equality case of subadditivity (roadmap item H3b)

For a joint law `P` of a pair `(A, B)` on finite types, `I(A ; B) = 0` forces `A` and `B` to be
independent: `P = prodLaw (P.map Prod.fst) (P.map Prod.snd)`
(`eq_prodLaw_of_mutualInfo_eq_zero`).

The proof refines the proof of `entropyNats_subadditive`: the pointwise Gibbs slack
`crossSlack p q = −p log q + (q − p) + p log p` is nonnegative (`crossSlack_nonneg`), vanishes only
at `p = q` (`crossSlack_eq_zero`, from the strict bound `log y < y − 1` for `y ≠ 1`), and its sum
over the joint law with `q = P_A · P_B` equals `H(A) + H(B) − H(A, B)` in nats
(`sum_crossSlack`).

What this file does NOT prove: the zero-doubling case of (35) itself (roadmap items H3c, H3d).
-/

namespace EntropyLean

/-- Pointwise Gibbs slack `−p log q + (q − p) − (−p log p)` (natural log). -/
noncomputable def crossSlack (p q : ℝ) : ℝ :=
  -p * Real.log q + (q - p) - (-p * Real.log p)

theorem crossSlack_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    0 ≤ crossSlack p q := by
  unfold crossSlack
  linarith [neg_mul_log_le_cross hp hq hpq]

/-- The Gibbs slack vanishes only at `p = q`. -/
theorem crossSlack_eq_zero {p q : ℝ} (hp : 0 ≤ p) (hpq : 0 < p → 0 < q)
    (h : crossSlack p q = 0) : p = q := by
  unfold crossSlack at h
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0] at h
    rw [← h0]
    linarith
  · have hq' := hpq hpos
    by_contra hne
    have hy : q / p ≠ 1 := by
      intro h1
      exact hne ((div_eq_one_iff_eq hpos.ne').mp h1).symm
    have key := Real.log_lt_sub_one_of_pos (div_pos hq' hpos) hy
    rw [Real.log_div hq'.ne' hpos.ne'] at key
    have k2 := mul_lt_mul_of_pos_left key hpos
    have e : p * (q / p - 1) = q - p := by
      field_simp
    rw [e] at k2
    linarith [mul_sub p (Real.log q) (Real.log p), neg_mul p (Real.log q),
      neg_mul p (Real.log p)]

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Summing the slack over a joint law against the product of its marginals gives
`H(A) + H(B) − H(A, B)` in nats. -/
theorem sum_crossSlack (P : PMF (α × β)) :
    ∑ x : α × β, crossSlack (P x).toReal
        (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal) =
      ∑ a, -((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal +
        ∑ b, -((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal -
        ∑ x, -(P x).toReal * Real.log (P x).toReal := by
  classical
  have hpt : ∀ x : α × β, crossSlack (P x).toReal
      (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal) =
      -((P x).toReal * Real.log ((P.map Prod.fst) x.1).toReal +
        (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal) +
      (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal - (P x).toReal) +
      (P x).toReal * Real.log (P x).toReal := by
    intro x
    unfold crossSlack
    have hA := pmf_toReal_le_map P Prod.fst x
    have hB := pmf_toReal_le_map P Prod.snd x
    have h0 : 0 ≤ (P x).toReal := ENNReal.toReal_nonneg
    rcases h0.eq_or_lt with hz | hpos
    · rw [← hz]
      ring
    · rw [Real.log_mul (lt_of_lt_of_le hpos hA).ne' (lt_of_lt_of_le hpos hB).ne']
      ring
  rw [Finset.sum_congr rfl fun x _ => hpt x]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  have S1 : ∑ x : α × β, (P x).toReal * Real.log ((P.map Prod.fst) x.1).toReal =
      ∑ a, ((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal :=
    sum_toReal_mul_comp P Prod.fst (fun a => Real.log ((P.map Prod.fst) a).toReal)
  have S2 : ∑ x : α × β, (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal =
      ∑ b, ((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal :=
    sum_toReal_mul_comp P Prod.snd (fun b => Real.log ((P.map Prod.snd) b).toReal)
  have S3 : ∑ x : α × β, ((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal = 1 := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, pmf_sum_toReal, mul_one]
  have S4 := pmf_sum_toReal P
  have N0 : ∑ x, -(P x).toReal * Real.log (P x).toReal =
      -∑ x, (P x).toReal * Real.log (P x).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have N1 : ∑ a, -((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal =
      -∑ a, ((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have N2 : ∑ b, -((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal =
      -∑ b, ((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  linarith

/-- Equality case of subadditivity: `I(A ; B) = 0` forces `P = P_A ⊗ P_B`. -/
theorem eq_prodLaw_of_mutualInfo_eq_zero (P : PMF (α × β)) (h : mutualInfo P = 0) :
    P = prodLaw (P.map Prod.fst) (P.map Prod.snd) := by
  classical
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mutualInfo at h
  rw [entropyBits_eq_div_log P, entropyBits_eq_div_log (P.map Prod.fst),
    entropyBits_eq_div_log (P.map Prod.snd), ← add_div, ← sub_div, div_eq_zero_iff] at h
  have hn := h.resolve_right hl.ne'
  have hpos : ∀ x : α × β, 0 < (P x).toReal →
      0 < ((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal := fun x hp =>
    mul_pos (lt_of_lt_of_le hp (pmf_toReal_le_map P Prod.fst x))
      (lt_of_lt_of_le hp (pmf_toReal_le_map P Prod.snd x))
  have hnn : ∀ x ∈ (Finset.univ : Finset (α × β)), 0 ≤ crossSlack (P x).toReal
      (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal) := fun x _ =>
    crossSlack_nonneg ENNReal.toReal_nonneg
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hpos x)
  have hsum0 : ∑ x : α × β, crossSlack (P x).toReal
      (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal) = 0 := by
    rw [sum_crossSlack]
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  apply PMF.ext
  intro x
  have hx := crossSlack_eq_zero ENNReal.toReal_nonneg (hpos x) (hall x (Finset.mem_univ x))
  obtain ⟨i, j⟩ := x
  rw [prodLaw_apply, ← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)), ENNReal.toReal_mul]
  exact hx

end EntropyLean
