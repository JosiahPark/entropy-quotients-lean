import Mathlib
import EntropyLean.Posterior
import EntropyLean.CondInformation

/-!
# Posterior formation and the subspace defect, pair level (roadmap item D3c1)

For independent `A ∼ P`, `B ∼ Q` on a finite abelian group `V` and any map `f : V → W` to a finite
type, let `J` be the joint law of `(f A, A + B)` (`jointLaw`). This file computes the masses of `J`
(`jointLaw_toReal`, `sum_jointLaw_toReal`) and of the image under `f` of the posterior law
`Q_t = Law(A | A + B = t)` (`posteriorLaw_map_toReal`), and proves the chain rule
`∑ₜ (P * Q)(t) H(f_* Q_t) = H(f A, A + B) − H(A + B)` (`sum_conv_mul_entropy_posterior_map`).
Together with `sum_conv_mul_entropy_posterior` (item D3b) this gives
`∑ₜ (P * Q)(t) (H(Q_t) − H(f_* Q_t)) = H(P) + H(Q) − H(f A, A + B)`.

What this file does NOT prove: the inequality `H(f A) + H(B) ≤ H(f A, A + B)`, the pair-level bound
`∑ₜ (P * Q)(t) F_{Q_t}(G) ≤ F_P(G)` (item D3c2), the family-level inequality
`F_{Post 𝒫}(W) ≤ F_𝒫(W)`, or `posterior_closure` (item D3c3).
-/

namespace EntropyLean

open scoped BigOperators

/-- Joint law of `(f A, A + B)` for independent `A ∼ P`, `B ∼ Q`. -/
noncomputable def jointLaw {V W : Type*} [AddCommGroup V] (P Q : PMF V) (f : V → W) :
    PMF (W × V) :=
  (prodLaw P Q).map fun x => (f x.1, x.1 + x.2)

/-- Masses of the joint law of `(f A, A + B)`. -/
theorem jointLaw_toReal {V W : Type*} [Fintype V] [AddCommGroup V] [DecidableEq W]
    (P Q : PMF V) (f : V → W) (w : W) (t : V) :
    ((jointLaw P Q f) (w, t)).toReal =
      ∑ a, if f a = w then (P a).toReal * (Q (t - a)).toReal else 0 := by
  classical
  unfold jointLaw
  rw [pmf_map_toReal, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : f a = w
  · rw [if_pos ha, Finset.sum_eq_single (t - a)]
    · rw [if_pos, prodLaw_apply, ENNReal.toReal_mul]
      simp [ha]
    · intro b _ hb
      rw [if_neg]
      intro h
      apply hb
      have h2 : a + b = t := congrArg Prod.snd h
      rw [← h2]
      abel
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg ha]
    refine Finset.sum_eq_zero fun b _ => if_neg ?_
    intro h
    exact ha (congrArg Prod.fst h)

/-- The second marginal of the joint law is the law of `A + B`. -/
theorem jointLaw_map_snd {V W : Type*} [AddCommGroup V] (P Q : PMF V) (f : V → W) :
    (jointLaw P Q f).map Prod.snd = conv P Q := by
  unfold jointLaw
  rw [PMF.map_comp, ← prodLaw_map_add]
  try rfl

/-- `∑_w J(w, t) = (P * Q)(t)`. -/
theorem sum_jointLaw_toReal {V W : Type*} [Fintype V] [AddCommGroup V] [Fintype W]
    (P Q : PMF V) (f : V → W) (t : V) :
    ∑ w, ((jointLaw P Q f) (w, t)).toReal = (conv P Q t).toReal := by
  rw [sum_fst_toReal, jointLaw_map_snd]

/-- Masses of the image under `f` of the posterior law. -/
theorem posteriorLaw_map_toReal {V W : Type*} [Fintype V] [AddCommGroup V] (P Q : PMF V)
    (f : V → W) {t : V} (h : conv P Q t ≠ 0) (w : W) :
    (((posteriorLaw P Q t).map f) w).toReal =
      ((jointLaw P Q f) (w, t)).toReal / (conv P Q t).toReal := by
  classical
  rw [pmf_map_toReal, Finset.sum_filter, jointLaw_toReal, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [posteriorLaw_toReal P Q h]
  · rw [zero_div]

/-- `C · (-(m/C) log(m/C)) = -m log m + m log C` for `m ≥ 0`, `C > 0`. -/
theorem mul_neg_div_logb_eq {m C : ℝ} (hm : 0 ≤ m) (hC : 0 < C) :
    C * (-(m / C) * Real.logb 2 (m / C)) = -m * Real.logb 2 m + m * Real.logb 2 C := by
  rcases hm.eq_or_lt with h | h
  · rw [← h]
    ring
  have hC' : C ≠ 0 := hC.ne'
  rw [Real.logb_div h.ne' hC']
  have e : C * (m / C) = m := by
    first
    | (field_simp; done)
    | (field_simp; ring)
    | (rw [mul_comm]; exact div_mul_cancel₀ _ hC')
  calc C * (-(m / C) * (Real.logb 2 m - Real.logb 2 C))
      = -(C * (m / C)) * (Real.logb 2 m - Real.logb 2 C) := by ring
    _ = _ := by
        rw [e]
        ring

/-- `(P * Q)(t) · H(f_* Law(A | A + B = t))`, written as a sum over `w`. -/
theorem conv_mul_entropy_posterior_map {V W : Type*} [Fintype V] [AddCommGroup V] [Fintype W]
    (P Q : PMF V) (f : V → W) (t : V) :
    (conv P Q t).toReal * entropyBits ((posteriorLaw P Q t).map f) =
      ∑ w, (-((jointLaw P Q f) (w, t)).toReal * Real.logb 2 ((jointLaw P Q f) (w, t)).toReal +
        ((jointLaw P Q f) (w, t)).toReal * Real.logb 2 (conv P Q t).toReal) := by
  have hsum := sum_jointLaw_toReal P Q f t
  by_cases h : conv P Q t = 0
  · have hC : (conv P Q t).toReal = 0 := by rw [h, ENNReal.toReal_zero]
    have h0 : ∀ w, ((jointLaw P Q f) (w, t)).toReal = 0 := fun w =>
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => ENNReal.toReal_nonneg).mp (hsum.trans hC) w
        (Finset.mem_univ w)
    rw [hC, zero_mul]
    first
    | (simp only [h0, neg_zero, zero_mul, add_zero, Finset.sum_const_zero]; done)
    | simp [h0]
  · have hC : 0 < (conv P Q t).toReal := ENNReal.toReal_pos h (PMF.apply_ne_top _ _)
    rw [entropyBits_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [posteriorLaw_map_toReal P Q f h]
    exact mul_neg_div_logb_eq ENNReal.toReal_nonneg hC

/-- Chain rule: `∑ₜ (P * Q)(t) H(f_* Law(A | A + B = t)) = H(f A, A + B) − H(A + B)`. -/
theorem sum_conv_mul_entropy_posterior_map {V W : Type*} [Fintype V] [AddCommGroup V]
    [Fintype W] (P Q : PMF V) (f : V → W) :
    ∑ t, (conv P Q t).toReal * entropyBits ((posteriorLaw P Q t).map f) =
      entropyBits (jointLaw P Q f) - entropyBits (conv P Q) := by
  simp only [conv_mul_entropy_posterior_map, Finset.sum_add_distrib]
  have T1 : ∑ t, ∑ w, -((jointLaw P Q f) (w, t)).toReal *
      Real.logb 2 ((jointLaw P Q f) (w, t)).toReal = entropyBits (jointLaw P Q f) := by
    rw [entropyBits_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  have T2 : ∑ t, ∑ w, ((jointLaw P Q f) (w, t)).toReal * Real.logb 2 (conv P Q t).toReal =
      -entropyBits (conv P Q) := by
    rw [entropyBits_eq_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul, sum_jointLaw_toReal]
    ring
  rw [T1, T2]
  ring

end EntropyLean
