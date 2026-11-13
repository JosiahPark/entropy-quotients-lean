import Mathlib
import EntropyLean.EntropyFacts
import EntropyLean.QuotientFacts

/-!
# Conditional entropy and mutual information (roadmap items B2a, B2b)

For a joint law `P` of a pair `(A, B)` (a `PMF (α × β)`): the conditional entropy
`H(A | B) = H(A, B) - H(B)` (`condEntropy`), the mutual information
`I(A ; B) = H(A) + H(B) - H(A, B)` (`mutualInfo`), the chain rule
`H(A, B) = H(B) + H(A | B)` (`entropyBits_chain`), `H(A | B) ≥ 0` on finite types
(`condEntropy_nonneg`), the bounds `I(A ; B) ≤ H(A)`, `I(A ; B) ≤ H(B)`
(`mutualInfo_le_left`, `mutualInfo_le_right`), and symmetry of `I` under swapping the pair
(`mutualInfo_swap`).

Item B2b adds subadditivity `H(A, B) ≤ H(A) + H(B)` (`entropyBits_subadditive`), hence
`I(A ; B) ≥ 0` (`mutualInfo_nonneg`) and `H(A | B) ≤ H(A)` (`condEntropy_le`), via the cross-entropy
Gibbs bound `neg_mul_log_le_cross`.

What this file does NOT prove: conditional mutual information or `I(A ; B | C) ≥ 0` (item B2c). The definitions take the joint
law as primitive; marginals are `P.map Prod.fst` and `P.map Prod.snd`.
-/

namespace EntropyLean

variable {α β : Type*}

/-- Conditional entropy `H(A | B) = H(A, B) - H(B)` of a joint law of `(A, B)`. -/
noncomputable def condEntropy (P : PMF (α × β)) : ℝ :=
  entropyBits P - entropyBits (P.map Prod.snd)

/-- Mutual information `I(A ; B) = H(A) + H(B) - H(A, B)` of a joint law of `(A, B)`. -/
noncomputable def mutualInfo (P : PMF (α × β)) : ℝ :=
  entropyBits (P.map Prod.fst) + entropyBits (P.map Prod.snd) - entropyBits P

/-- Chain rule: `H(A, B) = H(B) + H(A | B)`. -/
theorem entropyBits_chain (P : PMF (α × β)) :
    entropyBits P = entropyBits (P.map Prod.snd) + condEntropy P := by
  unfold condEntropy
  ring

/-- `I(A ; B) = H(A) - H(A | B)`. -/
theorem mutualInfo_eq_sub_condEntropy (P : PMF (α × β)) :
    mutualInfo P = entropyBits (P.map Prod.fst) - condEntropy P := by
  unfold mutualInfo condEntropy
  ring

/-- `H(A | B) ≥ 0` on finite types. -/
theorem condEntropy_nonneg [Fintype α] [Fintype β] (P : PMF (α × β)) : 0 ≤ condEntropy P := by
  unfold condEntropy
  have h := entropyBits_map_le P Prod.snd
  linarith

/-- `H(A, B) ≥ H(A)` on finite types. -/
theorem entropyBits_fst_le [Fintype α] [Fintype β] (P : PMF (α × β)) :
    entropyBits (P.map Prod.fst) ≤ entropyBits P :=
  entropyBits_map_le P Prod.fst

/-- `I(A ; B) ≤ H(A)` on finite types. -/
theorem mutualInfo_le_left [Fintype α] [Fintype β] (P : PMF (α × β)) :
    mutualInfo P ≤ entropyBits (P.map Prod.fst) := by
  rw [mutualInfo_eq_sub_condEntropy]
  have h := condEntropy_nonneg P
  linarith

/-- `I(A ; B) ≤ H(B)` on finite types. -/
theorem mutualInfo_le_right [Fintype α] [Fintype β] (P : PMF (α × β)) :
    mutualInfo P ≤ entropyBits (P.map Prod.snd) := by
  unfold mutualInfo
  have h := entropyBits_fst_le P
  linarith

/-- Swapping the pair does not change the joint entropy. -/
theorem entropyBits_map_swap (P : PMF (α × β)) : entropyBits (P.map Prod.swap) = entropyBits P :=
  entropyBits_map_of_injective P Prod.swap_injective

/-- `I(B ; A) = I(A ; B)`. -/
theorem mutualInfo_swap (P : PMF (α × β)) : mutualInfo (P.map Prod.swap) = mutualInfo P := by
  have h1 : (P.map Prod.swap).map Prod.fst = P.map Prod.snd := by
    rw [PMF.map_comp]
    try rfl
  have h2 : (P.map Prod.swap).map Prod.snd = P.map Prod.fst := by
    rw [PMF.map_comp]
    try rfl
  unfold mutualInfo
  rw [h1, h2, entropyBits_map_swap]
  ring

/-! ## Subadditivity (roadmap item B2b) -/

/-- Cross-entropy form of Gibbs: `-p log p ≤ -p log q + (q - p)` when `q > 0` wherever `p > 0`. -/
theorem neg_mul_log_le_cross {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    -p * Real.log p ≤ -p * Real.log q + (q - p) := by
  rcases hp.eq_or_lt with h | h
  · rw [← h]
    simpa using hq
  · have hq' := hpq h
    have hp0 : p ≠ 0 := h.ne'
    have key := Real.log_le_sub_one_of_pos (div_pos hq' h)
    rw [Real.log_div hq'.ne' hp0] at key
    have e : p * (q / p - 1) = q - p := by
      first
      | (field_simp; done)
      | (field_simp; ring)
    have k2 := mul_le_mul_of_nonneg_left key h.le
    rw [e] at k2
    have e2 : -p * Real.log p = p * (Real.log q - Real.log p) - p * Real.log q := by ring
    rw [e2]
    linarith

/-- A mass is at most the mass of its image: `P(x) ≤ (f_* P)(f x)`. -/
theorem pmf_toReal_le_map {γ δ : Type*} [Fintype γ] (P : PMF γ) (f : γ → δ) (x : γ) :
    (P x).toReal ≤ ((P.map f) (f x)).toReal := by
  classical
  rw [pmf_map_toReal P f (f x)]
  exact Finset.single_le_sum (f := fun a => (P a).toReal) (fun a _ => ENNReal.toReal_nonneg)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩)

/-- `∑ₐ P(a) g(f a) = ∑_b (f_* P)(b) g(b)`. -/
theorem sum_toReal_mul_comp {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq δ] (P : PMF γ)
    (f : γ → δ) (g : δ → ℝ) :
    ∑ a, (P a).toReal * g (f a) = ∑ b, ((P.map f) b).toReal * g b := by
  calc ∑ a, (P a).toReal * g (f a)
      = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), (P a).toReal * g (f a) :=
        (Finset.sum_fiberwise Finset.univ f _).symm
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), (P a).toReal * g b := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
        rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ b, ((P.map f) b).toReal * g b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [pmf_map_toReal P f b, Finset.sum_mul]

/-- Entropy in bits is entropy in nats divided by `log 2`. -/
theorem entropyBits_eq_div_log {γ : Type*} [Fintype γ] (P : PMF γ) :
    entropyBits P = (∑ a, -(P a).toReal * Real.log (P a).toReal) / Real.log 2 := by
  rw [entropyBits_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Real.log_div_log]
  ring

/-- Subadditivity in nats. -/
theorem entropyNats_subadditive [Fintype α] [Fintype β] (P : PMF (α × β)) :
    ∑ x, -(P x).toReal * Real.log (P x).toReal ≤
      ∑ a, -((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal +
      ∑ b, -((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal := by
  classical
  have hpt : ∀ x : α × β, -(P x).toReal * Real.log (P x).toReal ≤
      -((P x).toReal * Real.log ((P.map Prod.fst) x.1).toReal +
        (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal) +
      (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal - (P x).toReal) := by
    intro x
    have hA := pmf_toReal_le_map P Prod.fst x
    have hB := pmf_toReal_le_map P Prod.snd x
    have h0 : 0 ≤ (P x).toReal := ENNReal.toReal_nonneg
    have hg := neg_mul_log_le_cross h0
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun hp => mul_pos (lt_of_lt_of_le hp hA) (lt_of_lt_of_le hp hB))
    have hsplit : (P x).toReal * Real.log
          (((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal) =
        (P x).toReal * Real.log ((P.map Prod.fst) x.1).toReal +
          (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal := by
      rcases h0.eq_or_lt with hz | hpos
      · rw [← hz]
        ring
      · rw [Real.log_mul (lt_of_lt_of_le hpos hA).ne' (lt_of_lt_of_le hpos hB).ne']
        ring
    linarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hpt x
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_sub_distrib] at hsum
  have S1 : ∑ x : α × β, (P x).toReal * Real.log ((P.map Prod.fst) x.1).toReal =
      ∑ a, ((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal :=
    sum_toReal_mul_comp P Prod.fst (fun a => Real.log ((P.map Prod.fst) a).toReal)
  have S2 : ∑ x : α × β, (P x).toReal * Real.log ((P.map Prod.snd) x.2).toReal =
      ∑ b, ((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal :=
    sum_toReal_mul_comp P Prod.snd (fun b => Real.log ((P.map Prod.snd) b).toReal)
  have S3 : ∑ x : α × β, ((P.map Prod.fst) x.1).toReal * ((P.map Prod.snd) x.2).toReal = 1 := by
    first
    | (simp only [Fintype.sum_prod_type, ← Finset.mul_sum, pmf_sum_toReal, mul_one]; done)
    | (rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum, pmf_sum_toReal, mul_one]; done)
    | (simp [Fintype.sum_prod_type, ← Finset.mul_sum, pmf_sum_toReal])
  have S4 := pmf_sum_toReal P
  have N1 : ∑ a, -((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal =
      -∑ a, ((P.map Prod.fst) a).toReal * Real.log ((P.map Prod.fst) a).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have N2 : ∑ b, -((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal =
      -∑ b, ((P.map Prod.snd) b).toReal * Real.log ((P.map Prod.snd) b).toReal := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  linarith

/-- Subadditivity: `H(A, B) ≤ H(A) + H(B)` on finite types. -/
theorem entropyBits_subadditive [Fintype α] [Fintype β] (P : PMF (α × β)) :
    entropyBits P ≤ entropyBits (P.map Prod.fst) + entropyBits (P.map Prod.snd) := by
  rw [entropyBits_eq_div_log P, entropyBits_eq_div_log (P.map Prod.fst),
    entropyBits_eq_div_log (P.map Prod.snd), ← add_div]
  exact div_le_div_of_nonneg_right (entropyNats_subadditive P) (Real.log_pos (by norm_num)).le

/-- `I(A ; B) ≥ 0` on finite types. -/
theorem mutualInfo_nonneg [Fintype α] [Fintype β] (P : PMF (α × β)) : 0 ≤ mutualInfo P := by
  unfold mutualInfo
  linarith [entropyBits_subadditive P]

/-- Conditioning does not increase entropy: `H(A | B) ≤ H(A)` on finite types. -/
theorem condEntropy_le [Fintype α] [Fintype β] (P : PMF (α × β)) :
    condEntropy P ≤ entropyBits (P.map Prod.fst) := by
  unfold condEntropy
  linarith [entropyBits_subadditive P]

end EntropyLean
