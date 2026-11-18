import EntropyLean.MathlibForPFR
import EntropyLean.MartonSmoothing
import EntropyLean.Posterior

/-!
# Smoothing a law by the uniform law on a subspace: masses (roadmap item D7b2a, Section 7)

For a law `K` on a finite F₂-space `V` and a subspace `W`, the law `K * U_W` of `A + U`
(`A ∼ K`, `U` uniform on `W`, independent) is constant on each coset of `W`:
`(K * U_W)(v) = (q_W K)(q_W v) / |W|`.

This file proves
* `conv_uniformSub_toReal`: `(K * U_W)(v) = (q_W K)(q_W v) / |W|`;
* `card_mkQ_fibre`: every fibre of `q_W : V → V ⧸ W` has `|W|` points;
* `sum_comp_mkQ`: `∑_v g(q_W v) = |W| ∑_x g(x)` for `g` on `V ⧸ W`.

What this file does NOT prove: the entropy identity `H(K * U_W) = H(q_W K) + dim W`, the formula
`d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2` (roadmap item D7b2b), the lower bound
`|dim W − H(K)| / 2 ≤ d(K, U_W)` (D7c), nor the entropic Marton bound (35), which stays a
hypothesis.
-/

namespace EntropyLean

section UniformConv

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- `v − a ∈ W` iff `a` and `v` lie in the same coset of `W`. -/
theorem sub_mem_iff_mkQ_eq (W : Submodule (ZMod 2) V) (a v : V) :
    v - a ∈ W ↔ W.mkQ a = W.mkQ v := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  constructor
  · intro h
    simpa using W.neg_mem h
  · intro h
    simpa using W.neg_mem h

open Classical in
/-- The masses of the smoothed law: `(K * U_W)(v) = (q_W K)(q_W v) / |W|`. -/
theorem conv_uniformSub_toReal (K : PMF V) (W : Submodule (ZMod 2) V) (v : V) :
    (conv K (uniformSub W) v).toReal =
      ((K.map fun x => W.mkQ x) (W.mkQ v)).toReal / (subCard W : ℝ) := by
  rw [conv_toReal_eq_sum, pmf_map_toReal]
  simp only [uniformSub_toReal]
  rw [Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : v - a ∈ W
  · rw [if_pos h, if_pos ((sub_mem_iff_mkQ_eq W a v).mp h), div_eq_mul_inv]
  · rw [if_neg h, if_neg fun h' => h ((sub_mem_iff_mkQ_eq W a v).mpr h'), mul_zero]

/-- Every fibre of `q_W` has `|W|` points. -/
theorem card_mkQ_fibre (W : Submodule (ZMod 2) V) [DecidableEq (V ⧸ W)] (x : V ⧸ W) :
    (Finset.univ.filter fun v : V => W.mkQ v = x).card = subCard W := by
  obtain ⟨v₀, rfl⟩ := Submodule.mkQ_surjective W x
  unfold subCard
  refine Finset.card_nbij' (fun v => v - v₀) (fun w => w + v₀) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hv
    exact hv
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    simpa using hw
  · intro v _
    simp
  · intro w _
    simp

/-- Summing a function of the coset over `V`: `∑_v g(q_W v) = |W| ∑_x g(x)`. -/
theorem sum_comp_mkQ (W : Submodule (ZMod 2) V) [Fintype (V ⧸ W)] [DecidableEq (V ⧸ W)]
    (g : V ⧸ W → ℝ) :
    ∑ v, g (W.mkQ v) = (subCard W : ℝ) * ∑ x, g x := by
  rw [← Finset.sum_fiberwise Finset.univ (fun v => W.mkQ v) (fun v => g (W.mkQ v)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ v ∈ Finset.univ.filter (fun v : V => W.mkQ v = x), g (W.mkQ v) = g x := by
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_mkQ_fibre, nsmul_eq_mul]

end UniformConv

end EntropyLean
