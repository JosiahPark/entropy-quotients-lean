import Mathlib
import EntropyLean.UniverseTransport
import EntropyLean.ConstantSlack

/-!
# Corollary 9.4: subspace-coset concentration (roadmap item F1)

Corollary 9.4 of arXiv:2610.38525: let `0 < α < η ≤ 1` and let `A ⊆ F₂^m` be nonempty with
`|A + A| ≤ |A|^(2−η)`. Then there is a subspace `G` with `dim G ≤ 2^(320/α) log₂|A|` and

  `(1/|A|) ∑_{a ∈ A} log₂ |A ∩ (a + G)| ≥ ((η − α)/(1 − α)) log₂ |A|`,

so some coset of `G` meets `A` in at least `|A|^(η−α)` points. The coset count `|A ∩ (a + G)|` is
written `(A.filter fun b => b - a ∈ G).card`.

Proved here, for a finite `F₂`-space `V`:

* `uniformFinset A hA`: the uniform law on a nonempty finset, with `H = log₂ |A|`
  (`entropyBits_uniformFinset`);
* `entropyBits_le_logb_card_of_support`: a law vanishing outside a finset `S` has `H ≤ log₂ |S|`;
* `entropyIncrement_uniformFinset_le`: `D(X) ≤ (1 − η) log₂ |A|` for `X` uniform on `A` when
  `|A + A| ≤ |A|^(2−η)`;
* `entropyBits_uniformFinset_quotient`:
  `H(q_G X) = log₂ |A| − (1/|A|) ∑_{a ∈ A} log₂ |A ∩ (a + G)|`;
* `coset_concentration_of_quotient`: Corollary 9.4 with the conclusion of Theorem 1.1 (constant
  `K` in place of 320) as the explicit hypothesis `hT`, and dimension bound `2^(K/α) log₂ |A|`;
* `exists_large_coset_of_quotient`: the "in particular" part;
* `coset_concentration_of_marton`, `exists_large_coset_of_marton`: both parts with the paper's
  constant 320 and the entropic Marton bound (35) on spaces in `Type` (`MartonBound.{0}`) as the
  only hypothesis; `coset_concentration_311_of_marton` is the same with 311 (item G3).

What this file does NOT prove: Corollary 9.4 unconditionally. Theorem 1.1 enters as the
hypothesis `hT`, or through the entropic Marton bound (35), which is not proved in this
repository.
-/

universe u

namespace EntropyLean

open scoped BigOperators Pointwise ENNReal

section UniformFinset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The elements of a finite type that lie in a finset `A` are the elements of `A`. -/
theorem filter_univ_mem_eq (A : Finset V) : (Finset.univ.filter fun v => v ∈ A) = A := by
  ext v
  simp

/-- The uniform law on a nonempty finset `A`. -/
noncomputable def uniformFinset (A : Finset V) (hA : A.Nonempty) : PMF V :=
  PMF.ofFintype (fun v => if v ∈ A then (A.card : ℝ≥0∞)⁻¹ else 0) (by
    rw [← Finset.sum_filter, filter_univ_mem_eq, Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hA.card_pos.ne') (ENNReal.natCast_ne_top _))

theorem uniformFinset_apply_of_not_mem (A : Finset V) (hA : A.Nonempty) {v : V} (hv : v ∉ A) :
    uniformFinset A hA v = 0 := by
  unfold uniformFinset
  rw [PMF.ofFintype_apply, if_neg hv]

theorem uniformFinset_toReal (A : Finset V) (hA : A.Nonempty) (v : V) :
    (uniformFinset A hA v).toReal = if v ∈ A then (A.card : ℝ)⁻¹ else 0 := by
  unfold uniformFinset
  rw [PMF.ofFintype_apply]
  split_ifs
  · simp [ENNReal.toReal_inv]
  · simp

/-- `H(X) = log₂ |A|` for `X` uniform on `A`. -/
theorem entropyBits_uniformFinset (A : Finset V) (hA : A.Nonempty) :
    entropyBits (uniformFinset A hA) = Real.logb 2 (A.card : ℝ) := by
  rw [entropyBits_eq_sum]
  have hN : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hterm : ∀ v, -(uniformFinset A hA v).toReal * Real.logb 2 (uniformFinset A hA v).toReal =
      if v ∈ A then (A.card : ℝ)⁻¹ * Real.logb 2 (A.card : ℝ) else 0 := by
    intro v
    rw [uniformFinset_toReal]
    split_ifs
    · rw [Real.logb_inv]
      ring
    · simp
  rw [Finset.sum_congr rfl fun v _ => hterm v]
  rw [← Finset.sum_filter, filter_univ_mem_eq, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hN.ne', one_mul]

end UniformFinset

/-- A law on a finite type that vanishes outside a finset `S` has entropy at most
`log₂ |S|`. -/
theorem entropyBits_le_logb_card_of_support {α : Type*} [Fintype α] (P : PMF α) (S : Finset α)
    (hS : ∀ a, a ∉ S → P a = 0) : entropyBits P ≤ Real.logb 2 (S.card : ℝ) := by
  obtain ⟨a0, ha0⟩ := P.support_nonempty
  have ha0S : a0 ∈ S := by
    by_contra h
    exact (P.mem_support_iff a0).mp ha0 (hS a0 h)
  have hn : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a0, ha0S⟩)
  have hzero : ∀ a, a ∉ S → (P a).toReal = 0 := fun a ha => by simp [hS a ha]
  have hsumS : ∑ a ∈ S, (P a).toReal = 1 :=
    (Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hzero a ha)).trans
      (pmf_sum_toReal P)
  have hEsum : ∑ a ∈ S, -(P a).toReal * Real.log (P a).toReal =
      ∑ a, -(P a).toReal * Real.log (P a).toReal :=
    Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => by rw [hzero a ha]; simp)
  have hS' : ∑ a, -(P a).toReal * Real.log (P a).toReal ≤ Real.log (S.card : ℝ) := by
    rw [← hEsum]
    calc ∑ a ∈ S, -(P a).toReal * Real.log (P a).toReal
        ≤ ∑ a ∈ S, ((P a).toReal * Real.log (S.card : ℝ)
            + (1 / (S.card : ℝ) - (P a).toReal)) :=
          Finset.sum_le_sum fun a _ => neg_mul_log_le_gibbs ENNReal.toReal_nonneg hn
      _ = (∑ a ∈ S, (P a).toReal) * Real.log (S.card : ℝ)
            + ((S.card : ℝ) * (1 / (S.card : ℝ)) - ∑ a ∈ S, (P a).toReal) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const,
            nsmul_eq_mul]
      _ = Real.log (S.card : ℝ) := by
          rw [hsumS, mul_one_div_cancel hn.ne', one_mul, sub_self, add_zero]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : ∑ a, -(P a).toReal * Real.logb 2 (P a).toReal =
      (∑ a, -(P a).toReal * Real.log (P a).toReal) / Real.log 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Real.log_div_log]
    ring
  rw [entropyBits_eq_sum, e, ← Real.log_div_log]
  exact div_le_div_of_nonneg_right hS' hl.le

section Concentration

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

omit [Module (ZMod 2) V] in
/-- The law of `X + X'` for `X`, `X'` independent and uniform on `A` vanishes outside
`A + A`. -/
theorem conv_uniformFinset_eq_zero (A : Finset V) (hA : A.Nonempty) {t : V} (ht : t ∉ A + A) :
    conv (uniformFinset A hA) (uniformFinset A hA) t = 0 := by
  rw [conv_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases ha : a ∈ A
  · have hta : t - a ∉ A := by
      intro h
      apply ht
      have h2 := Finset.add_mem_add ha h
      have e : a + (t - a) = t := by abel
      rw [e] at h2
      exact h2
    rw [uniformFinset_apply_of_not_mem A hA hta, mul_zero]
  · rw [uniformFinset_apply_of_not_mem A hA ha, zero_mul]

/-- `D(X) ≤ (1 − η) log₂ |A|` for `X` uniform on `A` with `|A + A| ≤ |A|^(2−η)`. -/
theorem entropyIncrement_uniformFinset_le (A : Finset V) (hA : A.Nonempty) {η : ℝ}
    (hAA : ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - η)) :
    entropyIncrement (uniformFinset A hA) ≤ (1 - η) * Real.logb 2 (A.card : ℝ) := by
  have hN : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hAApos : (0 : ℝ) < ((A + A).card : ℝ) := by exact_mod_cast (hA.add hA).card_pos
  have h1 : entropyBits (conv (uniformFinset A hA) (uniformFinset A hA)) ≤
      Real.logb 2 ((A + A).card : ℝ) :=
    entropyBits_le_logb_card_of_support _ (A + A)
      (fun t ht => conv_uniformFinset_eq_zero A hA ht)
  have h2 : Real.logb 2 ((A + A).card : ℝ) ≤ (2 - η) * Real.logb 2 (A.card : ℝ) := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hAApos hAA
    rwa [Real.logb_rpow_eq_mul_logb_of_pos hN] at h
  unfold entropyIncrement
  rw [entropyBits_uniformFinset]
  linarith

open Classical in
/-- Number of points of `A` in the coset `c ∈ V ⧸ G`. -/
noncomputable def fibreCount (A : Finset V) (G : Submodule (ZMod 2) V) (c : V ⧸ G) : ℕ :=
  (A.filter fun b => G.mkQ b = c).card

omit [Fintype V] [DecidableEq V] in
open Classical in
/-- The coset of `a` contains `|{b ∈ A : b − a ∈ G}|` points of `A`. -/
theorem fibreCount_mkQ (A : Finset V) (G : Submodule (ZMod 2) V) (a : V) :
    fibreCount A G (G.mkQ a) = (A.filter fun b => b - a ∈ G).card := by
  unfold fibreCount
  congr 1
  refine Finset.filter_congr fun b _ => ?_
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

open Classical in
/-- The quotient of the uniform law on `A` gives mass `|A ∩ c| / |A|` to the coset `c`. -/
theorem uniformFinset_map_mkQ_toReal (A : Finset V) (hA : A.Nonempty)
    (G : Submodule (ZMod 2) V) (c : V ⧸ G) :
    (((uniformFinset A hA).map fun v => G.mkQ v) c).toReal =
      (fibreCount A G c : ℝ) / (A.card : ℝ) := by
  rw [pmf_map_toReal]
  simp only [uniformFinset_toReal]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 1
  norm_cast
  unfold fibreCount
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

open Classical in
/-- `H(q_G X) = log₂ |A| − (1/|A|) ∑_{a ∈ A} log₂ |A ∩ (a + G)|` for `X` uniform on `A`. -/
theorem entropyBits_uniformFinset_quotient (A : Finset V) (hA : A.Nonempty)
    (G : Submodule (ZMod 2) V) :
    entropyBits ((uniformFinset A hA).map fun v => G.mkQ v) =
      Real.logb 2 (A.card : ℝ) -
        1 / (A.card : ℝ) * ∑ a ∈ A, Real.logb 2 ((A.filter fun b => b - a ∈ G).card : ℝ) := by
  haveI : Finite (V ⧸ G) := Finite.of_surjective _ (Submodule.mkQ_surjective G)
  letI : Fintype (V ⧸ G) := Fintype.ofFinite _
  have hN : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  rw [entropyBits_eq_sum]
  have hterm : ∀ c : V ⧸ G,
      -(((uniformFinset A hA).map fun v => G.mkQ v) c).toReal *
          Real.logb 2 (((uniformFinset A hA).map fun v => G.mkQ v) c).toReal =
        (fibreCount A G c : ℝ) / (A.card : ℝ) * Real.logb 2 (A.card : ℝ) -
          1 / (A.card : ℝ) * ((fibreCount A G c : ℝ) * Real.logb 2 (fibreCount A G c : ℝ)) := by
    intro c
    rw [uniformFinset_map_mkQ_toReal]
    rcases Nat.eq_zero_or_pos (fibreCount A G c) with h0 | hpos
    · rw [h0]
      simp
    · have hmc : (0 : ℝ) < (fibreCount A G c : ℝ) := Nat.cast_pos.mpr hpos
      rw [Real.logb_div hmc.ne' hN.ne']
      ring
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]
  have hcount : ∑ c : V ⧸ G, (fibreCount A G c : ℝ) = (A.card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun b : V => G.mkQ b) (s := A)
      (t := Finset.univ) (by intro x _; simp)
    unfold fibreCount
    exact_mod_cast h.symm
  have h1 : ∑ c : V ⧸ G, (fibreCount A G c : ℝ) / (A.card : ℝ) = 1 := by
    rw [← Finset.sum_div, hcount, div_self hN.ne']
  have h2 : ∑ c : V ⧸ G, (fibreCount A G c : ℝ) * Real.logb 2 (fibreCount A G c : ℝ) =
      ∑ a ∈ A, Real.logb 2 (fibreCount A G (G.mkQ a) : ℝ) := by
    rw [← Finset.sum_fiberwise A (fun b : V => G.mkQ b)
      (fun a => Real.logb 2 (fibreCount A G (G.mkQ a) : ℝ))]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hc : ∀ a ∈ A.filter (fun b : V => G.mkQ b = c),
        Real.logb 2 (fibreCount A G (G.mkQ a) : ℝ) = Real.logb 2 (fibreCount A G c : ℝ) := by
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [h1, h2, one_mul]
  simp only [fibreCount_mkQ]

open Classical in
/-- **Corollary 9.4** from the conclusion of Theorem 1.1 with constant `K` (hypothesis `hT`):
for `0 < α < η ≤ 1` and nonempty `A` with `|A + A| ≤ |A|^(2−η)` there is a subspace `G` with
`dim G ≤ 2^(K/α) log₂ |A|` and
`(1/|A|) ∑_{a ∈ A} log₂ |A ∩ (a + G)| ≥ ((η − α)/(1 − α)) log₂ |A|`. -/
theorem coset_concentration_of_quotient {K : ℝ}
    (hT : ∀ ε : ℝ, 0 < ε → ∀ X : PMF V, ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (K * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X)
    {α η : ℝ} (hα : 0 < α) (hαη : α < η) (hη : η ≤ 1) (A : Finset V) (hA : A.Nonempty)
    (hAA : ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - η)) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (K / α) * Real.logb 2 (A.card : ℝ) ∧
      (η - α) / (1 - α) * Real.logb 2 (A.card : ℝ) ≤
        1 / (A.card : ℝ) * ∑ a ∈ A, Real.logb 2 ((A.filter fun b => b - a ∈ G).card : ℝ) := by
  have h1α : 0 < 1 - α := by linarith
  have h1α' : 1 - α ≠ 0 := h1α.ne'
  have hα' : α ≠ 0 := hα.ne'
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = α / (1 - α) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hε_def]
    exact div_pos hα h1α
  have h1ε : 1 + ε = 1 / (1 - α) := by
    rw [hε_def, eq_div_iff h1α', add_mul, div_mul_cancel₀ _ h1α']
    ring
  have hexp : K * (1 + ε) / ε = K / α := by
    rw [h1ε, hε_def, mul_one_div, div_div_div_cancel_right₀ h1α']
  obtain ⟨G, hdim, hH, hD⟩ := hT ε hε (uniformFinset A hA)
  rw [entropyBits_uniformFinset, hexp] at hdim
  refine ⟨G, hdim, ?_⟩
  have h1ε0 : 0 ≤ 1 + ε := by linarith
  have hDX := entropyIncrement_uniformFinset_le A hA hAA
  have hHq : entropyBits ((uniformFinset A hA).map fun v => G.mkQ v) ≤
      (1 - η) / (1 - α) * Real.logb 2 (A.card : ℝ) := by
    calc entropyBits ((uniformFinset A hA).map fun v => G.mkQ v)
        ≤ (1 + ε) * entropyIncrement ((uniformFinset A hA).map fun v => G.mkQ v) := hH
      _ ≤ (1 + ε) * entropyIncrement (uniformFinset A hA) :=
          mul_le_mul_of_nonneg_left hD h1ε0
      _ ≤ (1 + ε) * ((1 - η) * Real.logb 2 (A.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hDX h1ε0
      _ = (1 - η) / (1 - α) * Real.logb 2 (A.card : ℝ) := by
          rw [h1ε]
          ring
  rw [entropyBits_uniformFinset_quotient] at hHq
  have efrac : (η - α) / (1 - α) = 1 - (1 - η) / (1 - α) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1α']
    ring
  have e : (η - α) / (1 - α) * Real.logb 2 (A.card : ℝ) =
      Real.logb 2 (A.card : ℝ) - (1 - η) / (1 - α) * Real.logb 2 (A.card : ℝ) := by
    rw [efrac]
    ring
  rw [e]
  linarith

open Classical in
/-- **Corollary 9.4, last assertion**: under the same hypotheses, some coset of `G` meets `A` in
at least `|A|^(η−α)` points. -/
theorem exists_large_coset_of_quotient {K : ℝ}
    (hT : ∀ ε : ℝ, 0 < ε → ∀ X : PMF V, ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (K * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤
        (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X)
    {α η : ℝ} (hα : 0 < α) (hαη : α < η) (hη : η ≤ 1) (A : Finset V) (hA : A.Nonempty)
    (hAA : ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - η)) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (K / α) * Real.logb 2 (A.card : ℝ) ∧
      ∃ a ∈ A, (A.card : ℝ) ^ (η - α) ≤ ((A.filter fun b => b - a ∈ G).card : ℝ) := by
  obtain ⟨G, hdim, havg⟩ := coset_concentration_of_quotient hT hα hαη hη A hA hAA
  refine ⟨G, hdim, ?_⟩
  have hN : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hN1 : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hL : 0 ≤ Real.logb 2 (A.card : ℝ) := Real.logb_nonneg (by norm_num) hN1
  have h1α : 0 < 1 - α := by linarith
  have hfrac : η - α ≤ (η - α) / (1 - α) := by
    rw [le_div_iff₀ h1α]
    nlinarith
  have hlow : (η - α) * Real.logb 2 (A.card : ℝ) ≤
      1 / (A.card : ℝ) * ∑ a ∈ A, Real.logb 2 ((A.filter fun b => b - a ∈ G).card : ℝ) :=
    (mul_le_mul_of_nonneg_right hfrac hL).trans havg
  have hsum : ∑ _a ∈ A, (η - α) * Real.logb 2 (A.card : ℝ) ≤
      ∑ a ∈ A, Real.logb 2 ((A.filter fun b => b - a ∈ G).card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left hlow hN.le
    rw [← mul_assoc (A.card : ℝ) (1 / (A.card : ℝ)), mul_one_div_cancel hN.ne', one_mul] at h
    linarith
  obtain ⟨a, haA, ha⟩ := Finset.exists_le_of_sum_le hA hsum
  refine ⟨a, haA, ?_⟩
  have hmem : a ∈ A.filter fun b => b - a ∈ G :=
    Finset.mem_filter.mpr ⟨haA, by rw [sub_self]; exact G.zero_mem⟩
  have hn : (0 : ℝ) < ((A.filter fun b => b - a ∈ G).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨a, hmem⟩)
  refine (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (Real.rpow_pos_of_pos hN _) hn).mp ?_
  rw [Real.logb_rpow_eq_mul_logb_of_pos hN]
  exact ha

end Concentration

section Marton

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

open Classical in
/-- **Corollary 9.4** with the paper's constant 320, with the entropic Marton bound (35) on
spaces in `Type` as the only hypothesis. -/
theorem coset_concentration_of_marton (hM : MartonBound.{0}) {α η : ℝ} (hα : 0 < α)
    (hαη : α < η) (hη : η ≤ 1) (A : Finset V) (hA : A.Nonempty)
    (hAA : ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - η)) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ ((320 : ℝ) / α) * Real.logb 2 (A.card : ℝ) ∧
      (η - α) / (1 - α) * Real.logb 2 (A.card : ℝ) ≤
        1 / (A.card : ℝ) * ∑ a ∈ A, Real.logb 2 ((A.filter fun b => b - a ∈ G).card : ℝ) :=
  coset_concentration_of_quotient
    (fun ε hε X => exponential_entropy_quotient_of_marton hM ε hε X) hα hαη hη A hA hAA

open Classical in
/-- **Corollary 9.4, last assertion**, with the paper's constant 320 and the entropic Marton
bound (35) on spaces in `Type` as the only hypothesis. -/
theorem exists_large_coset_of_marton (hM : MartonBound.{0}) {α η : ℝ} (hα : 0 < α)
    (hαη : α < η) (hη : η ≤ 1) (A : Finset V) (hA : A.Nonempty)
    (hAA : ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - η)) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ ((320 : ℝ) / α) * Real.logb 2 (A.card : ℝ) ∧
      ∃ a ∈ A, (A.card : ℝ) ^ (η - α) ≤ ((A.filter fun b => b - a ∈ G).card : ℝ) :=
  exists_large_coset_of_quotient
    (fun ε hε X => exponential_entropy_quotient_of_marton hM ε hε X) hα hαη hη A hA hAA

open Classical in
/-- **Corollary 9.4 with 311 in place of 320** (item G3), with the entropic Marton bound (35)
on spaces in `Type` as the only hypothesis. -/
theorem coset_concentration_311_of_marton (hM : MartonBound.{0}) {α η : ℝ} (hα : 0 < α)
    (hαη : α < η) (hη : η ≤ 1) (A : Finset V) (hA : A.Nonempty)
    (hAA : ((A + A).card : ℝ) ≤ (A.card : ℝ) ^ (2 - η)) :
    ∃ G : Submodule (ZMod 2) V,
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ ((311 : ℝ) / α) * Real.logb 2 (A.card : ℝ) ∧
      (η - α) / (1 - α) * Real.logb 2 (A.card : ℝ) ≤
        1 / (A.card : ℝ) * ∑ a ∈ A, Real.logb 2 ((A.filter fun b => b - a ∈ G).card : ℝ) :=
  coset_concentration_of_quotient
    (fun ε hε X => exponential_entropy_quotient_311_of_marton hM ε hε X) hα hαη hη A hA hAA

end Marton

end EntropyLean
