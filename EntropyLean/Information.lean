import Mathlib
import EntropyLean.EntropyFacts
import EntropyLean.QuotientFacts

/-!
# Conditional entropy and mutual information (roadmap item B2a)

For a joint law `P` of a pair `(A, B)` (a `PMF (α × β)`): the conditional entropy
`H(A | B) = H(A, B) - H(B)` (`condEntropy`), the mutual information
`I(A ; B) = H(A) + H(B) - H(A, B)` (`mutualInfo`), the chain rule
`H(A, B) = H(B) + H(A | B)` (`entropyBits_chain`), `H(A | B) ≥ 0` on finite types
(`condEntropy_nonneg`), the bounds `I(A ; B) ≤ H(A)`, `I(A ; B) ≤ H(B)`
(`mutualInfo_le_left`, `mutualInfo_le_right`), and symmetry of `I` under swapping the pair
(`mutualInfo_swap`).

What this file does NOT prove: `I(A ; B) ≥ 0` (subadditivity `H(A, B) ≤ H(A) + H(B)`, item B2b),
conditional mutual information or `I(A ; B | C) ≥ 0` (item B2c). The definitions take the joint
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

end EntropyLean
