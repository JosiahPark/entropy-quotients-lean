import EntropyLean.SparsePosterior
import EntropyLean.RatioGrowth
import EntropyLean.Statements
open EntropyLean

/-! Scratch sanity checks (not part of the repo).
1. `MartonInput` is not self-contradictory: it holds on the zero space.
2. The conditional chain really composes: from `RatioGrowth.{0}` one gets the paper's
   Theorem 1.1 statement on a concrete space `F2Vec 3`.
3. Universe check: the same conclusion for a `Type 1` space needs `RatioGrowth.{1}`, which the
   planned D9 (posterior families need `V : Type`) does not provide. -/

/-- Every law on a one-point type has entropy `0`. -/
theorem entropy_zero_of_card_one {α : Type*} [Fintype α] (h : Fintype.card α = 1) (P : PMF α) :
    entropyBits P = 0 := by
  have h1 := entropyBits_le_log_card P
  rw [h] at h1
  simp at h1
  exact le_antisymm h1 (entropyBits_nonneg P)

example : MartonInput (F2Vec 0) := by
  refine ⟨fun K => ⟨⊥, ?_⟩⟩
  have hc : Fintype.card (F2Vec 0) = 1 := by simp [F2Vec]
  unfold ruzsaDist entropyIncrement
  rw [entropy_zero_of_card_one hc, entropy_zero_of_card_one hc K,
    entropy_zero_of_card_one hc (uniformSub ⊥), entropy_zero_of_card_one hc (conv K K)]
  norm_num

example (hg : RatioGrowth.{0}) (ε : ℝ) (hε : 0 < ε) (X : PMF (F2Vec 3)) :
    ∃ G : Submodule (ZMod 2) (F2Vec 3),
      (Module.finrank (ZMod 2) G : ℝ) ≤ (2 : ℝ) ^ (320 * (1 + ε) / ε) * entropyBits X ∧
      entropyBits (X.map fun v => G.mkQ v) ≤ (1 + ε) * entropyIncrement (X.map fun v => G.mkQ v) ∧
      entropyIncrement (X.map fun v => G.mkQ v) ≤ entropyIncrement X :=
  exponential_entropy_quotient_of_growth hg ε hε X

-- Universe check: this is what one gets for a `Type 1` carrier; note the hypothesis universe.
#check @exponential_entropy_quotient_of_growth.{1}
-- and posterior families exist only over `V : Type`:
#check @WeightedFamily.posterior
