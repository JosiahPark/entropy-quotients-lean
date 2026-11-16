import Mathlib
import EntropyLean.MartonConvEntropy
import EntropyLean.QuotientFacts
import EntropyLean.EntropyFacts

/-!
# Trivial cases of the entropic Marton bound (roadmap item H2, Section 7)

For a law `K` on a finite F₂-space `V`, the uniform-smoothing formula
`d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2` (`ruzsaDist_uniformSub`) specialises at the two
trivial subspaces:
* `W = ⊥`: `q_⊥` is injective, so `d(K, U_⊥) = H(K) / 2` (`ruzsaDist_uniformSub_bot`);
* `W = ⊤`: `q_⊤ K` is a point mass, so `d(K, U_⊤) = (dim V − H(K)) / 2`
  (`ruzsaDist_uniformSub_top`).

Hence (35) holds for `K` whenever `H(K) ≤ 12 D(K)` (`marton_of_entropy_le`, witness `⊥`) or
`dim V − H(K) ≤ 12 D(K)` (`marton_of_codim_le`, witness `⊤`).

What this file does NOT prove: the entropic Marton bound (35) in general (it remains the
hypothesis `MartonInput V` / `MartonBound` elsewhere), nor the zero-doubling and one-bit cases
(roadmap items H3, H4).
-/

namespace EntropyLean

section MartonPartial

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- `q_⊥` is injective, so `H(q_⊥ K) = H(K)`. -/
theorem entropyBits_map_mkQ_bot (K : PMF V) :
    entropyBits (K.map fun v => (⊥ : Submodule (ZMod 2) V).mkQ v) = entropyBits K := by
  apply entropyBits_map_of_injective
  intro a b h
  first
  | exact LinearMap.ker_eq_bot.mp (Submodule.ker_mkQ (⊥ : Submodule (ZMod 2) V)) h
  | exact sub_eq_zero.mp ((Submodule.mem_bot (ZMod 2)).mp ((Submodule.Quotient.eq _).mp h))
  | simpa [sub_eq_zero] using h

/-- `q_⊤ K` is a point mass, so `H(q_⊤ K) = 0`. -/
theorem entropyBits_map_mkQ_top (K : PMF V) :
    entropyBits (K.map fun v => (⊤ : Submodule (ZMod 2) V).mkQ v) = 0 := by
  have hc : (fun v : V => (⊤ : Submodule (ZMod 2) V).mkQ v) = Function.const V 0 := by
    funext v
    show (⊤ : Submodule (ZMod 2) V).mkQ v = 0
    first
    | (rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact Submodule.mem_top)
    | simp
  first
  | rw [hc, PMF.map_const, entropyBits_pure]
  | simp only [hc, PMF.map_const, entropyBits_pure]

/-- `d(K, U_⊥) = H(K) / 2`. -/
theorem ruzsaDist_uniformSub_bot (K : PMF V) :
    ruzsaDist K (uniformSub (⊥ : Submodule (ZMod 2) V)) = entropyBits K / 2 := by
  have h0 : (Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) : ℝ) = 0 := by simp
  rw [ruzsaDist_uniformSub, entropyBits_map_mkQ_bot, h0]
  ring

/-- `d(K, U_⊤) = (dim V − H(K)) / 2`. -/
theorem ruzsaDist_uniformSub_top (K : PMF V) :
    ruzsaDist K (uniformSub (⊤ : Submodule (ZMod 2) V)) =
      ((Module.finrank (ZMod 2) V : ℝ) - entropyBits K) / 2 := by
  have ht : (Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) : ℝ) =
      (Module.finrank (ZMod 2) V : ℝ) := by simp
  rw [ruzsaDist_uniformSub, entropyBits_map_mkQ_top, ht]
  ring

/-- (35) for laws of small entropy: if `H(K) ≤ 12 D(K)` then `d(K, U_⊥) ≤ 6 D(K)`. -/
theorem marton_of_entropy_le (K : PMF V) (h : entropyBits K ≤ 12 * entropyIncrement K) :
    ∃ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K :=
  ⟨⊥, by rw [ruzsaDist_uniformSub_bot]; linarith⟩

/-- (35) for laws of nearly full entropy: if `dim V − H(K) ≤ 12 D(K)` then
`d(K, U_⊤) ≤ 6 D(K)`. -/
theorem marton_of_codim_le (K : PMF V)
    (h : (Module.finrank (ZMod 2) V : ℝ) - entropyBits K ≤ 12 * entropyIncrement K) :
    ∃ W : Submodule (ZMod 2) V, ruzsaDist K (uniformSub W) ≤ 6 * entropyIncrement K :=
  ⟨⊤, by rw [ruzsaDist_uniformSub_top]; linarith⟩

end MartonPartial

end EntropyLean
