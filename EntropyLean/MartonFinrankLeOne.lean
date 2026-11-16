import Mathlib
import EntropyLean.MartonOneBit
import EntropyLean.MartonBernoulliIneq

/-!
# The entropic Marton bound on spaces of dimension at most one (roadmap item H4c)

Proved here:
* `martonInput_of_finrank_le_one`: the entropic Marton bound (35), `MartonInput V`, holds on every
  finite F₂-space `V` with `dim V ≤ 1`. Dimension `0` is `martonInput_of_finrank_eq_zero`;
  dimension `1` is `martonInput_of_finrank_eq_one_of_bernoulli` (item H4a) with its Bernoulli
  hypothesis discharged by `bernoulli_marton_ineq` (item H4b);
* `martonInput_zmod2`: in particular (35) holds on `ZMod 2`.

What this file does NOT prove: the entropic Marton bound (35) in any dimension `≥ 2`, and hence
not `MartonBound`; Theorems 1.1, 1.2 and 8.2 still take (35) as a hypothesis.
-/

namespace EntropyLean

/-- **H4c.** The entropic Marton bound (35) on every finite F₂-space of dimension at most one. -/
theorem martonInput_of_finrank_le_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (h : Module.finrank (ZMod 2) V ≤ 1) : MartonInput V := by
  have h01 : Module.finrank (ZMod 2) V = 0 ∨ Module.finrank (ZMod 2) V = 1 := by omega
  rcases h01 with h0 | h1
  · exact martonInput_of_finrank_eq_zero h0
  · exact martonInput_of_finrank_eq_one_of_bernoulli h1
      (fun p hp0 hp1 => bernoulli_marton_ineq hp0 hp1)

/-- The entropic Marton bound (35) on `ZMod 2`. -/
theorem martonInput_zmod2 : MartonInput (ZMod 2) :=
  martonInput_of_finrank_le_one (Module.finrank_self (ZMod 2)).le

end EntropyLean
