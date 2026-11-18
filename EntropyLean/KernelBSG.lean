import EntropyLean.MathlibForPFR
import EntropyLean.Posterior
import EntropyLean.ConditionalBSGLemma

/-!
# Lemma 6.2 conditioned on a third variable (roadmap item D6d1)

The proof of Lemma 6.3 applies Lemma 6.2 to `(A, C)` conditionally on `(S, T)` and averages.
This file proves that averaged form for a joint law given by a kernel. Let `R` be a law of
`((U, V), Y)` with `R((u, v), y) = c(y) K_y(u, v)`, so `c` is the law of `Y` and `K_y` the law of
`(U, V)` given `Y = y`. With `Z = U + V`:

* `sum_kernel_entropy_map`: for any map `g`,
  `∑_y c(y) H(g_* K_y) = H(g(·), Y) − H(Y)` (an average of conditional entropies);
* `kernel_conditional_bsg`: summing (33) for each `K_y` with weights `c(y)`,
  `∑_y c(y) ∑_z K_{y,Z}(z) d(Law(U | Z = z, Y = y), Law(V | Z = z, Y = y))
     ≤ 3 I(U ; V | Y) + 2 H(Z | Y) − H(U | Y) − H(V | Y)`,
  with every conditional quantity written through joint entropies of images of `R`;
* `kernelJoint_conditional_bsg`: the same for `R = kernelJoint c K`.

What this file does NOT prove: the conditional law of `(A, C)` given `S` at fixed laws, the
identification `Law(A | B = b, S = s, T) = Q_{I₁,I₃,b} * Q_{I₂,I₄,s+b}`, the averaging over index
tuples, or Lemma 6.3 (34) itself (roadmap items D6d2–D6d4).
-/

namespace EntropyLean

open scoped BigOperators

/-- If `R(a, t) = c(t) K_t(a)`, then `∑ₜ c(t) H(g_* K_t) = H(g(A), T) − H(T)`. -/
theorem sum_kernel_entropy_map {α β T : Type*} [Fintype α] [Fintype β] [Fintype T]
    (R : PMF (α × T)) (c : PMF T) (K : T → PMF α) (g : α → β)
    (h : ∀ a t, (R (a, t)).toReal = (c t).toReal * (K t a).toReal) :
    ∑ t, (c t).toReal * entropyBits ((K t).map g) =
      entropyBits (R.map fun x => (g x.1, x.2)) - entropyBits c := by
  classical
  have hk : entropyBits (R.map fun x => (g x.1, x.2)) =
      entropyBits c + ∑ t, (c t).toReal * entropyBits ((K t).map g) :=
    entropyBits_of_kernel _ c (fun t => (K t).map g) fun u t => kernel_masses_map R c K g h u t
  linarith

section KernelBSG

variable {V T : Type*} [Fintype V] [AddCommGroup V] [Module (ZMod 2) V] [Fintype T]

/-- **Lemma 6.2 conditioned on `Y`**: if `R((u, v), y) = c(y) K_y(u, v)`, then
`∑_y c(y) ∑_z K_{y,Z}(z) d(Law(U | z, y), Law(V | z, y)) ≤
3 I(U ; V | Y) + 2 H(Z | Y) − H(U | Y) − H(V | Y)`, where
`I(U ; V | Y) = H(U, Y) + H(V, Y) − H(U, V, Y) − H(Y)` and `H(X | Y) = H(X, Y) − H(Y)`. -/
theorem kernel_conditional_bsg (R : PMF ((V × V) × T)) (c : PMF T) (K : T → PMF (V × V))
    (h : ∀ p t, (R (p, t)).toReal = (c t).toReal * (K t p).toReal) :
    ∑ t, (c t).toReal *
        ∑ z, (sumLaw (K t) z).toReal * ruzsaDist (fibreLaw (K t) z) (fibreLawSnd (K t) z) ≤
      3 * (entropyBits (R.map fun x => (x.1.1, x.2)) + entropyBits (R.map fun x => (x.1.2, x.2)) -
          entropyBits R - entropyBits c) +
        2 * (entropyBits (R.map fun x => (x.1.1 + x.1.2, x.2)) - entropyBits c) -
        (entropyBits (R.map fun x => (x.1.1, x.2)) - entropyBits c) -
        (entropyBits (R.map fun x => (x.1.2, x.2)) - entropyBits c) := by
  classical
  have hU : ∑ t, (c t).toReal * entropyBits ((K t).map Prod.fst) =
      entropyBits (R.map fun x => (x.1.1, x.2)) - entropyBits c :=
    sum_kernel_entropy_map R c K Prod.fst h
  have hV : ∑ t, (c t).toReal * entropyBits ((K t).map Prod.snd) =
      entropyBits (R.map fun x => (x.1.2, x.2)) - entropyBits c :=
    sum_kernel_entropy_map R c K Prod.snd h
  have hZ : ∑ t, (c t).toReal * entropyBits (sumLaw (K t)) =
      entropyBits (R.map fun x => (x.1.1 + x.1.2, x.2)) - entropyBits c :=
    sum_kernel_entropy_map R c K (fun p : V × V => p.1 + p.2) h
  have hR : entropyBits R = entropyBits c + ∑ t, (c t).toReal * entropyBits (K t) :=
    entropyBits_of_kernel R c K h
  have hle : ∑ t, (c t).toReal *
        ∑ z, (sumLaw (K t) z).toReal * ruzsaDist (fibreLaw (K t) z) (fibreLawSnd (K t) z) ≤
      ∑ t, (c t).toReal * (3 * mutualInfo (K t) + 2 * entropyBits (sumLaw (K t)) -
        entropyBits ((K t).map Prod.fst) - entropyBits ((K t).map Prod.snd)) :=
    Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (conditional_bsg (K t)) ENNReal.toReal_nonneg
  have hpt : ∀ t, (c t).toReal * (3 * mutualInfo (K t) + 2 * entropyBits (sumLaw (K t)) -
        entropyBits ((K t).map Prod.fst) - entropyBits ((K t).map Prod.snd)) =
      2 * ((c t).toReal * entropyBits ((K t).map Prod.fst)) +
          2 * ((c t).toReal * entropyBits ((K t).map Prod.snd)) -
          3 * ((c t).toReal * entropyBits (K t)) +
        2 * ((c t).toReal * entropyBits (sumLaw (K t))) := by
    intro t
    unfold mutualInfo
    ring
  have hexp : ∑ t, (c t).toReal * (3 * mutualInfo (K t) + 2 * entropyBits (sumLaw (K t)) -
        entropyBits ((K t).map Prod.fst) - entropyBits ((K t).map Prod.snd)) =
      2 * ∑ t, (c t).toReal * entropyBits ((K t).map Prod.fst) +
          2 * ∑ t, (c t).toReal * entropyBits ((K t).map Prod.snd) -
          3 * ∑ t, (c t).toReal * entropyBits (K t) +
        2 * ∑ t, (c t).toReal * entropyBits (sumLaw (K t)) := by
    rw [Finset.sum_congr rfl fun t _ => hpt t, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [hexp] at hle
  linarith

/-- `kernel_conditional_bsg` for the kernel law `kernelJoint c K` of `((U, V), Y)`. -/
theorem kernelJoint_conditional_bsg (c : PMF T) (K : T → PMF (V × V)) :
    ∑ t, (c t).toReal *
        ∑ z, (sumLaw (K t) z).toReal * ruzsaDist (fibreLaw (K t) z) (fibreLawSnd (K t) z) ≤
      3 * (entropyBits ((kernelJoint c K).map fun x => (x.1.1, x.2)) +
          entropyBits ((kernelJoint c K).map fun x => (x.1.2, x.2)) -
          entropyBits (kernelJoint c K) - entropyBits c) +
        2 * (entropyBits ((kernelJoint c K).map fun x => (x.1.1 + x.1.2, x.2)) - entropyBits c) -
        (entropyBits ((kernelJoint c K).map fun x => (x.1.1, x.2)) - entropyBits c) -
        (entropyBits ((kernelJoint c K).map fun x => (x.1.2, x.2)) - entropyBits c) :=
  kernel_conditional_bsg (kernelJoint c K) c K (kernelJoint_toReal c K)

end KernelBSG

end EntropyLean
