# Roadmap

Ordered work list for formalizing arXiv:2610.38525. Items are sized for one change each
(roughly under 120 new Lean lines) and name their file and theorem names. Take the first
unchecked item; tick it (`- [x]`) only after CI shows it compiled. The dependency chart in
[docs/DEPENDENCIES.md](docs/DEPENDENCIES.md) shows how the items connect.
[docs/roadmap.html](docs/roadmap.html) is an interactive map of this file (open it in a browser; it reads
this file live from main). [docs/PARALLEL_EFFORTS.md](docs/PARALLEL_EFFORTS.md) records two independent
Grok attempts at the same formalization and how they compare with this repository.

Markers: `- [ ]` open, `- [x]` done and compiled, `- [-]` deliberately skipped (with a reason).

Rules: no `sorry` in a ticked item, no `axiom`, `opaque`, `admit`, `native_decide` or `unsafe`.
An analytic input that is not proved here enters as a named hypothesis or structure field, never
as a hidden assumption. No item claims that Theorem 1.1 is proved until its proof has no `sorry`
and no hypotheses beyond the paper's.

## Done (v0.2, CI-verified at 9130247)

- [x] Definitions: `entropyBits`, `conv`, `entropyIncrement`, `entropyDefect`, `interaction`,
      `quotientLoss`, `IsSparse` (`EntropyLean/Basic.lean`); `WeightedFamily`, `meanEntropy`,
      `meanInteraction`, `averagedLoss`, `WeightedFamily.IsSparse`, `quotient`, `convFamily`
      (`EntropyLean/Families.lean`).
- [x] Identities: `entropyBits_eq_sum`, `entropyDefect_eq`, `interaction_self`,
      `meanEntropy_quotient`, `conv_weights_sum`.
- [x] `bernoulli_parameter_mem_Ioo`; `entropy_le_increment_of_defect_le` (the algebraic step in
      the proof of Theorem 1.1).
- [x] Statements with `sorry`: Theorem 1.1, Theorem 1.2, Theorem 8.2, Lemma 4.1, Lemma 9.1,
      Proposition 9.3 (`EntropyLean/Statements.lean`).

## A. Entropy basics (`EntropyLean/Basic.lean` or `EntropyLean/EntropyFacts.lean`)

- [x] A1. `negMulLogb_nonneg`: `0 ≤ -p * logb 2 p` for `0 ≤ p ≤ 1`; `entropyBits_nonneg` for a
      law on a finite type.
  - Written by the hourly task 2026-11-13 (uncompiled at push): `negMulLogb_nonneg`,
    `pmf_toReal_le_one`, `entropyBits_term_nonneg`, `entropyBits_nonneg`, `entropyBits_nonneg'`
    (`EntropyLean/EntropyFacts.lean`).
- [x] A2. `entropyBits_pure`: `entropyBits (PMF.pure a) = 0`; `entropyBits_le_log_card`:
      `entropyBits P ≤ logb 2 (Fintype.card α)`.
  - Written by the hourly task 2026-11-13 (uncompiled at push): `entropyBits_pure`,
    `neg_mul_log_le_gibbs`, `pmf_sum_toReal`, `entropyBits_le_log_card`
    (`EntropyLean/EntropyFacts.lean`).
- [x] A3. `entropyBits_map_le`: `H(f ∘ X) ≤ H(X)` for `PMF.map f` on finite types (data
      processing for a function); `entropyBits_map_injective`: equality for injective `f`.
  - Written by the hourly task 2026-11-13 (uncompiled at push): `neg_mul_logb_sum_le`,
    `pmf_map_toReal`, `entropyBits_map_le`, `entropyBits_map_injective`
    (`EntropyLean/EntropyFacts.lean`).
- [x] A4. `conv_map_hom`: for an additive map `q`, `(conv P Q).map q = conv (P.map q) (Q.map q)`
      (quotient commutes with convolution, used in Lemma 4.1).
  - Written by the hourly task 2026-11-13 (uncompiled at push): `conv_map_of_add`,
    `conv_map_hom`, `conv_map_mkQ` (`EntropyLean/EntropyFacts.lean`).
- [x] A5. `WeightedFamily.quotient_quotient`: quotienting by `G`, then by `W ≤ V ⧸ G`, equals
      quotienting by the inverse image of `W` (entropy-level statement), used in Lemma 9.1.
  - Written by the hourly task 2026-11-13 (uncompiled at push): `pmf_map_apply_injective`,
    `pmf_map_apply_of_not_mem_range`, `entropyBits_map_of_injective`,
    `entropyBits_map_eq_of_fibres`, `mkQ_mkQ_surjective`, `mkQ_mkQ_fibres`,
    `entropyBits_map_mkQ_mkQ`, `WeightedFamily.quotient_quotient`,
    `WeightedFamily.averagedLoss_quotient` (`EntropyLean/QuotientFacts.lean`).

## B. Information-theory layer

- [ ] B1. Decide the entropy backend and record the decision here: (i) continue with the
      `PMF`-based definitions, or (ii) depend on the PFR project (github.com/teorth/pfr), which
      formalizes Shannon entropy, Ruzsa distance and an entropic PFR theorem. Check its
      toolchain against Lean 4.35.0 and whether its constant matches the 6 in (35). If (ii),
      prove `entropyBits` agrees with PFR's entropy divided by `log 2`.
- [x] B2. Conditional entropy and mutual information for finite joint laws; chain rule;
      `I(A;B|C) ≥ 0` (`EntropyLean/Information.lean`). Split by the hourly task 2026-11-13:
  - [x] B2a. `condEntropy`, `mutualInfo`, chain rule `entropyBits_chain`, `condEntropy_nonneg`,
        `mutualInfo_le_left`, `mutualInfo_le_right`, `mutualInfo_swap`.
    - Written by the hourly task 2026-11-13 (uncompiled at push; CI green at 2e3eabd).
  - [x] B2b. Subadditivity `entropyBits_subadditive : H(A,B) ≤ H(A) + H(B)`, hence
        `mutualInfo_nonneg` and `condEntropy_le`.
    - Written by the hourly task 2026-11-13 (uncompiled at push): `neg_mul_log_le_cross`,
      `pmf_toReal_le_map`, `sum_toReal_mul_comp`, `entropyBits_eq_div_log`,
      `entropyNats_subadditive`, `entropyBits_subadditive`, `mutualInfo_nonneg`, `condEntropy_le`.
      First push failed CI (`div_add_div_same` no longer exists); fixed in 36b62fa, CI green.
  - [x] B2c. Conditional mutual information `condMutualInfo` for a law on `α × β × γ` and
        `condMutualInfo_nonneg : I(A;B|C) ≥ 0` (conditional subadditivity).
    - Written by the hourly task 2026-11-13 (uncompiled at push): `tripleAC`, `tripleC`,
      `condMutualInfo`, `sum_fst_toReal`, `sum_cond_ratio_le_one`, `condMutualInfo_nats_nonneg`,
      `condMutualInfo_nonneg` (`EntropyLean/CondInformation.lean`).
- [x] B3. Equation (9): `interaction_nonneg`, `interaction_le_left`, `interaction_le_right`;
      equation (14): `0 ≤ e(𝒫) ≤ h(𝒫)` (`meanInteraction_nonneg`, `meanInteraction_le`).
      Split by the hourly task 2026-11-13 (`EntropyLean/Interaction.lean`):
  - [x] B3a. Joint law `prodLaw P Q` with marginals `P`, `Q` and sum law `conv P Q`;
        `entropyBits_conv_le : H(P * Q) ≤ H(P) + H(Q)`, `interaction_nonneg`,
        `WeightedFamily.meanInteraction_nonneg`.
    - Written by the hourly task 2026-11-13 (uncompiled at push): `prodLaw`, `prodLaw_map_fst`,
      `prodLaw_map_snd`, `prodLaw_map_add`, `entropyBits_conv_le`, `interaction_nonneg`,
      `WeightedFamily.meanInteraction_nonneg`. CI green at f39bd51.
  - [x] B3b. `H(A + B) ≥ H(B)` for independent `A`, `B` in a finite additive group
        (`entropyBits_le_conv_right`, `entropyBits_le_conv_left`), hence `interaction_le_left`,
        `interaction_le_right`.
    - Written by the hourly task 2026-11-13 (uncompiled at push): `prodLaw_apply`,
      `entropyBits_prodLaw`, `fst_add_injective`, `snd_add_injective`, `entropyBits_le_conv_right`,
      `entropyBits_le_conv_left`, `interaction_le_left`, `interaction_le_right`.
      First push failed CI (`congrArg Prod.fst h` in `fst_add_injective`); fixed in 352b199, CI green.
  - [x] B3c. `WeightedFamily.meanInteraction_le : e(𝒫) ≤ h(𝒫)` from B3b.
    - Written by the hourly task 2026-11-14 (uncompiled at push): `WeightedFamily.meanInteraction_le`
      (`EntropyLean/Interaction.lean`, ef95c01). CI green.
- [x] B4. Equation (15): `meanEntropy_convFamily : h(𝒫 * 𝒫) = 2h(𝒫) − e(𝒫)`.
  - Written by the hourly task 2026-11-14 (uncompiled at push): `WeightedFamily.meanEntropy_convFamily`
    (`EntropyLean/Interaction.lean`, fe44eaa). CI green.
- [x] B5. Data processing for the increment: `entropyIncrement_quotient_le : D(q_G X) ≤ D(X)`.
  - Written by the hourly task 2026-11-14 (uncompiled at push): `incTriple`, `incTriple_injective`,
    `pair_self_injective`, `prodLaw_map_left`, `entropyBits_sub_map_le_conv`,
    `entropyIncrement_map_le`, `entropyIncrement_quotient_le`, `quotientLoss_le_conv`
    (`EntropyLean/Increment.lean`, 27d39b9). Proof: `I(X+Y ; (fX, Y) | f(X+Y)) ≥ 0`. CI green.
- [x] B6. Lemma 2.1: `quotient_entropy_supermodular` (equation (11)).
  - Written by the hourly task 2026-11-14 (uncompiled at push): `quot_mkQ_eq_iff`, `quotTriple`,
    `quotTriple_fibres`, `quotTriple_AC_fibres`, `quotTriple_BC_fibres`,
    `quotient_entropy_supermodular`, `quotientLoss_supermodular`,
    `WeightedFamily.averagedLoss_supermodular` (`EntropyLean/Supermodular.lean`, 3a405a2).
    Proof: `I(q_U A ; q_W A | q_{U ⊔ W} A) ≥ 0`. CI green.

## C. Variational steps and the reduction of Theorem 1.1

- [x] C1. Lemma 9.1: prove `variational_sparsification` by minimizing `h(q_G 𝒫) + λ dim G`
      over the finite set of subspaces (needs A1, A5).
  - Written by the hourly task 2026-11-14 (uncompiled at push): `quotientLoss_bot`,
    `finrank_comap_mkQ`, `WeightedFamily.meanEntropy_nonneg`, `WeightedFamily.averagedLoss_bot`,
    `WeightedFamily.variationalObjective`, `WeightedFamily.variationalObjective_bot`,
    `WeightedFamily.variational_sparsification_proof` (`EntropyLean/Variational.lean`, dd5dc59);
    the `sorry` in `variational_sparsification` (`EntropyLean/Statements.lean`) is replaced by it.
    CI green at 39edb78; L91 marked proved in docs/DEPENDENCIES.md (8f50e25).
- [x] C2. Conditional Theorem 1.1: `exponential_entropy_quotient_of_rigidity`, proving the
      statement of Theorem 1.1 from Lemma 9.1, B5, `entropy_le_increment_of_defect_le` and
      Theorem 8.2 taken as an explicit hypothesis. Also the singleton family
      `WeightedFamily.singleton` and `meanEntropy_singleton`.
  - Written by the hourly task 2026-11-14 (uncompiled at push): `WeightedFamily.singleton`,
    `meanEntropy_singleton`, `meanInteraction_singleton`, `averagedLoss_singleton`,
    `isSparse_singleton_iff`, `meanEntropy_singleton_quotient`,
    `meanInteraction_singleton_quotient`, `WeightedFamilyRigidity` (Theorem 8.2 as a `Prop`),
    `entropy_le_of_defect_le_aux`, `exponential_entropy_quotient_of_rigidity`
    (`EntropyLean/Conditional.lean`, eb65786). Theorem 1.1 itself stays open. CI green.
- [x] C3. Theorem 1.2 from Theorem 8.2: `sparse_rigidity_of_family_rigidity` via the singleton
      family (Theorem 8.2 as an explicit hypothesis).
  - Written by the hourly task 2026-11-14 (uncompiled at push): `sparse_rigidity_of_family_rigidity`
    (`EntropyLean/Conditional.lean`, 6af3de7). Theorem 1.2 itself stays open. CI green.
- [x] C4. Lemma 4.1: prove `ratio_preserving_sparsification` from the objective (24) (needs A4,
      B3, B4). Split by the hourly task 2026-11-14 (`EntropyLean/RatioSparsification.lean`):
  - [x] C4a. Objective `WeightedFamily.ratioObjective` (24); equation (26) at a minimizer
        (`ratioObjective_min_loss`); items 2–3 of Lemma 4.1 (`ratioObjective_min_sparse`).
    - Written by the hourly task 2026-11-14 (uncompiled at push): `quotientLoss_nonneg`,
      `WeightedFamily.averagedLoss_nonneg`, `WeightedFamily.quotient_convFamily_averagedLoss`,
      `WeightedFamily.quotient_convFamily_meanEntropy`, `WeightedFamily.ratioObjective`,
      `WeightedFamily.ratioObjective_bot`, `WeightedFamily.ratioObjective_min_loss`,
      `WeightedFamily.ratioObjective_min_sparse` (2704606). CI green at 69d8db3.
  - [x] C4b. Equation (25) (ratio does not decrease, via (15) on `q_G 𝒫` and
        `h(q_G ℛ) ≤ 2h(q_G 𝒫)`), positivity `h(q_G 𝒫) > 0` at a least-dimension minimizer, and
        the proof of `ratio_preserving_sparsification` replacing its `sorry`.
    - Written by the hourly task 2026-11-14 (uncompiled at push): `WeightedFamily.ratioObjective_eq`,
      `WeightedFamily.ratioObjective_bot_of`, `WeightedFamily.ratioObjective_min_ratio`,
      `WeightedFamily.ratioObjective_min_pos`, `WeightedFamily.ratio_preserving_sparsification_proof`
      (459e514); the `sorry` in `ratio_preserving_sparsification` (`EntropyLean/Statements.lean`)
      is replaced by it. Proof: with `d = e/h`, `Φ(G) = (4+d)h(q_G 𝒫) − e(q_G 𝒫) + 4λ dim G` and
      `Φ(0) = 4h(𝒫)`; `λ`-sparsity of `𝒫` at `G` gives (25). CI green at 459e514 (checked in the
      same run); L41 marked proved in docs/DEPENDENCIES.md (b74c0ea).
- [x] C5. Corollary 9.2: statement, and its proof from Lemma 9.1, B5 and Theorem 8.2 as a
      hypothesis.
  - Written by the hourly task 2026-11-14 (uncompiled at push): `conv_comm_law`, `interaction_comm`,
    `WeightedFamily.pair`, `WeightedFamily.meanEntropy_pair`, `WeightedFamily.meanInteraction_pair`,
    `WeightedFamily.meanEntropy_pair_quotient`, `WeightedFamily.meanInteraction_pair_quotient`,
    `two_input_almost_additivity_of_rigidity` (`EntropyLean/TwoInput.lean`, d8a3bdd): (45), (46), the
    additive error `s(q_G U, q_G V) ≤ α(H(U) + H(V))` and both mixed-input bounds, with Theorem 8.2
    as the hypothesis `hrig`. Corollary 9.2 itself stays open. CI green at d8a3bdd (checked in the
    same run); linter clean-up in 86bf9ad; C92 marked stated in docs/DEPENDENCIES.md (cb95eeb).

## D. Rigidity core (Sections 2.3, 3, 5–8)

- [x] D1. Iteration arithmetic of Theorem 8.2, pure real analysis: from (43) derive
      `d * logb 2 (1/λ) < 320` for `0 < d ≤ 1` (`EntropyLean/RigidityArith.lean`).
  - Written by the hourly task 2026-11-14 (uncompiled at push): `inv_ratio_step` (42),
    `neg_mul_log_le_one_sub`, `half_le_log_two`, `log_1600_lt`, `rigidity_arith_aux`,
    `rigidity_iteration_bound` (`EntropyLean/RigidityArith.lean`, 2869a24). The hypothesis
    `λ > (d²/1600)·4^(−⌈149/d⌉)` is written `d^2 / (1600 * 4 ^ ⌈149/d⌉₊) < λ`; the proof uses
    `−d log d ≤ 1 − d` in place of `d log₂(1/d) ≤ 1/(e ln 2)` and still gives `< 311 + 2/ln 2`.
    CI green at 2869a24 (checked in the same run); linter clean-up in 1a94cc0; ARITH marked
    proved in docs/DEPENDENCIES.md (e12507d).
- [x] D2. Theorem 8.2 from Lemma 8.1: `weighted_family_rigidity_of_growth`, with Lemma 8.1 as an
      explicit hypothesis, using D1.
  - Written by the hourly task 2026-11-14 (uncompiled at push): `FiniteF2Family`, `RatioGrowth`
    (Lemma 8.1 as a `Prop`, with `d ≥ 40√λ` written `1600 λ ≤ d²`), `ratio_le_one_aux`,
    `ratio_iteration`, `weighted_family_rigidity_of_growth`, `exponential_entropy_quotient_of_growth`,
    `sparse_rigidity_of_growth` (`EntropyLean/RatioGrowth.lean`, c74880f). Theorem 8.2 itself stays
    open. CI green at c74880f (checked in the same run; job log not readable this run, so linter
    warnings unchecked); L81 marked stated in docs/DEPENDENCIES.md (6aed3f7).
- [x] D3. Posterior families: `WeightedFamily.posterior` and Lemma 2.2 (`posterior_closure`).
      Split by the hourly task 2026-11-14 (`EntropyLean/Posterior.lean`):
  - [x] D3a. `conv_apply : (P * Q)(t) = ∑ₐ P(a) Q(t − a)`, the posterior law `posteriorLaw` of `A`
        given `A + B = t`, and the posterior family `WeightedFamily.posterior` (equation (16)) with
        weights `a_i a_j (P_i * P_j)(t)` summing to one (for `V : Type`).
    - Written by the hourly task 2026-11-14 (uncompiled at push): `conv_apply`, `posteriorLaw`,
      `posteriorLaw_apply`, `posteriorLaw_toReal`, `WeightedFamily.postMass`,
      `WeightedFamily.postMass_sum`, `WeightedFamily.postMass_pos`, `WeightedFamily.posterior`
      (5643889). CI green.
  - [x] D3b. First half of (17): `meanEntropy_posterior : h(Post 𝒫) = e(𝒫)`, via
        `H(A | I, J, A + B) = H(A) + H(B) − H(A + B)` given the indices.
    - Written by the hourly task 2026-11-14 (uncompiled at push): `posterior_term_eq`,
      `conv_toReal_eq_sum`, `fintype_sum_shift`, `conv_mul_entropy_posterior`,
      `sum_conv_mul_entropy_posterior`, `WeightedFamily.meanEntropy_posterior` (3dab04d). CI green.
  - [x] D3c. Second half of (17): `averagedLoss_posterior_le : F_{Post 𝒫}(W) ≤ F_𝒫(W)`, and
        `posterior_closure` (posterior formation preserves averaged λ-sparsity).
        Split by the hourly task 2026-11-14:
    - [x] D3c1. Disintegration along `A + B`: `entropyBits_of_kernel` (`H(R) = H(c) + ∑ₜ c(t) H(K_t)`
          when `R(a, t) = c(t) K_t(a)`), `kernel_masses_map`, `entropyBits_pair_sum`,
          `entropyBits_map_pair_sum`.
      - Written by the hourly task 2026-11-14 (uncompiled at push): `entropyBits_of_kernel`,
        `kernel_masses_map`, `conv_mul_posteriorLaw_toReal`, `pair_sum_masses`,
        `entropyBits_pair_sum`, `entropyBits_map_pair_sum` (c54874b). CI green.
      - Parallel version from an overlapping hourly run 2026-11-14 (`EntropyLean/PosteriorLoss.lean`,
        7bbc47d, CI green): for any map `f`, the joint law `jointLaw P Q f` of `(f A, A + B)` and the
        chain rule `sum_conv_mul_entropy_posterior_map :
        ∑ₜ (P * Q)(t) H(f_* Q_t) = H(f A, A + B) − H(A + B)` (also `jointLaw_toReal`,
        `jointLaw_map_snd`, `sum_jointLaw_toReal`, `posteriorLaw_map_toReal`, `mul_neg_div_logb_eq`,
        `conv_mul_entropy_posterior_map`). D3c2 may use either version.
    - [x] D3c2. `H(A, A + B) − H(q_W A, A + B) ≤ H(A) − H(q_W A)` from `condMutualInfo_nonneg`
          on `(A, A + B, q_W A)`, hence `∑ₜ (P * Q)(t) F_{Q_t}(W) ≤ F_P(W)`; averaging gives
          `averagedLoss_posterior_le` and `posterior_closure`.
      - Written by the hourly task 2026-11-14 (uncompiled at push): `joint_loss_le`,
        `sum_conv_mul_quotientLoss_posterior_le`, `WeightedFamily.averagedLoss_posterior_le`,
        `WeightedFamily.posterior_closure`, `WeightedFamily.posterior_lemma` (Lemma 2.2)
        (`EntropyLean/PosteriorClosure.lean`, 7df22ae). Uses the D3c1 lemmas of `Posterior.lean`.
        CI green at 7df22ae (checked in the same run); L22 marked proved in docs/DEPENDENCIES.md
        (685e565). Lemma 2.2 is proved for `V : Type` (the index type of a `WeightedFamily`
        lives in `Type`).
- [x] D4. Lemma 3.1: fibring identity (20) and the nested inequality (22).
      Split by the hourly task 2026-11-14 (`EntropyLean/Fibring.lean`):
  - [x] D4a. Fibre interaction `s_W` (18) along an additive map, the fibring identity (20) and (21).
    - Written by the hourly task 2026-11-14 (uncompiled at push): `prodLaw_map_right`,
      `prodLaw_map_both`, `fibreJoint`, `fibreInteraction`, `fibreTriple`, `fibreMutualInfo`,
      `fibreMutualInfo_nonneg`, `fibreInteraction_eq`, `fibreMutualInfo_eq`, `interaction_fibring`,
      `interaction_sub_le_fibre`, `subspaceInteraction`, `interaction_fibring_quot`,
      `interaction_sub_le_subspace` (57d684c). Proof: `I(A + B ; (q A, q B) | q (A + B)) ≥ 0`.
      First push failed CI (`congrArg Prod.fst` in the injectivity step of `fibreMutualInfo_eq`);
      fixed with `Prod.mk.inj` in 118d4a3, CI green. An overlapping hourly run wrote a different
      `Fibring.lean` in 6683d9c (`fiberInteraction`, `fibringDefect`), which 57d684c replaced.
  - [x] D4b. Equation (19): `0 ≤ s_W(P, Q) ≤ min(F_P(W), F_Q(W))` (`subspaceInteraction_nonneg`,
        `subspaceInteraction_le_left`, `subspaceInteraction_le_right`).
    - Written by the hourly task 2026-11-14 (uncompiled at push): `fibreInteraction_nonneg`,
      `fibreInteraction_le_left`, `fibreInteraction_le_right`, `subspaceInteraction_nonneg`,
      `subspaceInteraction_le_left`, `subspaceInteraction_le_right`, `subspaceInteraction_le_min`
      (1d0d93c). Proof: `I(A + B ; A | f A, f B) ≥ 0` (resp. `B`) via `condMutualInfo_nonneg`.
      CI green at 1d0d93c (checked in the same run; job log not readable, so linter warnings
      unchecked).
  - [x] D4c. Nested inequality (22) via (23): for `U ≤ W`,
        `F_Q(U) ≥ s_W(P, Q) − (H(q_U P) − H(q_W P))` (`subspaceInteraction_nested`).
    - Written by Claude 2026-11-14 (uncompiled at push): `fibreInteraction_nested` ((23) along a
      factorisation `k = g ∘ f`: `s_k ≤ s_f + H(f A) − H(k A)`, from `I(A + B ; f A | k A, k B) ≥ 0`),
      `fibreInteraction_nested_loss`, `subspaceInteraction_nested` (with `g = U.liftQ W.mkQ`)
      (f1600fa). CI green at f1600fa (checked in the same run; job log not readable, so linter
      warnings unchecked). L31 marked proved in docs/DEPENDENCIES.md.
- [x] D5. Lemma 5.1: averaged density estimate (28)–(29).
      Split by Claude 2026-11-14 (`EntropyLean/DensityEstimate.lean`):
  - [x] D5a. One-step inequality (30) `subspaceInteraction_step` (from (22) with `U = S ⊓ W`,
        monotonicity `quotientLoss_mono` and (11)), and its average over a fresh index for a
        `λ`-sparse family, `WeightedFamily.averaged_density_step`.
    - Written by Claude 2026-11-14 (uncompiled at push): `quotientLoss_mono`,
      `subspaceInteraction_step`, `WeightedFamily.averaged_density_step` (2a1d5f9). CI green at
      2a1d5f9 (checked in the same run).
  - [x] D5b. Inequality (28) `A ≤ h/N + λB(N − 1)/2` for every `N ≥ 1`. Avoid product measures over
        sample sequences: for fixed `u` define recursively `Φ₀(S) = H(q_S Q_u)`,
        `Φ_{k+1}(S) = ∑_w b_w Φ_k(S ⊔ V(u, w))` and `D₀(S) = dim S`, `D_{k+1}(S) = ∑_w b_w D_k(S ⊔ V(u, w))`;
        prove `N A_u ≤ Φ₀(S) − Φ_N(S) + λ ∑_{k<N} D_k(S)` by induction on `N` generalising `S` (from
        D5a), `Φ_N ≥ 0` and `D_k(S) ≤ dim S + k B_u`; then take `S = 0` and average over `u`
        (`WeightedFamily.averaged_density_estimate`).
    - Written by Claude 2026-11-14 (uncompiled at push): `finrank_sup_le_add`,
      `sum_range_cast_mul_two`, `WeightedFamily.rowInteraction`, `densPhi`, `densDim` (with
      `_zero`/`_succ` equations), `densPhi_nonneg`, `densDim_le`, `densPhi_induction`,
      `averaged_density_estimate` (e45ffe9). Hypothesis `0 ≤ λ` added (the paper takes `λ ≥ 0`).
      First push failed CI (`quotientLoss_bot` needs `import EntropyLean.Variational`); fixed with
      linter clean-up in ca39b0e, CI green.
  - [x] D5c. Inequality (29): `B ≤ 26h ⇒ A ≤ 14√λ h`, with `N = ⌈λ^{-1/2}⌉` for `0 < λ ≤ 1`,
        `A ≤ h` from (19) for `λ > 1`, and `h = 0` for `λ = 0` (`WeightedFamily.averaged_density_sqrt`).
    - Written by the hourly task 2026-11-14 (uncompiled at push): `density_sqrt_arith`,
      `WeightedFamily.averaged_density_sqrt`, `WeightedFamily.averaged_density_lemma` (Lemma 5.1,
      (28) and (29)) (`EntropyLean/DensitySqrt.lean`, 066a13a). With `N = ⌈λ^{-1/2}⌉` for `λ > 0`
      (no separate case `λ > 1` needed) and `N → ∞` for `λ = 0`. Do not re-implement in
      `DensityEstimate.lean` (the names would clash). CI green at 066a13a; L51 marked proved in
      docs/DEPENDENCIES.md (eb44992).
- [x] D6. Lemma 6.1 (four-sample splitting), Lemma 6.2 (conditional BSG), Lemma 6.3.
      Split by the hourly task 2026-11-14:
  - [x] D6a. Entropic Ruzsa distance (8) `ruzsaDist` with `ruzsaDist_self` (`d(P, P) = D(P)`),
        `ruzsaDist_comm`, `ruzsaDist_nonneg`, translation invariance `ruzsaDist_map_add_const`,
        `ruzsaDist_translate_self`; entropy submodularity `entropyBits_submodular`
        (`EntropyLean/RuzsaDistance.lean`).
    - Written by the hourly task 2026-11-14 (uncompiled at push): `ruzsaDist`, `ruzsaDist_self`,
      `ruzsaDist_eq_sub_interaction`, `ruzsaDist_comm`, `ruzsaDist_nonneg`, `conv_map_add_const`,
      `ruzsaDist_map_add_const`, `ruzsaDist_translate_self`, `entropyBits_submodular` (0dc2f93). CI green at 0dc2f93.
  - [x] D6b. Lemma 6.2 (33) for a joint law `R` of `(U, V)` on a finite F₂-space: conditional laws
        `Law(U | Z = z)`, `Law(V | Z = z)` of `Z = U + V`, the conditionally independent double
        trial given `Z`, and `∑_z R_Z(z) d(Law(U | z), Law(V | z)) ≤ 3I(U ; V) + 2H(Z) − H(U) − H(V)`
        (`EntropyLean/ConditionalBSG.lean`, `conditional_bsg`). Split by the hourly task 2026-11-14:
    - [x] D6b1. `sumLaw R` (law of `Z = U + V`), conditional laws `fibreLaw R z` (`U` given `Z = z`)
          and `fibreLawSnd R z` (`V` given `Z = z`), chain rule `entropyBits_fibre_chain`
          (`H(U, V) = H(Z) + ∑_z R_Z(z) H(K_z)`), and over F₂ `ruzsaDist_fibreLaw`
          (`d(K_z, L_z) = D(K_z)`) and `sum_ruzsaDist_fibreLaw`.
      - Written by the hourly task 2026-11-14 (uncompiled at push): `sumLaw`, `sumLaw_apply`,
        `sumLaw_toReal`, `fibreLaw`, `fibreLawSnd`, `fibreLaw_toReal`, `sumLaw_mul_fibreLaw_toReal`,
        `fibrePair_masses`, `entropyBits_fibre_chain`, `sub_eq_add_of_zmod2`, `ruzsaDist_fibreLaw`,
        `sum_ruzsaDist_fibreLaw` (a43f76d). CI green at a43f76d.
    - [x] D6b2. Conditionally independent double trial: the law `T` of `(U₁, U₂, Z)` with masses
          `R_Z(z) K_z(a) K_z(b)`, `H(T) = 2H(U, V) − H(Z)`, marginals of `(U₁, V₂ = U₂ + Z)` and
          `(V₁ = U₁ + Z, U₂)` with entropy `≤ H(U) + H(V)`, and via `entropyBits_submodular` (both
          pairs determine `W = U₁ + V₂`) `H(W) ≤ 2I(U ; V) + H(Z)` (`double_trial_sum_le`).
          Split by the hourly task 2026-11-14 (`EntropyLean/DoubleTrial.lean`):
      - [x] D6b2a. Kernel joint law `kernelJoint c K`, the double trial `doubleTrial R` (law of
            `((U₁, U₂), Z)`), `H(T) = 2H(U, V) − H(Z)`, the laws of `(U₁, Z)`, `(U₂, Z)`, `U₁`, `U₂`,
            `V₁ = U₁ + Z`, `V₂ = U₂ + Z`, and `H(U₁, V₂), H(V₁, U₂) ≤ H(U) + H(V)`.
        - Written by the hourly task 2026-11-14 (uncompiled at push): `kernelJoint`,
          `kernelJoint_apply`, `kernelJoint_toReal`, `entropyBits_kernelJoint`, `pmf_ext_toReal`,
          `doubleTrial`, `entropyBits_doubleTrial`, `doubleTrial_map_fst_pair`,
          `doubleTrial_map_snd_pair`, `zmod2_add_add_self`, `add_comp_fst_add`, `doubleTrial_map_U1`,
          `doubleTrial_map_U2`, `doubleTrial_map_V1`, `doubleTrial_map_V2`, `dtPair1`, `dtPair2`,
          `entropyBits_dtPair1_le`, `entropyBits_dtPair2_le` (9c60ff4). CI green at 9c60ff4.
      - [x] D6b2b. Submodularity step: with `W = U₁ + V₂ = V₁ + U₂`, apply `entropyBits_submodular`
            to the law of `((U₁, V₂), (V₁, U₂), W)` (injective image of `T`; each pair determines `W`)
            to get `H(T) + H(W) ≤ H(U₁, V₂) + H(V₁, U₂)`, hence `double_trial_sum_le :
            H(W) ≤ 2 * mutualInfo R + H(Z)` (`EntropyLean/DoubleTrial.lean`).
        - Written by the hourly task 2026-11-15 (uncompiled at push): `dtSum`, `dtTriple`, `withSum`,
          `withSum_injective`, `dtTriple_injective`, `double_trial_sum_le` (09f86df). CI green at 09f86df.
    - [x] D6b3. `∑_z R_Z(z) H(K_z * K_z) ≤ H(W)` (kernel formula for `(W, Z)` and `H(W | Z) ≤ H(W)`),
          then `conditional_bsg` (33) from `sum_ruzsaDist_fibreLaw` and D6b2.
      - Written by the hourly task 2026-11-15 (uncompiled at push): `dtSumPair`, `shiftPair`,
        `shiftPair_injective`, `entropyBits_dtSumPair`, `doubleTrial_map_Z`, `sum_conv_fibreLaw_le`,
        `conditional_bsg` (`EntropyLean/ConditionalBSGLemma.lean`, caefe56; a separate file because
        `DoubleTrial.lean` imports `ConditionalBSG.lean`). CI green at caefe56; L62 marked proved in
        docs/DEPENDENCIES.md (d37b9f2).
  - [x] D6c. Four-sample setup of Section 6 (`T`, `S`, `A`, `B`, `C`, `J = I(A ; B | S, T)`) and
        Lemma 6.1 (32) `e(𝒫 * 𝒫) + e(Post 𝒫) = 2δH + J` (`EntropyLean/FourSample.lean`,
        `four_sample_splitting`). Split by the hourly task 2026-11-15 (conditioning on `T` is a
        weighted sum over index tuples, so each step is first proved for four fixed laws):
    - [x] D6c1. Fixed laws `P₁, …, P₄`: `fourProd`, the law `fourLaw` of `(A, B, S)`,
          `fourJ = I(A ; B | S)`, `H(A | S) = s(P₁ * P₂, P₃ * P₄)`, `H(B | S) = s(P₁ * P₃, P₂ * P₄)`,
          and `fourJ = H(B | S) − (H(A, B, S) − H(A, S))` (`EntropyLean/FourSample.lean`).
      - Written by the hourly task 2026-11-15 (uncompiled at push): `fourProd`, `fourABS`, `fourLaw`,
        `fourJ`, `fourJ_nonneg`, `fourSwap`, `fourSwap_injective`, `fourProd_swap`, `fourPairSums`,
        `fourAS`, `fourS`, `fourProd_map_pairSums`, `entropyBits_fourAS_sub`, `fourLaw_map_AC`,
        `fourLaw_map_C`, `fourLaw_map_BC`, `fourLaw_map_C_swap`, `fourLaw_condEntropy_A`,
        `fourLaw_condEntropy_B`, `fourJ_eq` (82be130). First push failed CI (`fourLaw_map_BC`,
        `fourLaw_map_C_swap` omitted `[Fintype V]`, needed by `fourProd_swap`); fixed in 80a5299, CI green.
    - [x] D6c2. Posterior formula at fixed laws: `H(A, B, S) − H(A, S) =
          ∑_{a,c} (P₁ * P₂)(a) (P₃ * P₄)(c) H(Q_{12,a} * Q_{34,c})` with `Q_{12,a} = posteriorLaw P₁ P₂ a`,
          via `entropyBits_of_kernel` on `(B, (A, C))`, `C = X₃ + X₄` (`EntropyLean/FourSamplePosterior.lean`).
      - Written by the hourly task 2026-11-15 (uncompiled at push): `fourPostJoint`,
        `fourPostJoint_kernel`, `fourPost_masses`, `entropyBits_fourPost`, `fourPhi_injective`,
        `fourLaw_eq_map_post`, `entropyBits_fourLaw_AC`, `fourLaw_condEntropy_B_given_AS` (dfed001).
        First push failed CI (`isDefEq` timeout in the term-mode `entropyBits_fourPost`); fixed with
        explicit kernel arguments in 274edd4, CI green.
    - [x] D6c3. Averaging over `T` with weights `a_{i₁} a_{i₂} a_{i₃} a_{i₄}`: define
          `WeightedFamily.fourSampleJ`, reindex `∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄}) = e(𝒫 * 𝒫)` and
          the posterior sum as `2h(Post 𝒫) − e(Post 𝒫)`, and with `meanEntropy_posterior` prove
          `four_sample_splitting : e(𝒫 * 𝒫) + e(Post 𝒫) = 2e(𝒫) + J`. Split by the hourly task 2026-11-15:
      - [x] D6c3a. `e(Post 𝒫) = 2e(𝒫) − ∑_{x,y} m(x) m(y) H(Q_x * Q_y)` over all triples
            `x = (i, j, t)` with `m = postMass` (`EntropyLean/PosteriorInteraction.lean`).
        - Written by the hourly task 2026-11-15 (uncompiled at push): `postLawAt`, `postMass_eq_zero`,
          `sum_posterior_index`, `sum_postMass_mul_entropy`, `postPairTerm`,
          `meanInteraction_posterior_full`, `meanInteraction_posterior_eq` (2cac57b). CI green.
      - [x] D6c3b. `WeightedFamily.fourSampleJ`, `e(𝒫 * 𝒫) = ∑_T s(P_{i₁} * P_{i₃}, P_{i₂} * P_{i₄})`,
            reordering the posterior double sum into `∑_T ∑_{a,c}` (from D6c2), and
            `four_sample_splitting` (`EntropyLean/FourSampleSplitting.lean`).
        - Written by the hourly task 2026-11-15 (uncompiled at push): `sum_reorder3`, `fourSampleJ`,
          `fourSampleJ_nonneg`, `fourPostTerm`, `fourSampleJ_eq`, `meanInteraction_convFamily_four`,
          `sum_postMass_conv_eq`, `four_sample_splitting` (Lemma 6.1, (32), with `2δH = 2e(𝒫)`)
          (71dc6e3). CI green at 71dc6e3 (checked in the same run); L61 marked proved in
          docs/DEPENDENCIES.md (04c1579).
  - [x] D6d. Lemma 6.3 (34) `E_{u,w} D(Q_u * Q_w) ≤ 3J` from D6a–D6c (`posterior_doubling`).
        Split by the formalize task 2026-11-15:
    - [x] D6d1. Lemma 6.2 conditioned on a third variable: for `R((u, v), y) = c(y) K_y(u, v)`,
          `∑_y c(y) ∑_z K_{y,Z}(z) d(Law(U | z, y), Law(V | z, y)) ≤ 3I(U ; V | Y) + 2H(Z | Y) −
          H(U | Y) − H(V | Y)` (`EntropyLean/KernelBSG.lean`, `kernel_conditional_bsg`).
      - Written by the formalize task 2026-11-15 02:52 UTC (uncompiled at push):
        `sum_kernel_entropy_map`, `kernel_conditional_bsg`, `kernelJoint_conditional_bsg` (dc28847). CI green at dc28847.
    - [x] D6d2. Fixed laws `P₁, …, P₄`: a conditional law `condKernel R t` of `A` given `T = t` for
          `R : PMF (α × T)` with `R(a, t) = R_T(t) condKernel R t a`; apply D6d1 to the law of
          `((A, C), S)`; `I(A ; C | S) = fourJ` (`(A, C) ↔ (A, B)` is a bijection) and
          `H(C | S) = s(P₂ * P₃, P₁ * P₄)`, giving the fixed-law bound
          `≤ 3 fourJ + 2H(B | S) − H(A | S) − H(C | S)` (`EntropyLean/PosteriorDoubling.lean`,
          `four_conditional_bsg`).
      - Written by the formalize task 2026-11-15 03:05 UTC (uncompiled at push): `sum_fst_apply`,
        `condKernel`, `condKernel_toReal_mul`, `acsMap`, `acsMap_injective`, `fourCS`, `acsLaw`,
        `acs_map_A`, `acs_map_C`, `acs_map_S`, `acs_map_B`, `entropyBits_acsLaw`, `four_conditional_bsg`
        (1a364e5). CI green at 1a364e5. The bound is stated with `H(C | S)`; the identity
        `H(C | S) = s(P₂ * P₃, P₁ * P₄)` is left to D6d3.
    - [x] D6d3. Identify `Law(A | B = b, S = s) = Q_{13,b} * Q_{24,s+b}` (posterior laws of `(P₁, P₃)`
          and `(P₂, P₄)`) with joint weight `(P₁ * P₃)(b) (P₂ * P₄)(s + b)`, and over F₂ the Ruzsa
          term as `D(Q_{13,b} * Q_{24,s+b})` (`four_posterior_doubling_fixed`).
          Split by the formalize task 2026-11-15:
      - [x] D6d3a. Masses: kernel descriptions with the same masses give the same averages
            (`sum_kernel_congr`); `P(A = a, B = b, S = b + d) = (P₁ * P₃)(b) (P₂ * P₄)(d) (Q_{13,b} * Q_{24,d})(a)`
            (`fourLaw_post_toReal`); the weights of `four_conditional_bsg` times `Law(A | B = z, S = s)(a)`
            equal `P(A = a, B = z, S = s)` (`acsLaw_fibre_toReal`) (`EntropyLean/PosteriorDoublingMasses.lean`).
        - Written by the formalize task 2026-11-15 03:45 UTC (uncompiled at push): `sum_kernel_congr`,
          `tripleSwap12`, `tripleSwap12_injective`, `fourLaw_eq_swap`, `fourLaw_post_toReal`,
          `acsLaw_fibre_toReal` (68237b0). CI green at 68237b0.
      - [x] D6d3b. Rewrite the left side of `four_conditional_bsg` with `ruzsaDist_fibreLaw`, the
            reindexing `(s, z) ↦ (z, s + z)` of `V × V`, and `sum_kernel_congr` with `acsLaw_fibre_toReal`
            and `fourLaw_post_toReal`, as `∑_{b,d} (P₁ * P₃)(b) (P₂ * P₄)(d) D(Q_{13,b} * Q_{24,d})`
            (`four_posterior_doubling_fixed`).
        - Written by the formalize task 2026-11-15 03:49 UTC (uncompiled at push):
          `four_posterior_doubling_fixed`, `four_posterior_doubling_bound` (the posterior form of the
          left side bounded by `3 J + 2 H(C | S) − H(B | S) − H(A | S)`)
          (`EntropyLean/PosteriorDoublingFixed.lean`, 5ee3558). First push failed CI
          (`(Equiv.addLeft b).sum_comp` resolved to `Equiv.Perm.sum_comp`); fixed with
          `Equiv.sum_comp` in d652178, CI green.
      - [x] D6d3c. `H(C | S) = s(P₂ * P₃, P₁ * P₄)` over F₂ (`C = X₂ + X₃`; exchange coordinates as in
            `fourLaw_condEntropy_B`) (`fourLaw_condEntropy_C`).
        - Written by the formalize task 2026-11-15 04:10 UTC (uncompiled at push): `fourRot`,
          `fourRot_injective`, `fourProd_rot`, `fourLaw_map_CS`, `fourLaw_map_C_rot`,
          `fourLaw_condEntropy_C`, `four_posterior_doubling_interaction` (the fixed-law bound with
          `3 J + 2 s(P₂ * P₃, P₁ * P₄) − s(P₁ * P₃, P₂ * P₄) − s(P₁ * P₂, P₃ * P₄)` on the right)
          (`EntropyLean/PosteriorDoublingC.lean`, 1abdff1). CI green at 1abdff1.
    - [x] D6d4. Average over `T`: reindex the left side to `∑_{u,w} m(u) m(w) D(Q_u * Q_w)` with
          `m = postMass`, show the averaged `H(A | S, T)`, `H(B | S, T)`, `H(C | S, T)` all equal
          `e(𝒫 * 𝒫)`, and conclude `posterior_doubling` (34).
      - Written by the formalize task 2026-11-15 09:50 UTC (uncompiled at push): `sum4_swap23`,
        `sum4_swap34`, `WeightedFamily.sum_postMass_conv_inc`, `WeightedFamily.fourSampleJ_swap`,
        `WeightedFamily.sum_interaction_swap23`, `WeightedFamily.sum_interaction_rot`,
        `WeightedFamily.posterior_doubling` (Lemma 6.3, (34): `∑_{x,y} m(x) m(y) D(Q_x * Q_y) ≤ 3 J`,
        summed over all posterior triples as in `meanInteraction_posterior_full`)
        (`EntropyLean/PosteriorDoublingAvg.lean`, b008317). The three averaged interaction terms are
        shown equal by relabelling indices, so `e(𝒫 * 𝒫)` itself is not needed. CI green at b008317;
        L63 marked proved in docs/DEPENDENCIES.md (30bd968).
- [x] D7. `structure MartonInput`: the entropic Marton bound (35) as a named hypothesis, and its
      consequence (36). Replace by a theorem if B1 chooses the PFR backend and the constant
      matches. Split by the formalize task 2026-11-15:
  - [x] D7a. `uniformSub W` (uniform law on a subspace), `structure MartonInput` with (35) as the field
        `marton`, `MartonBound`, `0 ≤ D(K) ≤ H(K)`, and (36) from (35) with the two uniform-smoothing
        facts as explicit hypotheses (`MartonInput.consequence_of_smoothing`)
        (`EntropyLean/MartonInput.lean`).
    - Written by the formalize task 2026-11-15 10:50 UTC (uncompiled at push): `subIndicator`,
      `subIndicator_le_one`, `tsum_subIndicator_ne_zero`, `tsum_subIndicator_ne_top`, `uniformSub`,
      `MartonInput`, `MartonBound`, `entropyIncrement_nonneg`, `entropyIncrement_le_entropyBits`,
      `marton_consequence_arith`, `MartonInput.consequence_of_smoothing` (95a5dc7). First push failed
      CI (`PMF.uniformOfFinset` no longer exists in Mathlib; `uniformSub` is now `PMF.normalize` of
      the indicator of `W`); fixed in bee7b79, CI green; linter clean-up in 0ad4f28. E36 marked
      stated in docs/DEPENDENCIES.md.
  - [x] D7b. Entropy of the uniform law and uniform smoothing (`EntropyLean/MartonSmoothing.lean`):
        `uniformSub_apply` (`U_W(v) = 2^(−dim W)` on `W`, `0` off `W`), `entropyBits_uniformSub :
        H(U_W) = dim W`, and `entropyBits_conv_uniformSub : H(K * U_W) = H(q_W K) + dim W` (given
        `q_W(A + U)`, the law of `A + U` is uniform on that coset), hence
        `ruzsaDist_uniformSub : d(K, U_W) = H(q_W K) + (dim W − H(K)) / 2`. Split by the formalize task
        2026-11-15:
    - [x] D7b1. Masses of `U_W` (`uniformSub_toReal`: `1 / |W|` on `W`, `0` off `W`), `|W| = 2 ^ dim W`
          (`subCard_eq`), and `entropyBits_uniformSub : H(U_W) = dim W`.
      - Written by the formalize task 2026-11-15 13:50 UTC (uncompiled at push): `subCard`,
        `tsum_subIndicator`, `subCard_pos`, `uniformSub_toReal`, `entropyBits_uniformSub_card`,
        `subCard_eq`, `entropyBits_uniformSub` (579fad9). First push failed CI (`DecidablePred` for
        `Finset.sum_ite` in `tsum_subIndicator`, fixed with `open Classical in`); fixed with linter
        clean-up in eedc194, CI green (checked in the same run).
    - [x] D7b2. `(K * U_W)(v) = (q_W K)(q_W v) / |W|` (`conv_uniformSub_toReal`), hence
          `entropyBits_conv_uniformSub : H(K * U_W) = H(q_W K) + dim W` and `ruzsaDist_uniformSub`
          (in a new file importing `EntropyLean.MartonSmoothing` if needed). Split by the formalize task
          2026-11-15:
      - [x] D7b2a. Masses `conv_uniformSub_toReal`, fibre count `card_mkQ_fibre` and
            `sum_comp_mkQ : ∑_v g(q_W v) = |W| ∑_x g(x)` (`EntropyLean/MartonConv.lean`).
        - Written by the formalize task 2026-11-15 15:55 UTC (uncompiled at push): `sub_mem_iff_mkQ_eq`,
          `conv_uniformSub_toReal`, `card_mkQ_fibre`, `sum_comp_mkQ` (0606f43). CI green at 0606f43.
      - [x] D7b2b. `entropyBits_conv_uniformSub : H(K * U_W) = H(q_W K) + dim W` (split `−c log c` with
            `c(v) = (q_W K)(q_W v) / |W|`, then `sum_comp_mkQ` and `∑_v c(v) = 1`) and
            `ruzsaDist_uniformSub` (`EntropyLean/MartonConvEntropy.lean`).
        - Written by the formalize task 2026-11-15 16:26 UTC (uncompiled at push): `uniformSmooth_term_eq`,
          `sum_smooth_comp_mkQ`, `entropyBits_conv_uniformSub`, `ruzsaDist_uniformSub` (df6bb0c).
          CI green at df6bb0c (checked in the same run; job log not readable, so linter warnings
          unchecked).
  - [x] D7c. `ruzsaDist_uniformSub_ge : |dim W − H(K)| / 2 ≤ d(K, U_W)` (from
        `H(K * U_W) ≥ max(H(K), H(U_W))`), and `MartonInput.consequence` ((36) with no smoothing
        hypotheses) (`EntropyLean/MartonConsequence.lean`, importing `EntropyLean.MartonConvEntropy`:
        `ruzsaDist_uniformSub` is not available in `MartonSmoothing.lean`, which that file imports).
    - Written by the formalize task 2026-11-15 16:37 UTC (uncompiled at push): `ruzsaDist_uniformSub_ge`,
      `MartonInput.consequence` (795cb8f). (36) now follows from the hypothesis `MartonInput V` alone.
      CI green at 795cb8f. D7 ticked: (35) itself stays the hypothesis `MartonInput V`.
- [ ] D8. Lemma 7.1 (sparse posterior estimate, (37)): `e(𝒬) ≤ 36 J + 14 √ρ δH` for a `ρ`-sparse
      posterior family `𝒬 = Post 𝒫`, with the Marton bound as the hypothesis `MartonInput V`.
      Split by the formalize task 2026-11-15:
  - [x] D8a. Two laws `P`, `Q`: apply (36) to `K = P * Q`, then (21) and `s(q_W P, q_W Q) ≤
        H(q_W (P * Q))` give `s(P, Q) ≤ s_W(P, Q) + 12 D(P * Q)` with `dim W ≤ 13 (H(P) + H(Q))`
        (`EntropyLean/MartonStep.lean`, `interaction_le_subspace_add_increment`).
    - Written by the formalize task 2026-11-15 16:47 UTC (uncompiled at push):
      `interaction_quot_le_entropyBits_conv`, `interaction_le_subspace_add_increment` (a1b87ac).
      CI green at a1b87ac (checked in the same run).
  - [ ] D8b. Average D8a over posterior pairs `(x, y)` with weights `m(x) m(y)` (`m = postMass`,
        all triples as in `meanInteraction_posterior_full`): choose `W(x, y)` by `Classical.choose`,
        then with `posterior_doubling` (34) get `e(𝒬) ≤ ∑ m(x) m(y) s_{W(x,y)}(Q_x, Q_y) + 36 J` and
        (38) `∑ m(x) m(y) dim W(x, y) ≤ 26 h(𝒬)` (`EntropyLean/SparsePosterior.lean`,
        `posterior_interaction_le_subspace`, `posterior_mean_dim_le`).
    - Written by the formalize task 2026-11-15 16:55 UTC (uncompiled at push): `postMass_nonneg`,
      `postSubspace`, `postSubspace_spec`, `posterior_interaction_le_subspace`,
      `posterior_mean_dim_le` (2861748). `W(x, y)` is `postSubspace P hM x y`.
  - [ ] D8c. Lemma 5.1 (`averaged_density_lemma`, (29)) for the `ρ`-sparse family `𝒬` with the
        subspace choice of D8b bounds the first term by `14 √ρ h(𝒬)`; with `meanEntropy_posterior`
        (`h(𝒬) = e(𝒫) = δH`) conclude `sparse_posterior_estimate` (37)
        (`EntropyLean/SparsePosterior.lean`).
- [ ] D9. Lemma 8.1 from C4, D3, D6, D8.

## E. Proposition 9.3 (independent of Theorem 8.2)

- [ ] E1. `entropyBits` of a Bernoulli law on `ZMod 2` equals `binaryEntropy p`; the sum of two
      independent Bernoulli(p) bits is Bernoulli(2p(1−p)).
- [ ] E2. Bernoulli expansions: `binaryEntropy p = p logb 2 (1/p) + p logb 2 e + O(p²)` and
      `bernoulliDefect p = 2p + O(p² log(1/p))` as explicit inequalities for small `p`.
- [ ] E3. Prove `exponential_scale_necessary` from E1, E2 and `bernoulli_parameter_mem_Ioo`.

## F. Corollary 9.4

- [ ] F1. Statement of Corollary 9.4 and its proof from Theorem 1.1 (as a hypothesis until
      Theorem 1.1 is proved).

## G. Tracking and improving the constant 320

The exponent `2^(320(1+ε)/ε)` in Theorem 1.1 comes from the iteration arithmetic (42)–(43)
(item D1) and, through it, from the constant 6 in the entropic Marton bound (35) and the constants
12, 13 in (36). These items make that dependence explicit in Lean and then look for slack. They
come after A–F on purpose: none of them blocks Theorem 1.1. No item may claim a constant below
what its proof actually gives.

- [ ] G1. Parametric iteration arithmetic (`EntropyLean/RigidityArith.lean`): redo D1 with the
      Marton constant `C` and the constants of (36) as real parameters, deriving
      `d * logb 2 (1/λ) < K` for an explicit expression `K` in them
      (`rigidity_arith_param`), and recover D1 by `K ≤ 320` at `C = 6`
      (`rigidity_arith_param_six`).
- [ ] G2. Constant as a field: give D7's `MartonInput` its constant as a field `C` (with (36)
      in terms of `C`), and restate the conditional Theorem 1.1 of C2 with exponent
      `K(C) * (1+ε)/ε` (`exponential_entropy_quotient_of_rigidity_const`), so that any
      better Marton constant gives a better exponent with no further work.
- [ ] G3. Slack in the paper's argument: find the smallest constant `c₀` that the arithmetic of
      (42)–(43) gives at `C = 6` (prove `K(6) ≤ c₀`), and if `c₀ < 320` state Theorem 1.1
      with `c₀`. Record in this file where the slack came from, so Josiah can check it against
      the paper.
- [ ] G4. Constant from the PFR backend: only if B1 chooses PFR, check which Marton constant
      that project proves and instantiate G2 with it.

## Not attempted here

- Improving the constant beyond what the paper's argument gives (a new proof of Theorem 8.2 with
  a better iteration); item G only tracks and tightens the existing argument.

- A proof of the entropic Marton theorem itself (Gowers–Green–Manners–Tao); it is the paper's
  one external input.
- Constructive or algorithmic versions (Section 10).
