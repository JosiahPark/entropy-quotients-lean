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
  - Note from Grok's report of 2026-11-15 ([numerics/](numerics/README.md)): the report states that
    PFR's entropic theorem has constant at most 6 (11/2 from GGMT's bound with `X₁ = X₂`), so
    (ii) would turn the hypothesis `MartonInput V` into a theorem. Not checked here; the toolchain
    check is still open.
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
- [x] D8. Lemma 7.1 (sparse posterior estimate, (37)): `e(𝒬) ≤ 36 J + 14 √ρ δH` for a `ρ`-sparse
      posterior family `𝒬 = Post 𝒫`, with the Marton bound as the hypothesis `MartonInput V`.
      Split by the formalize task 2026-11-15:
  - [x] D8a. Two laws `P`, `Q`: apply (36) to `K = P * Q`, then (21) and `s(q_W P, q_W Q) ≤
        H(q_W (P * Q))` give `s(P, Q) ≤ s_W(P, Q) + 12 D(P * Q)` with `dim W ≤ 13 (H(P) + H(Q))`
        (`EntropyLean/MartonStep.lean`, `interaction_le_subspace_add_increment`).
    - Written by the formalize task 2026-11-15 16:47 UTC (uncompiled at push):
      `interaction_quot_le_entropyBits_conv`, `interaction_le_subspace_add_increment` (a1b87ac).
      CI green at a1b87ac (checked in the same run).
  - [x] D8b. Average D8a over posterior pairs `(x, y)` with weights `m(x) m(y)` (`m = postMass`,
        all triples as in `meanInteraction_posterior_full`): choose `W(x, y)` by `Classical.choose`,
        then with `posterior_doubling` (34) get `e(𝒬) ≤ ∑ m(x) m(y) s_{W(x,y)}(Q_x, Q_y) + 36 J` and
        (38) `∑ m(x) m(y) dim W(x, y) ≤ 26 h(𝒬)` (`EntropyLean/SparsePosterior.lean`,
        `posterior_interaction_le_subspace`, `posterior_mean_dim_le`).
    - Written by the formalize task 2026-11-15 16:55 UTC (uncompiled at push): `postMass_nonneg`,
      `postSubspace`, `postSubspace_spec`, `posterior_interaction_le_subspace`,
      `posterior_mean_dim_le` (2861748). `W(x, y)` is `postSubspace P hM x y`. CI green at 2861748
      (checked in the same run; job log not readable, so linter warnings unchecked).
  - [x] D8c. Lemma 5.1 (`averaged_density_lemma`, (29)) for the `ρ`-sparse family `𝒬` with the
        subspace choice of D8b bounds the first term by `14 √ρ h(𝒬)`; with `meanEntropy_posterior`
        (`h(𝒬) = e(𝒫) = δH`) conclude `sparse_posterior_estimate` (37)
        (`EntropyLean/SparsePosterior.lean`).
    - Written by Claude 2026-11-15 17:25 UTC (uncompiled at push): `posterior_double_sum`,
      `sparse_posterior_estimate` (Lemma 7.1, (37): `e(Post 𝒫) ≤ 36 J + 14 √ρ e(𝒫)` for a `ρ`-sparse
      posterior family, `ρ ≥ 0`), `sparse_posterior_estimate_of_sparse` (the same for a `ρ`-sparse `𝒫`,
      via `posterior_closure`) (73b4d5b). CI green at 73b4d5b (checked in the same run). D8 ticked:
      the Marton bound (35) stays the hypothesis `MartonInput V`; L71 marked stated in
      docs/DEPENDENCIES.md.
- [x] D9. Lemma 8.1 from C4, D3, D6, D8.
  - Note from Grok's report of 2026-11-15 (L6): `WeightedFamily.posterior` exists only for
    `V : Type` (the index type of a `WeightedFamily` lives in `Type`), so D9 proves Lemma 8.1 only as
    `RatioGrowth.{0}` (`ratio_growth_of_marton`, 0440122); D10 lifts it to every universe.
  - Written 2026-11-15 18:26 UTC in 0440122 ("formalize: D9 ratio_growth_of_marton"; no note was
    added then): `ratio_growth_arith`, `WeightedFamily.isSparse_of_le`,
    `WeightedFamily.ratio_growth_of_marton` (Lemma 8.1 as `RatioGrowth.{0}` from
    `MartonBound.{0}`), `weighted_family_rigidity_of_marton` (`EntropyLean/RatioGrowthProof.lean`).
    CI green at 0440122 and at 9914c7d. Note and tick added by the formalize task 2026-11-15
    19:36 UTC (job log not readable, so linter warnings unchecked). D9 ticked: (35) stays the
    hypothesis `MartonBound.{0}`.
- [x] D10. Universe transport (Grok's report, L6; [numerics/](numerics/README.md)): the statements in
      `EntropyLean/Statements.lean` quantify over `V : Type*`, and
      `exponential_entropy_quotient_of_growth.{u}` needs `RatioGrowth.{u}`. Prove
      `RatioGrowth.{0} → RatioGrowth.{u}` by transport along linear equivalences
      `W ≃ₗ[ZMod 2] W'`: `h`, `e` and `F_𝒫(W)`, hence sparsity, are invariant for the pushed-forward
      family, and `ULift` carries the family returned by `RatioGrowth.{0}` into universe `u`
      (`EntropyLean/UniverseTransport.lean`, `ratioGrowth_lift`). Alternative: generalize
      `WeightedFamily.index` to `Type*`, which touches every file that uses families.
  - Written by the formalize task 2026-11-15 19:36 UTC (uncompiled at push):
    `entropyBits_map_linearEquiv`, `interaction_map_linearEquiv`, `finrank_comap_linearEquiv`,
    `quotientLoss_map_linearEquiv`, `WeightedFamily.mapLinearEquiv`,
    `WeightedFamily.meanEntropy_mapLinearEquiv`, `WeightedFamily.meanInteraction_mapLinearEquiv`,
    `WeightedFamily.averagedLoss_mapLinearEquiv`, `WeightedFamily.isSparse_mapLinearEquiv`,
    `ratioGrowth_lift` (via a basis `W ≃ₗ (Fin (dim W) → ZMod 2)` and `ULift`), and the corollaries
    `ratio_growth_of_marton_univ`, `weighted_family_rigidity_of_marton_univ`,
    `exponential_entropy_quotient_of_marton`, `sparse_rigidity_of_marton` (Lemma 8.1, Theorem 8.2
    and the statements of Theorems 1.1, 1.2 in every universe, with `MartonBound.{0}` as the only
    hypothesis) (`EntropyLean/UniverseTransport.lean`, 289e966; imported in `EntropyLean.lean`).
    First push failed CI (structure-instance indentation in `ratioGrowth_lift`); fixed in 1cb0c86,
    linter clean-up in b34f32d, CI green at both. D10 ticked: (35) stays the hypothesis
    `MartonBound.{0}`.

## E. Proposition 9.3 (independent of Theorem 8.2)

- [x] E1. `entropyBits` of a Bernoulli law on `ZMod 2` equals `binaryEntropy p`; the sum of two
      independent Bernoulli(p) bits is Bernoulli(2p(1−p)).
  - Written by the formalize task 2026-11-15 19:56 UTC (uncompiled at push): `zmod2_eq_zero_or_one`,
    `sum_zmod2_eq`, `bernoulliBit` (the law on `ZMod 2` with masses `1 − p`, `p`),
    `bernoulliBit_toReal_zero`, `bernoulliBit_toReal_one`, `entropyBits_bernoulliBit`,
    `bernoulliBit_param_nonneg`, `bernoulliBit_param_le_one`, `conv_bernoulliBit`,
    `entropyIncrement_bernoulliBit`, `entropyDefect_bernoulliBit`
    (`EntropyLean/BernoulliLaw.lean`, 8c02055; imported in `EntropyLean.lean`). CI green at 8c02055
    and 9f23ac6; ticked by the formalize task 2026-11-15 21:43 UTC.
- [x] E2. Bernoulli expansions: `binaryEntropy p = p logb 2 (1/p) + p logb 2 e + O(p²)` and
      `bernoulliDefect p = 2p + O(p² log(1/p))` as explicit inequalities for small `p`.
      Split by the formalize task 2026-11-15:
  - [x] E2a. `p logb 2 (1/p) + (p − p²)/log 2 ≤ h₂(p) ≤ p logb 2 (1/p) + p/log 2` and
        `2p − 2p² − 2p²/log 2 ≤ bernoulliDefect p` for `0 < p < 1`
        (`EntropyLean/BernoulliExpansion.lean`).
    - Written 2026-11-15 20:59 UTC in 7c68f07 (formalize: E2a; no note was added then):
      `bern_log_le_sub_one`, `one_sub_mul_log_one_sub_ge`, `one_sub_mul_log_one_sub_le`,
      `div_log2_le_div_log2`, `binaryEntropy_eq_nats`, `binaryEntropy_ge`, `binaryEntropy_le`,
      `bernoulli_q_pos`, `bernoulli_q_lt_one`, `bernoulliDefect_eq_nats`, `bernoulliDefect_ge`.
      CI green at 7c68f07 (linter: the `first` block in `bernoulliDefect_ge` can be `field_simp`
      alone; `if_pos` in `binaryEntropy_eq_nats` is deprecated). Note and tick added by the formalize
      task 2026-11-15 21:43 UTC.
  - [x] E2b. Upper bound `bernoulliDefect_le : bernoulliDefect p ≤ 2p + 2p² logb 2 (1/p) + 4p²/log 2`
        and the two-sided form `bernoulliDefect_sub_abs_le :
        |bernoulliDefect p − 2p| ≤ 2p² logb 2 (1/p) + 4p²/log 2` (`EntropyLean/BernoulliDefect.lean`).
    - Written by the formalize task 2026-11-15 21:35 UTC (uncompiled at push): `bern_div_le_add_div`,
      `bernoulliDefect_le`, `bern_logb_inv_nonneg`, `bern_sq_le_div_log_two`,
      `bernoulliDefect_sub_abs_le` (323be41; `BernoulliExpansion` and `BernoulliDefect` now imported
      in `EntropyLean.lean`). CI green at 323be41 (checked in the same run, no new warnings); BEXP
      marked proved in docs/DEPENDENCIES.md (46b5eae).
- [x] E3. Prove `exponential_scale_necessary` from E1, E2 and `bernoulli_parameter_mem_Ioo`.
  - Suggested route (formalize task 2026-11-15; not yet checked in Lean): only E1 and E2a are
    needed. Take `m = 1` and `X` the image of `bernoulliBit p` under the injective additive map
    `b ↦ fun _ => b`, so `H(X) = h₂(p)` and `E(X) = bernoulliDefect p`. For `G = ⊥`,
    `H(q_G X) = H(X)` and the hypothesis gives `(1 + ε) E(X) ≤ ε H(X)`, which fails for
    `p = 2^(−c/ε)`, `c < 2` and small `ε` (E2a: `E ≥ 2p − O(p²)`, `h₂(p) ≤ p (c/ε + 1/log 2)`). So
    `dim G ≥ 1`, `C(ε) ≥ 1/h₂(p)` and `ε log₂ C(ε) ≥ c − ε log₂(c/ε + 1/log 2)`, which tends to `c`.
      Split by the formalize task 2026-11-15:
  - [x] E3a. The one-bit example forces `dim G ≥ 1` (`EntropyLean/ScaleNecessary.lean`): `bitEmbed`,
        `bernoulliVec p` (law of `bernoulliBit p` on `F2Vec 1`) with `H = h₂(p)`, `E = bernoulliDefect p`;
        if `ε h₂(p) < (1+ε) bernoulliDefect p` then the hypothesis of Proposition 9.3 gives
        `1 ≤ C(ε) h₂(p)` (`one_le_C_mul_binaryEntropy`).
    - Written by the formalize task 2026-11-15 21:52 UTC (uncompiled at push): `bitEmbed`,
      `bitEmbed_injective`, `bernoulliVec`, `entropyBits_bernoulliVec`, `entropyDefect_bernoulliVec`,
      `dim_pos_of_defect_gt`, `one_le_C_mul_binaryEntropy` (d3bc836). CI green at d3bc836 (job log
      not readable, so linter warnings from the `first` blocks unchecked); ticked by the formalize
      task 2026-11-15 22:34 UTC.
  - [x] E3b. Real analysis (`EntropyLean/ScaleNecessaryLimit.lean`): for `0 < c < c' < 2` and
        `p = 2^(−c'/ε)`, eventually as `ε ↓ 0`: `ε h₂(p) < (1+ε) bernoulliDefect p`
        (`scale_gap_eventually`, from `binaryEntropy_le` and `bernoulliDefect_ge`) and
        `c ≤ −ε logb 2 (h₂(p))` (`scale_log_eventually`, from `binaryEntropy_le` and
        `ε logb 2 (c'/ε + 1/log 2) → 0`). Split further if over one run.
        Split by the formalize task 2026-11-15 (`p = scaleParam c' ε`):
    - [x] E3b1. `scaleParam a ε = 2^(−a/ε)` with `0 < p < 1`, `log₂(1/p) = a/ε`, `p · a · log 2 ≤ ε`,
          the explicit gap `scale_gap_of_le` and `scale_gap_eventually` (for `0 < a < 2`,
          eventually `ε h₂(p) < (1+ε) bernoulliDefect p`) (`EntropyLean/ScaleNecessaryLimit.lean`).
      - Written by the formalize task 2026-11-15 22:34 UTC (uncompiled at push): `scaleParam`,
        `scaleParam_pos`, `log_scaleParam`, `scaleParam_lt_one`, `logb_inv_scaleParam`,
        `scaleParam_mul_le`, `scale_eventually_of_lt`, `scale_gap_of_le`, `scale_gap_eventually`
        (5b0cb69). CI green at 5b0cb69 and e8a86b9. Linter (seen in the job log of the `formalize-efg`
        run at 38f8074, which builds the same file): unused `first` alternatives at lines 57, 71, 84,
        104 and deprecated `push_neg` at 44, 141. Ticked by the formalize task 2026-11-15 23:25 UTC.
    - [x] E3b2. `scale_log_eventually`: for `0 < a` and `c < a`, eventually
          `c ≤ −(ε logb 2 (h₂(scaleParam a ε)))` (`EntropyLean/ScaleNecessaryLog.lean`, importing
          `EntropyLean.ScaleNecessaryLimit`). Suggested route: for `ε ≤ 1/2`,
          `h₂(p) ≤ p (a + 1)/ε` (`binaryEntropy_le`, `half_le_log_two`); `x²/4 ≤ eˣ` (from
          `eˣ = (e^(x/2))²` and `1 + x/2 ≤ e^(x/2)`) gives `(a + 1)/ε ≤ exp((a − c) log 2 / ε)` once
          `16 ε (a + 1) ≤ (a − c)²`; then `ε log h₂(p) ≤ −c log 2`. Use `scale_eventually_of_lt`.
      - Written by the formalize task 2026-11-15 23:25 UTC (uncompiled at push): `slog_logb_scaleParam`,
        `slog_entropy_le`, `slog_entropy_pos`, `slog_small`, `scale_log_of_le`, `scale_log_eventually`
        (0f7ea55). The proofs are those of `ScaleNecessaryProof.lean` on branch `formalize-efg`
        (38f8074; that file compiled in the branch's CI run, which failed only in
        `CosetConcentration.lean`), with renamed declarations so that a later merge does not clash.
        They use `log x ≤ x − 1` instead of the `x²/4 ≤ eˣ` route above.
        CI green at 0f7ea55 (main) and at a3d1d61 (branch `formalize-efg-v2`, which builds this file
        and uses `scale_log_eventually` in E3c). Ticked by Claude 2026-11-15 23:35 UTC.
  - [x] E3c. `exponential_scale_necessary` from E3a and E3b: `C(ε) ≥ 1/h₂(p) > 0`, so
        `ε logb 2 (C ε) ≥ −ε logb 2 (h₂(p)) ≥ c` (for `c ≤ 0` use `c < c' := 1`). The proof goes in a
        new file (`exponential_scale_necessary_proof`) and `Statements.lean` then uses it, as for
        Lemma 9.1.
    - Written by Claude (desktop session) 2026-11-15 23:10 UTC: `exponential_scale_necessary_proof` (`EntropyLean/ScaleNecessaryProof.lean`, cfd43a4),
      with `a = (max(c, 1) + 2)/2`, from `scale_gap_eventually` (E3b1), `scale_log_eventually`
      (E3b2) and `one_le_C_mul_binaryEntropy` (E3a). `exponential_scale_necessary` in
      `EntropyLean/Statements.lean` is now this theorem, so Proposition 9.3 has no `sorry`; the
      open statements are Theorems 1.1, 1.2 and 8.2. `EntropyLean.lean` imports `ScaleNecessary`,
      `ScaleNecessaryLimit`, `ScaleNecessaryLog` and `ScaleNecessaryProof`. P93 marked proved in docs/DEPENDENCIES.md.
      CI green at a3d1d61 (branch `formalize-efg-v2`; same Lean files as cfd43a4); ticked by Claude 2026-11-15 23:35 UTC.

## F. Corollary 9.4

- [x] F1. Statement of Corollary 9.4 and its proof from Theorem 1.1 (as a hypothesis until
      Theorem 1.1 is proved).
  - Written by Claude (desktop session) 2026-11-15 23:10 UTC: `uniformFinset` (uniform law on a nonempty finset, `entropyBits_uniformFinset :
    H = log₂ |A|`), `entropyBits_le_logb_card_of_support`, `conv_uniformFinset_eq_zero`,
    `entropyIncrement_uniformFinset_le` (`D(X) ≤ (1 − η) log₂ |A|` when `|A + A| ≤ |A|^(2−η)`),
    `fibreCount`, `entropyBits_uniformFinset_quotient`
    (`H(q_G X) = log₂ |A| − (1/|A|) ∑_{a ∈ A} log₂ |A ∩ (a + G)|`),
    `coset_concentration_of_quotient` (Corollary 9.4 with the conclusion of Theorem 1.1 for a
    constant `K` as hypothesis `hT`; dimension bound `2^(K/α) log₂ |A|`),
    `exists_large_coset_of_quotient` (some coset meets `A` in at least `|A|^(η−α)` points), and
    `coset_concentration_of_marton`, `exists_large_coset_of_marton` (constant 320, hypothesis
    `MartonBound.{0}` only), `coset_concentration_311_of_marton`
    (`EntropyLean/CosetConcentration.lean`, cfd43a4). `|A ∩ (a + G)|` is written
    `(A.filter fun b => b - a ∈ G).card`. Corollary 9.4 is NOT proved unconditionally: Theorem 1.1
    enters as `hT` or through (35). C94 marked stated in docs/DEPENDENCIES.md.
    CI green at a3d1d61 (branch `formalize-efg-v2`; same Lean files as cfd43a4); ticked by Claude 2026-11-15 23:35 UTC.

## G. Tracking and improving the constant 320

The exponent `2^(320(1+ε)/ε)` in Theorem 1.1 comes from the iteration arithmetic (42)–(43)
(item D1) and, through it, from the constant 6 in the entropic Marton bound (35) and the constants
12, 13 in (36). These items make that dependence explicit in Lean and then look for slack. They
come after A–F on purpose: none of them blocks Theorem 1.1. No item may claim a constant below
what its proof actually gives.

- [x] G1. Parametric iteration arithmetic (`EntropyLean/RigidityArith.lean`): redo D1 with the
      Marton constant `C` and the constants of (36) as real parameters, deriving
      `d * logb 2 (1/λ) < K` for an explicit expression `K` in them
      (`rigidity_arith_param`), and recover D1 by `K ≤ 320` at `C = 6`
      (`rigidity_arith_param_six`).
  - Written by Claude (desktop session) 2026-11-15 23:10 UTC: the parameters are the two constants of Lemma 8.1, `a` (growth `d + d²/a`) and `b`
    (hypothesis `b λ ≤ d²`); the paper has `a = 148`, `b = 1600`. `rigidityConst a b =
    2(a + 1) + 2 + log₂ b`, `inv_ratio_step_param` (42), `rigidity_arith_param_aux`,
    `rigidity_arith_param` (if `0 < d ≤ 1`, `b ≥ 4` and `λ > d²/(b · 4^⌈(a+1)/d⌉)` then
    `d · logb 2 (1/λ) < rigidityConst a b`), `rigidityConst_paper_lt : rigidityConst 148 1600 <
    311`, `rigidity_arith_param_six` (D1's hypothesis gives `< 311`), `RatioGrowthConst a b`
    (Lemma 8.1 with constants; `RatioGrowth` is `RatioGrowthConst 148 1600`),
    `ratio_iteration_param`, `weighted_family_rigidity_of_growth_param` (Theorem 8.2 with constant
    `rigidityConst a b` from `RatioGrowthConst a b`), `exponential_entropy_quotient_of_growth_param`,
    `sparse_rigidity_of_growth_param` (`EntropyLean/RigidityArithParam.lean`, a new file,
    cfd43a4). How `a`, `b` depend on the Marton constant `C` is item G2
    (`a = 24C + 4`, `b = 32 (1 + C)²`).
    CI green at a3d1d61 (branch `formalize-efg-v2`; same Lean files as cfd43a4); ticked by Claude 2026-11-15 23:35 UTC.
- [x] G2. Constant as a field: give D7's `MartonInput` its constant as a field `C` (with (36)
      in terms of `C`), and restate the conditional Theorem 1.1 of C2 with exponent
      `K(C) * (1+ε)/ε` (`exponential_entropy_quotient_of_rigidity_const`), so that any
      better Marton constant gives a better exponent with no further work.
  - Written by Claude (desktop session) 2026-11-15 23:10 UTC, in three new files (cfd43a4); `MartonInput` itself is unchanged.
    `EntropyLean/RigidityConst.lean`: `WeightedFamilyRigidityConst K` (Theorem 8.2 with constant
    `K`; `WeightedFamilyRigidity` is the case 320), its monotonicity in `K`,
    `exponential_entropy_quotient_of_rigidity_const` (Theorem 1.1 with exponent `K(1+ε)/ε`) and
    `sparse_rigidity_of_family_rigidity_const`.
    `EntropyLean/MartonConst.lean`: `MartonInputConst C V`, `MartonBoundConst C` ((35) with
    constant `C`; `C = 6` is `MartonInput`, `MartonBound`), monotonicity in `C`, and
    `MartonInputConst.consequence`: (36) as `H(q_W K) ≤ 2C · D(K)`,
    `dim W ≤ H(K) + 2C · D(K) ≤ (1 + 2C) H(K)`.
    `EntropyLean/MartonChainConst.lean`: Sections 7–8 with `C ≥ 0`:
    `interaction_le_subspace_add_increment_const` (D8a), `density_sqrt_arith_param` and
    `averaged_density_sqrt_param` (Lemma 5.1 (29) as `B ≤ β h ⇒ A ≤ (1 + β/2) √λ h`),
    `sparse_posterior_estimate_const` (Lemma 7.1: `e(𝒬) ≤ 6C · J + (2 + 2C) √ρ · e(𝒫)`),
    `ratio_growth_arith_const`, `ratio_growth_of_marton_const` (Lemma 8.1 as
    `RatioGrowthConst.{0} (24C + 4) (32 (1 + C)²)`), `ratioGrowthConst_lift` (D10 for
    `RatioGrowthConst`), `martonRigidityConst C = 48C + 17 + 2 log₂(1 + C)`
    (`martonRigidityConst_eq`), `weighted_family_rigidity_of_marton_const` (Theorem 8.2 with that
    constant), `exponential_entropy_quotient_of_marton_const` and
    `sparse_rigidity_of_marton_const` (Theorems 1.1 and 1.2 with exponent
    `martonRigidityConst C · (1+ε)/ε`, in every universe, from `MartonBoundConst.{0} C`), and
    `martonRigidityConst_six_lt : martonRigidityConst 6 < 311`. At `C = 6` the hypothesis of
    Lemma 8.1 is `1568 λ ≤ d²` (the paper rounds `14√2` up to 20, giving 1600). No `C < 6` is
    claimed to be available.
    CI green at a3d1d61 (branch `formalize-efg-v2`; same Lean files as cfd43a4); ticked by Claude 2026-11-15 23:35 UTC.
- [x] G3. Slack in the paper's argument: find the smallest constant `c₀` that the arithmetic of
      (42)–(43) gives at `C = 6` (prove `K(6) ≤ c₀`), and if `c₀ < 320` state Theorem 1.1
      with `c₀`. Record in this file where the slack came from, so Josiah can check it against
      the paper.
  - Written by Claude (desktop session) 2026-11-15 23:10 UTC: `c₀ = rigidityConst 148 1600 = 300 + log₂ 1600`, with `310 < c₀ < 311`
    (`rigidityConst_paper_eq`, `rigidityConst_paper_gt`, `rigidityConst_paper_lt`).
    `weighted_family_rigidity_slack_of_growth` (Theorem 8.2 with `c₀` from `RatioGrowth`),
    `weighted_family_rigidity_311_of_growth`, `weighted_family_rigidity_311_of_marton`,
    `exponential_entropy_quotient_311_of_marton` (Theorem 1.1 with `dim G ≤ 2^(311(1+ε)/ε) H(X)`),
    `sparse_rigidity_311_of_marton`, and the same from `MartonBoundConst C` with `C ≤ 6`
    (`EntropyLean/ConstantSlack.lean`, cfd43a4). The open statements in `Statements.lean` keep 320.
    Where the slack comes from, for Josiah to check against the paper: (i) the paper bounds
    `d log₂(1/λ) < 298 + (log₂ 1600 + 2) d + 2 d log₂(1/d)` and estimates the last two terms
    separately (`d ≤ 1`, `d log₂(1/d) ≤ 1/(e ln 2)`), getting `< 312`; for `d ≤ 1` their sum is at
    most `log₂ 1600 + 2`, its value at `d = 1` (from `−d log d ≤ 1 − d` and
    `log 1600 + 2 log 2 ≥ 2`), which gives `300 + log₂ 1600 ≈ 310.64`; (ii) the paper then rounds
    312 up to 320. Not formalized: that `c₀` is the supremum of `d log₂(1/λ)` under the
    hypothesis of (43) (approached as `d ↑ 1`). With the parametric chain of G2 the hypothesis
    `1568 λ ≤ d²` gives `305 + 2 log₂ 7 ≈ 310.61`, still 311 as an integer.
    CI green at a3d1d61 (branch `formalize-efg-v2`; same Lean files as cfd43a4); ticked by Claude 2026-11-15 23:35 UTC.
- [ ] G4. Constant from the PFR backend: only if B1 chooses PFR, check which Marton constant
      that project proves and instantiate G2 with it.
  - Not attempted (Claude, 2026-11-15): B1 is undecided. Once a constant `C` is available as
    `MartonBoundConst.{0} C`, `exponential_entropy_quotient_of_marton_const` (G2) gives Theorem 1.1
    with exponent `(48C + 17 + 2 log₂(1 + C))(1+ε)/ε`; for `C = 11/2` that constant is about 286.4.

## H. Toward green: the Marton frontier

Added by the formalize task 2026-11-15 (no unchecked item was actionable: B1 is Josiah's
decision and G4 waits for it). Every amber node of docs/DEPENDENCIES.md (E36, L71, L81, T82, T12,
T11, C92, C94) is already proved in Lean from the single hypothesis `MartonBound.{0}` (35), so the
remaining distance to green is the external node MAR. These items make that visible and prove
the cases of (35) that need no new ideas. None of them proves the entropic Marton theorem, and
none may add a `sorry` to `Statements.lean`.

- [x] H1. Chart: add a class `conditional` ("proved in Lean from (35) as a hypothesis") to
      docs/DEPENDENCIES.md, move E36, L71, L81, T82, T12, T11, C92, C94 to it, and put the Lean
      names in their labels (`MartonInput.consequence`, `sparse_posterior_estimate`,
      `ratio_growth_of_marton`, `weighted_family_rigidity_of_marton_univ`,
      `sparse_rigidity_of_marton`, `exponential_entropy_quotient_of_marton`,
      `coset_concentration_of_marton`). Docs only; no Lean change.
  - Written by the formalize task 2026-11-16 03:45 UTC (uncompiled at push): docs/DEPENDENCIES.md now has
    class `conditional` (lilac, with a legend row and a note under "Reading the chart"); E36, L71, L81,
    T82, T12, T11, C92, C94 moved to it with the Lean names above (C92 as
    `two_input_almost_additivity_of_rigidity` + `weighted_family_rigidity_of_marton_univ`) (4d14fc1).
    No node is `stated` any more; the open `sorry`s are the statements of Theorems 1.1, 1.2, 8.2 in
    `Statements.lean` (3) and `FeatureMap.lean` (2).
    CI green at 4d14fc1 (docs only); ticked by the formalize task 2026-11-16 03:51 UTC.
- [x] H2. Trivial subspaces (`EntropyLean/MartonPartial.lean`): `ruzsaDist_uniformSub_bot :
      d(K, U_⊥) = H(K)/2` and `ruzsaDist_uniformSub_top : d(K, U_⊤) = (dim V − H(K))/2` (from
      `ruzsaDist_uniformSub`, D7b2b), hence `marton_of_entropy_le : H(K) ≤ 12 D(K) → ∃ W, d(K, U_W) ≤
      6 D(K)` and `marton_of_codim_le : dim V − H(K) ≤ 12 D(K) → ∃ W, d(K, U_W) ≤ 6 D(K)`.
  - Written by the formalize task 2026-11-16 03:51 UTC (uncompiled at push): `entropyBits_map_mkQ_bot`,
    `entropyBits_map_mkQ_top`, `ruzsaDist_uniformSub_bot`, `ruzsaDist_uniformSub_top`,
    `marton_of_entropy_le`, `marton_of_codim_le` in the new file `EntropyLean/MartonPartial.lean` (6b740e5).
    CI green at 6b740e5; ticked by the formalize task 2026-11-16 04:00 UTC (unused `first` fallbacks removed in 082b63e).
- [x] H3. Zero doubling (`EntropyLean/MartonPartial.lean`): if `D(K) = 0` then (35) holds, i.e.
      `K` is uniform on a coset `x + W` and `d(K, U_W) = 0` (`marton_of_increment_zero`). Split by
      the formalize task 2026-11-16 04:00 UTC (there is no equality-case lemma for entropy in the
      repository yet, so the original H3a/H3b plan was too large for one run):
  - [x] H3a. Support of a convolution: `lawSupport K = {v : K v ≠ 0}`, `mem_support_conv_iff`,
        `lawSupport_conv : lawSupport (P * Q) = lawSupport P + lawSupport Q`.
    - Written by the formalize task 2026-11-16 04:00 UTC (uncompiled at push): `mem_support_conv_iff`,
      `lawSupport`, `mem_lawSupport`, `lawSupport_nonempty`, `lawSupport_conv` in
      `EntropyLean/MartonPartial.lean` (082b63e).
      CI green at 4a86741; ticked by the formalize task 2026-11-16 04:18 UTC (fallbacks removed in a83d9f2).
  - [x] H3b. Equality case of subadditivity (`EntropyLean/Information.lean` or a new file):
        `mutualInfo P = 0 → P = prodLaw (P.map Prod.fst) (P.map Prod.snd)` (`eq_prodLaw_of_mutualInfo_eq_zero`),
        via the equality case of Jensen for `−x log x` (`StrictConcaveOn.map_sum_eq_iff`).
    - Written by the formalize task 2026-11-16 04:18 UTC (uncompiled at push): `crossSlack`,
      `crossSlack_nonneg`, `crossSlack_eq_zero`, `sum_crossSlack`, `eq_prodLaw_of_mutualInfo_eq_zero` in the
      new file `EntropyLean/MutualInfoZero.lean` (a83d9f2); proved via the strict bound `log y < y − 1`
      on the pointwise Gibbs slack rather than via Jensen.
      CI green at 368970f (after a fix: `div_add_div_same` unknown, replaced by `add_div`/`sub_div`);
      ticked by the formalize task 2026-11-16 04:48 UTC.
  - [x] H3c. Translates: `D(K) = 0 → ∀ b, K b ≠ 0 → K.map (· + b) = conv K K`
        (`map_add_eq_conv_of_increment_zero`), from H3b applied to the pair `(B, A + B)`, whose mutual
        information is `H(K * K) − H(K) = D(K)`.
    - Written by the formalize task 2026-11-16 04:48 UTC (uncompiled at push): `mutualInfo_snd_add`,
      `toReal_sub_eq_conv_of_increment_zero`, `map_add_eq_conv_of_increment_zero` in
      `EntropyLean/MartonPartial.lean` (ec62d4b; the file now imports `EntropyLean.MutualInfoZero`).
      CI green at ec62d4b and 13b417d (no `MartonPartial.lean` warnings besides the module notice);
      ticked by the formalize task 2026-11-16 05:33 UTC.
  - [x] H3d. `S = lawSupport K` is a coset `x + W` of a subspace and `K` is uniform on it, hence
        `d(K, U_W) = 0` and `marton_of_increment_zero` (uses H3a to get `S + S = S + b`).
    - Written by the formalize task 2026-11-16 05:33 UTC (uncompiled at push): `lawPeriods`,
      `mem_lawPeriods`, `pmf_map_add_neg_apply`, `pmf_map_add_neg_apply_of_mem`, `lawPeriodSub`,
      `mem_lawPeriodSub`, `apply_sub_eq_of_increment_zero`, `sub_mem_lawPeriods`,
      `mem_lawSupport_iff_of_increment_zero`, `pmf_map_add_neg_apply_of_not_mem`,
      `map_add_neg_eq_uniformSub_of_increment_zero`, `ruzsaDist_lawPeriodSub_of_increment_zero`,
      `marton_of_increment_zero` in `EntropyLean/MartonPartial.lean` (b6ea618). `W` is the
      subspace of periods of `K` (via `AddSubgroup.toZModSubmodule`); for `x` in the support,
      `K − x = U_W`, so `d(K, U_W) = d(K, K − x) = D(K) = 0` by translation invariance (no entropy
      computation and no use of H3a needed).
      CI green at ec3c48f (contains b6ea618; no `MartonPartial.lean` warnings besides the module notice);
      ticked by the formalize task 2026-11-16 05:53 UTC. With H3a–H3d done, H3 is complete.
- [ ] H4. One-bit spaces (`EntropyLean/MartonPartial.lean`): `martonInput_of_finrank_le_one :
      finrank V ≤ 1 → MartonInput V`, from H2 and the Bernoulli bounds of E1–E2
      (`min(h₂(p), 1 − h₂(p)) ≤ 12 (h₂(2p(1−p)) − h₂(p))`). If the real-analysis inequality does
      not close in one run, prove it for `p ≤ 1/8` first and record the gap. Split by the formalize
      task 2026-11-16 05:53 UTC:
  - [ ] H4a. Reduction (`EntropyLean/MartonOneBit.lean`): `martonInput_of_finrank_eq_zero`, invariance of
        `H` and `D` under an additive equivalence, `eq_bernoulliBit` (every law on `ZMod 2` is
        Bernoulli), and `martonInput_of_finrank_eq_one_of_bernoulli` ((35) on a one-dimensional space
        from the Bernoulli inequality as an explicit hypothesis `hB`).
    - Written by the formalize task 2026-11-16 05:53 UTC (uncompiled at push): `martonInput_of_finrank_eq_zero`,
      `entropyBits_map_addEquiv`, `entropyIncrement_map_addEquiv`, `eq_bernoulliBit`,
      `martonInput_of_finrank_eq_one_of_bernoulli` in the new file `EntropyLean/MartonOneBit.lean` (1f3879f).
  - [ ] H4b. The Bernoulli inequality (`EntropyLean/MartonOneBit.lean` or a new file): `bernoulli_marton_ineq :
        0 ≤ p → p ≤ 1 → min (binaryEntropy p) (1 − binaryEntropy p) ≤ 12 * bernoulliIncrement p`;
        if it does not close in one run, prove the range `p ≤ 1/8` (and its mirror `p ≥ 7/8`) first.
  - [ ] H4c. `martonInput_of_finrank_le_one : finrank V ≤ 1 → MartonInput V`, from H4a and H4b.
- [ ] H5. PFR-strength constant, arithmetic only (`EntropyLean/ConstantSlack.lean` or a new file
      `EntropyLean/MartonConstPFR.lean`): `martonRigidityConst_eleven_half_lt :
      martonRigidityConst (11/2) < 287` and `exponential_entropy_quotient_287_of_marton_const`
      (Theorem 1.1 with exponent `287(1+ε)/ε` from `MartonBoundConst.{0} (11/2)`). This does not
      depend on B1: it only says what a proof of (35) with constant 11/2 would give.

## Not attempted here

- Improving the constant beyond what the paper's argument gives (a new proof of Theorem 8.2 with
  a better iteration); item G only tracks and tightens the existing argument.

- A proof of the entropic Marton theorem itself (Gowers–Green–Manners–Tao); it is the paper's
  one external input.
- Constructive or algorithmic versions (Section 10).
