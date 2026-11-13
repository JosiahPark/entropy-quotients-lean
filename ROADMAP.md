# Roadmap

Ordered work list for formalizing arXiv:2610.38525. Items are sized for one change each
(roughly under 120 new Lean lines) and name their file and theorem names. Take the first
unchecked item; tick it (`- [x]`) only after CI shows it compiled. The dependency chart in
[docs/DEPENDENCIES.md](docs/DEPENDENCIES.md) shows how the items connect.

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
- [ ] A2. `entropyBits_pure`: `entropyBits (PMF.pure a) = 0`; `entropyBits_le_log_card`:
      `entropyBits P ≤ logb 2 (Fintype.card α)`.
  - Written by the hourly task 2026-11-13 (uncompiled at push): `entropyBits_pure`,
    `neg_mul_log_le_gibbs`, `pmf_sum_toReal`, `entropyBits_le_log_card`
    (`EntropyLean/EntropyFacts.lean`).
- [ ] A3. `entropyBits_map_le`: `H(f ∘ X) ≤ H(X)` for `PMF.map f` on finite types (data
      processing for a function); `entropyBits_map_injective`: equality for injective `f`.
- [ ] A4. `conv_map_hom`: for an additive map `q`, `(conv P Q).map q = conv (P.map q) (Q.map q)`
      (quotient commutes with convolution, used in Lemma 4.1).
- [ ] A5. `WeightedFamily.quotient_quotient`: quotienting by `G`, then by `W ≤ V ⧸ G`, equals
      quotienting by the inverse image of `W` (entropy-level statement), used in Lemma 9.1.

## B. Information-theory layer

- [ ] B1. Decide the entropy backend and record the decision here: (i) continue with the
      `PMF`-based definitions, or (ii) depend on the PFR project (github.com/teorth/pfr), which
      formalizes Shannon entropy, Ruzsa distance and an entropic PFR theorem. Check its
      toolchain against Lean 4.35.0 and whether its constant matches the 6 in (35). If (ii),
      prove `entropyBits` agrees with PFR's entropy divided by `log 2`.
- [ ] B2. Conditional entropy and mutual information for finite joint laws; chain rule;
      `I(A;B|C) ≥ 0` (`EntropyLean/Information.lean`).
- [ ] B3. Equation (9): `interaction_nonneg`, `interaction_le_left`, `interaction_le_right`;
      equation (14): `0 ≤ e(𝒫) ≤ h(𝒫)` (`meanInteraction_nonneg`, `meanInteraction_le`).
- [ ] B4. Equation (15): `meanEntropy_convFamily : h(𝒫 * 𝒫) = 2h(𝒫) − e(𝒫)`.
- [ ] B5. Data processing for the increment: `entropyIncrement_quotient_le : D(q_G X) ≤ D(X)`.
- [ ] B6. Lemma 2.1: `quotient_entropy_supermodular` (equation (11)).

## C. Variational steps and the reduction of Theorem 1.1

- [ ] C1. Lemma 9.1: prove `variational_sparsification` by minimizing `h(q_G 𝒫) + λ dim G`
      over the finite set of subspaces (needs A1, A5).
- [ ] C2. Conditional Theorem 1.1: `exponential_entropy_quotient_of_rigidity`, proving the
      statement of Theorem 1.1 from Lemma 9.1, B5, `entropy_le_increment_of_defect_le` and
      Theorem 8.2 taken as an explicit hypothesis. Also the singleton family
      `WeightedFamily.singleton` and `meanEntropy_singleton`.
- [ ] C3. Theorem 1.2 from Theorem 8.2: `sparse_rigidity_of_family_rigidity` via the singleton
      family (Theorem 8.2 as an explicit hypothesis).
- [ ] C4. Lemma 4.1: prove `ratio_preserving_sparsification` from the objective (24) (needs A4,
      B3, B4).
- [ ] C5. Corollary 9.2: statement, and its proof from Lemma 9.1, B5 and Theorem 8.2 as a
      hypothesis.

## D. Rigidity core (Sections 2.3, 3, 5–8)

- [ ] D1. Iteration arithmetic of Theorem 8.2, pure real analysis: from (43) derive
      `d * logb 2 (1/λ) < 320` for `0 < d ≤ 1` (`EntropyLean/RigidityArith.lean`).
- [ ] D2. Theorem 8.2 from Lemma 8.1: `weighted_family_rigidity_of_growth`, with Lemma 8.1 as an
      explicit hypothesis, using D1.
- [ ] D3. Posterior families: `WeightedFamily.posterior` and Lemma 2.2 (`posterior_closure`).
- [ ] D4. Lemma 3.1: fibring identity (20) and the nested inequality (22).
- [ ] D5. Lemma 5.1: averaged density estimate (28)–(29).
- [ ] D6. Lemma 6.1 (four-sample splitting), Lemma 6.2 (conditional BSG), Lemma 6.3.
- [ ] D7. `structure MartonInput`: the entropic Marton bound (35) as a named hypothesis, and its
      consequence (36). Replace by a theorem if B1 chooses the PFR backend and the constant
      matches.
- [ ] D8. Lemma 7.1 from D4–D7.
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

## Not attempted here

- A proof of the entropic Marton theorem itself (Gowers–Green–Manners–Tao); it is the paper's
  one external input.
- Constructive or algorithmic versions (Section 10).
