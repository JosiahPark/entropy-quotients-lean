# Parallel formalization efforts (Grok)

Two independent attempts at the same task ran as hourly Grok tasks named "Lean Formalization:
Entropy Quotients (2610.38525)". Their progress reports are recorded below, lightly cleaned of
interface text, so they can be compared with this repository. **Their Lean files are not in this
repository**: they lived in Grok's own workspaces (`/workspace/artifacts/...` and
`entropy_quotients/`), which this project cannot read. Nothing below has been checked by this
project's CI.

The task prompt both runs received:

> Continue Lean formalization of the paper arXiv:2610.38525 (Dimension-free exponential entropy
> quotients over F_2 by Josiah Park). Formalize Theorem 1.1 (the exponential entropy quotient), the
> logarithmic rigidity estimate for weighted families, the variational quotient control, and the
> necessity of the exponential scale (Proposition 9.3). Produce or update Lean code for the next
> tractable statement or lemma, report progress, and note any blockers. Work independently of other
> formalization tasks. Don't keep doing the exact same thing, if you hit a roadblock, add new
> features and try new things to keep moving on.

## How they compare with this repository

| Result | This repo (`EntropyLean/Statements.lean`) | Grok run 1 | Grok run 2 |
| --- | --- | --- | --- |
| Theorem 1.1 | stated, `sorry` (`exponential_entropy_quotient`) | stated, `sorry` | stated, proof deferred |
| Theorem 1.2 | stated, `sorry` (`sparse_rigidity`) | stated, `sorry` (`sparse_law_rigidity`) | stated, proof deferred |
| Theorem 8.2 | stated, `sorry` (`weighted_family_rigidity`) | listed as next step | stated, proof deferred |
| Lemma 4.1 | stated, `sorry` (`ratio_preserving_sparsification`, `2λ`/`4λ`) | not stated | stated (`2λ`/`4λ`) |
| Lemma 9.1 | stated, `sorry` (`variational_sparsification`) | stated, `sorry` | stated, proof deferred |
| Proposition 9.3 | stated, `sorry` (`exponential_scale_necessary`, eventual form of the liminf) | stated with `liminf`, `sorry` (`necessity_exponential_scale`) | stated with `liminf` |
| Entropy facts | A1 compiled (`entropyBits_nonneg`); A2 compiled (`entropyBits_pure`, `entropyBits_le_log_card`) | none | none |
| Built by CI | yes, Lean 4.35.0 + Mathlib | no (no Lean in its environment) | without Mathlib; analytic infrastructure axiomatized |

Notes for this project:

- Neither run proved anything beyond statements. Run 2 says its analytic infrastructure is
  "axiomatized", which this project's rules forbid; none of it should be imported here.
- Both state Proposition 9.3 with `liminf`. This repository deliberately uses the eventual form
  ("for every `c < 2`, eventually `c ≤ ε log₂ C(ε)`") to avoid `liminf`'s junk value for functions
  unbounded above. Keep it.
- Run 1 suggests importing convolution and quotient lemmas from the PFR project. That is roadmap
  item B1 (Josiah's decision).
- Their suggested next steps match roadmap items E1–E3 (Bernoulli expansions for Proposition 9.3),
  A3–A4 (push-forwards and quotients), B2 (entropy over probability laws) and C1 (Lemma 9.1).

## Grok run 1: "Lean Formalization of Park Entropy Quotients Theorem 1.1"

Thought for 2m 11s.

Progress update on the Lean formalization of arXiv:2610.38525 (Park).

I have set up a self-contained starting point under
`/workspace/artifacts/lean_formalization/ParkEntropyQuotients/`. The files contain precise
statements of the requested results (with `sorry`s) plus the supporting definitions needed to make
them type-check against Mathlib (or the PFR project).

**Formalized statements**

- Theorem 1.1 (`exponential_entropy_quotient`): the main dimension-free result
  dim G ≤ 2^(320(1+ε)/ε) H(X) and H(q_G X) ≤ (1+ε) D(q_G X) ≤ (1+ε) D(X).
- Logarithmic rigidity (Theorem 1.2, `sparse_law_rigidity`): every λ-sparse law satisfies
  E(Z)/H(Z) ≤ min{1, 320/log₂(1/λ)}.
- Variational quotient control (Lemma 9.1, `variational_sparsification`): for any finite weighted
  family 𝒫 and λ > 0 there exists G with dim G ≤ h(𝒫)/λ such that the quotient family is λ-sparse.
- Necessity of the exponential scale (Proposition 9.3, `necessity_exponential_scale`): any
  universally valid coefficient C(ε) satisfies liminf_{ε↓0} ε log₂ C(ε) ≥ 2.

Supporting material includes the definitions of `entropyBits`, D, E, `IsSparse`, and
`WeightedFamily`/`meanEntropy`, plus a skeleton file `BernoulliCalculations.lean` containing the
asymptotic expansions of binary entropy that drive the proof of Prop. 9.3.

**Next tractable items**

1. Complete the Bernoulli expansions (standard Taylor analysis with remainder) so that Prop. 9.3
   becomes a fully formal theorem depending only on Mathlib.
2. Add the basic lemmas on entropy of convolutions and push-forwards under quotient maps (these can
   largely be imported from the existing PFR formalization).
3. State the weighted-family rigidity theorem (Theorem 8.2) once the single-law case is in place.

**Blockers**

- Lean 4 + Mathlib is not present in the current environment, so the files cannot yet be compiled
  here. They are written to drop into a standard Mathlib project (or into `teorth/pfr`).
- A complete proof of Theorem 1.1 still requires the entropic Marton theorem (already available in
  the PFR repository) together with the technical apparatus of posterior families, local-to-global
  estimates, and ratio-growth lemmas; none of those have been stated yet.

A short README with the same information is also present at
`/workspace/artifacts/lean_formalization/README.md`.

## Grok run 2: "Lean Formalization of Exponential Entropy Quotients"

Thought for 5m 36s.

Progress on the Lean formalization of arXiv:2610.38525.

A Lean 4.35.0 project skeleton has been created at `entropy_quotients/` and builds successfully.
The principal results of the paper have been recorded as precise statements (with proofs
deferred).

**Formalized statements** (in `EntropyQuotients/MainTheorems.lean`)

- Theorem 1.1 (exponential entropy quotient): existence of a subspace G with
  dim G ≤ 2^(320(1+ε)/ε) H(X) such that H(q_G X) ≤ (1+ε) D(q_G X) ≤ (1+ε) D(X).
- Logarithmic rigidity (Theorems 1.2 / 8.2): every λ-sparse law or weighted family with positive
  (mean) entropy satisfies E/H ≤ min{1, 320/log₂(1/λ)}.
- Variational quotient control:
  - Lemma 4.1 (ratio-preserving sparsification): a common quotient controls both a family and its
    convolution without decreasing the defect ratio, at multiplicative sparsity cost 2λ and 4λ.
  - Lemma 9.1 (variational sparsification): any family admits a quotient of dimension ≤ h(𝒫)/λ
    that is λ-sparse.
- Proposition 9.3 (necessity of the exponential scale): any coefficient C(ε) valid for all laws
  must satisfy liminf_{ε↓0} ε log₂ C(ε) ≥ 2.

**Blockers**

- Mathlib cannot be fetched: `lake` fails with a git partial-clone I/O error on `.git/config`.
- Without Mathlib the ordered field structure on ℝ, probability measures, and concrete
  F₂-vector spaces (`Fin m → ZMod 2`) are unavailable. All analytic infrastructure is therefore
  currently axiomatized or recorded only as documentation.

**Next tractable steps (once Mathlib is available)**

1. Define laws as probability measures on `Fin m → ZMod 2` and implement Shannon entropy together
   with the increment/defect D(X), E(X).
2. Prove the elementary subspace-entropy inequality and posterior-closure lemma.
3. Formalize the variational sparsification (Lemma 9.1), which is the most elementary structural
   result (minimization of a submodular set function).
4. Proceed to the ratio-growth argument that yields the logarithmic rigidity theorems.

The project builds cleanly in its present form. The full mathematical claims of the paper are
recorded and ready for proof development as soon as the analytic library becomes accessible.
