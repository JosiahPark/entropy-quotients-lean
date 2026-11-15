# EntropyLean: Lean 4 formalization of arXiv:2610.38525

Lean 4 / Mathlib formalization work for

> Josiah Park, *Dimension-free exponential entropy quotients over 𝔽₂*, arXiv:2610.38525v1 (28 Oct 2026).
> The paper is included at [`paper/2610.38525v1.pdf`](paper/2610.38525v1.pdf).

**Status: research blueprint, not a verified proof.** Theorems 1.1, 1.2, 8.2 and Proposition 9.3
are stated in Lean with `sorry`. Most of the paper's supporting results are proved without
`sorry`: Lemmas 2.1, 2.2, 3.1, 4.1, 5.1, 6.1–6.3 and 9.1; (36), Lemma 7.1 and Lemma 8.1 from the
entropic Marton theorem (35), the paper's one external input, which enters as a hypothesis
(`MartonInput V`, `MartonBound`); Theorem 8.2 from (35) for spaces in `Type`; and Theorems 1.1,
1.2 and Corollary 9.2 from Theorem 8.2. GitHub Actions compiles the project with Lean 4.35.0 and
Mathlib v4.35.0 on every push (see the Actions tab); the library first compiled at commit
`9130247`.

- [ROADMAP.md](ROADMAP.md): the ordered work list.
- [docs/DEPENDENCIES.md](docs/DEPENDENCIES.md): chart of how the paper's results depend on each
  other, coloured by Lean status (GitHub renders it as a diagram).

## Numerical constants

The table of constants is in [numerics/eq_constants/README.md](numerics/eq_constants/README.md),
section "Worst-case constants". For each constant of the paper it gives the worst case found
numerically on 𝔽₂ⁿ (n ≤ 5) and the output file that records it. For example, the worst cases found
are 1.17 for the Marton constant 6 in (35), 2.19 for the 3 of Lemma 6.3, and below 2 for the 320 of
Theorems 1.2 and 8.2. These are numerical observations by Grok, not proofs; rerunning three of the
scripts reproduced their outputs exactly. Everything Grok produced, including its report
(`grok_output.pdf`), is in [numerics/](numerics/README.md). The Bernoulli lower-bound table for
Proposition 9.3 is [docs/NUMERICAL_TABLE.md](docs/NUMERICAL_TABLE.md).

## Layout

| File | Contents | Proved |
| --- | --- | --- |
| `EntropyLean/Basic.lean` | Entropy in bits `H`, convolution, increment `D`, defect `E`, interaction `s`, subspace defect `F_P(W)`, single-law sparsity (eqs. (1), (6), (8), (10)) | `entropyBits_eq_sum`, `entropyDefect_eq` (`E = H − D`), `interaction_self` (`s(P,P) = E(P)`) |
| `EntropyLean/Families.lean` | Weighted families, `h(𝒫)`, `e(𝒫)`, `F_𝒫(W)`, averaged sparsity, quotient family `q_G 𝒫`, convolution family `𝒫 * 𝒫` (eqs. (12)–(13)) | `meanEntropy_quotient`, `conv_weights_sum` |
| `EntropyLean/Bernoulli.lean` | Binary entropy `h₂`, Bernoulli increment and defect (Prop. 9.3) | `binaryEntropy_eq_zero_of_not_mem`, `bernoulli_parameter_mem_Ioo` |
| `EntropyLean/Statements.lean` | Theorem 1.1, Theorem 1.2, Theorem 8.2, Lemma 4.1, Lemma 9.1, Proposition 9.3 | Lemma 4.1 and Lemma 9.1 (proofs in `RatioSparsification.lean` and `Variational.lean`) and the algebraic step `E ≤ θH ⇒ H ≤ (1+ε)D` (`entropy_le_increment_of_defect_le`); Theorems 1.1, 1.2, 8.2 and Proposition 9.3 are `sorry` |
| `EntropyLean/*.lean` (the other 41 files) | One file per roadmap item, from entropy facts (`EntropyFacts.lean`) to Lemma 8.1 (`RatioGrowthProof.lean`); each starts with a docstring saying what it proves and what it does not | see [ROADMAP.md](ROADMAP.md), which names the file and theorems of every item |
| `EntropyLean/FeatureMap.lean` | Separate p-frame symmetric-power feature map (not part of this paper; not imported by the root module `EntropyLean.lean`) | nothing (2 `sorry`) |
| `archive/` | The five original draft files, unchanged | — |
| `paper/` | The arXiv PDF | — |
| `missing/` | Draft declarations with no counterpart in the library, collected verbatim (not built) | — |
| `numerics/` | Grok's numerical and adversarial checks, with the table of constants (not built) | — |

## Changes in v0.2 (relative to the consolidated draft)

- `λ` is a reserved word in Lean 4; sparsity parameters are now named `lam`.
- Entropy is a `tsum`, so it is defined on quotients `V ⧸ G` without a `Fintype` instance; on finite types it equals the finite sum.
- Convolution is defined directly (`conv P Q = P.bind (fun a => Q.map (a + ·))`) instead of relying on a Mathlib `PMF.convolve`.
- Lemma 9.1 now states the full conclusion (`q_G 𝒫` is λ-sparse), and Lemma 4.1 includes the convolution-family clause (`𝒫₀ * 𝒫₀` is 4λ-sparse), using the new `WeightedFamily.quotient` and `WeightedFamily.convFamily`.
- Proposition 9.3 is stated as "for every `c < 2`, eventually `c ≤ ε log₂ C(ε)`", which is what `liminf ≥ 2` means. Lean's `liminf` on `ℝ` returns a junk value for functions unbounded above, so the `liminf` form could be false for the wrong reason.
- The Bernoulli placeholder target is replaced by a proved lemma.
- A CI workflow builds the library and the FeatureMap module and lists every `sorry`.

## Build

```sh
lake exe cache get
lake build
lake env lean EntropyLean/FeatureMap.lean
python3 scripts/audit_sorries.py
```

## Next proof work

See [ROADMAP.md](ROADMAP.md). Items A1–D9 are done (D9 compiled at `0440122`), apart from the
entropy-backend decision B1, which is Josiah's. Open: the universe transport (item D10), after
which Theorems 1.1 and 1.2 for `V : Type*` follow from (35) alone; Proposition 9.3 (section E);
and Corollary 9.4 (section F).
