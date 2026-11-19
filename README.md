# EntropyLean: Lean 4 formalization of arXiv:2610.38525

Lean 4 / Mathlib formalization work for

> Josiah Park, *Dimension-free exponential entropy quotients over 𝔽₂*, arXiv:2610.38525v1 (28 Oct 2026).
> The paper is included at [`paper/2610.38525v1.pdf`](paper/2610.38525v1.pdf).

**Status: Theorems 1.1, 1.2 and 8.2 are proved in Lean, with no `sorry` and no hypothesis.** So
is every other result in the dependency chart: Lemmas 2.1, 2.2, 3.1, 4.1, 5.1, 6.1–6.3, 7.1, 8.1
and 9.1, equation (36), Corollaries 9.2 and 9.4, and Proposition 9.3 (`EntropyLean/Statements.lean`
states the main ones). The paper's one external input, the entropic Marton theorem (35) of
Gowers, Green, Manners and Tao, is not reproved here: it comes from the Lean proof in the
[PFR project](https://github.com/teorth/pfr), which this repository imports and translates to its
own definitions (`EntropyLean/PFRBridge.lean`). The build fails if one of the main results
depends on `sorry` or on an axiom other than Lean's standard `propext`, `Classical.choice` and
`Quot.sound`. The Lean statements were checked against the paper but have not been independently
reviewed. GitHub Actions compiles the project with Lean 4.35.0 and Mathlib v4.35.0 on every push
(see the Actions tab); the library first compiled at commit `9130247`.

- [ROADMAP.md](ROADMAP.md): the ordered work list.
- [docs/DEPENDENCIES.md](docs/DEPENDENCIES.md): chart of how the paper's results depend on each
  other, coloured by Lean status (GitHub renders it as a diagram).
- [docs/THEOREMS.md](docs/THEOREMS.md): the full theorem list, every theorem and lemma of the
  library by file, each with a link to its source line.

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
| `EntropyLean/Statements.lean` | Theorem 1.1, Theorem 1.2, Theorem 8.2, Lemma 4.1, Lemma 9.1, Proposition 9.3; with no hypothesis, (36), Lemmas 7.1 and 8.1, Corollaries 9.2 and 9.4 | All of them. Theorems 1.1, 1.2 and 8.2 from `martonBound`; the file ends with checks that fail the build if one of its theorems depends on `sorry` or on a non-standard axiom |
| `EntropyLean/PFRBridge.lean` | The entropic Marton bound (35) from the PFR project | `martonBound` ((35) with the paper's constant 6) and `martonBoundConst_five` (constant 5), and the agreement of PFR's entropy, Ruzsa distance and uniform variables with the ones used here (roadmap item B1) |
| `EntropyLean/*.lean` (the other files) | One file per roadmap item, from entropy facts (`EntropyFacts.lean`) to Lemma 8.1 (`RatioGrowthProof.lean`); each starts with a docstring saying what it proves and what it does not | see [ROADMAP.md](ROADMAP.md), which names the file and theorems of every item, and [docs/THEOREMS.md](docs/THEOREMS.md), which lists every theorem |
| `EntropyLean/MathlibForPFR.lean` | The import list of Mathlib without the six modules whose declarations have the same names as declarations of the PFR project; the library files import it in place of `import Mathlib` (roadmap item B1d1) | nothing (imports only) |
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
node scripts/theorem_list.js > docs/THEOREMS.md   # regenerate the theorem list
```

The build also compiles the part of the PFR project that the library imports (roadmap item B1);
`lake exe cache get` only fetches Mathlib.

A library file imports `EntropyLean.MathlibForPFR`, not `Mathlib`. PFR and Mathlib declare four
names in common, so no file can import both; `EntropyLean/MathlibForPFR.lean` is Mathlib without
the six modules involved (roadmap item B1d1). `FeatureMap.lean` is the exception and still
imports `Mathlib`.

## Next proof work

See [ROADMAP.md](ROADMAP.md). Every item is done. Besides the paper's results, two
improvements of the constant 320 are proved from (35): 311 (`EntropyLean/ConstantSlack.lean`), and
`48C + 17 + 2 log₂(1 + C)` for a Marton constant `C` in place of 6
(`EntropyLean/MartonChainConst.lean`).

The entropic Marton bound (35) is taken from the [PFR project](https://github.com/teorth/pfr),
pinned to PFR's last commit on Lean v4.35.0 (roadmap item B1). PFR proves it, with constant 5, for
random variables on a probability space. `EntropyLean/PFRBridge.lean` translates PFR's entropy,
Ruzsa distance and uniform variables to the `PMF`-based definitions used here, and proves
`martonBound`, the bound with the paper's constant 6, with no hypothesis. One generalization is
pending and not scheduled (G4 in ROADMAP.md): PFR's constant 5 would replace 320 by 263 in
Theorems 1.1, 1.2 and 8.2.
