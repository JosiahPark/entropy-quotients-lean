# EntropyLean: Lean 4 formalization of arXiv:2610.38525

Lean 4 / Mathlib formalization work for

> Josiah Park, *Dimension-free exponential entropy quotients over 𝔽₂*, arXiv:2610.38525v1 (28 Oct 2026).
> The paper is included at [`paper/2610.38525v1.pdf`](paper/2610.38525v1.pdf).

**Status: research scaffold, not a verified proof.** The main results are stated in Lean with
`sorry`; only definitions and elementary identities are proved. GitHub Actions compiles the
project with Lean 4.35.0 and Mathlib v4.35.0 on every push (see the Actions tab); the library
first compiled at commit `9130247`.

- [ROADMAP.md](ROADMAP.md): the ordered work list.
- [docs/DEPENDENCIES.md](docs/DEPENDENCIES.md): chart of how the paper's results depend on each
  other, coloured by Lean status (GitHub renders it as a diagram).

## Layout

| File | Contents | Proved |
| --- | --- | --- |
| `EntropyLean/Basic.lean` | Entropy in bits `H`, convolution, increment `D`, defect `E`, interaction `s`, subspace defect `F_P(W)`, single-law sparsity (eqs. (1), (6), (8), (10)) | `entropyBits_eq_sum`, `entropyDefect_eq` (`E = H − D`), `interaction_self` (`s(P,P) = E(P)`) |
| `EntropyLean/Families.lean` | Weighted families, `h(𝒫)`, `e(𝒫)`, `F_𝒫(W)`, averaged sparsity, quotient family `q_G 𝒫`, convolution family `𝒫 * 𝒫` (eqs. (12)–(13)) | `meanEntropy_quotient`, `conv_weights_sum` |
| `EntropyLean/Bernoulli.lean` | Binary entropy `h₂`, Bernoulli increment and defect (Prop. 9.3) | `binaryEntropy_eq_zero_of_not_mem`, `bernoulli_parameter_mem_Ioo` |
| `EntropyLean/Statements.lean` | Theorem 1.1, Theorem 1.2, Theorem 8.2, Lemma 4.1, Lemma 9.1, Proposition 9.3 | only the algebraic step `E ≤ θH ⇒ H ≤ (1+ε)D` (`entropy_le_increment_of_defect_le`); the six results are `sorry` |
| `EntropyLean/FeatureMap.lean` | Separate p-frame symmetric-power feature map (not part of this paper; not imported by the library) | nothing (2 `sorry`) |
| `archive/` | The five original draft files, unchanged | — |
| `paper/` | The arXiv PDF | — |

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

See [ROADMAP.md](ROADMAP.md). The first items are entropy nonnegativity and data processing
(section A), then the conditional reduction of Theorem 1.1 to Theorem 8.2 (item C2) and the
iteration arithmetic of Theorem 8.2 (item D1).
