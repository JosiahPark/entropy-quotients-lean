# EntropyLean — consolidated Lean 4 draft

This repository consolidates five supplied Lean files into **one entropy-quotient development**, plus an **independent p-frame feature-map module**. It is a research scaffold, **not a verified formal proof** of the results in arXiv:2610.38525.

## Layout

| File | Purpose |
| --- | --- |
| `EntropyLean/Basic.lean` | PMF entropy in bits, increment, defect, quotient loss, single-law sparsity |
| `EntropyLean/Families.lean` | Finite weighted families, mean entropy, interaction, averaged sparsity |
| `EntropyLean/Bernoulli.lean` | One Bernoulli entropy definition and lower-bound proof targets |
| `EntropyLean/Statements.lean` | Main outstanding entropy quotient and rigidity proof targets |
| `EntropyLean/FeatureMap.lean` | Separate p-frame symmetric-power work (not imported by main library) |
| `archive/` | The five original inputs, preserved unchanged |

## Important corrections and limits

- **Naming fixed:** `entropyIncrement X = H(X+X')−H(X)`, and `entropyDefect X = 2H(X)−H(X+X')`. Source drafts disagreed and sometimes swapped their theorem uses.
- **No vacuous results:** the `True`-only “theorems” and dummy quotient-family expressions were removed, rather than counted as formalized mathematics.
- **No synthetic axioms:** the abstract `opaque` convolution/entropy definitions were replaced by PMF operations (subject to Lean elaboration verification).
- **Incomplete statements:** the Lemma 4.1 convolution-family condition, Lemma 9.1 projected sparsity clause, and Proposition 9.3 general liminf necessity argument are not claimed as completed. They require proper additional definitions and an audit against the paper.
- **Proof status:** `sorry` occurrences are explicit proof obligations, not proofs. Mathlib compatibility and the complete build **have not been verified** in this environment (no `lean` / `lake` executable available).
- **Feature-map caveat:** the proposed map with target dimension `choose (d + m − 1) m` is mathematically a useful model, but its Euclidean normalization/inner-product identity still needs construction and proof.

## Build (requires Lean 4 / elan and network for first Mathlib setup)

```sh
lake update
lake exe cache get
lake build
lake env lean EntropyLean/FeatureMap.lean
python3 scripts/audit_sorries.py
```

The `lean-toolchain` and Mathlib revision are pinned to v4.35.0 based on a **claim in the supplied progress file**, not a verified toolchain installation. If Mathlib revision is unavailable or incompatible, select a confirmed supported Lean–Mathlib pair before treating build output as valid.

## Next proof work

1. Verify Mathlib PMF `map` / `convolve`, quotient finiteness, and `Module.finrank` against the pinned API; repair any elaboration errors.
2. Prove elementary Bernoulli positivity, log-base conversion, and asymptotic lemmas.
3. Implement quotient-family pushforward and its sparsity property so Lemma 9.1 can be stated completely.
4. Add entropy quotient chain rules and supermodularity, then tackle the iterative rigidity and posterior arguments.
5. Audit exact hypotheses and all conclusions of the main theorems against the source paper before claiming fidelity.
