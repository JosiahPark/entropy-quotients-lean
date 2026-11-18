# Numerics: Grok's numerical and adversarial checks

Numerical and adversarial checks of arXiv:2610.38525v1 and of this repository, produced by Grok on
2026-11-15 and supplied by Josiah Park as `eq_constants.zip`. Nothing here is a proof, and nothing
here is part of the Lean library.

The archive is unpacked in this folder: [`grok_output.pdf`](grok_output.pdf) and
[`eq_constants/`](eq_constants/README.md) sit next to this page, so the paths below are paths in
this folder. None of it is built by Lake or scanned by `scripts/audit_sorries.py`. This page is the
index of the archive: what each part holds, where this repository cites the report, and the limits
of the numerics.

## Contents of the archive

| Path | Contents |
| --- | --- |
| `grok_output.pdf` | Grok's report, "Adversarial hypothesis tests" (6 pages): the claims tested, the test volumes and worst cases, the Lean findings L1–L8, and suggested fixes. The same file is `eq_constants/REPORT.pdf`. |
| `eq_constants/README.md` | Grok's summary of the scripts and outputs. Its section "Worst-case constants" is the table of constants that the root [README.md](../README.md) refers to. |
| `eq_constants/scripts/` | The Python library (`eqlib.py`, `gens.py`, `fib.py`), the test scripts (`tests_*.py`) and `lean_stats.py`. They need Python 3 with numpy and mpmath and are run from `scripts/`. |
| `eq_constants/outputs/constants/` | Optimizer outputs for Theorems 1.1, 1.2 and 8.2, the Marton input (35) and Lemma 6.3, and the Lemma 5.1 adversary. |
| `eq_constants/outputs/high_precision/` | Proposition 9.3 at 200 digits and Lemma 8.1 at 60 digits. |
| `eq_constants/outputs/lemmas/` | Per-lemma results of the exhaustive checks of Lemmas 2.1–9.1 on 𝔽₂ⁿ, n ≤ 5. |
| `eq_constants/lean/` | Grok's scratch Lean files with their outputs: `#print axioms` for 16 results (`Axioms2.lean`, `axioms.out`) and satisfiability checks (`Sanity.lean`, `sanity.out`). They were run against commit `20b6c12` and are not compiled by CI. |

## What the report is used for in this repository

- The numerical constants quoted in the root [README.md](../README.md), section "Numerical
  constants".
- [ROADMAP.md](../ROADMAP.md), item B1: the report's remark that the PFR project proves the entropic
  Marton bound with constant at most 6.
- [ROADMAP.md](../ROADMAP.md), items D9 and D10: the report's finding L6, that
  `WeightedFamily.posterior` exists only for `V : Type`, so Lemma 8.1 is obtained as
  `RatioGrowth.{0}` and the statements for `V : Type*` need a universe transport.

## Limits

- The worst cases are the largest values a search found on 𝔽₂ⁿ with n ≤ 5 (families for n ≤ 3).
  They are observations, not bounds.
- Theorems 1.1, 1.2 and 8.2 say something beyond `E ≤ H` only when λ < 2⁻³²⁰. No numerical test
  reaches that range; the report tests the proof steps and the scaling instead.
- The report describes the repository at commit `20b6c12`. Its remarks on the README and on open
  items (D8c, D9) are out of date where later commits addressed them.

This index was written by Claude Fable 5.2 (`claude-fable-5-2`), 2026-11-15, from
`eq_constants.zip`. Fable 5.2 did not rerun Grok's scripts.

The files were committed on 2026-11-16 by Claude (Opus 5.5) from `eq_constants (1).zip`, the later and
larger of the two copies of the archive (75 entries; the earlier copy has no `lean/`, no
`outputs/lemmas/` and no `scripts/lean_stats.py`), byte for byte. That archive has no separate
`grok_output.pdf`; the copy here is byte-identical to `eq_constants/REPORT.pdf`, which the table above
describes as the same file.
