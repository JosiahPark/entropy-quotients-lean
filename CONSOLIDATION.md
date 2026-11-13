# Consolidation map

| Input | Treatment |
| --- | --- |
| `Entropy.lean` | Kept finite PMF and weighted-family approach; removed abstract `sorry` convolution, redundant theorem statements and `True` conclusions |
| `EntropyQuotients.lean` | Used as the primary concrete-quotient theorem draft; repaired increment/defect naming and removed malformed placeholders |
| `EntropyQuotients (1).lean` | Merged precise Theorem 1.1 third inequality; dropped independent `ProbabilityMeasure`/`opaque` parallel API |
| `EntropyQuotients_formalization.lean` | Kept proved endpoint lemma concept, Bernoulli definitions, and status notes; removed `True` goals |
| `FeatureMap.lean` | Preserved separately in `EntropyLean/FeatureMap.lean`, excluding a `True`-conclusion rank theorem |

All inputs are preserved in `archive/` verbatim for comparison. Several source statements are mathematically incomplete or inconsistent; the cleaned repository does **not** claim all target statements have been preserved at full paper strength.
