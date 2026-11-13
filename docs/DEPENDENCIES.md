# Result dependency chart

How the results of arXiv:2610.38525 depend on each other, and how far each one is in Lean.
An arrow `A → B` means the paper's proof of B uses A. Colours give the Lean status at commit
time; [ROADMAP.md](../ROADMAP.md) is the ordered work list that moves nodes from grey to green.

| Colour | Meaning |
| --- | --- |
| green | proved in Lean (no `sorry`) |
| amber | stated in Lean, proof is `sorry` |
| grey | not yet stated in Lean |
| blue | external input (cited, not proved in the paper) |

```mermaid
flowchart TD
  classDef proved fill:#d4edda,stroke:#2e7d32,color:#1b3d1f
  classDef stated fill:#fff3cd,stroke:#b8860b,color:#4d3800
  classDef missing fill:#eceff1,stroke:#78909c,color:#263238
  classDef external fill:#dbe9f7,stroke:#1f5fa8,color:#0d2a4d

  %% Definitions and elementary identities
  DEF["Definitions: H, convolution, D, E, s, F_P(W),<br/>sparsity, weighted families, q_G 𝒫, 𝒫 * 𝒫<br/>(Basic, Families)"]:::proved
  ID["Identities: E = H − D, s(P,P) = E(P),<br/>h(q_G 𝒫) = h(𝒫) − F_𝒫(G), weights a_i a_j sum to 1"]:::proved
  ALG["Algebraic step: E(Z) ≤ θH(Z) ⇒ H(Z) ≤ (1+ε)D(Z)<br/>entropy_le_increment_of_defect_le"]:::proved
  BPAR["2^(−c/ε) ∈ (0,1)<br/>bernoulli_parameter_mem_Ioo"]:::proved

  %% Entropy toolkit (Section 2)
  NN["H ≥ 0, chain rule,<br/>I(A;B|C) ≥ 0<br/>entropyBits_nonneg, entropyBits_chain, condMutualInfo_nonneg"]:::proved
  E9["(9): 0 ≤ s(P,Q) ≤ min(H(P),H(Q));<br/>(14): 0 ≤ e(𝒫) ≤ h(𝒫)"]:::missing
  DP["Data processing: D(q_G X) ≤ D(X)"]:::missing
  E15["(15): h(𝒫 * 𝒫) = 2h(𝒫) − e(𝒫)"]:::missing
  QC["Quotient commutes with convolution<br/>conv_map_mkQ"]:::proved
  L21["Lemma 2.1: F_P supermodular"]:::missing
  L22["Lemma 2.2: posterior closure"]:::missing

  %% Sections 3-7
  L31["Lemma 3.1: fibring, nested interaction (20)–(22)"]:::missing
  L41["Lemma 4.1: ratio-preserving sparsification<br/>ratio_preserving_sparsification"]:::stated
  L51["Lemma 5.1: averaged density estimate"]:::missing
  L61["Lemma 6.1: four-sample splitting"]:::missing
  L62["Lemma 6.2: conditional BSG inequality"]:::missing
  L63["Lemma 6.3: posterior doubling estimate"]:::missing
  MAR["Entropic Marton theorem (35)<br/>Gowers–Green–Manners–Tao"]:::external
  E36["(36): H(q_V K) ≤ 12D(K), dim V ≤ 13H(K)"]:::missing
  L71["Lemma 7.1: sparse posterior estimate"]:::missing

  %% Section 8
  L81["Lemma 8.1: ratio growth"]:::missing
  ARITH["Iteration arithmetic (42)–(43):<br/>d log₂(1/λ) < 320"]:::missing
  T82["Theorem 8.2: weighted-family rigidity<br/>weighted_family_rigidity"]:::stated
  T12["Theorem 1.2: sparse-law rigidity<br/>sparse_rigidity"]:::stated

  %% Section 9
  L91["Lemma 9.1: variational sparsification<br/>variational_sparsification"]:::stated
  T11["Theorem 1.1: exponential entropy quotient<br/>exponential_entropy_quotient"]:::stated
  C92["Corollary 9.2: two-input almost-additivity"]:::missing
  BEXP["Bernoulli expansions of h₂(p), 2h₂(p) − h₂(2p(1−p))"]:::missing
  P93["Proposition 9.3: exponential scale is necessary<br/>exponential_scale_necessary"]:::stated
  C94["Corollary 9.4: subspace-coset concentration"]:::missing

  DEF --> ID
  DEF --> NN
  NN --> E9
  NN --> DP
  NN --> L21
  NN --> L22
  ID --> E15
  DEF --> QC
  E9 --> L31
  L21 --> L31

  E15 --> L41
  E9 --> L41
  QC --> L41
  L31 --> L51
  L21 --> L51
  E15 --> L61
  L22 --> L61
  NN --> L62
  L62 --> L63
  MAR --> E36
  E36 --> L71
  L31 --> L71
  L63 --> L71
  L51 --> L71

  L41 --> L81
  L22 --> L81
  L61 --> L81
  L71 --> L81
  L81 --> T82
  ARITH --> T82
  E9 --> T82
  T82 --> T12

  NN --> L91
  L91 --> T11
  T82 --> T11
  ALG --> T11
  DP --> T11
  L91 --> C92
  T82 --> C92
  DP --> C92
  BPAR --> P93
  BEXP --> P93
  T11 --> C94
```

## Reading the chart

- The only external input is the entropic Marton theorem (35). Everything else is proved in the
  paper, so every grey node is a formalization target, not an assumption.
- Theorem 1.1 is three steps away from its inputs: Lemma 9.1, Theorem 8.2 and data processing,
  plus the algebraic step already proved. A conditional version, with Theorem 8.2 as a named
  hypothesis, is item C2 of the roadmap.
- Theorem 8.2 carries the depth of the paper: Lemmas 4.1, 5.1, 6.1–6.3, 7.1 and 8.1 all feed it.
- Proposition 9.3 is independent of Theorem 8.2: it needs only Bernoulli calculus (items E1–E3).
