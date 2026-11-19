# Definitions and theorems against the literature

Watrous refers to J. Watrous, *The Theory of Quantum Information*, Cambridge University Press,
2018, by printed page; chapters [1](https://cs.uwaterloo.ca/~watrous/TQI/TQI.1.pdf) and
[2](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf) are on the author's site. Other references give
the PDF page of the version linked.

| Lean | Source | Relation |
|---|---|---|
| `MatrixMap.IsCP`, `MatrixMap.IsTP` | Watrous, (1.124)–(1.125), p. 23 | same definitions |
| `SubState` | Watrous, Definition 2.5, p. 62 | allows trace below one |
| `IsCP` with `IsTP` | Watrous, Definition 2.13, p. 73 | channels |
| `MatrixMap.traceRight` | Watrous, (2.30)–(2.34), p. 68 | two factors |
| `MatrixMap.choi` | Watrous, (2.64)–(2.65), p. 78 | same convention, $J(\Phi)$ |
| `isCP_iff_posSemidef_choi`, `isCP_iff_exists_kraus` | Watrous, Theorem 2.22, p. 82 | same statements |
| `isTP_sum_conj_iff` | Watrous, Theorem 2.26, p. 87 | for Kraus form |
| `IsCP.exists_stinespring_of_isTP` | Watrous, Corollary 2.27, p. 89 | non-minimal environment |
| `SubInstrument`, `outcomeMeasure`, `post` | Watrous, (2.258)–(2.261), p. 112 | allows failure and countably many outcomes |
| `SubInstrument.ofProjective` | Watrous, Proposition 2.40, p. 107 | complete projections are orthogonal |
| `norm_queryState_sub_queryState_le` | Bennett, Bernstein, Brassard, Vazirani, [arXiv quant-ph/9701001](https://arxiv.org/abs/quant-ph/9701001), Theorem 3.3, pp. 7–8 | the hybrid step, for contractions |
| `oracleUnitary`, `qromEvalDist` | Boneh et al., *Random Oracles in a Quantum World*, [arXiv:1008.0931v2](https://arxiv.org/abs/1008.0931v2), §2.1, p. 7 | additive groups in place of XOR |
| `parallelOracleUnitary`, `batch_oracleQuery`, `qromBatchEvalDist` | Chung, Fehr, Huang, Liao, [arXiv:2010.11658v4](https://arxiv.org/abs/2010.11658v4), §4.4, pp. 12–13 | simultaneous additive queries; variable classical widths and one shared random function |
| `preimageSearchAdvantage_le_of_isPointBound` | Chung, Fehr, Huang, Liao, [arXiv:2010.11658v4](https://arxiv.org/abs/2010.11658v4), Example 5.18; Zalka, [arXiv:quant-ph/9711070v2](https://arxiv.org/abs/quant-ph/9711070v2), §4 | fixed-target preimage game; direct hybrid and joint-table coupling, with total-point budgets, rather than compressed-oracle transition capacities |
| `Quantum.MaskedChain.recoveryAdvantage_le` | Afshar, Chung, Hsieh, Lin, Mahmoody, [ePrint 2023/932](https://eprint.iacr.org/2023/932), §5, Definition 5.1, Theorem 5.3 and Lemmas 5.4–5.5, pp. 24–28 | endpoint-only adaptation of the full-tuple bound, retaining the hidden tuple jointly; finite abelian groups and explicit error terms |
| `Quantum.MaskedChain.recoveryAdvantage_le_root` | Afshar et al., §5, Definition 5.1 and Theorem 5.3, p. 24; Lemmas 5.4–5.5 and event-error summation, pp. 27–28; root Minkowski and the Bennett–Bernstein–Brassard–Vazirani hybrid above | derived endpoint bound of order `kq³/N` for `k,q ≥ 1`, with explicit guessing and collision terms; the detailed paper theorem states full-tuple recovery of order `sqrt(kq³/N)` |
| `Quantum.MaskedChain.preprocessedRecoveryAdvantage_le` | Afshar et al., §5, together with the Bennett–Bernstein–Brassard–Vazirani hybrid above | query-bounded preprocessing extension derived here; round/point common-finisher hybrid and trace-homogeneous conditional online bound, rather than an auxiliary-input theorem from that paper |
| `Quantum.MaskedChain.preprocessedRecoveryAdvantage_le_root`, `preprocessedRecoveryAdvantage_le_root_min` | same masked-chain hybrid and query-bounded preprocessing argument above | derived here by combining online and preprocessing root errors before squaring, with one external collision allowance and the effective preprocessing round budget `min rpre Qpre` |
| `PointerChainPuzzle.LeanSeal.real_le_programmed_add_collision` | leanSeal, §4.4 and §8.3 item 4, and its classical ranked-path programming argument | derived here for the full finite-window raw oracle and arbitrary bounded joint observers; a coupling step toward the quantum theorem left open by the paper, retaining raw mask tails and unconditioned path words |
| `PointerChainPuzzle.LeanSeal.qromDelayAdvantage_quantumWindowScheme_le_of_preprocessing` | leanSeal, §4.4 and §8.3 item 4; Bennett–Bernstein–Brassard–Vazirani hybrid above | derived here for the exact finite-window raw encoding and structured public puzzles; rank-cutoff quantum recovery with query-bounded preprocessing, unrestricted retained memory and one external collision allowance; the paper leaves its quantum extension open |
| `QueryCache.flip`, `instability`, `condFlip` | Chiesa, Manohar, Spooner, [ePrint 2019/834](https://eprint.iacr.org/2019/834), Definitions 5.4, 5.6, 5.11, pp. 23–26 | any answer measure |
| `partitionInstability` | Chiesa, Di, Hu, Zheng, [ePrint 2025/2166](https://eprint.iacr.org/2025/2166), Definition 5.3, p. 31 | any indexed family |
| `instability_cacheHasCollision_le` | CMS19 Lemma 6.11, p. 35; CDHZ Lemma 8.7, p. 56 | the sharper $(t-1)/n$ |
| (motivation only) | CMS19 Lemma 5.10, p. 24; CDHZ Theorem 5.4, p. 31 | not formalized here |

Afshar et al.'s detailed Definition 5.1 uses the full vertex tuple as its secret. The informal
Theorem 1.3, printed p. 4, also mentions recovering the endpoint. The endpoint-only theorems
here retain that hidden endpoint jointly with the final output; recovering the full tuple
would imply recovering its last component without an additional query. The root-accumulated
comparison concerns the same hybrid structure with different probability bookkeeping, and
makes no claim to novelty or a best-known bound. The explicit zero-query guessing terms
are retained; the stated asymptotic comparison assumes positive `k` and `q`.

The separate auxiliary-input model allows unbounded preprocessing and limits retained advice.
Chung, Guo, Liu and Qian, *Tight Quantum Time-Space Tradeoffs for Function Inversion*,
[arXiv:2006.05650v2](https://arxiv.org/abs/2006.05650v2), §3.1, Definition 3.1, distinguishes
classical and quantum advice. Guo, Li, Liu and Zhang, *Unifying Presampling via Concentration
Bounds*, [ePrint 2020/1589](https://eprint.iacr.org/2020/1589), Definition 1, specifies bounded
classical advice after unbounded preprocessing. Neither advice model is implemented by the
query-bounded preprocessing theorem.

## Local security-normalization note

*Bits of security in the parallel QROM*, `parallel-qrom-security.pdf` in `~/QROM-lit`, is a
three-page local note with no printed author or version. Page 1 defines at least λ bits of
security by the bound `(1 + 2D√P)² / 2^λ`, where `D` is the number of adaptive rounds and `P`
the maximum width. This is an ideal-query-model metric, not a gate-cost estimate.

Appendix A distinguishes independent-target inversion from inversion of the image of a
uniform secret input. The independent-target bound follows from
`preimageSearchAdvantage_le_of_isPointBound` with at most `DP` total points. For a domain of
size `M` and range of size `N`, the secret-input variant uses the marginal preimage density
`ρ = 1/M + (1 - 1/M)/N`. Its sampling coupling remains unformalized; the existing generic
finding bound already permits correlated hidden sets.

Appendix B sketches a compressed-oracle collision bound of order `P²D⁴/N`, sufficient for
the note's normalization when `N = 2^(2λ)`. This argument remains unformalized and is weaker
than CFHL's depth-sensitive bound of order `P²D³/N`. It does not complete the separate CFHL
track. The reviewed PDF has SHA-256
`1e8207e233f080f147b7ebd8a88d0ebd7e86a843fa20aad8cc2247e7aa937506`.
