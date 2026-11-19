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
| `plantedPreimageAdvantage_le_of_isPointBound` | *Bits of security in the parallel QROM*, local note below, Appendix A | secret-input image target; exact joint table/target/secret coupling and sampled-set finding at density `1/M + (1 - 1/M)/N`, with target-dependent adversary families and adaptive round/point budgets |
| `ParallelQROMBits`, `parallelQROMBits_markedSearch`, `parallelQROMBits_preimageSearch`, `parallelQROMBits_plantedPreimage` | same local note, p. 1 and Appendix A | search-calibrated security predicate and corollaries for named games with actual syntactic round and width restrictions |
| `QueryCache.flip`, `instability`, `condFlip` | Chiesa, Manohar, Spooner, [ePrint 2019/834](https://eprint.iacr.org/2019/834), Definitions 5.4, 5.6, 5.11, pp. 23–26 | any answer measure |
| `partitionInstability` | Chiesa, Di, Hu, Zheng, [ePrint 2025/2166](https://eprint.iacr.org/2025/2166), Definition 5.3, p. 31 | any indexed family |
| `instability_cacheHasCollision_le` | CMS19 Lemma 6.11, p. 35; CDHZ Lemma 8.7, p. 56 | the sharper $(t-1)/n$ |
| (motivation only) | CMS19 Lemma 5.10, p. 24; CDHZ Theorem 5.4, p. 31 | not formalized here |

## Local security-normalization note

*Bits of security in the parallel QROM*, `parallel-qrom-security.pdf` in `~/QROM-lit`, is a
three-page local note with no printed author or version. Page 1 defines at least λ bits of
security by the bound `(1 + 2D√P)² / 2^λ`, where `D` is the number of adaptive rounds and `P`
the maximum width. This is an ideal-query-model metric, not a gate-cost estimate.

Appendix A distinguishes independent-target inversion from inversion of the image of a
uniform secret input. The independent-target bound follows from
`preimageSearchAdvantage_le_of_isPointBound` with at most `DP` total points. For a domain of
size `M` and range of size `N`, the secret-input variant uses the marginal preimage density
`ρ = 1/M + (1 - 1/M)/N`. `average_image_eq_plantedTargetPatch` preserves the complete joint
sampling law, and `plantedPreimageAdvantage_le_of_isPointBound` applies the generic finding
bound to this correlated hidden set. Both games allow the adversary to depend on the public
target, with no oracle-dependent advice.

Appendix B sketches a compressed-oracle collision bound of order `P²D⁴/N`, sufficient for
the note's normalization when `N = 2^(2λ)`. This argument remains unformalized and is weaker
than CFHL's depth-sensitive bound of order `P²D³/N`. It does not complete the separate CFHL
track. The reviewed PDF has SHA-256
`1e8207e233f080f147b7ebd8a88d0ebd7e86a843fa20aad8cc2247e7aa937506`.

The squared pair sum in Appendix B does not require orthogonal collision subspaces. If
$E_{ab}$ projects onto equal nonblank contents at cells $a,b$, these diagonal projectors satisfy
$E_{\mathrm{any}} \le \sum_{a<b} E_{ab}$. Thus
$\|E_{\mathrm{any}}v\|^2 \le \sum_{a<b}\|E_{ab}v\|^2$, even when three or more cells agree.
For a basis change on a set $A$ of addressed cells, its factors outside a given pair commute
with $E_{ab}$. Together with $1-E_{\mathrm{any}} \le 1-E_{ab}$, this reduces each pair's transition
to the one- or two-cell bound. Fixing the query addresses and outside database contents restricts
the possible pairs to at most $rP$ active cells at round $r$; these sectors are orthogonal.
This justifies the note's coarse transition estimate. A formal collision theorem still needs
the projector inequalities, support bookkeeping and final controlled-decompression bridge.
