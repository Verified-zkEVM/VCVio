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
| `QueryCache.flip`, `instability`, `condFlip` | Chiesa, Manohar, Spooner, [ePrint 2019/834](https://eprint.iacr.org/2019/834), Definitions 5.4, 5.6, 5.11, pp. 23–26 | any answer measure |
| `partitionInstability` | Chiesa, Di, Hu, Zheng, [ePrint 2025/2166](https://eprint.iacr.org/2025/2166), Definition 5.3, p. 31 | any indexed family |
| `instability_cacheHasCollision_le` | CMS19 Lemma 6.11, p. 35; CDHZ Lemma 8.7, p. 56 | the sharper $(t-1)/n$ |
| (motivation only) | CMS19 Lemma 5.10, p. 24; CDHZ Theorem 5.4, p. 31 | not formalized here |
