# References

This file centralizes public external references cited in `README.md`, `docs/agents/`, and the
module docstrings of the Lean libraries. When adding new references to shared docs, prefer
linking here instead of duplicating partial citations inline.

## Papers

### ERHL25

Martin Avanzini, Gilles Barthe, Davide Davoli, and Benjamin Grégoire.
*A Quantitative Probabilistic Relational Hoare Logic*.
In *Proceedings of the 52nd ACM SIGPLAN Symposium on Principles of Programming Languages*
(POPL 2025), Denver, Colorado, USA, January 2025.
DOI: <https://doi.org/10.1145/3704876>
Public abstract and metadata: <https://inria.hal.science/hal-04834149v1>
Preprint: <https://arxiv.org/abs/2407.17127>

Used in:
- `docs/agents/program-logic.md`
- `docs/agents/proof-workflows.md`
- `docs/agents/gotchas.md`

### LOOM26

Vladimir Gladshtein, George Pîrlea, Qiyuan Zhao, Vitaly Kurin, and Ilya Sergey.
*Foundational Multi-Modal Program Verifiers*.
*Proceedings of the ACM on Programming Languages* 10 (POPL), Article 77, January 2026.
DOI: <https://doi.org/10.1145/3776719>

Used in:
- `README.md`

### PRHL14

Gilles Barthe, Cédric Fournet, Benjamin Grégoire, Pierre-Yves Strub, Nikhil Swamy,
and Santiago Zanella-Béguelin.
*Probabilistic Relational Verification for Cryptographic Implementations*.
In *Proceedings of the 41st ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages*
(POPL 2014).
DOI: <https://doi.org/10.1145/2535838.2535847>
Public metadata: <https://inria.hal.science/hal-00935743v1>

Background reference for:
- pRHL mentions in `docs/agents/program-logic.md`

### FCF14

Adam Petcher and Greg Morrisett.
*The Foundational Cryptography Framework*.
arXiv:1410.3735, 2014.
DOI: <https://doi.org/10.48550/arXiv.1410.3735>
Public abstract: <https://arxiv.org/abs/1410.3735>

Used in:
- `README.md`

### BDHMS24

Manuel Barbosa, François Dupressoir, Andreas Hülsing, Matthias Meijers, and Pierre-Yves Strub.
*A Tight Security Proof for SPHINCS+, Formally Verified*.
Cryptology ePrint Archive, Report 2024/910, 2024.
Preprint: <https://eprint.iacr.org/2024/910>

Used in:
- `docs/design/slh-dsa-fips205-generalization.md`
- `VCVio/CryptoFoundations/TweakableHash.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/Collection.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPREFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTOpenPREFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity/Core.lean`

### DKKW25

Justin Drake, Dmitry Khovratovich, Mikhail Kudinov, and Benedikt Wagner.
*Hash-Based Multi-Signatures for Post-Quantum Ethereum*.
Cryptology ePrint Archive, Report 2025/055, 2025.
Preprint: <https://eprint.iacr.org/2025/055>

Used in:
- `VCVio/CryptoFoundations/TweakableHash.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUD.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUDFinalValidity.lean`

### GHHM21

Alex B. Grilo, Kathrin Hövelmanns, Andreas Hülsing, and Christian Majenz.
*Tight Adaptive Reprogramming in the QROM*.
In *Advances in Cryptology — ASIACRYPT 2021*, Lecture Notes in Computer Science 13090.
DOI: <https://doi.org/10.1007/978-3-030-92062-3_22>
Preprint: <https://eprint.iacr.org/2020/1361>

Used in:
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`

### HK22

Andreas Hülsing and Mikhail Kudinov.
*Recovering the Tight Security Proof of SPHINCS+*.
Cryptology ePrint Archive, Report 2022/346, 2022.
Preprint: <https://eprint.iacr.org/2022/346>

Used in:
- `VCVio/CryptoFoundations/TweakableHash.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/Collection.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTTCRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPRE.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTPREFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTDSPRFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTRTCR.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUD.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/SMDTUDFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity.lean`
- `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/ToFinalValidity/Core.lean`

### CO25

Alessandro Chiesa and Michele Orrù.
*A Fiat–Shamir Transformation From Duplex Sponges*.
Cryptology ePrint Archive, Paper 2025/536, 2025.
Version of March 27, 2026; Claim 7.9 (pp. 56–57).
Preprint: <https://eprint.iacr.org/2025/536>

Used in:
- `VCVio/OracleComp/Constructions/UniformPreimage.lean`

### CY24

Alessandro Chiesa and Eylon Yogev.
*Building Cryptographic Proofs from Hash Functions*.
Version 1.2, 2024.
Public book: <https://snargsbook.org/>
Pinned source (commit 305fa3d9):
<https://github.com/hash-based-snargs-book/hash-based-snargs-book/blob/305fa3d9d19ee6dba135de64b3156d1760df8426/snargs-book.tex>

Used in:
- `VCVio/CryptoFoundations/MerkleTree/Extractability.lean`
- `VCVio/CryptoFoundations/MerkleTree/Inductive/Batch/Defs.lean`
- `VCVio/CryptoFoundations/VectorCommitment/Basic.lean`
- `VCVio/CryptoFoundations/VectorCommitment/Hiding.lean`
- `VCVio/CryptoFoundations/VectorCommitment/PositionBinding.lean`
- `VCVio/EvalDist/DiscreteTVDist.lean`
- `docs/agents/crypto.md`

### CDHZ25

Alessandro Chiesa, Zijing Di, Zihan Hu, and Yuxi Zheng.
*How to Prove Post-Quantum Security for Succinct Non-Interactive Reductions*.
Cryptology ePrint Archive, Paper 2025/2166, 2025.
Revision of March 2, 2026.
Preprint: <https://eprint.iacr.org/2025/2166>

Used in:
- `VCVio/CryptoFoundations/MerkleTree/Instability.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/Commutativity.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/Conditions.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/Defs.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/Extract.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/Extraction.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/HalfPreimage.lean`
- `VCVio/CryptoFoundations/MerkleTree/Salted/Instability.lean`
- `VCVio/CryptoFoundations/VectorCommitment/Basic.lean`
- `VCVio/CryptoFoundations/VectorCommitment/Completeness.lean`
- `VCVio/CryptoFoundations/VectorCommitment/NonadaptiveCheck.lean`
- `VCVio/OracleComp/QueryTracking/Instability/Basic.lean`
- `VCVio/OracleComp/QueryTracking/Instability/Collision.lean`
- `VCVio/OracleComp/QueryTracking/QueryLogCheck.lean`
- `VCVio/Quantum/Comp/Combinators.lean`
- `VCVio/Quantum/Comp/Hybrid.lean`
- `VCVio/Quantum/Comp/HybridIndex.lean`
- `VCVio/Quantum/Comp/HybridMeasure.lean`
- `VCVio/Quantum/Comp/HybridProjected.lean`
- `VCVio/Quantum/Comp/Potential.lean`
- `VCVio/Quantum/Comp/QueryMass.lean`
- `VCVio/Quantum/Oracle/Classical.lean`
- `VCVio/Quantum/Oracle/ClassicalCalls.lean`
- `VCVio/Quantum/Oracle/ClassicalRepeatability.lean`
- `VCVio/Quantum/Oracle/Compressed/Basic.lean`
- `VCVio/Quantum/Oracle/Compressed/BinaryPartition.lean`
- `VCVio/Quantum/Oracle/Compressed/Collision.lean`
- `VCVio/Quantum/Oracle/Compressed/CollisionBlocks.lean`
- `VCVio/Quantum/Oracle/Compressed/CollisionPotential.lean`
- `VCVio/Quantum/Oracle/Compressed/CollisionRuntime.lean`
- `VCVio/Quantum/Oracle/Compressed/CommutatorBound.lean`
- `VCVio/Quantum/Oracle/Compressed/CommutatorSharp.lean`
- `VCVio/Quantum/Oracle/Compressed/Consistency.lean`
- `VCVio/Quantum/Oracle/Compressed/Equivalence.lean`
- `VCVio/Quantum/Oracle/Compressed/Instability.lean`
- `VCVio/Quantum/Oracle/Compressed/LocalPotential.lean`
- `VCVio/Quantum/Oracle/Compressed/Measurement.lean`
- `VCVio/Quantum/Oracle/Compressed/Phase.lean`
- `VCVio/Quantum/Oracle/Compressed/ProjectorEvent.lean`
- `VCVio/Quantum/Oracle/Compressed/Size.lean`
- `VCVio/Quantum/Oracle/Compressed/Truncation.lean`
- `VCVio/Quantum/Oracle/Emulated.lean`
- `VCVio/Quantum/Oracle/EmulatedTensor.lean`
- `VCVio/Quantum/VC/Compressed.lean`
- `VCVio/Quantum/VC/Conditions.lean`
- `VCVio/Quantum/VC/Emulated.lean`
- `VCVio/Quantum/VC/Merkle/MultiExtractable.lean`
- `VCVio/Quantum/VC/Merkle/Online.lean`
- `VCVio/Quantum/VC/MultiExtractable.lean`
- `VCVio/Quantum/VC/MultiExtractor.lean`
- `VCVio/Quantum/VC/Proof/Commutativity.lean`
- `VCVio/Quantum/VC/Proof/Extraction.lean`
- `VCVio/Quantum/VC/Proof/Offline.lean`
- `VCVio/Quantum/VC/Proof/Online.lean`
- `VCVio/Quantum/VC/Proof/OnlineSecurity.lean`
- `VCVio/Quantum/VC/Proof/Repeatability.lean`
- `VCVio/Quantum/VC/Tuples.lean`
- `VCVio/Quantum/VC/Unitaries.lean`
- `VCVioTest/Quantum/Compressed.lean`
- `VCVioTest/Quantum/Hybrid.lean`
- `VCVioTest/Quantum/InstabilityBound.lean`
- `VCVioTest/Quantum/MultiExtractableModule.lean`
- `VCVioTest/Quantum/VCCompressed.lean`
- `VCVioTest/Quantum/VCProof.lean`
- `VCVioTest/Quantum/VectorCommitmentQuantum.lean`
- `VCVioTest/SaltedMerkle.lean`

### HHK17

Dennis Hofheinz, Kathrin Hövelmanns, and Eike Kiltz.
*A Modular Analysis of the Fujisaki-Okamoto Transformation*.
In *Theory of Cryptography — TCC 2017*.
Cryptology ePrint Archive, Report 2017/604, version of November 2, 2021; Definition 2.1 and
Figure 3 (p. 8).
Preprint: <https://eprint.iacr.org/2017/604>

Used in:
- `VCVio/CryptoFoundations/FujisakiOkamoto/Defs.lean`

## Projects and Repositories

### MATHLIB4

The Lean community.
*mathlib4: The math library of Lean 4*.
GitHub repository: <https://github.com/leanprover-community/mathlib4>
Documentation: <https://leanprover-community.github.io/mathlib4_docs/>

Used in:
- `README.md`

### LOOM-REPO

VERSE Lab.
*loom*.
GitHub repository: <https://github.com/verse-lab/loom>

Used in:
- `README.md`

### FCF-REPO

Adam Petcher.
*fcf*.
GitHub repository: <https://github.com/adampetcher/fcf>

Used in:
- `README.md`

### LEANCRYPTO3-REPO

`dtumad/lean-crypto-formalization`.
Deprecated Lean 3 repository for formalizing cryptography proofs.
GitHub repository: <https://github.com/dtumad/lean-crypto-formalization>

Used in:
- `README.md`
