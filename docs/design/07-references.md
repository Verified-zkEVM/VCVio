# 07 — References and Acquisition List

Working bibliography for the suite, split into (a) sources already available locally, (b) papers
to acquire into paper-note (`~/Documents/Research/Papers`), (c) code baselines. PolyFun's
`REFERENCES.md` remains canonical for what its modules cite; this list is the *suite's* reading
map, keyed by direction.

## A. In hand

| Source | Where | Feeds |
|---|---|---|
| Spivak–Niu, *Polynomial Functors* (CUP 2025) + PolyFun ch5–ch8 notes | PolyFun `docs/reading/spivak-niu-ch*.md` | all; ch7–8 → `02`, `06` |
| Libkind–Spivak, *Pattern runs on matter* (EPTCS 429) + note | `docs/reading/pattern-runs-on-matter.md`, arXiv:2404.16321 | `03` |
| Aberlé, *Compositional Program Verification with Polynomial Functors* (Abe26, arXiv 2604.01303) + note | `docs/reading/aberle-parallel.md`; Agda artifact cited therein | `04`, `05` |
| VCVio paper | ePrint 2026/899, PDF in workspace root | all (§10 = paper-3 promise) |
| Canetti, *Universally Composable Security* | Papers: `2000-067` | `06` requirements |
| Canetti et al., UC with a random oracle / global ROs | Papers: `2014-908`, `2018-165` | `05` §2.2 |
| UC-AGM | Papers: `2021-1218` | later (worlds/instrumentation) |
| Strict poly-time simulation/extraction | Papers: `2002-043` | R5 boundary in `06` |
| Hancock–Setzer; Indexed Containers (AGHMM15); ITrees (POPL 2020); Escardó–Oliva | PolyFun `REFERENCES.md` | substrate |
| iris-lean, iris-bluebell, loom2-lean, cslib | workspace checkouts | `04` bridges, `05` kill-criterion comparison |

## B. To acquire (priority order; all open-access)

1. **Brzuska–Delignat-Lavaud–Fournet–Kohbrok–Kohlweiss, *State-Separating Proofs*** — ePrint
   2018/306. The SSP source of truth; `03` names its reduction lemma as derivation target.
2. **Broadbent–Karvonen, *Categorical composable cryptography*** — arXiv:2105.05949 (+ extended
   FoSSaCS/LMCS version). Attack structures on symmetric monoidal categories; the closest
   published relative of `OpenTheory`+`Emulates`; paper-3 related-work anchor and a check on
   `02`'s ladder placement.
3. **Maurer–Renner, *Abstract Cryptography* / Maurer, *Constructive Cryptography*** (ICS 2011 /
   TOSCA 2011). The resource/converter/distinguisher trinity ↔ `Obj`/`map`/`plug`; the
   "equality up to simulator" algebra `02` §3.4 should be compared against.
4. **Küsters–Tuengerthal(–Rausch), *The IITM Model*** (J. Cryptology 2020 version) and **iUC**
   (ePrint 2019/1324). The directory/replication discipline `06` adopts; read §on runtime
   accounting for the R5 boundary.
5. **Canetti–Cohen–Lindell, *A simpler variant of UC*** (ePrint 2014/553) and **Canetti–Sarkar–
   Wang JUC/EUC materials** as needed by the `!F_com` pilot's joint-state exclusions.
6. **Myers, *Categorical Systems Theory*** (book draft, davidjaz.com). Doubly indexed functors;
   "behavior of composite = composite of behaviors" — the packaging for `06` §2.4.
7. **EasyUC** (Canetti–Stoughton–Varia, CSF 2019, ePrint 2019/582) and **ILC** (Liao et al.).
   The ≈18k-line baseline every UC rent test is measured against.
8. **Libkind, *Operads for Dynamical Systems* / Libkind–Spivak Org** (arXiv:2112.11518 etc.) —
   mode-dependent wiring for `06` §2.2.
9. **Nominal-SSProve** (LS25 in paper-1's bibliography) — the competing separation mechanism;
   `05`'s frame design should cite its location-quotient approach as the alternative.
10. **Ahman–Uustalu, directed containers / comonoid = category line** — citation hygiene for the
    comonoid layer (PolyFun G0 already lists; mirror into paper-note).

Suggested first action for an implementation agent: `/paper-note` download of items 1–7 with
index entries keyed to this suite's doc numbers.

## C. Code baselines (for honest comparison, not import)

- **SSProve** (Rocq) — package algebra maturity bar for `03`.
- **CryptHOL / Constructive Crypto in CryptHOL** (Isabelle) — the GPV/determinization design
  source the ledger already names for observational equivalence (`02` §3.3 caveat).
- **EasyUC artifact** — routing-cost baseline (`06` honest column).
- **squiggle/aberle Agda artifact** (Abe26) — displayed-parallel executable reference for `04`.
