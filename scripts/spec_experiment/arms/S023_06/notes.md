# S023_06 forsNodeHashM_isTotalQueryBound — arm A

- Minutes: ~3
- Original: 5 lines / 48 HB (4 statement lines + 1 term line `PublicHash.h_isTotalQueryBound core pk _ _ _`).
- A: 5 lines / 49 HB, 54 tokens (vs 58). Only change: explicit args replaced by `..`.
- Reason code: NO-ROOM (proof is already a single term application; statement is 4 of the 5 lines).
- Tried: nothing else worth trying; the per-primitive query-bound lemma already exists.
- Missing: nothing. (A `@[simp]`/instance-style query-bound registry would let `query_bound`-style
  automation discharge this, but it would not shorten a 1-line term.)

## B
- Minutes: ~1. B.lean = A.lean + `-- imports: VCVio.ProgramLogic.Library`. 5 lines / 49 HB (A: 5 / 49).
- Library lemmas used: none. The proof is a single application of the existing per-primitive bound
  `PublicHash.h_isTotalQueryBound`; the T1 `QueryBound` simp lemmas (`isTotalQueryBound_query_iff`,
  `…_bind_le`) would only re-derive it.
