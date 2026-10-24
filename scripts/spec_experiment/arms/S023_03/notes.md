# S023_03 evalDist_singleIdeal_run'_eq_tableSample — arm A

- Minutes: ~3
- Result: 9 lines / 408 HB (original 11 / 473). Accepted.
- Tried: `(by simp)` for the two uniformity hypotheses (simp makes no progress — the
  `𝒟[$ᵗ β] = uniformOn univ` fact is not a simp lemma); kept the explicit
  `SampleableType.evalDist_uniformSample`.
- What shortened it: `tableExtending` is `@[reducible]` and `(∅ : QueryCache) t = none`, so
  `tableExtending ∅ g` is defeq to `g`; the general Step-A lemma applies as a term, with no
  `rw` + `simp only [tableExtending_empty]`.
- Missing: essentially nothing generic; the remaining cost is the local
  `MeasurableSpace Digest := ⊤` instance and spelling the uniform-sample hypotheses. A version of
  the general lemma whose hypotheses are discharged by default (`SampleableType` uniformity as
  an autoparam / instance-implied fact) would make this a one-liner.

## B
- Minutes: ~1. B = A + import: 9 lines / 408 HB (A 9 / 408).
- Library not relevant: the proof is one application of a file-specific eager-table lemma; no
  handler run, support, bound or bisimulation step. Nothing missing from the library for it.
