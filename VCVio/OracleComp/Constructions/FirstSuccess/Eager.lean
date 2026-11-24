/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.Algorithms.FirstSuccess.Basic
public import VCVio.OracleComp.EvalDist.AnswerMeasure
public import VCVio.EvalDist.EvalDistEq

/-!
# Eager first-success search

`FirstSuccess.runWith sample accept n` draws lazily: it draws one value, stops if `accept` returns
a result, and otherwise draws again, up to `n` draws. An eager search instead draws all `n` values
up front and returns the first accepted one with `List.findSome?`. Unused draws change nothing an
observer of the result can see, so both searches return the same distribution
(`findSome?_eager_evalDistEq_runWith`). The eager draws may come from a different sampler, as long
as it has the same distribution as `sample`.

A PRF-based signer uses this form: it reads its `n` retry randomizers from `n` PRF outputs up
front, while the direct signer samples randomizers one at a time until encoding succeeds.
-/

public section

namespace VCVio.Algorithms.FirstSuccess

open OracleComp

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {R α : Type}

/-- Drawing `n` values eagerly and returning the first accepted one has the distribution of the
lazy search `runWith sample accept n`, provided each eager draw has the distribution of
`sample`. -/
theorem findSome?_eager_evalDistEq_runWith {eager sample : OracleComp spec R}
    (hlaw : eager =ᵈ sample) (accept : R → Option α) (n : ℕ) :
    List.findSome? accept <$> (List.ofFn <$> Fin.mOfFn n fun _ => eager) =ᵈ
      runWith sample accept n := by
  have hdraws (n : ℕ) :
      Fin.mOfFn n (fun _ => eager) =ᵈ Fin.mOfFn n (fun _ => sample) := by
    induction n with
    | zero => exact EvalDistEq.rfl
    | succ n ih =>
        change (do
          let head ← eager
          let tail ← Fin.mOfFn n (fun _ => eager)
          pure (Fin.cons head tail : Fin (n + 1) → R)) =ᵈ (do
          let head ← sample
          let tail ← Fin.mOfFn n (fun _ => sample)
          pure (Fin.cons head tail : Fin (n + 1) → R))
        exact hlaw.bind fun _ => ih.bind fun _ => EvalDistEq.rfl
  have hlazy (n : ℕ) :
      List.findSome? accept <$> (List.ofFn <$> Fin.mOfFn n fun _ => sample) =ᵈ
        runWith sample accept n := by
    induction n with
    | zero => simp [Fin.mOfFn]
    | succ n ih =>
        rw [runWith_succ]
        simp only [Fin.mOfFn, map_bind, map_pure, List.ofFn_cons]
        apply EvalDistEq.bind_right
        intro draw
        cases h : accept draw with
        | some value =>
            refine evalDistEq_iff_evalDist_eq.mpr ?_
            simp [h]
        | none =>
            simpa [List.findSome?_cons, h, map_eq_bind_pure_comp, bind_assoc] using ih
  exact ((hdraws n).map _).map _ |>.trans (hlazy n)

end VCVio.Algorithms.FirstSuccess
