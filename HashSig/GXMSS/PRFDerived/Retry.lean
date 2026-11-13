/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.PRFDerived.Query
public import HashSig.GXMSS.Scheme

/-!
# PRF-derived bounded signing

The complete retry coordinate list is derived eagerly. First-success classification maps only its
payload to a signature, retaining the shared one-based attempt and ordered consumed prefix.
-/

public section
namespace GXMSS.PRFDerived
open IncomparableEncoding GXMSS VCVio.Algorithms
variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Every bounded retry coordinate in its eager zero-based order. -/
@[expose] def retryCoordinates (budget : ℕ) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    List (Query PP M h v) :=
  List.ofFn fun attempt : Fin budget => Query.retry pp epoch message attempt.val

/-- The ordered randomizers for attempts `0, ..., budget - 1`. -/
@[expose] def retryRandomizers (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) : List R :=
  List.ofFn fun attempt : Fin budget =>
    interpretation.retryRandomizer (evaluate key (.retry pp epoch message attempt.val))

/-- The derived retry sequence has exactly the requested budget. -/
theorem retryRandomizers_length (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    (retryRandomizers budget evaluate interpretation key pp epoch message).length = budget :=
  List.length_ofFn

/-- All retry coordinates are evaluated before the first-success consumed-prefix observation. -/
theorem retryRandomizers_eq_map (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M) :
    retryRandomizers budget evaluate interpretation key pp epoch message =
      (retryCoordinates budget pp epoch message).map
        (fun query => interpretation.retryRandomizer (evaluate key query)) := by
  simp [retryRandomizers, retryCoordinates, List.map_ofFn, Function.comp_def]

/-- Position `attempt` uses its exact zero-based PP-indexed query. -/
theorem retryRandomizers_get (budget : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (interpretation : Interpretation PP H R Response)
    (key : Key) (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (attempt : Fin budget) :
    (retryRandomizers budget evaluate interpretation key pp epoch message).get
        (Fin.cast
          (retryRandomizers_length budget evaluate interpretation key pp epoch message).symm
          attempt) =
      interpretation.retryRandomizer (evaluate key (.retry pp epoch message attempt.val)) := by
  simp [retryRandomizers, Fin.cast]

/-- Shared first-success evidence with a signature as its returned payload. -/
abbrev SignResult (R H : Type) (h v : ℕ) :=
  FirstSuccess.Result R (Signature R H h v)

/-- Deterministic signing uses the shared indexed first-success operation on the
finite derived retry sequence. Each finite index selects its exact randomizer. -/
@[expose] def signResult (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M)
    (randomizers : List R) : SignResult R H h v :=
  let sample : Fin randomizers.length → Id R := fun attempt => randomizers.get attempt
  (enc.retryIndexed sk.seed message epoch randomizers.length sample).map
    (GXMSS.signatureOfWord hash sk epoch)

/-- The empty derived sequence returns exhaustion without consumption. -/
theorem signResult_nil (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M) :
    signResult hash enc sk epoch message [] = .exhausted [] := rfl

/-- The indexed operation retains the familiar first-success list equation. -/
theorem signResult_cons (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M)
    (randomizer : R) (remaining : List R) :
    signResult hash enc sk epoch message (randomizer :: remaining) =
      match enc.value sk.seed message randomizer epoch with
      | some word => .success (GXMSS.signatureOfWord hash sk epoch (word, randomizer))
          1 [randomizer]
      | none =>
          match signResult hash enc sk epoch message remaining with
          | .success signature attempt consumed =>
              .success signature (attempt + 1) (randomizer :: consumed)
          | .exhausted consumed => .exhausted (randomizer :: consumed) := by
  simp only [signResult, List.length_cons, IncomparableEncoding.retryIndexed_id_succ,
    List.get_cons_zero]
  cases hv : enc.value sk.seed message randomizer epoch with
  | some word => simp [FirstSuccess.Result.map]
  | none =>
      cases htail : enc.retryIndexed (m := Id) sk.seed message epoch remaining.length
          (fun attempt => (remaining.get attempt : Id R))
      all_goals simp only [List.get_eq_getElem] at htail
      all_goals simp [htail, FirstSuccess.Result.map, FirstSuccess.Result.prepend]

/-- The signer consumes an ordered bounded prefix. Success records its positive one-based
prefix length; returned exhaustion consumes the complete supplied sequence. -/
theorem signResult_prefix (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.SecretKey PP H h v) (epoch : Fin (2 ^ h)) (message : M)
    (randomizers : List R) :
    let result := signResult hash enc sk epoch message randomizers
    result.consumed = randomizers.take result.consumed.length ∧
      result.consumed.length ≤ randomizers.length ∧
      match result with
      | .success _ attempt _ => attempt = result.consumed.length ∧ 0 < attempt
      | .exhausted _ => result.consumed.length = randomizers.length := by
  have hobs := FirstSuccess.indexed_id_observations
    (enc.attempt sk.seed message epoch) randomizers.length randomizers.get
  simp only [List.ofFn_get] at hobs
  cases hresult : FirstSuccess.indexed (m := Id) (enc.attempt sk.seed message epoch)
      randomizers.length randomizers.get <;>
    simpa only [signResult, IncomparableEncoding.retryIndexed, hresult,
      FirstSuccess.Result.map, FirstSuccess.Result.consumed] using hobs

end GXMSS.PRFDerived
