/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyTable
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! # Chronological private-oracle programs

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). The public interface has two kinds of group replies.
The private interface supplies their common scalar or mask values. Transcript positions retain
repetitions and query order, including when the two kinds share a cached label.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Randomness and two group-valued interfaces over a common label type. -/
abbrev interfaceSpec (M G : Type) := (unifSpec + (M →ₒ G)) + (M →ₒ G)

/-- Chronological reply labels; `false` denotes the first interface and `true` the second. -/
abbrev Transcript (M : Type) := List (Bool × M)

/-- Answer both interfaces using one private lookup oracle, retaining the chronological labels. -/
@[expose] def transcriptOracle {M R G : Type} (hash sign : R → G) :
    QueryImpl (interfaceSpec M G)
      (StateT (Transcript M) (OracleComp (unifSpec + (M →ₒ R)))) := by
  intro q tr
  rcases q with ((n | m) | m)
  · exact (fun r => (r, tr)) <$> (unifSpec + (M →ₒ R)).query (.inl n)
  · exact (fun r => (hash r, tr ++ [(false, m)])) <$>
      (unifSpec + (M →ₒ R)).query (.inr m)
  · exact (fun r => (sign r, tr ++ [(true, m)])) <$>
      (unifSpec + (M →ₒ R)).query (.inr m)

/-- Public randomness leaves the chronological transcript unchanged. -/
@[simp] theorem transcriptOracle_random {M R G : Type} (hash sign : R → G)
    (n : ℕ) (tr : Transcript M) :
    (transcriptOracle hash sign (.inl (.inl n))).run tr =
      (fun r => (r, tr)) <$> (unifSpec + (M →ₒ R)).query (.inl n) := rfl

/-- A hash reply appends its label at the next chronological position. -/
@[simp] theorem transcriptOracle_hash {M R G : Type} (hash sign : R → G)
    (m : M) (tr : Transcript M) :
    (transcriptOracle hash sign (.inl (.inr m))).run tr =
      (fun r => (hash r, tr ++ [(false, m)])) <$>
        (unifSpec + (M →ₒ R)).query (.inr m) := rfl

/-- A signing reply appends its label at the next chronological position. -/
@[simp] theorem transcriptOracle_sign {M R G : Type} (hash sign : R → G)
    (m : M) (tr : Transcript M) :
    (transcriptOracle hash sign (.inr m)).run tr =
      (fun r => (sign r, tr ++ [(true, m)])) <$>
        (unifSpec + (M →ₒ R)).query (.inr m) := rfl

/-- A fixed pair of public functions supplies replies while preserving ordinary randomness. -/
@[expose] def fixedOracle {M G : Type} (hash sign : M → G) :
    QueryImpl (interfaceSpec M G) (StateT (Transcript M) ProbComp) := by
  intro q tr
  rcases q with ((n | m) | m)
  · exact (fun r => (r, tr)) <$> (unifSpec.query n : ProbComp _)
  · exact pure (hash m, tr ++ [(false, m)])
  · exact pure (sign m, tr ++ [(true, m)])

/-- Fixed-table execution, retaining every group-reply occurrence. -/
@[expose] def fixedRun {M G α : Type} (hash sign : M → G)
    (oa : OracleComp (interfaceSpec M G) α) : ProbComp (α × Transcript M) :=
  (simulateQ (fixedOracle hash sign) oa).run []

private theorem table_random {M R : Type} (table : M → R) (n : ℕ) :
    unifFwdAnswerImpl (QueryImpl.ofFn table) (.inl n) =
      (unifSpec.query n : ProbComp _) := rfl

private theorem table_lookup {M R : Type} (table : M → R) (m : M) :
    unifFwdAnswerImpl (QueryImpl.ofFn table) (.inr m) = pure (table m) := rfl

/-- Interpreting the private oracle by a table gives exactly fixed-table transcript execution. -/
theorem transcriptOracle_table {M R G α : Type} (table : M → R) (hash sign : R → G)
    (oa : OracleComp (interfaceSpec M G) α) (tr : Transcript M) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((simulateQ (transcriptOracle hash sign) oa).run tr) =
      (simulateQ (fixedOracle (hash ∘ table) (sign ∘ table)) oa).run tr := by
  apply simulateQ_StateT_compose
  intro q tr
  rcases q with ((n | m) | m) <;>
    simp [StateT.run, transcriptOracle, fixedOracle, table_random, table_lookup]

/-- Read each chronological label through the private oracle and interpret its reply kind. -/
@[expose] def readTranscript {M R V : Type} (hash sign : R → V) :
    Transcript M → OracleComp (unifSpec + (M →ₒ R)) (List V)
  | [] => pure []
  | (kind, m) :: rest => do
      let r ← (unifSpec + (M →ₒ R)).query (.inr m)
      let vs ← readTranscript hash sign rest
      return (if kind then sign r else hash r) :: vs

/-- Fixed-table interpretation of chronological extraction lookups. -/
theorem readTranscript_table {M R V : Type} (table : M → R) (hash sign : R → V)
    (tr : Transcript M) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table)) (readTranscript hash sign tr) =
      pure (tr.map fun q => if q.1 then sign (table q.2) else hash (table q.2)) := by
  induction tr with
  | nil => simp [readTranscript]
  | cons q rest ih =>
      rcases q with ⟨kind, m⟩
      simp [readTranscript, table_lookup, ih]

/-- Execute an adaptive program and look up its final target without adding the verification
lookup to the transcript of received inputs. -/
@[expose] def targetProgram {M R G α : Type} (target : α → M)
    (hash sign : R → G) (oa : OracleComp (interfaceSpec M G) α) :
    OracleComp (unifSpec + (M →ₒ R)) (α × Transcript M × R) := do
  let (out, tr) ← (simulateQ (transcriptOracle hash sign) oa).run []
  let r ← (unifSpec + (M →ₒ R)).query (.inr (target out))
  return (out, tr, r)

/-- A fixed table supplies the execution and final target from the same values. -/
theorem targetProgram_table {M R G α : Type} (table : M → R) (target : α → M)
    (hash sign : R → G) (oa : OracleComp (interfaceSpec M G) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (targetProgram target hash sign oa) =
      (fun z => (z.1, z.2, table (target z.1))) <$>
        fixedRun (hash ∘ table) (sign ∘ table) oa := by
  simp [targetProgram, transcriptOracle_table, table_lookup, fixedRun]

/-- Execute an adaptive program, recover representations from its reply labels, and query its
final target through the same private oracle. Initial group inputs precede all replies. -/
@[expose] def extractionProgram {M R G V α : Type} (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec M G) α) :
    OracleComp (unifSpec + (M →ₒ R)) (α × List V × R) := do
  let (out, tr) ← (simulateQ (transcriptOracle hash sign) oa).run []
  let basis ← readTranscript hashRep signRep tr
  let r ← (unifSpec + (M →ₒ R)).query (.inr (target out))
  return (out, initial ++ basis, r)

/-- A fixed table jointly interprets the execution, extracted basis, and final target lookup. -/
theorem extractionProgram_table {M R G V α : Type} (table : M → R) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec M G) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (extractionProgram target hash sign hashRep signRep initial oa) =
      (fun z => (z.1, initial ++ z.2.map
        (fun q => if q.1 then signRep (table q.2) else hashRep (table q.2)),
        table (target z.1))) <$>
        fixedRun (hash ∘ table) (sign ∘ table) oa := by
  simp [extractionProgram, transcriptOracle_table, readTranscript_table,
    table_lookup, fixedRun]

end GroupModel.LinearFunctional
