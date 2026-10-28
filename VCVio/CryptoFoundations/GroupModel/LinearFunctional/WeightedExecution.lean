/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedOracle
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Interaction
public import VCVio.OracleComp.SimSemantics.StateT.Basic

/-! # Chronological execution of weighted signature queries

Hash labels and messages have independent types. A signing request combines a finite list of
bases through the same private oracle used for direct hash requests. Only the returned group
point extends the chronological transcript. Extraction replays these labels through the shared
cache, preserving occurrences and order without enumerating either type.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional.Weighted

/-- Randomness, base queries, and message-signing queries. -/
abbrev interfaceSpec (I M G : Type) := (unifSpec + (I →ₒ G)) + (M →ₒ G)

/-- Chronological occurrences of public hash and signing replies. -/
abbrev Transcript (I M : Type) := List (I ⊕ M)

/-- Interpret a weighted list using a fixed table. -/
@[expose] def value {F I R : Type} [AddMonoid R] [SMul F R]
    (table : I → R) (ts : List (I × F)) : R := (ts.map fun t => t.2 • table t.1).sum

/-- A private oracle supplies bases shared by direct hashing and weighted signing. -/
@[expose] def oracle {F I M R G : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → G) :
    QueryImpl (interfaceSpec I M G)
      (StateT (Transcript I M) (OracleComp (unifSpec + (I →ₒ R)))) := by
  intro q tr
  rcases q with ((n | i) | m)
  · exact (fun r => (r, tr)) <$> (unifSpec + (I →ₒ R)).query (.inl n)
  · exact (fun r => (hash r, tr ++ [.inl i])) <$>
      (unifSpec + (I →ₒ R)).query (.inr i)
  · exact (fun r => (sign r, tr ++ [.inr m])) <$> weightedQuery (terms m)

/-- Randomness leaves the chronological transcript unchanged. -/
@[simp] theorem oracle_run_random {F I M R G : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → G) (n : ℕ) (tr : Transcript I M) :
    (oracle terms hash sign (.inl (.inl n))).run tr =
      (fun r => (r, tr)) <$> (unifSpec.query n : OracleComp (unifSpec + (I →ₒ R)) _) := rfl

/-- A base-hash reply contributes exactly one chronological occurrence. -/
@[simp] theorem oracle_run_hash {F I M R G : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → G) (i : I) (tr : Transcript I M) :
    (oracle terms hash sign (.inl (.inr i))).run tr =
      (fun r => (hash r, tr ++ [.inl i])) <$>
        ((I →ₒ R).query i : OracleComp (unifSpec + (I →ₒ R)) _) := rfl

/-- A weighted signing reply contributes one occurrence after all its private base lookups. -/
@[simp] theorem oracle_run_sign {F I M R G : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → G) (m : M) (tr : Transcript I M) :
    (oracle terms hash sign (.inr m)).run tr =
      (fun r => (sign r, tr ++ [.inr m])) <$> weightedQuery (terms m) := rfl

/-- A fixed pair of functions answers public queries and records reply occurrences. -/
@[expose] def fixedOracle {I M G : Type} (hash : I → G) (sign : M → G) :
    QueryImpl (interfaceSpec I M G) (StateT (Transcript I M) ProbComp) := by
  intro q tr
  rcases q with ((n | i) | m)
  · exact (fun r => (r, tr)) <$> (unifSpec.query n : ProbComp _)
  · exact pure (hash i, tr ++ [.inl i])
  · exact pure (sign m, tr ++ [.inr m])

/-- Execute a public program at fixed hash and signing functions. -/
@[expose] def fixedRun {I M G α : Type} (hash : I → G) (sign : M → G)
    (oa : OracleComp (interfaceSpec I M G) α) : ProbComp (α × Transcript I M) :=
  (simulateQ (fixedOracle hash sign) oa).run []

private theorem table_random {I R : Type} (table : I → R) (n : ℕ) :
    unifFwdAnswerImpl (QueryImpl.ofFn table) (.inl n) =
      (unifSpec.query n : ProbComp _) := rfl

private theorem table_lookup {I R : Type} (table : I → R) (i : I) :
    unifFwdAnswerImpl (QueryImpl.ofFn table) (.inr i) = pure (table i) := rfl

/-- Fixed-table interpretation commutes with chronological weighted execution. -/
theorem oracle_table {F I M R G α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R) (hash sign : R → G)
    (oa : OracleComp (interfaceSpec I M G) α) (tr : Transcript I M) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      ((simulateQ (oracle terms hash sign) oa).run tr) =
      (simulateQ (fixedOracle (hash ∘ table)
        (fun m => sign (value table (terms m)))) oa).run tr := by
  apply simulateQ_StateT_compose
  intro q tr
  rcases q with ((n | i) | m) <;>
    simp [StateT.run, oracle, fixedOracle, table_random, table_lookup, weightedQuery_table, value]

/-- Replay public reply occurrences to recover their scalar or affine representations. -/
@[expose] def readTranscript {F I M R V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (hash sign : R → V) :
    Transcript I M → OracleComp (unifSpec + (I →ₒ R)) (List V)
  | [] => pure []
  | .inl i :: rest => do
      let r ← (unifSpec + (I →ₒ R)).query (.inr i)
      let vs ← readTranscript terms hash sign rest
      return hash r :: vs
  | .inr m :: rest => do
      let r ← weightedQuery (terms m)
      let vs ← readTranscript terms hash sign rest
      return sign r :: vs

/-- Replay at a fixed table gives the chronological list of reply representations. -/
theorem readTranscript_table {F I M R V : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R) (hash sign : R → V)
    (tr : Transcript I M) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (readTranscript terms hash sign tr) =
      pure (tr.map (Sum.elim (hash ∘ table) (fun m => sign (value table (terms m))))) := by
  induction tr with
  | nil => simp [readTranscript]
  | cons q rest ih =>
      cases q <;> simp [readTranscript, table_lookup, weightedQuery_table, value, ih]

/-- Run the adversary, replay its reply representations, and evaluate its final weighted target. -/
@[expose] def extractionProgram {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec I M G) α) :
    OracleComp (unifSpec + (I →ₒ R)) (α × List V × R) := do
  let (out, tr) ← (simulateQ (oracle terms hash sign) oa).run []
  let basis ← readTranscript terms hashRep signRep tr
  let r ← weightedQuery (terms (target out))
  return (out, initial ++ basis, r)

/-- One fixed table supplies the execution, chronological representations, and final target. -/
theorem extractionProgram_table {F I M R G V α : Type} [AddMonoid R] [SMul F R]
    (terms : M → List (I × F)) (table : I → R) (target : α → M)
    (hash sign : R → G) (hashRep signRep : R → V) (initial : List V)
    (oa : OracleComp (interfaceSpec I M G) α) :
    simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn table))
      (extractionProgram terms target hash sign hashRep signRep initial oa) =
      (fun z => (z.1, initial ++ z.2.map
        (Sum.elim (hashRep ∘ table) (fun m => signRep (value table (terms m)))),
        value table (terms (target z.1)))) <$>
        fixedRun (hash ∘ table) (fun m => sign (value table (terms m))) oa := by
  simp [extractionProgram, oracle_table, readTranscript_table, weightedQuery_table, value, fixedRun]

end GroupModel.LinearFunctional.Weighted
