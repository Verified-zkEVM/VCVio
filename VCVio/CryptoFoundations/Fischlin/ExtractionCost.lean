/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction
import all VCVio.CryptoFoundations.Fischlin.KnowledgeSoundness.Extraction

/-!
# Record inspections in Fischlin's online extractor

An instrumented `findSome?` counts log records inspected by the actual nested search.
Erasing the counter recovers `onlineExtract` as a program equality. Each inspected record
may compare an entire commitment vector and evaluate the Σ-verifier; a record inspection
is not a constant-time machine instruction or a random-oracle query.
-/

public section

open OracleComp OracleSpec

namespace Fischlin

private def scanWithCost {A B : Type} (f : A → Option B × ℕ) : List A → Option B × ℕ
  | [] => (none, 0)
  | x :: xs =>
    let (result, cost) := f x
    match result with
    | some y => (some y, cost)
    | none =>
      let (tail, tailCost) := scanWithCost f xs
      (tail, cost + tailCost)

private theorem scanWithCost_fst {A B : Type} (f : A → Option B × ℕ) (xs : List A) :
    (scanWithCost f xs).1 = xs.findSome? (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [scanWithCost, List.findSome?_cons]
    cases (f x).1 <;> simp [ih]

private theorem scanWithCost_le {A B : Type} (f : A → Option B × ℕ)
    (xs : List A) (k : ℕ) (hk : ∀ x ∈ xs, (f x).2 ≤ k) :
    (scanWithCost f xs).2 ≤ xs.length * k := by
  induction xs with
  | nil => simp [scanWithCost]
  | cons x xs ih =>
    have hx := hk x (by simp)
    have ht := ih (fun y hy => hk y (by simp [hy]))
    simp only [scanWithCost]
    cases (f x).1 <;> simp only [List.length_cons, Nat.add_mul, Nat.one_mul] <;> omega

private theorem scanWithCost_none {A B : Type} (xs : List A) :
    scanWithCost (fun _ => ((none : Option B), 0)) xs = (none, 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scanWithCost, ih, zero_add]

variable {Stmt Wit Commit PrvState Chal Resp : Type} {rel : Stmt → Wit → Bool}
variable [DecidableEq Stmt] [DecidableEq Commit] [DecidableEq Chal]
variable (σ : SigmaProtocol Stmt Wit Commit PrvState Chal Resp rel) (ρ b : ℕ) (M : Type)

private def scanRecords (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    Option (Chal × Resp × Chal × Resp) × ℕ :=
  scanWithCost (fun i : Fin ρ =>
    scanWithCost (fun entry =>
      (if entry.1.stmt == x && entry.1.comList == List.ofFn (fun j => (π j).1) &&
          entry.1.rep == i && σ.verify x (π i).1 entry.1.chal entry.1.resp &&
          decide (entry.1.chal ≠ (π i).2.1) then
        some ((π i).2.1, (π i).2.2, entry.1.chal, entry.1.resp)
      else none, 1)) log) (List.finRange ρ)

private theorem scanRecords_fst (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    (scanRecords σ ρ b M x π log).1 = fischlinFindWitness σ ρ b M x π log := by
  simp [scanRecords, scanWithCost_fst, fischlinFindWitness]

/-- Counted record inspections, with the same optional witness as the actual online extractor. -/
def onlineExtractWithScanCount (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    ProbComp (Option Wit × ℕ) := do
  let (result, cost) := scanRecords σ ρ b M x π log
  let witness ← match result with
    | some (c₁, r₁, c₂, r₂) => some <$> σ.extract c₁ r₁ c₂ r₂
    | none => pure none
  return (witness, cost)

/-- An empty query log contains no records to inspect. -/
theorem onlineExtractWithScanCount_nil (x : Stmt) (π : FischlinProof Commit Chal Resp ρ) :
    onlineExtractWithScanCount σ ρ b M x π [] = pure (none, 0) := by
  simp only [onlineExtractWithScanCount, scanRecords, scanWithCost, scanWithCost_none, pure_bind]

/-- With no repetitions the extractor never inspects the log. -/
theorem onlineExtractWithScanCount_zero (x : Stmt) (π : FischlinProof Commit Chal Resp 0)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp 0 b M)) :
    onlineExtractWithScanCount σ 0 b M x π log = pure (none, 0) := by
  simp only [onlineExtractWithScanCount, scanRecords, List.finRange_zero, scanWithCost, pure_bind]

/-- A matching first record at the sole repetition stops the scan after one inspection. -/
theorem onlineExtractWithScanCount_cons_of_match (x : Stmt)
    (π : FischlinProof Commit Chal Resp 1)
    (e : (_t : FischlinROInput Stmt Commit Chal Resp 1 M) × Fin (2 ^ b))
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp 1 b M))
    (hx : e.1.stmt = x) (hcom : e.1.comList = List.ofFn (fun j => (π j).1))
    (hv : σ.verify x (π 0).1 e.1.chal e.1.resp = true)
    (hne : e.1.chal ≠ (π 0).2.1) :
    onlineExtractWithScanCount σ 1 b M x π (e :: log) =
      (fun w => (some w, 1)) <$> σ.extract (π 0).2.1 (π 0).2.2 e.1.chal e.1.resp := by
  have hrep : e.1.rep = 0 := Subsingleton.elim _ _
  simp [onlineExtractWithScanCount, scanRecords, show List.finRange 1 = [0] from rfl, scanWithCost,
    hx, hcom, hv, hne, hrep, monad_norm]

/-- Erasing the inspection count recovers the actual extractor, including its failure branch. -/
theorem onlineExtractWithScanCount_fst (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M)) :
    Prod.fst <$> onlineExtractWithScanCount σ ρ b M x π log =
      onlineExtract σ ρ b M x π log := by
  simp only [onlineExtractWithScanCount]
  rw [scanRecords_fst, onlineExtract_eq_match]
  cases fischlinFindWitness σ ρ b M x π log with
  | none => simp
  | some result => rcases result with ⟨c₁, r₁, c₂, r₂⟩; simp [monad_norm]

/-- The nested search inspects at most `ρ * log.length` records. This counts repeated visits
across repetitions; comparing commitment vectors or evaluating the verifier has separate cost. -/
theorem onlineExtractWithScanCount_le (x : Stmt) (π : FischlinProof Commit Chal Resp ρ)
    (log : QueryLog (fischlinROSpec Stmt Commit Chal Resp ρ b M))
    {z : Option Wit × ℕ} (hz : z ∈ support (onlineExtractWithScanCount σ ρ b M x π log)) :
    z.2 ≤ ρ * log.length := by
  have hs : (scanRecords σ ρ b M x π log).2 ≤ ρ * log.length := by
    unfold scanRecords
    simpa using scanWithCost_le _ (List.finRange ρ) log.length (by
      intro i _
      simpa using scanWithCost_le _ log 1 (by simp))
  cases hscan : scanRecords σ ρ b M x π log with
  | mk result cost =>
    rw [hscan] at hs
    simp only [onlineExtractWithScanCount, hscan] at hz
    cases result with
    | none =>
      simp only [pure_bind, mem_support_pure_iff] at hz
      subst z
      exact hs
    | some result =>
      rcases result with ⟨c₁, r₁, c₂, r₂⟩
      simp only [mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨w, _, rfl⟩ := hz
      exact hs

end Fischlin
