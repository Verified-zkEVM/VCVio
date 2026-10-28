/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan
-/

module
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.List.Indexes
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.Support

/-!
# Algebraic interaction with separately tracked group sorts

One adaptive program can send and receive elements in several groups. Each sort has its own
chronological received-input list, and outgoing elements must reconstruct from inputs of the
same sort. Replies extend every sort's list separately, without requiring explanations.

The coefficient type is shared, as for pairing source groups over the same scalar field.
Use `Tag := Unit` and `G := fun _ => G₁` for a single group. No finiteness or decidable
equality on the sort index is needed. Initial generators must be supplied explicitly;
outgoing elements do not extend the received-input lists.

The plain-data/group distinction is syntactic. Games must not hide unlisted group inputs in
plain data, closures, or auxiliary advice. Neither that semantic independence condition nor
computational efficiency is enforced here. This does not supply pairing-product
representations in a target group: those require a different representation rule.

## References

Fuchsbauer, Kiltz, and Loss, *The Algebraic Group Model and its Applications*, Section 2.1:
https://www.iacr.org/archive/crypto2018/10993298/10993298.pdf
-/

public section

namespace GroupModel.Interaction

open OracleComp OracleSpec

variable {Tag : Type}

/-- Received inputs or outgoing values, separated by group sort. -/
abbrev Groups (G : Tag → Type) := (s : Tag) → List (G s)

/-- Append only received values, preserving order and repetitions within each sort. -/
@[expose] def extend {G : Tag → Type} (inputs replies : Groups G) : Groups G :=
  fun s => inputs s ++ replies s

/-- A game message with independently typed group arguments. -/
structure Message (Data : Type) (G : Tag → Type) where
  data : Data
  groups : Groups G

/-- One exact-length coefficient vector for each outgoing element, separately at each sort. -/
structure Explained (F Data : Type) (G : Tag → Type) where
  value : Message Data G
  coefficients : Tag → List (List F)

/-- Evaluate a vector over the chronological list of received group inputs. -/
@[expose] def evaluate {F G : Type} [Zero F] [AddMonoid G] [SMul F G]
    (coeff : List F) (inputs : List G) : G :=
  (inputs.mapIdx fun n g => (coeff[n]?).getD 0 • g).sum

/-- Only inputs of the same sort can explain an outgoing element. -/
@[expose] def Explained.Valid {F Data : Type} {G : Tag → Type}
    [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
    (inputs : Groups G) (out : Explained F Data G) : Prop :=
  ∀ s, List.Forall₂
    (fun g coeff => coeff.length = (inputs s).length ∧ evaluate coeff (inputs s) = g)
    (out.value.groups s) (out.coefficients s)

/-- Construct explanations from vectors indexed by each sort's current basis. -/
@[expose] def Explained.ofVectors {F Data : Type} {G : Tag → Type}
    [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
    (inputs : Groups G) (data : Data) (vectors : (s : Tag) → List (Fin (inputs s).length → F)) :
    Explained F Data G :=
  ⟨⟨data, fun s => (vectors s).map fun v => evaluate (List.ofFn v) (inputs s)⟩,
    fun s => (vectors s).map List.ofFn⟩

theorem Explained.valid_ofVectors {F Data : Type} {G : Tag → Type}
    [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]
    (inputs : Groups G) (data : Data) (vectors : (s : Tag) → List (Fin (inputs s).length → F)) :
    (Explained.ofVectors inputs data vectors).Valid inputs := by
  intro s
  dsimp only [Explained.ofVectors]
  induction vectors s with
  | nil => exact .nil
  | cons v vs ih => exact .cons ⟨by simp, rfl⟩ ih

/-- Plain game oracles may depend on the request's data and receive its actual group arguments. -/
abbrev plainSpec (G : Tag → Type) (Query : Type) (Reply : Query → Type) : OracleSpec
    (Message Query G) :=
  fun q => Message (Reply q.data) G

/-- Adversarial requests carry explanations; oracle replies deliberately do not. -/
abbrev explainedSpec (F : Type) (G : Tag → Type) (Query : Type) (Reply : Query → Type) :
    OracleSpec (Explained F Query G) := fun q => Message (Reply q.value.data) G

variable {F Query Result : Type} {G : Tag → Type} {Reply : Query → Type}

section Algebraicity

variable [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)]

/-- Every outgoing message is explained using only group inputs already received on that path. -/
@[expose] def IsAlgebraic (inputs : Groups G)
    (program : OracleComp (explainedSpec F G Query Reply) (Explained F Result G)) : Prop :=
  OracleComp.recOn (motive := fun _ => Groups G → Prop) program
    (fun out basis => out.Valid basis)
    (fun q _ next basis => q.Valid basis ∧
      ∀ reply, next reply (extend basis reply.groups)) inputs

@[simp] theorem isAlgebraic_pure (inputs : Groups G) (out : Explained F Result G) :
    IsAlgebraic (Reply := Reply) inputs (pure out) ↔ out.Valid inputs := Iff.rfl

@[simp] theorem isAlgebraic_query (inputs : Groups G) (q : Explained F Query G)
    (next : Message (Reply q.value.data) G →
      OracleComp (explainedSpec F G Query Reply) (Explained F Result G)) :
    IsAlgebraic inputs (OracleComp.queryBind q next) ↔
      q.Valid inputs ∧ ∀ reply, IsAlgebraic (extend inputs reply.groups) (next reply) := Iff.rfl

/-- A raw-value adversary with algebraicity evidence on all inputs and reply paths. -/
structure Adversary (F : Type) (G : Tag → Type) (Input Query : Type) (Reply : Query → Type)
    (Result : Type)
    [Zero F] [∀ s, AddMonoid (G s)] [∀ s, SMul F (G s)] where
  main : Message Input G → OracleComp (explainedSpec F G Query Reply) (Explained F Result G)
  algebraic : ∀ input, IsAlgebraic input.groups (main input)

/-- Run a certified adversary, recording only newly received group inputs. -/
@[expose] def Adversary.run {Input : Type} {N : Type → Type} [Monad N]
    (A : Adversary F G Input Query Reply Result)
    (impl : QueryImpl (plainSpec G Query Reply) N) (input : Message Input G) :
    N (Explained F Result G × Groups G) :=
  (simulateQ (fun q => StateT.mk fun basis => do
    let reply ← impl q.value
    pure (reply, extend basis reply.groups)) (A.main input)).run input.groups

/-- Certified execution produces valid final explanations over the actual received inputs. -/
theorem Adversary.run_valid {Input I : Type} {ambient : OracleSpec I}
    (A : Adversary F G Input Query Reply Result)
    (impl : QueryImpl (plainSpec G Query Reply) (OracleComp ambient)) (input : Message Input G)
    (z : Explained F Result G × Groups G) (hz : z ∈ support (A.run impl input)) :
    z.1.Valid z.2 := by
  have h := A.algebraic input
  unfold Adversary.run at hz
  generalize A.main input = program at h hz
  generalize input.groups = basis at h hz
  induction program using OracleComp.inductionOn generalizing basis z with
  | pure out =>
      simpa only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        using hz ▸ h
  | query_bind q next ih =>
      change IsAlgebraic basis (OracleComp.queryBind q next) at h
      obtain ⟨_, hnext⟩ := (isAlgebraic_query basis q next).mp h
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk,
        bind_assoc, pure_bind] at hz
      rw [mem_support_bind_iff] at hz
      obtain ⟨reply, _, hz⟩ := hz
      exact ih reply z _ (hnext reply) hz

end Algebraicity

end GroupModel.Interaction
