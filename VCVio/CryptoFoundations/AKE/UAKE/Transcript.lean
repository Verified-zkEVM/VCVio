/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import Mathlib.Data.List.Chain

/-!
# Transcript Definition for UAKE from DF'17

The transcripts in DF'17 bundle messages with timestamps from a global clock
incremented whenever a party sends a message.
-/

namespace AKE.UAKE

variable {W : Type}

/-- A transcript is a list of messages and timestamps. -/
structure Transcript (W : Type) where
  entries : List (W × ℕ)

namespace Transcript

def relabel {A B : Type} (f : A → B) (t : Transcript A) : Transcript B :=
  ⟨t.entries.map fun p => (f p.1, p.2)⟩

def merge {A : Type} (t1 t2 : Transcript A) : Transcript A :=
  ⟨(t1.entries ++ t2.entries).mergeSort fun p q => decide (p.2 ≤ q.2)⟩

def combine {A B : Type} (ta : Transcript A) (tb : Transcript B) :
    Transcript (A ⊕ B) :=
  (ta.relabel Sum.inl).merge (tb.relabel Sum.inr)

def prefixWith {A B : Type} (a : A) (t : ℕ) (tb : Transcript B) :
    Transcript (A ⊕ B) :=
  ⟨(Sum.inl a, t) :: tb.entries.map fun p => (Sum.inr p.1, p.2)⟩

end Transcript

structure Session (σ W : Type) where
  state : σ
  transcript : Transcript W

def interleave : Bool → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | ab, (a, b) :: rest => (if ab then [a, b] else [b, a]) ++ interleave (!ab) rest

/-- Def. 3 from DF'17. A pair of transcripts match (T ⊆ T*) if their messages
   are elementwise identical and their timestamps are "interleaved" as t₁ < t₁*
   < t₂* < t₂ < ... or t₁* < t₁ < t₂ < t₂* < ..., depending on which party
   speaks first. -/
def Matching (oracleLeadsFirst : Bool) (T Tstar : Transcript W) : Prop :=
  T.entries.map Prod.fst = Tstar.entries.map Prod.fst ∧
    List.IsChain (· < ·)
      (interleave oracleLeadsFirst ((T.entries.map Prod.snd).zip (Tstar.entries.map Prod.snd)))

instance [DecidableEq W] (b : Bool) (T Tstar : Transcript W) :
    Decidable (Matching b T Tstar) := by
  unfold Matching
  infer_instance

def pingPong [DecidableEq W] (oracleLeadsFirst : Bool)
    (oracleTrs : List (Transcript W)) (challengeTr : Transcript W) : Bool :=
  oracleTrs.any fun T => decide (Matching oracleLeadsFirst T challengeTr)

def recordOne (tr : Transcript W) (w : W) (clock : ℕ) : Transcript W × ℕ :=
  (⟨tr.entries ++ [(w, clock)]⟩, clock + 1)

def recordOpt (tr : Transcript W) : Option W → ℕ → Transcript W × ℕ
  | none, clock => (tr, clock)
  | some w, clock => recordOne tr w clock

end AKE.UAKE
