/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Tactics.Unary

/-!
# Program-equality examples

`prrw` proves equalities between the `Pr{…}[…]` events of two programs: `prrw` swaps adjacent
independent binds, `prrw under n` swaps them under `n` shared prefixes, `prrw congr` and
`prrw congr'` reduce a shared prefix, and `prrw normalize` searches for a sequence of these steps
that closes the goal. Oracle responses carry a chosen discrete measure specification; swaps use
countable responses, and congruence leaves the continuations on the structural support of the
shared prefix.
-/

@[expose] public section

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

variable {ι : Type} {spec : OracleSpec ι}
  [∀ t, Countable (spec.Range t)] [OracleSpec.AnswerMeasure spec]
variable {α β γ δ ε ζ : Type}

/-! ## Congruence -/

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x ∈ support mx, Pr{let y ← f x}[q y] = Pr{let y ← g x}[q y]) :
    Pr{let y ← mx >>= f}[q y] = Pr{let y ← mx >>= g}[q y] := by
  prrw congr
  exact h _ ‹_›

/-! ## Bind swap -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {y : γ} :
    Pr{let x ← mx >>= fun a => my >>= fun b => f a b}[x = y] =
    Pr{let x ← my >>= fun b => mx >>= fun a => f a b}[x = y] := by
  prrw

/-! ## Swaps under a shared prefix -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {mz : OracleComp spec γ} {f : α → β → γ → OracleComp spec δ} {q : δ → Prop} :
    Pr{let r ← mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c}[q r] =
    Pr{let r ← mx >>= fun a => mz >>= fun c => my >>= fun b => f a b c}[q r] := by
  prrw under 1

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec ε} {out : ε} :
    Pr{let v ← mw >>= fun w => mx >>= fun x => my >>= fun y => mz >>= fun z => f w x y z}[
        v = out] =
    Pr{let v ← mw >>= fun w => mx >>= fun x => mz >>= fun z => my >>= fun y => f w x y z}[
        v = out] := by
  prrw under 2

/-! ## Searching for the swaps -/

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec ε} {q : ε → Prop} :
    Pr{let r ← mw >>= fun w => mx >>= fun x => my >>= fun y => mz >>= fun z => f w x y z}[q r] =
    Pr{let r ← mw >>= fun w => mx >>= fun x => mz >>= fun z => my >>= fun y => f w x y z}[q r] := by
  prrw normalize

example {mv : OracleComp spec α} {mw : OracleComp spec β}
    {mx : OracleComp spec γ} {my : OracleComp spec δ} {mz : OracleComp spec ε}
    {f : α → β → γ → δ → ε → OracleComp spec ζ} {out : ζ} :
    Pr{let u ← (mv >>= fun v => mw >>= fun w => mx >>= fun x => my >>= fun y => mz >>= fun z =>
        f v w x y z)}[u = out] =
    Pr{let u ← (mv >>= fun v => mw >>= fun w => mx >>= fun x => mz >>= fun z => my >>= fun y =>
        f v w x y z)}[u = out] := by
  prrw normalize

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec (Bool × ε)} :
    Pr{let w ← mw; let x ← mx; let b ← (Prod.fst <$> (do
        let y ← my
        let z ← mz
        f w x y z))}[b = true] =
    Pr{let w ← mw; let x ← mx; let b ← (Prod.fst <$> (do
        let z ← mz
        let y ← my
        f w x y z))}[b = true] := by
  prrw normalize

example {mw : OracleComp spec α} {mx : OracleComp spec β} {my : OracleComp spec γ}
    {f : α → β → γ → δ} {out : δ} :
    Pr{let w ← mw; let x ← mx; let z ← f w x <$> my}[z = out] =
    Pr{let x ← mx; let w ← mw; let z ← f w x <$> my}[z = out] := by
  prrw normalize

/-! ## Congruence without support hypotheses -/

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr{let y ← f x}[q y] = Pr{let y ← g x}[q y]) :
    Pr{let y ← mx >>= f}[q y] = Pr{let y ← mx >>= g}[q y] := by
  prrw congr'
  exact h _
