/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.FreshL
import VCVio.OracleComp.EvalDist.Measure
import VCVio.EvalDist.ProbabilityBounds
import ToMathlib.Data.Nat.Log

/-!
# The oracle rules: Rw-Oracle and Pc-Oracle

CCS26 Fig. 3 (p. 7) has two rules with an oracle, a term `o` of type `a → b` with `a` a Boolean or
base type, on the left of a non-deduction:

```
u⃗, o₂ ⊬ v    ∀̃ m. (u⃗, o₁ ▷ m) ⇒̃ [o₁(m) = o₂(m)]                        (Rw-Oracle)
-------------------------------------------------
                 u⃗, o₁ ⊬ v

u⃗, o′ ⊬ v    u⃗, o′ ⊬ m       where o′ = λx. if x ≠ m then o(x) else w      (Pc-Oracle)
-------------------------
       u⃗, o ⊬ v
```

App. C.1 (pp. 15–16) proves Rw-Oracle as a "double rule", with the deduction in the second premise
from `u⃗, o_β` for `β = 1, 2`, and derives Pc-Oracle from the case `β = 2`.

## The proof, as in App. C.1

* **Identical until bad** (step 1, `deduceAdv_le_add_faulty`): the attacker machine `g`, run with
  `o₁` and with `o₂`, gives the same result unless the run with `o_β` queries the oracle at a point
  where the two differ (`faultyAt`). The proof is `Machine.run_cons_eq_of_firstArgs` at each tape,
  for the machine `AdvMachine.withOracleFirst`, which takes the oracle as its first input.
* **The guess** (step 2, `prEvent_faultyAt_le`): the reduction `AdvMachine.rwGuess` reads `j`
  from `⌈log₂ q(η)⌉` bits of `ρa` above the read bounds of `g`, `u⃗`, `o₁` and `o₂`, runs `g` with
  `o_β`, and returns the argument of `g`'s `j`-th oracle query (`Machine.guess`). Over uniform tapes
  (`sum_prEvent_eq_two_pow_mul`), the probability that some query of `g` is faulty is at most
  `2 ^ ⌈log₂ q(η)⌉` times the probability that the guess is a faulty point, where `q` bounds `g`'s
  queries (`AdvClass.queryBound_mem`); `2 ^ ⌈log₂ q⌉ ≤ 2q + 1` (`Nat.pow_clog_le_mul_add_one`).
* **The premise** is used at `m := rwGuess(u⃗, o_β)`, which `u⃗, o_β ▷ m` holds of with the guess as
  witness, so `[o₁(m) = o₂(m)]` bounds the guess's success.

At each `η` where the drawn bits fit on the tape:

`deduceAdv g (u⃗, o₁) v η ≤ deduceAdv g (u⃗, o₂) v η + 2 ^ ⌈log₂ q(η)⌉ · Pr[o₁(m) ≠ o₂(m)]`.

## What the formalization adds

* **Shared tape.** `j` must be independent of everything the run and the terms read, so the terms
  `u⃗`, `o₁` and `o₂` read `ρa` below a polynomial (`FTerm.ReadsPoly`), and the tapes are long
  (`Model.LongTapes`): the conditions of FreshL. CCS26 says only that `B` uses "a part of `ρa`
  further away".
* **The default.** `A_j` returns "a default value empty if there is no such call". Carriers here
  need not contain the empty bitstring, so the guess draws its default with the model's sampler of
  the argument type (`Machine.sampler`), which the class admits for types with polynomial bit
  blocks: the model condition `Model.PolyCoins a`.
* **Ground right side.** `v` has Boolean or base type: a deduction of a function would compare the
  attacker's function with `v` at every argument, and the guess could not know which argument
  matters (as for Rw-Equiv).
* **Answer sizes.** The guess never computes `o₁` or `o₂`: it forwards `g`'s queries to its own
  oracle input and keeps their arguments (`AdvClass.guess_mem`). Answers are typed values passed
  by the handler, so no premise on their size is needed; a class whose machines pay for copying
  answers would have to meet `guess_mem` with such a premise.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: Fig. 3 and App. C.1.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec

variable {B : Type} {D : Decl B} {M : Model D} {τs : List (Ty B)} {a b β : Ty B}

/-! ## Moving the oracle first -/

namespace Machine

/-- The renaming that moves the oracle, the last entry of the tuple `τs ++ [σ]`, first; a Boolean
or base result type has no arguments; the inputs `Γ` follow the tuple, unused. -/
@[expose] def oracleFirst (τs : List (Ty B)) (σ : Ty B) (hβ : β.IsGround) (Γ : List (Ty B)) :
    Renaming ((τs ++ [σ]) ++ β.args) (σ :: (τs ++ Γ)) :=
  Env.append (Env.append (fun _ x => .succ (x.appendLeft Γ)) (Env.cons .zero Env.empty))
    (Renaming.ofGround hβ)

private theorem rename_oracleFirst {η : ℕ} {σ : Ty B} {Γ : List (Ty B)} (hβ : β.IsGround)
    (o : σ.Value M.carrier η) (e : Vals M η τs) (w : Vals M η Γ) :
    Env.rename (oracleFirst τs σ hβ Γ) (Env.cons o (Env.append e w)) =
      Env.append (Env.append e (Env.cons o Env.empty)) (Ty.groundArgs hβ) := by
  rw [oracleFirst, Env.rename_append_renaming, Env.rename_append_renaming,
    Ty.eq_groundArgs hβ (Env.rename (Renaming.ofGround hβ) _)]
  congr 2
  · funext _ x
    exact Env.append_appendLeft e w x
  · funext _ x
    cases x with
    | zero => rfl
    | succ x => exact nomatch x

/-- The renaming that moves the first input, the oracle, back to the end of the tuple. -/
@[expose] def firstLast (τs : List (Ty B)) (σ : Ty B) (Γ : List (Ty B)) :
    Renaming (σ :: (τs ++ Γ)) ((τs ++ [σ]) ++ Γ) :=
  Env.cons (((ScopedVar.zero : ScopedVar [σ] σ).weakenMany τs).appendLeft Γ)
    (Env.append (fun _ x => (x.appendLeft [σ]).appendLeft Γ)
      fun _ x => x.weakenMany (τs ++ [σ]))

private theorem rename_firstLast {η : ℕ} {σ : Ty B} {Γ : List (Ty B)} (o : σ.Value M.carrier η)
    (e : Vals M η τs) (w : Vals M η Γ) :
    Env.rename (firstLast τs σ Γ) (Env.append (Env.append e (Env.cons o Env.empty)) w) =
      Env.cons o (Env.append e w) := by
  funext τ x
  cases x with
  | zero => exact (Env.append_appendLeft _ _ _).trans (Env.append_weakenMany _ _ _)
  | succ x =>
    refine congrFun (congrFun (?_ : Env.rename (Env.append
      (fun _ x => (x.appendLeft [σ]).appendLeft Γ) fun _ x => x.weakenMany (τs ++ [σ])) _ =
        Env.append e w) τ) x
    rw [Env.rename_append_renaming, Env.rename_weakenMany_append]
    congr 1
    funext _ y
    exact (Env.append_appendLeft _ _ _).trans (Env.append_appendLeft _ _ _)

end Machine

namespace AdvMachine

/-- An attacker machine against `u⃗, o ⊢ v`, with a Boolean or base right side, as a machine whose
first input is the oracle; the inputs `a.args` (none, for a Boolean or base `a`) follow the
tuple. -/
@[expose] def withOracleFirst (hβ : β.IsGround) (g : AdvMachine M (τs ++ [.arrow a b]) β) :
    Machine M (.arrow a b :: (τs ++ a.args)) β.res :=
  g.rename (Machine.oracleFirst τs (.arrow a b) hβ a.args)

theorem appVals_eval_eq_withOracleFirst {η : ℕ} (ha : a.IsGround) (hβ : β.IsGround)
    (g : AdvMachine M (τs ++ [.arrow a b]) β) (ρa : M.TapeA η) (e : Vals M η τs)
    (o : (Ty.arrow a b).Value M.carrier η) :
    Ty.appVals (g.eval η ρa) (Env.append e (Env.cons o Env.empty)) =
      Ty.ofRes hβ ((g.withOracleFirst hβ).run η ρa
        (Env.cons o (Env.append e (Ty.groundArgs ha)))) := by
  rw [appVals_eval, Ty.curry_eq_ofRes hβ, withOracleFirst, Machine.run_rename,
    Machine.rename_oracleFirst]

/-- **The guessing reduction of Rw-Oracle** (CCS26 App. C.1, p. 15): read `j` from
`⌈log₂ q(η)⌉` bits of the attacker tape from bit `p(η)`, run `g` with the oracle first, and return
the argument of its `j`-th oracle query; if there is none, a value of the argument type drawn by
the model's sampler (CCS26's default value). -/
@[expose] def rwGuess (p q : Polynomial ℕ) (ha : a.IsGround) (hβ : β.IsGround)
    (g : AdvMachine M (τs ++ [.arrow a b]) β) : AdvMachine M (τs ++ [.arrow a b]) a :=
  ((g.withOracleFirst hβ).guess (fun η => p.eval η) (fun η => Nat.clog 2 (q.eval η)) ha
      ((Machine.sampler a ((Ty.isGround_iff_order_eq_zero.1 ha).trans_le zero_le_one)).rename
        fun _ y => .succ (y.weakenMany τs))).rename
    (Machine.firstLast τs (.arrow a b) a.args)

/-- The guessing reduction returns the argument of the `j`-th oracle query, when there is one. -/
theorem appVals_eval_rwGuess {η : ℕ} {p q : Polynomial ℕ} (ha : a.IsGround) (hβ : β.IsGround)
    (g : AdvMachine M (τs ++ [.arrow a b]) β) (ρa : M.TapeA η) (e : Vals M η τs)
    (o : (Ty.arrow a b).Value M.carrier η) {x : Vals M η (Ty.arrow a b).args}
    (hx : (M.firstArgs (runLog (M.answer ρa (Env.cons o (Env.append e (Ty.groundArgs ha))))
      ((g.withOracleFirst hβ) η)))[(bitsEquiv (Nat.clog 2 (q.eval η))
        (M.bitsAt ρa (p.eval η) (Nat.clog 2 (q.eval η))) : ℕ)]? = some x) :
    Ty.appVals ((g.rwGuess p q ha hβ).eval η ρa) (Env.append e (Env.cons o Env.empty)) =
      x _ .zero := by
  rw [appVals_eval, Ty.curry_eq_ofRes ha, rwGuess, Machine.run_rename, Machine.rename_firstLast,
    Machine.run_guess, hx]
  exact Ty.ofRes_apply_groundArgs ha _

end AdvMachine

/-- The reduction of Rw-Oracle is admitted, for an argument type with polynomial bit blocks. -/
theorem AdvClass.rwGuess_mem (C : AdvClass M) (p q : Polynomial ℕ) (ha : a.IsGround)
    (hβ : β.IsGround) (hc : M.PolyCoins a) {g : AdvMachine M (τs ++ [.arrow a b]) β}
    (hg : C.mem g) : C.mem (g.rwGuess p q ha hβ) :=
  C.rename_mem _ (C.guess_mem p q ha (C.rename_mem _ hg) (C.rename_mem _ (C.sampler_mem _ hc)))

/-! ## The bound at one security parameter -/

section Bound

variable (ha : a.IsGround) (hβ : β.IsGround) (g : AdvMachine M (τs ++ [.arrow a b]) β)
  (u : VecRV M τs)

/-- CCS26's `E^{ρ,η}`: the run of the attacker machine with the oracle `o` queries it at a point
where `o` and `o'` differ. -/
@[expose] def faultyAt (o o' : RV M (.arrow a b)) (η : ℕ) (ρ : M.Tape η) : Prop :=
  ∃ x ∈ M.firstArgs (runLog (M.answer ρ.1 (Env.cons (o η ρ) (Env.append (u η ρ)
      (Ty.groundArgs ha)))) ((g.withOracleFirst hβ) η)),
    o η ρ (x _ .zero) ≠ o' η ρ (x _ .zero)

/-- **Identical until bad** (CCS26 App. C.1, step 1): where the run with `o` makes no faulty
query, `g` computes the same from `u⃗, o` and from `u⃗, o'`, so the two successes differ by at most
the probability of a faulty query, in either direction. -/
theorem deduceAdv_le_add_faulty (v : RV M β) (o o' : RV M (.arrow a b)) (η : ℕ) :
    deduceAdv g.eval (VecRV.snoc u o) v η ≤
        deduceAdv g.eval (VecRV.snoc u o') v η +
          Pr{let ρ ← $ᵗ (M.Tape η)}[faultyAt ha hβ g u o o' η ρ] ∧
      deduceAdv g.eval (VecRV.snoc u o') v η ≤
        deduceAdv g.eval (VecRV.snoc u o) v η +
          Pr{let ρ ← $ᵗ (M.Tape η)}[faultyAt ha hβ g u o o' η ρ] := by
  have hrun : ∀ ρ : M.Tape η, ¬ faultyAt ha hβ g u o o' η ρ →
      Ty.appVals (g.eval η ρ.1) (VecRV.snoc u o η ρ) =
        Ty.appVals (g.eval η ρ.1) (VecRV.snoc u o' η ρ) := fun ρ hρ => by
    simp only [VecRV.snoc]
    rw [AdvMachine.appVals_eval_eq_withOracleFirst ha,
      AdvMachine.appVals_eval_eq_withOracleFirst ha,
      Machine.run_cons_eq_of_firstArgs _ fun x hx => by_contra fun hne => hρ ⟨x, hx, hne⟩]
  refine ⟨prEvent_le_prEvent_add_prEvent_of_imp _ fun ρ h hρ => ?_,
    prEvent_le_prEvent_add_prEvent_of_imp _ fun ρ h hρ => ?_⟩
  · exact (hrun ρ hρ).symm.trans h
  · exact (hrun ρ hρ).trans h

/-- **The guessing bound**, for any event on the queried point (CCS26 App. C.1, step 2). Let `g`
read the attacker tape below `p` and make at most `q` input queries, `u⃗` and `o` read it below
`p`, and the event `S` on a point of `a` read it below `p` too. At an `η` where `⌈log₂ q(η)⌉` bits
from `p(η)` fit on the tape, the probability that the run with `o` queries the oracle at a point
where `S` holds is at most `2 ^ ⌈log₂ q(η)⌉` times the probability that `S` holds at the output of
the reduction `AdvMachine.rwGuess`, run with `o`. -/
theorem prEvent_exists_firstArgs_le {p q : Polynomial ℕ}
    (hg : Machine.ReadsBelow g fun η => p.eval η) (hq : Machine.QueryBound g fun η => q.eval η)
    (o : RV M (.arrow a b)) (S : (η : ℕ) → M.Tape η → a.Value M.carrier η → Prop)
    (hu : u.ReadsBelow fun η => p.eval η) (ho : o.ReadsBelow fun η => p.eval η)
    (hS : ∀ η ρa ρa' ρh x, (∀ i < p.eval η, M.readBit ρa i = M.readBit ρa' i) →
      S η (ρa, ρh) x → S η (ρa', ρh) x) {η : ℕ}
    (hη : p.eval η + Nat.clog 2 (q.eval η) ≤ M.lenA η) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[∃ x ∈ M.firstArgs (runLog (M.answer ρ.1 (Env.cons (o η ρ)
        (Env.append (u η ρ) (Ty.groundArgs ha)))) ((g.withOracleFirst hβ) η)),
          S η ρ (x _ .zero)] ≤
      2 ^ Nat.clog 2 (q.eval η) * Pr{let ρ ← $ᵗ (M.Tape η)}[
        S η ρ (Ty.appVals ((g.rwGuess p q ha hβ).eval η ρ.1) (VecRV.snoc u o η ρ))] := by
  set k := Nat.clog 2 (q.eval η)
  let L : M.Tape η → List (Vals M η (Ty.arrow a b).args) := fun ρ =>
    M.firstArgs (runLog (M.answer ρ.1 (Env.cons (o η ρ) (Env.append (u η ρ)
      (Ty.groundArgs ha)))) ((g.withOracleFirst hβ) η))
  let E : ℕ → M.Tape η → Prop := fun j ρ => ∃ x, (L ρ)[j]? = some x ∧ S η ρ (x _ .zero)
  have hG : Machine.ReadsBelow (g.withOracleFirst hβ) fun η => p.eval η := hg.rename _
  have hGq : Machine.QueryBound (g.withOracleFirst hβ) fun η => q.eval η := hq.rename _
  -- The events `E j` read the attacker tape only below `p(η)`.
  have hE : ∀ j ρa ρa' ρh, (∀ i < p.eval η, M.readBit ρa i = M.readBit ρa' i) →
      E j (ρa, ρh) → E j (ρa', ρh) := by
    intro j ρa ρa' ρh hρ ⟨x, hx, hs⟩
    have hu' : u η (ρa, ρh) = u η (ρa', ρh) :=
      funext fun τ => funext fun y => hu τ y η ρa ρa' ρh hρ
    refine ⟨x, ?_, hS η ρa ρa' ρh _ hρ hs⟩
    change (M.firstArgs (runLog _ _))[j]? = some x
    rw [← ho η ρa ρa' ρh hρ, ← hu', ← hG.runLog_eq hρ]
    exact hx
  calc Pr{let ρ ← $ᵗ (M.Tape η)}[∃ x ∈ L ρ, S η ρ (x _ .zero)]
      ≤ Pr{let ρ ← $ᵗ (M.Tape η)}[∃ j ∈ Finset.range (2 ^ k), E j ρ] := by
        refine prEvent_mono _ _ _ fun ρ ⟨x, hx, hs⟩ => ?_
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
        have hlen : j < (L ρ).length := (List.getElem?_eq_some_iff.1 hj).1
        refine ⟨j, Finset.mem_range.2 (lt_of_lt_of_le hlen ((hGq.length_firstArgs_le _ _).trans
          (Nat.le_pow_clog one_lt_two _))), x, hj, hs⟩
    _ ≤ ∑ j ∈ Finset.range (2 ^ k), Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ] :=
        prEvent_exists_finset_le _ _ _
    _ = 2 ^ k * Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k (M.bitsAt ρ.1 (p.eval η) k)) ρ] :=
        sum_prEvent_eq_two_pow_mul _ _ hη E hE
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (prEvent_mono _ _ _ fun ρ ⟨x, hx, hs⟩ => ?_)
        rw [VecRV.snoc, AdvMachine.appVals_eval_rwGuess ha hβ g ρ.1 (u η ρ) (o η ρ) hx]
        exact hs

/-- **The guessing bound** of Rw-Oracle (CCS26 App. C.1, step 2): `prEvent_exists_firstArgs_le` at
the event that `o` and `o'` differ. At an `η` where `⌈log₂ q(η)⌉` bits from `p(η)` fit on the
tape, the probability that the run with `o` makes a faulty query is at most `2 ^ ⌈log₂ q(η)⌉`
times the probability that the reduction `AdvMachine.rwGuess`, run with `o`, returns a point where
`o` and `o'` differ. -/
theorem prEvent_faultyAt_le {p q : Polynomial ℕ} (hg : Machine.ReadsBelow g fun η => p.eval η)
    (hq : Machine.QueryBound g fun η => q.eval η) (o o' : RV M (.arrow a b))
    (hu : u.ReadsBelow fun η => p.eval η) (ho : o.ReadsBelow fun η => p.eval η)
    (ho' : o'.ReadsBelow fun η => p.eval η) {η : ℕ}
    (hη : p.eval η + Nat.clog 2 (q.eval η) ≤ M.lenA η) :
    Pr{let ρ ← $ᵗ (M.Tape η)}[faultyAt ha hβ g u o o' η ρ] ≤
      2 ^ Nat.clog 2 (q.eval η) * Pr{let ρ ← $ᵗ (M.Tape η)}[
        o η ρ (Ty.appVals ((g.rwGuess p q ha hβ).eval η ρ.1) (VecRV.snoc u o η ρ)) ≠
          o' η ρ (Ty.appVals ((g.rwGuess p q ha hβ).eval η ρ.1) (VecRV.snoc u o η ρ))] :=
  prEvent_exists_firstArgs_le ha hβ g u hg hq o (fun η ρ x => o η ρ x ≠ o' η ρ x) hu ho
    (fun η ρa ρa' ρh x hρ hne => by rwa [← ho η ρa ρa' ρh hρ, ← ho' η ρa ρa' ρh hρ]) hη

end Bound

/-! ## Rw-Oracle -/

/-- **Rw-Oracle**, semantically, as CCS26's double rule (App. C.1, pp. 15–16): in a model with long
attacker tapes and polynomial bit blocks for the oracles' argument type, if `u⃗, o₂ ⊬ v`, the terms
read the attacker tape below a polynomial, and every `m` deducible from `u⃗, o_β`, with `o_β` one of
the two oracles, has `o₁(m) = o₂(m)` overwhelmingly, then `u⃗, o₁ ⊬ v`. The reduction is
`AdvMachine.rwGuess`, run with `o_β`, at the sum of the read bounds and the attacker machine's
query bound; at every large `η` the bound is that of `deduceAdv_le_add_faulty` and
`prEvent_faultyAt_le`. -/
theorem AdvClass.NonDed.rwOracle {C : AdvClass M} (hlong : M.LongTapes) (hc : M.PolyCoins a)
    (ha : a.IsGround) (hβ : β.IsGround) {u : VecRV M τs} {o₁ o₂ oβ : RV M (.arrow a b)}
    {v : RV M β} (hoβ : oβ = o₁ ∨ oβ = o₂)
    (hu : ∃ p : Polynomial ℕ, u.ReadsBelow fun η => p.eval η)
    (ho₁ : ∃ p : Polynomial ℕ, o₁.ReadsBelow fun η => p.eval η)
    (ho₂ : ∃ p : Polynomial ℕ, o₂.ReadsBelow fun η => p.eval η)
    (h : C.NonDed (VecRV.snoc u o₂) v)
    (hagree : ∀ X : RV M a, C.Ded (VecRV.snoc u oβ) X →
      negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[o₁ η ρ (X η ρ) ≠ o₂ η ρ (X η ρ)]) :
    C.NonDed (VecRV.snoc u o₁) v := by
  intro g hg
  obtain ⟨pg, hpg⟩ := C.readBound_mem hg
  obtain ⟨qg, hqg⟩ := C.queryBound_mem hg
  obtain ⟨pu, hpu⟩ := hu
  obtain ⟨p₁, hp₁⟩ := ho₁
  obtain ⟨p₂, hp₂⟩ := ho₂
  set p := pg + pu + p₁ + p₂
  have hle : ∀ {r : Polynomial ℕ}, (r = pg ∨ r = pu ∨ r = p₁ ∨ r = p₂) → ∀ η,
      r.eval η ≤ p.eval η := by
    rintro r (rfl | rfl | rfl | rfl) η <;> simp only [p, Polynomial.eval_add] <;> omega
  have hpu' : u.ReadsBelow fun η => p.eval η :=
    fun τ x => (hpu τ x).mono (hle (.inr (.inl rfl)))
  have hp₁' : o₁.ReadsBelow fun η => p.eval η := hp₁.mono (hle (.inr (.inr (.inl rfl))))
  have hp₂' : o₂.ReadsBelow fun η => p.eval η := hp₂.mono (hle (.inr (.inr (.inr rfl))))
  have hpg' : Machine.ReadsBelow g fun η => p.eval η := hpg.mono (hle (.inl rfl))
  -- The premise, at the value of the guessing reduction run with `o_β`.
  let X : RV M a := fun η ρ =>
    Ty.appVals ((g.rwGuess p qg ha hβ).eval η ρ.1) (VecRV.snoc u oβ η ρ)
  have hX : C.Ded (VecRV.snoc u oβ) X := ⟨_, C.rwGuess_mem p qg ha hβ hc hg,
    negligible_of_zero fun η => prEvent_eq_zero_of_forall_not _ _ fun _ h => h rfl⟩
  have hneg := negligible_polynomial_mul (hagree X hX) (2 * qg + 1)
  refine negligible_of_eventuallyLE ?_ (negligible_add (h g hg) hneg)
  filter_upwards [hlong (p + qg)] with η hη
  have hη' : p.eval η + Nat.clog 2 (qg.eval η) ≤ M.lenA η := by
    have := Nat.clog_le_of_le_pow (b := 2) (Nat.lt_two_pow_self (n := qg.eval η)).le
    simp only [Polynomial.eval_add] at hη
    omega
  have hfac : (2 : ENNReal) ^ Nat.clog 2 (qg.eval η) ≤ ((2 * qg + 1).eval η : ℕ) := by
    have := Nat.pow_clog_le_mul_add_one 2 (qg.eval η)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    exact_mod_cast this
  rcases hoβ with rfl | rfl
  · refine (deduceAdv_le_add_faulty ha hβ g u v oβ o₂ η).1.trans (add_le_add le_rfl ?_)
    exact (prEvent_faultyAt_le ha hβ g u hpg' hqg oβ o₂ hpu' hp₁' hp₂' hη').trans
      (mul_le_mul' hfac le_rfl)
  · refine (deduceAdv_le_add_faulty ha hβ g u v oβ o₁ η).2.trans (add_le_add le_rfl ?_)
    refine (prEvent_faultyAt_le ha hβ g u hpg' hqg oβ o₁ hpu' hp₂' hp₁' hη').trans
      (mul_le_mul' hfac (le_of_eq (prEvent_congr _ _ _ fun ρ => ne_comm)))

/-! ## Pc-Oracle -/

/-- The oracle `o` punctured at `m` to `w`: CCS26's `o′ = λx. if x ≠ m then o(x) else w`. -/
@[expose] noncomputable def RV.puncture (o : RV M (.arrow a b)) (m : RV M a) (w : RV M b) :
    RV M (.arrow a b) :=
  fun η ρ x => @ite _ (x ≠ m η ρ) (Classical.propDecidable _) (o η ρ x) (w η ρ)

/-- **Pc-Oracle**, semantically (CCS26 Fig. 3), derived from the double Rw-Oracle at `β = 2` as
App. C.1 derives it: with `o′` the oracle `o` punctured at `m` to `w`, from `u⃗, o′ ⊬ v` and
`u⃗, o′ ⊬ m` conclude `u⃗, o ⊬ v`. Wherever `u⃗, o′ ▷ m'`, Ineq gives `[m ≠ m']` from `u⃗, o′ ⊬ m`,
and `o` and `o′` agree away from `m`. -/
theorem AdvClass.NonDed.pcOracle {C : AdvClass M} (hlong : M.LongTapes) (hc : M.PolyCoins a)
    (ha : a.IsGround) (hβ : β.IsGround) {u : VecRV M τs} {o : RV M (.arrow a b)} {m : RV M a}
    {w : RV M b} {v : RV M β}
    (hu : ∃ p : Polynomial ℕ, u.ReadsBelow fun η => p.eval η)
    (ho : ∃ p : Polynomial ℕ, o.ReadsBelow fun η => p.eval η)
    (hm : ∃ p : Polynomial ℕ, m.ReadsBelow fun η => p.eval η)
    (hw : ∃ p : Polynomial ℕ, w.ReadsBelow fun η => p.eval η)
    (h : C.NonDed (VecRV.snoc u (RV.puncture o m w)) v)
    (hm' : C.NonDed (VecRV.snoc u (RV.puncture o m w)) m) :
    C.NonDed (VecRV.snoc u o) v := by
  obtain ⟨po, hpo⟩ := ho
  obtain ⟨pm, hpm⟩ := hm
  obtain ⟨pw, hpw⟩ := hw
  refine h.rwOracle hlong hc ha hβ (Or.inr rfl) hu ⟨po, hpo⟩ ⟨po + pm + pw, ?_⟩ fun X hX => ?_
  · intro η ρa ρa' ρh hρ
    have h₁ := hpo η ρa ρa' ρh fun i hi => hρ i (by
      dsimp only at hi ⊢; simp only [Polynomial.eval_add]; omega)
    have h₂ := hpm η ρa ρa' ρh fun i hi => hρ i (by
      dsimp only at hi ⊢; simp only [Polynomial.eval_add]; omega)
    have h₃ := hpw η ρa ρa' ρh fun i hi => hρ i (by
      dsimp only at hi ⊢; simp only [Polynomial.eval_add]; omega)
    unfold RV.puncture
    rw [h₁, h₂, h₃]
  · refine negligible_of_le (fun η => prEvent_mono _ _ _ fun ρ hne => ?_) (hm'.negligible_eq hX)
    by_contra hmX
    refine hne ?_
    unfold RV.puncture
    split_ifs with hx
    · rfl
    · exact absurd (not_not.1 hx).symm hmX

/-! ## The rules as global formulas -/

section Syntax

variable {Γ : List (Kind B)}

/-- The second premise of Rw-Oracle (CCS26 Fig. 3), `∀̃ m. (u⃗, o_β ▷ m) ⇒̃ [o₁(m) = o₂(m)]`, for a
message `m` of the oracles' argument type deducible from `u⃗` and the oracle `o_β`. -/
@[expose] def Form.oracleAgree (u : Vec D Γ τs) (oβ o₁ o₂ : FTerm D Γ (.arrow a b))
    (h : Ty.SecrecyOrder (τs ++ [.arrow a b]) a := by exact of_decide_eq_true rfl) : Form D Γ :=
  .all a (.imp (.ded (Vec.snoc (u.weaken _) (oβ.weaken _)) (Term.var .zero) h)
    (.box (FTerm.eq (FTerm.app (o₁.weaken _) (Term.var .zero))
      (FTerm.app (o₂.weaken _) (Term.var .zero)))))

/-- CCS26's `o′ = λx. if x ≠ m then o(x) else w`: the oracle `o` punctured at `m` to `w`. -/
@[expose] def FTerm.puncture (o : FTerm D Γ (.arrow a b)) (m : FTerm D Γ a) (w : FTerm D Γ b) :
    FTerm D Γ (.arrow a b) :=
  FTerm.lam (FTerm.ite (FTerm.not (FTerm.eq (Term.var .zero) (m.weaken _)))
    (FTerm.app (o.weaken _) (Term.var .zero)) (w.weaken _))

variable {M : Model D} {C : AdvClass M} {env : Env (Kind.Value M) Γ}

private theorem cond_cond_decide {α : Type} (P : Prop) (i : Decidable P) (t e : α) :
    cond (cond (@decide P i) false true) t e = @ite α P i e t := by
  cases i <;> rfl

private theorem denote_var_zero {s : Kind B} (X : s.Value M) :
    (Term.var .zero : (fullSig D).Term (s :: Γ) s).denote (fullInterp M C) (Env.cons X env) = X :=
  rfl

theorem FTerm.denote_puncture (o : FTerm D Γ (.arrow a b)) (m : FTerm D Γ a) (w : FTerm D Γ b) :
    (FTerm.puncture o m w).denote (fullInterp M C) env =
      RV.puncture (o.denote (fullInterp M C) env) (m.denote (fullInterp M C) env)
        (w.denote (fullInterp M C) env) := by
  funext η ρ x
  rw [FTerm.puncture, FTerm.denote_lam]
  simp only [FTerm.not, FTerm.denote_ite, FTerm.denote_eq, FTerm.denote_app, FTerm.denote_ff,
    FTerm.denote_tt]
  rw [cond_cond_decide]
  have hP : (Term.var .zero : FTerm D (.loc a :: Γ) a).denote (fullInterp M C)
      (Env.cons (RV.constAt η x) env) η ρ =
        (m.weaken (.loc a)).denote (fullInterp M C) (Env.cons (RV.constAt η x) env) η ρ ↔
      x = m.denote (fullInterp M C) env η ρ := by
    rw [denote_var_zero, RV.constAt_apply_self, denote_weaken_cons]
  unfold RV.puncture
  split_ifs with h₁ h₂ h₂
  · exact absurd (hP.1 h₁) h₂
  · rw [denote_weaken_cons]
  · rw [denote_weaken_cons, denote_var_zero, RV.constAt_apply_self]
  · exact absurd (hP.2 (not_not.1 h₂)) h₁

theorem Form.holds_oracleAgree {u : Vec D Γ τs} {oβ o₁ o₂ : FTerm D Γ (.arrow a b)}
    {h : Ty.SecrecyOrder (τs ++ [.arrow a b]) a} :
    (Form.oracleAgree u oβ o₁ o₂ h).Holds M C env ↔
      ∀ X : RV M a, C.Ded (VecRV.snoc (u.rv M C env) (oβ.denote (fullInterp M C) env)) X →
        negligible fun η => Pr{let ρ ← $ᵗ (M.Tape η)}[o₁.denote (fullInterp M C) env η ρ (X η ρ) ≠
          o₂.denote (fullInterp M C) env η ρ (X η ρ)] := by
  rw [Form.oracleAgree, Form.holds_all]
  refine forall_congr' fun X => ?_
  rw [Form.holds_imp, Form.holds_ded, Form.holds_box, Vec.rv_snoc, Vec.rv_weaken,
    denote_weaken_cons]
  refine imp_congr Iff.rfl (iff_of_eq (congrArg negligible (funext fun η =>
    prEvent_congr _ _ _ fun ρ => ?_)))
  simp only [FTerm.denote_eq, FTerm.denote_app, denote_var_zero]
  refine decide_eq_false_iff_not.trans ?_
  rw [denote_weaken_cons, denote_weaken_cons]

end Syntax

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Γ : List (Kind B)}
  {Θ : List (Form D Γ)} {u : Vec D Γ τs} {v : FTerm D Γ β}

/-- **Rw-Oracle** as CCS26's double rule (App. C.1): from `u⃗, o₂ ⊬ v` and
`∀̃ m. (u⃗, o_β ▷ m) ⇒̃ [o₁(m) = o₂(m)]`, with `o_β` one of the two oracles, conclude `u⃗, o₁ ⊬ v`,
for oracles with a Boolean or base argument type and a right side of Boolean or base type. The
models have long attacker tapes and polynomial bit blocks for the argument type, and the terms
read the attacker tape below a polynomial in every admitted model of `Θ`. -/
theorem nonDed_rwOracle_of {o₁ o₂ oβ : FTerm D Γ (.arrow a b)}
    {ho₁ ho₂ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β}
    {hd : Ty.SecrecyOrder (τs ++ [.arrow a b]) a} (ha : a.IsGround) (hβ : β.IsGround)
    (hoβ : oβ = o₁ ∨ oβ = o₂) (hR : ∀ M, R M → M.LongTapes ∧ M.PolyCoins a)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      u.ReadsPoly M (C M) env ∧ o₁.ReadsPoly M (C M) env ∧ o₂.ReadsPoly M (C M) env)
    (h : Valid R C Θ (.nonDed (Vec.snoc u o₂) v ho₂))
    (hagree : Valid R C Θ (Form.oracleAgree u oβ o₁ o₂ hd)) :
    Valid R C Θ (.nonDed (Vec.snoc u o₁) v ho₁) := fun M hl hRM env hΘ => by
  obtain ⟨hlong, hc⟩ := hR M hRM
  obtain ⟨hru, hr₁, hr₂⟩ := hread M hl hRM env hΘ
  have h' := Form.holds_nonDed.1 (h M hl hRM env hΘ)
  rw [Vec.rv_snoc] at h'
  have hoβ' : oβ.denote (fullInterp M (C M)) env = o₁.denote (fullInterp M (C M)) env ∨
      oβ.denote (fullInterp M (C M)) env = o₂.denote (fullInterp M (C M)) env :=
    hoβ.imp (fun h => by rw [h]) (fun h => by rw [h])
  rw [Form.holds_nonDed, Vec.rv_snoc]
  exact AdvClass.NonDed.rwOracle (u := u.rv M (C M) env) (v := v.denote (fullInterp M (C M)) env)
    hlong hc ha hβ hoβ' hru.exists_readsBelow hr₁ hr₂ h'
    (Form.holds_oracleAgree.1 (hagree M hl hRM env hΘ))

/-- **Rw-Oracle** (CCS26 Fig. 3, p. 7): from `u⃗, o₂ ⊬ v` and
`∀̃ m. (u⃗, o₁ ▷ m) ⇒̃ [o₁(m) = o₂(m)]` conclude `u⃗, o₁ ⊬ v`, under the conditions of
`Valid.nonDed_rwOracle_of`. -/
theorem nonDed_rwOracle {o₁ o₂ : FTerm D Γ (.arrow a b)}
    {ho₁ ho₂ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β}
    {hd : Ty.SecrecyOrder (τs ++ [.arrow a b]) a} (ha : a.IsGround) (hβ : β.IsGround)
    (hR : ∀ M, R M → M.LongTapes ∧ M.PolyCoins a)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      u.ReadsPoly M (C M) env ∧ o₁.ReadsPoly M (C M) env ∧ o₂.ReadsPoly M (C M) env)
    (h : Valid R C Θ (.nonDed (Vec.snoc u o₂) v ho₂))
    (hagree : Valid R C Θ (Form.oracleAgree u o₁ o₁ o₂ hd)) :
    Valid R C Θ (.nonDed (Vec.snoc u o₁) v ho₁) :=
  nonDed_rwOracle_of ha hβ (.inl rfl) hR hread h hagree

/-- **Pc-Oracle** (CCS26 Fig. 3, p. 7): from `u⃗, o′ ⊬ v` and `u⃗, o′ ⊬ m`, with
`o′ = λx. if x ≠ m then o(x) else w`, conclude `u⃗, o ⊬ v`; derived from Rw-Oracle at `β = 2`
(`AdvClass.NonDed.pcOracle`). The conditions are Rw-Oracle's, with the read bounds of `o′` coming
from those of `o`, `m` and `w`. -/
theorem nonDed_pcOracle {o : FTerm D Γ (.arrow a b)} {m : FTerm D Γ a} {w : FTerm D Γ b}
    {ho₁ ho₂ : Ty.SecrecyOrder (τs ++ [.arrow a b]) β}
    {hom : Ty.SecrecyOrder (τs ++ [.arrow a b]) a} (ha : a.IsGround) (hβ : β.IsGround)
    (hR : ∀ M, R M → M.LongTapes ∧ M.PolyCoins a)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      u.ReadsPoly M (C M) env ∧ o.ReadsPoly M (C M) env ∧ m.ReadsPoly M (C M) env ∧
        w.ReadsPoly M (C M) env)
    (h : Valid R C Θ (.nonDed (Vec.snoc u (FTerm.puncture o m w)) v ho₂))
    (hm : Valid R C Θ (.nonDed (Vec.snoc u (FTerm.puncture o m w)) m hom)) :
    Valid R C Θ (.nonDed (Vec.snoc u o) v ho₁) := fun M hl hRM env hΘ => by
  obtain ⟨hlong, hc⟩ := hR M hRM
  obtain ⟨hru, hro, hrm, hrw⟩ := hread M hl hRM env hΘ
  have h' := Form.holds_nonDed.1 (h M hl hRM env hΘ)
  have hm' := Form.holds_nonDed.1 (hm M hl hRM env hΘ)
  rw [Vec.rv_snoc, FTerm.denote_puncture] at h' hm'
  rw [Form.holds_nonDed, Vec.rv_snoc]
  exact AdvClass.NonDed.pcOracle (u := u.rv M (C M) env) (v := v.denote (fullInterp M (C M)) env)
    hlong hc ha hβ hru.exists_readsBelow hro hrm hrw h' hm'

end Valid

end Interop.Squirrel
