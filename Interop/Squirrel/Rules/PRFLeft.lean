/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Rules.PRFOracle
import VCVio.EvalDist.ProbabilityBounds
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import ToMathlib.Data.Nat.Log

/-!
# The hash oracle on the left: PRF.L-sec

CCS26's PRF.L-X (Fig. 4) gives the attacker the hash of a message beside the oracle
`o_h^k = λx. h(x, k)`; its variant `sec` (Remark 1) takes the secrecy of the message as the side
condition. This file proves it in the form of §2.3:

```
u⃗, o_h^k ⊬ v    [ψ_key(u⃗, v, m)]    [ψ_msg^{m,k}(u⃗, v, m)]    u⃗, o_h^k ⊬ m
-------------------------------------------------------------------------
                       u⃗, o_h^k, h(m, k) ⊬ v
```

`ψ_msg` ranges over the calls of `u⃗`, `v` and `m`. Fig. 4 and App. C.3.1 drop `m`'s own calls,
which the paper handles by guessing which of `A₂`'s oracle calls is on the message; here `m` is
not hashed before the challenge, as in §2.3 and in the last case of Remark 1.

## The proof

The reductions `PRFSymbols.leftReduction` and `PRFSymbols.leftFreshReduction` draw both tapes, run
phase one (the compiled `u⃗`, `v` and `m`, logged and forwarded to the PRF oracle), take the
challenge, the oracle at the message or a fresh draw, and run phase two: the attacker on the
vector's values and the challenge, its oracle input answered by the compiled `λx. call x` except
at the message, where the challenge answers (`PRFSymbols.interceptIn`). They succeed when the
attacker computes the secret or queries its oracle at the message, unless the message was hashed
in phase one. `PRFSymbols.leftAdvantage_le` is the statement at one `η`, in four hops.

1. **The real world of the first reduction** is the conclusion's event where `ψ_msg` holds: the
   intercepting oracle with the hash as challenge is the keyed hash.
2. **The ideal worlds agree** (`PRFSymbols.prEvent_prfIdealExperiment_leftReduction`): where the
   message was not hashed, its value is a fresh draw, and phase two never queries the hash there,
   so the cache entry at the message does not matter (VCVio's
   `OracleSpec.fst_map_run_simulateQ_romImpl_eq_of_allQueriesSatisfy`). The interception makes
   this an equality of distributions, with no identical-until-bad step in the ideal world.
3. **The real world of the second reduction** gives, at uniform tapes and a fresh draw `n`, that
   the attacker with `n` and the keyed hash computes the secret or queries the message: the
   reprogrammed oracle runs as the keyed hash until the message is queried
   (`Machine.run_cons_eq_of_firstArgs`), and a query at the message is one with either oracle
   (`Machine.runLog_cons_eq_of_firstArgs`).
4. **The fresh draw from the tape** (`prEvent_coin_eq_coinAt`): it is read from a block of the
   attacker tape above what the attacker and the terms read, so the attacker with `n` is FreshL's
   reduction (`AdvMachine.freshL`) of the attacker with its last two inputs swapped
   (`AdvMachine.swapLast`). Its success against `u⃗, o_h^k ⊢ v` is bounded by the premise; its
   queries at the message by `2 ^ ⌈log₂ q⌉` times the guess (`prEvent_exists_firstArgs_le`)
   against `u⃗, o_h^k ⊢ m`, bounded by `C_sec`.

`Valid.nonDed_prfLSec` is the rule, with the conclusion's entries in CCS26's order
(`AdvClass.NonDed.swapLast`), and `PRFLInstance` packages its data for derivations.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §2.3, Fig. 4, Remark 1 and App. C.3.1.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec PRFScheme

variable {B : Type} {D : Decl B}

/-- **Reprogramming at an unqueried point.** A machine whose first input is an oracle queries a
point `x` with one oracle exactly when it queries it with another that agrees with the first away
from `x`. -/
private theorem exists_firstArgs_of_agree {M : Model D} {η : ℕ} {a b γ : Ty B}
    {Γ : List (Ty B)} (gF : Machine M (.arrow a b :: Γ) γ) (ρa : M.TapeA η) (e : Vals M η Γ)
    {o₁ o₂ : (Ty.arrow a b).Value M.carrier η} (x : a.Value M.carrier η)
    (h : ∀ y, y ≠ x → o₁ y = o₂ y) :
    (∃ q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons o₁ e)) (gF η)), q _ .zero = x) →
      ∃ q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons o₂ e)) (gF η)), q _ .zero = x := by
  rintro ⟨q, hq, hqx⟩
  by_contra h₂
  have hlog := gF.runLog_cons_eq_of_firstArgs (o₁ := o₂) (o₂ := o₁) (e := e) (ρa := ρa)
    fun q' hq' => (h _ fun hx => h₂ ⟨q', hq', hx⟩).symm
  exact h₂ ⟨q, hlog ▸ hq, hqx⟩

/-! ## Swapping the last two inputs -/

namespace AdvMachine

variable {M : Model D} {η : ℕ} {τs : List (Ty B)} {b c β : Ty B}

/-- An attacker machine with the last two entries of its tuple swapped. -/
@[expose] def swapLast (g : AdvMachine M ((τs ++ [b]) ++ [c]) β) :
    AdvMachine M ((τs ++ [c]) ++ [b]) β :=
  g.rename (Env.append (fun _ x => (Interop.Squirrel.swapLast τs b c _ x).appendLeft β.args)
    (fun _ x => x.weakenMany ((τs ++ [c]) ++ [b])))

theorem appVals_eval_swapLast (g : AdvMachine M ((τs ++ [b]) ++ [c]) β) (ρa : M.TapeA η)
    (e : Vals M η τs) (x : c.Value M.carrier η) (y : b.Value M.carrier η) :
    Ty.appVals (g.swapLast.eval η ρa)
        (Env.append (Env.append e (Env.cons x Env.empty)) (Env.cons y Env.empty)) =
      Ty.appVals (g.eval η ρa)
        (Env.append (Env.append e (Env.cons y Env.empty)) (Env.cons x Env.empty)) := by
  rw [appVals_eval, appVals_eval, swapLast]
  refine congrArg Ty.curry (funext fun q => ?_)
  rw [Machine.run_rename, Env.rename_append_renaming, Env.rename_weakenMany_append]
  congr 2
  funext _ z
  exact (Env.append_appendLeft _ _ _).trans (congrFun (congrFun (rename_swapLast e x y) _) z)

end AdvMachine

/-- Swapping the last two entries of the left side keeps a secret. -/
theorem AdvClass.NonDed.swapLast {M : Model D} {C : AdvClass M} {τs : List (Ty B)} {b c β : Ty B}
    {u : VecRV M τs} {x : RV M c} {y : RV M b} {v : RV M β}
    (h : C.NonDed (VecRV.snoc (VecRV.snoc u y) x) v) :
    C.NonDed (VecRV.snoc (VecRV.snoc u x) y) v := fun g hg =>
  negligible_of_eventuallyLE (Filter.Eventually.of_forall fun η => le_of_eq
    (prEvent_congr _ _ _ fun ρ => by
      simp only [VecRV.snoc]
      rw [AdvMachine.appVals_eval_swapLast])) (h g.swapLast (C.rename_mem _ hg))

/-! ## A fresh coin as a block of the attacker tape -/

/-- **A fresh coin as a block of the attacker tape.** If an event reads the attacker tape only
below `p` and the block `[p, p + coinLen η b)` fits on the tape, drawing a coin of `b`
independently gives the event the probability it has with the coin read from that block. The
proof is the involution of (coin, tape) that swaps the coin with the block, as in FreshL. -/
theorem prEvent_coin_eq_coinAt {M : Model D} {η : ℕ} {b : Ty B} (p : ℕ)
    (hk : p + M.coinLen η b ≤ M.lenA η) (E : M.Tape η → M.Coin η b → Prop)
    (hE : ∀ c ρa ρa' ρh, (∀ i < p, M.readBit ρa i = M.readBit ρa' i) →
      E (ρa, ρh) c → E (ρa', ρh) c) :
    Pr{let c ← $ᵗ (M.Coin η b); let ρ ← $ᵗ (M.Tape η)}[E ρ c] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[E ρ (M.coinAt b ρ.1 p)] := by
  let σf : M.Coin η b × M.Tape η → M.Coin η b × M.Tape η := fun x =>
    (M.bitsAt x.2.1 p (M.coinLen η b), (M.setBlock p x.2.1 x.1, x.2.2))
  have hσ : Function.Involutive σf := fun x => by
    simp only [σf, M.bitsAt_setBlock _ _ _ hk, Model.setBlock_setBlock, Model.setBlock_bitsAt]
  rw [← SampleableType.prEvent_uniformSample_prod (p := fun x : M.Coin η b × M.Tape η =>
    E x.2 x.1), ← SampleableType.prEvent_uniformSample_equiv (Function.Involutive.toPerm σf hσ)]
  refine (prEvent_congr _ _ (fun x => E x.2 (M.coinAt b x.2.1 p)) fun x =>
    ⟨hE _ _ _ _ fun i hi => M.readBit_setBlock_of_lt _ _ hi,
      hE _ _ _ _ fun i hi => (M.readBit_setBlock_of_lt _ _ hi).symm⟩).trans ?_
  rw [SampleableType.prEvent_uniformSample_prod]
  dsimp only
  exact OracleComp.prEvent_bind_const ($ᵗ (M.Coin η b)) _

/-- Drawing a coin of `a`, the tapes and an independent coin of `b`, and writing the first coin
into the honest tape's coordinate `k`, gives uniform tapes and an independent coin of `b`. -/
private theorem update_coin_evalDistEq {M : Model D} {η : ℕ} [DecidableEq (M.Slot η)]
    (k : M.Slot η) (b : Ty B) :
    (do
        let c ← $ᵗ (M.Coin η k.1.2.1)
        let ρ ← $ᵗ (M.Tape η)
        let yc ← $ᵗ (M.Coin η b)
        pure ((ρ.1, Function.update ρ.2 k c), yc) : ProbComp (M.Tape η × M.Coin η b)) =ᵈ
      (do
        let yc ← $ᵗ (M.Coin η b)
        let ρ ← $ᵗ (M.Tape η)
        pure (ρ, yc) : ProbComp (M.Tape η × M.Coin η b)) := by
  have := D.finite_names
  have : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  have hupd : (do
        let c ← $ᵗ (M.Coin η k.1.2.1)
        let ρ ← $ᵗ (M.Tape η)
        pure (ρ.1, Function.update ρ.2 k c) : ProbComp (M.Tape η)) =ᵈ
      ($ᵗ (M.Tape η) : ProbComp (M.Tape η)) := EvalDistEq.of_forall_prEvent_eq fun q => by
    simpa only [prEvent_norm] using SampleableType.prEvent_uniformSample_prod_update
      (β := M.TapeA η) (R := fun k : M.Slot η => M.Coin η k.1.2.1) k q
  calc (do
          let c ← $ᵗ (M.Coin η k.1.2.1)
          let ρ ← $ᵗ (M.Tape η)
          let yc ← $ᵗ (M.Coin η b)
          pure ((ρ.1, Function.update ρ.2 k c), yc) : ProbComp (M.Tape η × M.Coin η b))
      =ᵈ (do
          let c ← $ᵗ (M.Coin η k.1.2.1)
          let yc ← $ᵗ (M.Coin η b)
          let ρ ← $ᵗ (M.Tape η)
          pure ((ρ.1, Function.update ρ.2 k c), yc) : ProbComp (M.Tape η × M.Coin η b)) :=
        EvalDistEq.bind_right _ fun _ => OracleComp.EvalDistEq.bind_bind_swap _ _ _
    _ =ᵈ (do
          let yc ← $ᵗ (M.Coin η b)
          let c ← $ᵗ (M.Coin η k.1.2.1)
          let ρ ← $ᵗ (M.Tape η)
          pure ((ρ.1, Function.update ρ.2 k c), yc) : ProbComp (M.Tape η × M.Coin η b)) :=
        OracleComp.EvalDistEq.bind_bind_swap _ _ _
    _ = (do
          let yc ← $ᵗ (M.Coin η b)
          (fun ρ => (ρ, yc)) <$> (do
            let c ← $ᵗ (M.Coin η k.1.2.1)
            let ρ ← $ᵗ (M.Tape η)
            pure (ρ.1, Function.update ρ.2 k c)) : ProbComp (M.Tape η × M.Coin η b)) := by
        simp [map_eq_bind_pure_comp, bind_assoc]
    _ =ᵈ (do
          let yc ← $ᵗ (M.Coin η b)
          (fun ρ => (ρ, yc)) <$> ($ᵗ (M.Tape η) : ProbComp (M.Tape η)) :
            ProbComp (M.Tape η × M.Coin η b)) :=
        EvalDistEq.bind_right _ fun _ => hupd.map _
    _ = _ := by simp [map_eq_bind_pure_comp]

namespace PRFSymbols

variable (P : PRFSymbols D)

/-! ## The oracle intercepted at the message -/

section Intercept

variable (M : Model D) (η : ℕ)

/-- The input answers of PRF.L's attacker: its first input `o_h^k` is answered by the compiled
`λx. call x` (`kapp`) except at `x₀`, where `y₀` answers without a query; its other inputs from the
values `e`. -/
@[expose] noncomputable def interceptIn {Γ : List (Ty B)} (x₀ : P.Dom M η) (y₀ : P.Rng M η)
    (e : Vals M η Γ) : InputImpl M η (.arrow P.msgTy P.hTy :: Γ) (OracleComp (P.Iface M η)) :=
  Env.cons (V := fun τ : Ty B => Vals M η τ.args →
      OracleComp (P.Iface M η) (τ.res.Value M.carrier η)) (a := Ty.arrow P.msgTy P.hTy)
    (fun (q : Vals M η (P.msgTy :: P.hTy.args)) =>
      (fun y => Ty.apply (τ := P.hTy) y fun _ i => q _ (.succ i)) <$>
        @ite _ (q _ .zero = x₀) (Classical.propDecidable _) (pure y₀)
          (P.kapp M η P.callOracle (q _ .zero)))
    (InputImpl.ofVals e)

/-- A function reprogrammed at `x₀` to `y₀`. -/
private noncomputable def reprogram (f : P.Dom M η → P.Rng M η) (x₀ : P.Dom M η)
    (y₀ : P.Rng M η) : P.Dom M η → P.Rng M η :=
  fun x => @ite _ (x = x₀) (Classical.propDecidable _) y₀ (f x)

variable {P M η}

private theorem reprogram_self (f : P.Dom M η → P.Rng M η) (x₀ : P.Dom M η) :
    P.reprogram M η f x₀ (f x₀) = f := by
  funext x
  unfold reprogram
  split_ifs with h
  · rw [h]
  · rfl

private theorem reprogram_of_ne (f : P.Dom M η → P.Rng M η) {x₀ x : P.Dom M η} (y₀ : P.Rng M η)
    (h : x ≠ x₀) : P.reprogram M η f x₀ y₀ x = f x :=
  ite_eq_right_of_eq_false _ _ (eq_false h)

variable {ρ : M.Tape η} {kv : P.keyTy.Value M.carrier η}

/-- The intercepting answers, run with the answers of `ρ` and `kv`, answer as the keyed hash
reprogrammed at `x₀` to `y₀`, followed by the values. -/
private theorem evalWithAnswerFn_interceptIn {Γ : List (Ty B)} (hmg : P.msgTy.IsGround)
    (hh : P.hTy.IsGround) (x₀ : P.Dom M η) (y₀ : P.Rng M η) (e : Vals M η Γ) :
    ∀ τ x q, evalWithAnswerFn (P.answer M η ρ kv) (P.interceptIn M η x₀ y₀ e τ x q) =
      Ty.apply (Env.cons (V := Ty.Value M.carrier η) (a := .arrow P.msgTy P.hTy)
        (P.reprogram M η (fun x => M.fn η P.hOf x kv) x₀ y₀) e τ x) q
  | _, .zero, q => by
    refine (evalWithAnswerFn_map _ _ _).trans ?_
    change Ty.apply (evalWithAnswerFn _ (@ite _ (q _ .zero = x₀) (Classical.propDecidable _) _ _))
      _ = Ty.apply (@ite _ (q _ .zero = x₀) (Classical.propDecidable _) _ _) _
    split_ifs
    · rfl
    · rw [evalWithAnswerFn_kapp hmg hh _ (P.pptm_callOracle hmg hh)]
      rfl
  | _, .succ _, _ => rfl

/-- The intercepted run never queries the hash at `x₀`. -/
private theorem allQueriesSatisfy_interceptIn {Γ : List (Ty B)} {α : Type}
    (hmg : P.msgTy.IsGround) (ρa : M.TapeA η) (x₀ : P.Dom M η) (y₀ : P.Rng M η)
    (e : Vals M η Γ) (c : OracleComp (M.Iface η (.arrow P.msgTy P.hTy :: Γ)) α) :
    (simulateQ (M.answerIn ρa (P.interceptIn M η x₀ y₀ e)) c).AllQueriesSatisfy
      (· ≠ Sum.inr x₀) := by
  refine (allQueriesSatisfy_of_forall (P := fun _ => True) (fun _ => trivial) c).simulateQ
    fun t _ => ?_
  rcases t with i | ⟨τ, y, q⟩
  · exact allQueriesSatisfy_pure _ _
  · cases y with
    | zero =>
      refine (allQueriesSatisfy_map_iff _ _ _).2 ?_
      change (@ite (OracleComp (P.Iface M η) (P.Rng M η)) (q _ .zero = x₀)
        (Classical.propDecidable _) (pure y₀)
        (P.kapp M η P.callOracle (q _ .zero))).AllQueriesSatisfy (· ≠ Sum.inr x₀)
      split_ifs with h
      · exact allQueriesSatisfy_pure _ _
      · rw [kapp_callOracle, M.lower_embed η hmg]
        exact (allQueriesSatisfy_map_iff _ _ _).2 ((allQueriesSatisfy_query_iff _ _).2
          fun h' => h (Sum.inr.inj h'))
    | succ y => exact allQueriesSatisfy_pure _ _

/-- A program forwarded to the PRF oracle (`fwd`) that never queries the hash at `x₀` never
queries the PRF oracle at `x₀`. -/
private theorem allQueriesSatisfy_fwd (ρ : M.Tape η) (x₀ : P.Dom M η) {α : Type}
    {c : OracleComp (P.Iface M η) α} (hc : c.AllQueriesSatisfy (· ≠ Sum.inr x₀)) :
    (simulateQ (P.fwd M η ρ) c).AllQueriesSatisfy (Sum.elim (fun _ => True) (· ≠ x₀)) :=
  hc.simulateQ fun t ht => by
    rcases t with (k | ⟨⟩) | x
    · exact allQueriesSatisfy_pure _ _
    · exact allQueriesSatisfy_pure _ _
    · exact (allQueriesSatisfy_query_iff _ _).2 fun h => ht (h ▸ rfl)

end Intercept

/-! ## PRF.L-sec: the reductions -/

variable {P} {M : Model D} {η : ℕ} {τs : List (Ty B)} {β : Ty B}

variable (P M η) in
/-- Phase one of PRF.L's reductions: compile the vector `u⃗`, the secret `v` and the message
`m`. -/
@[expose] noncomputable def leftProg (u : OVec P [] τs) (v : OTerm P [] β)
    (m : OTerm P [] P.msgTy) :
    OracleComp (P.Iface M η) (Vals M η τs × β.Value M.carrier η × P.Dom M η) := do
  let e ← P.cbvVec M η u
  let xv ← v.denoteCBV (P.cbvInterp M η) Env.empty
  let xm ← m.denoteCBV (P.cbvInterp M η) Env.empty
  pure (e, M.lower η β xv, M.lower η P.msgTy xm)

variable (P M η) in
/-- Phase two of PRF.L's reductions: run the attacker machine `gF` on the vector's values `e` and
the challenge `y`, logging its queries, with its oracle input answered by the compiled
`λx. call x` except at the message `x`, where `y` answers (`interceptIn`). -/
@[expose] noncomputable def leftAttack {γ : Ty B} (hmg : P.msgTy.IsGround)
    (gF : Machine M (.arrow P.msgTy P.hTy :: ((τs ++ [P.hTy]) ++ P.msgTy.args)) γ)
    (ρa : M.TapeA η) (e : Vals M η τs) (x : P.Dom M η) (y : P.Rng M η) :
    OracleComp (P.Iface M η) (γ.Value M.carrier η ×
      QueryLog (M.Iface η (.arrow P.msgTy P.hTy :: ((τs ++ [P.hTy]) ++ P.msgTy.args)))) :=
  simulateQ (M.answerIn ρa (P.interceptIn M η x y
    (Env.append (Env.append e (Env.cons y Env.empty)) (Ty.groundArgs hmg)))) (gF η).withQueryLog

variable (η) in
/-- PRF.L's reduction with a challenge program `chal`: draw both tapes; run phase one, logged,
with its hashes forwarded to the PRF oracle (`fwd`); obtain the challenge at the message's value;
run phase two; and return whether the attacker computed the secret or queried its oracle at the
message, unless the message was hashed in phase one. -/
@[expose] noncomputable def leftReductionWith (hmg : P.msgTy.IsGround) (hβ : β.IsGround)
    (u : OVec P [] τs) (v : OTerm P [] β) (m : OTerm P [] P.msgTy)
    (g : AdvMachine M ((τs ++ [P.hTy]) ++ [.arrow P.msgTy P.hTy]) β)
    (chal : P.Dom M η → OracleComp (PRFOracleSpec (P.Dom M η) (P.Rng M η)) (P.Rng M η)) :
    PRFAdversary (P.Dom M η) (P.Rng M η) :=
  (do
    let ρ ← liftComp ($ᵗ (M.Tape η)) (PRFOracleSpec (P.Dom M η) (P.Rng M η))
    let r ← simulateQ (P.fwd M η ρ) (P.leftProg M η u v m).withQueryLog
    let y ← chal r.1.2.2
    let a ← simulateQ (P.fwd M η ρ)
      (P.leftAttack M η hmg (g.withOracleFirst hβ) ρ.1 r.1.1 r.1.2.2 y)
    pure ((@decide (Ty.ofRes hβ a.1 = r.1.2.1) (Classical.propDecidable _) ||
        @decide (∃ q ∈ M.firstArgs a.2, q _ .zero = r.1.2.2) (Classical.propDecidable _)) &&
      !(@QueryLog.wasQueried _ _ (Classical.decEq _) r.2 (Sum.inr r.1.2.2))) :
    OracleComp (PRFOracleSpec (P.Dom M η) (P.Rng M η)) Bool)

variable (η) in
/-- **The first reduction of PRF.L-sec**: the challenge is the PRF oracle at the message. -/
@[expose] noncomputable def leftReduction (hmg : P.msgTy.IsGround) (hβ : β.IsGround)
    (u : OVec P [] τs) (v : OTerm P [] β) (m : OTerm P [] P.msgTy)
    (g : AdvMachine M ((τs ++ [P.hTy]) ++ [.arrow P.msgTy P.hTy]) β) :
    PRFAdversary (P.Dom M η) (P.Rng M η) :=
  leftReductionWith η hmg hβ u v m g fun x => functionQuery x

variable (η) in
/-- **The second reduction of PRF.L-sec**: the challenge is drawn by the sampler of the hash
type. -/
@[expose] noncomputable def leftFreshReduction (hmg : P.msgTy.IsGround) (hβ : β.IsGround)
    (u : OVec P [] τs) (v : OTerm P [] β) (m : OTerm P [] P.msgTy)
    (g : AdvMachine M ((τs ++ [P.hTy]) ++ [.arrow P.msgTy P.hTy]) β) :
    PRFAdversary (P.Dom M η) (P.Rng M η) :=
  leftReductionWith η hmg hβ u v m g fun _ =>
    liftComp (M.sample η P.hTy <$> ($ᵗ (M.Coin η P.hTy))) (PRFOracleSpec (P.Dom M η) (P.Rng M η))

/-- The outcome of PRF.L's reductions in the real world, at the tapes `ρ`, the key value `kv`
and the challenge `chal` of the message's value. -/
@[expose] noncomputable def leftOutcome (hmg : P.msgTy.IsGround) (hβ : β.IsGround)
    (u : OVec P [] τs) (v : OTerm P [] β) (m : OTerm P [] P.msgTy)
    (g : AdvMachine M ((τs ++ [P.hTy]) ++ [.arrow P.msgTy P.hTy]) β) (ρ : M.Tape η)
    (kv : P.keyTy.Value M.carrier η) (chal : P.Dom M η → P.Rng M η) : Bool :=
  let r := evalWithAnswerFn (P.answer M η ρ kv) (P.leftProg M η u v m).withQueryLog
  let a := evalWithAnswerFn (P.answer M η ρ kv)
    (P.leftAttack M η hmg (g.withOracleFirst hβ) ρ.1 r.1.1 r.1.2.2 (chal r.1.2.2))
  (@decide (Ty.ofRes hβ a.1 = r.1.2.1) (Classical.propDecidable _) ||
      @decide (∃ q ∈ M.firstArgs a.2, q _ .zero = r.1.2.2) (Classical.propDecidable _)) &&
    !(@QueryLog.wasQueried _ _ (Classical.decEq _) r.2 (Sum.inr r.1.2.2))

variable (hmg : P.msgTy.IsGround) (hβ : β.IsGround) (u : OVec P [] τs) (v : OTerm P [] β)
  (m : OTerm P [] P.msgTy) (g : AdvMachine M ((τs ++ [P.hTy]) ++ [.arrow P.msgTy P.hTy]) β)

section Phase

variable {ρ : M.Tape η} {kv : P.keyTy.Value M.carrier η}

include hmg hβ in
/-- Phase one returns the readings of `u⃗`, `v` and `m`, and hashes only messages satisfying `Q`,
for Boolean or base types in the `⊢pptm` fragment whose calls have arguments satisfying `Q`. -/
private theorem leftProg_spec (Q : P.Dom M η → Prop) (hg : ∀ τ ∈ τs, τ.IsGround)
    (hpu : ∀ τ x, P.Pptm (u τ x)) (hpv : P.Pptm v) (hpm : P.Pptm m)
    (hq : ∀ τ x, ((u τ x).denote (P.guardInterp ρ kv Q) (pairEnv Env.empty)).2)
    (hqv : (v.denote (P.guardInterp ρ kv Q) (pairEnv Env.empty)).2)
    (hqm : (m.denote (P.guardInterp ρ kv Q) (pairEnv Env.empty)).2) :
    evalWithAnswerFn (P.answer M η ρ kv) (P.leftProg M η u v m) =
        ((fun τ x => (u τ x).denote (P.ointerp M η ρ kv) Env.empty),
          v.denote (P.ointerp M η ρ kv) Env.empty, m.denote (P.ointerp M η ρ kv) Env.empty) ∧
      HashOK (P.answer M η ρ kv) Q (P.leftProg M η u v m) := by
  obtain ⟨h₁, h₁o⟩ := cbvVec_spec Q u hg hpu hq
  obtain ⟨h₂, h₂o⟩ := denoteCBV_guard v hpv (e := Env.empty) (Env.liftRel_empty _) hqv
  obtain ⟨h₃, h₃o⟩ := denoteCBV_guard m hpm (e := Env.empty) (Env.liftRel_empty _) hqm
  refine ⟨?_, hashOK_bind_iff.2 ⟨h₁o, hashOK_bind_iff.2 ⟨h₂o,
    hashOK_bind_iff.2 ⟨h₃o, hashOK_pure Q _⟩⟩⟩⟩
  rw [leftProg, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure, h₁, CRel.lower_eq hβ h₂, CRel.lower_eq hmg h₃]

/-- Phase two, run with the answers of `ρ` and `kv`: the attacker's run with the keyed hash
reprogrammed at `x` to `y` as its oracle, and its log. -/
private theorem evalWithAnswerFn_leftAttack {γ : Ty B} (hh : P.hTy.IsGround)
    (gF : Machine M (.arrow P.msgTy P.hTy :: ((τs ++ [P.hTy]) ++ P.msgTy.args)) γ)
    (ρa : M.TapeA η) (e : Vals M η τs) (x : P.Dom M η) (y : P.Rng M η) :
    evalWithAnswerFn (P.answer M η ρ kv) (P.leftAttack M η hmg gF ρa e x y) =
      (gF.run η ρa (Env.cons (P.reprogram M η (fun x => M.fn η P.hOf x kv) x y)
          (Env.append (Env.append e (Env.cons y Env.empty)) (Ty.groundArgs hmg))),
        runLog (M.answer ρa (Env.cons (P.reprogram M η (fun x => M.fn η P.hOf x kv) x y)
          (Env.append (Env.append e (Env.cons y Env.empty)) (Ty.groundArgs hmg)))) (gF η)) :=
  gF.evalWithAnswerFn_simulateQ_withQueryLog (evalWithAnswerFn_interceptIn hmg hh x y _)

end Phase

/-- **The first reduction in the real world**: the challenge is the keyed hash of the message. -/
theorem prEvent_prfRealExperiment_leftReduction :
    Pr{let b ← (P.scheme M η).prfRealExperiment (leftReduction η hmg hβ u v m g)}[b = true] =
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η)}[
        leftOutcome hmg hβ u v m g ρ (M.sample η P.keyTy kc)
          (fun x => M.fn η P.hOf x (M.sample η P.keyTy kc)) = true] := by
  simp only [prfRealExperiment, leftReduction, leftReductionWith, simulateQ_bind, simulateQ_map,
    simulateQ_prfRealQueryImpl_liftComp, simulateQ_prfRealQueryImpl_fwd, pure_bind, map_pure,
    simulateQ_prfRealQueryImpl_functionQuery, prEvent_norm]
  rfl

/-- **The second reduction in the real world**: the challenge is a fresh sample. -/
theorem prEvent_prfRealExperiment_leftFreshReduction :
    Pr{let b ← (P.scheme M η).prfRealExperiment (leftFreshReduction η hmg hβ u v m g)}[
        b = true] =
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η); let yc ← $ᵗ (M.Coin η P.hTy)}[
        leftOutcome hmg hβ u v m g ρ (M.sample η P.keyTy kc) (fun _ => M.sample η P.hTy yc) =
          true] := by
  simp only [prfRealExperiment, leftFreshReduction, leftReductionWith, simulateQ_bind,
    simulateQ_map, simulateQ_prfRealQueryImpl_liftComp, simulateQ_prfRealQueryImpl_fwd, pure_bind,
    prEvent_norm]
  rfl

/-- **The middle hop of PRF.L-sec.** Against a lazily sampled random function whose values are
drawn by the sampler of the hash type, the two reductions output `true` equally often. Where the
message was not hashed in phase one, its value is a fresh draw, as the second reduction's
challenge is; phase two never queries the hash at the message, so the cache entry that the first
reduction leaves there does not matter
(`OracleSpec.fst_map_run_simulateQ_romImpl_eq_of_allQueriesSatisfy`). -/
theorem prEvent_prfIdealExperiment_leftReduction [DecidableEq (P.Dom M η)]
    [SampleableType (P.Rng M η)]
    (hsel : ($ᵗ (P.Rng M η)) = M.sample η P.hTy <$> ($ᵗ (M.Coin η P.hTy))) :
    Pr{let b ← prfIdealExperiment (leftReduction η hmg hβ u v m g)}[b = true] =
      Pr{let b ← prfIdealExperiment (leftFreshReduction η hmg hβ u v m g)}[b = true] := by
  simp only [prfIdealExperiment, leftReduction, leftFreshReduction, leftReductionWith,
    simulateQ_bind, simulateQ_prfIdealQueryImpl_liftComp, StateT.run'_liftM_bind]
  refine prEvent_bind_congr _ _ _ _ _ fun ρ => ?_
  simp only [StateT.run'_eq, StateT.run_bind, simulateQ_pure,
    simulateQ_prfIdealQueryImpl_functionQuery, prEvent_norm]
  refine prEvent_bind_congr_of_support _ _ _ fun p hp => ?_
  by_cases hb : (@QueryLog.wasQueried _ _ (Classical.decEq _) p.1.2 (Sum.inr p.1.1.2.2)) = true
  · simp [hb]
  · have hnone := eq_none_of_mem_support_run ρ _ ∅ p hp p.1.1.2.2 rfl fun h => hb (by
      rw [@QueryLog.wasQueried_eq_decide_mem_map_fst _ _ (Classical.decEq _)]
      simpa using h)
    simp only [randomOracle.run_eq, hnone, hsel, StateT.run_liftM, prEvent_norm]
    refine prEvent_bind_congr_of_forall _ _ _ _ _ fun c => ?_
    have h : Prod.fst <$> (simulateQ (prfIdealQueryImpl (D := P.Dom M η) (R := P.Rng M η))
        (simulateQ (P.fwd M η ρ) (P.leftAttack M η hmg (g.withOracleFirst hβ) ρ.1 p.1.1.1
          p.1.1.2.2 (M.sample η P.hTy c)))).run (p.2.cacheQuery p.1.1.2.2 (M.sample η P.hTy c)) =
        Prod.fst <$> (simulateQ (prfIdealQueryImpl (D := P.Dom M η) (R := P.Rng M η))
          (simulateQ (P.fwd M η ρ) (P.leftAttack M η hmg (g.withOracleFirst hβ) ρ.1 p.1.1.1
            p.1.1.2.2 (M.sample η P.hTy c)))).run p.2 :=
      OracleSpec.fst_map_run_simulateQ_romImpl_eq_of_allQueriesSatisfy
        (allQueriesSatisfy_fwd ρ _ (allQueriesSatisfy_interceptIn hmg ρ.1 _ _ _ _))
        fun y hy => QueryCache.cacheQuery_of_ne _ _ hy
    have key := congrArg (fun z => Pr{let a ← z}[((@decide (Ty.ofRes hβ a.1 = p.1.1.2.1)
        (Classical.propDecidable _) || @decide (∃ q ∈ M.firstArgs a.2, q P.msgTy ScopedVar.zero =
          p.1.1.2.2) (Classical.propDecidable _)) &&
        !(@QueryLog.wasQueried _ _ (Classical.decEq _) p.1.2 (Sum.inr p.1.1.2.2))) = true]) h
    simp only [StateT.run_map, prEvent_norm, Functor.map_map] at key ⊢
    exact key

/-! ## PRF.L-sec at one security parameter -/

/-- **Through the ideal world.** If two distinguishers output `true` equally often in the ideal
world, the first's probability of `true` in the real world is at most the two PRF advantages plus
the second's. -/
private theorem prEvent_prfRealExperiment_le_of_ideal (hU : M.UniformSampler P.hTy)
    (adv adv' : PRFAdversary (P.Dom M η) (P.Rng M η))
    (hid : Pr{let b ← (@prfIdealExperiment _ _ (Classical.decEq _)
        (M.uniformSampler P.hTy hU η) adv)}[b = true] =
      Pr{let b ← (@prfIdealExperiment _ _ (Classical.decEq _)
        (M.uniformSampler P.hTy hU η) adv')}[b = true]) :
    Pr{let b ← (P.scheme M η).prfRealExperiment adv}[b = true] ≤
      P.prfAdv M η hU adv + P.prfAdv M η hU adv' +
        Pr{let b ← (P.scheme M η).prfRealExperiment adv'}[b = true] := by
  have hr := (ENNReal.absDiff_le_iff.1 (le_of_eq (prfAdv_eq hU adv).symm)).1
  have hf := (ENNReal.absDiff_le_iff.1 (le_of_eq (prfAdv_eq hU adv').symm)).2
  rw [hid] at hr
  calc _ ≤ _ := hr
    _ ≤ _ := add_le_add hf le_rfl
    _ = _ := by ring

/-- The event of the second reduction's real world, at the tapes `ρ` and the challenge `n`: with
`n` in place of the hash of the message, `g` computes `V`, or its run queries its oracle at `Mv`. -/
private def leftEvent (U : VecRV M τs) (O : RV M (.arrow P.msgTy P.hTy)) (V : RV M β)
    (Mv : RV M P.msgTy) (η : ℕ) (ρ : M.Tape η) (n : P.Rng M η) : Prop :=
  Ty.appVals (g.eval η ρ.1) (Env.append (Env.append (U η ρ) (Env.cons n Env.empty))
      (Env.cons (O η ρ) Env.empty)) = V η ρ ∨
    ∃ x ∈ M.firstArgs (runLog (M.answer ρ.1 (Env.cons (O η ρ) (Env.append
      (Env.append (U η ρ) (Env.cons n Env.empty)) (Ty.groundArgs hmg))))
        ((g.withOracleFirst hβ) η)), x _ .zero = Mv η ρ

section Hops

variable [DecidableEq (M.Slot η)] (hh : P.hTy.IsGround) (hg : ∀ τ ∈ τs, τ.IsGround)
  (hku : ∀ τ x, P.KeyFree (u τ x)) (hkv : P.KeyFree v) (hkm : P.KeyFree m)
  (hpu : ∀ τ x, P.Pptm (u τ x)) (hpv : P.Pptm v) (hpm : P.Pptm m)
  (C : AdvClass M) (env : Env (Kind.Value M) [])

include hh hg hku hkv hkm hpu hpv hpm in
/-- **Hop 1: the first reduction's real world.** At the tapes `ρ` with the key's coordinate
overwritten by `kc`, where `ψ_msg(u⃗, v, m)` holds, the conclusion's event is the first reduction's
outcome: the intercepting oracle with the hash of the message as challenge is the keyed hash. -/
private theorem leftOutcome_of_win (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfv : P.FirstOrder v)
    (hfm : P.FirstOrder m) (kc : M.Coin η P.keyTy) (ρ : M.Tape η)
    (hW : Ty.appVals (g.eval η ρ.1) (VecRV.snoc (VecRV.snoc ((P.closeVec u).rv M C env)
        ((P.hashTerm (P.close m)).denote (fullInterp M C) env))
        ((P.hashOracle (Γ := [])).denote (fullInterp M C) env) η
        (ρ.1, Function.update ρ.2 (P.keySlot M η) kc)) =
      (P.close v).denote (fullInterp M C) env η (ρ.1, Function.update ρ.2 (P.keySlot M η) kc))
    (hψ : (P.psiMsg (Env.append u (Env.cons v Env.empty)) m).denote (fullInterp M C) env η
      (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) = true) :
    leftOutcome hmg hβ u v m g ρ (M.sample η P.keyTy kc)
      (fun x => M.fn η P.hOf x (M.sample η P.keyTy kc)) = true := by
  set kv := M.sample η P.keyTy kc
  set xm := m.denote (P.ointerp M η ρ kv) Env.empty
  have hagree : ∀ k : M.Slot η, k.1 ≠ P.keyName →
      Function.update ρ.2 (P.keySlot M η) kc k = ρ.2 k :=
    fun k hk => Function.update_of_ne (fun h => hk (congrArg Sigma.fst h)) _ _
  rw [psiMsg_eq_true_iff, keyVal_update] at hψ
  have hq : ∀ {σ : Ty B} (t : OTerm P [] σ), P.KeyFree t → P.FirstOrder t →
      (∀ t' ∈ P.calls t, t' ∈ P.vecCalls (Env.append u (Env.cons v Env.empty)) ++ P.calls m) →
      (t.denote (P.guardInterp ρ kv fun y => y ≠ xm) (pairEnv Env.empty)).2 := by
    intro σ t hk hf hsub
    rw [snd_denote_guardInterp_iff _ _ hf]
    intro t' ht'
    have h := hψ t' (hsub t' ht')
    rwa [congrFun (ointerp_eq_of_keyFree hagree kv t'
        ((heads_subset_of_mem_calls _ t' ht').trans hk)) Env.empty,
      congrFun (ointerp_eq_of_keyFree hagree kv m hkm) Env.empty] at h
  obtain ⟨hrun, hok⟩ := leftProg_spec hmg hβ u v m (ρ := ρ) (kv := kv) (fun y => y ≠ xm) hg hpu
    hpv hpm (fun τ x => hq _ (hku τ x) (hfu τ x) fun t' h => List.mem_append_left _
      (mem_vecCalls.2 ⟨τ, x.appendLeft [β], by rw [Env.append_appendLeft]; exact h⟩))
    (hq v hkv hfv fun t' h => List.mem_append_left _ (mem_vecCalls.2
      ⟨β, (ScopedVar.zero : ScopedVar [β] β).weakenMany τs, by
        rw [Env.append_weakenMany]; exact h⟩))
    (hq m hkm hfm fun t' h => List.mem_append_right _ h)
  unfold leftOutcome
  simp only [evalWithAnswerFn_withQueryLog, hrun, evalWithAnswerFn_leftAttack hmg hh,
    reprogram_self, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨Or.inl ?_, ?_⟩
  · change Ty.appVals (g.eval η ρ.1) (Env.append (Env.append
        ((P.closeVec u).rv M C env η (ρ.1, Function.update ρ.2 (P.keySlot M η) kc))
        (Env.cons (M.fn η P.hOf ((P.close m).denote (fullInterp M C) env η
            (ρ.1, Function.update ρ.2 (P.keySlot M η) kc))
          (P.keyVal M η (Function.update ρ.2 (P.keySlot M η) kc))) Env.empty))
        (Env.cons ((P.hashOracle (Γ := [])).denote (fullInterp M C) env η
          (ρ.1, Function.update ρ.2 (P.keySlot M η) kc)) Env.empty)) =
      (P.close v).denote (fullInterp M C) env η (ρ.1, Function.update ρ.2 (P.keySlot M η) kc)
      at hW
    rwa [AdvMachine.appVals_eval_eq_withOracleFirst hmg hβ, closeVec_rv_apply_update C env u hku,
      hashOracle_apply_update, close_apply_update C env m hkm, close_apply_update C env v hkv,
      keyVal_update] at hW
  · rw [@QueryLog.wasQueried_eq_decide_mem_map_fst _ _ (Classical.decEq _),
      decide_eq_false_iff_not]
    exact fun hx => hok xm hx rfl

include hh hg hku hkv hkm hpu hpv hpm in
/-- **Hop 3: the second reduction's real world.** Its outcome gives the event `leftEvent` at the
tapes with the key's coordinate overwritten and the fresh draw: the reprogrammed oracle runs as
the keyed hash until the message is queried, and a query at the message is one with either
oracle. -/
private theorem leftEvent_of_outcome (kc : M.Coin η P.keyTy) (ρ : M.Tape η)
    (yc : M.Coin η P.hTy)
    (hout : leftOutcome hmg hβ u v m g ρ (M.sample η P.keyTy kc)
      (fun _ => M.sample η P.hTy yc) = true) :
    P.leftEvent hmg hβ g ((P.closeVec u).rv M C env)
      ((P.hashOracle (Γ := [])).denote (fullInterp M C) env)
      ((P.close v).denote (fullInterp M C) env) ((P.close m).denote (fullInterp M C) env) η
      (ρ.1, Function.update ρ.2 (P.keySlot M η) kc) (M.sample η P.hTy yc) := by
  set kv := M.sample η P.keyTy kc
  obtain ⟨hrun, -⟩ := leftProg_spec hmg hβ u v m (ρ := ρ) (kv := kv) (fun _ => True) hg hpu hpv
    hpm (fun _ _ => snd_denote_guardInterp_true _ _) (snd_denote_guardInterp_true _ _)
    (snd_denote_guardInterp_true _ _)
  unfold leftOutcome at hout
  simp only [evalWithAnswerFn_withQueryLog, hrun, evalWithAnswerFn_leftAttack hmg hh,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hout
  obtain ⟨hor, -⟩ := hout
  unfold leftEvent
  rw [closeVec_rv_apply_update C env u hku, hashOracle_apply_update,
    close_apply_update C env v hkv, close_apply_update C env m hkm,
    AdvMachine.appVals_eval_eq_withOracleFirst hmg hβ]
  by_cases hq : ∃ q ∈ M.firstArgs (runLog (M.answer ρ.1 (Env.cons
      (P.reprogram M η (fun x => M.fn η P.hOf x kv) (m.denote (P.ointerp M η ρ kv) Env.empty)
        (M.sample η P.hTy yc))
      (Env.append (Env.append (fun τ x => (u τ x).denote (P.ointerp M η ρ kv) Env.empty)
        (Env.cons (M.sample η P.hTy yc) Env.empty)) (Ty.groundArgs hmg))))
        ((g.withOracleFirst hβ) η)),
      q _ .zero = m.denote (P.ointerp M η ρ kv) Env.empty
  · exact Or.inr (exists_firstArgs_of_agree _ ρ.1 _ _ (fun y hy => reprogram_of_ne _ _ hy) hq)
  · refine Or.inl ?_
    rcases hor with h | h
    · rwa [Machine.run_cons_eq_of_firstArgs _ (o₂ := fun x => M.fn η P.hOf x kv)
        fun q hq' => reprogram_of_ne _ _ fun hx => hq ⟨q, hq', hx⟩] at h
    · exact absurd h hq

end Hops

/-- **Hop 4: the fresh draw from the tape.** The event `leftEvent` at uniform tapes and a fresh
draw reads the attacker tape below `p`, so the draw can be read from the block of the tape at
`p(η)` (`prEvent_coin_eq_coinAt`). Its first disjunct is then the success of FreshL's reduction of
`g`, with its last two inputs swapped, against `u⃗, o_h^k ⊢ v`; its second is bounded by
`2 ^ ⌈log₂ q(η)⌉` times the success of the guess of `g`'s oracle queries, with the same sampling,
against `u⃗, o_h^k ⊢ m` (`prEvent_exists_firstArgs_le`). -/
private theorem prEvent_leftEvent_le (hh : P.hTy.IsGround) (U : VecRV M τs)
    (O : RV M (.arrow P.msgTy P.hTy)) (V : RV M β) (Mv : RV M P.msgTy) {p pc q : Polynomial ℕ}
    (hpg : Machine.ReadsBelow g fun η => p.eval η) (hqg : Machine.QueryBound g fun η => q.eval η)
    (hru : U.ReadsBelow fun η => p.eval η) (hro : O.ReadsBelow fun η => p.eval η)
    (hrv : V.ReadsBelow fun η => p.eval η) (hrm : Mv.ReadsBelow fun η => p.eval η)
    (hpc : ∀ η, M.coinLen η P.hTy ≤ pc.eval η)
    (hη : (p + pc).eval η + Nat.clog 2 (q.eval η) ≤ M.lenA η) :
    Pr{let yc ← $ᵗ (M.Coin η P.hTy); let ρ ← $ᵗ (M.Tape η)}[
        P.leftEvent hmg hβ g U O V Mv η ρ (M.sample η P.hTy yc)] ≤
      deduceAdv (g.swapLast.freshL (fun η => p.eval η)
          ((Ty.isGround_iff_order_eq_zero.1 hh).trans_le zero_le_one)).eval
        (VecRV.snoc U O) V η +
        2 ^ Nat.clog 2 (q.eval η) * deduceAdv ((g.rwGuess (p + pc) q hmg hβ).swapLast.freshL
            (fun η => p.eval η) ((Ty.isGround_iff_order_eq_zero.1 hh).trans_le zero_le_one)).eval
          (VecRV.snoc U O) Mv η := by
  have hle : ∀ η', p.eval η' ≤ (p + pc).eval η' := fun η' =>
    (Nat.le_add_right _ _).trans_eq Polynomial.eval_add.symm
  have hk : p.eval η + M.coinLen η P.hTy ≤ M.lenA η := by
    have := hpc η
    simp only [Polynomial.eval_add] at hη
    omega
  -- `leftEvent` reads the attacker tape below `p`.
  have hE : ∀ c ρa ρa' ρh, (∀ i < p.eval η, M.readBit ρa i = M.readBit ρa' i) →
      P.leftEvent hmg hβ g U O V Mv η (ρa, ρh) (M.sample η P.hTy c) →
        P.leftEvent hmg hβ g U O V Mv η (ρa', ρh) (M.sample η P.hTy c) := by
    intro c ρa ρa' ρh hρ hF
    have hU' : U η (ρa, ρh) = U η (ρa', ρh) :=
      funext fun τ => funext fun y => hru τ y η ρa ρa' ρh hρ
    rcases hF with hF | ⟨x, hx, hxm⟩
    · refine Or.inl ?_
      change Ty.appVals (g.eval η ρa') _ = V η (ρa', ρh)
      rw [← AdvMachine.eval_eq_of_readsBelow hpg hρ, ← hU', ← hro η ρa ρa' ρh hρ,
        ← hrv η ρa ρa' ρh hρ]
      exact hF
    · refine Or.inr ⟨x, ?_, hxm.trans (hrm η ρa ρa' ρh hρ)⟩
      have hG : Machine.ReadsBelow (g.withOracleFirst hβ) fun η => p.eval η := hpg.rename _
      change x ∈ M.firstArgs (runLog (M.answer ρa' _) ((g.withOracleFirst hβ) η))
      rw [← hro η ρa ρa' ρh hρ, ← hU', ← hG.runLog_eq hρ]
      exact hx
  rw [prEvent_coin_eq_coinAt (p.eval η) hk (fun ρ c => P.leftEvent hmg hβ g U O V Mv η ρ
    (M.sample η P.hTy c)) hE]
  -- The fresh draw read from the tape, beside `U`.
  set N : RV M P.hTy := fun η ρ => M.sample η P.hTy (M.coinAt P.hTy ρ.1 (p.eval η))
  have hUN : (VecRV.snoc U N).ReadsBelow fun η => (p + pc).eval η := by
    intro τ y η' ρa ρa' ρh hρ
    have hN : N η' (ρa, ρh) = N η' (ρa', ρh) := by
      change M.sample η' P.hTy (M.coinAt P.hTy ρa (p.eval η')) =
        M.sample η' P.hTy (M.coinAt P.hTy ρa' (p.eval η'))
      congr 1
      funext j
      exact hρ _ (by have := hpc η'; have := j.2; simp only [Polynomial.eval_add]; omega)
    change VecRV.snoc U N η' (ρa, ρh) τ y = VecRV.snoc U N η' (ρa', ρh) τ y
    simp only [VecRV.snoc]
    rw [hN, show U η' (ρa, ρh) = U η' (ρa', ρh) from funext fun τ => funext fun y =>
      hru τ y η' ρa ρa' ρh fun i hi => hρ i (lt_of_lt_of_le hi (hle η'))]
  refine (prEvent_or_le _ _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · refine prEvent_congr _ _ _ fun ρ => ?_
    simp only [VecRV.snoc]
    rw [AdvMachine.appVals_eval_freshL, AdvMachine.appVals_eval_swapLast]
  · refine (prEvent_exists_firstArgs_le hmg hβ g (VecRV.snoc U N) (hpg.mono hle) hqg O
      (fun η ρ x => x = Mv η ρ) hUN (hro.mono hle) (fun η ρa ρa' ρh x hρ hx => hx.trans
        (hrm η ρa ρa' ρh fun i hi => hρ i (lt_of_lt_of_le hi (hle η)))) hη).trans (le_of_eq ?_)
    refine congrArg _ (prEvent_congr _ _ _ fun ρ => ?_)
    simp only [VecRV.snoc]
    rw [AdvMachine.appVals_eval_freshL, AdvMachine.appVals_eval_swapLast]

/-- **PRF.L-sec at `η`** (CCS26 §2.3 and Fig. 4). Let `g` be an attacker machine against
`u⃗, h(m, k), o_h^k ⊢ v` that reads the attacker tape below `p` and makes at most `q` input
queries, with `u⃗`, `v` and `m` reading the tape below `p` and `pc` bounding the bit blocks of
hashes. At an `η` where `⌈log₂ q(η)⌉` bits from `(p + pc)(η)` fit on the tape, `g`'s success is at
most

* the probability that `ψ_msg(u⃗, v, m)` fails: the message is hashed before the challenge;
* the PRF advantages of `leftReduction` and `leftFreshReduction`: the hash of the message, given
  to `g` and answered by its oracle at the message, is replaced by a fresh draw (the ideal worlds
  agree, `prEvent_prfIdealExperiment_leftReduction`);
* the success against `u⃗, o_h^k ⊢ v` of `g` with the fresh draw read from the tape
  (`AdvMachine.freshL` of `AdvMachine.swapLast g`): the premise;
* `2 ^ ⌈log₂ q(η)⌉` times the success against `u⃗, o_h^k ⊢ m` of the guess of one of `g`'s oracle
  queries, with the fresh draw read from the tape: `C_sec`. -/
theorem leftAdvantage_le (hU : M.UniformSampler P.hTy) (hh : P.hTy.IsGround)
    (hg : ∀ τ ∈ τs, τ.IsGround) (hku : ∀ τ x, P.KeyFree (u τ x)) (hkv : P.KeyFree v)
    (hkm : P.KeyFree m) (hpu : ∀ τ x, P.Pptm (u τ x)) (hpv : P.Pptm v) (hpm : P.Pptm m)
    (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfv : P.FirstOrder v) (hfm : P.FirstOrder m)
    (C : AdvClass M) (env : Env (Kind.Value M) []) {p pc q : Polynomial ℕ}
    (hpg : Machine.ReadsBelow g fun η => p.eval η) (hqg : Machine.QueryBound g fun η => q.eval η)
    (hru : ((P.closeVec u).rv M C env).ReadsBelow fun η => p.eval η)
    (hrv : ((P.close v).denote (fullInterp M C) env).ReadsBelow fun η => p.eval η)
    (hrm : ((P.close m).denote (fullInterp M C) env).ReadsBelow fun η => p.eval η)
    (hpc : ∀ η, M.coinLen η P.hTy ≤ pc.eval η)
    (hη : (p + pc).eval η + Nat.clog 2 (q.eval η) ≤ M.lenA η) :
    deduceAdv g.eval (Vec.rv M C (Vec.snoc (Vec.snoc (P.closeVec u) (P.hashTerm (P.close m)))
        P.hashOracle) env) ((P.close v).denote (fullInterp M C) env) η ≤
      Pr{let ρ ← $ᵗ (M.Tape η)}[(P.psiMsg (Env.append u (Env.cons v Env.empty)) m).denote
        (fullInterp M C) env η ρ = false] +
        P.prfAdv M η hU (leftReduction η hmg hβ u v m g) +
        P.prfAdv M η hU (leftFreshReduction η hmg hβ u v m g) +
        deduceAdv (g.swapLast.freshL (fun η => p.eval η)
            ((Ty.isGround_iff_order_eq_zero.1 hh).trans_le zero_le_one)).eval
          (Vec.rv M C (Vec.snoc (P.closeVec u) P.hashOracle) env)
          ((P.close v).denote (fullInterp M C) env) η +
        2 ^ Nat.clog 2 (q.eval η) * deduceAdv ((g.rwGuess (p + pc) q hmg hβ).swapLast.freshL
            (fun η => p.eval η) ((Ty.isGround_iff_order_eq_zero.1 hh).trans_le zero_le_one)).eval
          (Vec.rv M C (Vec.snoc (P.closeVec u) P.hashOracle) env)
          ((P.close m).denote (fullInterp M C) env) η := by
  classical
  have := D.finite_names
  have : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  simp only [Vec.rv_snoc]
  let T : ProbComp (M.Coin η P.keyTy × M.Tape η) := do
    let kc ← $ᵗ (M.Coin η P.keyTy)
    let ρ ← $ᵗ (M.Tape η)
    pure (kc, ρ)
  have hT : ∀ r : M.Coin η P.keyTy → M.Tape η → Prop,
      Pr{let kc ← $ᵗ (M.Coin η P.keyTy); let ρ ← $ᵗ (M.Tape η)}[r kc ρ] =
        Pr{let x ← T}[r x.1 x.2] := fun r => by
    simp only [T, prEvent_norm]
  -- Hop 1: where `ψ_msg` holds, the conclusion's event is the first reduction's real world.
  have h₁ : Pr{let ρ ← $ᵗ (M.Tape η)}[Ty.appVals (g.eval η ρ.1)
        (VecRV.snoc (VecRV.snoc ((P.closeVec u).rv M C env)
          ((P.hashTerm (P.close m)).denote (fullInterp M C) env))
          ((P.hashOracle (Γ := [])).denote (fullInterp M C) env) η ρ) =
        (P.close v).denote (fullInterp M C) env η ρ ∧
      ¬ (P.psiMsg (Env.append u (Env.cons v Env.empty)) m).denote (fullInterp M C) env η ρ =
        false] ≤
      Pr{let b ← (P.scheme M η).prfRealExperiment (leftReduction η hmg hβ u v m g)}[b = true] := by
    rw [← SampleableType.prEvent_uniformSample_prod_update (β := M.TapeA η)
      (R := fun k : M.Slot η => M.Coin η k.1.2.1) (P.keySlot M η), hT,
      prEvent_prfRealExperiment_leftReduction, hT]
    exact prEvent_mono T _ _ fun x hx => leftOutcome_of_win hmg hβ u v m g hh hg hku hkv hkm
      hpu hpv hpm C env hfu hfv hfm x.1 x.2 hx.1 (Bool.not_eq_false _ ▸ hx.2)
  -- Hop 2: through the ideal world, where the two reductions agree.
  have h₂ := prEvent_prfRealExperiment_le_of_ideal hU _ _
    (@prEvent_prfIdealExperiment_leftReduction _ _ P M η _ _ hmg hβ u v m g
      (Classical.decEq _) (M.uniformSampler P.hTy hU η) rfl)
  -- Hop 3: the second reduction's real world is the event `leftEvent` at uniform tapes and a
  -- fresh draw.
  have h₃ : Pr{let b ← (P.scheme M η).prfRealExperiment (leftFreshReduction η hmg hβ u v m g)}[
        b = true] ≤
      Pr{let yc ← $ᵗ (M.Coin η P.hTy); let ρ ← $ᵗ (M.Tape η)}[
        P.leftEvent hmg hβ g ((P.closeVec u).rv M C env)
          ((P.hashOracle (Γ := [])).denote (fullInterp M C) env)
          ((P.close v).denote (fullInterp M C) env) ((P.close m).denote (fullInterp M C) env) η
          ρ (M.sample η P.hTy yc)] := by
    rw [prEvent_prfRealExperiment_leftFreshReduction]
    have h := (update_coin_evalDistEq (P.keySlot M η) P.hTy).prEvent_eq (fun z =>
      P.leftEvent hmg hβ g ((P.closeVec u).rv M C env)
        ((P.hashOracle (Γ := [])).denote (fullInterp M C) env)
        ((P.close v).denote (fullInterp M C) env) ((P.close m).denote (fullInterp M C) env) η
        z.1 (M.sample η P.hTy z.2))
    simp only [prEvent_norm] at h ⊢
    rw [← h]
    refine prEvent_bind_mono_of_support _ _ _ fun kc _ =>
      prEvent_bind_mono_of_support _ _ _ fun ρ _ => prEvent_mono _ _ _ fun yc hyc => ?_
    exact leftEvent_of_outcome hmg hβ u v m g hh hg hku hkv hkm hpu hpv hpm C env kc ρ yc hyc
  -- Hop 4: the fresh draw read from the tape, and the premise and `C_sec`.
  have h₄ := prEvent_leftEvent_le hmg hβ g hh ((P.closeVec u).rv M C env)
    ((P.hashOracle (Γ := [])).denote (fullInterp M C) env)
    ((P.close v).denote (fullInterp M C) env) ((P.close m).denote (fullInterp M C) env)
    hpg hqg hru (fun η ρa ρa' ρh _ => by rw [denote_hashOracle]) hrv hrm hpc hη
  refine (prEvent_le_prEvent_add_prEvent_and_not _ _ (fun ρ =>
    (P.psiMsg (Env.append u (Env.cons v Env.empty)) m).denote (fullInterp M C) env η ρ =
      false)).trans ?_
  refine (add_le_add le_rfl (h₁.trans (h₂.trans (add_le_add le_rfl (h₃.trans h₄))))).trans
    (le_of_eq ?_)
  rw [← add_assoc, ← add_assoc, ← add_assoc]

end PRFSymbols

/-! ## PRF.L-sec -/

namespace Valid

variable {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {τs : List (Ty B)}

/-- **PRF.L-sec** (CCS26 §2.3; Fig. 4 and Remark 1), with the hash oracle `o_h^k = λx. h(x, k)`
on the left:

```
u⃗, o_h^k ⊬ v    [ψ_key(u⃗, v, m)]    [ψ_msg^{m,k}(u⃗, v, m)]    u⃗, o_h^k ⊬ m
-------------------------------------------------------------------------
                       u⃗, o_h^k, h(m, k) ⊬ v
```

for a closed vector `u⃗`, secret `v` and message `m` given as terms with calls, closed up. The
side condition `C_sec = u⃗, o_h^k ⊬ m` is the fourth premise. `ψ_msg` ranges over the calls of
`u⃗`, `v` and `m`, as in the rule of §2.3; Fig. 4's PRF.L-X does not ask it of `m`.

* `ψ_key`, `⊢pptm` and first order, with entries, secret and message of Boolean or base type, and
  a Boolean or base hash type.
* In every model of `R`: names of the hash type are uniform, the attacker tapes are long, and
  messages and hashes have polynomial bit blocks (the guess's default, and the fresh draw read
  from the tape); in every admitted model of `Θ` the terms read the attacker tape below a
  polynomial.
* `hprf` is the PRF assumption, on the named reductions `PRFSymbols.leftReduction` and
  `PRFSymbols.leftFreshReduction` of each admitted machine `g`: their PRF advantages
  (`PRFSymbols.prfAdv`) are negligible.

At every large `η`, for `g` reading the tape below `p` and making at most `q` input queries, and
with `pc` bounding the bit blocks of hashes,
`deduceAdv g (u⃗, h(m, k), o_h^k) v η ≤ Pr[ψ_msg(u⃗, v, m) = false] +
  prfAdv (leftReduction η hmg hβ u v m g) + prfAdv (leftFreshReduction η hmg hβ u v m g) +
  deduceAdv (freshL (swapLast g)) (u⃗, o_h^k) v η +
  2 ^ ⌈log₂ q(η)⌉ · deduceAdv (freshL (swapLast (rwGuess g))) (u⃗, o_h^k) m η`
(`PRFSymbols.leftAdvantage_le`), after swapping the last two entries of the left side
(`AdvClass.NonDed.swapLast`). -/
theorem nonDed_prfLSec (P : PRFSymbols D) {Θ : List (Form D [])} {β : Ty B} (u : OVec P [] τs)
    (v : OTerm P [] β) (m : OTerm P [] P.msgTy)
    {ho : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) β}
    {hom : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) P.msgTy}
    {ho' : Ty.SecrecyOrder ((τs ++ [.arrow P.msgTy P.hTy]) ++ [P.hTy]) β}
    (hg : ∀ τ ∈ τs, τ.IsGround) (hβ : β.IsGround) (hmg : P.msgTy.IsGround)
    (hh : P.hTy.IsGround) (hku : ∀ τ x, P.KeyFree (u τ x)) (hkv : P.KeyFree v)
    (hkm : P.KeyFree m) (hpu : ∀ τ x, P.Pptm (u τ x)) (hpv : P.Pptm v) (hpm : P.Pptm m)
    (hfu : ∀ τ x, P.FirstOrder (u τ x)) (hfv : P.FirstOrder v) (hfm : P.FirstOrder m)
    (hR : ∀ M, R M → M.UniformSampler P.hTy ∧ M.LongTapes ∧ M.PolyCoins P.msgTy ∧
      M.PolyCoins P.hTy)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      Vec.ReadsPoly M (C M) (P.closeVec u) env ∧ FTerm.ReadsPoly M (C M) (P.close v) env ∧
        FTerm.ReadsPoly M (C M) (P.close m) env)
    (hprf : ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler P.hTy,
      ∀ g : AdvMachine M ((τs ++ [P.hTy]) ++ [.arrow P.msgTy P.hTy]) β, (C M).mem g →
        negligible (fun η => P.prfAdv M η hU (P.leftReduction η hmg hβ u v m g)) ∧
          negligible (fun η => P.prfAdv M η hU (P.leftFreshReduction η hmg hβ u v m g)))
    (hmsg : Valid R C Θ (.box (P.psiMsg (Env.append u (Env.cons v Env.empty)) m)))
    (h : Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) P.hashOracle) (P.close v) ho))
    (hsec : Valid R C Θ (.nonDed (Vec.snoc (P.closeVec u) P.hashOracle) (P.close m) hom)) :
    Valid R C Θ (.nonDed (Vec.snoc (Vec.snoc (P.closeVec u) P.hashOracle)
      (P.hashTerm (P.close m))) (P.close v) ho') := by
  intro M hl hRM env hΘ
  obtain ⟨hU, hlong, hc, pc, hpc⟩ := hR M hRM
  obtain ⟨hru, ⟨pv, hpv'⟩, ⟨pm, hpm'⟩⟩ := hread M hl hRM env hΘ
  obtain ⟨pu, hpu'⟩ := hru.exists_readsBelow
  have hbox := Form.holds_box.1 (hmsg M hl hRM env hΘ)
  have h' := Form.holds_nonDed.1 (h M hl hRM env hΘ)
  have hs' := Form.holds_nonDed.1 (hsec M hl hRM env hΘ)
  rw [Vec.rv_snoc] at h' hs'
  rw [Form.holds_nonDed, Vec.rv_snoc, Vec.rv_snoc]
  refine AdvClass.NonDed.swapLast fun g hgm => ?_
  obtain ⟨pg, hpg⟩ := (C M).readBound_mem hgm
  obtain ⟨qg, hqg⟩ := (C M).queryBound_mem hgm
  set p := pg + pu + pv + pm
  have hle' : ∀ {r : Polynomial ℕ}, (r = pg ∨ r = pu ∨ r = pv ∨ r = pm) → ∀ η,
      r.eval η ≤ p.eval η := by
    rintro r (rfl | rfl | rfl | rfl) η <;> simp only [p, Polynomial.eval_add] <;> omega
  have hb : P.hTy.order ≤ 1 := (Ty.isGround_iff_order_eq_zero.1 hh).trans_le zero_le_one
  have hneg₁ := h' (g.swapLast.freshL (fun η => p.eval η) hb) ((C M).freshL_mem p hb ⟨pc, hpc⟩
    ((C M).rename_mem _ hgm))
  have hneg₂ := hs' ((g.rwGuess (p + pc) qg hmg hβ).swapLast.freshL (fun η => p.eval η) hb)
    ((C M).freshL_mem p hb ⟨pc, hpc⟩
      ((C M).rename_mem _ ((C M).rwGuess_mem (p + pc) qg hmg hβ hc hgm)))
  obtain ⟨hprf₁, hprf₂⟩ := hprf M hl hRM hU g hgm
  refine negligible_of_eventuallyLE ?_ (negligible_add (negligible_add (negligible_add
    (negligible_add hbox hprf₁) hprf₂) hneg₁) (negligible_polynomial_mul hneg₂ (2 * qg + 1)))
  filter_upwards [hlong (p + pc + qg)] with η hη
  have hη' : (p + pc).eval η + Nat.clog 2 (qg.eval η) ≤ M.lenA η := by
    have := Nat.clog_le_of_le_pow (b := 2) (Nat.lt_two_pow_self (n := qg.eval η)).le
    simp only [Polynomial.eval_add] at hη ⊢
    omega
  have hfac : (2 : ENNReal) ^ Nat.clog 2 (qg.eval η) ≤ ((2 * qg + 1).eval η : ℕ) := by
    have := Nat.pow_clog_le_mul_add_one 2 (qg.eval η)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      Polynomial.eval_ofNat]
    exact_mod_cast this
  have hbnd := P.leftAdvantage_le hmg hβ u v m g hU hh hg hku hkv hkm hpu hpv hpm hfu hfv hfm
    (C M) env (hpg.mono (hle' (.inl rfl))) hqg
    (fun τ x => (hpu' τ x).mono (hle' (.inr (.inl rfl))))
    (hpv'.mono (hle' (.inr (.inr (.inl rfl))))) (hpm'.mono (hle' (.inr (.inr (.inr rfl))))) hpc hη'
  simp only [Vec.rv_snoc] at hbnd
  exact hbnd.trans (add_le_add le_rfl (mul_le_mul' hfac le_rfl))

end Valid

/-! ## Instances, for derivations -/

/-- An instance of PRF.L-sec: the keyed hash, a closed vector, secret and message with calls, with
Boolean or base secret and message types, and the order bounds of the premises and the
conclusion. -/
structure PRFLInstance (D : Decl B) where
  /-- The keyed hash. -/
  P : PRFSymbols D
  /-- The types of the vector. -/
  τs : List (Ty B)
  /-- The type of the secret. -/
  β : Ty B
  /-- The vector, with calls. -/
  u : OVec P [] τs
  /-- The secret, with calls. -/
  v : OTerm P [] β
  /-- The message, with calls. -/
  m : OTerm P [] P.msgTy
  /-- The secret is Boolean or base. -/
  hβ : β.IsGround
  /-- Messages are Boolean or base. -/
  hmg : P.msgTy.IsGround
  /-- The premise has order at most one. -/
  order : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) β
  /-- `C_sec` has order at most one. -/
  orderM : Ty.SecrecyOrder (τs ++ [.arrow P.msgTy P.hTy]) P.msgTy
  /-- The conclusion has order at most one. -/
  orderC : Ty.SecrecyOrder ((τs ++ [.arrow P.msgTy P.hTy]) ++ [P.hTy]) β

namespace PRFLInstance

variable (e : PRFLInstance D)

/-- The syntactic side conditions of PRF.L-sec: entries and a hash type of Boolean or base type,
`ψ_key`, `⊢pptm` and first order. For names with decidable equality they are decidable, and
`decide` checks them. -/
@[expose] def Syntactic : Prop :=
  (∀ τ ∈ e.τs, τ.IsGround) ∧ e.P.hTy.IsGround ∧ (∀ τ x, e.P.KeyFree (e.u τ x)) ∧
    e.P.KeyFree e.v ∧ e.P.KeyFree e.m ∧ (∀ τ x, e.P.Pptm (e.u τ x)) ∧ e.P.Pptm e.v ∧
    e.P.Pptm e.m ∧ (∀ τ x, e.P.FirstOrder (e.u τ x)) ∧ e.P.FirstOrder e.v ∧ e.P.FirstOrder e.m

instance decidableSyntactic [DecidableEq ((a : Ty B) × (b : Ty B) × D.Name a b)] :
    Decidable e.Syntactic :=
  haveI := decidableForallEntries (fun _ t => e.P.KeyFree t) e.u
  haveI := decidableForallEntries (fun _ t => e.P.Pptm t) e.u
  haveI := decidableForallEntries (fun _ t => e.P.FirstOrder t) e.u
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The PRF assumption of PRF.L-sec: in every model of `R`, the two named reductions
`PRFSymbols.leftReduction` and `PRFSymbols.leftFreshReduction` of every admitted machine have
negligible PRF advantage. -/
@[expose] def Holds (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M) : Prop :=
  ∀ M : Model D, M.RespectsLabels → R M → ∀ hU : M.UniformSampler e.P.hTy,
    ∀ g : AdvMachine M ((e.τs ++ [e.P.hTy]) ++ [.arrow e.P.msgTy e.P.hTy]) e.β, (C M).mem g →
      negligible (fun η => e.P.prfAdv M η hU (e.P.leftReduction η e.hmg e.hβ e.u e.v e.m g)) ∧
        negligible (fun η => e.P.prfAdv M η hU (e.P.leftFreshReduction η e.hmg e.hβ e.u e.v e.m g))

/-- The left side of the premises, `u⃗, o_h^k`. -/
@[expose] def lhs : Vec D [] (e.τs ++ [.arrow e.P.msgTy e.P.hTy]) :=
  Vec.snoc (e.P.closeVec e.u) e.P.hashOracle

/-- PRF.L-sec at an instance. -/
theorem valid {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D [])}
    (hs : e.Syntactic) (hh : e.Holds R C)
    (hR : ∀ M, R M → M.UniformSampler e.P.hTy ∧ M.LongTapes ∧ M.PolyCoins e.P.msgTy ∧
      M.PolyCoins e.P.hTy)
    (hread : ∀ M : Model D, M.RespectsLabels → R M → ∀ env, (∀ θ ∈ Θ, θ.Holds M (C M) env) →
      Vec.ReadsPoly M (C M) (e.P.closeVec e.u) env ∧ FTerm.ReadsPoly M (C M) (e.P.close e.v) env ∧
        FTerm.ReadsPoly M (C M) (e.P.close e.m) env)
    (hmsg : Valid R C Θ (.box (e.P.psiMsg (Env.append e.u (Env.cons e.v Env.empty)) e.m)))
    (h : Valid R C Θ (.nonDed e.lhs (e.P.close e.v) e.order))
    (hsec : Valid R C Θ (.nonDed e.lhs (e.P.close e.m) e.orderM)) :
    Valid R C Θ (.nonDed (Vec.snoc e.lhs (e.P.hashTerm (e.P.close e.m))) (e.P.close e.v)
      e.orderC) :=
  let ⟨hg, hh', hku, hkv, hkm, hpu, hpv, hpm, hfu, hfv, hfm⟩ := hs
  Valid.nonDed_prfLSec e.P e.u e.v e.m hg e.hβ e.hmg hh' hku hkv hkm hpu hpv hpm hfu hfv hfm hR
    hread hh hmsg h hsec

end PRFLInstance

end Interop.Squirrel
