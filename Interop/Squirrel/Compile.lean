/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.OracleTerm
public import VCVio.OracleComp.SimSemantics.SimulateQ
public import VCVio.OracleComp.QueryTracking.RunLog

/-!
# Terms with calls, compiled to free programs

CCS26's PRF reduction (App. C.3) runs machines `A₁` and `A₂` that "recursively evaluate the
terms", reading the honest tape for names other than the key and calling the hash oracle "when a
hash with key k is needed"; LICS23 describes the same machine for EUF-CMA and PRF. Here that
machine is PolyFun's call-by-value reading `Term.denoteCBV` at one `CBVInterpretation`: a term
with calls (`OTerm`) is read as a free program over the interface `PRFSymbols.Iface P M η`, the sum
of

* the honest coins: the query `k` returns the bit block of the slot `k` of the honest tape;
* the attacker tape: one query returns `ρa`;
* the hash oracle: the query `x` returns a hash of the message `x`.

Values are Kleisli values (`Ty.KVal`): Booleans and base values as they are, and an arrow
`a → b` as a Kleisli arrow `a → OracleComp _ b`. The interpretation `PRFSymbols.cbvInterp` is the
sum (`CBVInterpretation.sum`) of a reading of the local constructors and a reading of the call:
application runs the function, then the argument, then the closure; an abstraction returns a
closure; a conditional runs only the branch it takes; a name queries the coin of its slot and runs
the sampler; an attacker symbol queries the tape; and `call t` runs `t` and queries the hash
oracle. Nothing else is defined: the compiled program of a term `t` is `t.denoteCBV
(P.cbvInterp M η) env`. A reduction answers its queries by a handler (`simulateQ`): the coins and
the tape from tapes it draws itself, and the hash from its PRF oracle.

## Adequacy

`PRFSymbols.answer M η ρ kv` answers from the tapes `ρ` and hashes with the key value `kv`.
Running the compiled program with these answers gives the ordinary reading of the term with its
calls read as `h(·, kv)` (`PRFSymbols.lower_evalWithAnswerFn_denoteCBV`). The proof is PolyFun's
fundamental lemma `Term.denoteCBV_related` at a logical relation, with nothing proved by
induction over terms here: the relation `PRFSymbols.CRel` is equality at Boolean and base types
and, at `a → b`, "related arguments give related runs"; the one obligation is that each head of the
`⊢pptm` fragment sends related arguments to related results (`CBVInterpretation.RelatedOn`).

The same relation also tracks which messages the run hashes. `PRFSymbols.HashOK ans Q c` says
that every hash query of the run of `c` (VCVio's `runLog`) satisfies `Q`. The ordinary reading is
paired with a proposition, `PRFSymbols.guardInterp`: the conjunction of `Q` over the arguments of
every call in the term, under abstractions for every value of the bound variable, with conditions
of conditionals dropped. `PRFSymbols.denoteCBV_guard` is the theorem: where that proposition
holds, the run's hash queries satisfy `Q`. With `Q` the inequality to the challenge message this is
what `ψ_msg` gives a reduction: it never queries the challenge before the challenge itself
(`PRFSymbols.snd_denote_guardInterp_iff` relates the proposition to `PRFSymbols.calls` for
first-order terms).

## References

* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Fig. 10 and Prop. 17.
* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: App. C.3.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec

variable {B : Type} {D : Decl B}

/-! ## Kleisli values -/

/-- The values of a type when arrows are Kleisli arrows of the monad `m`. -/
@[expose, reducible] def Ty.KVal (m : Type → Type) (carrier : B → ℕ → Set (List Bool)) (η : ℕ) :
    Ty B → Type
  | .bool => Bool
  | .base b => carrier b η
  | .arrow a b => a.KVal m carrier η → m (b.KVal m carrier η)

/-- The Kleisli values of a sort; the global sort has none. -/
@[expose, reducible] def Kind.KVal (m : Type → Type) (M : Model D) (η : ℕ) : Kind B → Type
  | .loc τ => τ.KVal m M.carrier η
  | .glob => PUnit

variable {m : Type → Type}

/-- The value of a Boolean or base Kleisli value; at arrow types an arbitrary value, which no
reading in the fragment uses. -/
@[expose] noncomputable def Model.lower (M : Model D) (η : ℕ) :
    (τ : Ty B) → τ.KVal m M.carrier η → τ.Value M.carrier η
  | .bool, v => v
  | .base _, v => v
  | .arrow a b, _ => Classical.choice (Ty.nonempty_value M.nonempty η (.arrow a b))

/-- A value as a Kleisli value: an arrow returns, by `pure`, the value at the argument's value. -/
@[expose] noncomputable def Model.embed [Pure m] (M : Model D) (η : ℕ) :
    (τ : Ty B) → τ.Value M.carrier η → τ.KVal m M.carrier η
  | .bool, v => v
  | .base _, v => v
  | .arrow a b, f => fun x => pure (M.embed η b (f (M.lower η a x)))

/-- A Boolean or base value embedded as a Kleisli value and lowered back is itself. -/
theorem Model.lower_embed [Pure m] (M : Model D) (η : ℕ) {τ : Ty B} (hτ : τ.IsGround)
    (v : τ.Value M.carrier η) : M.lower (m := m) η τ (M.embed η τ v) = v := by
  cases τ with
  | bool => rfl
  | base _ => rfl
  | arrow _ _ => exact hτ.elim

namespace PRFSymbols

variable (P : PRFSymbols D) (M : Model D) (η : ℕ)

/-! ## The interface -/

/-- The hash's domain at `η`. -/
abbrev Dom : Type := P.msgTy.Value M.carrier η

/-- The hash's range at `η`. -/
abbrev Rng : Type := P.hTy.Value M.carrier η

/-- The interface of the compiled reading: the honest coin of each slot, the attacker tape, and
the hash oracle. -/
abbrev Iface : OracleSpec ((M.Slot η ⊕ Unit) ⊕ P.Dom M η) :=
  (OracleSpec.ofFn (fun k : M.Slot η => M.Coin η k.1.2.1) +
      OracleSpec.ofFn (fun _ : Unit => M.TapeA η)) +
    (P.Dom M η →ₒ P.Rng M η)

/-- Kleisli values of the compiled reading. -/
abbrev CV : Kind B → Type := Kind.KVal (OracleComp (P.Iface M η)) M η

/-- Query the coin of the slot `k`. -/
@[expose] def askCoin (k : M.Slot η) : OracleComp (P.Iface M η) (M.Coin η k.1.2.1) :=
  liftM ((P.Iface M η).query (.inl (.inl k)))

/-- Query the attacker tape. -/
@[expose] def askTape : OracleComp (P.Iface M η) (M.TapeA η) :=
  liftM ((P.Iface M η).query (.inl (.inr ())))

/-- Query the hash oracle. -/
@[expose] def askHash (x : P.Dom M η) : OracleComp (P.Iface M η) (P.Rng M η) :=
  liftM ((P.Iface M η).query (.inr x))

/-! ## The interpretation -/

/-- The call-by-value reading of the local constructors. Local quantifiers are read as `true`:
they are outside the fragment (`PRFSymbols.PptmAt`). -/
@[expose] noncomputable def cbvLocal :
    CBVInterpretation (localSig D) (OracleComp (P.Iface M η)) (P.CV M η)
  | _, .app _ _, next => do
      let f ← next 0 Env.empty
      let x ← next 1 Env.empty
      f x
  | _, .lam _ _, next => pure fun x => next 0 (Env.single x)
  | _, .ite _, next => do
      let c ← next 0 Env.empty
      cond c (next 1 Env.empty) (next 2 Env.empty)
  | _, .tt, _ => pure true
  | _, .ff, _ => pure false
  | _, .eq a, _ => pure fun x => pure fun y =>
      pure (@decide (M.lower η a x = M.lower η a y) (Classical.propDecidable _))
  | _, .all _, _ => pure fun _ => pure true
  | _, .ex _, _ => pure fun _ => pure true
  | _, @LocalOp.name _ _ a b n, _ => pure fun x => do
      let c ← P.askCoin M η ⟨⟨a, b, n⟩, M.lower η a x⟩
      pure (M.embed η b (M.sample η b c))
  | _, @LocalOp.fn _ _ τ f, _ => pure (M.embed η τ (M.fn η f))
  | _, .att f, _ => do
      let ρa ← P.askTape M η
      pure (M.embed η _ (M.att η f ρa))

/-- The call-by-value reading of a call: run the message, then query the hash oracle. -/
@[expose] noncomputable def cbvCall :
    CBVInterpretation P.callSig (OracleComp (P.Iface M η)) (P.CV M η)
  | _, .call, next => do
      let x ← next () Env.empty
      M.embed η P.hTy <$> P.askHash M η (M.lower η P.msgTy x)

/-- **The compiled reading** of terms with calls, as a call-by-value interpretation of the sum
signature: the reading of the local constructors and that of the call. The compiled program of a
term `t` is PolyFun's `t.denoteCBV (P.cbvInterp M η) env`. -/
@[expose, reducible] noncomputable def cbvInterp :
    CBVInterpretation P.oSig (OracleComp (P.Iface M η)) (P.CV M η) :=
  CBVInterpretation.sum (P.cbvLocal M η) (P.cbvCall M η)

/-! ## Answers, runs and hash logs -/

/-- The answers of the tapes `ρ` with hashes keyed by `kv`. -/
@[expose] def answer (ρ : M.Tape η) (kv : P.keyTy.Value M.carrier η) :
    QueryImpl (P.Iface M η) Id
  | .inl (.inl k) => ρ.2 k
  | .inl (.inr ()) => ρ.1
  | .inr x => M.fn η P.hOf x kv

variable {P M η}

/-- Every message that the run of `c` with the answers `ans` hashes satisfies `Q`. -/
@[expose] def HashOK (ans : QueryImpl (P.Iface M η) Id) (Q : P.Dom M η → Prop) {α : Type}
    (c : OracleComp (P.Iface M η) α) : Prop :=
  ∀ x, Sum.inr x ∈ (runLog ans c).map (fun e => e.1) → Q x

section Runs

variable {ans : QueryImpl (P.Iface M η) Id} {α β : Type}

theorem hashOK_pure (Q : P.Dom M η → Prop) (a : α) :
    HashOK ans Q (pure a : OracleComp (P.Iface M η) α) := by
  intro x hx
  simp at hx

theorem hashOK_bind_iff {Q : P.Dom M η → Prop} {c : OracleComp (P.Iface M η) α}
    {f : α → OracleComp (P.Iface M η) β} :
    HashOK ans Q (c >>= f) ↔ HashOK ans Q c ∧ HashOK ans Q (f (evalWithAnswerFn ans c)) := by
  simp only [HashOK, runLog_bind, List.map_append, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem hashOK_map {Q : P.Dom M η → Prop} {c : OracleComp (P.Iface M η) α} (g : α → β)
    (h : HashOK ans Q c) : HashOK ans Q (g <$> c) := by
  rw [map_eq_bind_pure_comp]
  exact hashOK_bind_iff.2 ⟨h, hashOK_pure Q _⟩

theorem hashOK_askCoin (Q : P.Dom M η → Prop) (k : M.Slot η) :
    HashOK ans Q (P.askCoin M η k) := by
  intro x hx
  rw [askCoin, runLog_query] at hx
  simp at hx

theorem hashOK_askTape (Q : P.Dom M η → Prop) : HashOK ans Q (P.askTape M η) := by
  intro x hx
  rw [askTape, runLog_query] at hx
  simp at hx

theorem hashOK_askHash {Q : P.Dom M η → Prop} {x : P.Dom M η} (hx : Q x) :
    HashOK ans Q (P.askHash M η x) := by
  intro y hy
  rw [askHash, runLog_query] at hy
  simp only [List.map_cons, List.map_nil, List.mem_singleton, Sum.inr.injEq] at hy
  exact hy ▸ hx

end Runs

/-! ## The logical relation -/

section Relation

variable (ans : QueryImpl (P.Iface M η) Id) (Q : P.Dom M η → Prop)

/-- Kleisli values related to values: equal at Boolean and base types, and at `a → b`, related
arguments give runs that return related values and hash only messages satisfying `Q`. -/
@[expose] def CRel : (τ : Ty B) → τ.KVal (OracleComp (P.Iface M η)) M.carrier η →
    τ.Value M.carrier η → Prop
  | .bool, v, w => v = w
  | .base _, v, w => v = w
  | .arrow a b, g, f => ∀ y x, CRel a y x →
      CRel b (evalWithAnswerFn ans (g y)) (f x) ∧ HashOK ans Q (g y)

/-- `CRel` at a sort; the global sort relates everything. -/
@[expose] def CRelK : (s : Kind B) → P.CV M η s → Kind.PtValue M η s → Prop
  | .loc τ, v, w => CRel ans Q τ v w
  | .glob, _, _ => True

variable {ans Q}

/-- At a Boolean or base type, a related Kleisli value lowers to the value. -/
theorem CRel.lower_eq : ∀ {τ : Ty B}, τ.IsGround → ∀ {v w}, CRel ans Q τ v w → M.lower η τ v = w
  | .bool, _, _, _, h => h
  | .base _, _, _, _, h => h
  | .arrow _ _, h, _, _, _ => h.elim

/-- The embedding of a value of a type of order at most one is related to it. -/
theorem crel_embed : ∀ {τ : Ty B}, τ.order ≤ 1 → ∀ w, CRel ans Q τ (M.embed η τ w) w
  | .bool, _, _ => rfl
  | .base _, _, _ => rfl
  | .arrow a b, h, w => fun y x hyx => by
    have ha : a.IsGround := Ty.isGround_of_order_arrow_le_one h
    change CRel ans Q b (evalWithAnswerFn ans (pure _)) (w x) ∧ HashOK ans Q (pure _)
    refine ⟨?_, hashOK_pure Q _⟩
    rw [evalWithAnswerFn_pure, hyx.lower_eq ha]
    exact crel_embed (le_trans (Ty.order_cod_le a b) h) _

end Relation

/-! ## Pairing the reading with a condition on calls -/

/-- An environment of values, each paired with `True`. -/
@[expose] def pairEnv {Γ : List (Kind B)} (e : Env (Kind.PtValue M η) Γ) :
    Env (fun s => Kind.PtValue M η s × Prop) Γ :=
  fun s x => (e s x, True)

theorem pairEnv_append {Ξ Γ : List (Kind B)} (ξ : Env (Kind.PtValue M η) Ξ)
    (e : Env (Kind.PtValue M η) Γ) :
    pairEnv (Env.append ξ e) = Env.append (pairEnv ξ) (pairEnv e) := by
  induction Ξ with
  | nil => rfl
  | cons s Ξ ih =>
    funext t x
    cases x with
    | zero => rfl
    | succ x => exact congrFun (congrFun (ih fun b v => ξ b (.succ v)) t) x

private theorem pairEnv_empty :
    (Env.empty : Env (fun s => Kind.PtValue M η s × Prop) []) = pairEnv Env.empty :=
  (Env.eq_empty _).symm

variable (P) in
/-- The ordinary reading paired with a proposition: the conjunction of `Q` over the arguments of
all calls, read under an abstraction at every value of its variable. The conditions of
conditionals are dropped. -/
@[expose] noncomputable def guardInterp (ρ : M.Tape η) (kv : P.keyTy.Value M.carrier η)
    (Q : P.Dom M η → Prop) : Interpretation P.oSig (fun s => Kind.PtValue M η s × Prop)
  | _, .inl o, next => (interp M η ρ o fun p ξ => (next p (pairEnv ξ)).1,
      ∀ p ξ, (next p (pairEnv ξ)).2)
  | _, .inr .call, next => (M.fn η P.hOf (next () Env.empty).1 kv,
      (next () Env.empty).2 ∧ Q (next () Env.empty).1)

variable {ρ : M.Tape η} {kv : P.keyTy.Value M.carrier η}

/-- The first component of the paired reading is the ordinary reading. -/
theorem fst_denote_guardInterp (Q : P.Dom M η → Prop) {Γ : List (Kind B)} {s : Kind B}
    (t : P.oSig.Term Γ s) (e : Env (Kind.PtValue M η) Γ) :
    (t.denote (P.guardInterp ρ kv Q) (pairEnv e)).1 = t.denote (P.ointerp M η ρ kv) e := by
  induction t using Term.inductionOn with
  | hvar Γ s x => rfl
  | hnode Γ s op args ih =>
    rw [Term.denote_node, Term.denote_node]
    rcases op with o | o
    · change interp M η ρ o _ = interp M η ρ o _
      congr 1
      funext p ξ
      dsimp only
      rw [← pairEnv_append, ih]
    · cases o
      change M.fn η P.hOf _ kv = M.fn η P.hOf _ kv
      dsimp only
      rw [pairEnv_empty, ← pairEnv_append, ih]

/-- With no condition on calls, the second component of the paired reading holds. -/
theorem snd_denote_guardInterp_true {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s)
    (e : Env (Kind.PtValue M η) Γ) :
    (t.denote (P.guardInterp ρ kv fun _ => True) (pairEnv e)).2 := by
  induction t using Term.inductionOn with
  | hvar Γ s x => trivial
  | hnode Γ s op args ih =>
    rcases op with o | o
    · intro p ξ
      change (Term.denote _ (args p) (Env.append (pairEnv ξ) (pairEnv e))).2
      rw [← pairEnv_append]
      exact ih p _
    · cases o
      refine ⟨?_, trivial⟩
      change (Term.denote _ (args ()) (Env.append Env.empty (pairEnv e))).2
      rw [pairEnv_empty, ← pairEnv_append]
      exact ih () _

/-- For a first-order term, the paired condition is the conjunction of `Q` over the values of
the arguments of its calls (`PRFSymbols.calls`). -/
theorem snd_denote_guardInterp_iff (Q : P.Dom M η → Prop) {Γ : List (Kind B)} {s : Kind B}
    (t : P.oSig.Term Γ s) (ht : P.FirstOrder t) (e : Env (Kind.PtValue M η) Γ) :
    (t.denote (P.guardInterp ρ kv Q) (pairEnv e)).2 ↔
      ∀ t' ∈ P.calls t, Q (t'.denote (P.ointerp M η ρ kv) e) := by
  induction t using Term.inductionOn with
  | hvar Γ s x => exact iff_of_true trivial fun _ h => absurd h List.not_mem_nil
  | hnode Γ s op args ih =>
    have ih' := fun p => ih p ((Term.heads_subset_heads_node op args p).trans ht)
    rcases op with o | o
    · cases o with
      | app a b =>
        change (∀ p ξ, (Term.denote _ (args p) (Env.append (pairEnv ξ) (pairEnv e))).2) ↔
          ∀ t' ∈ P.calls (args 0) ++ P.calls (args 1), _
        refine ⟨fun h t' ht' => ?_, fun h p ξ => ?_⟩
        · rcases List.mem_append.1 ht' with h' | h'
          · exact (ih' 0 e).1 (h 0 Env.empty) t' h'
          · exact (ih' 1 e).1 (h 1 Env.empty) t' h'
        · refine Fin.cases ?_ (Fin.cases ?_ fun i => i.elim0) p
          · exact (ih' 0 e).2 fun t' h' => h t' (List.mem_append_left _ h')
          · exact (ih' 1 e).2 fun t' h' => h t' (List.mem_append_right _ h')
      | lam a b => exact (ht (Term.mem_heads_node_self _ args)).elim
      | ite a =>
        change (∀ p ξ, (Term.denote _ (args p) (Env.append (pairEnv ξ) (pairEnv e))).2) ↔
          ∀ t' ∈ P.calls (args 0) ++ P.calls (args 1) ++ P.calls (args 2), _
        refine ⟨fun h t' ht' => ?_, fun h p ξ => ?_⟩
        · rcases List.mem_append.1 ht' with h' | h'
          · rcases List.mem_append.1 h' with h' | h'
            · exact (ih' 0 e).1 (h 0 Env.empty) t' h'
            · exact (ih' 1 e).1 (h 1 Env.empty) t' h'
          · exact (ih' 2 e).1 (h 2 Env.empty) t' h'
        · refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ fun i => i.elim0)) p
          · exact (ih' 0 e).2 fun t' h' =>
              h t' (List.mem_append_left _ (List.mem_append_left _ h'))
          · exact (ih' 1 e).2 fun t' h' =>
              h t' (List.mem_append_left _ (List.mem_append_right _ h'))
          · exact (ih' 2 e).2 fun t' h' => h t' (List.mem_append_right _ h')
      | _ => exact iff_of_true (fun p => p.elim0) fun _ h => absurd h List.not_mem_nil
    · cases o
      change (Term.denote _ (args ()) (Env.append Env.empty (pairEnv e))).2 ∧ _ ↔
        ∀ t' ∈ (P.callsAux (args ())).1 :: P.calls (args ()), _
      rw [fst_callsAux, List.forall_mem_cons, ← ih' () e]
      change _ ∧ Q (Term.denote _ (args ()) (pairEnv e)).1 ↔ _
      rw [fst_denote_guardInterp]
      exact and_comm

/-- For a term without the key name, the paired reading is the same at two honest tapes that
agree on every coordinate not belonging to the key name. -/
theorem guardInterp_eq_of_keyFree {ρa : M.TapeA η} {ρh ρh' : M.TapeH η}
    (hρ : ∀ k : M.Slot η, k.1 ≠ P.keyName → ρh k = ρh' k) (Q : P.Dom M η → Prop)
    {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) (ht : P.KeyFree t) :
    t.denote (P.guardInterp (ρa, ρh) kv Q) = t.denote (P.guardInterp (ρa, ρh') kv Q) := by
  refine Term.denote_congr_of_heads_subset t ht ?_
  rintro ⟨s, o | o⟩ ho
  · funext next
    exact congrArg (·, _) (congrFun (interp_eq_of_keyFreeAt hρ o ho) _)
  · cases o
    rfl

/-! ## The fundamental lemma at the paired reading -/

section Guard

variable (ρ kv) (Q : P.Dom M η → Prop)

/-- Values related where the paired condition holds. -/
private def GuardRV (s : Kind B) (v : P.CV M η s) (w : Kind.PtValue M η s × Prop) : Prop :=
  w.2 → CRelK (P.answer M η ρ kv) Q s v w.1

/-- Computations related where the paired condition holds: they return related values and hash
only messages satisfying `Q`. -/
private def GuardRC (s : Kind B) (c : OracleComp (P.Iface M η) (P.CV M η s))
    (w : Kind.PtValue M η s × Prop) : Prop :=
  w.2 → CRelK (P.answer M η ρ kv) Q s (evalWithAnswerFn (P.answer M η ρ kv) c) w.1 ∧
    HashOK (P.answer M η ρ kv) Q c

/-- **The compiled reading simulates the paired reading** at every head of the `⊢pptm`
fragment: the one obligation of PolyFun's fundamental lemma, checked head by head. -/
private theorem relatedOn_guard :
    CBVInterpretation.RelatedOn {h | P.PptmAt h} (GuardRV ρ kv Q) (GuardRC ρ kv Q)
      (P.cbvInterp M η) (P.guardInterp ρ kv Q) := by
  rintro ⟨s, o | o⟩ hok nextV nextW h
  · cases o with
    | app a b =>
      intro hw
      obtain ⟨hf, hfo⟩ := h 0 Env.empty (pairEnv Env.empty) (fun _ x => nomatch x) (hw 0 Env.empty)
      obtain ⟨hx, hxo⟩ := h 1 Env.empty (pairEnv Env.empty) (fun _ x => nomatch x) (hw 1 Env.empty)
      obtain ⟨hy, hyo⟩ := hf _ _ hx
      refine ⟨?_, hashOK_bind_iff.2 ⟨hfo, hashOK_bind_iff.2 ⟨hxo, hyo⟩⟩⟩
      change CRel _ Q b (evalWithAnswerFn _ (_ >>= _)) _
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind]
      exact hy
    | lam a b =>
      intro hw
      refine ⟨fun y x hyx => h 0 (Env.single y) (pairEnv (Env.single x)) (fun _ z => ?_)
        (hw 0 (Env.single x)), hashOK_pure Q _⟩
      cases z with
      | zero => exact fun _ => hyx
      | succ z => exact nomatch z
    | ite a =>
      intro hw
      obtain ⟨hc, hco⟩ := h 0 Env.empty (pairEnv Env.empty) (fun _ x => nomatch x) (hw 0 Env.empty)
      obtain ⟨ht, hto⟩ := h 1 Env.empty (pairEnv Env.empty) (fun _ x => nomatch x) (hw 1 Env.empty)
      obtain ⟨he, heo⟩ := h 2 Env.empty (pairEnv Env.empty) (fun _ x => nomatch x) (hw 2 Env.empty)
      change _ = _ at hc
      refine ⟨?_, hashOK_bind_iff.2 ⟨hco, ?_⟩⟩
      · change CRel _ Q a (evalWithAnswerFn _ (_ >>= _)) (cond _ _ _)
        rw [evalWithAnswerFn_bind, hc]
        dsimp only
        cases (nextW 0 (pairEnv Env.empty)).1
        · exact he
        · exact ht
      · rw [hc]
        cases (nextW 0 (pairEnv Env.empty)).1
        · exact heo
        · exact hto
    | tt => exact fun _ => ⟨rfl, hashOK_pure Q _⟩
    | ff => exact fun _ => ⟨rfl, hashOK_pure Q _⟩
    | eq a =>
      intro _
      refine ⟨fun y x hyx => ⟨fun y' x' hyx' => ⟨?_, hashOK_pure Q _⟩, hashOK_pure Q _⟩,
        hashOK_pure Q _⟩
      change @decide (M.lower η a y = M.lower η a y') (Classical.propDecidable _) =
        @decide (x = x') (Classical.propDecidable _)
      rw [hyx.lower_eq hok, hyx'.lower_eq hok]
    | all _ => exact hok.elim
    | ex _ => exact hok.elim
    | name n =>
      intro _
      refine ⟨fun y x hyx => ⟨?_, hashOK_bind_iff.2 ⟨hashOK_askCoin Q _, hashOK_pure Q _⟩⟩,
        hashOK_pure Q _⟩
      change CRel _ Q _ (evalWithAnswerFn _ (_ >>= _)) (M.name η n x ρ.2)
      rw [evalWithAnswerFn_bind, hyx.lower_eq hok.1]
      exact crel_embed hok.2 _
    | fn f => exact fun _ => ⟨crel_embed hok _, hashOK_pure Q _⟩
    | att f =>
      intro _
      refine ⟨?_, hashOK_bind_iff.2 ⟨hashOK_askTape Q, hashOK_pure Q _⟩⟩
      change CRel _ Q _ (evalWithAnswerFn _ (_ >>= _)) (M.att η f ρ.1)
      rw [evalWithAnswerFn_bind]
      exact crel_embed hok _
  · cases o
    intro hw
    obtain ⟨hx, hxo⟩ := h () Env.empty Env.empty (fun _ x => nomatch x) hw.1
    refine ⟨?_, hashOK_bind_iff.2 ⟨hxo, hashOK_map _ (hashOK_askHash ?_)⟩⟩
    · change CRel _ Q P.hTy (evalWithAnswerFn _ (_ >>= _)) (M.fn η P.hOf _ kv)
      rw [evalWithAnswerFn_bind, evalWithAnswerFn_map, hx.lower_eq hok.1]
      exact crel_embed (by rw [Ty.isGround_iff_order_eq_zero.1 hok.2]; exact Nat.zero_le 1) _
    · rw [hx.lower_eq hok.1]
      exact hw.2

variable {ρ kv Q}

/-- **The compiled reading tracks the hashes** (CCS26 App. C.3: "when encountering a hash with
`k(t′)`, … call the hashing oracle"). For a term of the `⊢pptm` fragment, in environments related
by `CRel`, where the conjunction of `Q` over the arguments of the term's calls holds
(`guardInterp`), running the compiled term with the answers of `ρ` and `kv` returns a value
related to the ordinary reading of the term at `ρ` with calls hashed under `kv`, and hashes only
messages satisfying `Q`. It is PolyFun's fundamental lemma `Term.denoteCBV_related` at the
relations `GuardRV` and `GuardRC`. -/
theorem denoteCBV_guard {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s) (ht : P.Pptm t)
    {eV : Env (P.CV M η) Γ} {e : Env (Kind.PtValue M η) Γ}
    (he : Env.LiftRel (CRelK (P.answer M η ρ kv) Q) eV e)
    (hg : (t.denote (P.guardInterp ρ kv Q) (pairEnv e)).2) :
    CRelK (P.answer M η ρ kv) Q s
        (evalWithAnswerFn (P.answer M η ρ kv) (t.denoteCBV (P.cbvInterp M η) eV))
        (t.denote (P.ointerp M η ρ kv) e) ∧
      HashOK (P.answer M η ρ kv) Q (t.denoteCBV (P.cbvInterp M η) eV) := by
  have h := Term.denoteCBV_related (fun _ _ _ hv hw => ⟨hv hw, hashOK_pure Q _⟩)
    (relatedOn_guard ρ kv Q) t ht (η := eV) (ζ := pairEnv e) fun s x _ => he s x
  rw [GuardRC, fst_denote_guardInterp] at h
  exact h hg

/-- **Adequacy** of the compiled reading: for a term of the `⊢pptm` fragment, in related
environments, the run of the compiled term with the answers of `ρ` and `kv` is related to the
ordinary reading at `ρ` with calls hashed under `kv`. -/
theorem denoteCBV_adequate {Γ : List (Kind B)} {s : Kind B} (t : P.oSig.Term Γ s)
    (ht : P.Pptm t) {eV : Env (P.CV M η) Γ} {e : Env (Kind.PtValue M η) Γ}
    (he : Env.LiftRel (CRelK (P.answer M η ρ kv) fun _ => True) eV e) :
    CRelK (P.answer M η ρ kv) (fun _ => True) s
      (evalWithAnswerFn (P.answer M η ρ kv) (t.denoteCBV (P.cbvInterp M η) eV))
      (t.denote (P.ointerp M η ρ kv) e) :=
  (denoteCBV_guard t ht he (snd_denote_guardInterp_true t e)).1

/-- **Adequacy at a closed term of Boolean or base type**: the run of the compiled term with the
answers of `ρ` and `kv` is the ordinary reading at `ρ` with calls hashed under `kv`. -/
theorem lower_evalWithAnswerFn_denoteCBV {τ : Ty B} (hτ : τ.IsGround) (t : OTerm P [] τ)
    (ht : P.Pptm t) :
    M.lower η τ (evalWithAnswerFn (P.answer M η ρ kv)
        (t.denoteCBV (P.cbvInterp M η) Env.empty)) =
      t.denote (P.ointerp M η ρ kv) Env.empty :=
  CRel.lower_eq hτ (denoteCBV_adequate (e := Env.empty) t ht (Env.liftRel_empty _))

/-! ## Hashed messages -/

/-- **A hashed message is the value of a call argument.** The run of a closed first-order term of
the `⊢pptm` fragment, with the answers of `ρ` and `kv`, hashes only values of the arguments of its
calls (`denoteCBV_guard` at `Q = (· ≠ x)`). -/
theorem exists_mem_calls_of_hashed {τ : Ty B} (t : OTerm P [] τ) (hp : P.Pptm t)
    (hf : P.FirstOrder t) {x : P.Dom M η}
    (hx : Sum.inr x ∈ (runLog (P.answer M η ρ kv)
      (t.denoteCBV (P.cbvInterp M η) Env.empty)).map (fun e => e.1)) :
    ∃ t' ∈ P.calls t, t'.denote (P.ointerp M η ρ kv) Env.empty = x := by
  by_contra h
  push Not at h
  have hg : (t.denote (P.guardInterp ρ kv fun y => y ≠ x) (pairEnv Env.empty)).2 :=
    (snd_denote_guardInterp_iff _ t hf Env.empty).2 h
  exact (denoteCBV_guard (e := Env.empty) t hp (Env.liftRel_empty _) hg).2 x hx rfl

/-- **A candidate not hashed by its own run.** Among a closed first-order message `m` of the
`⊢pptm` fragment and the arguments of its calls, some term has `m`'s value and its run does not
hash that value. If a term's run hashes its own value, a call argument has that value
(`exists_mem_calls_of_hashed`) and fewer calls (`PRFSymbols.length_calls_lt`), so the descent
stops. -/
theorem exists_unhashed (m : OTerm P [] P.msgTy) (hp : P.Pptm m) (hf : P.FirstOrder m) :
    ∃ t ∈ m :: P.calls m, t.denote (P.ointerp M η ρ kv) Env.empty =
        m.denote (P.ointerp M η ρ kv) Env.empty ∧
      Sum.inr (m.denote (P.ointerp M η ρ kv) Env.empty) ∉ (runLog (P.answer M η ρ kv)
        (t.denoteCBV (P.cbvInterp M η) Env.empty)).map (fun e => e.1) := by
  set x := m.denote (P.ointerp M η ρ kv) Env.empty
  have key : ∀ n, ∀ t ∈ m :: P.calls m, (P.calls t).length = n →
      t.denote (P.ointerp M η ρ kv) Env.empty = x →
        ∃ t₀ ∈ m :: P.calls m, t₀.denote (P.ointerp M η ρ kv) Env.empty = x ∧
          Sum.inr x ∉ (runLog (P.answer M η ρ kv)
            (t₀.denoteCBV (P.cbvInterp M η) Env.empty)).map (fun e => e.1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht hn htx
      have hsub : t.heads ⊆ m.heads := by
        rcases List.mem_cons.1 ht with rfl | h
        · exact subset_rfl
        · exact heads_subset_of_mem_calls m t h
      by_cases hx : Sum.inr x ∈ (runLog (P.answer M η ρ kv)
          (t.denoteCBV (P.cbvInterp M η) Env.empty)).map (fun e => e.1)
      · obtain ⟨t', ht', ht'x⟩ := exists_mem_calls_of_hashed t (hsub.trans hp) (hsub.trans hf) hx
        refine ih _ (hn ▸ length_calls_lt ht') t' ?_ rfl (ht'x.trans rfl)
        rcases List.mem_cons.1 ht with rfl | h
        · exact List.mem_cons_of_mem _ ht'
        · exact List.mem_cons_of_mem _ (mem_calls_of_mem_calls h ht')
      · exact ⟨t, ht, htx, hx⟩
  exact key _ m List.mem_cons_self rfl rfl

end Guard

/-! ## Compiling a vector and a message -/

variable (P M η) in
/-- Compile the closed entries of a vector one after the other, and lower their values. -/
@[expose] noncomputable def cbvVec : {τs : List (Ty B)} → OVec P [] τs →
    OracleComp (P.Iface M η) (Vals M η τs)
  | [], _ => pure Env.empty
  | τ :: _, u => do
      let x ← (u _ .zero).denoteCBV (P.cbvInterp M η) Env.empty
      let xs ← cbvVec fun _ y => u _ (.succ y)
      pure (Env.cons (M.lower η τ x) xs)

variable (P M η) in
/-- The program that a PRF reduction runs: compile the vector `u⃗`, then the message `m`. -/
@[expose] noncomputable def prog {τs : List (Ty B)} (u : OVec P [] τs) (m : OTerm P [] P.msgTy) :
    OracleComp (P.Iface M η) (Vals M η τs × P.Dom M η) := do
  let e ← P.cbvVec M η u
  let x ← m.denoteCBV (P.cbvInterp M η) Env.empty
  pure (e, M.lower η P.msgTy x)

/-- The compiled vector returns the readings of its entries and hashes only messages satisfying
`Q`, for entries of Boolean or base type in the `⊢pptm` fragment whose calls have arguments
satisfying `Q`. -/
theorem cbvVec_spec (Q : P.Dom M η → Prop) :
    ∀ {τs : List (Ty B)} (u : OVec P [] τs), (∀ τ ∈ τs, τ.IsGround) → (∀ τ x, P.Pptm (u τ x)) →
      (∀ τ x, ((u τ x).denote (P.guardInterp ρ kv Q) (pairEnv Env.empty)).2) →
      evalWithAnswerFn (P.answer M η ρ kv) (P.cbvVec M η u) =
          (fun τ x => (u τ x).denote (P.ointerp M η ρ kv) Env.empty) ∧
        HashOK (P.answer M η ρ kv) Q (P.cbvVec M η u)
  | [], u, _, _, _ => ⟨funext fun _ => funext fun x => (nomatch x), hashOK_pure Q _⟩
  | τ :: τs, u, hg, hp, hq => by
    obtain ⟨h₁, h₁o⟩ := denoteCBV_guard (u _ .zero) (hp _ .zero) (e := Env.empty)
      (Env.liftRel_empty _) (hq _ .zero)
    obtain ⟨h₂, h₂o⟩ := cbvVec_spec Q (fun _ y => u _ (.succ y))
      (fun σ hσ => hg σ (List.mem_cons_of_mem _ hσ)) (fun _ y => hp _ y.succ) fun _ y => hq _ y.succ
    refine ⟨?_, hashOK_bind_iff.2 ⟨h₁o, hashOK_bind_iff.2 ⟨h₂o, hashOK_pure Q _⟩⟩⟩
    rw [cbvVec, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure, h₂,
      CRel.lower_eq (hg τ List.mem_cons_self) h₁]
    funext σ x
    cases x <;> rfl

/-- The program of a reduction returns the readings of `u⃗` and `m` and hashes only messages
satisfying `Q`, under the conditions of `cbvVec_spec` and with `m` in the fragment and its calls'
arguments satisfying `Q`. -/
theorem prog_spec (Q : P.Dom M η → Prop) {τs : List (Ty B)} (u : OVec P [] τs)
    (m : OTerm P [] P.msgTy) (hg : ∀ τ ∈ τs, τ.IsGround) (hmg : P.msgTy.IsGround)
    (hp : ∀ τ x, P.Pptm (u τ x)) (hpm : P.Pptm m)
    (hq : ∀ τ x, ((u τ x).denote (P.guardInterp ρ kv Q) (pairEnv Env.empty)).2)
    (hqm : (m.denote (P.guardInterp ρ kv Q) (pairEnv Env.empty)).2) :
    evalWithAnswerFn (P.answer M η ρ kv) (P.prog M η u m) =
        ((fun τ x => (u τ x).denote (P.ointerp M η ρ kv) Env.empty),
          m.denote (P.ointerp M η ρ kv) Env.empty) ∧
      HashOK (P.answer M η ρ kv) Q (P.prog M η u m) := by
  obtain ⟨h₁, h₁o⟩ := cbvVec_spec Q u hg hp hq
  obtain ⟨h₂, h₂o⟩ := denoteCBV_guard m hpm (e := Env.empty) (Env.liftRel_empty _) hqm
  refine ⟨?_, hashOK_bind_iff.2 ⟨h₁o, hashOK_bind_iff.2 ⟨h₂o, hashOK_pure Q _⟩⟩⟩
  rw [prog, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure, h₁,
    CRel.lower_eq hmg h₂]

end PRFSymbols

end Interop.Squirrel
