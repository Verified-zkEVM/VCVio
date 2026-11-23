/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Derivation

/-!
# Forward secrecy of CCS26's toy ratchet, derived for every fixed trace

The motivating example of CCS26 (§2, Fig. 1–2) is a hash chain: a key `ck` starts at a secret `s`,
each update replaces it by `h(⟨ck, x⟩, k)` for an attacker-chosen `x`, and the attacker may query
the keyed hash and corrupt the key once. CCS26 proves perfect forward secrecy,
`happens(τ) ⇒ safe(τ) ⇒ frame(τ′) ⊬ ck(τ)`, in Squirrel. Here the same statement is derived in the
logic, for every trace given as a Lean value, by a derivation built by Lean recursion on the
trace, and the derivation is sound by `Derivation.sound` (`chainPFS_sound`).

## The execution model (CCS26 Fig. 2)

* **Traces** (`Trace`): a list of steps `A` (an update) and `ROM` (a hash query), optionally
  followed by one `Corrupt`. The history is listed latest step first, so the positions of a trace
  are the suffixes of its history (`List.IsSuffix`), and `Init` is the empty history. A position is
  safe when it is not `Corrupt`.
* **Terms by recursion on the history**, as terms with explicit calls of the keyed hash
  (`OTerm`), so that the PRF rules apply to them; `PRFSymbols.close` turns each call `o_h^k(t)`
  into `h(t, k)`:
  `frame [] = empty_f`, `frame (st :: h) = ⟨frame h, output st h⟩_f`, `input h = att(frame h)`,
  `output A h = empty`, `output ROM h = h(input h, k)`, `ck [] = s`,
  `ck (A :: h) = h(⟨ck h, input h⟩, k)`, `ck (ROM :: h) = ck h`; at `Corrupt`, the key
  `ckC h = h(⟨ck h, input h⟩, k)` is output (`frameC h = ⟨frame h, ckC h⟩_f`).
* **`ck` at `ROM`.** Fig. 2 sets `ck(ROM(i)) = empty`. With that definition `secrecy_base` fails
  at an update after a hash query: the attacker computes `input(τ)` from the oracle and queries
  `⟨empty, input(τ)⟩`, so `ck(τ)` is deducible. Here a hash query leaves the key unchanged, and
  every position before `Corrupt` is safe.

## The declaration

* Base types `msg`, labelled `large`, and `frm`, the type of frames. Names: the key
  `k : bool → (msg → msg)` and the initial key `s : bool → msg`, read at the honest index `idx`.
* Honest symbols: the hash `h : msg → (msg → msg) → msg`, the message pairing `pair` and its first
  projection `fst`, the message `empty`, and for frames `empty_f` and `pair_f : frm → msg → frm`.
* One attacker symbol `att : frm → msg`, applied to the frame, as CCS26's `att`. The logic has no
  product types, so the frame is a nested pair, of its own type.
* **Why a type of frames.** The derivation uses only `fst(⟨x, y⟩) = x` (`FstPair`, a condition
  on models). With a second projection too, pairing would be injective, which no finite carrier
  admits; in every finite model of `FstPair` alone, `⟨x, y⟩` depends only on `x`. Messages must
  be finite in a model where the key is a whole uniform function table (a perfect PRF), so a frame
  that keeps its outputs needs a type of its own. Frames are never hashed, so their type can be
  infinite (`Interop.Squirrel.ChainModel`, in the tests).

## The derivation

* `secrecyBase`, CCS26's `secrecy_base` (`o_h ⊬ ck(τ)`): FreshR at `Init`, and PRF.R at each
  update, whose premise `o_h ⊬ ⟨ck(pred τ), input(τ)⟩` comes from the previous key by WeakR with
  `[⟨ck, input⟩] ▷ ck` (the first projection and `FstPair`). Its `ψ_msg` is over the empty vector.
* `sim`, CCS26's `simulate` (`leakage ▷ frame(τ)`): honest symbols, `att` (Trans with `adv(att)`)
  and the oracle applied to the input (`dedApp`, then `dedRewrite` by β-reduction).
* At `Corrupt`, PRF.L-sec removes `C = ckC` from `leakage = (o_h, C)`. Its `[ψ_msg]` asks every
  call argument of `ck(τ)` and of the corrupted message to differ from the corrupted message. The
  updates' messages differ from it by the **NoCollision hypotheses** `[ck(τ′) ≠ ck(last)]` and the
  first projection; the hash queries' inputs differ from it by Ineq, since `o_h ⊬ m` and
  `o_h ▷ input`, as CCS26 argues (p. 6, "follows from the non-collision lemmas and from the
  secrecy_base lemma"). `Derivation.boxOfMap` combines them.
* `chainPFS`: WeakL with the simulation.

**Hypotheses.** `hyps tr` holds `adv(att)`, which bounds what `att` reads of the attacker tape
(CCS26 Fig. 11's caption asks every declared variable to be a name or adversarial), and, when the
trace corrupts, the NoCollision lemmas that its derivation uses. CCS26 proves them from collision
and pre-image resistance (App. B); those rules are not formalized here, so the derivation takes
the lemmas as hypotheses, as CCS26's proof takes them as lemmas. The model conditions are
`ChainR`, and the PRF assumption is that of each PRF.R and PRF.L-sec instance (`instR`, `instL`).
`Interop.Squirrel.ChainModel` shows that all of them hold jointly in a model with a perfect PRF,
and that the corrupted key is not secret there.

## Scope

The trace is fixed in advance: the attacker's inputs depend on the frame through `att`, but the
schedule of updates, hash queries and the single `Corrupt` is a Lean value, and the induction over
traces is not derived. The conclusion is asymptotic: each rule has a bound at every `η`
(`PRFSymbols.rightAdvantage_le`, `PRFSymbols.leftAdvantage_le`), but `Derivation.sound` gives only
negligibility, and no bound composed along the derivation is stated. The NoCollision lemmas are
hypotheses, not derived from collision resistance.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: §2 (Fig. 1–2, pp. 3–6), Fig. 3, Fig. 4, Fig. 11 and App. B.
-/

public section

namespace Interop.Squirrel.Chain

open IPFunctor IPFunctor.ScopedSignature

/-! ## The declaration -/

/-- The base types: messages and frames. -/
inductive Base where
  /-- Messages, keys and hashes. -/
  | msg
  /-- Frames: the sequences of the protocol's outputs. -/
  | frm

/-- The type of messages. -/
abbrev msg : Ty Base := .base .msg

/-- The type of frames. -/
abbrev frm : Ty Base := .base .frm

/-- The type of keys: functions on messages. -/
abbrev keyT : Ty Base := .arrow msg msg

/-- The key name and the initial key, each indexed by a Boolean. -/
inductive Name : Ty Base → Ty Base → Type where
  /-- The hash key `k`. -/
  | k : Name .bool keyT
  /-- The initial chain key `s`. -/
  | s : Name .bool msg

/-- The honest symbols. -/
inductive Fn : Ty Base → Type where
  /-- The index at which names are read. -/
  | idx : Fn .bool
  /-- The keyed hash `h(m, k)`. -/
  | h : Fn (.arrow msg (.arrow keyT msg))
  /-- The message pairing `⟨x, y⟩`. -/
  | pair : Fn (.arrow msg (.arrow msg msg))
  /-- The first projection. -/
  | fst : Fn (.arrow msg msg)
  /-- The empty message, the output of an update. -/
  | empty : Fn msg
  /-- The empty frame, at `Init`. -/
  | emptyF : Fn frm
  /-- A frame followed by one more output. -/
  | pairF : Fn (.arrow frm (.arrow msg frm))

deriving instance DecidableEq for Base, Name

/-- The attacker symbol. -/
inductive Att where
  /-- `att`, the attacker's input computed from the frame. -/
  | att

/-- Messages are labelled `large`; frames carry no label. -/
@[expose] def labels : Base → Label → Prop
  | .msg, l => l = .large
  | .frm, _ => False

/-- The declaration of the chain. -/
@[expose] def decl : Decl Base where
  labels := labels
  Name := Name
  nameDom_finite := fun n => match n with | .k | .s => nofun
  finite_names := Finite.of_injective (β := Bool)
    (fun n => match n with | ⟨_, _, .k⟩ => false | ⟨_, _, .s⟩ => true)
    fun | ⟨_, _, .k⟩, ⟨_, _, .k⟩, _ => rfl | ⟨_, _, .s⟩, ⟨_, _, .s⟩, _ => rfl
  Fn := Fn
  Att := Att
  attTy _ := .arrow frm msg

/-- The keyed hash `h(·, k)` of the declaration. -/
abbrev P : PRFSymbols decl where
  keyIdx := .bool
  keyTy := keyT
  msgTy := msg
  hTy := msg
  nk := Name.k
  ik := Fn.idx
  hOf := Fn.h

/-! ## Terms -/

/-- The initial key `s(idx)`. -/
@[expose] def sO : OTerm P [] msg := OTerm.name (D := decl) Name.s (OTerm.fn (D := decl) Fn.idx)

/-- The message `empty`. -/
@[expose] def emptyO : OTerm P [] msg := OTerm.fn (D := decl) Fn.empty

/-- The pair `⟨x, y⟩`. -/
@[expose] def pairO (x y : OTerm P [] msg) : OTerm P [] msg :=
  OTerm.app (OTerm.app (OTerm.fn (D := decl) Fn.pair) x) y

/-- The frame `⟨f, x⟩_f`, the frame `f` followed by the output `x`. -/
@[expose] def pairFO (f : OTerm P [] frm) (x : OTerm P [] msg) : OTerm P [] frm :=
  OTerm.app (OTerm.app (OTerm.fn (D := decl) Fn.pairF) f) x

/-- The attacker's input `att(f)`. -/
@[expose] def attO (f : OTerm P [] frm) : OTerm P [] msg :=
  OTerm.app (OTerm.att (D := decl) Att.att) f

/-- The steps of a trace before `Corrupt`. -/
inductive Step where
  /-- An update of the chain key, `A(i)`. -/
  | A
  /-- A query of the keyed hash, `ROM(i)`. -/
  | ROM

/-- The frame after the history `h` (latest step first): `frame(τ) = ⟨frame(pred τ), output(τ)⟩`,
with `output` empty for an update and `h(input(τ), k)` for a hash query, and the empty frame at
`Init` (CCS26 Fig. 2). -/
@[expose] def frame : List Step → OTerm P [] frm
  | [] => OTerm.fn (D := decl) Fn.emptyF
  | .A :: h => pairFO (frame h) emptyO
  | .ROM :: h => pairFO (frame h) (OTerm.call (attO (frame h)))

/-- The attacker's input at the step after the history `h`: `input(τ) = att(frame(pred τ))`. -/
@[expose] def input (h : List Step) : OTerm P [] msg := attO (frame h)

/-- The chain key after the history `h`: `s` at `Init`, `h(⟨ck(pred τ), input(τ)⟩, k)` after an
update, and unchanged by a hash query. -/
@[expose] def ck : List Step → OTerm P [] msg
  | [] => sO
  | .A :: h => OTerm.call (pairO (ck h) (input h))
  | .ROM :: h => ck h

/-- The message hashed by the update or the corruption after the history `h`:
`⟨ck(pred τ), input(τ)⟩`. -/
@[expose] def msgA (h : List Step) : OTerm P [] msg := pairO (ck h) (input h)

/-- The key output at `Corrupt` after the history `h`: `ck(Corrupt) = h(⟨ck(pred τ), input⟩, k)`. -/
@[expose] def ckC (h : List Step) : OTerm P [] msg := OTerm.call (msgA h)

/-- The frame at `Corrupt` after the history `h`: the previous frame followed by the key. -/
@[expose] def frameC (h : List Step) : OTerm P [] frm := pairFO (frame h) (ckC h)

/-- A trace: its steps before `Corrupt`, latest first, and whether it ends with `Corrupt`. -/
structure Trace where
  /-- The steps before `Corrupt`, latest first. -/
  hist : List Step
  /-- Whether the trace ends with `Corrupt`. -/
  corrupt : Bool

/-- The frame at the last position of a trace. -/
@[expose] def Trace.frame : Trace → OTerm P [] frm
  | ⟨h, false⟩ => Chain.frame h
  | ⟨h, true⟩ => frameC h

/-! ## The closed-up terms -/

/-- The pair of two terms of the logic. -/
@[expose] def pairT (x y : FTerm decl [] msg) : FTerm decl [] msg :=
  FTerm.app (FTerm.app (FTerm.fn (D := decl) Fn.pair) x) y

/-- The frame pair of two terms of the logic. -/
@[expose] def pairFT (f : FTerm decl [] frm) (x : FTerm decl [] msg) : FTerm decl [] frm :=
  FTerm.app (FTerm.app (FTerm.fn (D := decl) Fn.pairF) f) x

/-- `att(f)` as a term of the logic. -/
@[expose] def attT (f : FTerm decl [] frm) : FTerm decl [] msg :=
  FTerm.app (FTerm.att (D := decl) Att.att) f

theorem close_sO :
    P.close sO = FTerm.name (D := decl) Name.s (FTerm.fn (D := decl) Fn.idx) :=
  (PRFSymbols.close_name _ _).trans (congrArg _ (PRFSymbols.close_fn _))

theorem close_emptyO : P.close emptyO = FTerm.fn (D := decl) Fn.empty :=
  PRFSymbols.close_fn _

theorem close_emptyF :
    P.close (OTerm.fn (P := P) (Γ := []) (D := decl) Fn.emptyF) = FTerm.fn (D := decl) Fn.emptyF :=
  PRFSymbols.close_fn _

theorem close_pairO (x y : OTerm P [] msg) :
    P.close (pairO x y) = pairT (P.close x) (P.close y) :=
  (PRFSymbols.close_app _ _).trans (congrArg (FTerm.app · _)
    ((PRFSymbols.close_app _ _).trans (congrArg (FTerm.app · _) (PRFSymbols.close_fn _))))

theorem close_pairFO (f : OTerm P [] frm) (x : OTerm P [] msg) :
    P.close (pairFO f x) = pairFT (P.close f) (P.close x) :=
  (PRFSymbols.close_app _ _).trans (congrArg (FTerm.app · _)
    ((PRFSymbols.close_app _ _).trans (congrArg (FTerm.app · _) (PRFSymbols.close_fn _))))

theorem close_attO (f : OTerm P [] frm) : P.close (attO f) = attT (P.close f) :=
  (PRFSymbols.close_app _ _).trans
    (congrArg (FTerm.app · _) (congrArg (IFreeM.liftBind _) (funext fun p => p.elim0)))

/-! ## Hypotheses, model conditions and the PRF instances -/

/-- `adv(att)`: an admitted machine computes the attacker symbol (CCS26 Fig. 11's caption). -/
@[expose] def advAtt : Form decl [] :=
  .adv (τs := [frm]) (β := msg) (FTerm.att (D := decl) Att.att)

/-- The histories `h'` such that `A :: h'` is a suffix of `h`: the positions just before the
updates of `h`. -/
@[expose] def aSteps : List Step → List (List Step)
  | [] => []
  | .A :: h => h :: aSteps h
  | .ROM :: h => aSteps h

/-- The histories `h'` such that `ROM :: h'` is a suffix of `h`: the positions just before the
hash queries of `h`. -/
@[expose] def romSteps : List Step → List (List Step)
  | [] => []
  | .A :: h => romSteps h
  | .ROM :: h => h :: romSteps h

/-- The NoCollision lemma `ck(h') ≠ ck(h)` (CCS26 §2.3, p. 5), as a local formula. -/
@[expose] def noCollision (h' h : List Step) : FTerm decl [] .bool :=
  FTerm.not (FTerm.eq (P.close (ck h')) (P.close (ck h)))

/-- The hypotheses of the derivation for a trace: `adv(att)`, and, when the trace corrupts after
the history `h`, the NoCollision lemmas `[ck(h') ≠ ck(h)]` for the positions `h'` just before the
updates of `h`. -/
@[expose] def hyps : Trace → List (Form decl [])
  | ⟨_, false⟩ => [advAtt]
  | ⟨h, true⟩ => advAtt :: (aSteps h).map fun h' => .box (noCollision h' h)

/-- `fst(⟨x, y⟩) = x`: the equation of the first projection, a condition on models. -/
@[expose] def FstPair (M : Model decl) : Prop :=
  ∀ η x y, M.fn η (Fn.fst : decl.Fn _) (M.fn η (Fn.pair : decl.Fn _) x y) = x

/-- The models over which the derivations are sound: uniform names of messages, long attacker
tapes and polynomial bit blocks for messages (the model conditions of PRF.R and PRF.L-sec), and
the equation of the first projection. -/
abbrev ChainR (M : Model decl) : Prop :=
  M.UniformSampler msg ∧ M.LongTapes ∧ M.PolyCoins msg ∧ FstPair M

/-- PRF.R at the update after the history `h`: from `o_h^k ⊬ ⟨ck h, input h⟩`, conclude
`o_h^k ⊬ ck(A :: h)`. -/
@[expose] def instR (h : List Step) : PRFRInstance decl :=
  ⟨P, [], Env.empty, msgA h, trivial, trivial, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- PRF.L-sec at the corruption after the history `h`, for the secret `ck(hτ)`: from
`o_h^k ⊬ ck(hτ)` and `o_h^k ⊬ ⟨ck h, input h⟩`, conclude `o_h^k, ckC h ⊬ ck(hτ)`. -/
@[expose] def instL (h hτ : List Step) : PRFLInstance decl :=
  ⟨P, [], msg, Env.empty, ck hτ, msgA h, trivial, trivial, of_decide_eq_true rfl,
    of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The PRF instances that the derivations use. -/
@[expose] def ChainPRF (e : PRFRule decl) : Prop :=
  (∃ h, e = .right (instR h)) ∨ ∃ h hτ, e = .left (instL h hτ)

/-- The leakage without the corrupted key: the oracle `o_h^k = λx. h(x, k)` (CCS26 §2.3). -/
abbrev leak : Vec decl [] ([] ++ [Ty.arrow msg msg]) :=
  Vec.snoc (P.closeVec (Env.empty : OVec P [] [])) P.hashOracle

/-- The leakage with the corrupted key after the history `h`: `(o_h^k, C)` with `C = ckC h`. -/
abbrev leakC (h : List Step) : Vec decl [] (([] ++ [Ty.arrow msg msg]) ++ [msg]) :=
  Vec.snoc leak (P.close (ckC h))

/-! ## Side conditions

The side conditions of PRF.R and PRF.L-sec are conditions on the heads of a term. Every head of a
chain term lies in every set that contains the constructors the chain uses (`ChainOps`), so one
induction on the history gives `ψ_key`, `⊢pptm` and first order for every chain term. -/

/-- A set of heads that contains the constructors the chain's terms use. -/
private structure ChainOps (H : Set P.oSig.Head) : Prop where
  app : ∀ a b, (⟨_, .inl (.app a b)⟩ : P.oSig.Head) ∈ H
  call : (⟨_, .inr .call⟩ : P.oSig.Head) ∈ H
  name_s : (⟨_, .inl (.name (D := decl) Name.s)⟩ : P.oSig.Head) ∈ H
  idx : (⟨_, .inl (.fn (D := decl) Fn.idx)⟩ : P.oSig.Head) ∈ H
  pair : (⟨_, .inl (.fn (D := decl) Fn.pair)⟩ : P.oSig.Head) ∈ H
  empty : (⟨_, .inl (.fn (D := decl) Fn.empty)⟩ : P.oSig.Head) ∈ H
  emptyF : (⟨_, .inl (.fn (D := decl) Fn.emptyF)⟩ : P.oSig.Head) ∈ H
  pairF : (⟨_, .inl (.fn (D := decl) Fn.pairF)⟩ : P.oSig.Head) ∈ H
  att : (⟨_, .inl (.att (D := decl) Att.att)⟩ : P.oSig.Head) ∈ H

private theorem ChainOps.heads_app {H : Set P.oSig.Head} (hH : ChainOps H) {a b : Ty Base}
    {f : OTerm P [] (.arrow a b)} {x : OTerm P [] a} (hf : f.heads ⊆ H) (hx : x.heads ⊆ H) :
    (OTerm.app f x).heads ⊆ H :=
  Set.insert_subset_iff.2 ⟨hH.app a b, Set.iUnion_subset fun p => Fin.cases hf (fun _ => hx) p⟩

private theorem heads_fn {H : Set P.oSig.Head} {τ : Ty Base} {f : decl.Fn τ}
    (hf : (⟨_, .inl (.fn f)⟩ : P.oSig.Head) ∈ H) : (OTerm.fn (P := P) (Γ := []) f).heads ⊆ H :=
  Set.insert_subset_iff.2 ⟨hf, Set.iUnion_subset fun p => p.elim0⟩

private theorem ChainOps.heads_attO {H : Set P.oSig.Head} (hH : ChainOps H)
    {f : OTerm P [] frm} (hf : f.heads ⊆ H) : (attO f).heads ⊆ H :=
  hH.heads_app (Set.insert_subset_iff.2 ⟨hH.att, Set.iUnion_subset fun p => p.elim0⟩) hf

private theorem ChainOps.heads_pairO {H : Set P.oSig.Head} (hH : ChainOps H)
    {x y : OTerm P [] msg} (hx : x.heads ⊆ H) (hy : y.heads ⊆ H) : (pairO x y).heads ⊆ H :=
  hH.heads_app (hH.heads_app (heads_fn hH.pair) hx) hy

private theorem ChainOps.heads_call {H : Set P.oSig.Head} (hH : ChainOps H)
    {t : OTerm P [] msg} (ht : t.heads ⊆ H) : (OTerm.call t).heads ⊆ H :=
  Set.insert_subset_iff.2 ⟨hH.call, Set.iUnion_subset fun _ => ht⟩

private theorem ChainOps.heads_frame {H : Set P.oSig.Head} (hH : ChainOps H) :
    ∀ h : List Step, (frame h).heads ⊆ H
  | [] => heads_fn hH.emptyF
  | .A :: h => hH.heads_app (hH.heads_app (heads_fn hH.pairF) (hH.heads_frame h))
      (heads_fn hH.empty)
  | .ROM :: h => hH.heads_app (hH.heads_app (heads_fn hH.pairF) (hH.heads_frame h))
      (hH.heads_call (hH.heads_attO (hH.heads_frame h)))

private theorem ChainOps.heads_ck {H : Set P.oSig.Head} (hH : ChainOps H) :
    ∀ h : List Step, (ck h).heads ⊆ H
  | [] => hH.heads_app (Set.insert_subset_iff.2 ⟨hH.name_s, Set.iUnion_subset fun p => p.elim0⟩)
      (heads_fn hH.idx)
  | .A :: h => hH.heads_call (hH.heads_pairO (hH.heads_ck h) (hH.heads_attO (hH.heads_frame h)))
  | .ROM :: h => hH.heads_ck h

private theorem ChainOps.heads_msgA {H : Set P.oSig.Head} (hH : ChainOps H) (h : List Step) :
    (msgA h).heads ⊆ H :=
  hH.heads_pairO (hH.heads_ck h) (hH.heads_attO (hH.heads_frame h))

private theorem chainOps_keyFree : ChainOps {h | P.KeyFreeAt h} :=
  ⟨fun _ _ => trivial, trivial, (fun h => by cases h), trivial, trivial, trivial, trivial, trivial,
    trivial⟩

private theorem chainOps_pptm : ChainOps {h | P.PptmAt h} :=
  ⟨fun _ _ => trivial, ⟨trivial, trivial⟩, ⟨trivial, by decide⟩, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

private theorem chainOps_firstOrder : ChainOps {h | P.FirstOrderAt h} :=
  ⟨fun _ _ => trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- The syntactic side conditions of PRF.R at every update: `msg` is `large`, and the message
meets `ψ_key`, `⊢pptm` and first order. -/
theorem instR_syntactic (h : List Step) : (instR h).Syntactic :=
  ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun _ x => (nomatch x),
    chainOps_keyFree.heads_msgA h, fun _ x => (nomatch x), chainOps_pptm.heads_msgA h,
    fun _ x => (nomatch x), chainOps_firstOrder.heads_msgA h⟩

/-- The syntactic side conditions of PRF.L-sec at every corruption and secret. -/
theorem instL_syntactic (h hτ : List Step) : (instL h hτ).Syntactic :=
  ⟨fun _ h => absurd h List.not_mem_nil, trivial, fun _ x => (nomatch x),
    chainOps_keyFree.heads_ck hτ, chainOps_keyFree.heads_msgA h, fun _ x => (nomatch x),
    chainOps_pptm.heads_ck hτ, chainOps_pptm.heads_msgA h, fun _ x => (nomatch x),
    chainOps_firstOrder.heads_ck hτ, chainOps_firstOrder.heads_msgA h⟩

/-! ## The call arguments of the chain's terms -/

private theorem calls_frame_ROM (h : List Step) :
    P.calls (frame (.ROM :: h)) = P.calls (frame h) ++ (input h :: P.calls (frame h)) :=
  congrArg (P.calls (frame h) ++ ·) (PRFSymbols.calls_call _)

private theorem calls_ck_A (h : List Step) :
    P.calls (ck (.A :: h)) = msgA h :: (P.calls (ck h) ++ P.calls (frame h)) :=
  PRFSymbols.calls_call _

/-- The call arguments of a frame are the inputs of its hash queries. -/
private theorem mem_calls_frame {t : OTerm P [] msg} :
    ∀ {h : List Step}, t ∈ P.calls (frame h) → ∃ h' ∈ romSteps h, t = input h'
  | [], ht => absurd ht List.not_mem_nil
  | .A :: h, ht => by
    have ht' : t ∈ P.calls (frame h) ++ [] := ht
    rw [List.append_nil] at ht'
    exact mem_calls_frame (h := h) ht'
  | .ROM :: h, ht => by
    rw [calls_frame_ROM, List.mem_append, List.mem_cons] at ht
    rcases ht with ht | rfl | ht
    · obtain ⟨h', hh', rfl⟩ := mem_calls_frame ht
      exact ⟨h', List.mem_cons_of_mem _ hh', rfl⟩
    · exact ⟨h, List.mem_cons_self, rfl⟩
    · obtain ⟨h', hh', rfl⟩ := mem_calls_frame ht
      exact ⟨h', List.mem_cons_of_mem _ hh', rfl⟩

/-- The call arguments of a chain key are the messages of its updates and the inputs of its hash
queries. -/
private theorem mem_calls_ck {t : OTerm P [] msg} :
    ∀ {h : List Step}, t ∈ P.calls (ck h) →
      (∃ h' ∈ aSteps h, t = msgA h') ∨ ∃ h' ∈ romSteps h, t = input h'
  | [], ht => absurd ht List.not_mem_nil
  | .A :: h, ht => by
    rw [calls_ck_A, List.mem_cons, List.mem_append] at ht
    rcases ht with rfl | ht | ht
    · exact .inl ⟨h, List.mem_cons_self, rfl⟩
    · rcases mem_calls_ck ht with ⟨h', hh', rfl⟩ | ⟨h', hh', rfl⟩
      · exact .inl ⟨h', List.mem_cons_of_mem _ hh', rfl⟩
      · exact .inr ⟨h', hh', rfl⟩
    · exact .inr (mem_calls_frame (h := h) ht)
  | .ROM :: h, ht => by
    rcases mem_calls_ck (h := h) ht with ⟨h', hh', rfl⟩ | ⟨h', hh', rfl⟩
    · exact .inl ⟨h', hh', rfl⟩
    · exact .inr ⟨h', List.mem_cons_of_mem _ hh', rfl⟩

private theorem aSteps_subset {h₁ : List Step} :
    ∀ {h₂ : List Step}, h₁ <:+ h₂ → aSteps h₁ ⊆ aSteps h₂
  | [], hs => by rw [List.suffix_nil.1 hs]
  | st :: h₂, hs => by
    rcases List.suffix_cons_iff.1 hs with rfl | hs
    · exact List.Subset.refl _
    · intro x hx
      have hx' := aSteps_subset hs hx
      cases st
      · exact List.mem_cons_of_mem _ hx'
      · exact hx'

private theorem romSteps_subset {h₁ : List Step} : ∀ {h₂ : List Step}, h₁ <:+ h₂ →
    romSteps h₁ ⊆ romSteps h₂
  | [], hs => by rw [List.suffix_nil.1 hs]
  | st :: h₂, hs => by
    rcases List.suffix_cons_iff.1 hs with rfl | hs
    · exact List.Subset.refl _
    · intro x hx
      have hx' := romSteps_subset hs hx
      cases st
      · exact hx'
      · exact List.mem_cons_of_mem _ hx'

/-- The call arguments that PRF.L-sec's `ψ_msg` ranges over, at the corruption after `h` with the
secret `ck(hτ)`: the messages of the updates of `h` and the inputs of its hash queries. -/
private theorem mem_calls_psiL {hτ h : List Step} (hs : hτ <:+ h) {t : OTerm P [] msg}
    (ht : t ∈ P.vecCalls (Env.append (Env.empty : OVec P [] []) (Env.cons (ck hτ) Env.empty)) ++
      P.calls (msgA h)) :
    (∃ h' ∈ aSteps h, t = msgA h') ∨ ∃ h' ∈ romSteps h, t = input h' := by
  change t ∈ P.vecCalls (Env.cons (ck hτ) Env.empty : OVec P [] [msg]) ++
    (P.calls (ck h) ++ P.calls (frame h)) at ht
  simp only [PRFSymbols.vecCalls_cons, PRFSymbols.vecCalls_nil, List.append_nil,
    List.mem_append] at ht
  rcases ht with ht | ht | ht
  · rcases mem_calls_ck ht with ⟨h', hh', rfl⟩ | ⟨h', hh', rfl⟩
    · exact .inl ⟨h', aSteps_subset hs hh', rfl⟩
    · exact .inr ⟨h', romSteps_subset hs hh', rfl⟩
  · exact mem_calls_ck ht
  · exact .inr (mem_calls_frame ht)

/-! ## Read bounds -/

private theorem readsPoly_hashTerm {M : Model decl} {C : AdvClass M}
    {env : Env (Kind.Value M) []} {x : FTerm decl [] msg} (hx : x.ReadsPoly M C env) :
    (P.hashTerm x).ReadsPoly M C env :=
  ((FTerm.readsPoly_fn _).app hx).app (FTerm.ReadsPoly.name _ (FTerm.readsPoly_fn _))

section Reads

variable {M : Model decl} {C : AdvClass M} {env : Env (Kind.Value M) []}
  (hatt : (FTerm.att (D := decl) Att.att : FTerm decl [] (.arrow frm msg)).ReadsPoly M C env)
include hatt

private theorem readsPoly_frame : ∀ h : List Step, FTerm.ReadsPoly M C (P.close (frame h)) env
  | [] => close_emptyF ▸ FTerm.readsPoly_fn _
  | .A :: h => by
    rw [frame, close_pairFO, close_emptyO]
    exact ((FTerm.readsPoly_fn _).app (readsPoly_frame h)).app (FTerm.readsPoly_fn _)
  | .ROM :: h => by
    rw [frame, close_pairFO, PRFSymbols.close_call, close_attO]
    exact ((FTerm.readsPoly_fn _).app (readsPoly_frame h)).app
      (readsPoly_hashTerm (hatt.app (readsPoly_frame h)))

private theorem readsPoly_ck : ∀ h : List Step, FTerm.ReadsPoly M C (P.close (ck h)) env
  | [] => close_sO ▸ FTerm.ReadsPoly.name _ (FTerm.readsPoly_fn _)
  | .A :: h => by
    rw [ck, PRFSymbols.close_call, close_pairO, input, close_attO]
    exact readsPoly_hashTerm (((FTerm.readsPoly_fn _).app (readsPoly_ck h)).app
      (hatt.app (readsPoly_frame hatt h)))
  | .ROM :: h => readsPoly_ck h

private theorem readsPoly_msgA (h : List Step) : FTerm.ReadsPoly M C (P.close (msgA h)) env := by
  rw [msgA, close_pairO, input, close_attO]
  exact ((FTerm.readsPoly_fn _).app (readsPoly_ck hatt h)).app
    (hatt.app (readsPoly_frame hatt h))

end Reads

/-- In every model of the hypotheses, `att` reads the attacker tape below a polynomial, since
`adv(att)` holds. -/
private theorem readsPoly_att {Θ : List (Form decl [])} (hadv : advAtt ∈ Θ) {M : Model decl}
    {C : AdvClass M} {env : Env (Kind.Value M) []} (hΘ : ∀ θ ∈ Θ, θ.Holds M C env) :
    (FTerm.att (D := decl) Att.att : FTerm decl [] (.arrow frm msg)).ReadsPoly M C env :=
  FTerm.readsPoly_of_adv (Form.holds_adv.1 (hΘ _ hadv))

/-- The oracle reads only the key's coordinate of the honest tape, not that of `s(idx)`. -/
private theorem leak_avoids : leak.AvoidsNames (· = ⟨_, _, (Name.s : decl.Name _ _)⟩) :=
  letI : DecidableEq ((a : Ty Base) × (b : Ty Base) × decl.Name a b) :=
    inferInstanceAs (DecidableEq ((a : Ty Base) × (b : Ty Base) × Name a b))
  by decide

/-! ## The derivation -/

/-- Derivations of the chain: no encryption rule, the PRF instances `ChainPRF`, over the models of
`ChainR`. -/
abbrev Der (Θ : List (Form decl [])) (F : Form decl []) : Type :=
  Derivation decl (fun _ => False) ChainPRF ChainR Θ F

/-- A derivation, cast along an equality of its conclusions. -/
def dcast {Θ : List (Form decl [])} {F F' : Form decl []} (e : F = F') (d : Der Θ F) :
    Der Θ F' :=
  e ▸ d

theorem order_leak : Ty.SecrecyOrder ([] ++ [Ty.arrow msg msg]) msg := by decide

theorem order_frame : Ty.SecrecyOrder [frm] msg := by decide

theorem order_leakC : Ty.IndistOrder (([] ++ [Ty.arrow msg msg]) ++ [msg]) := by decide

theorem denote_pairT {M : Model decl} {C : AdvClass M} {x y : FTerm decl [] msg}
    {env : Env (Kind.Value M) []} {η : ℕ} {ρ : M.Tape η} :
    (pairT x y).denote (fullInterp M C) env η ρ =
      M.fn η (Fn.pair : decl.Fn _) (x.denote (fullInterp M C) env η ρ)
        (y.denote (fullInterp M C) env η ρ) :=
  rfl

/-- `[⟨ck h, input h⟩] ▷ ck h`: the first projection, then `fst(⟨x, y⟩) = x` (`FstPair`). -/
def dedFst {Θ : List (Form decl [])} (h : List Step) :
    Der Θ (.ded (Env.cons (P.close (msgA h)) Env.empty) (P.close (ck h)) (by decide)) :=
  .dedRewrite (.dedApp (by decide) (.dedFn _ (Fn.fst : decl.Fn _) (by decide))
      (.dedInput _ .zero (by decide)))
    (.boxValid _ fun M _ hR C env η ρ => by
      rw [FTerm.denote_eq]
      refine @decide_eq_true _ (Classical.propDecidable _) ?_
      change M.fn η (Fn.fst : decl.Fn _) ((P.close (pairO (ck h) (input h))).denote
        (fullInterp M C) env η ρ) = _
      rw [close_pairO, denote_pairT]
      exact hR.2.2.2 η _ _)

/-- `o_h^k ⊬ ⟨ck h, input h⟩` from `o_h^k ⊬ ck h`, by WeakR with `dedFst`: the premise of PRF.R at
the update after `h`, and PRF.L-sec's `C_sec` at the corruption after `h`. -/
def secMsg {Θ : List (Form decl [])} (h : List Step)
    (d : Der Θ (.nonDed leak (P.close (ck h)) order_leak)) :
    Der Θ (.nonDed leak (P.close (msgA h)) order_leak) :=
  .nonDedWeakR d (dedFst h)

/-- The facts from which PRF.L-sec's `ψ_msg` follows at the corruption after `h`: the NoCollision
lemma `ck(h') ≠ ck(h)` for each update of `h` (`inl`), and `⟨ck h, input h⟩ ≠ input(h')` for each
hash query of `h` (`inr`). -/
private def psiFact (h : List Step) : List Step ⊕ List Step → FTerm decl [] .bool
  | .inl h' => noCollision h' h
  | .inr h' => FTerm.not (FTerm.eq (P.close (msgA h)) (P.close (input h')))

/-- The updates and the hash queries of `h`, indexing `psiFact h`. -/
private def psiFacts (h : List Step) : List (List Step ⊕ List Step) :=
  (aSteps h).map .inl ++ (romSteps h).map .inr

/-- **`ψ_msg` of PRF.L-sec from the facts**, at a tape where they hold, in a model of `FstPair`:
every call argument of `ck(hτ)` and of `⟨ck h, input h⟩` is the message of an update of `h`, whose
first component differs from `ck h` by NoCollision, or the input of a hash query of `h`. -/
private theorem psiL_of_facts {hτ h : List Step} (hs : hτ <:+ h) {M : Model decl}
    (hM : FstPair M) (C : AdvClass M) (env : Env (Kind.Value M) []) {η : ℕ} (ρ : M.Tape η)
    (hall : ∀ a ∈ psiFacts h, (psiFact h a).denote (fullInterp M C) env η ρ = true) :
    ((instL h hτ).P.psiMsg (Env.append (instL h hτ).u (Env.cons (instL h hτ).v Env.empty))
      (instL h hτ).m).denote (fullInterp M C) env η ρ = true := by
  refine (P.psiMsg_eq_true_iff C _ _ env ρ).2 fun t ht heq' => ?_
  have heq : (P.close t).denote (fullInterp M C) env η ρ =
      (P.close (msgA h)).denote (fullInterp M C) env η ρ := by
    rw [P.denote_close_apply C t env ρ, P.denote_close_apply C (msgA h) env ρ]
    exact heq'
  rcases mem_calls_psiL hs ht with ⟨h', hh', rfl⟩ | ⟨h', hh', rfl⟩
  · refine FTerm.denote_not_eq_eq_true.1
      (hall (.inl h') (List.mem_append_left _ (List.mem_map_of_mem hh'))) ?_
    rw [msgA, msgA, close_pairO, close_pairO, denote_pairT, denote_pairT] at heq
    have h₁ := congrArg (M.fn η (Fn.fst : decl.Fn _)) heq
    rwa [hM, hM] at h₁
  · exact FTerm.denote_not_eq_eq_true.1
      (hall (.inr h') (List.mem_append_right _ (List.mem_map_of_mem hh'))) heq.symm

section Derivations

variable {Θ : List (Form decl [])} (hadv : advAtt ∈ Θ)
include hadv

/-- The read bounds of PRF.R at the update after `h`, from `adv(att)`. -/
private theorem readsR (h : List Step) :
    ∀ M : Model decl, M.RespectsLabels → ChainR M → ∀ (C : AdvClass M) env,
      (∀ θ ∈ Θ, θ.Holds M C env) →
        Vec.ReadsPoly M C ((instR h).P.closeVec (instR h).u) env ∧
          FTerm.ReadsPoly M C ((instR h).P.close (instR h).m) env :=
  fun _ _ _ _ _ hΘ => ⟨fun _ x => (nomatch x), readsPoly_msgA (readsPoly_att hadv hΘ) h⟩

/-- **secrecy_base** (CCS26 §2.3, p. 5): `o_h^k ⊬ ck(h)` at every position, by FreshR at `Init`
and PRF.R (rule (1) of §2.3) at each update; a hash query leaves the key unchanged. -/
def secrecyBase : (h : List Step) → Der Θ (.nonDed leak (P.close (ck h)) order_leak)
  | [] => dcast (congrArg (Form.nonDed leak · order_leak) close_sO.symm)
      (.nonDedFreshR leak (Name.s : decl.Name _ _) (Fn.idx : decl.Fn _) order_leak rfl
        leak_avoids)
  | .A :: h => .nonDedPRFR (instR h) (.inl ⟨h, rfl⟩) (instR_syntactic h)
      (fun _ hM => ⟨hM.1, hM.2.1, hM.2.2.1⟩) (readsR hadv h)
      (.boxValid _ fun _ _ _ C env _ ρ => (P.psiMsgVec_eq_true_iff C _ _ env ρ).2
        fun _ ht => absurd ht List.not_mem_nil)
      (secMsg h (secrecyBase h))
  | .ROM :: h => secrecyBase h

/-- `u⃗ ▷ input(h)`, from `u⃗ ▷ frame(h)` by Trans with `adv(att)`. -/
def simInput {τs : List (Ty Base)} {u : Vec decl [] τs} {ho : Ty.IndistOrder τs}
    (h : List Step) (d : Der Θ (.ded u (P.close (frame h)) ⟨ho, Nat.zero_le 1⟩)) :
    Der Θ (.ded u (P.close (input h)) ⟨ho, Nat.zero_le 1⟩) :=
  dcast (congrArg (Form.ded u · _) (close_attO (frame h)).symm)
    (.dedTrans d (.dedApps (u := Env.cons (P.close (frame h)) Env.empty)
      (f := FTerm.att (D := decl) Att.att) (by decide) (.ax hadv)))

/-- **simulate** (CCS26 §2.3, p. 5): `u⃗ ▷ frame(h)` before `Corrupt`, for a vector whose entry `y`
is the oracle `o_h^k`. The frame is built from `empty_f`, `pair_f` and `empty`, and the output of a
hash query is the oracle applied to the input, which is `h(input, k)` by β-reduction. -/
def sim {τs : List (Ty Base)} (u : Vec decl [] τs) (y : ScopedVar τs (.arrow msg msg))
    (hy : u _ y = P.hashOracle) (ho : Ty.IndistOrder τs) :
    (h : List Step) → Der Θ (.ded u (P.close (frame h)) ⟨ho, Nat.zero_le 1⟩)
  | [] => dcast (congrArg (Form.ded u · _) close_emptyF.symm)
      (.dedFn u (Fn.emptyF : decl.Fn _) _)
  | .A :: h => dcast (congrArg (Form.ded u · _) (close_pairFO (frame h) emptyO).symm)
      (.dedApp _ (.dedApp ⟨ho, by decide⟩ (.dedFn u (Fn.pairF : decl.Fn _) ⟨ho, by decide⟩)
          (sim u y hy ho h))
        (dcast (congrArg (Form.ded u · _) close_emptyO.symm)
          (.dedFn u (Fn.empty : decl.Fn _) ⟨ho, Nat.zero_le 1⟩)))
  | .ROM :: h => dcast (congrArg (Form.ded u · _)
        (close_pairFO (frame h) (OTerm.call (attO (frame h)))).symm)
      (.dedApp _ (.dedApp ⟨ho, by decide⟩ (.dedFn u (Fn.pairF : decl.Fn _) ⟨ho, by decide⟩)
          (sim u y hy ho h))
        (.dedRewrite (.dedApp (hot := (⟨ho, Nat.zero_le 1⟩ : Ty.SecrecyOrder τs msg))
            (⟨ho, Nat.zero_le 1⟩ : Ty.SecrecyOrder τs msg)
            (dcast (congrArg (Form.ded u · ⟨ho, by decide⟩) hy) (.dedInput u y ⟨ho, by decide⟩))
            (simInput hadv (ho := ho) h (sim u y hy ho h)))
          (.boxValid _ fun M _ _ C env η ρ => by
            rw [FTerm.denote_eq]
            refine @decide_eq_true _ (Classical.propDecidable _) ?_
            simp only [FTerm.denote_app, PRFSymbols.denote_hashOracle]
            rfl)))

/-- **PFS at a position before `Corrupt`**: `frame(h') ⊬ ck(hτ)`, by WeakL from secrecy_base and
the simulation of the frame from the oracle. -/
def pfsFrame (hτ h' : List Step) :
    Der Θ (.nonDed (Env.cons (P.close (frame h')) Env.empty) (P.close (ck hτ)) order_frame) :=
  .nonDedWeakL (secrecyBase hadv hτ) (sim hadv leak .zero rfl order_leak.1 h')

/-- The read bounds of PRF.L-sec at the corruption after `h`, from `adv(att)`. -/
private theorem readsL (h hτ : List Step) :
    ∀ M : Model decl, M.RespectsLabels → ChainR M → ∀ (C : AdvClass M) env,
      (∀ θ ∈ Θ, θ.Holds M C env) →
        Vec.ReadsPoly M C ((instL h hτ).P.closeVec (instL h hτ).u) env ∧
          FTerm.ReadsPoly M C ((instL h hτ).P.close (instL h hτ).v) env ∧
            FTerm.ReadsPoly M C ((instL h hτ).P.close (instL h hτ).m) env :=
  fun _ _ _ _ _ hΘ => ⟨fun _ x => (nomatch x), readsPoly_ck (readsPoly_att hadv hΘ) hτ,
    readsPoly_msgA (readsPoly_att hadv hΘ) h⟩

/-- PRF.L-sec's `[ψ_msg]` at the corruption after `h`: the NoCollision lemmas from the
hypotheses, the inequalities with the hash queries' inputs by Ineq from `C_sec` and the
simulation, combined by `Derivation.boxOfMap` with `psiL_of_facts`. -/
def psiL {h hτ : List Step} (hs : hτ <:+ h)
    (hnc : ∀ h' ∈ aSteps h, Form.box (noCollision h' h) ∈ Θ) :
    Der Θ (.box ((instL h hτ).P.psiMsg (Env.append (instL h hτ).u (Env.cons (instL h hτ).v
      Env.empty)) (instL h hτ).m)) :=
  Derivation.boxOfMap (psiFact h) (psiFacts h)
    (fun a ha => match a, ha with
      | .inl h', ha => .ax (hnc h' (by simpa [psiFacts] using ha))
      | .inr h', _ => .boxNotEq (secMsg h (secrecyBase hadv h))
          (simInput hadv (ho := order_leak.1) h' (sim hadv leak .zero rfl order_leak.1 h')))
    fun _ _ hR C env _ ρ hall => psiL_of_facts hs hR.2.2.2 C env ρ hall

/-- **PFS at `Corrupt`**: `frameC(h) ⊬ ck(hτ)` for a safe `hτ`. PRF.L-sec removes the corrupted
key from the leakage `(o_h^k, C)`, from secrecy_base at `hτ`, `C_sec` (secrecy_base at `h` and
WeakR) and `[ψ_msg]`; WeakL with the simulation of the frame from `(o_h^k, C)` concludes. -/
def pfsCorrupt {h hτ : List Step} (hs : hτ <:+ h)
    (hnc : ∀ h' ∈ aSteps h, Form.box (noCollision h' h) ∈ Θ) :
    Der Θ (.nonDed (Env.cons (P.close (frameC h)) Env.empty) (P.close (ck hτ)) order_frame) :=
  .nonDedWeakL
    (.nonDedPRFLSec (instL h hτ) (.inr ⟨h, hτ, rfl⟩) (instL_syntactic h hτ)
      (fun _ hM => ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.1⟩) (readsL hadv h hτ) (psiL hadv hs hnc)
      (secrecyBase hadv hτ) (secMsg h (secrecyBase hadv h)))
    (dcast (congrArg
        (Form.ded (leakC h) · (⟨order_leakC, Nat.zero_le 1⟩ : Ty.SecrecyOrder _ frm))
        (close_pairFO (frame h) (ckC h)).symm)
      (.dedApp (⟨order_leakC, Nat.zero_le 1⟩ : Ty.SecrecyOrder _ frm)
        (.dedApp ⟨order_leakC, by decide⟩
          (.dedFn (leakC h) (Fn.pairF : decl.Fn _) ⟨order_leakC, by decide⟩)
          (sim hadv (leakC h) .zero rfl order_leakC h))
        (.dedInput (leakC h) (.succ .zero)
          (⟨order_leakC, Nat.zero_le 1⟩ : Ty.SecrecyOrder _ msg))))

end Derivations

/-! ## The headline -/

private theorem advAtt_mem_hyps (tr : Trace) : advAtt ∈ hyps tr := by
  rcases tr with ⟨h, _ | _⟩ <;> exact List.mem_cons_self

private theorem noCollision_mem_hyps {h h' : List Step} (hh' : h' ∈ aSteps h) :
    Form.box (noCollision h' h) ∈ hyps ⟨h, true⟩ :=
  List.mem_cons_of_mem _ (List.mem_map_of_mem (f := fun h' => Form.box (noCollision h' h)) hh')

/-- **Forward secrecy of the ratchet, derived for a fixed trace** (CCS26 §2.2–2.3,
`happens(τ) ⇒ safe(τ) ⇒ frame(τ′) ⊬ ck(τ)`, with `τ′` the last position): for a safe position
`hτ`, a suffix of the history before `Corrupt`, the frame at the last position of the trace does
not deduce `ck(hτ)`. Without `Corrupt` it is `pfsFrame`; with it, `pfsCorrupt`. -/
def chainPFS : (tr : Trace) → {hτ : List Step} → hτ <:+ tr.hist →
    Der (hyps tr) (.nonDed (Env.cons (P.close tr.frame) Env.empty) (P.close (ck hτ)) order_frame)
  | ⟨h, false⟩, hτ, _ => pfsFrame (advAtt_mem_hyps ⟨h, false⟩) hτ h
  | ⟨h, true⟩, _, hs => pfsCorrupt (advAtt_mem_hyps ⟨h, true⟩) hs fun _ => noCollision_mem_hyps

/-- The PRF instances of the chain meet their PRF assumption when each PRF.R and PRF.L-sec
instance does. -/
private theorem holds_of_chainPRF {R : Model decl → Prop} {C : ∀ M : Model decl, AdvClass M}
    (hprfR : ∀ h, (instR h).Holds R C) (hprfL : ∀ h h', (instL h h').Holds R C) :
    ∀ e, ChainPRF e → e.Holds R C
  | _, .inl ⟨h, rfl⟩ => hprfR h
  | _, .inr ⟨h, h', rfl⟩ => hprfL h h'

/-- **Soundness of the derivation** (`Derivation.sound`): over every restriction on models that
gives `ChainR` (uniform names of messages, long attacker tapes, polynomial bit blocks for messages,
`fst(⟨x, y⟩) = x`), against every class of machines under which each PRF.R and PRF.L-sec instance
meets its PRF assumption, `frame(last) ⊬ ck(hτ)` holds in every model of `hyps tr`: `adv(att)` and
the NoCollision lemmas. -/
theorem chainPFS_sound (tr : Trace) {hτ : List Step} (hs : hτ <:+ tr.hist)
    (R : Model decl → Prop) (C : ∀ M : Model decl, AdvClass M) (hR : ∀ M, R M → ChainR M)
    (hprfR : ∀ h, (instR h).Holds R C) (hprfL : ∀ h h', (instL h h').Holds R C) :
    Valid R C (hyps tr)
      (.nonDed (Env.cons (P.close tr.frame) Env.empty) (P.close (ck hτ)) order_frame) :=
  (chainPFS tr hs).sound R C (fun _ h => h.elim) (holds_of_chainPRF hprfR hprfL) hR

/-- **Forward secrecy at every position before `Corrupt`**: for positions `h'` and `hτ` of a trace,
both before `Corrupt` and in either order, `frame(h') ⊬ ck(hτ)`, sound as `chainPFS_sound`. -/
theorem pfsFrame_sound (tr : Trace) (hτ h' : List Step) (R : Model decl → Prop)
    (C : ∀ M : Model decl, AdvClass M) (hR : ∀ M, R M → ChainR M)
    (hprfR : ∀ h, (instR h).Holds R C) (hprfL : ∀ h h', (instL h h').Holds R C) :
    Valid R C (hyps tr)
      (.nonDed (Env.cons (P.close (frame h')) Env.empty) (P.close (ck hτ)) order_frame) :=
  (pfsFrame (advAtt_mem_hyps tr) hτ h').sound R C (fun _ h => h.elim)
    (holds_of_chainPRF hprfR hprfL) hR

end Interop.Squirrel.Chain
