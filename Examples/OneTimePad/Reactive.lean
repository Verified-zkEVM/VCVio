/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.Interaction.UC.ReactiveRuntime

/-!
# A single-use authenticated transmission network

An environment chooses a message, sends it to a service, receives the actual channel view,
and computes its Boolean verdict. The service encrypts the message, asks a ciphertext-only
adversary whether to deliver, and opens only the authenticated ciphertext it retained.
Dropping a message consumes a tick in place of opening it.

The two actors have different polynomial effect and packet interfaces. The service's key
is shared setup, unavailable to the environment's handlers. Both finite execution policies
are compared with the same stateful conversation. This is a restricted delivery-adversary
model: adversarial modification, side conversations, and general UC composition need
additional components and theorems.
-/

public section

namespace OneTimePad.Reactive

open PFunctor Interaction.UC ReactiveProcess ReactiveNetwork ReactiveRuntime
  DynSystem OracleComp MeasureTheory ProbabilityTheory

attribute [local implicit_reducible] signature Response

variable {Message Cipher Memory S : Type}

/-- Public ciphertext and the message delivered over an authenticated channel, if any. -/
abbrev View (Message Cipher : Type) := Cipher × Option Message

/-- A single-use environment retains its input and private auxiliary state across the exchange. -/
structure Environment (Message Cipher Memory : Type) where
  /-- Chosen independently of the private setup. -/
  choose : ProbComp (Message × Memory)
  /-- Observe the actual reply together with the input and retained private state. -/
  observe : Message → Memory → View Message Cipher → ProbComp Bool

/-- Stateful operations available to the transmission service. -/
structure Operations (Message Cipher S : Type) where
  /-- Produce a ciphertext from an input message. -/
  encrypt : Message → StateT S ProbComp Cipher
  /-- Decide whether to deliver, using only the ciphertext as explicit input. -/
  allow : Cipher → StateT S ProbComp Bool
  /-- Recover the authenticated message from the retained ciphertext. -/
  decrypt : Cipher → StateT S ProbComp Message

/-- Environment requests retain the chosen message at the observation operation. -/
inductive EnvOp (Message Cipher Memory : Type) where
  | choose
  | observe (input : Message × Memory) (view : View Message Cipher)

/-- The answer types of environment requests. -/
@[expose] def envAnswer : EnvOp Message Cipher Memory → Type
  | .choose => Message × Memory
  | .observe _ _ => Bool

/-- Service requests distinguish encryption, adversarial delivery, and decryption. -/
inductive ServiceOp (Message Cipher : Type) where
  | encrypt (message : Message)
  | allow (ciphertext : Cipher)
  | decrypt (ciphertext : Cipher)

/-- The answer types of service requests. -/
@[expose] def serviceAnswer : ServiceOp Message Cipher → Type
  | .encrypt _ => Cipher
  | .allow _ => Bool
  | .decrypt _ => Message

/-- Environment and service have different effect capabilities. -/
@[expose] def effects (Message Cipher Memory : Type) : Bool → PFunctor.{0, 0}
  | false => ⟨EnvOp Message Cipher Memory, envAnswer⟩
  | true => ⟨ServiceOp Message Cipher, serviceAnswer⟩

/-- The environment sends messages and receives channel views; the service has dual ports. -/
@[expose] def ports (Message Cipher : Type) : Bool → PortBoundary
  | false => ⟨⟨Unit, fun _ => View Message Cipher⟩, ⟨Unit, fun _ => Message⟩⟩
  | true => ⟨⟨Unit, fun _ => Message⟩, ⟨Unit, fun _ => View Message Cipher⟩⟩

attribute [local implicit_reducible] effects ports serviceAnswer envAnswer

/-- A verdict depends on the packet actually received after sending the chosen input. -/
@[expose] def environmentProgram :
    FreeM (signature (effects Message Cipher Memory false) (ports Message Cipher false))
      (Outcome Bool) :=
  .liftBind (.effect .choose) fun input =>
    .liftBind (.send ⟨(), input.1⟩) fun _ =>
      .liftBind .receive fun packet =>
        .liftBind (.effect (.observe input packet.2)) fun verdict => .pure (.returned verdict)

/-- Retain the encrypted ciphertext across the delivery decision, preventing modification. -/
@[expose] def serviceProgram :
    FreeM (signature (effects Message Cipher Memory true) (ports Message Cipher true))
      (Outcome Bool) :=
  .liftBind .receive fun packet =>
    .liftBind (.effect (.encrypt packet.2)) fun ciphertext =>
      .liftBind (.effect (.allow ciphertext)) fun permitted =>
        match permitted with
        | true =>
          .liftBind (.effect (.decrypt ciphertext)) fun message =>
            .liftBind (.send ⟨(), (ciphertext, some message)⟩) fun _ => .pure (.returned true)
        | false =>
          .liftBind .tick fun _ =>
            .liftBind (.send ⟨(), (ciphertext, none)⟩) fun _ => .pure (.returned true)

/-- A closed, two-actor network with typed bidirectional routing. -/
@[expose] def network (Message Cipher Memory : Type) : Network Bool PortBoundary.empty Bool where
  effect := effects Message Cipher Memory
  ports := ports Message Cipher
  component
    | false => DynComputation.ofFreeM fun _ => environmentProgram
    | true => DynComputation.ofFreeM fun _ => serviceProgram
  route
    | false, packet => .inl ⟨true, packet⟩
    | true, packet => .inl ⟨false, packet⟩
  ingress packet := packet.1.elim
  environment := false

attribute [local implicit_reducible] network DynComputation.ofFreeM

/-- Environment effects preserve the hidden service state; service effects use their API. -/
@[expose] def implementation (env : Environment Message Cipher Memory)
    (ops : Operations Message Cipher S) :
    (id : Bool) → Handler (StateT S ProbComp) ((network Message Cipher Memory).effect id)
  | false, .choose => fun state => (fun message => (message, state)) <$> env.choose
  | false, .observe input view => fun state =>
      (fun verdict => (verdict, state)) <$> env.observe input.1 input.2 view
  | true, .encrypt message => ops.encrypt message
  | true, .allow ciphertext => ops.allow ciphertext
  | true, .decrypt ciphertext => ops.decrypt ciphertext

/-- Direct interpretation of the same single-use conversation, retaining shared state. -/
@[expose] def conversation (env : Environment Message Cipher Memory)
    (ops : Operations Message Cipher S)
    (state : S) : ProbComp Bool := do
  let input ← env.choose
  let (ciphertext, state) ← ops.encrypt input.1 state
  let (permitted, state) ← ops.allow ciphertext state
  let delivered ← if permitted = true then
      (fun pair => some pair.1) <$> ops.decrypt ciphertext state
    else pure none
  env.observe input.1 input.2 (ciphertext, delivered)

/-- Nine token activations execute the chosen message, delivery decision, and verdict. -/
theorem tokenExperiment_eq (env : Environment Message Cipher Memory)
    (ops : Operations Message Cipher S)
    (setup : ProbComp S) :
    tokenExperiment (network Message Cipher Memory) (implementation env ops) setup 9 =
      setup >>= fun state => (fun verdict => some (.returned verdict)) <$>
        conversation env ops state := by
  simp only [tokenExperiment]
  congr 1
  funext state
  simp only [network, environmentProgram, FreeM.pure_eq_pure, serviceProgram, runToken,
    activate, initial, DynComputation.ofFreeM_init, DynComputation.view_ofFreeM_liftBind,
    DynComputation.ofFreeM_State, StateT.run, implementation, zero_add, bind_pure_comp,
    Functor.map_map, dispatch, bind_pure, bind_map_left, Function.update, ↓reduceDIte,
    Function.update_idem, List.nil_append, Nat.reduceAdd, pure_bind, Bool.true_eq_false,
    Function.update_eq_self, outcome, map_bind, conversation]
  apply bind_congr
  intro message
  apply bind_congr
  rintro ⟨ciphertext, state⟩
  apply bind_congr
  rintro ⟨permitted, state⟩
  cases permitted <;>
    simp only [DynComputation.view_ofFreeM_liftBind, DynComputation.ofFreeM_State,
      pure_bind, bind_map_left, Function.update, ↓reduceDIte, Function.update_idem,
      List.nil_append, Nat.reduceAdd, Bool.false_eq_true, Function.update_eq_self,
      Functor.map_map, DynComputation.view_ofFreeM_pure, ↓reduceIte, map_bind] <;> rfl

/-- Two explicitly charged deliveries accompany the nine local activations. -/
@[expose] def fifoSchedule : List (Activation Bool) :=
  [.node false, .node false, .deliver, .node true, .node true, .node true,
    .node true, .node true, .deliver, .node false, .node false]

/-- The fixed FIFO schedule realizes the same stateful conversation. -/
theorem fifoExperiment_eq (env : Environment Message Cipher Memory)
    (ops : Operations Message Cipher S)
    (setup : ProbComp S) :
    fifoExperiment (network Message Cipher Memory) (implementation env ops) setup fifoSchedule =
      setup >>= fun state => (fun verdict => some (.returned verdict)) <$>
        conversation env ops state := by
  simp only [fifoExperiment]
  congr 1
  funext state
  simp only [network, environmentProgram, FreeM.pure_eq_pure, serviceProgram, fifoSchedule,
    initial, runFIFO, fifoStep, activate, DynComputation.ofFreeM_init,
    DynComputation.view_ofFreeM_liftBind, DynComputation.ofFreeM_State, StateT.run,
    implementation, zero_add, bind_pure_comp, Functor.map_map, deliver, dispatch, bind_pure,
    pure_bind, bind_map_left, Function.update, ↓reduceDIte, Function.update_idem,
    List.nil_append, Nat.reduceAdd, Bool.true_eq_false, Function.update_eq_self,
    outcome, map_bind, conversation]
  apply bind_congr
  intro message
  apply bind_congr
  rintro ⟨ciphertext, state⟩
  apply bind_congr
  rintro ⟨permitted, state⟩
  cases permitted <;>
    simp only [DynComputation.view_ofFreeM_liftBind, DynComputation.ofFreeM_State,
      pure_bind, bind_map_left, Function.update, ↓reduceDIte, Function.update_idem,
      List.nil_append, Nat.reduceAdd, Bool.false_eq_true, Function.update_eq_self,
      Functor.map_map, DynComputation.view_ofFreeM_pure, ↓reduceIte, map_bind] <;> rfl

/-- Observation equality uses different activation budgets for the two policies. -/
theorem fifoExperiment_eq_tokenExperiment (env : Environment Message Cipher Memory)
    (ops : Operations Message Cipher S) (setup : ProbComp S) :
    fifoExperiment (network Message Cipher Memory) (implementation env ops) setup fifoSchedule =
      tokenExperiment (network Message Cipher Memory) (implementation env ops) setup 9 := by
  rw [fifoExperiment_eq, tokenExperiment_eq]

end OneTimePad.Reactive
