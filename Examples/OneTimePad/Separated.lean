/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.Interaction.UC.ReactiveWorld

/-!
# Separated actors for authenticated single-use transmission

The environment, sender, private setup, public channel, delivery adversary, and receiver
are six distinct polynomial machines. Setup randomness lives in the setup machine's private
continuation and is sent only on internal share-distribution routes. The channel retains its
original ciphertext and accepts only a delivery decision. The adversary has one explicit
ciphertext/advice exchange with the environment before making that decision.

This fixed single-use topology gives a concrete execution model. Its finite conversation
does not provide dynamic sessions, arbitrary backchannel protocols, or computational admission.
-/

public section

namespace OneTimePad.Separated

open PFunctor Interaction.UC ReactiveProcess ReactiveNetwork DynSystem

variable {Message Cipher Random SendKey ReceiveKey Memory Advice : Type}

/-- Six distinct components, including the private setup and the public delivery channel. -/
inductive Node where
  | environment | setup | sender | channel | adversary | receiver
  deriving DecidableEq

instance : Fintype Node where
  elems := {.environment, .setup, .sender, .channel, .adversary, .receiver}
  complete node := by cases node <;> simp

/-- Private share distribution and deterministic endpoint transformations. -/
structure Encoding (Message Cipher Random SendKey ReceiveKey : Type) where
  /-- Distribute two private shares after drawing setup randomness. -/
  shares : Message → Random → SendKey × ReceiveKey
  /-- Sender-side ciphertext formation. -/
  encrypt : SendKey → Message → Cipher
  /-- Receiver-side recovery from the authenticated ciphertext. -/
  decrypt : ReceiveKey → Cipher → Message

/-- An environment retaining private auxiliary state and participating in the backchannel. -/
structure Environment (Message Cipher Memory Advice : Type) where
  /-- Select an input and private state before private setup sampling. -/
  choose : ProbComp (Message × Memory)
  /-- Respond to the adversary's actual public ciphertext. -/
  advise : Message → Memory → Cipher → ProbComp Advice
  /-- Observe the actual ciphertext and optional delivered message. -/
  observe : Message → Memory → Cipher → Option Message → ProbComp Bool

/-- The adversary receives only the public ciphertext and the environment's explicit advice. -/
structure Adversary (Cipher Advice : Type) where
  /-- The channel consumes this Boolean decision, retaining the original ciphertext itself. -/
  allow : Cipher → Advice → ProbComp Bool

/-- Environment operations retain the chosen input and private auxiliary state. -/
inductive EnvOp (Message Cipher Memory : Type) where
  | choose
  | advise (input : Message × Memory) (ciphertext : Cipher)
  | observe (input : Message × Memory) (ciphertext : Cipher) (delivered : Option Message)

/-- Dependent responses of the environment's local operations. -/
@[expose] def envAnswer (Advice : Type) : EnvOp Message Cipher Memory → Type
  | .choose => Message × Memory
  | .advise _ _ => Advice
  | .observe _ _ _ => Bool

/-- Local effects give sampling to setup and explicit observations to the two opponents. -/
@[expose] def effects (Message Cipher Random Memory Advice : Type) : Node → PFunctor.{0, 0}
  | .environment => ⟨EnvOp Message Cipher Memory, envAnswer Advice⟩
  | .setup => ⟨Unit, fun _ => Random⟩
  | .adversary => ⟨Cipher × Advice, fun _ => Bool⟩
  | .sender | .channel | .receiver => ⟨Empty, Empty.elim⟩

/-- A single packet channel with the indicated payload type. -/
@[expose] def port (Payload : Type) : Interface := ⟨Unit, fun _ => Payload⟩

/-- Internal endpoint interfaces distinguish setup traffic, public traffic, and delivery. -/
@[expose] def ports (Message Cipher SendKey ReceiveKey Advice : Type) : Node → PortBoundary
  | .environment => ⟨port (Cipher ⊕ Option Message), port (Message ⊕ Advice)⟩
  | .setup => ⟨port (Message ⊕ Unit), port (SendKey ⊕ ReceiveKey)⟩
  | .sender => ⟨port (Message ⊕ SendKey), port (Message ⊕ Cipher)⟩
  | .channel => ⟨port (Cipher ⊕ Bool), port (Cipher ⊕ Option Cipher)⟩
  | .adversary => ⟨port (Cipher ⊕ Advice), port (Cipher ⊕ Bool)⟩
  | .receiver => ⟨port (Option Cipher ⊕ ReceiveKey), port (Unit ⊕ Option Message)⟩

attribute [local implicit_reducible] effects ports envAnswer port signature Response

/-- The one-step polynomial signature of a selected actor. -/
abbrev ActorSignature (Message Cipher Random SendKey ReceiveKey Memory Advice : Type)
    (node : Node) :=
  signature (effects Message Cipher Random Memory Advice node)
    (ports Message Cipher SendKey ReceiveKey Advice node)

/-- Choose, send, answer the backchannel, and finally observe the actual delivery. -/
@[expose] def environmentProgram :
    FreeM (ActorSignature Message Cipher Random SendKey ReceiveKey Memory Advice .environment)
      (Outcome Bool) :=
  .liftBind (.effect .choose) fun input =>
    .liftBind (.send ⟨(), .inl input.1⟩) fun _ =>
      .liftBind .receive fun packet => match packet.2 with
      | .inr _ => .pure .aborted
      | .inl ciphertext =>
        .liftBind (.effect (.advise input ciphertext)) fun advice =>
          .liftBind (.send ⟨(), .inr advice⟩) fun _ =>
            .liftBind .receive fun packet => match packet.2 with
            | .inl _ => .pure .aborted
            | .inr delivered =>
              .liftBind (.effect (.observe input ciphertext delivered)) fun verdict =>
                .pure (.returned verdict)

/-- Sample privately, send the sender's share, and retain the receiver's share until requested. -/
@[expose] def setupProgram (encoding : Encoding Message Cipher Random SendKey ReceiveKey) :
    FreeM (ActorSignature Message Cipher Random SendKey ReceiveKey Memory Advice .setup)
      (Outcome Bool) :=
  .liftBind .receive fun packet => match packet.2 with
  | .inr _ => .pure .aborted
  | .inl message =>
    .liftBind (.effect ()) fun random =>
      let shares := encoding.shares message random
      .liftBind (.send ⟨(), .inl shares.1⟩) fun _ =>
        .liftBind .receive fun packet => match packet.2 with
        | .inl _ => .pure .aborted
        | .inr _ =>
          .liftBind (.send ⟨(), .inr shares.2⟩) fun _ => .pure (.returned true)

/-- Obtain a private share and encrypt the message actually received from the environment. -/
@[expose] def senderProgram (encoding : Encoding Message Cipher Random SendKey ReceiveKey) :
    FreeM (ActorSignature Message Cipher Random SendKey ReceiveKey Memory Advice .sender)
      (Outcome Bool) :=
  .liftBind .receive fun packet => match packet.2 with
  | .inr _ => .pure .aborted
  | .inl message =>
    .liftBind (.send ⟨(), .inl message⟩) fun _ =>
      .liftBind .receive fun packet => match packet.2 with
      | .inl _ => .pure .aborted
      | .inr key =>
        .liftBind (.send ⟨(), .inr (encoding.encrypt key message)⟩) fun _ =>
          .pure (.returned true)

/-- Retain the original ciphertext while asking the adversary whether to deliver it. -/
@[expose] def channelProgram :
    FreeM (ActorSignature Message Cipher Random SendKey ReceiveKey Memory Advice .channel)
      (Outcome Bool) :=
  .liftBind .receive fun packet => match packet.2 with
  | .inr _ => .pure .aborted
  | .inl ciphertext =>
    .liftBind (.send ⟨(), .inl ciphertext⟩) fun _ =>
      .liftBind .receive fun packet => match packet.2 with
      | .inl _ => .pure .aborted
      | .inr permitted =>
        .liftBind (.send ⟨(), .inr (if permitted then some ciphertext else none)⟩) fun _ =>
          .pure (.returned true)

/-- Exchange public ciphertext and advice with the environment before deciding delivery. -/
@[expose] def adversaryProgram :
    FreeM (ActorSignature Message Cipher Random SendKey ReceiveKey Memory Advice .adversary)
      (Outcome Bool) :=
  .liftBind .receive fun packet => match packet.2 with
  | .inr _ => .pure .aborted
  | .inl ciphertext =>
    .liftBind (.send ⟨(), .inl ciphertext⟩) fun _ =>
      .liftBind .receive fun packet => match packet.2 with
      | .inl _ => .pure .aborted
      | .inr advice =>
        .liftBind (.effect (ciphertext, advice)) fun permitted =>
          .liftBind (.send ⟨(), .inr permitted⟩) fun _ => .pure (.returned true)

/-- Decode only authenticated deliveries. A drop consumes the corresponding four local ticks. -/
@[expose] def receiverProgram (encoding : Encoding Message Cipher Random SendKey ReceiveKey) :
    FreeM (ActorSignature Message Cipher Random SendKey ReceiveKey Memory Advice .receiver)
      (Outcome Bool) :=
  .liftBind .receive fun packet => match packet.2 with
  | .inr _ => .pure .aborted
  | .inl none =>
    .liftBind .tick fun _ => .liftBind .tick fun _ =>
      .liftBind .tick fun _ => .liftBind .tick fun _ =>
        .liftBind (.send ⟨(), .inr none⟩) fun _ => .pure (.returned true)
  | .inl (some ciphertext) =>
    .liftBind (.send ⟨(), .inl ()⟩) fun _ =>
      .liftBind .receive fun packet => match packet.2 with
      | .inl _ => .pure .aborted
      | .inr key =>
        .liftBind (.send ⟨(), .inr (some (encoding.decrypt key ciphertext))⟩) fun _ =>
          .pure (.returned true)

/-- Actual component machines and routes, with no global state shared by the effect handlers. -/
@[expose] def diagram (encoding : Encoding Message Cipher Random SendKey ReceiveKey)
    (draw : ProbComp Random) (env : Environment Message Cipher Memory Advice)
    (adversary : Adversary Cipher Advice) :
    HandledDiagram ProbComp Node PortBoundary.empty Bool where
  effect := effects Message Cipher Random Memory Advice
  ports := ports Message Cipher SendKey ReceiveKey Advice
  component
    | .environment => DynComputation.ofFreeM fun _ => environmentProgram
    | .setup => DynComputation.ofFreeM fun _ => setupProgram encoding
    | .sender => DynComputation.ofFreeM fun _ => senderProgram encoding
    | .channel => DynComputation.ofFreeM fun _ => channelProgram
    | .adversary => DynComputation.ofFreeM fun _ => adversaryProgram
    | .receiver => DynComputation.ofFreeM fun _ => receiverProgram encoding
  route
    | .environment, ⟨_, .inl message⟩ => .inl ⟨.sender, ⟨(), .inl message⟩⟩
    | .environment, ⟨_, .inr advice⟩ => .inl ⟨.adversary, ⟨(), .inr advice⟩⟩
    | .setup, ⟨_, .inl key⟩ => .inl ⟨.sender, ⟨(), .inr key⟩⟩
    | .setup, ⟨_, .inr key⟩ => .inl ⟨.receiver, ⟨(), .inr key⟩⟩
    | .sender, ⟨_, .inl message⟩ => .inl ⟨.setup, ⟨(), .inl message⟩⟩
    | .sender, ⟨_, .inr ciphertext⟩ => .inl ⟨.channel, ⟨(), .inl ciphertext⟩⟩
    | .channel, ⟨_, .inl ciphertext⟩ => .inl ⟨.adversary, ⟨(), .inl ciphertext⟩⟩
    | .channel, ⟨_, .inr delivered⟩ => .inl ⟨.receiver, ⟨(), .inl delivered⟩⟩
    | .adversary, ⟨_, .inl ciphertext⟩ => .inl ⟨.environment, ⟨(), .inl ciphertext⟩⟩
    | .adversary, ⟨_, .inr permitted⟩ => .inl ⟨.channel, ⟨(), .inr permitted⟩⟩
    | .receiver, ⟨_, .inl _⟩ => .inl ⟨.setup, ⟨(), .inr ()⟩⟩
    | .receiver, ⟨_, .inr delivered⟩ => .inl ⟨.environment, ⟨(), .inr delivered⟩⟩
  ingress packet := packet.1.elim
  handler
    | .environment, .choose => env.choose
    | .environment, .advise input ciphertext => env.advise input.1 input.2 ciphertext
    | .environment, .observe input ciphertext delivered =>
      env.observe input.1 input.2 ciphertext delivered
    | .setup, _ => draw
    | .adversary, input => adversary.allow input.1 input.2
    | .sender, operation | .channel, operation | .receiver, operation => operation.elim

/-- A finite closed assembly of the six actual actors. -/
@[expose] def assembly (encoding : Encoding Message Cipher Random SendKey ReceiveKey)
    (draw : ProbComp Random) (env : Environment Message Cipher Memory Advice)
    (adversary : Adversary Cipher Advice) : ReactiveSecurity.System PortBoundary.empty :=
  HandledAssembly.ofDiagram (diagram encoding draw env adversary)

/-- Observe the actual environment after the specified number of token activations. -/
@[expose] def experiment (encoding : Encoding Message Cipher Random SendKey ReceiveKey)
    (draw : ProbComp Random) (env : Environment Message Cipher Memory Advice)
    (adversary : Adversary Cipher Advice) (fuel : ℕ) : ProbComp ReactiveSecurity.Result :=
  ReactiveSecurity.observe <$>
    (assembly encoding draw env adversary).tokenObservation .environment fuel

/-- The effectful conversation implemented by the six communicating actors. -/
@[expose] def conversation (encoding : Encoding Message Cipher Random SendKey ReceiveKey)
    (draw : ProbComp Random) (env : Environment Message Cipher Memory Advice)
    (adversary : Adversary Cipher Advice) : ProbComp Bool := do
  let input ← env.choose
  let random ← draw
  let shares := encoding.shares input.1 random
  let ciphertext := encoding.encrypt shares.1 input.1
  let advice ← env.advise input.1 input.2 ciphertext
  let permitted ← adversary.allow ciphertext advice
  env.observe input.1 input.2 ciphertext
    (if permitted then some (encoding.decrypt shares.2 ciphertext) else none)

end OneTimePad.Separated
