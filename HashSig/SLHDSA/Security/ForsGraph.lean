/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Fors.Program
public import HashSig.SLHDSA.Security.GraphInput
import HashSig.SLHDSA.Security.ProviderObservation

/-!
# Canonical SHAKE interpretation of the effectful FORS graph

The natural-label FORS theorem is interpreted through the actual public-hash encoder and
effectful secret provider. The existing traversal issues every scheduled query in its original
order and reads back the existing signature carrier. No cache freshness, address width, resource
bound or relation between digest and node lengths is required for this program equality.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

open Graph

variable (vp : ValidatedParams)

private abbrev NativeSpec := (Adrs × List (Bytes vp.params.n)) →ₒ Bytes vp.params.n
private abbrev World := unifSpec + shakeSpec vp

private noncomputable def labelProgram (core : CorePrimitives vp.params) (seed : core.Y)
    (key : ForsKey vp.params) (md : List Byte) :
    OracleComp ((Adrs × List core.Y) →ₒ core.Y) (ForsSigCore vp.params core) :=
  forsSignWithSecret core
    (fun address value => query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [value]))
    (fun address left right =>
      query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [left, right]))
    (fun address => query (spec := (Adrs × List core.Y) →ₒ core.Y) (address, [seed])) md key.address

private noncomputable def base (pk : Bytes vp.params.n) :
    QueryImpl (NativeSpec vp) (OracleComp (World vp)) := fun input =>
  prefixBytes vp.params.n <$> (query (spec := shakeSpec vp)
    (encode vp (.inl (.thash pk ((shakeCore vp).adrsToKey input.1) input.2))) :
      OracleComp (World vp) (Bytes vp.params.m))

private theorem label_program_eq_actual (pk sk : Bytes vp.params.n) (key : ForsKey vp.params)
    (md : List Byte) :
    simulateQ (base vp pk) (labelProgram vp (shakeCore vp) sk key md) =
    simulateQ (encImpl vp)
      (forsSignWithSecretM (shakeCore vp) (oracleSecret (shakeCore vp) (Equiv.refl _) pk sk)
        md pk key.address : OracleComp (unifSpec + hashSpec (shakeCore vp))
          (ForsSigCore vp.params (shakeCore vp))) := by
  have leaf : (fun address value => simulateQ (base vp pk)
      (query (spec := NativeSpec vp) (address, [value]) : OracleComp (NativeSpec vp) (Bytes
          vp.params.n))) =
      (fun address value => simulateQ (encImpl vp)
        (PublicHash.f (shakeCore vp) pk address value :
          OracleComp (unifSpec + hashSpec (shakeCore vp)) (Bytes vp.params.n))) := by
    funext address value
    simp only [base, PublicHash.f, simulateQ_HasQuery_query, encImpl]
    rfl
  have node : (fun address left right => simulateQ (base vp pk)
      (query (spec := NativeSpec vp) (address, [left, right]) : OracleComp (NativeSpec vp)
          (Bytes vp.params.n))) =
      (fun address left right => simulateQ (encImpl vp)
        (PublicHash.h (shakeCore vp) pk address left right :
          OracleComp (unifSpec + hashSpec (shakeCore vp)) (Bytes vp.params.n))) := by
    funext address left right
    simp only [base, PublicHash.h, simulateQ_HasQuery_query, encImpl]
    rfl
  have secret : (fun address => simulateQ (base vp pk)
      (query (spec := NativeSpec vp) (address, [sk]) : OracleComp (NativeSpec vp) (Bytes
          vp.params.n))) =
      (fun address => simulateQ (encImpl vp)
        (oracleSecret (shakeCore vp) (Equiv.refl _) pk sk address :
          OracleComp (unifSpec + hashSpec (shakeCore vp)) (Bytes vp.params.n))) := by
    funext address
    exact congrFun (congrFun leaf address) sk
  have native := forsSignWithSecret_natural (shakeCore vp) (simulateQ' (base vp pk))
    (fun address value => query (spec := NativeSpec vp) (address, [value]))
    (fun address value => simulateQ (encImpl vp)
      (PublicHash.f (shakeCore vp) pk address value))
    (fun address left right => query (spec := NativeSpec vp) (address, [left, right]))
    (fun address left right => simulateQ (encImpl vp)
      (PublicHash.h (shakeCore vp) pk address left right))
    (fun address => query (spec := NativeSpec vp) (address, [sk]))
    (fun address => simulateQ (encImpl vp)
      (oracleSecret (shakeCore vp) (Equiv.refl _) pk sk address))
    (fun address value => congrFun (congrFun leaf address) value)
    (fun address left right => congrFun (congrFun (congrFun node address) left) right)
    (fun address _ => congrFun secret address) md key.address
  have actual := simulateQ_forsSignWithSecret (shakeCore vp) (encImpl vp)
    (PublicHash.f (shakeCore vp) pk) (PublicHash.h (shakeCore vp) pk)
    (oracleSecret (shakeCore vp) (Equiv.refl _) pk sk) md key.address
  exact native.trans actual.symm

private def labelInput (node : StructuralNode vp.params)
    (cells : Node vp.params → Bytes vp.params.n) : (NativeSpec vp).Domain :=
  StructuralNode.input vp.valid node cells

private def labelAssign (node : StructuralNode vp.params)
    (cells : Node vp.params → Bytes vp.params.n) (answer : Bytes vp.params.n) :
    Node vp.params → Bytes vp.params.n := updateCell node cells answer

private noncomputable def graphAssign (node : StructuralNode vp.params)
    (cells : Node vp.params → Bytes vp.params.n) (answer : Bytes vp.params.m) :
    Node vp.params → Bytes vp.params.n :=
  Function.update cells (.structural node) (prefixBytes vp.params.n answer)

private theorem input_pullback (pk : Bytes vp.params.n) (node : StructuralNode vp.params)
    (cells : Node vp.params → Bytes vp.params.n) :
    base vp pk (labelInput vp node cells) =
      prefixBytes vp.params.n <$> (query (spec := shakeSpec vp)
        (GraphInput.input vp pk node cells) : OracleComp (World vp) (Bytes vp.params.m)) := rfl

private theorem traversal_interpretation (pk : Bytes vp.params.n)
    (nodes : List (StructuralNode vp.params)) (cells : Node vp.params → Bytes vp.params.n) :
    simulateQ (base vp pk)
      (RandomOracleTraversal.evaluate (labelInput vp) (labelAssign vp) nodes cells) =
      simulateQ (QueryImpl.ofLift (shakeSpec vp) (OracleComp (World vp)))
        (RandomOracleTraversal.evaluate (GraphInput.input vp pk) (graphAssign vp) nodes cells) := by
  induction nodes generalizing cells with
  | nil => simp [RandomOracleTraversal.evaluate]
  | cons node nodes ih =>
      simp only [RandomOracleTraversal.evaluate, simulateQ_bind, simulateQ_spec_query,
        QueryImpl.ofLift_apply]
      rw [input_pullback]
      simp only [bind_map_left]
      apply congrArg (Bind.bind (query (spec := shakeSpec vp)
        (GraphInput.input vp pk node cells) : OracleComp (World vp) (Bytes vp.params.m)))
      funext answer
      exact ih (graphAssign vp node cells answer)

/-- The actual SHAKE FORS component is exactly its ordered structural traversal, for every
validated parameter set and digest list. Returned answers retain the canonical zero-padding
when the full digest is shorter than one node; no width or prefix-length premise is needed. -/
theorem forsSignWithSecretM_eq_graph (pk sk : Bytes vp.params.n) (key : ForsKey vp.params)
    (md : List Byte) (cells : Node vp.params → Bytes vp.params.n) (seed : cells .secretSeed = sk) :
    simulateQ (encImpl vp)
      (forsSignWithSecretM (shakeCore vp) (oracleSecret (shakeCore vp) (Equiv.refl _) pk sk)
        md pk key.address : OracleComp (unifSpec + hashSpec (shakeCore vp))
          (ForsSigCore vp.params (shakeCore vp))) =
      Fors.reconstruct (shakeCore vp) key md <$>
        simulateQ (QueryImpl.ofLift (shakeSpec vp) (OracleComp (unifSpec + shakeSpec vp)))
          (RandomOracleTraversal.evaluate (GraphInput.input vp pk)
            (fun node table answer => updateCell node table (prefixBytes vp.params.n answer))
            (ForsSchedule.signing key md) cells) := by
  have generic := Fors.forsSignWithSecret_eq_evaluate vp.params vp.valid (shakeCore vp) sk key
      md cells seed
  have folded := congrArg (simulateQ (base vp pk)) generic
  have mapped := simulateQ_map (base vp pk)
    (RandomOracleTraversal.evaluate (labelInput vp) (labelAssign vp)
      (ForsSchedule.signing key md) cells)
    (Fors.reconstruct (shakeCore vp) key md)
  have transported := congrArg (fun computation : OracleComp (World vp)
      (Node vp.params → Bytes vp.params.n) =>
        Fors.reconstruct (shakeCore vp) key md <$> computation)
    (traversal_interpretation vp pk (ForsSchedule.signing key md) cells)
  exact (label_program_eq_actual vp pk sk key md).symm.trans (folded.trans (mapped.trans
      transported))


end SLHDSA.Security
