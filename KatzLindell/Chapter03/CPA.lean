/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.CryptoFoundations.Asymptotics.Game.Challenger
import VCVio.OracleComp.SimSemantics.Append

/-!
# Katz–Lindell §3.4: CPA Security as a Stateful Left-Right Responder

The chosen-plaintext-attack security experiment `PrivK^cpa` for symmetric encryption, presented as
a **dynamical system**: the challenger is a genuinely stateful probabilistic **responder**
(`ProbResponder`) whose hidden state is the secret key together with the challenge bit, and whose
answer to each left-right query is a *fresh* encryption of the selected message. This is the
pays-rent instance of the stateful-responder machinery — a memoryless `ProbHandler` cannot hold the
fixed key across queries, so the eavesdropping game (`KatzLindell.PrivKEav`, a *stateless* per-query
oracle) is the sharpest game the old memoryless former could express; CPA needs the key in the
responder's state.

- `lrSpec M C`: the CPA oracle interface `unifSpec + (M × M →ₒ C)` — the adversary's own coins plus
  a left-right encryption oracle.
- `cpaLROracle` / `cpaResponder`: the keyed left-right oracle as a `StateT (K × Bool) ProbComp`
  handler and its bundled `ProbResponder`. State = `(key, challenge bit)`; each query encrypts
  `if b then m₁ else m₀` under the fixed key with fresh randomness, keeping the state.
- `run_cpaResponder_eq`: the **games-as-dynamical-systems** identity — running an adversary against
  the stateful responder is `𝒟` of running it against the underlying left-right oracle. The
  responder computes exactly the keyed left-right encryption oracle.
- `cpaExp` / `cpaSecurityGame` / `CPASecure`: `PrivK^cpa` as a concrete `ProbComp` experiment, its
  guessing game via `SecurityGame.ofBoolGuessGame`, and CPA security against a distinguisher class.
- `cpaChallenger`: the same game wrapped as a single-phase `Challenger`, exposing the machine-level
  reading `toMachineGame` (the Turing-machine adversary pipeline).

The book's find-then-guess presentation via `Challenger₂` and the left-right ⇔ find-then-guess
equivalence are next-milestone tickets; the single-phase left-right responder here is the
load-bearing definition.

## Polynomial-time note

As with the PRF distinguishing game, a CPA adversary carries oracle access to the left-right oracle
`M × M →ₒ C`, so its interface is the compound spec `lrSpec`; the canonical fixed-width boundary
encoding for that compound oracle interface is deferred, so `CPASecure` is quantified over an
abstract efficiency predicate `isPPT` (the abstract-`isPPT` design of `SecurityGame.secureAgainst`).
-/

open OracleComp OracleSpec ENNReal SymmEncAlg

namespace KatzLindell

/-! ## The left-right encryption oracle -/

section Single

variable {M K C : Type} [DecidableEq M]

/-- The CPA oracle interface: the adversary's own uniform sampling plus a left-right encryption
oracle taking a pair of messages to a ciphertext. -/
@[reducible] def lrSpec (M C : Type) : OracleSpec (ℕ ⊕ (M × M)) := unifSpec + (M × M →ₒ C)

/-- The keyed left-right encryption oracle as a stateful `ProbComp` handler: uniform-sampling
queries pass through, and a left-right query `(m₀, m₁)` freshly encrypts `if b then m₁ else m₀`
under the fixed key `k`, where `(k, b)` is the responder's hidden state (unchanged by the query —
the key and bit are fixed for the whole game). -/
noncomputable def cpaLROracle (π : SymmEncAlg ProbComp M K C) :
    QueryImpl (lrSpec M C) (StateT (K × Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (K × Bool) ProbComp) +
    fun (mm : M × M) => (do
      let st ← get
      StateT.lift (π.encrypt st.1 (if st.2 then mm.1 else mm.2)) :
        StateT (K × Bool) ProbComp C)

/-- The keyed left-right encryption oracle bundled as a genuinely stateful probabilistic responder
(`ProbResponder.ofStateQueryImpl`): the hidden state is `(key, challenge bit)`, and each answer — a
fresh ciphertext of the selected message — is drawn jointly with the (unchanged) state. The CPA
challenger's wiring data in its coalgebraic presentation. -/
noncomputable def cpaResponder (π : SymmEncAlg ProbComp M K C) : ProbResponder (lrSpec M C) :=
  .ofStateQueryImpl (cpaLROracle π)

omit [DecidableEq M] in
@[simp] theorem cpaResponder_state (π : SymmEncAlg ProbComp M K C) :
    (cpaResponder π).State = (K × Bool) := rfl

omit [DecidableEq M] in
/-- **The CPA game is a dynamical system**: running an adversary against the stateful responder's
`SPMF` handler is exactly `𝒟` of running it against the underlying `StateT (K × Bool) ProbComp`
left-right oracle — the responder *is* the keyed left-right oracle, in the coalgebraic
presentation. Instance of the stateful-responder bridge
`ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl`. -/
theorem run_cpaResponder_eq {γ : Type} (π : SymmEncAlg ProbComp M K C)
    (oa : OracleComp (lrSpec M C) γ) (s : K × Bool) :
    (simulateQ (cpaResponder π).toQueryImpl oa).run s =
      𝒟[(simulateQ (cpaLROracle π) oa).run s] :=
  ProbResponder.run_simulateQ_toQueryImpl_ofStateQueryImpl (cpaLROracle π) oa s

end Single

/-! ## The concrete CPA experiment and security notion -/

variable {M K C : ℕ → Type} [∀ n, DecidableEq (M n)]

/-- A single-phase CPA adversary family: a program with oracle access to the left-right encryption
oracle (and its own coins), outputting a guess of the challenge bit. -/
def PPTCpaAdversary (M C : ℕ → Type) := (n : ℕ) → OracleComp (lrSpec (M n) (C n)) Bool

/-- `PrivK^cpa_{A,π}(n)` as a plain `ProbComp Bool`: sample the key and a hidden uniform challenge
bit, run the adversary against the keyed left-right oracle from that state, and report whether the
adversary's guess matches the challenge bit. -/
noncomputable def cpaExp (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (A : PPTCpaAdversary M C) (n : ℕ) : ProbComp Bool := do
  let k ← (π n).keygen
  let b ← ($ᵗ Bool)
  let b' ← (simulateQ (cpaLROracle (π n)) (A n)).run' (k, b)
  pure (b == b')

/-- The CPA guessing game: advantage is the bias of `PrivK^cpa` away from a fair coin
(`ProbComp.boolBiasAdvantage`), packaged with `SecurityGame.ofBoolGuessGame`. -/
noncomputable def cpaSecurityGame (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n)) :
    SecurityGame (PPTCpaAdversary M C) :=
  SecurityGame.ofBoolGuessGame (cpaExp π)

/-- **CPA security** (Katz–Lindell Definition 3.22): every adversary family in the efficiency class
`isPPT` identifies the challenge bit with probability at most negligibly above `1/2`. The efficiency
class is abstract because the machine-model boundary for oracle-access adversaries over the compound
spec `lrSpec` is deferred (see the module docstring). -/
def CPASecure (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (isPPT : PPTCpaAdversary M C → Prop) : Prop :=
  (cpaSecurityGame π).secureAgainst isPPT

/-! ## The machine-level reading

The same game as a single-phase `Challenger` built by the stateful former `Challenger.ofStateOracle`
(carrier `= K × Bool` exposed), so the CPA experiment also rides the Turing-machine adversary
pipeline (`Challenger.toMachineGame`), and its *program*-game advantage identifies with the concrete
`ProbComp` experiment (`advantage_cpaChallenger_toProgGame`) — the exposed carrier is exactly what
lets that identity go through. -/

/-- `PrivK^cpa` as a single-phase `Challenger` over the left-right oracle, via the stateful former
`Challenger.ofStateOracle`: setup samples the key and hidden bit into the state, the keyed
left-right oracle is the responder, and the judge compares the guess against the hidden bit in the
final state. Exposes `Challenger.toMachineGame` and `advantage_cpaChallenger_toProgGame`. -/
noncomputable def cpaChallenger (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n)) :
    Challenger (fun n => lrSpec (M n) (C n)) (fun _ => Unit) (fun _ => Bool) :=
  Challenger.ofStateOracle (fun n => cpaLROracle (π n))
    (fun n => do
      let k ← (π n).keygen
      let b ← ($ᵗ Bool)
      pure ((k, b), ()))
    (fun _ st ob => pure (some st.2 == ob))

omit [∀ n, DecidableEq (M n)] in
/-- **The CPA challenger's program-game advantage is the concrete `PrivK^cpa` success probability**:
sample the key and hidden bit, run the adversary against the keyed left-right oracle, and report
whether its guess matches the hidden bit read from the final state. A direct instance of the
stateful-challenger characterization `Challenger.advantage_toProgGame_ofStateOracle`, available
because `cpaChallenger` carries its `K × Bool` state explicitly. -/
theorem advantage_cpaChallenger_toProgGame
    (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))
    (oa : (n : ℕ) → Unit → OracleComp (lrSpec (M n) (C n)) Bool) (n : ℕ) :
    (cpaChallenger π).toProgGame.advantage oa n =
      Pr[= true | do
        let k ← (π n).keygen
        let b ← ($ᵗ Bool)
        let rs ← (simulateQ (cpaLROracle (π n)) (oa n ())).run (k, b)
        pure (rs.2.2 == rs.1)] := by
  rw [cpaChallenger, Challenger.advantage_toProgGame_ofStateOracle]
  refine congrArg (fun p : ProbComp Bool => Pr[= true | p]) ?_
  simp only [bind_assoc, pure_bind]
  exact bind_congr fun k => bind_congr fun b => bind_congr fun rs => by simp

end KatzLindell
