/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import KatzLindell.Common.Scheme
import VCVio.CryptoFoundations.SymmEncAlg.EAV
import VCVio.CryptoFoundations.Asymptotics.Security
import VCVio.OracleComp.Coinductive.PolyTimeClosure

/-!
# Katz–Lindell Definitions 3.9 and 3.10: Eavesdropping Security

The asymptotic definition of computationally secure private-key encryption from Katz and
Lindell, *Introduction to Modern Cryptography*, §3.2.1, on top of the single-scheme
experiments of `VCVio.CryptoFoundations.SymmEncAlg.EAV`:

- `PPTEavAdversary`: the two-phase eavesdropping adversary as a pair of program families
  over the coin oracle (the textbook's probabilistic machine with a random bit tape),
  with `PPTEavAdversary.IsPPT` demanding Turing-machine-grounded polynomial time for
  both phases.
- `privKEav` / `eavGuessGame`: the experiment `PrivK^eav` and Definition 3.9 (the
  adversary identifies the hidden bit with probability at most negligibly above `1/2`),
  packaged as a `SecurityGame` whose advantage is the guessing bias.
- `privKEavFixed` / `eavDistGame`: Definition 3.10, the distinguishing form comparing
  the adversary's outputs across the two fixed values of the challenge bit.
- `eavGuessGame_eq_eavDistGame`: the two definitions give literally the same advantage
  function, so the induced security notions coincide with no loss factor (the exercise
  left after Definition 3.10 in the book).
- `EavSecure`: eavesdropping security, quantified over all PPT two-phase adversaries.
- `exists_negligible_probOutput_privKEav_le`: the book's literal one-sided reading of
  Definition 3.9, `Pr[PrivK^eav = 1] ≤ 1/2 + negl n`.
-/


open ENNReal OracleComp OracleSpec SymmEncAlg

namespace KatzLindell

variable {M K C : ℕ → Type}

/-- A two-phase eavesdropping adversary family in the probabilistic-polynomial-time
model: each phase is a program over the coin oracle (the random bit tape), so that
`IsPPT` below can demand Turing-machine-grounded polynomial time per phase. The
cross-phase `State` family carries whatever the first phase wants to remember. -/
structure PPTEavAdversary (M C : ℕ → Type) where
  /-- Cross-phase adversary state. -/
  State : ℕ → Type
  /-- The adversary's fixed-width representation of its own cross-phase state. This is
  the sole *adversary-supplied* boundary encoding in the model, and it is sound because
  it is **shared** between the phase that writes it and the phase that reads it: every
  bit cached in the encoded state was produced by the choose phase's witnessed machine
  from canonical inputs and coin answers, so no computation can be smuggled through the
  representation (see the `## Model` notes of `VCVio.OracleComp.Coinductive.PolyTime`). -/
  encState : Computability.BitEncFam State
  /-- Choose the two challenge messages, retaining state. -/
  choose : (n : ℕ) → OracleComp coinSpec (M n × M n × State n)
  /-- Guess which challenge message a ciphertext encrypts. -/
  distinguish : (n : ℕ) → State n × C n → OracleComp coinSpec Bool

/-- Interpret the coin-oracle phases into `ProbComp` (answering each coin query
uniformly) to form a single-scheme `SymmEncAlg.EavAdversary` at each parameter. -/
def PPTEavAdversary.toEavAdversary (A : PPTEavAdversary M C) (n : ℕ) :
    EavAdversary ProbComp (M n) (C n) where
  State := A.State n
  chooseMessages := simulateQ uniformSampleImpl (A.choose n)
  distinguish s c := simulateQ uniformSampleImpl (A.distinguish n (s, c))

/-- Probabilistic polynomial time for a two-phase eavesdropping adversary: both phases
are `OracleComp.IsPolyTime` program families, at boundaries pinned to the canonical
message/ciphertext encodings `eM`/`eC` and the adversary's own shared cross-phase state
encoding. This is the `isPPT` slot of `SecurityGame.secureAgainst` used by `EavSecure`. -/
def PPTEavAdversary.IsPPT (A : PPTEavAdversary M C) (eM : Computability.BitEncFam M)
    (eC : Computability.BitEncFam C) : Prop :=
  OracleComp.IsPolyTime (BoundaryData.coin .unit (eM.pair (eM.pair A.encState)))
      (fun n (_ : Unit) => A.choose n) ∧
    OracleComp.IsPolyTime (BoundaryData.coin (A.encState.pair eC) .bool)
      (fun n (p : A.State n × C n) => A.distinguish n p)

/-- Flip a two-phase eavesdropping adversary's guess: same choice phase, distinguish phase's
output bit negated. The adversary that outputs `1 - PrivK^eav` guess. -/
def PPTEavAdversary.negateDistinguish (A : PPTEavAdversary M C) : PPTEavAdversary M C where
  State := A.State
  encState := A.encState
  choose := A.choose
  distinguish n p := (fun b => !b) <$> A.distinguish n p

/-- The PPT adversary class is **closed under output negation** (`distinguish ↦
!distinguish`) — the closure the one-sided→two-sided reading of Definition 3.9 needs
(see `exists_negligible_probOutput_privKEav_le`). Discharged by the abstract output-map
closure `OracleComp.IsPolyTime.map`, which is derivable exactly because the output
boundary is the canonical `Bool` encoding (with an existential output encoding this
closure was uncertifiable — the pre-canonicalization model carried it as a
hypothesis). -/
theorem PPTEavAdversary.isPPT_negateDistinguish {A : PPTEavAdversary M C}
    {eM : Computability.BitEncFam M} {eC : Computability.BitEncFam C}
    (hA : A.IsPPT eM eC) : A.negateDistinguish.IsPPT eM eC :=
  ⟨hA.1, hA.2.map (fun _ b => !b) .bool (.C 2) (fun n => by simp)⟩

variable (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n))

/-- Katz–Lindell `PrivK^eav_{A,π}(n)`: the guessing experiment across the family. -/
noncomputable def privKEav (A : PPTEavAdversary M C) (n : ℕ) : ProbComp Bool :=
  EavExp (π n) (A.toEavAdversary n)

/-- Katz–Lindell `out(PrivK^eav_{A,π}(n, b))`: the fixed-bit branch experiments,
returning the adversary's output bit. -/
noncomputable def privKEavFixed (A : PPTEavAdversary M C) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  EavExpFixed (π n) (A.toEavAdversary n) b

/-- **Katz–Lindell Definition 3.9** packaged as a `SecurityGame`: the advantage of an
adversary is the bias of the guessing experiment away from the coin flip `1/2`. -/
noncomputable def eavGuessGame : SecurityGame (PPTEavAdversary M C) :=
  SecurityGame.ofBoolGuessGame (fun A n => privKEav π A n)

/-- **Katz–Lindell Definition 3.10** packaged as a `SecurityGame`: the advantage of an
adversary is the distinguishing advantage between the two fixed-bit branches. -/
noncomputable def eavDistGame : SecurityGame (PPTEavAdversary M C) :=
  SecurityGame.ofBoolDistGame (fun A n => privKEavFixed π A true n)
    (fun A n => privKEavFixed π A false n)

/-- Definitions 3.9 and 3.10 define literally the same advantage function, hence the
same security notion — the equivalence exercise after Katz–Lindell Definition 3.10,
via the single-scheme hidden-bit decomposition
`SymmEncAlg.eavBiasAdvantage_eq_eavDistAdvantage`. -/
theorem eavGuessGame_eq_eavDistGame : eavGuessGame π = eavDistGame π :=
  congrArg SecurityGame.mk (funext fun A => funext fun n =>
    congrArg ENNReal.ofReal
      (eavBiasAdvantage_eq_eavDistAdvantage (π n) (A.toEavAdversary n)))

/-- **Eavesdropping security** (Katz–Lindell Definitions 3.9 / 3.10): every PPT
two-phase adversary — at the pinned canonical message/ciphertext boundaries `eM`/`eC` —
has negligible advantage in the guessing experiment. -/
def EavSecure (eM : Computability.BitEncFam M) (eC : Computability.BitEncFam C) : Prop :=
  (eavGuessGame π).secureAgainst (PPTEavAdversary.IsPPT · eM eC)

/-- Eavesdropping security is equivalently the distinguishing form of the game being
secure, by the game equality. -/
theorem eavSecure_iff_distGame_secure (eM : Computability.BitEncFam M)
    (eC : Computability.BitEncFam C) :
    EavSecure π eM eC ↔ (eavDistGame π).secureAgainst (PPTEavAdversary.IsPPT · eM eC) := by
  rw [EavSecure, eavGuessGame_eq_eavDistGame]

/-- The literal one-sided reading of Katz–Lindell Definition 3.9: for a secure scheme,
every PPT adversary identifies the hidden bit with probability at most negligibly above
`1/2`.

The two-sided bias form of `EavSecure` is stronger, and recovering it from the one-sided
`Pr[PrivK = 1] ≤ 1/2 + negl` reading needs the PPT adversary class closed under **output
negation** (`distinguish ↦ !distinguish`) — available unconditionally as
`PPTEavAdversary.isPPT_negateDistinguish` now that the output boundary is canonical.
Assembling the full two-sided `EavSecure` from the one-sided bound and this closure is
the remaining probability step. -/
theorem exists_negligible_probOutput_privKEav_le {eM : Computability.BitEncFam M}
    {eC : Computability.BitEncFam C} (h : EavSecure π eM eC)
    (A : PPTEavAdversary M C) (hA : A.IsPPT eM eC) :
    ∃ f : ℕ → ℝ≥0∞, negligible f ∧
      ∀ n, Pr[= true | privKEav π A n] ≤ 1 / 2 + f n := by
  exact ⟨(eavGuessGame π).advantage A, h A hA, fun n =>
    ProbComp.probOutput_true_le_half_add_ofReal_boolBiasAdvantage (privKEav π A n)⟩

end KatzLindell
