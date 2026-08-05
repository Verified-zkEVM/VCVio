/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# Transcript Fixtures

Machine-checked fixtures for `Matching` (DF'17 Def. 3), `pingPong` (Def. 4), and
the `isPingPong` / `fullPingPong` wrappers used by the security experiment.

For clarity, the transcripts are written out literally. The positive tests
contain the timestamps an honest relay produces under the clock discipline of
`recordOne` / `recordOpt`: each recorded message consumes one tick, and the
adversary relaying a message to the other session records it there at a later
tick.

These fixtures do *not* exercise `opImpl`, `recordOne`, or `recordOpt`.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace TranscriptFixtures

/-
These are transcripts that should satisfy the `Matching` predicate for the
correct value of the `oracleLeadsFirst` argument. Note that `oracleLeadsFirst`
must be true exactly when the number of rounds is odd. This, along with the
requirement that `Matching` transcripts interleave their messages, captures the
convention that T speaks last in the UAKE security game (since the oracle
corresponds to T in the UAKE game).
-/

private def oracle2 : Transcript ℕ := ⟨[(1, 1), (2, 2)]⟩
private def challenge2 : Transcript ℕ := ⟨[(1, 0), (2, 3)]⟩

private def oracle3 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4)]⟩
private def challenge3 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5)]⟩

private def oracle4 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5), (4, 6)]⟩
private def challenge4 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4), (4, 7)]⟩

private def oracle5 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4), (4, 7), (5, 8)]⟩
private def challenge5 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5), (4, 6), (5, 9)]⟩

private def oracle6 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5), (4, 6), (5, 9), (6, 10)]⟩
private def challenge6 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4), (4, 7), (5, 8), (6, 11)]⟩

private def oracle7 : Transcript ℕ :=
  ⟨[(1, 0), (2, 3), (3, 4), (4, 7), (5, 8), (6, 11), (7, 12)]⟩
private def challenge7 : Transcript ℕ :=
  ⟨[(1, 1), (2, 2), (3, 5), (4, 6), (5, 9), (6, 10), (7, 13)]⟩

example : Matching false oracle2 challenge2 := by decide
example : Matching true oracle3 challenge3 := by decide
example : Matching false oracle4 challenge4 := by decide
example : Matching true oracle5 challenge5 := by decide
example : Matching false oracle6 challenge6 := by decide
example : Matching true oracle7 challenge7 := by decide

/-
`Matching` does *not* hold for the wrong value of `oracleLeadsFirst`.
-/

example : ¬ Matching true oracle2 challenge2 := by decide
example : ¬ Matching false oracle3 challenge3 := by decide
example : ¬ Matching true oracle4 challenge4 := by decide
example : ¬ Matching false oracle5 challenge5 := by decide
example : ¬ Matching true oracle6 challenge6 := by decide
example : ¬ Matching false oracle7 challenge7 := by decide

/-
`Matching` does not commute.
-/

example : ¬ Matching false challenge2 oracle2 := by decide
example : ¬ Matching true challenge3 oracle3 := by decide

/-
A transcript fails to satisfy `Matching` when its message content is wrong.
-/

private def substituted2 : Transcript ℕ := ⟨[(1, 1), (99, 2)]⟩
private def substituted3 : Transcript ℕ := ⟨[(1, 0), (99, 3), (3, 4)]⟩

example : ¬ Matching false substituted2 challenge2 := by decide
example : ¬ Matching true substituted3 challenge3 := by decide

/-
A transcript fails to satisfy `Matching` when its length doesn't match.
-/

private def truncated2 : Transcript ℕ := ⟨[(1, 1)]⟩
private def extended2 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 4)]⟩

example : ¬ Matching false truncated2 challenge2 := by decide
example : ¬ Matching false extended2 challenge2 := by decide

/-
Reordering oracle messages in a `Matching` transcript pair renders it
non-matching.
-/

private def reordered2 : Transcript ℕ := ⟨[(1, 2), (2, 1)]⟩

example : ¬ Matching false reordered2 challenge2 := by decide

/-
Transcripts opened or extended after challenge completes cannot satisfy
`Matching`, even if the message sequence itself matches.
-/

private def afterChallenge2 : Transcript ℕ := ⟨[(1, 4), (2, 5)]⟩
private def afterChallenge3 : Transcript ℕ := ⟨[(1, 6), (2, 7), (3, 8)]⟩

example : ¬ Matching false afterChallenge2 challenge2 := by decide
example : ¬ Matching true afterChallenge3 challenge3 := by decide

example : afterChallenge2.entries.map (·.1) = challenge2.entries.map (·.1) := by decide
example : afterChallenge3.entries.map (·.1) = challenge3.entries.map (·.1) := by decide

private def lateChallenge3 : Transcript ℕ := ⟨[(1, 2), (2, 3), (3, 6)]⟩
private def lateRelayed3 : Transcript ℕ := ⟨[(1, 0), (2, 4), (3, 5)]⟩
private def finishedLate3 : Transcript ℕ := ⟨[(1, 1), (2, 7), (3, 8)]⟩

example : Matching true lateRelayed3 lateChallenge3 := by decide
example : ¬ Matching true finishedLate3 lateChallenge3 := by decide
example : finishedLate3.entries.map (·.1) = lateChallenge3.entries.map (·.1) := by decide

/-
`Matching` and non-`Matching` transcripts for testing `pingPong`, `isPingPong`,
and `fullPingPong`.
-/

private def twoSessionChallenge2 : Transcript ℕ := ⟨[(1, 0), (2, 5)]⟩
private def relayed2 : Transcript ℕ := ⟨[(1, 3), (2, 4)]⟩
private def bogus2 : Transcript ℕ := ⟨[(99, 1), (100, 2)]⟩

private def twoSessionChallenge3 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 8)]⟩
private def relayed3 : Transcript ℕ := ⟨[(1, 0), (2, 6), (3, 7)]⟩
private def bogus3 : Transcript ℕ := ⟨[(1, 3), (99, 4), (100, 5)]⟩

example : Matching false relayed2 twoSessionChallenge2 := by decide
example : ¬ Matching false bogus2 twoSessionChallenge2 := by decide
example : Matching true relayed3 twoSessionChallenge3 := by decide
example : ¬ Matching true bogus3 twoSessionChallenge3 := by decide

/-
`pingPong` is satisfied when a `Matching` transcript is present
-/

example : pingPong false [oracle2] challenge2 = true := by decide
example : pingPong true [oracle3] challenge3 = true := by decide

/-
... even when a non-matching transcript is also present
-/

example : pingPong false [bogus2, relayed2] twoSessionChallenge2 = true := by decide
example : pingPong true [bogus3, relayed3] twoSessionChallenge3 = true := by decide

example :
    ([bogus2, relayed2].filter fun T =>
      decide (Matching false T twoSessionChallenge2)).length = 1 := by decide
example :
    ([bogus3, relayed3].filter fun T =>
      decide (Matching true T twoSessionChallenge3)).length = 1 := by decide

/-
... but not when a matching transcript is absent.
-/

example : pingPong false [bogus2] twoSessionChallenge2 = false := by decide
example : pingPong false [] challenge2 = false := by decide
example : pingPong false [afterChallenge2] challenge2 = false := by decide

/-
Dummy `Party` and `Scheme` (and helper functions) for testing `isPingPong` and
`fullPingPong`.
-/

private def inertParty : Party Id Unit ℕ (Option ℕ) where
  State := Unit
  init := fun _ => pure (.waitForMsg ())
  step := fun _ _ => pure .reject
  output := fun _ => pure none

private def roundsOnly (n : ℕ) : Scheme Id ℕ Unit Unit ℕ where
  rounds := n
  setup := pure ((), ())
  U := inertParty
  T := inertParty

private def result (n : ℕ) (oracleTrs : List (Transcript ℕ)) (challengeTr : Transcript ℕ) :
    ChallengeResult (roundsOnly n) :=
  ⟨none, challengeTr, oracleTrs⟩

private def sessions (n : ℕ) (trs : List (Transcript ℕ × Bool)) :
    List (TSession (roundsOnly n)) :=
  trs.map fun s => ⟨(), s.1, none, s.2⟩

/-
`isPingPong` is satisfied when a `Matching` transcript is present
-/

example : isPingPong (result 2 [oracle2] challenge2) = true := by decide
example : isPingPong (result 3 [oracle3] challenge3) = true := by decide
example : isPingPong (result 4 [oracle4] challenge4) = true := by decide
example : isPingPong (result 5 [oracle5] challenge5) = true := by decide
example : isPingPong (result 6 [oracle6] challenge6) = true := by decide
example : isPingPong (result 7 [oracle7] challenge7) = true := by decide

/-
... even if a non-`Matching` transcript is also present
-/

example : isPingPong (result 2 [bogus2, relayed2] twoSessionChallenge2) = true := by decide

/-
... but not when the round-count parity is wrong.
-/

example : isPingPong (result 3 [oracle2] challenge2) = false := by decide
example : isPingPong (result 2 [oracle3] challenge3) = false := by decide

/-
`fullPingPong` is satisfied when a `Matching` transcript is present, and it has
been revealed, but not when the transcript has not been revealed or does not
satisfy `Matching`.
-/

example :
    fullPingPong (sessions 2 [(oracle2, true)]) (result 2 [oracle2] challenge2) = true := by
  decide
example :
    fullPingPong (sessions 2 [(oracle2, false)]) (result 2 [oracle2] challenge2) = false := by
  decide
example :
    fullPingPong (sessions 2 [(bogus2, true)]) (result 2 [bogus2] twoSessionChallenge2)
      = false := by
  decide

/-
`fullPingPong` is not satisfied when the revealed transcript does not satisfy
`Matching`, even if a second non-revealed transcript *does* satisfy `Matching`.
-/

example :
    fullPingPong (sessions 2 [(bogus2, true), (relayed2, false)])
      (result 2 [bogus2, relayed2] twoSessionChallenge2) = false := by
  decide

end TranscriptFixtures

end AKE.UAKE
