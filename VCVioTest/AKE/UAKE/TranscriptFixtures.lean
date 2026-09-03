/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/

module

public import VCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# Transcript Fixtures

Machine-checked fixtures for `Matching` (DF'17 Def. 3), `pingPong` (Def. 4), and
the `isPingPong` / `fullPingPong` wrappers used by the security experiment.

For clarity, the transcripts are written out literally. The positive tests
contain the timestamps an honest relay produces under the clock discipline of
`recordOne` / `recordOpt`: each recorded message consumes one tick, and the
adversary relaying a message to the other session records it there at a later
tick.
-/

@[expose] public section

open OracleSpec OracleComp

namespace VCVioTest.AKE.UAKE

open _root_.AKE.UAKE

/-
These are transcripts that should satisfy the `Matching` predicate for the
correct value of the `oracleLeadsFirst` argument. Note that `oracleLeadsFirst`
must be true exactly when the number of rounds is odd. This, along with the
requirement that `Matching` transcripts interleave their messages, captures the
convention that T speaks last in the UAKE security game (since the oracle
corresponds to T in the UAKE game).
-/

def oracle2 : Transcript ℕ := ⟨[(1, 1), (2, 2)]⟩
def challenge2 : Transcript ℕ := ⟨[(1, 0), (2, 3)]⟩

def oracle3 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4)]⟩
def challenge3 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5)]⟩

def oracle4 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5), (4, 6)]⟩
def challenge4 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4), (4, 7)]⟩

def oracle5 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4), (4, 7), (5, 8)]⟩
def challenge5 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5), (4, 6), (5, 9)]⟩

def oracle6 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 5), (4, 6), (5, 9), (6, 10)]⟩
def challenge6 : Transcript ℕ := ⟨[(1, 0), (2, 3), (3, 4), (4, 7), (5, 8), (6, 11)]⟩

def oracle7 : Transcript ℕ :=
  ⟨[(1, 0), (2, 3), (3, 4), (4, 7), (5, 8), (6, 11), (7, 12)]⟩
def challenge7 : Transcript ℕ :=
  ⟨[(1, 1), (2, 2), (3, 5), (4, 6), (5, 9), (6, 10), (7, 13)]⟩

theorem matching_oracle2_challenge2 : Matching false oracle2 challenge2 := by decide
theorem matching_oracle3_challenge3 : Matching true oracle3 challenge3 := by decide
theorem matching_oracle4_challenge4 : Matching false oracle4 challenge4 := by decide
theorem matching_oracle5_challenge5 : Matching true oracle5 challenge5 := by decide
theorem matching_oracle6_challenge6 : Matching false oracle6 challenge6 := by decide
theorem matching_oracle7_challenge7 : Matching true oracle7 challenge7 := by decide

/-
`Matching` does *not* hold for the wrong value of `oracleLeadsFirst`.
-/

theorem not_matching_wrongParity_oracle2 : ¬ Matching true oracle2 challenge2 := by decide
theorem not_matching_wrongParity_oracle3 : ¬ Matching false oracle3 challenge3 := by decide
theorem not_matching_wrongParity_oracle4 : ¬ Matching true oracle4 challenge4 := by decide
theorem not_matching_wrongParity_oracle5 : ¬ Matching false oracle5 challenge5 := by decide
theorem not_matching_wrongParity_oracle6 : ¬ Matching true oracle6 challenge6 := by decide
theorem not_matching_wrongParity_oracle7 : ¬ Matching false oracle7 challenge7 := by decide

/-
`Matching` does not commute.
-/

theorem not_matching_challenge2_oracle2 : ¬ Matching false challenge2 oracle2 := by decide
theorem not_matching_challenge3_oracle3 : ¬ Matching true challenge3 oracle3 := by decide

/-
A transcript fails to satisfy `Matching` when its message content is wrong.
-/

def substituted2 : Transcript ℕ := ⟨[(1, 1), (99, 2)]⟩
def substituted3 : Transcript ℕ := ⟨[(1, 0), (99, 3), (3, 4)]⟩

theorem not_matching_substituted2_challenge2 :
    ¬ Matching false substituted2 challenge2 := by decide
theorem not_matching_substituted3_challenge3 :
    ¬ Matching true substituted3 challenge3 := by decide

/-
A transcript fails to satisfy `Matching` when its length doesn't match.
-/

def truncated2 : Transcript ℕ := ⟨[(1, 1)]⟩
def extended2 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 4)]⟩

theorem not_matching_truncated2_challenge2 : ¬ Matching false truncated2 challenge2 := by decide
theorem not_matching_extended2_challenge2 : ¬ Matching false extended2 challenge2 := by decide

/-
Reordering oracle messages in a `Matching` transcript pair renders it
non-matching.
-/

def reordered2 : Transcript ℕ := ⟨[(1, 2), (2, 1)]⟩

theorem not_matching_reordered2_challenge2 : ¬ Matching false reordered2 challenge2 := by decide

/-
Transcripts opened or extended after challenge completes cannot satisfy
`Matching`, even if the message sequence itself matches.
-/

def afterChallenge2 : Transcript ℕ := ⟨[(1, 4), (2, 5)]⟩
def afterChallenge3 : Transcript ℕ := ⟨[(1, 6), (2, 7), (3, 8)]⟩

theorem not_matching_afterChallenge2_challenge2 :
    ¬ Matching false afterChallenge2 challenge2 := by decide
theorem not_matching_afterChallenge3_challenge3 :
    ¬ Matching true afterChallenge3 challenge3 := by decide

theorem afterChallenge2_messages_eq_challenge2 :
    afterChallenge2.entries.map (·.1) = challenge2.entries.map (·.1) := by decide
theorem afterChallenge3_messages_eq_challenge3 :
    afterChallenge3.entries.map (·.1) = challenge3.entries.map (·.1) := by decide

def lateChallenge3 : Transcript ℕ := ⟨[(1, 2), (2, 3), (3, 6)]⟩
def lateRelayed3 : Transcript ℕ := ⟨[(1, 0), (2, 4), (3, 5)]⟩
def finishedLate3 : Transcript ℕ := ⟨[(1, 1), (2, 7), (3, 8)]⟩

theorem matching_lateRelayed3_lateChallenge3 :
    Matching true lateRelayed3 lateChallenge3 := by decide
theorem not_matching_finishedLate3_lateChallenge3 :
    ¬ Matching true finishedLate3 lateChallenge3 := by decide
theorem finishedLate3_messages_eq_lateChallenge3 :
    finishedLate3.entries.map (·.1) = lateChallenge3.entries.map (·.1) := by decide

/-
`Matching` and non-`Matching` transcripts for testing `pingPong`, `isPingPong`,
and `fullPingPong`.
-/

def twoSessionChallenge2 : Transcript ℕ := ⟨[(1, 0), (2, 5)]⟩
def relayed2 : Transcript ℕ := ⟨[(1, 3), (2, 4)]⟩
def bogus2 : Transcript ℕ := ⟨[(99, 1), (100, 2)]⟩

def twoSessionChallenge3 : Transcript ℕ := ⟨[(1, 1), (2, 2), (3, 8)]⟩
def relayed3 : Transcript ℕ := ⟨[(1, 0), (2, 6), (3, 7)]⟩
def bogus3 : Transcript ℕ := ⟨[(1, 3), (99, 4), (100, 5)]⟩

theorem matching_relayed2_twoSession :
    Matching false relayed2 twoSessionChallenge2 := by decide
theorem not_matching_bogus2_twoSession :
    ¬ Matching false bogus2 twoSessionChallenge2 := by decide
theorem matching_relayed3_twoSession :
    Matching true relayed3 twoSessionChallenge3 := by decide
theorem not_matching_bogus3_twoSession :
    ¬ Matching true bogus3 twoSessionChallenge3 := by decide

/-
`pingPong` is satisfied when a `Matching` transcript is present
-/

theorem pingPong_oracle2_eq_true : pingPong false [oracle2] challenge2 = true := by decide
theorem pingPong_oracle3_eq_true : pingPong true [oracle3] challenge3 = true := by decide

/-
... even when a non-matching transcript is also present
-/

theorem pingPong_bogus2_relayed2_eq_true :
    pingPong false [bogus2, relayed2] twoSessionChallenge2 = true := by decide
theorem pingPong_bogus3_relayed3_eq_true :
    pingPong true [bogus3, relayed3] twoSessionChallenge3 = true := by decide

theorem matching_count_bogus2_relayed2 :
    ([bogus2, relayed2].filter fun T =>
      decide (Matching false T twoSessionChallenge2)).length = 1 := by decide
theorem matching_count_bogus3_relayed3 :
    ([bogus3, relayed3].filter fun T =>
      decide (Matching true T twoSessionChallenge3)).length = 1 := by decide

/-
... but not when a matching transcript is absent.
-/

theorem pingPong_bogus2_eq_false :
    pingPong false [bogus2] twoSessionChallenge2 = false := by decide
theorem pingPong_nil_eq_false : pingPong false [] challenge2 = false := by decide
theorem pingPong_afterChallenge2_eq_false :
    pingPong false [afterChallenge2] challenge2 = false := by decide

/-
Dummy `Party` and `Scheme` (and helper functions) for testing `isPingPong` and
`fullPingPong`.
-/

def inertParty : Party Id Unit ℕ (Option ℕ) where
  State := Unit
  init := fun _ => pure (.waitForMsg ())
  step := fun _ _ => pure .reject
  output := fun _ => pure none

def roundsOnly (n : ℕ) : Scheme Id ℕ Unit Unit ℕ where
  rounds := n
  setup := pure ((), ())
  U := inertParty
  T := inertParty

def result (n : ℕ) (oracleTrs : List (Transcript ℕ)) (challengeTr : Transcript ℕ) :
    ChallengeResult (roundsOnly n) :=
  ⟨none, challengeTr, oracleTrs⟩

def sessions (n : ℕ) (trs : List (Transcript ℕ × Bool)) :
    List (TSession (roundsOnly n)) :=
  trs.map fun s => ⟨(), s.1, none, s.2⟩

/-
`isPingPong` is satisfied when a `Matching` transcript is present
-/

theorem isPingPong_oracle2_eq_true : isPingPong (result 2 [oracle2] challenge2) = true := by decide
theorem isPingPong_oracle3_eq_true : isPingPong (result 3 [oracle3] challenge3) = true := by decide
theorem isPingPong_oracle4_eq_true : isPingPong (result 4 [oracle4] challenge4) = true := by decide
theorem isPingPong_oracle5_eq_true : isPingPong (result 5 [oracle5] challenge5) = true := by decide
theorem isPingPong_oracle6_eq_true : isPingPong (result 6 [oracle6] challenge6) = true := by decide
theorem isPingPong_oracle7_eq_true : isPingPong (result 7 [oracle7] challenge7) = true := by decide

/-
... even if a non-`Matching` transcript is also present
-/

theorem isPingPong_bogus2_relayed2_eq_true :
    isPingPong (result 2 [bogus2, relayed2] twoSessionChallenge2) = true := by decide

/-
... but not when the round-count parity is wrong.
-/

theorem isPingPong_wrongParity_oracle2_eq_false :
    isPingPong (result 3 [oracle2] challenge2) = false := by decide
theorem isPingPong_wrongParity_oracle3_eq_false :
    isPingPong (result 2 [oracle3] challenge3) = false := by decide

/-
`fullPingPong` is satisfied when a `Matching` transcript is present, and it has
been revealed, but not when the transcript has not been revealed or does not
satisfy `Matching`.
-/

theorem fullPingPong_oracle2_revealed_eq_true :
    fullPingPong (sessions 2 [(oracle2, true)]) (result 2 [oracle2] challenge2) = true := by
  decide
theorem fullPingPong_oracle2_unrevealed_eq_false :
    fullPingPong (sessions 2 [(oracle2, false)]) (result 2 [oracle2] challenge2) = false := by
  decide
theorem fullPingPong_bogus2_revealed_eq_false :
    fullPingPong (sessions 2 [(bogus2, true)]) (result 2 [bogus2] twoSessionChallenge2)
      = false := by
  decide

/-
`fullPingPong` is not satisfied when the revealed transcript does not satisfy
`Matching`, even if a second non-revealed transcript *does* satisfy `Matching`.
-/

theorem fullPingPong_bogus2_relayed2_eq_false :
    fullPingPong (sessions 2 [(bogus2, true), (relayed2, false)])
      (result 2 [bogus2, relayed2] twoSessionChallenge2) = false := by
  decide

end VCVioTest.AKE.UAKE
