/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.QueueReplay
import Bandits.Support.CappedService

/-!
# Conservation for literal queue replay

This module proves register conservation for `QueueReplay.transition` and its
chronological list replay. The queue update is from
`sources/zip4/manuscript/04_slow_fast_learner.tex:154-174`; the replayed
register-algebra aspect of reconstruction is related to
`sources/zip4/manuscript/06_interruptions.tex:80-101`. These results concern
only the integer score and backlog registers, not the full operational
reconstruction lemma.
-/

public section

namespace Bandits.Support.QueueTraceConservation

/-- The arrival accepted by a queue record: disabled records accept none. -/
@[expose]
def acceptedArrival (record : Bool × Nat) : Nat :=
  if record.1 then record.2 else 0

/-- One literal transition changes score plus backlog by exactly its accepted
arrival. The service bound and subtraction cancellation are proved here from
the capped-service definition. -/
theorem transition_score_add_backlog (capacity : Nat) (registers : Nat × Nat)
    (record : Bool × Nat) :
    (Bandits.Support.QueueReplay.transition capacity registers record).1 +
        (Bandits.Support.QueueReplay.transition capacity registers record).2 =
      registers.1 + registers.2 + acceptedArrival record := by
  cases record with
  | mk enabled arrival =>
    cases registers with
    | mk score backlog =>
      cases enabled with
      | false =>
          simp [acceptedArrival, Bandits.Support.QueueReplay.transition]
      | true =>
          change
            (score + min capacity (backlog + arrival)) +
                (backlog + arrival - min capacity (backlog + arrival)) =
              score + backlog + arrival
          have hservice : min capacity (backlog + arrival) ≤ backlog + arrival := by
            exact Bandits.Support.CappedService.service_le_total capacity backlog arrival
          have hcancel := Nat.sub_add_cancel hservice
          calc
            (score + min capacity (backlog + arrival)) +
                (backlog + arrival - min capacity (backlog + arrival)) =
              score +
                ((backlog + arrival - min capacity (backlog + arrival)) +
                  min capacity (backlog + arrival)) := by omega
            _ = score + (backlog + arrival) := by rw [hcancel]
            _ = score + backlog + arrival := by omega

/-- Fold induction invariant for score-plus-backlog conservation. -/
private theorem foldl_score_add_backlog (capacity : Nat) (initial : Nat × Nat)
    (records : List (Bool × Nat)) :
    (records.foldl
        (fun registers record =>
          Bandits.Support.QueueReplay.transition capacity registers record)
        initial).1 +
        (records.foldl
          (fun registers record =>
            Bandits.Support.QueueReplay.transition capacity registers record)
          initial).2 =
      initial.1 + initial.2 + (records.map acceptedArrival).sum := by
  induction records generalizing initial with
  | nil =>
      simp
  | cons record records ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, transition_score_add_backlog]
      omega

/-- Replaying records preserves the initial score-plus-backlog total and adds
the sum of per-record accepted arrivals from the list. -/
theorem replay_score_add_backlog (capacity : Nat) (initial : Nat × Nat)
    (records : List (Bool × Nat)) :
    (Bandits.Support.QueueReplay.replay capacity initial records).1 +
        (Bandits.Support.QueueReplay.replay capacity initial records).2 =
      initial.1 + initial.2 + (records.map acceptedArrival).sum := by
  simpa only [Bandits.Support.QueueReplay.replay] using
    foldl_score_add_backlog capacity initial records

end Bandits.Support.QueueTraceConservation
