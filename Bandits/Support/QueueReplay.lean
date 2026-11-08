module

public import Batteries.Data.List.Lemmas

/-!
Deterministic replay of a single integer queue register pair.

The transition follows the queue update in `sources/zip4/manuscript/04_slow_fast_learner.tex`,
lines 157–165: enabled records serve `min capacity (backlog + arrival)` and update score and
backlog, while disabled records preserve both registers. In particular, enabled records with
zero arrival still serve existing backlog. The replay composition helper is relevant to the
reconstruction discussion in `sources/zip4/manuscript/06_interruptions.tex`, lines 97–100.
These definitions model only that register update; they do not encode protocol histories.
-/

public section

namespace Bandits.Support.QueueReplay

/-- Apply one enabled or disabled queue record to `(score, backlog)`. -/
@[expose]
def transition (capacity : Nat) (registers : Nat × Nat) (record : Bool × Nat) : Nat × Nat :=
  if record.1 then
    let service := min capacity (registers.2 + record.2)
    (registers.1 + service, registers.2 + record.2 - service)
  else
    registers

/-- Replay a list of `(enabled, arrival)` records from an initial register pair. -/
@[expose]
def replay (capacity : Nat) (initial : Nat × Nat) (records : List (Bool × Nat)) : Nat × Nat :=
  records.foldl (fun registers record => transition capacity registers record) initial

/-- Replaying concatenated records is replaying the second list from the first result. -/
theorem replay_append (capacity : Nat) (initial : Nat × Nat)
    (first second : List (Bool × Nat)) :
    replay capacity initial (first ++ second) =
      replay capacity (replay capacity initial first) second := by
  change
    List.foldl (fun registers record => transition capacity registers record)
        initial (first ++ second) =
      List.foldl (fun registers record => transition capacity registers record)
        (List.foldl (fun registers record => transition capacity registers record)
          initial first) second
  exact List.foldl_append

/-- Equal initial score and backlog registers and equal records give equal replays. -/
theorem replay_congruent (capacity score₁ backlog₁ score₂ backlog₂ : Nat)
    (records₁ records₂ : List (Bool × Nat))
    (hscore : score₁ = score₂) (hbacklog : backlog₁ = backlog₂)
    (hrecords : records₁ = records₂) :
    replay capacity (score₁, backlog₁) records₁ =
      replay capacity (score₂, backlog₂) records₂ := by
  cases hscore
  cases hbacklog
  cases hrecords
  rfl

/-- An enabled zero-arrival record still serves the backlog already present. -/
theorem transition_enabled_zero_arrival (capacity score backlog : Nat) :
    transition capacity (score, backlog) (true, 0) =
      (score + min capacity backlog, backlog - min capacity backlog) := rfl

/-- With positive capacity and backlog, enabled service with zero arrival is positive. -/
theorem transition_zero_arrival_service_pos {capacity _score backlog : Nat}
    (hcapacity : 0 < capacity) (hbacklog : 0 < backlog) :
    0 < min capacity backlog := by
  rcases Nat.le_total capacity backlog with h | h
  · rw [Nat.min_eq_left h]
    exact hcapacity
  · rw [Nat.min_eq_right h]
    exact hbacklog

end Bandits.Support.QueueReplay
