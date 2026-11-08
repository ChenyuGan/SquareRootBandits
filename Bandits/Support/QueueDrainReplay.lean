/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.QueueReplay
public import Bandits.Support.ZeroArrival
public import Bandits.Support.CappedService

/-!
# Queue replay across enabled zero-arrival rounds

These identities formalize the enabled zero-arrival service rule in
`sources/zip4/manuscript/04_slow_fast_learner.tex`, lines 157–174, and the
continued service on zero-arrival enabled rounds in
`sources/zip4/manuscript/06_interruptions.tex`, lines 96–101. Disabled records
preserve both registers, while enabled records with zero arrivals continue to
drain the backlog.
-/

public section

namespace Bandits.Support.QueueDrainReplay

open Bandits.Support

/-- One enabled zero-arrival replay step is the capped-service register update. -/
theorem transition_zero_arrival_eq_capped (capacity score backlog : Nat) :
    QueueReplay.transition capacity (score, backlog) (true, 0) =
      (score + CappedService.service capacity backlog 0,
        CappedService.residual capacity backlog 0) := by
  rw [QueueReplay.transition_enabled_zero_arrival]
  simp [CappedService.service, CappedService.residual]

/-- Replaying `n` enabled zero-arrival records accumulates exactly the service
counted by `ZeroArrival.totalService` and leaves its stated backlog. -/
theorem replay_replicate_enabled_zero_arrival_eq_totalService
    (capacity score backlog n : Nat) :
    QueueReplay.replay capacity (score, backlog) (List.replicate n (true, 0)) =
      (score + ZeroArrival.totalService capacity backlog n,
        ZeroArrival.backlogAfter capacity backlog n) := by
  induction n with
  | zero =>
      simp [QueueReplay.replay, ZeroArrival.totalService, ZeroArrival.backlogAfter]
  | succ n ih =>
      rw [show List.replicate (Nat.succ n) (true, 0) =
          List.replicate n (true, 0) ++ [(true, 0)] by
            simp [List.replicate_succ']]
      rw [QueueReplay.replay_append, ih]
      change QueueReplay.transition capacity
          (score + ZeroArrival.totalService capacity backlog n,
            ZeroArrival.backlogAfter capacity backlog n) (true, 0) = _
      rw [transition_zero_arrival_eq_capped]
      rw [ZeroArrival.totalService_succ, ZeroArrival.backlogAfter_succ]
      simp only [CappedService.residual_eq_sub_capacity, CappedService.service,
        ZeroArrival.serviceInRound, Nat.add_zero, Nat.add_assoc]

/-- The exact replay result for `n` enabled zero-arrival rounds: each round
serves up to `capacity`, including when the arrival is zero. -/
theorem replay_replicate_enabled_zero_arrival
    (capacity score backlog n : Nat) :
    QueueReplay.replay capacity (score, backlog) (List.replicate n (true, 0)) =
      (score + (backlog - (backlog - n * capacity)),
        backlog - n * capacity) := by
  rw [replay_replicate_enabled_zero_arrival_eq_totalService]
  rw [ZeroArrival.totalService_eq_capped_drain,
    ZeroArrival.backlogAfter_eq_sub_mul]

/-- A disabled record at the head of a replay leaves the registers unchanged. -/
theorem replay_cons_disabled (capacity : Nat) (initial : Nat × Nat)
    (arrival : Nat) (records : List (Bool × Nat)) :
    QueueReplay.replay capacity initial ((false, arrival) :: records) =
      QueueReplay.replay capacity initial records := by
  change QueueReplay.replay capacity
    (QueueReplay.transition capacity initial (false, arrival)) records = _
  rfl

/-- A disabled record can be removed from any replay without changing either
register, even when enabled records occur before or after it. -/
theorem replay_insert_disabled (capacity : Nat) (initial : Nat × Nat)
    (before after : List (Bool × Nat)) (arrival : Nat) :
    QueueReplay.replay capacity initial (before ++ (false, arrival) :: after) =
      QueueReplay.replay capacity initial (before ++ after) := by
  calc
    QueueReplay.replay capacity initial (before ++ (false, arrival) :: after) =
        QueueReplay.replay capacity (QueueReplay.replay capacity initial before)
          ((false, arrival) :: after) := by
            rw [QueueReplay.replay_append]
    _ = QueueReplay.replay capacity (QueueReplay.replay capacity initial before) after := by
          exact replay_cons_disabled capacity _ arrival after
    _ = QueueReplay.replay capacity initial (before ++ after) := by
          rw [QueueReplay.replay_append]

end Bandits.Support.QueueDrainReplay
