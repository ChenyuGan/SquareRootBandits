module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.MinMax

/-!
Internal helper for enabled rounds with zero arrivals. The source queue rule is
given in `sources/zip4/manuscript/04_slow_fast_learner.tex:154-172`; it also
states that service continues on enabled DOWN and UP rounds without arrivals,
while disabled rounds set service to zero and preserve queues, in
`sources/zip4/manuscript/06_interruptions.tex:96-101`.

This module models only the enabled zero-arrival case: a backlog is reduced by
the service cap on each round, down to zero, and the actually served amount is
counted toward cumulative service.
-/

@[expose] public section

namespace Bandits.Support.ZeroArrival

/-- Backlog after `n` enabled rounds, each with zero arrivals and cap `c`. -/
def backlogAfter (c q n : Nat) : Nat := (fun b => b - c)^[n] q

/-- Service on the next enabled zero-arrival round from the current backlog. -/
def serviceInRound (c q n : Nat) : Nat := min c (backlogAfter c q n)

/-- Total service during the first `n` enabled zero-arrival rounds. -/
def totalService (c q : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => totalService c q n + serviceInRound c q n

/-- One enabled zero-arrival round subtracts the capped service from the backlog. -/
theorem backlogAfter_succ (c q n : Nat) :
    backlogAfter c q (Nat.succ n) = backlogAfter c q n - c := by
  change (fun b : Nat => b - c)^[Nat.succ n] q =
    ((fun b : Nat => b - c)^[n] q) - c
  rw [Function.iterate_succ_apply']

/-- After `n` enabled zero-arrival rounds, the remaining backlog is `q - n*c`. -/
theorem backlogAfter_eq_sub_mul (c q n : Nat) :
    backlogAfter c q n = q - n * c := by
  induction n with
  | zero => simp [backlogAfter]
  | succ n ih =>
      rw [backlogAfter_succ, ih]
      calc
        q - n * c - c = q - (n * c + c) := by rw [Nat.sub_sub]
        _ = q - (c + n * c) := by rw [Nat.add_comm]
        _ = q - Nat.succ n * c := by rw [Nat.succ_mul, Nat.add_comm (n * c) c]

/-- In one enabled round, service plus the remaining backlog equals the old backlog. -/
theorem roundService_add_backlog (c b : Nat) : min c b + (b - c) = b := by
  rcases Nat.le_total c b with h | h
  · rw [min_eq_left h, Nat.add_comm]
    exact Nat.sub_add_cancel h
  · rw [min_eq_right h]
    simp only [Nat.sub_eq_zero_of_le h, Nat.add_zero]

/-- The recursive cumulative service has its expected zero and successor equations. -/
@[simp] theorem totalService_zero (c q : Nat) : totalService c q 0 = 0 := rfl

@[simp] theorem totalService_succ (c q n : Nat) :
    totalService c q (Nat.succ n) = totalService c q n + serviceInRound c q n := rfl

/-- Cumulative enabled service and current backlog conserve the initial amount. -/
theorem totalService_add_backlog (c q n : Nat) :
    totalService c q n + backlogAfter c q n = q := by
  induction n with
  | zero => simp [backlogAfter]
  | succ n ih =>
      rw [totalService_succ, backlogAfter_succ]
      calc
        totalService c q n + serviceInRound c q n + (backlogAfter c q n - c) =
            totalService c q n + (serviceInRound c q n + (backlogAfter c q n - c)) := by
          rw [Nat.add_assoc]
        _ = totalService c q n + backlogAfter c q n := by
          rw [serviceInRound, roundService_add_backlog]
        _ = q := ih

/-- Total enabled service is the initial backlog minus the remaining backlog. -/
theorem totalService_eq_initial_sub_backlog (c q n : Nat) :
    totalService c q n = q - backlogAfter c q n :=
  Nat.eq_sub_of_add_eq (totalService_add_backlog c q n)

/-- Total service after `n` enabled zero-arrival rounds is `q - (q - n*c)`. -/
theorem totalService_eq_capped_drain (c q n : Nat) :
    totalService c q n = q - (q - n * c) := by
  rw [totalService_eq_initial_sub_backlog, backlogAfter_eq_sub_mul]

end Bandits.Support.ZeroArrival
