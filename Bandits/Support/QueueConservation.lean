module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Queue conservation helpers

These generic recurrence identities capture the arithmetic of the queue update and
conservation equation in `sources/zip4/manuscript/04_slow_fast_learner.tex:154-172`.
They are internal mathematical helpers and do not close a manuscript theorem.
-/

public section

namespace Bandits.Support.QueueConservation

/-- Summing the queue recurrence gives initial backlog plus arrivals as final
backlog plus total service. -/
theorem backlog_add_sum_service_eq_initial_add_sum_arrivals
    (backlog arrivals service : ℕ → ℕ)
    (hservice : ∀ t, service t ≤ backlog t + arrivals t)
    (hbacklog : ∀ t, backlog (t + 1) = backlog t + arrivals t - service t)
    (n : ℕ) :
    backlog n + (∑ t ∈ Finset.range n, service t) =
      backlog 0 + (∑ t ∈ Finset.range n, arrivals t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hbacklog n]
      have hservice_n := hservice n
      omega

/-- If score grows by the served amount while backlog follows its queue
recurrence, their sum is initial score and backlog plus cumulative arrivals. -/
theorem score_add_backlog_eq_initial_total_add_sum_arrivals
    (score backlog arrivals service : ℕ → ℕ)
    (hservice : ∀ t, service t ≤ backlog t + arrivals t)
    (hbacklog : ∀ t, backlog (t + 1) = backlog t + arrivals t - service t)
    (hscore : ∀ t, score (t + 1) = score t + service t)
    (n : ℕ) :
    score n + backlog n =
      score 0 + backlog 0 + (∑ t ∈ Finset.range n, arrivals t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, hscore n, hbacklog n]
      have hservice_n := hservice n
      omega

end Bandits.Support.QueueConservation
