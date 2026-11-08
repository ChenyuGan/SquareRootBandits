/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Basic

/-!
# Capped natural-number service

Literal service and residual identities for the integer queue update in
`sources/zip4/manuscript/04_slow_fast_learner.tex`, lines 157–172.
-/

@[expose] public section

namespace Bandits.Support.CappedService

/-- The amount served from a backlog plus an arrival, capped by capacity. -/
def service (capacity backlog arrival : ℕ) : ℕ := min capacity (backlog + arrival)

/-- The backlog left after the capped service. -/
def residual (capacity backlog arrival : ℕ) : ℕ :=
  backlog + arrival - service capacity backlog arrival

theorem service_le_capacity (capacity backlog arrival : ℕ) :
    service capacity backlog arrival ≤ capacity := by
  exact min_le_left capacity (backlog + arrival)

theorem service_le_total (capacity backlog arrival : ℕ) :
    service capacity backlog arrival ≤ backlog + arrival := by
  exact min_le_right capacity (backlog + arrival)

theorem residual_add_service (capacity backlog arrival : ℕ) :
    residual capacity backlog arrival + service capacity backlog arrival =
      backlog + arrival := by
  exact Nat.sub_add_cancel (service_le_total capacity backlog arrival)

theorem residual_eq_sub_capacity (capacity backlog arrival : ℕ) :
    residual capacity backlog arrival = (backlog + arrival) - capacity := by
  dsimp [residual, service]
  by_cases h : capacity ≤ backlog + arrival
  · rw [min_eq_left h]
  · have h' : backlog + arrival ≤ capacity := Nat.le_of_not_ge h
    rw [min_eq_right h']
    simp [Nat.sub_eq_zero_of_le h']

theorem residual_eq_zero_iff_total_le_capacity (capacity backlog arrival : ℕ) :
    residual capacity backlog arrival = 0 ↔ backlog + arrival ≤ capacity := by
  rw [residual_eq_sub_capacity]
  exact Nat.sub_eq_zero_iff_le

end Bandits.Support.CappedService

end
