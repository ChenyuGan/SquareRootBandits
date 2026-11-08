/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapBlockConstruction
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fixed-state private bootstrap block isolation

At a fixed positive numerator state for each follower, this module forms the
finite independent product of the accepted one-follower private block-draw
laws. It proves the exact mass of the event that a distinguished follower is
active on a specified arm while every other uninformed follower is inactive,
including the private-ID joint formula and the source's one-quarter bound.

The product coordinates outside the uninformed set are latent analysis
coordinates used to write a full finite product. This module does not assert
that informed followers make bootstrap draws, or that real activation histories
have this fixed-prior-state law. Sources:
`sources/zip4/manuscript/07_public_setup.tex:27-38` and
`sources/zip4/manuscript/appendix_b_communication.tex:376-403,510-568`.
-/

public section

namespace Bandits.Support.BootstrapBlockIsolation

open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapWeightPotential
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.ConstructorDimensions
open scoped BigOperators

/-- The product of the accepted fixed-state activity, held-arm, and private-ID
laws over the actual follower carrier `Fin (p.m - 1)`. Each factor uses the
same constructor parameter `p` and its own visible numerator vector. -/
theorem privateBlockProfileMass_sum_eq_one (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a) :
    (∑ profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p),
      ∏ j : Fin (p.m - 1),
        privateBlockDrawLaw p (n j) (hn j) (profile j)) = 1 := by
  classical
  calc
    _ = ∏ j : Fin (p.m - 1),
        ∑ outcome : Bool × Fin p.K × Fin (A_id p),
          privateBlockDrawLaw p (n j) (hn j) outcome :=
      (Fintype.prod_sum (f := fun j outcome =>
        privateBlockDrawLaw p (n j) (hn j) outcome)).symm
    _ = ∏ j : Fin (p.m - 1), (1 : ENNReal) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [← tsum_fintype (L := SummationFilter.unconditional _)]
      exact PMF.tsum_coe (privateBlockDrawLaw p (n j) (hn j))
    _ = 1 := by simp

/-- The literal finite independent product of each follower's existing
`privateBlockDrawLaw`. Its normalization is proved by
`privateBlockProfileMass_sum_eq_one`. -/
@[expose] noncomputable def privateBlockProfileLaw (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a) :
    PMF (Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :=
  PMF.ofFintype
    (fun profile =>
      ∏ j : Fin (p.m - 1), privateBlockDrawLaw p (n j) (hn j) (profile j))
    (privateBlockProfileMass_sum_eq_one p n hn)

/-- The complete joint atom law is the product of the actual one-follower
private block-draw atom laws. -/
theorem privateBlockProfileLaw_apply (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :
    privateBlockProfileLaw p n hn profile =
      ∏ j : Fin (p.m - 1), privateBlockDrawLaw p (n j) (hn j) (profile j) := by
  rfl

/-- The product atom's real mass is the product of the real factor masses. -/
theorem privateBlockProfileLaw_toReal_apply (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :
    (privateBlockProfileLaw p n hn profile).toReal =
      ∏ j : Fin (p.m - 1),
        (privateBlockDrawLaw p (n j) (hn j) (profile j)).toReal := by
  rw [privateBlockProfileLaw_apply, ENNReal.toReal_prod]

/-- Finite event mass for one follower's existing private draw law. -/
@[expose] noncomputable def privateBlockDrawEventMass
    (p : Parameters) (n : Fin p.K → ℕ)
    (hn : ∀ a, 1 ≤ weight (b_N p) n a)
    (event : (Bool × Fin p.K × Fin (A_id p)) → Prop) : ℝ := by
  classical
  exact ∑ outcome, if event outcome then
    (privateBlockDrawLaw p n hn outcome).toReal else 0

/-- Finite event probability on the explicitly constructed joint PMF. -/
@[expose] noncomputable def privateBlockProfileEventProbability
    (p : Parameters) (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (event : (Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) → Prop) : ℝ := by
  classical
  exact ∑ profile, if event profile then
    (privateBlockProfileLaw p n hn profile).toReal else 0

/-- Event probabilities for coordinatewise conditions factor because the
joint PMF was constructed as the finite product. -/
theorem privateBlockProfileEventProbability_forall
    (p : Parameters) (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (condition : Fin (p.m - 1) →
      (Bool × Fin p.K × Fin (A_id p)) → Prop) :
    privateBlockProfileEventProbability p n hn
        (fun profile => ∀ j, condition j (profile j)) =
      ∏ j : Fin (p.m - 1),
        privateBlockDrawEventMass p (n j) (hn j) (condition j) := by
  classical
  unfold privateBlockProfileEventProbability privateBlockDrawEventMass
  calc
    _ = ∑ profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p),
        if (∀ j, condition j (profile j)) then
          ∏ j : Fin (p.m - 1),
            (privateBlockDrawLaw p (n j) (hn j) (profile j)).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro profile hprofile
      simp only [privateBlockProfileLaw_toReal_apply]
    _ = ∑ profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p),
        ∏ j : Fin (p.m - 1),
          if condition j (profile j) then
            (privateBlockDrawLaw p (n j) (hn j) (profile j)).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro profile hprofile
      rw [Fintype.prod_ite_zero]
      by_cases h : ∀ j, condition j (profile j) <;> simp [h]
    _ = ∏ j : Fin (p.m - 1),
        ∑ outcome : Bool × Fin p.K × Fin (A_id p),
          if condition j outcome then
            (privateBlockDrawLaw p (n j) (hn j) outcome).toReal else 0 :=
      (Fintype.prod_sum (f := fun j outcome =>
        if condition j outcome then
          (privateBlockDrawLaw p (n j) (hn j) outcome).toReal else 0)).symm

/-- A draw is active and held on `a`; its private ID is intentionally left
unrestricted. -/
@[expose] def distinguishedEvent {p : Parameters}
    (i : Fin (p.m - 1)) (a : Fin p.K)
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) : Prop :=
  (profile i).1 = true ∧ (profile i).2.1 = a

/-- Every member of `U` except the distinguished follower is inactive. -/
@[expose] def otherUninformedInactiveEvent {p : Parameters}
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1))
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) : Prop :=
  ∀ j ∈ U.erase i, (profile j).1 = false

/-- The isolation event is the distinguished active-arm event intersected
with inactivity of every other uninformed follower. -/
@[expose] def isolatedBootstrapEvent {p : Parameters}
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (a : Fin p.K)
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) : Prop :=
  distinguishedEvent i a profile ∧ otherUninformedInactiveEvent U i profile

/-- Coordinatewise version of the distinguished event intersected with the
other uninformed followers' inactivity event. Coordinates outside `U` are
unconstrained latent variables. -/
@[expose] def isolationCoordinateEvent {p : Parameters}
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (a : Fin p.K)
    (j : Fin (p.m - 1)) (outcome : Bool × Fin p.K × Fin (A_id p)) : Prop :=
  if j = i then outcome.1 = true ∧ outcome.2.1 = a
  else if j ∈ U.erase i then outcome.1 = false else True

/-- Coordinatewise isolation condition with a fixed distinguished private ID.
-/
@[expose] def isolationPrivateIdCoordinateEvent {p : Parameters}
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (a : Fin p.K)
    (u : Fin (A_id p)) (j : Fin (p.m - 1))
    (outcome : Bool × Fin p.K × Fin (A_id p)) : Prop :=
  if j = i then outcome.1 = true ∧ outcome.2.1 = a ∧ outcome.2.2 = u
  else if j ∈ U.erase i then outcome.1 = false else True

/-- The joint isolation event is exactly the conjunction of its coordinate
conditions. -/
theorem isolatedBootstrapEvent_iff_forall_coordinate
    {p : Parameters} (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1))
    (a : Fin p.K) (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :
    isolatedBootstrapEvent U i a profile ↔
      ∀ j, isolationCoordinateEvent U i a j (profile j) := by
  classical
  constructor
  · rintro ⟨hE, hI⟩ j
    by_cases hji : j = i
    · subst j
      simpa [isolationCoordinateEvent, distinguishedEvent] using hE
    · by_cases hU : j ∈ U.erase i
      · simp [isolationCoordinateEvent, hji, hU, hI j hU]
      · simp [isolationCoordinateEvent, hji, hU]
  · intro h
    constructor
    · have hi := h i
      simpa [isolationCoordinateEvent, distinguishedEvent] using hi
    · intro j hj
      have hji : j ≠ i := by
        intro hEq
        subst j
        simp at hj
      have hj' := h j
      simpa [isolationCoordinateEvent, hji, hj] using hj'

/-- Function-level form of `isolatedBootstrapEvent_iff_forall_coordinate`.
-/
theorem isolatedBootstrapEvent_eq_forall_coordinate
    {p : Parameters} (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1))
    (a : Fin p.K) :
    isolatedBootstrapEvent U i a =
      fun profile => ∀ j, isolationCoordinateEvent U i a j (profile j) := by
  funext profile
  exact propext (isolatedBootstrapEvent_iff_forall_coordinate U i a profile)

/-- The joint isolation and distinguished-ID event is exactly its
coordinatewise condition. -/
theorem isolatedBootstrapPrivateIdEvent_iff_forall_coordinate
    {p : Parameters} (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1))
    (a : Fin p.K) (u : Fin (A_id p))
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :
    (isolatedBootstrapEvent U i a profile ∧ (profile i).2.2 = u) ↔
      ∀ j, isolationPrivateIdCoordinateEvent U i a u j (profile j) := by
  classical
  constructor
  · rintro ⟨⟨hE, hI⟩, hID⟩ j
    by_cases hji : j = i
    · subst j
      simpa [isolationPrivateIdCoordinateEvent, distinguishedEvent] using
        ⟨hE.1, hE.2, hID⟩
    · by_cases hU : j ∈ U.erase i
      · simp [isolationPrivateIdCoordinateEvent, hji, hU, hI j hU]
      · simp [isolationPrivateIdCoordinateEvent, hji, hU]
  · intro h
    have hi := h i
    have hEi : (profile i).1 = true ∧ (profile i).2.1 = a ∧
        (profile i).2.2 = u := by
      simpa [isolationPrivateIdCoordinateEvent] using hi
    refine ⟨?_, hEi.2.2⟩
    change distinguishedEvent i a profile ∧ otherUninformedInactiveEvent U i profile
    refine ⟨?_, ?_⟩
    · change (profile i).1 = true ∧ (profile i).2.1 = a
      exact ⟨hEi.1, hEi.2.1⟩
    intro j hj
    have hji : j ≠ i := by
      intro hEq
      subst j
      simp at hj
    have hj' := h j
    simpa [isolationPrivateIdCoordinateEvent, hji, hj] using hj'

/-- Function-level form of `isolatedBootstrapPrivateIdEvent_iff_forall_coordinate`.
-/
theorem isolatedBootstrapPrivateIdEvent_eq_forall_coordinate
    {p : Parameters} (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1))
    (a : Fin p.K) (u : Fin (A_id p)) :
    (fun profile => isolatedBootstrapEvent U i a profile ∧
      (profile i).2.2 = u) =
      fun profile => ∀ j, isolationPrivateIdCoordinateEvent U i a u j (profile j) := by
  funext profile
  exact propext (isolatedBootstrapPrivateIdEvent_iff_forall_coordinate U i a u profile)

/-- The distinguished event, with all other follower coordinates
unconstrained. -/
@[expose]
def distinguishedCoordinateEvent {p : Parameters}
    (i : Fin (p.m - 1)) (a : Fin p.K) (j : Fin (p.m - 1))
    (outcome : Bool × Fin p.K × Fin (A_id p)) : Prop :=
  if j = i then outcome.1 = true ∧ outcome.2.1 = a else True

theorem distinguishedEvent_iff_forall_coordinate
    {p : Parameters} (i : Fin (p.m - 1)) (a : Fin p.K)
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :
    distinguishedEvent i a profile ↔
      ∀ j, distinguishedCoordinateEvent i a j (profile j) := by
  classical
  constructor
  · intro h j
    by_cases hji : j = i
    · subst j
      simpa [distinguishedCoordinateEvent, distinguishedEvent] using h
    · simp [distinguishedCoordinateEvent, hji]
  · intro h
    have hi := h i
    change distinguishedEvent i a profile
    simpa [distinguishedCoordinateEvent, distinguishedEvent] using hi

/-- Function-level form of `distinguishedEvent_iff_forall_coordinate`. -/
theorem distinguishedEvent_eq_forall_coordinate
    {p : Parameters} (i : Fin (p.m - 1)) (a : Fin p.K) :
    distinguishedEvent i a =
      fun profile => ∀ j, distinguishedCoordinateEvent i a j (profile j) := by
  funext profile
  exact propext (distinguishedEvent_iff_forall_coordinate i a profile)

/-- The finite real mass of the single-follower active-on-arm event. -/
theorem privateBlockDrawLaw_active_arm_event_mass (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) (a : Fin p.K) :
    (∑ outcome : Bool × Fin p.K × Fin (A_id p),
      if outcome.1 = true ∧ outcome.2.1 = a then
        (privateBlockDrawLaw p n hn outcome).toReal else 0) =
      probability (b_N p) n a / (p.m : ℝ) := by
  classical
  simp_rw [privateBlockDrawLaw_toReal_apply]
  simp only [Fintype.sum_prod_type]
  simp [privateDrawMass, privateIdProbability, activityProbability]
  field_simp [Nat.cast_ne_zero.mpr (A_id_pos p).ne',
    Nat.cast_ne_zero.mpr (m_pos p).ne']

/-- The finite real mass of a single-follower inactive event. -/
theorem privateBlockDrawLaw_inactive_event_mass (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    (∑ outcome : Bool × Fin p.K × Fin (A_id p),
      if outcome.1 = false then
        (privateBlockDrawLaw p n hn outcome).toReal else 0) =
      activityProbability p false := by
  classical
  simpa [Fintype.sum_prod_type, Fintype.sum_bool] using
    privateBlockDrawLaw_activity_marginal p n hn false

/-- The finite real masses of all single-follower outcomes sum to one. -/
theorem privateBlockDrawLaw_real_mass_sum_eq_one (p : Parameters)
    (n : Fin p.K → ℕ) (hn : ∀ a, 1 ≤ weight (b_N p) n a) :
    (∑ outcome : Bool × Fin p.K × Fin (A_id p),
      (privateBlockDrawLaw p n hn outcome).toReal) = 1 := by
  classical
  simp_rw [privateBlockDrawLaw_toReal_apply]
  exact privateDrawMass_sum_eq_one p n hn

/-- Real mass of one coordinate's condition in the isolation event. -/
theorem isolationCoordinateEvent_mass {p : Parameters}
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i j : Fin (p.m - 1)) (a : Fin p.K) :
    privateBlockDrawEventMass p (n j) (hn j) (isolationCoordinateEvent U i a j) =
      if j = i then probability (b_N p) (n i) a / (p.m : ℝ)
      else if j ∈ U.erase i then activityProbability p false else 1 := by
  classical
  unfold privateBlockDrawEventMass
  by_cases hji : j = i
  · subst j
    simp [isolationCoordinateEvent,
      privateBlockDrawLaw_active_arm_event_mass]
  · by_cases hU : j ∈ U.erase i
    · simp [isolationCoordinateEvent, hji, hU,
        privateBlockDrawLaw_inactive_event_mass]
    · simp [isolationCoordinateEvent, hji, hU,
        privateBlockDrawLaw_real_mass_sum_eq_one]

/-- Real mass of one coordinate's condition in the isolation event with a
fixed distinguished ID. -/
theorem isolationPrivateIdCoordinateEvent_mass {p : Parameters}
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i j : Fin (p.m - 1)) (a : Fin p.K)
    (u : Fin (A_id p)) :
    privateBlockDrawEventMass p (n j) (hn j)
      (isolationPrivateIdCoordinateEvent U i a u j) =
      if j = i then privateDrawMass p (n i) (true, a, u)
      else if j ∈ U.erase i then activityProbability p false else 1 := by
  classical
  unfold privateBlockDrawEventMass
  by_cases hji : j = i
  · subst j
    simp only [isolationPrivateIdCoordinateEvent, ↓reduceIte,
      Fintype.sum_prod_type, privateBlockDrawLaw_toReal_apply]
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, false_and, true_and, ↓reduceIte]
    simp only [Finset.sum_const_zero, add_zero]
    calc
      _ = ∑ arm : Fin p.K,
          if arm = a then privateDrawMass p (n i) (true, a, u) else 0 := by
        apply Finset.sum_congr rfl
        intro arm harm
        by_cases ha : arm = a
        · subst arm
          simp
        · simp [ha]
      _ = privateDrawMass p (n i) (true, a, u) := by simp
  · by_cases hU : j ∈ U.erase i
    · simp [isolationPrivateIdCoordinateEvent, hji, hU,
        privateBlockDrawLaw_inactive_event_mass]
    · simp [isolationPrivateIdCoordinateEvent, hji, hU,
        privateBlockDrawLaw_real_mass_sum_eq_one]

/-- Real mass of one coordinate's condition in the distinguished event. -/
theorem distinguishedCoordinateEvent_mass {p : Parameters}
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (i j : Fin (p.m - 1)) (a : Fin p.K) :
    privateBlockDrawEventMass p (n j) (hn j)
      (distinguishedCoordinateEvent i a j) =
      if j = i then probability (b_N p) (n i) a / (p.m : ℝ) else 1 := by
  classical
  unfold privateBlockDrawEventMass
  by_cases hji : j = i
  · subst j
    simp [distinguishedCoordinateEvent,
      privateBlockDrawLaw_active_arm_event_mass]
  · simp [distinguishedCoordinateEvent, hji,
      privateBlockDrawLaw_real_mass_sum_eq_one]

private theorem isolation_marginal_product_eq (p : Parameters)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (e q : ℝ) :
    (∏ j : Fin (p.m - 1),
      if j = i then e else if j ∈ U.erase i then q else 1) =
      e * q ^ (U.card - 1) := by
  classical
  have hiErase : i ∉ U.erase i := by simp
  calc
    _ = ∏ j : Fin (p.m - 1),
        (if j = i then e else 1) *
          (if j ∈ U.erase i then q else 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases hji : j = i
      · simp [hji, hiErase]
      · simp [hji]
    _ = (∏ j : Fin (p.m - 1), if j = i then e else 1) *
        (∏ j : Fin (p.m - 1), if j ∈ U.erase i then q else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = e * q ^ (U.card - 1) := by
      rw [Finset.prod_ite_eq', Finset.prod_ite_mem_eq]
      simp [Finset.card_erase_of_mem hi]

/-- The exact probability of the distinguished follower being active on arm
`a`. -/
theorem distinguishedEvent_probability (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (i : Fin (p.m - 1)) (a : Fin p.K) :
    privateBlockProfileEventProbability p n hn (distinguishedEvent i a) =
      probability (b_N p) (n i) a / (p.m : ℝ) := by
  classical
  rw [distinguishedEvent_eq_forall_coordinate i a]
  rw [privateBlockProfileEventProbability_forall]
  simp_rw [distinguishedCoordinateEvent_mass]
  simp

/-- The distinguished event has positive mass, so conditioning on it is
well-defined. -/
theorem distinguishedEvent_probability_pos (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (i : Fin (p.m - 1)) (a : Fin p.K) :
    0 < privateBlockProfileEventProbability p n hn (distinguishedEvent i a) := by
  rw [distinguishedEvent_probability]
  exact div_pos (heldArmProbability_pos p (n i) a)
    (Nat.cast_pos.mpr (m_pos p))

/-- The exact real joint mass of the isolation event. Its only state-dependent
factor is the distinguished follower's held-arm law; every other coordinate
contributes only its activity marginal or the normalizing mass one. -/
theorem isolatedBootstrapEvent_probability (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) :
    privateBlockProfileEventProbability p n hn (isolatedBootstrapEvent U i a) =
      (probability (b_N p) (n i) a / (p.m : ℝ)) *
        (1 - 1 / (p.m : ℝ)) ^ (U.card - 1) := by
  classical
  rw [isolatedBootstrapEvent_eq_forall_coordinate U i a]
  rw [privateBlockProfileEventProbability_forall]
  simp_rw [isolationCoordinateEvent_mass]
  rw [isolation_marginal_product_eq p U i hi
    (probability (b_N p) (n i) a / (p.m : ℝ)) (activityProbability p false)]
  simp [activityProbability]

/-- The isolated-event probability is unchanged when any follower state other
than `i` changes. In particular, latent coordinates for informed followers do
not affect the event law. -/
theorem isolatedBootstrapEvent_probability_state_irrel (p : Parameters)
    (n n' : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (hn' : ∀ j a, 1 ≤ weight (b_N p) (n' j) a)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) (hni : n i = n' i) :
    privateBlockProfileEventProbability p n hn (isolatedBootstrapEvent U i a) =
      privateBlockProfileEventProbability p n' hn'
        (isolatedBootstrapEvent U i a) := by
  rw [isolatedBootstrapEvent_probability p n hn U i hi a,
    isolatedBootstrapEvent_probability p n' hn' U i hi a, hni]

/-- The exact joint event probability when the distinguished private ID is
fixed to `u`, retaining its uniform factor jointly with both isolation events.
-/
theorem isolatedBootstrapEvent_privateId_probability (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) (u : Fin (A_id p)) :
    privateBlockProfileEventProbability p n hn
      (fun profile => isolatedBootstrapEvent U i a profile ∧
        (profile i).2.2 = u) =
      ((probability (b_N p) (n i) a / (p.m : ℝ)) *
        privateIdProbability p u) *
        (1 - 1 / (p.m : ℝ)) ^ (U.card - 1) := by
  classical
  rw [isolatedBootstrapPrivateIdEvent_eq_forall_coordinate U i a u]
  rw [privateBlockProfileEventProbability_forall]
  simp_rw [isolationPrivateIdCoordinateEvent_mass]
  rw [isolation_marginal_product_eq p U i hi
    (privateDrawMass p (n i) (true, a, u)) (activityProbability p false)]
  rw [privateDrawMass]
  simp only [activityProbability, Bool.false_eq_true, ↓reduceIte]
  ring

/-- The distinguished private ID is uniform jointly with the active-arm and
isolation events. -/
theorem isolatedBootstrapEvent_privateId_independent (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) (u : Fin (A_id p)) :
    privateBlockProfileEventProbability p n hn
      (fun profile => isolatedBootstrapEvent U i a profile ∧
        (profile i).2.2 = u) =
      privateBlockProfileEventProbability p n hn
        (isolatedBootstrapEvent U i a) * privateIdProbability p u := by
  rw [isolatedBootstrapEvent_privateId_probability p n hn U i hi a u,
    isolatedBootstrapEvent_probability p n hn U i hi a]
  field_simp [Nat.cast_ne_zero.mpr (A_id_pos p).ne',
    Nat.cast_ne_zero.mpr (m_pos p).ne']

/-- Conditioning on the distinguished active-arm event, the other uninformed
followers are all inactive with the exact product probability. -/
theorem isolation_conditional_probability (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) :
    privateBlockProfileEventProbability p n hn (isolatedBootstrapEvent U i a) /
      privateBlockProfileEventProbability p n hn (distinguishedEvent i a) =
      (1 - 1 / (p.m : ℝ)) ^ (U.card - 1) := by
  rw [isolatedBootstrapEvent_probability p n hn U i hi a,
    distinguishedEvent_probability p n hn i a]
  have hden : 0 < probability (b_N p) (n i) a / (p.m : ℝ) :=
    div_pos (heldArmProbability_pos p (n i) a)
      (Nat.cast_pos.mpr (m_pos p))
  rw [div_eq_iff hden.ne']
  ring

/-- The real follower carrier bounds the number of other uninformed
followers, including the boundary case `m = 2` and `U = {i}`. -/
theorem otherUninformed_count_le (p : Parameters)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U) :
    U.card - 1 ≤ p.m - 2 := by
  have hU : U.card ≤ p.m - 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ U
  have hnonempty : 1 ≤ U.card := Finset.one_le_card.mpr ⟨i, hi⟩
  omega

/-- Elementary isolation power bound. Mathlib's exponential bound
`(1 + 1/n)^n ≤ exp 1 < 3` supplies a direct reciprocal proof. -/
theorem inactivity_power_lower_bound (p : Parameters) :
    (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) ≥ 1 / 4 := by
  have hm1 : 1 ≤ p.m := le_trans (by decide) p.two_le_m
  have hmpos : (0 : ℝ) < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
  have hsubcast : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
    rw [Nat.cast_sub hm1]
    norm_num
  let x : ℝ := 1 + ((p.m - 1 : ℕ) : ℝ)⁻¹
  have hx : 1 ≤ x := by
    dsimp [x]
    exact le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hn : p.m - 2 ≤ p.m - 1 := by omega
  have hpow : x ^ (p.m - 2) ≤ x ^ (p.m - 1) :=
    pow_le_pow_right₀ hx hn
  have hexp : x ^ (p.m - 1) ≤ Real.exp 1 := by
    dsimp [x]
    exact Real.one_add_inv_pow_le_exp
  have hden : x ^ (p.m - 2) < 3 :=
    (hpow.trans hexp).trans_lt Real.exp_one_lt_three
  have hsubpos : 0 < (p.m : ℝ) - 1 := by
    have hmNat : 1 < p.m := lt_of_lt_of_le (by decide) p.two_le_m
    have hmReal : (1 : ℝ) < (p.m : ℝ) := by exact_mod_cast hmNat
    exact sub_pos.mpr hmReal
  have hq : 1 - 1 / (p.m : ℝ) = x⁻¹ := by
    dsimp [x]
    rw [hsubcast]
    field_simp [hmpos.ne', hsubpos.ne']
    ; ring
  have hinv : (1 / 3 : ℝ) < (x ^ (p.m - 2))⁻¹ := by
    simpa [one_div] using
      (one_div_lt_one_div_of_lt
        (a := x ^ (p.m - 2)) (b := (3 : ℝ))
        (pow_pos (by linarith [hx]) _) hden)
  exact (calc
    (1 / 4 : ℝ) ≤ 1 / 3 := by norm_num
    _ < (x ^ (p.m - 2))⁻¹ := hinv
    _ = (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) := by
      rw [hq, inv_pow]).le

/-- The exact conditional isolation probability is at least one quarter for
every accepted `m`, including `m = 2`. -/
theorem isolation_conditional_probability_ge_one_fourth (p : Parameters)
    (n : Fin (p.m - 1) → Fin p.K → ℕ)
    (hn : ∀ j a, 1 ≤ weight (b_N p) (n j) a)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) :
    1 / 4 ≤ privateBlockProfileEventProbability p n hn
        (isolatedBootstrapEvent U i a) /
          privateBlockProfileEventProbability p n hn (distinguishedEvent i a) := by
  rw [isolation_conditional_probability p n hn U i hi a]
  have hq : 0 ≤ 1 - 1 / (p.m : ℝ) := by
    exact (activityProbability_pos p false).le
  have hq_one : 1 - 1 / (p.m : ℝ) ≤ 1 := by
    have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
    have hinv : 0 ≤ 1 / (p.m : ℝ) := by positivity
    linarith
  have hcount := otherUninformed_count_le p U i hi
  calc
    (1 / 4 : ℝ) ≤ (1 - 1 / (p.m : ℝ)) ^ (p.m - 2) :=
      inactivity_power_lower_bound p
    _ ≤ (1 - 1 / (p.m : ℝ)) ^ (U.card - 1) :=
      pow_le_pow_of_le_one hq hq_one hcount

/-- Actual calendar-prefix product law: every factor's positive-state
invariant is discharged internally by `blockRun_weight_ge_one`. -/
@[expose] noncomputable def constructedBlockProfileLaw {p : Parameters}
    (traces : Fin (p.m - 1) → ExplicitTrace p)
    (r : ℕ) (hr : r ≤ n_boot p) :
    PMF (Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :=
  privateBlockProfileLaw p (fun j => blockRun (traces j) r)
    (fun j a => blockRun_weight_ge_one (traces j) r hr a)

/-- Full joint atom law at actual constructed calendar-prefix states. -/
theorem constructedBlockProfileLaw_apply {p : Parameters}
    (traces : Fin (p.m - 1) → ExplicitTrace p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (profile : Fin (p.m - 1) → Bool × Fin p.K × Fin (A_id p)) :
    constructedBlockProfileLaw traces r hr profile =
      ∏ j : Fin (p.m - 1),
        privateBlockDrawLaw p (blockRun (traces j) r)
          (blockRun_weight_ge_one (traces j) r hr) (profile j) := by
  rfl

/-- The source isolation formula at actual calendar-prefix states. -/
theorem constructed_isolatedBootstrapEvent_probability {p : Parameters}
    (traces : Fin (p.m - 1) → ExplicitTrace p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (U : Finset (Fin (p.m - 1))) (i : Fin (p.m - 1)) (hi : i ∈ U)
    (a : Fin p.K) :
    privateBlockProfileEventProbability p
        (fun j => blockRun (traces j) r)
        (fun j arm => blockRun_weight_ge_one (traces j) r hr arm)
        (isolatedBootstrapEvent U i a) =
      (probability (b_N p) (blockRun (traces i) r) a / (p.m : ℝ)) *
        (1 - 1 / (p.m : ℝ)) ^ (U.card - 1) := by
  exact isolatedBootstrapEvent_probability p
    (fun j => blockRun (traces j) r)
    (fun j arm => blockRun_weight_ge_one (traces j) r hr arm)
    U i hi a

end Bandits.Support.BootstrapBlockIsolation

end
