/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompleteRowStoppingLaw
public import Bandits.Support.ReferenceInitializationRun
public import Bandits.Support.ReferenceInitializationCausality
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceInitializationMeasurability
public import Bandits.Support.BootstrapPrivateRoundStreams

import Mathlib.MeasureTheory.Measure.Prod

/-!
# The actual reference launch as a selected-row stopping time

For fixed identification array, rounded rewards, constants, and positive
learning rate, this module turns the existing reference launch into a
`CompleteRowStoppingLaw.PreRoundStoppingTime`. Its side input is the existing
full `ExtendedPrivateCoordinates` product. The event functional completes a
row tail only to evaluate the already-defined launch map; prefix invariance
proves that no completion of that tail changes any launch event.

The future sigma-field retains, at every time, the full forward-ID vector and
the entire continuous `TimeControl`, including all affine coefficients and
offsets. The resulting freshness statement is before full-row revelation. It
does not expose or randomize unused private coordinates, and it is not a
conditional law after revealing a complete numerical public row.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/appendix_b_communication.tex:786-798`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-83`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationCausality
open Bandits.Support.ReferenceInitializationPrefixInvariance
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open scoped ENNReal

namespace Bandits.Support.ReferenceLaunchRowLaw

abbrev Parameters := ConstructorDimensions.Parameters

abbrev SideInput (p : Parameters) := ExtendedPrivateCoordinates p

abbrev LaunchIndex (p : Parameters) := Fin (p.T + 1)

/-- One literal scalar used only to complete the event functional's row tail. -/
def tailScalar : ContinuousLearningRows.Scalar := ⟨0, by norm_num⟩

/-- One literal continuous control sample used only in the event completion. -/
def tailTimeControl (p : Parameters) : TimeControl p :=
  ((fun _ : Label p => tailScalar),
    fun _ : Channel p => ((fun _ : Fin (B p) => (0 : Bit)), (0 : Bit)))

/-- A fixed calendar entry used only in the measurable completion of a
strict-past event functional. It is never installed into a physical run. -/
def tailEntry (p : Parameters) : CalendarEntry p :=
  ((fun _ : Fin (A_id p) => false), tailTimeControl p)

/-- Complete an event functional's missing future coordinates with a constant
value. This is an event-evaluation device, not a row or physical trajectory. -/
def completedCalendar (p : Parameters) (σ : LaunchIndex p)
    (past : PastArray p σ) : CalendarArray p :=
  (calendarSplitEquiv p σ).symm (past, fun _ => tailEntry p)

/-- Reassemble a complete-row argument for evaluating the launch event from a
strict past and the fixed completion. -/
def completedRow (p : Parameters) (σ : LaunchIndex p) (past : PastArray p σ) :
    CompletePublicTable.CompleteRow p :=
  (calendarizeRowEquiv p).symm (completedCalendar p σ past)

theorem measurable_completedCalendar (p : Parameters) (σ : LaunchIndex p) :
    Measurable (completedCalendar p σ) := by
  exact ((calendarSplitEquiv p σ).symm.measurable).comp
    (measurable_id.prodMk measurable_const)

theorem measurable_completedRow (p : Parameters) (σ : LaunchIndex p) :
    Measurable (completedRow p σ) := by
  exact (calendarizeRowEquiv p).symm.measurable.comp
    (measurable_completedCalendar p σ)

theorem calendarize_completedRow (p : Parameters) (σ : LaunchIndex p)
    (past : PastArray p σ) :
    calendarizeRow p (completedRow p σ past) = completedCalendar p σ past := by
  exact (calendarizeRowEquiv p).apply_symm_apply (completedCalendar p σ past)

theorem completedRow_agrees_on_past (p : Parameters) (σ : LaunchIndex p)
    (past : PastArray p σ) (t : PastIndex p σ) :
    calendarizeRow p (completedRow p σ past) t.1 = past t := by
  have hsplit := (calendarSplitEquiv p σ).apply_symm_apply
    (past, fun _ => tailEntry p)
  have hpast := congrArg Prod.fst hsplit
  have hcalendar := congrArg (fun r : CalendarArray p => r t.1)
    (calendarize_completedRow p σ past)
  rw [hcalendar]
  exact congrFun hpast t

/-- Private total postprocessing used only to transfer measurability from the
accepted natural-valued launch map. `actualLaunchStop` itself is the direct
bounded value `launchRound - 1`. -/
private def sourceLaunchIndex (p : Parameters) (n : ℕ) : LaunchIndex p :=
  ⟨min (n - 1) p.T, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

private theorem sourceLaunchIndex_eq_sub (p : Parameters) (n : ℕ)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ p.T + 1) :
    sourceLaunchIndex p n = ⟨n - 1, by omega⟩ := by
  apply Fin.ext
  simp only [sourceLaunchIndex, Fin.val_mk]
  exact Nat.min_eq_left (by omega)

/-- The actual existing reference input, assembled from the fixed public data
and the original private coordinates and selected complete row. -/
def actualInput (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (coordinates : SideInput p)
    (row : CompletePublicTable.CompleteRow p) : Input p :=
  inputOfCoordinates p C_star C_h eta rewards (ids, (row, coordinates))

/-- The source launch round shifted to its pre-round stopping index. The
`T+1` source sentinel, whether from no launch or a terminal launch, maps to T. -/
def actualLaunchStop (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) : SideInput p × CompletePublicTable.CompleteRow p →
      LaunchIndex p :=
  fun z => ⟨ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta z.1 z.2) - 1, by
        have hb := ReferenceInitializationRun.launchRound_bounds
          (actualInput p ids rewards C_star C_h eta z.1 z.2)
        omega⟩

theorem actualLaunchStop_eq_sub (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (z : SideInput p × CompletePublicTable.CompleteRow p) :
    actualLaunchStop p ids rewards C_star C_h eta z =
      ⟨ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta z.1 z.2) - 1, by
          have hb := ReferenceInitializationRun.launchRound_bounds
            (actualInput p ids rewards C_star C_h eta z.1 z.2)
          omega⟩ := by
  apply Fin.ext
  rfl

theorem measurable_actualLaunchStop (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) :
    Measurable (actualLaunchStop p ids rewards C_star C_h eta) := by
  have heq : actualLaunchStop p ids rewards C_star C_h eta =
      fun z => sourceLaunchIndex p
        (ReferenceInitializationRun.launchRound (actualInput p ids rewards C_star C_h eta z.1 z.2)) := by
    funext z
    apply Fin.ext
    rw [actualLaunchStop_eq_sub p ids rewards C_star C_h eta z]
    simp only [sourceLaunchIndex, Fin.val_mk]
    exact (Nat.min_eq_left (by
      have hb := ReferenceInitializationRun.launchRound_bounds
        (actualInput p ids rewards C_star C_h eta z.1 z.2)
      omega)).symm
  rw [heq]
  apply (measurable_of_countable (sourceLaunchIndex p)).comp
  exact (ReferenceInitializationMeasurability.measurable_launchRound
      p C_star C_h eta rewards).comp
    (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))

/-- The event evaluator uses exactly the given private side input and strict
past. Its only row completion is `completedRow`. -/
def launchEventAt (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) :
    SidePast (SideInput p) p σ → Bool := fun z =>
      decide (actualLaunchStop p ids rewards C_star C_h eta
        (z.1, completedRow p σ z.2) = σ)

private theorem launchPrefixInputEq_of_same_strict_past
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (coordinates : SideInput p) (σ : LaunchIndex p)
    (r₁ r₂ : CompletePublicTable.CompleteRow p)
    (hpast : ∀ t : PastIndex p σ,
      calendarizeRow p r₁ t.1 = calendarizeRow p r₂ t.1)
    {n : ℕ} (hn : n ≤ σ.val + 1) :
    ReferenceInitializationCausality.launchPrefixInputEq
      (actualInput p ids rewards C_star C_h eta coordinates r₁)
      (actualInput p ids rewards C_star C_h eta coordinates r₂) n := by
  dsimp [ReferenceInitializationCausality.launchPrefixInputEq,
    actualInput, ReferenceInitializationMeasurability.inputOfCoordinates]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro u
      have htσ : t.val < σ.val := by omega
      have he := hpast ⟨t, htσ⟩
      exact congrArg (fun x : CalendarEntry p => x.1 u) he
    · have htσ : t.val < σ.val := by omega
      have he := hpast ⟨t, htσ⟩
      exact congrArg (fun x : CalendarEntry p => x.2) he
  · intro s hs
    constructor
    · intro j
      rfl
    · rfl
  · intro i t ht
    rfl

theorem launchEventAt_eq_actual (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (coordinates : SideInput p)
    (row : CompletePublicTable.CompleteRow p) :
    launchEventAt p ids rewards C_star C_h eta σ
        (coordinates, (calendarSplitEquiv p σ (calendarizeRow p row)).1) =
      decide (actualLaunchStop p ids rewards C_star C_h eta (coordinates, row) = σ) := by
  let past := (calendarSplitEquiv p σ (calendarizeRow p row)).1
  let completed := completedRow p σ past
  let x := actualInput p ids rewards C_star C_h eta coordinates row
  let y := actualInput p ids rewards C_star C_h eta coordinates completed
  have hpast : ∀ t : PastIndex p σ,
      calendarizeRow p completed t.1 = calendarizeRow p row t.1 := by
    intro t
    calc
      calendarizeRow p completed t.1 = past t :=
        completedRow_agrees_on_past p σ past t
      _ = calendarizeRow p row t.1 := rfl
  have hprefix (n : ℕ) (hn : n ≤ σ.val + 1) :
      ReferenceInitializationCausality.launchPrefixInputEq x y n := by
    exact launchPrefixInputEq_of_same_strict_past p ids rewards C_star C_h eta
      coordinates σ row completed (fun t => (hpast t).symm) hn
  have hminus : ReferenceInitializationRun.launchRound x ≤ σ.val ↔
      ReferenceInitializationRun.launchRound y ≤ σ.val :=
    ReferenceInitializationPrefixInvariance.launchSublevel_eq_of_launchPrefixInputEq
      x y (by have := σ.isLt; omega) (hprefix σ.val (by omega))
  have hplus : ReferenceInitializationRun.launchRound x ≤ σ.val + 1 ↔
      ReferenceInitializationRun.launchRound y ≤ σ.val + 1 :=
    ReferenceInitializationPrefixInvariance.launchSublevel_eq_of_launchPrefixInputEq
      x y (by have := σ.isLt; omega) (hprefix (σ.val + 1) (by omega))
  have hstop : actualLaunchStop p ids rewards C_star C_h eta (coordinates, row) = σ ↔
      actualLaunchStop p ids rewards C_star C_h eta (coordinates, completed) = σ := by
    rw [actualLaunchStop_eq_sub p ids rewards C_star C_h eta (coordinates, row),
      actualLaunchStop_eq_sub p ids rewards C_star C_h eta (coordinates, completed)]
    simp only [Fin.ext_iff]
    change ReferenceInitializationRun.launchRound x - 1 = σ.val ↔
      ReferenceInitializationRun.launchRound y - 1 = σ.val
    have hxb := ReferenceInitializationRun.launchRound_bounds x
    have hyb := ReferenceInitializationRun.launchRound_bounds y
    constructor
    · intro hxstop
      have hxle : ReferenceInitializationRun.launchRound x ≤ σ.val + 1 := by omega
      have hxnot : ¬ ReferenceInitializationRun.launchRound x ≤ σ.val := by omega
      have hyle := hplus.mp hxle
      have hynot : ¬ ReferenceInitializationRun.launchRound y ≤ σ.val :=
        fun hy => hxnot (hminus.mpr hy)
      omega
    · intro hystop
      have hyle : ReferenceInitializationRun.launchRound y ≤ σ.val + 1 := by omega
      have hynot : ¬ ReferenceInitializationRun.launchRound y ≤ σ.val := by omega
      have hxle := hplus.mpr hyle
      have hxnot : ¬ ReferenceInitializationRun.launchRound x ≤ σ.val :=
        fun hx => hynot (hminus.mp hx)
      omega
  change decide (actualLaunchStop p ids rewards C_star C_h eta
      (coordinates, completed) = σ) =
    decide (actualLaunchStop p ids rewards C_star C_h eta (coordinates, row) = σ)
  by_cases h : actualLaunchStop p ids rewards C_star C_h eta (coordinates, row) = σ
  · have hc := hstop.mp h
    simp [h, hc]
  · have hc : actualLaunchStop p ids rewards C_star C_h eta
        (coordinates, completed) ≠ σ := fun hc => h (hstop.mpr hc)
    simp [h, hc]

/-- The actual selected-row launch and its strict-past event functional. -/
def actualReferenceLaunchStoppingTime (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) : PreRoundStoppingTime (SideInput p) p where
  stop := actualLaunchStop p ids rewards C_star C_h eta
  eventAt := launchEventAt p ids rewards C_star C_h eta
  measurable_eventAt := by
    intro σ
    exact (measurable_of_countable (fun i : LaunchIndex p => decide (i = σ))).comp
      ((measurable_actualLaunchStop p ids rewards C_star C_h eta).comp
        (measurable_fst.prodMk
          ((measurable_completedRow p σ).comp measurable_snd)))
  eventAt_eq := by
    intro σ coordinates row
    exact launchEventAt_eq_actual p ids rewards C_star C_h eta σ coordinates row

/-- The source-time shift is exact: a launch round `t` is indexed by `t-1`,
and the source sentinel `T+1` is the empty-future stopping index `T`. -/
theorem actualLaunchStop_source_shift (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (coordinates : SideInput p)
    (row : CompletePublicTable.CompleteRow p) :
    (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop
        (coordinates, row) =
      ⟨ReferenceInitializationRun.launchRound
        (actualInput p ids rewards C_star C_h eta coordinates row) - 1, by
          have hb := ReferenceInitializationRun.launchRound_bounds
            (actualInput p ids rewards C_star C_h eta coordinates row)
          omega⟩ := by
  exact actualLaunchStop_eq_sub p ids rewards C_star C_h eta (coordinates, row)

theorem actualLaunchStop_sentinel (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (coordinates : SideInput p)
    (row : CompletePublicTable.CompleteRow p)
    (hsource : ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta coordinates row) = p.T + 1) :
    (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop
      (coordinates, row) = horizonStoppingIndex p := by
  change actualLaunchStop p ids rewards C_star C_h eta (coordinates, row) =
    horizonStoppingIndex p
  apply Fin.ext
  change ReferenceInitializationRun.launchRound
      (actualInput p ids rewards C_star C_h eta coordinates row) - 1 = p.T
  rw [hsource]
  omega

/-- At source launch round `T+1`, including no launch, the stopping index is
the horizon and its strict future subtype is empty. -/
theorem source_sentinel_has_empty_future (p : Parameters) :
    IsEmpty (FutureIndex p (horizonStoppingIndex p)) :=
  futureIndexAtHorizon_isEmpty p

/-- Launch-event factorization against every measurable side/past event and
every measurable event of the entire future CalendarArray. -/
theorem actual_launch_event_factorization
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p)
    (A : Set (SidePast (SideInput p) p σ)) (hA : MeasurableSet A)
    (B : Set (FutureArray p σ)) (hB : MeasurableSet B) :
    (extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ B} =
      ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        (A ∩ {x | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).eventAt σ x = true}) *
        (futureArrayLaw p σ) B := by
  let τ := actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta
  let E : Set (SidePast (SideInput p) p σ) := {x | τ.eventAt σ x = true}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage (τ.measurable_eventAt σ)
  have hfactor := side_past_future_event_factorization
    (extendedPrivateLaw p) p σ (A ∩ E) B (hA.inter hE) hB
  have hset :
      {z | τ.stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).1 ∈ A ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ B} =
      (sideCompleteRowSplitEquiv (SideInput p) p σ) ⁻¹' ((A ∩ E) ×ˢ B) := by
    ext z
    rcases z with ⟨coordinates, row⟩
    let past := (calendarSplitEquiv p σ (calendarizeRow p row)).1
    let future := (calendarSplitEquiv p σ (calendarizeRow p row)).2
    change (τ.stop (coordinates, row) = σ ∧ (coordinates, past) ∈ A ∧ future ∈ B) ↔
      (((coordinates, past) ∈ A ∧ τ.eventAt σ (coordinates, past) = true) ∧ future ∈ B)
    have hevent := τ.eventAt_eq σ coordinates row
    change τ.eventAt σ (coordinates, past) = decide (τ.stop (coordinates, row) = σ) at hevent
    rw [hevent]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hp, ha, hb⟩
      exact ⟨⟨ha, hp⟩, hb⟩
    · rintro ⟨⟨ha, hp⟩, hb⟩
      exact ⟨hp, ha, hb⟩
  rw [hset]
  exact hfactor

/-- Any two complete-row tail choices with the same strict past give the same
launch event. Thus the constant completion used by `launchEventAt` has no
effect on the event's value. -/
theorem actual_launch_event_invariant_under_tail_completion
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p) (coordinates : SideInput p)
    (r₁ r₂ : CompletePublicTable.CompleteRow p)
    (hpast : ∀ t : PastIndex p σ,
      calendarizeRow p r₁ t.1 = calendarizeRow p r₂ t.1) :
    decide (actualLaunchStop p ids rewards C_star C_h eta (coordinates, r₁) = σ) =
      decide (actualLaunchStop p ids rewards C_star C_h eta (coordinates, r₂) = σ) := by
  have hpastEq :
      (calendarSplitEquiv p σ (calendarizeRow p r₁)).1 =
        (calendarSplitEquiv p σ (calendarizeRow p r₂)).1 := by
    funext t
    exact hpast t
  calc
    decide (actualLaunchStop p ids rewards C_star C_h eta (coordinates, r₁) = σ) =
        launchEventAt p ids rewards C_star C_h eta σ
          (coordinates, (calendarSplitEquiv p σ (calendarizeRow p r₁)).1) :=
      (launchEventAt_eq_actual p ids rewards C_star C_h eta σ coordinates r₁).symm
    _ = launchEventAt p ids rewards C_star C_h eta σ
        (coordinates, (calendarSplitEquiv p σ (calendarizeRow p r₂)).1) := by
          rw [hpastEq]
    _ = decide (actualLaunchStop p ids rewards C_star C_h eta (coordinates, r₂) = σ) :=
      launchEventAt_eq_actual p ids rewards C_star C_h eta σ coordinates r₂

/-- Bounded measurable tests of the complete side/past and the whole future
factor at each actual launch index. This directly consumes the generic
stopping-event integral factorization for the produced stop. -/
theorem actual_launch_bounded_test_integral_factorization
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p)
    (f : SidePast (SideInput p) p σ → ℝ) (hf : Measurable f) (Cf : ℝ)
    (hCf : ∀ x, ‖f x‖ ≤ Cf)
    (g : FutureArray p σ → ℝ) (hg : Measurable g) (Cg : ℝ)
    (hCg : ∀ y, ‖g y‖ ≤ Cg) :
    ∫ z, (if (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ then
        f ((sideCompleteRowSplitEquiv (SideInput p) p σ z).1) *
          g ((sideCompleteRowSplitEquiv (SideInput p) p σ z).2) else 0)
        ∂((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)) =
      (∫ x, (if (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).eventAt σ x = true
          then f x else 0) ∂((extendedPrivateLaw p).prod (pastArrayLaw p σ))) *
        ∫ y, g y ∂(futureArrayLaw p σ) := by
  exact stopping_event_integral_factorization (extendedPrivateLaw p) p
    (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta) σ
    f hf Cf hCf g hg Cg hCg

/-- The launch event's normalized restriction has exactly the full future
product law whenever that stopping-index event has positive mass. The formula
is stated on every measurable future set, so it determines the entire
normalized future marginal. -/
theorem actual_launch_normalized_future_marginal
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p)
    (hpos : 0 < ((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ})
    (B : Set (FutureArray p σ)) (hB : MeasurableSet B) :
    ((((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)).restrict
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ}).map
        (fun z => (sideCompleteRowSplitEquiv (SideInput p) p σ z).2) B) /
      (((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p))
        {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop z = σ}) =
      (futureArrayLaw p σ) B := by
  let τ := actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta
  let μ := (extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)
  let E : Set (SideInput p × CompletePublicTable.CompleteRow p) := {z | τ.stop z = σ}
  have hproj : Measurable (fun z : SideInput p × CompletePublicTable.CompleteRow p =>
      (sideCompleteRowSplitEquiv (SideInput p) p σ z).2) :=
    measurable_snd.comp (sideCompleteRowSplitEquiv (SideInput p) p σ).measurable
  have hmap :
      (μ.restrict E).map (fun z =>
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2) B =
        μ {z | τ.stop z = σ ∧
          (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ B} := by
    rw [Measure.map_apply_of_aemeasurable hproj.aemeasurable hB,
      Measure.restrict_apply (hproj hB)]
    congr 1
    ext z
    simp [E, Set.mem_inter_iff, and_comm]
  have hfactor := actual_launch_event_factorization p ids rewards C_star C_h eta σ
    Set.univ MeasurableSet.univ B hB
  have hmass : μ E =
      ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        {x | τ.eventAt σ x = true} := by
    simpa [μ, E, τ, Set.univ_inter, (futureArrayLaw_probability p σ).measure_univ] using
      (actual_launch_event_factorization p ids rewards C_star C_h eta σ
        Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ)
  have hjoint :
      μ {z | τ.stop z = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ B} =
        μ E * (futureArrayLaw p σ) B := by
    calc
      μ {z | τ.stop z = σ ∧
          (sideCompleteRowSplitEquiv (SideInput p) p σ z).2 ∈ B} =
        ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
          {x | τ.eventAt σ x = true} * (futureArrayLaw p σ) B := by
            simpa [μ, τ, Set.univ_inter] using hfactor
      _ = μ E * (futureArrayLaw p σ) B := by rw [← hmass]
  calc
    (μ.restrict E).map (fun z =>
        (sideCompleteRowSplitEquiv (SideInput p) p σ z).2) B / μ E =
      (μ E * (futureArrayLaw p σ) B) / μ E := by rw [hmap, hjoint]
    _ = (futureArrayLaw p σ) B := by
      rw [mul_comm (μ E) ((futureArrayLaw p σ) B)]
      exact ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top μ E)

/-- Swapping the literal row/private product order is an actual
measure-preserving product commutation. -/
theorem measurePreserving_row_private_commutation (p : Parameters) :
    MeasurePreserving Prod.swap
      ((CompletePublicTable.completeRowMeasure p).prod (extendedPrivateLaw p))
      ((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)) :=
  MeasureTheory.Measure.measurePreserving_swap

/-- The original row-then-private product has the same full strict-past and
whole-future factorization after the explicit product commutation. -/
theorem actual_launch_event_factorization_row_private
    (p : Parameters) (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : LearningRate) (σ : LaunchIndex p)
    (A : Set (SidePast (SideInput p) p σ)) (hA : MeasurableSet A)
    (B : Set (FutureArray p σ)) (hB : MeasurableSet B) :
    ((CompletePublicTable.completeRowMeasure p).prod (extendedPrivateLaw p))
      {z | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).stop (z.2, z.1) = σ ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ (z.2, z.1)).1 ∈ A ∧
        (sideCompleteRowSplitEquiv (SideInput p) p σ (z.2, z.1)).2 ∈ B} =
      ((extendedPrivateLaw p).prod (pastArrayLaw p σ))
        (A ∩ {x | (actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta).eventAt σ x = true}) *
        (futureArrayLaw p σ) B := by
  let τ := actualReferenceLaunchStoppingTime p ids rewards C_star C_h eta
  let split := sideCompleteRowSplitEquiv (SideInput p) p σ
  let S : Set (SideInput p × CompletePublicTable.CompleteRow p) :=
    {z | τ.stop z = σ ∧ (split z).1 ∈ A ∧ (split z).2 ∈ B}
  have hstop : Measurable (actualLaunchStop p ids rewards C_star C_h eta) :=
    measurable_actualLaunchStop p ids rewards C_star C_h eta
  have hsplit := split.measurable
  have hS : MeasurableSet S := by
    exact ((measurableSet_singleton σ).preimage hstop).inter
      ((hA.preimage (measurable_fst.comp hsplit)).inter
        (hB.preimage (measurable_snd.comp hsplit)))
  have hset :
      {z : CompletePublicTable.CompleteRow p × SideInput p |
        τ.stop (z.2, z.1) = σ ∧
          (split (z.2, z.1)).1 ∈ A ∧ (split (z.2, z.1)).2 ∈ B} =
        Prod.swap ⁻¹' S := by
    ext z
    rfl
  rw [hset]
  calc
    ((CompletePublicTable.completeRowMeasure p).prod (extendedPrivateLaw p))
        (Prod.swap ⁻¹' S) =
      ((CompletePublicTable.completeRowMeasure p).prod (extendedPrivateLaw p)).map
        Prod.swap S := by
          exact (Measure.map_apply_of_aemeasurable
            measurable_swap.aemeasurable hS).symm
    _ = ((extendedPrivateLaw p).prod (CompletePublicTable.completeRowMeasure p)) S := by
          rw [(measurePreserving_row_private_commutation p).map_eq]
    _ = _ := by
          simpa [S, τ, split] using
            actual_launch_event_factorization p ids rewards C_star C_h eta σ A hA B hB

end Bandits.Support.ReferenceLaunchRowLaw

end
