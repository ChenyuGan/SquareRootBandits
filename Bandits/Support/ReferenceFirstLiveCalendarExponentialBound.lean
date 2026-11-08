/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCalendarIntegralAssembly
public import Bandits.Support.ReferenceFirstLiveOriginalBranchEstimates
public import Bandits.Support.ReferenceFirstLaunchEnergyInitialization
public import Bandits.Support.ReferenceFirstLiveEmptyPendingConditionalExponentialQueue

/-!
# First-window exponential calendar estimate on the original source

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:245-288`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:145-164`.

The literal calendar backlog is integrated under the unchanged original source
law. Birth, nonempty-pending, and empty-pending increments are bounded by their
inherited finite, possibly zero masses. The inclusive first-overflow update is
retained; the stopped queue then stays fixed while physical play continues.
This internal first-window estimate supplies the later stopped-overflow
exponential/Markov union bound. It does not assert a tail bound, a global queue
law, a manuscript filtration identification, or a regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveCalendarExponentialBound

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "beta" => ReferenceFirstLiveSourceSavedMoments.beta rate
/-- The literal first-window exponential starts at one on every source point. -/
theorem firstWindowExpBacklogAt_zero (j : Fin p.K) (omega : S) :
    Real.exp (beta * ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
      rate rewards C_star C_h j 0 omega) = 1 := by
  simp [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt,
    RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

/-- Every literal calendar exponential is integrable under the original law. -/
theorem integrable_firstWindowExpBacklogAt (j : Fin p.K) (n : ℕ) :
    Integrable (fun omega : S => Real.exp (beta *
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h j n omega)) mu :=
  ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
    rate rewards C_star C_h j n

section EmptyPrefix

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p)

local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "cells" => ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
  rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "past" => ReferenceFirstLiveEmptyPendingAcceptedMoments.past
  rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s

private theorem empty_physicalStart (z : Ze) :
    ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
  exact z.val.property.2.2

/-- The empty-cell list is the inclusive prefix of the same original source's
whole first window. No trace or equality is supplied by the caller. -/
theorem wholeFirstLiveCells_take_empty_current (z : Ze) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z.val.val).take (n + 1) = cells z := by
  let source := z.val.val
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true :=
    z.val.property.2.1
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s :=
    z.val.property.2.2
  let sFin : Fin (p.T + 1) := ⟨s, by omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s :=
    ⟨source, hcross, helapsed⟩
  have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sFin x
  have hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
      (p.T - s) ≤ p.T := by rw [helapsed]; omega
  have hwholeCells : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hcross (p.T - s) hspan := by
    simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells,
      ReferenceFirstLiveOverflowReadout.launch_crossing,
      ReferenceFirstLiveOverflowReadout.launch_span, sFin] using hwhole.2
  rw [hwholeCells]
  exact ReferenceFirstLiveCalendarPrefixReadout.actualLiveSourceCells_take_of_le
    rate source rewards C_star C_h hcross (n + 1) (p.T - s) (by omega) hspan

/-- Before an actual empty-pending cell, the calendar backlog is precisely its
existing strict-past queue readout, on the same original source point. -/
theorem firstWindowBacklogAt_empty_before (z : Ze) (j : Fin p.K) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
      rate rewards C_star C_h j t.val z.val.val =
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore
        rate rewards C_star C_h q t s hs control0 j z := by
  have hprefix : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z.val.val).take n = (cells z).take n := by
    calc
      _ = ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h z.val.val).take (n + 1)).take n := by
            rw [List.take_take, Nat.min_eq_left (by omega : n ≤ n + 1)]
      _ = _ := by rw [wholeFirstLiveCells_take_empty_current
        rate rewards C_star C_h q t s hs control0 z]
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt,
    empty_physicalStart rate rewards C_star C_h q t s hs control0 z,
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_eq_normalized,
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.past_eq_actualCells_take]
  exact congrArg (fun rounds =>
    StoppedQueueBound.normalizedBacklog queue (RecordedQueueRun.run queue rounds) j) hprefix

/-- After an actual empty-pending cell, the same calendar prefix includes its
current update, even when that update first overflows. -/
theorem firstWindowBacklogAt_empty_after (z : Ze) (j : Fin p.K) :
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
      rate rewards C_star C_h j (t.val + 1) z.val.val =
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogAfter
        rate rewards C_star C_h q t s hs control0 j z := by
  have hnext : t.val + 1 - s = n + 1 := by omega
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt,
    empty_physicalStart rate rewards C_star C_h q t s hs control0 z, hnext,
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogAfter_eq_normalized,
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.post_eq_actualCells_take_succ]
  have htake : (cells z).take (n + 1) = cells z := by
    apply List.take_of_length_le
    rw [ReferenceFirstLiveEmptyPendingSourceMoments.actualCells_length]
  rw [htake]
  exact congrArg (fun rounds =>
    StoppedQueueBound.normalizedBacklog queue (RecordedQueueRun.run queue rounds) j)
      (wholeFirstLiveCells_take_empty_current rate rewards C_star C_h q t s hs control0 z)

end EmptyPrefix

section Cells

variable (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p) (j : Fin p.K)

local notation "Zbirth" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muBirth" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)

/-- Birth-before is one, so the inclusive birth exponential increment costs at
most the unchanged birth-stratum mass. -/
theorem integral_exp_birth_difference_le_mass :
    (∫ z : Zbirth,
      (Real.exp (beta * StoppedQueueBound.normalizedBacklog
        (ReferenceFirstLiveCalendarPrefixReadout.queueParameters rate)
        (ReferenceFirstLaunchCommonUpdateSource.firstUpdate
          rate rewards C_star C_h q t control0 z) j) - 1) ∂muBirth) ≤
      (muBirth).real Set.univ := by
  have hi := ReferenceFirstLaunchEnergyInitialization.integrable_birthExponential
    rate rewards C_star C_h q t control0 j
  have hb := ReferenceFirstLaunchEnergyInitialization.integral_birthExponential
    rate rewards C_star C_h q t control0 j
  change (∫ z : Zbirth,
    ReferenceFirstLaunchEnergyInitialization.birthBacklogExponential
      rate rewards C_star C_h q t control0 j z - 1 ∂muBirth) ≤ _
  rw [integral_sub hi (integrable_const (1 : ℝ))]
  simp only [integral_const, smul_eq_mul, mul_one]
  exact (sub_le_iff_le_add).mpr (by simpa only [two_mul, Measure.real_def] using hb)

variable (s : ℕ) (hs : s ≤ t.val)

local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "muEmpty" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
  rate rewards C_star C_h q t s hs control0
local notation "expAt" => fun (v : ℕ) (omega : S) => Real.exp (beta *
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j v omega)

/-- The original nonempty-branch estimate bounds the actual calendar
increment by its whole branch mass, using strict-past mass monotonicity. -/
theorem integral_exp_nonempty_difference_le_mass :
    (∫ z : Zplus, expAt (t.val + 1) z.val.val - expAt t.val z.val.val ∂muPlus) ≤
      (muPlus).real Set.univ := by
  let E := ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
    rate rewards C_star C_h q t s hs control0
  have ha := ReferenceFirstLiveOriginalBranchEstimates.integrableOn_originalExpBacklogAfter
    rate rewards C_star C_h q t s hs control0 j
  have hb := ReferenceFirstLiveOriginalBranchEstimates.integrableOn_originalExpBacklogBefore
    rate rewards C_star C_h q t s hs control0 j
  have hstep := ReferenceFirstLiveOriginalBranchEstimates.integral_expBacklogAfter_step_originalBranch
    rate rewards C_star C_h q t s hs control0 j
  rw [ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch
    rate rewards C_star C_h q t s hs control0
      (fun omega : S => expAt (t.val + 1) omega - expAt t.val omega)]
  rw [integral_sub ha hb]
  apply (sub_le_iff_le_add').mpr
  refine hstep.trans (add_le_add le_rfl ?_)
  have hmass : (muPlus).real Set.univ = (mu).real E :=
    by
      simp only [Measure.real_def]
      exact congrArg ENNReal.toReal
        (ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_mass_original
          rate rewards C_star C_h q t s hs control0)
  rw [hmass]
  exact measureReal_mono Set.inter_subset_left

/-- The actual empty-branch step is transported by the proved literal prefix
equalities and integrated on the same finite, unnormalized empty measure. -/
theorem integral_exp_empty_difference_le_mass :
    (∫ z : Ze, expAt (t.val + 1) z.val.val - expAt t.val z.val.val ∂muEmpty) ≤
      (muEmpty).real Set.univ := by
  have heq : (fun z : Ze => expAt (t.val + 1) z.val.val - expAt t.val z.val.val) =
      (fun z : Ze =>
        ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogAfter
          rate rewards C_star C_h q t s hs control0 j z -
        ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogBefore
          rate rewards C_star C_h q t s hs control0 j z) := by
    funext z
    change Real.exp (beta * ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h j (t.val + 1) z.val.val) -
      Real.exp (beta * ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h j t.val z.val.val) = _
    rw [firstWindowBacklogAt_empty_after rate rewards C_star C_h q t s hs control0 z j,
      firstWindowBacklogAt_empty_before rate rewards C_star C_h q t s hs control0 z j]
    rfl
  rw [heq]
  have haCalendar := ReferenceFirstLiveSourcePhasePartition.integrable_emptyPullback_ExpBacklog
    rate rewards C_star C_h q t s hs control0 j (t.val + 1)
  have hbCalendar := ReferenceFirstLiveSourcePhasePartition.integrable_emptyPullback_ExpBacklog
    rate rewards C_star C_h q t s hs control0 j t.val
  have ha : Integrable
      (ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogAfter
        rate rewards C_star C_h q t s hs control0 j) muEmpty := by
    apply haCalendar.congr
    filter_upwards [] with z
    rw [firstWindowBacklogAt_empty_after rate rewards C_star C_h q t s hs control0 z j]
    rfl
  have hb : Integrable
      (ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.expBacklogBefore
        rate rewards C_star C_h q t s hs control0 j) muEmpty := by
    apply hbCalendar.congr
    filter_upwards [] with z
    rw [firstWindowBacklogAt_empty_before rate rewards C_star C_h q t s hs control0 z j]
    rfl
  rw [integral_sub ha hb]
  exact (sub_le_iff_le_add).mpr
    (ReferenceFirstLiveEmptyPendingConditionalExponentialQueue.integral_expBacklogAfter_step
      rate rewards C_star C_h q t s hs control0 j)

end Cells

variable (control0 : ContinuousLearningRows.TimeControl p) (j : Fin p.K)

include control0

local notation "expAt" => fun (v : ℕ) (omega : S) => Real.exp (beta *
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j v omega)

/-- One actual calendar step increases the original-source exponential
expectation by at most one. Exceptional and frozen suffixes are included. -/
theorem integral_exp_calendar_step (t : Fin p.T) :
    (∫ omega : S, expAt (t.val + 1) omega ∂mu) ≤
      (∫ omega : S, expAt t.val omega ∂mu) + 1 := by
  have hiAfter := integrable_firstWindowExpBacklogAt rate rewards C_star C_h j (t.val + 1)
  have hiBefore := integrable_firstWindowExpBacklogAt rate rewards C_star C_h j t.val
  apply (sub_le_iff_le_add').mp
  rw [← integral_sub hiAfter hiBefore]
  rw [ReferenceFirstLiveCalendarIntegralAssembly.integral_exp_calendar_step
    rate rewards C_star C_h t control0 j]
  refine le_trans (add_le_add ?_ ?_)
    (ReferenceFirstLiveCalendarIntegralAssembly.source_cell_mass_le_one
      rate rewards C_star C_h t control0)
  · apply Finset.sum_le_sum
    intro q _
    exact integral_exp_birth_difference_le_mass rate rewards C_star C_h q t control0 j
  · apply Finset.sum_le_sum
    intro q _
    apply Finset.sum_le_sum
    intro v _
    exact add_le_add
      (integral_exp_nonempty_difference_le_mass rate rewards C_star C_h q t control0 j
        v.val (Nat.lt_succ_iff.mp v.isLt))
      (integral_exp_empty_difference_le_mass rate rewards C_star C_h q t control0 j
        v.val (Nat.lt_succ_iff.mp v.isLt))

/-- Finite iteration of the actual calendar steps, starting from the proved
pointwise value one. The bound on `n` is only the horizon index condition. -/
theorem integral_exp_calendar_le (n : ℕ) (hn : n ≤ p.T) :
    (∫ omega : S, expAt n omega ∂mu) ≤ (n : ℝ) + 1 := by
  have hprob : IsProbabilityMeasure mu :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  induction n with
  | zero =>
      have hzero : (fun omega : S => expAt 0 omega) = fun _ => (1 : ℝ) := by
        funext omega
        exact firstWindowExpBacklogAt_zero rate rewards C_star C_h j omega
      rw [hzero]
      simp
  | succ n ih =>
      have hnt : n < p.T := by omega
      have hprev := ih (by omega)
      have hstep := integral_exp_calendar_step rate rewards C_star C_h control0 j ⟨n, hnt⟩
      calc
        (∫ omega : S, expAt (n + 1) omega ∂mu) ≤
            (∫ omega : S, expAt n omega ∂mu) + 1 := hstep
        _ ≤ ((n : ℝ) + 1) + 1 := add_le_add hprev le_rfl
        _ = ((n + 1 : ℕ) : ℝ) + 1 := by simp only [Nat.cast_add, Nat.cast_one]

/-- Terminal first-window exponential expectation under the original source
law, with the first overflow update and every exceptional source retained. -/
theorem integral_exp_calendar_terminal :
    (∫ omega : S, expAt p.T omega ∂mu) ≤ (p.T : ℝ) + 1 :=
  integral_exp_calendar_le rate rewards C_star C_h control0 j p.T le_rfl

end Bandits.Support.ReferenceFirstLiveCalendarExponentialBound

end
