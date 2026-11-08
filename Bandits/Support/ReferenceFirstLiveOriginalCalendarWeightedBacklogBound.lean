/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstLiveCalendarIntegralAssembly
public import Bandits.Support.ReferenceFirstLiveOriginalBranchEstimates
public import Bandits.Support.ReferenceFirstLaunchEnergyInitialization
public import Bandits.Support.ReferenceFirstLiveRateBoundedDrift
public import Bandits.Support.ReferenceFirstLiveEmptyPendingAnchorRateFeasibility
public import Bandits.Support.ReferenceFirstLiveEmptyPendingConditionalWeightedDrift

import Mathlib.Tactic

/-!
# Actual first-live original-source weighted backlog budget

The event and costs in this module are read from the actual first-live source
window and its original source law. The retained event includes the current
cell only when it is enabled and the strict-past queue has not overflowed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveOriginalCalendarWeightedBacklogBound

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)

/-- The actual launch boundary in the original source stream. -/
def firstLiveStart (omega : SourceInput p) : ℕ :=
  ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h

/-- The complete actual first-live list, retaining every source cell. -/
def firstLiveCells (omega : SourceInput p) :=
  ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega

/-- The actual numerical queue used by the first-live readout. -/
def firstLiveQueue :=
  ReferenceFirstLaunchNumericalCell.queueParameters rate

/-- The actual queue state at a calendar boundary. -/
def firstLiveRunAt (v : ℕ) (omega : SourceInput p) :=
  RecordedQueueRun.run (firstLiveQueue rate)
    ((firstLiveCells rate rewards C_star C_h omega).take (v - firstLiveStart rate rewards C_star C_h omega))

/-- Actual first-window weighted-square potential at calendar boundary `v`. -/
def firstLivePotentialAt (v : ℕ) (omega : SourceInput p) : ℝ :=
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
    rate rewards C_star C_h v omega

/-- Actual first-window weighted backlog at calendar boundary `v`. -/
def firstLiveWeightedBacklogAt (v : ℕ) (omega : SourceInput p) : ℝ :=
  ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt
    rate rewards C_star C_h v omega

/-- The literal retained-enabled source event at calendar step `t`. -/
def retainedEnabledEvent (t : Fin p.T) : Set (SourceInput p) :=
  {omega |
    (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
    firstLiveStart rate rewards C_star C_h omega ≤ t.val ∧
    ∃ hn : t.val - firstLiveStart rate rewards C_star C_h omega <
        (firstLiveCells rate rewards C_star C_h omega).length,
      ((firstLiveCells rate rewards C_star C_h omega)[t.val - firstLiveStart rate rewards C_star C_h omega]'hn).enabled = true ∧
      (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}

/-- The actual indicator-weighted cost charged at a first-live step. -/
def retainedWeightedBacklogCost (t : Fin p.T) (omega : SourceInput p) : ℝ :=
  Set.indicator (retainedEnabledEvent rate rewards C_star C_h t)
    (firstLiveWeightedBacklogAt rate rewards C_star C_h t.val) omega

/-- The sharp source drift constant, with the full `m`-marginal correction. -/
def sourceDriftConstant : ℝ :=
  CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)

private theorem actualFirstLiveCell_enabled (t : Fin p.T) (omega : SourceInput p)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true)
    (hidx : t.val - firstLiveStart rate rewards C_star C_h omega <
      (firstLiveCells rate rewards C_star C_h omega).length) :
    ((firstLiveCells rate rewards C_star C_h omega)[t.val - firstLiveStart rate rewards C_star C_h omega]'hidx).enabled = true := by
  classical
  let start := firstLiveStart rate rewards C_star C_h omega
  let sf : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le
    (ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h)⟩
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).completed = start := by
    rfl
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h sf.val :=
    ⟨omega, hc, helapsed⟩
  have hfiber := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sf x
  have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
    rate rewards C_star C_h omega
  have hindex : t.val - start <
      (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h sf.val
        (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x).length := by
    calc
      t.val - start < (firstLiveCells rate rewards C_star C_h omega).length := by
        simpa [firstLiveStart, start] using hidx
      _ = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega).length := by
        exact hlen
      _ = (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h sf.val
          (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x).length :=
        congrArg List.length hfiber.1
  have hindexCells : t.val - start <
      (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h sf.val
        (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x).length := by
    rw [← hfiber.2]
    simpa [firstLiveCells, start] using hidx
  let k : Fin (ReferenceFirstLiveOverflowReadout.firstLiveWindow rate rewards C_star C_h sf.val
      (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x).length :=
    ⟨t.val - start, hindex⟩
  have hcross := ReferenceFirstLiveOverflowReadout.launch_crossing rate rewards C_star C_h sf x
  have hspan := ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h sf
    (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x
  have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
    rate omega rewards C_star C_h hcross (p.T - sf.val) hspan k
  have hget := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
    rate omega rewards C_star C_h hcross (p.T - sf.val) hspan k
  have henabled : (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate omega rewards C_star C_h hcross (p.T - sf.val) hspan k).input.enabled = true :=
    hfacts.2.2.2.2.1
  let cellsFiber := ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h sf.val
    (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x
  have hcellEnabled : (cellsFiber[t.val - start]'hindexCells).enabled = true := by
    dsimp only [cellsFiber, ReferenceFirstLiveOverflowReadout.firstLiveCells]
    exact hget.symm ▸ henabled
  have hopt := congrArg
    (fun l : List (RecordedQueueRun.RoundInput p.K) => l[t.val - start]?) hfiber.2
  have hidxWhole : t.val - start <
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length := by
    simpa [firstLiveCells, firstLiveStart, start] using hidx
  rw [List.getElem?_eq_getElem hidxWhole,
    List.getElem?_eq_getElem hindexCells] at hopt
  have hcellEq :
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega)[t.val - start]'hidxWhole =
        (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h sf.val
          (p.T - sf.val) (ReferenceFirstLiveOverflowReadout.maximal_span sf) x)[t.val - start]'hindexCells :=
    Option.some.inj hopt
  exact hcellEq.symm ▸ hcellEnabled

private theorem retainedEvent_of_currentWindow (t : Fin p.T) (omega : SourceInput p)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true)
    (hstart : firstLiveStart rate rewards C_star C_h omega < t.val)
    (hwindow : t.val - firstLiveStart rate rewards C_star C_h omega <
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length)
    (hsafe : (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false) :
    omega ∈ retainedEnabledEvent rate rewards C_star C_h t := by
  have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
    rate rewards C_star C_h omega
  have hidx : t.val - firstLiveStart rate rewards C_star C_h omega <
      (firstLiveCells rate rewards C_star C_h omega).length := by
    change t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h <
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length
    rw [hlen]
    exact hwindow
  have henabled := actualFirstLiveCell_enabled rate rewards C_star C_h t omega hc hidx
  change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
    firstLiveStart rate rewards C_star C_h omega ≤ t.val ∧
    ∃ hn : t.val - firstLiveStart rate rewards C_star C_h omega <
        (firstLiveCells rate rewards C_star C_h omega).length,
      ((firstLiveCells rate rewards C_star C_h omega)[t.val -
        firstLiveStart rate rewards C_star C_h omega]'hn).enabled = true ∧
      (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false
  exact ⟨hc, Nat.le_of_lt hstart, ⟨hidx, henabled, hsafe⟩⟩

/-- The retained-enabled event is exactly birth together with the safe strict
past of the two continuing source phases. -/
theorem retainedEnabledEvent_eq_phaseRestriction (t : Fin p.T) (control0 : TimeControl p) :
    retainedEnabledEvent rate rewards C_star C_h t =
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) ∩
          {omega : SourceInput p |
            (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false} := by
  classical
  ext omega
  constructor
  · intro hk
    change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
      firstLiveStart rate rewards C_star C_h omega ≤ t.val ∧
      ∃ hn : t.val - firstLiveStart rate rewards C_star C_h omega <
          (firstLiveCells rate rewards C_star C_h omega).length,
        ((firstLiveCells rate rewards C_star C_h omega)[t.val -
          firstLiveStart rate rewards C_star C_h omega]'hn).enabled = true ∧
        (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false at hk
    rcases hk with ⟨hc, hstart, hcell⟩
    by_cases hbirth : firstLiveStart rate rewards C_star C_h omega = t.val
    ·
      have hphase : omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h t 2 := by
        change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
          t.val = ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
        exact ⟨hc, hbirth.symm⟩
      have hzero : t.val - firstLiveStart rate rewards C_star C_h omega = 0 := by omega
      have hsafeBirth : (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false := by
        change (RecordedQueueRun.run (firstLiveQueue rate)
          ((firstLiveCells rate rewards C_star C_h omega).take
            (t.val - firstLiveStart rate rewards C_star C_h omega))).overflow = false
        rw [hzero]
        simp [RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState]
      exact ⟨Or.inl hphase, hsafeBirth⟩
    · have hpast : firstLiveStart rate rewards C_star C_h omega < t.val := by omega
      obtain ⟨which, hwhich⟩ :=
        ReferenceFirstLiveSourcePhasePartition.source_phases_exhaustive
          rate rewards C_star C_h t omega
      have hclass :
          omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∨
          omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4 := by
        fin_cases which
        · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
              rate omega rewards C_star C_h).crossing = none := by
            simpa [ReferenceFirstLiveSourcePhasePartition.sourcePhase, firstLiveStart] using hwhich
          simp [hnone] at hc
        · have hfuture : t.val < firstLiveStart rate rewards C_star C_h omega := by
            simpa [firstLiveStart] using hwhich.2
          omega
        · have hb : t.val = firstLiveStart rate rewards C_star C_h omega := by
            simpa [firstLiveStart] using hwhich.2
          omega
        · exact Or.inl hwhich
        · exact Or.inr hwhich
        · have hlate :
              (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length ≤
                t.val - firstLiveStart rate rewards C_star C_h omega := by
            rcases hwhich with ⟨_, _, hlate⟩
            simpa [firstLiveStart] using hlate
          have hlength := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
            rate rewards C_star C_h omega
          have htooLong : t.val - firstLiveStart rate rewards C_star C_h omega <
              (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length := by
            rcases hcell with ⟨hn, _, _⟩
            calc
              t.val - firstLiveStart rate rewards C_star C_h omega <
                  (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length := by
                simpa [firstLiveCells, firstLiveStart] using hn
              _ = (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length := hlength
          omega
      exact ⟨Or.inr hclass, hcell.2.2⟩
  · rintro ⟨hphase, hsafe⟩
    rcases hphase with hbirth | hcontinuing
    · have hb :
          (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
            t.val = firstLiveStart rate rewards C_star C_h omega := by
        simpa [ReferenceFirstLiveSourcePhasePartition.sourcePhase, firstLiveStart] using hbirth
      have hc := hb.1
      have hstart : firstLiveStart rate rewards C_star C_h omega = t.val := hb.2.symm
      have hzero : t.val - firstLiveStart rate rewards C_star C_h omega = 0 := by omega
      have hposWindow := ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
        rate rewards C_star C_h t control0 omega hbirth
      have hposCells : 0 < (firstLiveCells rate rewards C_star C_h omega).length := by
        change 0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length
        rw [ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length]
        exact hposWindow
      have hidx : t.val - firstLiveStart rate rewards C_star C_h omega <
          (firstLiveCells rate rewards C_star C_h omega).length := by
        rw [hzero]
        exact hposCells
      have henabled := actualFirstLiveCell_enabled rate rewards C_star C_h t omega hc hidx
      have hsafe' : (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false := by
        unfold firstLiveRunAt
        rw [hzero]
        rfl
      change omega ∈ retainedEnabledEvent rate rewards C_star C_h t
      exact ⟨hc, by omega, ⟨hidx, henabled, hsafe'⟩⟩
    · rcases hcontinuing with h3 | h4
      · have hdata :
            (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
            firstLiveStart rate rewards C_star C_h omega < t.val ∧
            t.val - firstLiveStart rate rewards C_star C_h omega <
              (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length := by
          rcases h3 with ⟨hc, hstart, ⟨hwindow, _⟩⟩
          refine ⟨hc, ?_, ?_⟩
          · simpa [firstLiveStart] using hstart
          · simpa [firstLiveStart] using hwindow
        exact retainedEvent_of_currentWindow rate rewards C_star C_h t omega
          hdata.1 hdata.2.1 hdata.2.2 hsafe
      · have hdata :
            (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
            firstLiveStart rate rewards C_star C_h omega < t.val ∧
            t.val - firstLiveStart rate rewards C_star C_h omega <
              (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length := by
          rcases h4 with ⟨hc, hstart, ⟨hwindow, _⟩⟩
          refine ⟨hc, ?_, ?_⟩
          · simpa [firstLiveStart] using hstart
          · simpa [firstLiveStart] using hwindow
        exact retainedEvent_of_currentWindow rate rewards C_star C_h t omega
          hdata.1 hdata.2.1 hdata.2.2 hsafe

private theorem emptyActualSourceCells_eq
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    ReferenceFirstLiveBranchIntegralTransport.actualSourceCells
        rate rewards C_star C_h q t s hs z.val =
      ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
        rate rewards C_star C_h q t s hs control0 z := by
  unfold ReferenceFirstLiveBranchIntegralTransport.actualSourceCells
    ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
  congr 1

private theorem emptyActualCells_prefix_eq
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
        (t.val - s) =
      (ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
        rate rewards C_star C_h q t s hs control0 z).take (t.val - s) := by
  have hprefix := ReferenceFirstLiveWholeSourceReadout.wholeFirstLiveCells_take_stratum_prefix
    rate rewards C_star C_h q t s hs z.val (t.val - s) (by omega)
  rw [emptyActualSourceCells_eq rate rewards C_star C_h q t s hs control0 z] at hprefix
  exact hprefix

private theorem emptyActualCells_inclusive_prefix_eq
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
        (t.val - s + 1) =
      (ReferenceFirstLiveEmptyPendingSourceMoments.actualCells
        rate rewards C_star C_h q t s hs control0 z).take (t.val - s + 1) := by
  have hprefix := ReferenceFirstLiveWholeSourceReadout.wholeFirstLiveCells_take_stratum_prefix
    rate rewards C_star C_h q t s hs z.val (t.val - s + 1) (by omega)
  rw [emptyActualSourceCells_eq rate rewards C_star C_h q t s hs control0 z] at hprefix
  exact hprefix

/-- On the actual empty subtype, the calendar-boundary potential before the
current cell is E's literal strict-past potential. -/
theorem emptyFirstWindowPotentialBefore_eq
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    firstLivePotentialAt rate rewards C_star C_h t.val z.val.val =
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
        rate rewards C_star C_h q t s hs control0 z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  change RecordedWeightedDrift.weightedSquarePotential p.m (firstLiveQueue rate)
      (RecordedQueueRun.run (firstLiveQueue rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h))) =
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
      rate rewards C_star C_h q t s hs control0 z
  rw [hstart]
  unfold ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
  rw [ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.past_eq_actualCells_take
    rate rewards C_star C_h q t s hs control0 z]
  rw [emptyActualCells_prefix_eq rate rewards C_star C_h q t s hs control0 z]
  rfl

/-- On the actual empty subtype, the calendar-boundary potential after the
current update is E's potential after the full retained cell. -/
theorem emptyFirstWindowPotentialAfter_eq
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    firstLivePotentialAt rate rewards C_star C_h (t.val + 1) z.val.val =
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
        rate rewards C_star C_h q t s hs control0 z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  change RecordedWeightedDrift.weightedSquarePotential p.m (firstLiveQueue rate)
      (RecordedQueueRun.run (firstLiveQueue rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
          (t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h))) =
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
      rate rewards C_star C_h q t s hs control0 z
  rw [hstart]
  have hcount : t.val + 1 - s = t.val - s + 1 := by omega
  rw [hcount, emptyActualCells_inclusive_prefix_eq rate rewards C_star C_h q t s hs control0 z]
  unfold ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
  exact congrArg
    (fun state => RecordedWeightedDrift.weightedSquarePotential p.m (firstLiveQueue rate) state)
    (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.post_eq_actualCells_take_succ
      rate rewards C_star C_h q t s hs control0 z).symm

/-- The original weighted-backlog readout before an empty-branch update is
the literal weighted backlog E uses on `Zempty`. -/
theorem emptyFirstWindowWeightedBacklogBefore_eq
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    firstLiveWeightedBacklogAt rate rewards C_star C_h t.val z.val.val =
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
        rate rewards C_star C_h q t s hs control0 z := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  change RecordedWeightedDrift.weightedBacklog p.m (firstLiveQueue rate)
      (RecordedQueueRun.run (firstLiveQueue rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h))) =
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
      rate rewards C_star C_h q t s hs control0 z
  rw [hstart]
  unfold ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
  rw [ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.past_eq_actualCells_take
    rate rewards C_star C_h q t s hs control0 z]
  rw [emptyActualCells_prefix_eq rate rewards C_star C_h q t s hs control0 z]
  rfl

/-- The old whole-source overflow test is exactly E's strict-past event on the
same empty subtype. -/
theorem emptyFirstWindowOldOverflowFalse_iff_G
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0) :
    (firstLiveRunAt rate rewards C_star C_h t.val z.val.val).overflow = false ↔
      z ∈ ReferenceFirstLiveEmptyPendingAcceptedMoments.G
        rate rewards C_star C_h q t s hs control0 := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h = s := by
    simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput,
      ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  have hrun : firstLiveRunAt rate rewards C_star C_h t.val z.val.val =
      ReferenceFirstLiveEmptyPendingAcceptedMoments.past
        rate rewards C_star C_h q t s hs control0 z := by
    change RecordedQueueRun.run (firstLiveQueue rate)
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z.val.val).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val.val rewards C_star C_h)) = _
    rw [hstart]
    rw [ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.past_eq_actualCells_take
      rate rewards C_star C_h q t s hs control0 z]
    rw [emptyActualCells_prefix_eq rate rewards C_star C_h q t s hs control0 z]
    rfl
  rw [hrun]
  exact (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.mem_G_iff_past_not_overflow
    rate rewards C_star C_h q t s hs control0 z).symm

/-- D's empty-stratum drift with A's actual pointwise sharp rate bound,
integrated against the same unnormalized empty measure. -/
theorem emptyPotentialDriftIntegral_sharp
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0,
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
          rate rewards C_star C_h q t s hs control0 z -
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
          rate rewards C_star C_h q t s hs control0 z ∂
      ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0) ≤
      -(11 / 2 : ℝ) *
          (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0,
            Set.indicator
              (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0)
              (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
                rate rewards C_star C_h q t s hs control0) z ∂
            ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0).real
            (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0) := by
  let Ze := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0
  let muE := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0
  let w := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  let r := ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.markerRateWeightSum
    rate rewards C_star C_h q t s hs control0
  let c : ℝ := (33 / 2 : ℝ) * (p.m : ℝ)
  have hG : MeasurableSet G :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
      rate rewards C_star C_h q t s hs control0
  have hw : Integrable w muE :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_weightedBacklogBefore
      rate rewards C_star C_h q t s hs control0
  have hr : Integrable r muE :=
    ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.integrable_markerRateWeightSum
      rate rewards C_star C_h q t s hs control0
  have hsum (z : Ze) : r z ≤ CanonicalRecordingRates.R p := by
    change ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.markerRateWeightSum
      rate rewards C_star C_h q t s hs control0 z ≤ CanonicalRecordingRates.R p
    exact ReferenceFirstLiveEmptyPendingAnchorRateFeasibility.sum_thetaBefore_div_xiEmpty_le_R
      rate rewards C_star C_h q t s hs control0 z
  have hbase : Integrable (fun z : Ze =>
      -(11 / 2 : ℝ) * w z + r z + c) muE := by
    exact ((hw.const_mul (-(11 / 2 : ℝ))).add hr).add (integrable_const c)
  have hbaseG := hbase.indicator hG
  have hbounded : Integrable (fun z : Ze =>
      -(11 / 2 : ℝ) * w z + CanonicalRecordingRates.R p + c) muE := by
    exact ((hw.const_mul (-(11 / 2 : ℝ))).add
      (integrable_const (CanonicalRecordingRates.R p))).add (integrable_const c)
  have hboundedG := hbounded.indicator hG
  have hpoint (z : Ze) :
      Set.indicator G (fun x => -(11 / 2 : ℝ) * w x + r x + c) z ≤
        Set.indicator G (fun x => -(11 / 2 : ℝ) * w x + CanonicalRecordingRates.R p + c) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      linarith [hsum z]
    · simp [Set.indicator_of_notMem hz]
  have hmono := integral_mono_ae hbaseG hboundedG (Filter.Eventually.of_forall hpoint)
  have hsplit :
      (∫ z : Ze, Set.indicator G
        (fun x => -(11 / 2 : ℝ) * w x + CanonicalRecordingRates.R p + c) z ∂muE) =
        -(11 / 2 : ℝ) *
          (∫ z : Ze, Set.indicator G w z ∂muE) +
        (CanonicalRecordingRates.R p + c) * muE.real G := by
    have hwG : Integrable (Set.indicator G w) muE := hw.indicator hG
    have hconstG : Integrable (Set.indicator G (fun _ : Ze => CanonicalRecordingRates.R p + c)) muE :=
      (integrable_const (CanonicalRecordingRates.R p + c)).indicator hG
    have hpointwise :
        (fun z : Ze => Set.indicator G (fun x =>
          -(11 / 2 : ℝ) * w x + CanonicalRecordingRates.R p + c) z) =
        (fun z : Ze => -(11 / 2 : ℝ) * Set.indicator G w z +
          Set.indicator G (fun _ : Ze => CanonicalRecordingRates.R p + c) z) := by
      funext z
      by_cases hz : z ∈ G
      · simp [Set.indicator, hz]
        ring
      · simp [Set.indicator, hz]
    calc
      _ = ∫ z : Ze, -(11 / 2 : ℝ) * Set.indicator G w z +
          Set.indicator G (fun _ : Ze => CanonicalRecordingRates.R p + c) z ∂muE := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact congrFun hpointwise z
      _ = -(11 / 2 : ℝ) * (∫ z : Ze, Set.indicator G w z ∂muE) +
          (CanonicalRecordingRates.R p + c) * muE.real G := by
        rw [integral_add (hwG.const_mul (-(11 / 2 : ℝ))) hconstG,
          integral_const_mul, integral_indicator_const (CanonicalRecordingRates.R p + c) hG,
          smul_eq_mul]
        ring
  calc
    _ ≤ ∫ z : Ze, Set.indicator G
        (fun x => -(11 / 2 : ℝ) * w x + r x + c) z ∂muE :=
      by
        simpa only [G, w, r, c] using
          ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.potential_drift_integral_rate_sum
            rate rewards C_star C_h q t s hs control0
    _ ≤ ∫ z : Ze, Set.indicator G
        (fun x => -(11 / 2 : ℝ) * w x + CanonicalRecordingRates.R p + c) z ∂muE := hmono
    _ = _ := by
      rw [hsplit]

/-- The actual image of E's strict-past safe set is exactly the original
empty-source event intersected with the old-overflow-false restriction. -/
theorem emptyGoodImage_eq_originalIntersection
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 => z.val.val) ''
        ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0 =
      ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h q t s hs control0 ∩
        {omega : SourceInput p |
          (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false} := by
  let Ze := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0
  let O := ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0
  let H : Set (SourceInput p) := fun omega =>
    (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false
  ext omega
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ⟨z.val, z.property, rfl⟩
    · exact (emptyFirstWindowOldOverflowFalse_iff_G
        rate rewards C_star C_h q t s hs control0 z).2 hz
  · rintro ⟨hO, hH⟩
    rcases hO with ⟨z0, hz0, rfl⟩
    let z : Ze := ⟨z0, hz0⟩
    refine ⟨z, ?_, rfl⟩
    exact (emptyFirstWindowOldOverflowFalse_iff_G
      rate rewards C_star C_h q t s hs control0 z).1 hH

/-- The literal retained-enabled event is measurable on the complete original
source, using the already established source-phase and actual empty-image joins. -/
theorem measurableSet_retainedEnabledEvent (t : Fin p.T) (control0 : TimeControl p) :
    MeasurableSet (retainedEnabledEvent rate rewards C_star C_h t) := by
  let H : Set (SourceInput p) :=
    {omega | (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}
  let B := ReferenceFirstLiveSourcePhasePartition.sourcePhase
    rate rewards C_star C_h t 2
  let N := ReferenceFirstLiveSourcePhasePartition.sourcePhase
    rate rewards C_star C_h t 3
  let E := ReferenceFirstLiveSourcePhasePartition.sourcePhase
    rate rewards C_star C_h t 4
  have hBirthSafe : ∀ omega, omega ∈ B → omega ∈ H := by
    intro omega hB
    have hstart : firstLiveStart rate rewards C_star C_h omega = t.val := by
      change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate omega rewards C_star C_h).crossing.isSome = true ∧
        t.val = ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h at hB
      simpa [firstLiveStart] using hB.2.symm
    have hphysical : ReferenceCompletePhysicalHistory.physicalStart
        rate omega rewards C_star C_h = t.val := by
      simpa [firstLiveStart] using hstart
    change (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false
    simp [firstLiveRunAt, firstLiveQueue, firstLiveStart, firstLiveCells, hphysical,
      RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState]
  have hEvent : retainedEnabledEvent rate rewards C_star C_h t =
      B ∪ ((N ∪ E) ∩ H) := by
    rw [retainedEnabledEvent_eq_phaseRestriction rate rewards C_star C_h t control0]
    ext omega
    constructor
    · rintro ⟨hphase, hsafe⟩
      rcases hphase with hB | hN | hE
      · exact Or.inl hB
      · exact Or.inr ⟨Or.inl hN, hsafe⟩
      · exact Or.inr ⟨Or.inr hE, hsafe⟩
    · intro h
      rcases h with hB | ⟨hNE, hsafe⟩
      · exact ⟨Or.inl hB, hBirthSafe omega hB⟩
      · exact ⟨Or.inr hNE, hsafe⟩
  have hBirth : MeasurableSet B :=
    ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h t control0 2
  have hNonempty : MeasurableSet (N ∩ H) := by
    change MeasurableSet
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∩ H)
    rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_nonempty_iUnion
      rate rewards C_star C_h t control0]
    have hdist :
        (⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) ∩ H =
        ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          (ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 ∩ H) := by
      ext omega
      simp
    rw [hdist]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun v =>
      ReferenceFirstLiveOriginalBranchEstimates.measurableSet_originalBranch_intersection
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  have hEmptyPiece (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
      MeasurableSet
        (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 ∩ H) := by
    rw [← emptyGoodImage_eq_originalIntersection rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0]
    exact (ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0).measurableSet_image.mpr
      (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0)
  have hEmpty : MeasurableSet (E ∩ H) := by
    change MeasurableSet
      (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4 ∩ H)
    rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_empty_iUnion
      rate rewards C_star C_h t control0]
    have hdist :
        (⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0) ∩ H =
        ⋃ q : Fin (ConstructorDimensions.M p), ⋃ v : Fin (t.val + 1),
          (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
            rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0 ∩ H) := by
      ext omega
      simp
    rw [hdist]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun v => hEmptyPiece q v
  have hsplit : (N ∪ E) ∩ H = (N ∩ H) ∪ (E ∩ H) := by
    ext omega
    constructor
    · rintro ⟨hNE, hH⟩
      rcases hNE with hN | hE
      · exact Or.inl ⟨hN, hH⟩
      · exact Or.inr ⟨hE, hH⟩
    · rintro (⟨hN, hH⟩ | ⟨hE, hH⟩)
      · exact ⟨Or.inl hN, hH⟩
      · exact ⟨Or.inr hE, hH⟩
  rw [hEvent, hsplit]
  exact hBirth.union (hNonempty.union hEmpty)

/-- Each retained first-live weighted-backlog cost is integrable under the
actual complete-source law. -/
theorem integrable_retainedWeightedBacklogCost
    (t : Fin p.T) (control0 : TimeControl p) :
    Integrable (retainedWeightedBacklogCost rate rewards C_star C_h t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  change Integrable
    (fun omega => Set.indicator (retainedEnabledEvent rate rewards C_star C_h t)
      (firstLiveWeightedBacklogAt rate rewards C_star C_h t.val) omega)
    (BootstrapPrivateRoundStreams.sourceInputLaw p)
  exact (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowWeightedBacklogAt
    rate rewards C_star C_h t.val).indicator
      (measurableSet_retainedEnabledEvent rate rewards C_star C_h t control0)

/-- The actual finite sum of retained first-live costs is integrable. -/
theorem integrable_retainedFiniteWeightedBacklogCost (control0 : TimeControl p) :
    Integrable
      (fun omega => ∑ t : Fin p.T, retainedWeightedBacklogCost rate rewards C_star C_h t omega)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  classical
  exact integrable_finsetSum Finset.univ fun t ht =>
    integrable_retainedWeightedBacklogCost rate rewards C_star C_h t control0

/-- The unnormalized empty good mass is the original source mass of the same
empty branch intersected with the literal old-overflow-false event. -/
theorem emptyGoodMass_eq_originalIntersection
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0).real
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
            rate rewards C_star C_h q t s hs control0 ∩
          {omega : SourceInput p |
            (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}) := by
  let Ze := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0
  let muE := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0
  let f : Ze → SourceInput p :=
    ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t s hs control0
  let O := ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0
  let H : Set (SourceInput p) :=
    {omega | (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}
  have hEmb := ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
    rate rewards C_star C_h q t s hs control0
  have hImage := emptyGoodImage_eq_originalIntersection rate rewards C_star C_h q t s hs control0
  have hG : MeasurableSet G :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
      rate rewards C_star C_h q t s hs control0
  have hTarget : MeasurableSet (O ∩ H) := by
    rw [← hImage]
    exact hEmb.measurableSet_image.mpr hG
  have hpre : f ⁻¹' (O ∩ H) = G := by
    ext z
    change (f z ∈ O ∧ f z ∈ H) ↔ z ∈ G
    constructor
    · rintro ⟨_, hz⟩
      exact (emptyFirstWindowOldOverflowFalse_iff_G
        rate rewards C_star C_h q t s hs control0 z).1 hz
    · intro hz
      refine ⟨?_, ?_⟩
      · exact ⟨z.val, z.property, rfl⟩
      · exact (emptyFirstWindowOldOverflowFalse_iff_G
          rate rewards C_star C_h q t s hs control0 z).2 hz
  change (muE G).toReal = _
  calc
    (muE G).toReal = ((muE.map f) (O ∩ H)).toReal := by
      congr 1
      rw [Measure.map_apply hEmb.measurable hTarget, hpre]
    _ = (((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict O) (O ∩ H)).toReal := by
      rw [ReferenceFirstLiveSourcePhasePartition.muEmpty_map_original
        rate rewards C_star C_h q t s hs control0]
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p) (O ∩ H)).toReal := by
      congr 1
      rw [Measure.restrict_apply hTarget]
      congr 1
      ext omega
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨hO, hH⟩, _⟩
        exact ⟨hO, hH⟩
      · rintro ⟨hO, hH⟩
        exact ⟨⟨hO, hH⟩, hO⟩

/-- E's strict-past weighted backlog integral is exactly the original-source
weighted backlog integral on the empty branch intersected with old safety. -/
theorem emptyGoodWeightedBacklogIntegral_eq_original
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    (∫ z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0,
      Set.indicator
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0)
        (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
          rate rewards C_star C_h q t s hs control0) z ∂
      ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0) =
      (∫ omega in
        ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0 ∩
          {omega : SourceInput p |
            (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false},
        firstLiveWeightedBacklogAt rate rewards C_star C_h t.val omega ∂
        BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let Ze := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0
  let muE := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0
  let w := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  let f : Ze → SourceInput p :=
    ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t s hs control0
  let O := ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0
  let H : Set (SourceInput p) :=
    {omega | (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}
  let W := firstLiveWeightedBacklogAt rate rewards C_star C_h t.val
  have hsafe (z : Ze) : f z ∈ H ↔ z ∈ G := by
    exact emptyFirstWindowOldOverflowFalse_iff_G
      rate rewards C_star C_h q t s hs control0 z
  have hcost (z : Ze) : W (f z) = w z := by
    exact emptyFirstWindowWeightedBacklogBefore_eq
      rate rewards C_star C_h q t s hs control0 z
  have hfun :
      (fun z : Ze => Set.indicator H W (f z)) = Set.indicator G w := by
    funext z
    by_cases hz : z ∈ G
    · have hHz := (hsafe z).2 hz
      simp [Set.indicator, hz, hHz, hcost z]
    · have hHz : f z ∉ H := by
        intro hh
        exact hz ((hsafe z).1 hh)
      simp [Set.indicator, hz, hHz]
  have hO : MeasurableSet O :=
    ReferenceFirstLiveSourcePhasePartition.measurableSet_originalEmptyEvent
      rate rewards C_star C_h q t s hs control0
  have hEmb := ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
    rate rewards C_star C_h q t s hs control0
  have hG : MeasurableSet G :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
      rate rewards C_star C_h q t s hs control0
  have hOH : MeasurableSet (O ∩ H) := by
    rw [← emptyGoodImage_eq_originalIntersection rate rewards C_star C_h q t s hs control0]
    exact hEmb.measurableSet_image.mpr hG
  have hdom : O ∩ (O ∩ H) = O ∩ H := by
    ext omega
    change (omega ∈ O ∧ (omega ∈ O ∧ omega ∈ H)) ↔ (omega ∈ O ∧ omega ∈ H)
    constructor
    · rintro ⟨hO, ⟨_, hH⟩⟩
      exact ⟨hO, hH⟩
    · rintro ⟨hO, hH⟩
      exact ⟨hO, ⟨hO, hH⟩⟩
  calc
    _ = ∫ z : Ze, Set.indicator H W (f z) ∂muE := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (congrFun hfun z).symm
    _ = ∫ omega in O, Set.indicator H W omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p :=
      ReferenceFirstLiveSourcePhasePartition.integral_originalEmpty
        rate rewards C_star C_h q t s hs control0 (Set.indicator H W)
    _ = ∫ omega in O, Set.indicator (O ∩ H) W omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hO] with omega hω
      by_cases hH : omega ∈ H <;> simp [Set.indicator, hω, hH]
    _ = ∫ omega in O ∩ H, W omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      rw [setIntegral_indicator hOH, hdom]

/-- The exact empty-pending contribution to the original-source calendar
potential step, with the literal retained weighted-backlog cost. -/
theorem emptyOriginalPotentialStep_bound
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    (∫ omega in
      ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0,
      firstLivePotentialAt rate rewards C_star C_h (t.val + 1) omega -
        firstLivePotentialAt rate rewards C_star C_h t.val omega ∂
      BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      -(11 / 2 : ℝ) *
          (∫ omega in
            ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0 ∩
              {omega : SourceInput p |
                (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false},
            firstLiveWeightedBacklogAt rate rewards C_star C_h t.val omega ∂
            BootstrapPrivateRoundStreams.sourceInputLaw p) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real
            (ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0 ∩
              {omega : SourceInput p |
                (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}) := by
  let Ze := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0
  let O := ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent rate rewards C_star C_h q t s hs control0
  let f : Ze → SourceInput p :=
    ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t s hs control0
  let V := firstLivePotentialAt rate rewards C_star C_h
  have hpotential :
      (∫ omega in O, V (t.val + 1) omega - V t.val omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
        ∫ z : Ze,
          ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
              rate rewards C_star C_h q t s hs control0 z -
            ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
              rate rewards C_star C_h q t s hs control0 z ∂
          ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0 := by
    calc
      _ = ∫ z : Ze, V (t.val + 1) (f z) - V t.val (f z) ∂
          ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0 := by
        exact (ReferenceFirstLiveSourcePhasePartition.integral_originalEmpty
          rate rewards C_star C_h q t s hs control0
          (fun omega => V (t.val + 1) omega - V t.val omega)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with z
        change firstLivePotentialAt rate rewards C_star C_h (t.val + 1) z.val.val -
          firstLivePotentialAt rate rewards C_star C_h t.val z.val.val = _
        rw [emptyFirstWindowPotentialAfter_eq rate rewards C_star C_h q t s hs control0 z,
          emptyFirstWindowPotentialBefore_eq rate rewards C_star C_h q t s hs control0 z]
  calc
    _ = ∫ z : Ze,
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
            rate rewards C_star C_h q t s hs control0 z -
          ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
            rate rewards C_star C_h q t s hs control0 z ∂
        ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0 := hpotential
    _ ≤ -(11 / 2 : ℝ) *
          (∫ z : Ze, Set.indicator
            (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0)
            (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
              rate rewards C_star C_h q t s hs control0) z ∂
            ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0).real
            (ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0) :=
      emptyPotentialDriftIntegral_sharp rate rewards C_star C_h q t s hs control0
    _ = _ := by
      rw [emptyGoodWeightedBacklogIntegral_eq_original rate rewards C_star C_h q t s hs control0,
        emptyGoodMass_eq_originalIntersection rate rewards C_star C_h q t s hs control0]

/-- N's nonempty original-source drift with R's actual sharp marker-rate
bound, retaining the same original good weighted-backlog cost. -/
theorem nonemptyOriginalPotentialStep_bound
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    (∫ omega in
      ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
        rate rewards C_star C_h q t s hs control0,
      firstLivePotentialAt rate rewards C_star C_h (t.val + 1) omega -
        firstLivePotentialAt rate rewards C_star C_h t.val omega ∂
      BootstrapPrivateRoundStreams.sourceInputLaw p) ≤
      -(11 / 2 : ℝ) *
          (∫ omega in
            ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
                rate rewards C_star C_h q t s hs control0 ∩
              {omega : SourceInput p |
                (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false},
            firstLiveWeightedBacklogAt rate rewards C_star C_h t.val omega ∂
            BootstrapPrivateRoundStreams.sourceInputLaw p) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real
            (ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
                rate rewards C_star C_h q t s hs control0 ∩
              {omega : SourceInput p |
                (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}) := by
  let Zplus := ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
  let muPlus := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let G := ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
  let E := ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
    rate rewards C_star C_h q t s hs control0
  let Hraw : Set (SourceInput p) := fun omega =>
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (List.take (t.val - firstLiveStart rate rewards C_star C_h omega)
        (firstLiveCells rate rewards C_star C_h omega))).overflow = false
  let H : Set (SourceInput p) :=
    {omega | (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}
  let marker := ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum
    rate rewards C_star C_h q t s hs control0
  have hG : MeasurableSet G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
      rate rewards C_star C_h q t s hs control0
  have hmarker : Integrable marker muPlus :=
    ReferenceFirstLiveConditionalWeightedDrift.integrable_markerRateWeightSum
      rate rewards C_star C_h q t s hs control0
  have hmarkerG := hmarker.indicator hG
  have hconstantG : Integrable
      (Set.indicator G (fun _ : Zplus => CanonicalRecordingRates.R p)) muPlus :=
    (integrable_const (CanonicalRecordingRates.R p)).indicator hG
  have hpoint (z : Zplus) :
      Set.indicator G marker z ≤
        Set.indicator G (fun _ : Zplus => CanonicalRecordingRates.R p) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      exact ReferenceFirstLiveRateBoundedDrift.markerRateWeightSum_le_R
        rate rewards C_star C_h q t s hs control0 z
    · simp [Set.indicator_of_notMem hz]
  have hmono := integral_mono_ae hmarkerG hconstantG (Filter.Eventually.of_forall hpoint)
  have hmass := ReferenceFirstLiveOriginalBranchEstimates.branchSourceMeasure_strictPast_mass_real
    rate rewards C_star C_h q t s hs control0
  have hmassRaw : muPlus.real G =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ Hraw) := by
    simpa only [E, Hraw, Zplus, muPlus, G, firstLiveStart, firstLiveCells] using hmass
  have hHraw : Hraw = H := by
    ext omega
    change (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (List.take (t.val - firstLiveStart rate rewards C_star C_h omega)
        (firstLiveCells rate rewards C_star C_h omega))).overflow = false ↔
      (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false
    simp [firstLiveRunAt, firstLiveQueue, firstLiveStart, firstLiveCells]
  have hmarkerBound :
      (∫ z : Zplus, Set.indicator G marker z ∂muPlus) ≤
        CanonicalRecordingRates.R p *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ Hraw) := by
    calc
      _ ≤ ∫ z : Zplus,
          Set.indicator G (fun _ : Zplus => CanonicalRecordingRates.R p) z ∂muPlus := hmono
      _ = CanonicalRecordingRates.R p * muPlus.real G := by
        rw [integral_indicator_const (CanonicalRecordingRates.R p) hG, smul_eq_mul]
        ring
      _ = CanonicalRecordingRates.R p *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ Hraw) := by
        rw [hmassRaw]
  have hdrift := ReferenceFirstLiveOriginalBranchEstimates.potential_drift_integral_originalBranch_rate_sum
    rate rewards C_star C_h q t s hs control0
  calc
    _ ≤ -(11 / 2 : ℝ) *
          (∫ omega in E ∩ Hraw, firstLiveWeightedBacklogAt rate rewards C_star C_h t.val omega ∂
            BootstrapPrivateRoundStreams.sourceInputLaw p) +
        (∫ z : Zplus, Set.indicator G marker z ∂muPlus) +
        (33 / 2 : ℝ) * (p.m : ℝ) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ Hraw) := by
      simpa only [E, Hraw, Zplus, muPlus, G, marker,
        firstLivePotentialAt, firstLiveWeightedBacklogAt,
        firstLiveStart, firstLiveCells] using hdrift
    _ ≤ -(11 / 2 : ℝ) *
          (∫ omega in E ∩ Hraw, firstLiveWeightedBacklogAt rate rewards C_star C_h t.val omega ∂
            BootstrapPrivateRoundStreams.sourceInputLaw p) +
        CanonicalRecordingRates.R p *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ Hraw) +
        (33 / 2 : ℝ) * (p.m : ℝ) *
          (BootstrapPrivateRoundStreams.sourceInputLaw p).real (E ∩ Hraw) := by
      nlinarith [hmarkerBound]
    _ = _ := by
      rw [hHraw]
      simp only [firstLiveWeightedBacklogAt]
      ring

/-- A birth boundary has no old queue updates, so its weighted backlog cost is
zero even though the first update is retained in the after-potential. -/
theorem firstLiveWeightedBacklogAt_birth_eq_zero
    (t : Fin p.T) (omega : SourceInput p)
    (hstart : firstLiveStart rate rewards C_star C_h omega = t.val) :
    firstLiveWeightedBacklogAt rate rewards C_star C_h t.val omega = 0 := by
  have hzero : t.val - ReferenceCompletePhysicalHistory.physicalStart
      rate omega rewards C_star C_h = 0 := by
    simpa [firstLiveStart] using congrArg (fun n : ℕ => t.val - n) hstart
  simp [firstLiveWeightedBacklogAt,
    ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt,
    ReferenceFirstLiveCalendarPrefixReadout.queueParameters, hzero,
    RecordedWeightedDrift.weightedBacklog, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

/-- The retained cost vanishes on every exact birth source, by its actual
empty strict-past run. -/
theorem retainedWeightedBacklogCost_eq_zero_on_birth
    (t : Fin p.T) (omega : SourceInput p)
    (hbirth : omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
      rate rewards C_star C_h t 2) :
    retainedWeightedBacklogCost rate rewards C_star C_h t omega = 0 := by
  have hb : t.val = firstLiveStart rate rewards C_star C_h omega := by
    change (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
      t.val = ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
      at hbirth
    simpa [firstLiveStart] using hbirth.2
  have hW := firstLiveWeightedBacklogAt_birth_eq_zero rate rewards C_star C_h t omega hb.symm
  simp [retainedWeightedBacklogCost, Set.indicator, hW]


open ReferenceFirstLiveCalendarIntegralAssembly
open ReferenceFirstLiveSourcePhasePartition
open ReferenceFirstLiveBranchIntegralTransport

local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "V" => firstLivePotentialAt rate rewards C_star C_h
local notation "W" => firstLiveWeightedBacklogAt rate rewards C_star C_h

private theorem integral_continuing_phases (t : Fin p.T) (control0 : TimeControl p)
    {f : SourceInput p → ℝ} (hf : Integrable f mu) :
    (∫ omega in sourcePhase rate rewards C_star C_h t 3 ∪
        sourcePhase rate rewards C_star C_h t 4, f omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ omega in originalBranchEvent rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0, f omega ∂mu) +
         (∫ omega in originalEmptyEvent rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0, f omega ∂mu)) := by
  let cells : Fin 2 × (Fin (ConstructorDimensions.M p) × Fin (t.val + 1)) →
      Set (SourceInput p) := fun a =>
    if a.1.val = 0 then originalBranchEvent rate rewards C_star C_h a.2.1 t
      a.2.2.val (Nat.lt_succ_iff.mp a.2.2.isLt) control0
    else originalEmptyEvent rate rewards C_star C_h a.2.1 t
      a.2.2.val (Nat.lt_succ_iff.mp a.2.2.isLt) control0
  have hcover : (⋃ a, cells a) = sourcePhase rate rewards C_star C_h t 3 ∪
      sourcePhase rate rewards C_star C_h t 4 := by
    rw [sourcePhase_nonempty_iUnion rate rewards C_star C_h t control0,
      sourcePhase_empty_iUnion rate rewards C_star C_h t control0]
    ext omega
    simp [cells, Fin.exists_fin_two]
  have hm : ∀ a, MeasurableSet (cells a) := by
    rintro ⟨i, q, v⟩
    dsimp only [cells]
    split
    · exact measurableSet_originalBranchEvent rate rewards C_star C_h q t v.val
        (Nat.lt_succ_iff.mp v.isLt) control0
    · exact measurableSet_originalEmptyEvent rate rewards C_star C_h q t v.val
        (Nat.lt_succ_iff.mp v.isLt) control0
  rw [← hcover, integral_iUnion_fintype hm
    (source_images_pairwise rate rewards C_star C_h t control0) (fun _ => hf.integrableOn)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, cells, Finset.sum_add_distrib]

private theorem integral_retainedCost_on_continuing
    (t : Fin p.T) (control0 : TimeControl p) {E : Set (SourceInput p)}
    (hE : E ⊆ sourcePhase rate rewards C_star C_h t 3 ∪
      sourcePhase rate rewards C_star C_h t 4) :
    (∫ omega in E, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) =
      ∫ omega in E ∩ {omega : SourceInput p |
        (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false},
        W t.val omega ∂mu := by
  simp only [retainedWeightedBacklogCost]
  rw [setIntegral_indicator
    (measurableSet_retainedEnabledEvent rate rewards C_star C_h t control0)]
  have hsets : E ∩ retainedEnabledEvent rate rewards C_star C_h t =
      E ∩ {omega : SourceInput p |
        (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false} := by
    ext omega
    rw [retainedEnabledEvent_eq_phaseRestriction rate rewards C_star C_h t control0]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, Or.inr (hE h.1), h.2⟩
  rw [hsets]

/-- The actual retained cost is exactly the finite disjoint sum of the
nonempty and empty continuing costs. The birth cost vanishes. -/
theorem integral_retainedWeightedBacklogCost_eq_sum
    (t : Fin p.T) (control0 : TimeControl p) :
    (∫ omega, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ omega in originalBranchEvent rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0 ∩
              {omega : SourceInput p |
                (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false},
            W t.val omega ∂mu) +
         (∫ omega in originalEmptyEvent rate rewards C_star C_h q t v.val
            (Nat.lt_succ_iff.mp v.isLt) control0 ∩
              {omega : SourceInput p |
                (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false},
            W t.val omega ∂mu)) := by
  let E := sourcePhase rate rewards C_star C_h t 3 ∪ sourcePhase rate rewards C_star C_h t 4
  have hm : MeasurableSet E :=
    (measurableSet_sourcePhase rate rewards C_star C_h t control0 3).union
      (measurableSet_sourcePhase rate rewards C_star C_h t control0 4)
  have hrestrict : (∫ omega, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) =
      ∫ omega in E, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu := by
    rw [← integral_indicator hm]
    apply integral_congr_ae
    filter_upwards [] with omega
    by_cases hmem : omega ∈ E
    · exact (Set.indicator_of_mem hmem _).symm
    · rw [Set.indicator_of_notMem hmem]
      by_cases hk : omega ∈ retainedEnabledEvent rate rewards C_star C_h t
      · have hp := hk
        rw [retainedEnabledEvent_eq_phaseRestriction rate rewards C_star C_h t control0] at hp
        rcases hp.1 with hb | hc
        · exact retainedWeightedBacklogCost_eq_zero_on_birth rate rewards C_star C_h t omega hb
        · exact (hmem hc).elim
      · exact Set.indicator_of_notMem hk _
  rw [hrestrict, integral_continuing_phases rate rewards C_star C_h t control0
    (integrable_retainedWeightedBacklogCost rate rewards C_star C_h t control0)]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  · apply integral_retainedCost_on_continuing rate rewards C_star C_h t control0
    intro omega ho
    apply Or.inl
    rw [sourcePhase_nonempty_iUnion rate rewards C_star C_h t control0]
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, ho⟩⟩
  · apply integral_retainedCost_on_continuing rate rewards C_star C_h t control0
    intro omega ho
    apply Or.inr
    rw [sourcePhase_empty_iUnion rate rewards C_star C_h t control0]
    exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, ho⟩⟩

/-- The drift constant is nonnegative, permitting enlargement of good masses
to their full unnormalized source-stratum masses. -/
theorem sourceDriftConstant_nonneg : 0 ≤ sourceDriftConstant (p := p) := by
  have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
  have hsub : 0 ≤ 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
  unfold sourceDriftConstant CanonicalRecordingRates.R
  positivity

/-- The sharp one-step drift on the complete original source. Only the
literal retained-enabled cost is charged, including the first overflow update. -/
theorem integral_firstLivePotential_step_le
    (t : Fin p.T) (control0 : TimeControl p) :
    (∫ omega, V (t.val + 1) omega - V t.val omega ∂mu) ≤
      -(11 / 2 : ℝ) *
        (∫ omega, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) +
      sourceDriftConstant (p := p) := by
  let H := {omega : SourceInput p |
    (firstLiveRunAt rate rewards C_star C_h t.val omega).overflow = false}
  let f := fun omega : SourceInput p => V (t.val + 1) omega - V t.val omega
  let nonemptyCell := fun (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) =>
    originalBranchEvent rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let emptyCell := fun (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) =>
    originalEmptyEvent rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let cost := fun q v => (∫ omega in nonemptyCell q v ∩ H, W t.val omega ∂mu) +
    (∫ omega in emptyCell q v ∩ H, W t.val omega ∂mu)
  let mass := fun q v => (mu).real (nonemptyCell q v) + (mu).real (emptyCell q v)
  let delta := fun q v => (∫ omega in nonemptyCell q v, f omega ∂mu) +
    (∫ omega in emptyCell q v, f omega ∂mu)
  let birthMass := fun q : Fin (ConstructorDimensions.M p) =>
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ
  let birth := fun q : Fin (ConstructorDimensions.M p) =>
    ∫ z, ReferenceFirstLaunchEnergyInitialization.birthPotential
      rate rewards C_star C_h q t control0 z ∂
      ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  have hC := sourceDriftConstant_nonneg (p := p)
  have hcost : (∫ omega, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) =
      ∑ q, ∑ v, cost q v :=
    integral_retainedWeightedBacklogCost_eq_sum rate rewards C_star C_h t control0
  have hmass : (∑ q, birthMass q) + (∑ q, ∑ v, mass q v) ≤ 1 := by
    simpa only [birthMass, mass, nonemptyCell, emptyCell, Measure.real_def,
      branchSourceMeasure_mass_original, muEmpty_mass_original] using
      source_cell_mass_le_one rate rewards C_star C_h t control0
  have hbirth (q : Fin (ConstructorDimensions.M p)) :
      birth q ≤ sourceDriftConstant (p := p) * birthMass q :=
    ReferenceFirstLaunchEnergyInitialization.integral_birthPotential
      rate rewards C_star C_h q t control0
  have hcell (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
      delta q v ≤ -(11 / 2 : ℝ) * cost q v + sourceDriftConstant (p := p) * mass q v := by
    have hN := nonemptyOriginalPotentialStep_bound rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0
    have hE := emptyOriginalPotentialStep_bound rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0
    have hn : (mu).real (nonemptyCell q v ∩ H) ≤ (mu).real (nonemptyCell q v) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have he : (mu).real (emptyCell q v ∩ H) ≤ (mu).real (emptyCell q v) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have hm := mul_le_mul_of_nonneg_left (add_le_add hn he) hC
    change (∫ omega in nonemptyCell q v, f omega ∂mu) ≤
      -(11 / 2 : ℝ) * (∫ omega in nonemptyCell q v ∩ H, W t.val omega ∂mu) +
      sourceDriftConstant (p := p) * (mu).real (nonemptyCell q v ∩ H) at hN
    change (∫ omega in emptyCell q v, f omega ∂mu) ≤
      -(11 / 2 : ℝ) * (∫ omega in emptyCell q v ∩ H, W t.val omega ∂mu) +
      sourceDriftConstant (p := p) * (mu).real (emptyCell q v ∩ H) at hE
    dsimp only [delta, cost, mass]
    linarith only [hN, hE, hm]
  have hstep : (∫ omega, f omega ∂mu) = (∑ q, birth q) + (∑ q, ∑ v, delta q v) := by
    dsimp only [birth, delta, nonemptyCell, emptyCell, f, firstLivePotentialAt]
    simp_rw [← integral_originalBranch rate rewards C_star C_h,
      ← integral_originalEmpty rate rewards C_star C_h]
    exact integral_potential_calendar_step rate rewards C_star C_h t control0
  calc
    (∫ omega, f omega ∂mu) = (∑ q, birth q) + (∑ q, ∑ v, delta q v) := hstep
    _ ≤ (∑ q, sourceDriftConstant (p := p) * birthMass q) +
        ∑ q, ∑ v, (-(11 / 2 : ℝ) * cost q v + sourceDriftConstant (p := p) * mass q v) :=
      add_le_add (Finset.sum_le_sum fun q _ => hbirth q)
        (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun v _ => hcell q v)
    _ = -(11 / 2 : ℝ) * (∑ q, ∑ v, cost q v) +
        sourceDriftConstant (p := p) * ((∑ q, birthMass q) + (∑ q, ∑ v, mass q v)) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ -(11 / 2 : ℝ) *
        (∫ omega, retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) +
        sourceDriftConstant (p := p) := by
      rw [hcost]
      exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left hmass hC).trans_eq (mul_one _))

/-- Set-integral form of the sharp drift on the literal retained event. -/
theorem integral_firstLivePotential_step_le_setIntegral
    (t : Fin p.T) (control0 : TimeControl p) :
    (∫ omega, V (t.val + 1) omega - V t.val omega ∂mu) ≤
      -(11 / 2 : ℝ) * (∫ omega in retainedEnabledEvent rate rewards C_star C_h t,
        W t.val omega ∂mu) + sourceDriftConstant (p := p) := by
  simpa only [retainedWeightedBacklogCost, integral_indicator
    (measurableSet_retainedEnabledEvent rate rewards C_star C_h t control0)] using
    integral_firstLivePotential_step_le rate rewards C_star C_h t control0

/-- The original-source calendar telescope, whose initial potential is zero
on every source, including sources without a launch. -/
theorem integral_firstLivePotential_telescope (control0 : TimeControl p) :
    (∫ omega, V p.T omega ∂mu) =
      ∑ t : Fin p.T, ∫ omega, V (t.val + 1) omega - V t.val omega ∂mu := by
  refine (integral_potential_calendar_telescope rate rewards C_star C_h control0).trans ?_
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_potential_calendar_step rate rewards C_star C_h t control0).symm

/-- The sharp finite first-window weighted-backlog budget under the original
complete-source law. This is the first-window contribution to
`sq:eq:weighted-backlog`, for later multi-assignment learning-regret assembly. -/
theorem weightedBacklog_budget (control0 : TimeControl p) :
    (∫ omega, ∑ t : Fin p.T,
      Set.indicator (retainedEnabledEvent rate rewards C_star C_h t)
        (firstLiveWeightedBacklogAt rate rewards C_star C_h t.val) omega ∂mu) ≤
      (2 / 11 : ℝ) * (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (p.T : ℝ) := by
  change (∫ omega, ∑ t : Fin p.T,
    retainedWeightedBacklogCost rate rewards C_star C_h t omega ∂mu) ≤
      (2 / 11 : ℝ) * sourceDriftConstant (p := p) * (p.T : ℝ)
  have hsum := Finset.sum_le_sum fun (t : Fin p.T) (_ : t ∈ Finset.univ) =>
    integral_firstLivePotential_step_le rate rewards C_star C_h t control0
  rw [← integral_firstLivePotential_telescope rate rewards C_star C_h control0] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hterminal : 0 ≤ ∫ omega, V p.T omega ∂mu :=
    integral_nonneg fun omega =>
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_horizon_nonneg
        rate rewards C_star C_h omega
  rw [integral_finsetSum Finset.univ fun t _ =>
    integrable_retainedWeightedBacklogCost rate rewards C_star C_h t control0]
  linarith only [hsum, hterminal]

end Bandits.Support.ReferenceFirstLiveOriginalCalendarWeightedBacklogBound

end
