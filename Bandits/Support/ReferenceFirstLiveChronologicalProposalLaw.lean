/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLivePastTestProposalLaw
public import Bandits.Support.ReferenceFirstLiveCanonicalProposalJointLaw

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# The actual chronological proposal on the original first-live branches

For each original continuing or empty-pending source and the same auxiliary
array, select the current calendar cell from the existing chronological path.
Its proposal is the accepted full-past PRE-gated proposal. Applying the
accepted full-past proposal law gives the bounded-test integral identity for
the actual chronological field on each original unnormalized branch measure.

Sources: sources/zip4/manuscript/06_interruptions.tex:381-397,
sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366, and
sources/zip4/manuscript/08_main_theorem.tex:78-109.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceFirstLiveChronologicalProposalLaw

open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveCanonicalProposalJointLaw
open ReferenceFirstLivePastTestProposalLaw
open ReferenceFirstLivePostUpdateProposalLaw
open ReferenceFirstLiveOverflowReadout

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev AuxiliaryArray := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

abbrev SourcePlus := ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0

abbrev EmptySource := ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0

abbrev TaggedSource := SourcePlus rate rewards C_star C_h q t s hs control0 ⊕
  EmptySource rate rewards C_star C_h q t s hs control0

abbrev PastObservation := PastTestObservation rate rewards C_star C_h q t s hs control0

/-- The source-stratum point retained by either actual branch. -/
def chronologicalSource (tagged : TaggedSource rate rewards C_star C_h q t s hs control0) :
    ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) :=
  Sum.elim Subtype.val Subtype.val tagged

/-- The whole-source chronological index selected by the accepted alignment
theorem. Its bound is proved from the actual branch, rather than supplied as a
cell or history premise. -/
def chronologicalCurrentIndex
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0) :
    Fin (wholeFirstLiveWindow rate rewards C_star C_h
      (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val).length := by
  refine ⟨t.val - s, ?_⟩
  simpa only [chronologicalSource] using
    (source_whole_prefix_alignment rate rewards C_star C_h q t s hs control0 tagged).choose

@[simp] theorem chronologicalCurrentIndex_val
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0) :
    (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).val =
      t.val - s := rfl

/-- The date-t logical cell on the same source and auxiliary array. The Fin
index uses the bound produced by the actual source-alignment theorem. -/
def chronologicalCurrentEntry
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) : LogicalCell p rate :=
  let source := chronologicalSource rate rewards C_star C_h q t s hs control0 tagged
  let k := chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged
  (firstLiveChronologicalPrefix rate rewards C_star C_h (source.val, aux))[k.val]'(by
    rw [firstLiveChronologicalPrefix_length]
    exact k.isLt)

/-- The accepted complete observation on the selected original branch. -/
def chronologicalPastObservation
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) : PastObservation rate rewards C_star C_h q t s hs control0 :=
  match tagged with
  | .inl z => continuingPastTestObservation rate rewards C_star C_h q t s hs control0 z aux
  | .inr z => emptyPastTestObservation rate rewards C_star C_h q t s hs control0 z aux

/-- The proposal bit from the original whole current control retained by the
actual split on each branch. -/
def chronologicalPhysicalProposalBit
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0) : Bool :=
  match tagged with
  | .inl z => physicalProposalBit rate
      (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
        rate rewards C_star C_h q t s hs control0 z).2
  | .inr z => physicalProposalBit rate
      (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
        rate rewards C_star C_h q t s hs control0 z).2

/-- The selected whole-window record is the literal original current record;
the alignment also supplies the same whole numerical prefix used below. -/
theorem chronologicalCurrentEntry_originalRecord
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0) :
    (wholeFirstLiveWindow rate rewards C_star C_h
      (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val)[
        (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).val]'
          ((chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).isLt) =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0
          (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged) := by
  obtain ⟨_, hrecord, _, _⟩ :=
    source_whole_prefix_alignment rate rewards C_star C_h q t s hs control0 tagged
  simpa only [chronologicalSource, chronologicalCurrentIndex_val] using hrecord

/-- The chronological path entry is exactly the literal append of its aligned
original record, source-derived numerical cell, strict-prefix queue state,
and the same auxiliary array. -/
theorem chronologicalCurrentEntry_eq_append
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) :
    chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux =
      appendLogicalCell
        ((wholeFirstLiveWindow rate rewards C_star C_h
          (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val)[
          (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).val]'
            ((chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).isLt))
        (wholeLiveCell rate rewards C_star C_h
          (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val
          ((wholeFirstLiveWindow rate rewards C_star C_h
            (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val)[
            (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).val]'
              ((chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).isLt))
          (by
            change ((wholeFirstLiveWindow rate rewards C_star C_h
              (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val)[
                (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).val]'
                  ((chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).isLt)) ∈
              LiveWindow (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
                (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val rewards C_star C_h)
            exact List.getElem_mem
              (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).isLt))
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          ((wholeFirstLiveCells rate rewards C_star C_h
            (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val).take
              (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged).val)) aux := by
  simpa only [chronologicalCurrentEntry, chronologicalSource] using
    firstLiveChronologicalPrefix_get rate rewards C_star C_h
    (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val aux
    (chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged)

private theorem originalCurrentRecord_proposalBit_eq
    (source : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)) :
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 source).input.row
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 source).input.time =
      physicalProposalBit rate
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs source) := by
  let record := ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
    rate rewards C_star C_h q t s hs control0 source
  have hrow : record.input.row = source.val.1.2 q := by
    change record.input.rows record.input.selected = source.val.1.2 q
    rw [ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_rows,
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_selected]
  have hprop : (CompletePublicTable.completeRowLearning p record.input.row
      record.input.time).1 (propLabel p) =
      (ReferenceFirstLiveRecordingSourceCylinder.originalControl
        rate rewards C_star C_h q t s hs source).1 (propLabel p) := by
    rw [CompletePublicTable.completeRowLearning, hrow,
      ReferenceFirstLiveRecordingSourceCylinder.originalControl,
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time]
  exact completeRowProposalBit_eq_physicalProposalBit rate record.input.row
    record.input.time
    (ReferenceFirstLiveRecordingSourceCylinder.originalControl
      rate rewards C_star C_h q t s hs source) hprop

private theorem chronologicalCurrentEntry_before_eq_run
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) :
    (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux).before =
      RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((wholeFirstLiveCells rate rewards C_star C_h
          (chronologicalSource rate rewards C_star C_h q t s hs control0 tagged).val).take
            (t.val - s)) := by
  let source := chronologicalSource rate rewards C_star C_h q t s hs control0 tagged
  let k := chronologicalCurrentIndex rate rewards C_star C_h q t s hs control0 tagged
  have hstates := firstLiveChronologicalPrefix_queue_states rate rewards C_star C_h
    source.val aux k
  simpa only [chronologicalCurrentEntry, source, k, chronologicalCurrentIndex_val] using hstates.1

/-- The original actual PRE overflow readout is the before flag of this date-t
chronological entry. The detecting update remains in the entry; only its PRE
flag gates the proposal. -/
theorem chronologicalCurrentEntry_beforeOverflow_eq
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) :
    pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0
        (chronologicalPastObservation rate rewards C_star C_h q t s hs control0 tagged aux) =
      (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux).before.overflow := by
  let source := chronologicalSource rate rewards C_star C_h q t s hs control0 tagged
  let run := RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    ((wholeFirstLiveCells rate rewards C_star C_h source.val).take (t.val - s))
  let readout := ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
    rate rewards C_star C_h q t s hs control0 source
  have hprefix := originalSource_numerical_prefix
    rate rewards C_star C_h q t s hs control0 tagged
  dsimp only at hprefix
  have hread : ReferenceFirstLivePostUpdateProposalLaw.liveNumericalPast
      rate rewards C_star C_h q t s hs control0
        (originalLiveRemainder rate rewards C_star C_h q t s hs control0 tagged) = readout := by
    cases tagged with
    | inl point =>
        have h := continuingPreProposalReadout_actual
          rate rewards C_star C_h q t s hs control0 point
        exact congrArg (fun y : Option (Fin p.K) × NumericalUpdateFields p =>
          (y.2.beforeRegisters, y.2.beforeOverflow, y.2.beforeRecords)) h
    | inr point =>
        have h := emptyPreProposalReadout_actual
          rate rewards C_star C_h q t s hs control0 point
        exact congrArg (fun y : Option (Fin p.K) × NumericalUpdateFields p =>
          (y.2.beforeRegisters, y.2.beforeOverflow, y.2.beforeRecords)) h
  have hstate : (run.registers, run.overflow, run.records) = readout := by
    exact hprefix.symm.trans hread
  have hflag : readout.2.1 = run.overflow := by
    exact congrArg (fun y : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))) => y.2.1)
      hstate.symm
  have hactual : pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0
      (chronologicalPastObservation rate rewards C_star C_h q t s hs control0 tagged aux) =
      readout.2.1 := by
    cases tagged with
    | inl point =>
        simpa only [chronologicalPastObservation, readout, source, chronologicalSource,
          Sum.elim_inl,
          ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields] using
          continuingPastTestBeforeOverflow_actual
            rate rewards C_star C_h q t s hs control0 point aux
    | inr point =>
        simpa only [chronologicalPastObservation, readout, source, chronologicalSource,
          Sum.elim_inr,
          ReferenceFirstLivePostUpdateProposalLaw.numericalUpdateFields] using
          emptyPastTestBeforeOverflow_actual
            rate rewards C_star C_h q t s hs control0 point aux
  calc
    pastTestBeforeOverflow rate rewards C_star C_h q t s hs control0
        (chronologicalPastObservation rate rewards C_star C_h q t s hs control0 tagged aux) =
      readout.2.1 := hactual
    _ = run.overflow := hflag
    _ = (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux).before.overflow := by
      have hbefore := chronologicalCurrentEntry_before_eq_run
        rate rewards C_star C_h q t s hs control0 tagged aux
      exact congrArg (fun state : RecordedQueueRun.RunState p.K => state.overflow)
        hbefore.symm

/-- The proposal stored in the date-t chronological entry is exactly the
accepted computed-PRE formula and the original physical proposal bit. This
uses the actual source record and whole current control on both branches. -/
theorem chronologicalCurrentEntry_proposal_eq_pastTestLogicalProposal
    (tagged : TaggedSource rate rewards C_star C_h q t s hs control0)
    (aux : AuxiliaryArray p) :
    (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux).proposal =
      pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
        (chronologicalPastObservation rate rewards C_star C_h q t s hs control0 tagged aux)
        (chronologicalPhysicalProposalBit rate rewards C_star C_h q t s hs control0 tagged) := by
  let source := chronologicalSource rate rewards C_star C_h q t s hs control0 tagged
  have hrecord := chronologicalCurrentEntry_originalRecord
    rate rewards C_star C_h q t s hs control0 tagged
  have happended := chronologicalCurrentEntry_eq_append
    rate rewards C_star C_h q t s hs control0 tagged aux
  have hbit : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 source).input.row
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 source).input.time =
      chronologicalPhysicalProposalBit rate rewards C_star C_h q t s hs control0 tagged := by
    cases tagged with
    | inl point =>
        simpa only [source, chronologicalSource, Sum.elim_inl, chronologicalPhysicalProposalBit,
          ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit] using
          originalCurrentRecord_proposalBit_eq rate rewards C_star C_h q t s hs control0
            point.val
    | inr point =>
        simpa only [source, chronologicalSource, Sum.elim_inr, chronologicalPhysicalProposalBit,
          ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit] using
          originalCurrentRecord_proposalBit_eq rate rewards C_star C_h q t s hs control0
            point.val
  have hproposal :
      (chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux).proposal =
        (!((chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 tagged aux).before.overflow) &&
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
              rate rewards C_star C_h q t s hs control0 source).input.row
            (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
              rate rewards C_star C_h q t s hs control0 source).input.time) := by
    have hrecordBit := congrArg
      (fun r => FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time)
      hrecord
    rw [happended]
    simp only [appendLogicalCell]
    rw [hrecordBit]
  rw [hproposal, hbit]
  rw [← chronologicalCurrentEntry_beforeOverflow_eq
    rate rewards C_star C_h q t s hs control0 tagged aux]
  rfl

/-- Apply the accepted full-past proposal law to the actual continuing
chronological entry. The original finite branch measure and complete
auxiliary array are unchanged; the multiplier uses the actual PRE flag. -/
theorem continuingSource_chronologicalProposal_integral
    (_hpos : s < t.val)
    (F : PastObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) :
    let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let obs := fun za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      continuingPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
    let current := fun za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 (.inl za.1) za.2
    Integrable (fun za => F (obs za)) (μ.prod auxLaw) ∧
    Integrable (fun za => F (obs za) * pastTestBoolIndicator (current za).proposal)
      (μ.prod auxLaw) ∧
    (∫ za, F (obs za) * pastTestBoolIndicator (current za).proposal ∂μ.prod auxLaw) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearBitIndicator (current za).before.overflow
          ∂μ.prod auxLaw := by
  classical
  dsimp only
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let obs := fun za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    continuingPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
  let current := fun za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 (.inl za.1) za.2
  have hlaw := continuingSource_completePast_clearPRE_logical_integral
    rate rewards C_star C_h q t s hs control0 _hpos F hF C hC
  rcases hlaw with ⟨hFint, hlogicalInt, hlaw⟩
  have hproposal (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      (current za).proposal =
        pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
          (obs za) (physicalProposalBit rate
            (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
              rate rewards C_star C_h q t s hs control0 za.1).2) := by
    simpa only [current, obs, chronologicalPastObservation,
      chronologicalPhysicalProposalBit] using
      chronologicalCurrentEntry_proposal_eq_pastTestLogicalProposal
        rate rewards C_star C_h q t s hs control0 (.inl za.1) za.2
  have hclear (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      pastTestClearIndicator rate rewards C_star C_h q t s hs control0 (obs za) =
        pastTestClearBitIndicator (current za).before.overflow := by
    rw [pastTestClearIndicator]
    rw [← chronologicalCurrentEntry_beforeOverflow_eq
      rate rewards C_star C_h q t s hs control0 (.inl za.1) za.2]
    rfl
  have hpoint (za : SourcePlus rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      F (obs za) * pastTestBoolIndicator (current za).proposal =
        F (obs za) * pastTestBoolIndicator
          (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
            (obs za) (physicalProposalBit rate
              (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
                rate rewards C_star C_h q t s hs control0 za.1).2)) := by
    rw [hproposal za]
  have hactualInt := hlogicalInt.congr
    (Filter.Eventually.of_forall (fun za => (hpoint za).symm))
  refine ⟨hFint, hactualInt, ?_⟩
  calc
    (∫ za, F (obs za) * pastTestBoolIndicator (current za).proposal ∂μ.prod auxLaw) =
        ∫ za, F (obs za) * pastTestBoolIndicator
          (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
            (obs za) (physicalProposalBit rate
              (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
                rate rewards C_star C_h q t s hs control0 za.1).2)) ∂μ.prod auxLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearIndicator rate rewards C_star C_h q t s hs control0
          (obs za) ∂μ.prod auxLaw := hlaw
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearBitIndicator (current za).before.overflow
          ∂μ.prod auxLaw := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun za =>
        congrArg (fun x : ℝ => F (obs za) * x) (hclear za))

/-- Apply the accepted full-past proposal law to the actual empty-pending
chronological entry, retaining its own finite unnormalized branch and the
same complete auxiliary array. -/
theorem emptySource_chronologicalProposal_integral
    (_hpos : s < t.val)
    (F : PastObservation rate rewards C_star C_h q t s hs control0 → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : ∀ o, ‖F o‖ ≤ C) :
    let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
      rate rewards C_star C_h q t s hs control0
    let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
    let obs := fun za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      emptyPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
    let current := fun za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
      chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 (.inr za.1) za.2
    Integrable (fun za => F (obs za)) (μ.prod auxLaw) ∧
    Integrable (fun za => F (obs za) * pastTestBoolIndicator (current za).proposal)
      (μ.prod auxLaw) ∧
    (∫ za, F (obs za) * pastTestBoolIndicator (current za).proposal ∂μ.prod auxLaw) =
      FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearBitIndicator (current za).before.overflow
          ∂μ.prod auxLaw := by
  classical
  dsimp only
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let auxLaw := ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
  let obs := fun za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    emptyPastTestObservation rate rewards C_star C_h q t s hs control0 za.1 za.2
  let current := fun za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p =>
    chronologicalCurrentEntry rate rewards C_star C_h q t s hs control0 (.inr za.1) za.2
  have hlaw := emptySource_completePast_clearPRE_logical_integral
    rate rewards C_star C_h q t s hs control0 _hpos F hF C hC
  rcases hlaw with ⟨hFint, hlogicalInt, hlaw⟩
  have hproposal (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      (current za).proposal =
        pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
          (obs za) (physicalProposalBit rate
            (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
              rate rewards C_star C_h q t s hs control0 za.1).2) := by
    simpa only [current, obs, chronologicalPastObservation,
      chronologicalPhysicalProposalBit] using
      chronologicalCurrentEntry_proposal_eq_pastTestLogicalProposal
        rate rewards C_star C_h q t s hs control0 (.inr za.1) za.2
  have hclear (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      pastTestClearIndicator rate rewards C_star C_h q t s hs control0 (obs za) =
        pastTestClearBitIndicator (current za).before.overflow := by
    rw [pastTestClearIndicator]
    rw [← chronologicalCurrentEntry_beforeOverflow_eq
      rate rewards C_star C_h q t s hs control0 (.inr za.1) za.2]
    rfl
  have hpoint (za : EmptySource rate rewards C_star C_h q t s hs control0 × AuxiliaryArray p) :
      F (obs za) * pastTestBoolIndicator (current za).proposal =
        F (obs za) * pastTestBoolIndicator
          (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
            (obs za) (physicalProposalBit rate
              (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
                rate rewards C_star C_h q t s hs control0 za.1).2)) := by
    rw [hproposal za]
  have hactualInt := hlogicalInt.congr
    (Filter.Eventually.of_forall (fun za => (hpoint za).symm))
  refine ⟨hFint, hactualInt, ?_⟩
  calc
    (∫ za, F (obs za) * pastTestBoolIndicator (current za).proposal ∂μ.prod auxLaw) =
        ∫ za, F (obs za) * pastTestBoolIndicator
          (pastTestLogicalProposal rate rewards C_star C_h q t s hs control0
            (obs za) (physicalProposalBit rate
              (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
                rate rewards C_star C_h q t s hs control0 za.1).2)) ∂μ.prod auxLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearIndicator rate rewards C_star C_h q t s hs control0
          (obs za) ∂μ.prod auxLaw := hlaw
    _ = FollowerCutoffScan.proposalHazard p rate.eta.val *
        ∫ za, F (obs za) * pastTestClearBitIndicator (current za).before.overflow
          ∂μ.prod auxLaw := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun za =>
        congrArg (fun x : ℝ => F (obs za) * x) (hclear za))

end Bandits.Support.ReferenceFirstLiveChronologicalProposalLaw

end
