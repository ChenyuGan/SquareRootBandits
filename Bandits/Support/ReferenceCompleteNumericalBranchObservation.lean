/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterLiveCalendarMeasurability
public import Bandits.Support.ReferenceLaterCollectionCalendarMeasurability

/-!
# Dispatcher-tagged optional numerical observations

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

This observation tags the existing actual-round readouts by their retained
dispatcher phase. It keeps every suffix date and every absent readout. It does
not add a run, queue, state, or coverage assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCompleteNumericalBranchObservation

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  ReferenceLaterLiveCalendarMeasurability.SourceInput (p := p)
abbrev RoundRecord :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev RoundRecordCode :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
abbrev NumericalCoordinates (p : ConstructorDimensions.Parameters) :=
  ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p)
abbrev NumericalEntry (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Fin p.T × (RoundRecordCode rate ×
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p))

/-- Erase the readout certificate by the existing full numerical coordinate
projection. -/
def encodeNumerical (cell : RecordedQueueRun.RoundInput p.K) :
    NumericalCoordinates p :=
  ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates cell

/-- The actual selected phase chooses which existing optional numerical
readout is retained. -/
def branchReadout (b : ℕ) (record : RoundRecord rate) :
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p) :=
  match ReferenceCoordinatorRecorderCallTrace.selection
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
  | none => none
  | some selected =>
      if ReferenceCoordinatorRecorderCallTrace.live
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected then
        ((ReferenceLaterLiveNumericalReadout.laterLiveReadout b record).map
          encodeNumerical).map Sum.inl
      else
        ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).map
          encodeNumerical).map Sum.inr

abbrev TraceCellData (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
    (Bool × (Bool × Option (CoordinatorRecordingOperation.Output p)))

private def flattenOptionalReadout {α : Type*} : Option (Option α) → Option α
  | none => none
  | some value => value

private theorem measurable_flattenOptionalReadout {α : Type*} [MeasurableSpace α] :
    Measurable (flattenOptionalReadout : Option (Option α) → Option α) := by
  have hEquiv : Measurable (Equiv.optionEquivSumPUnit (Option α)) := comap_measurable _
  have hElim : Measurable
      (Sum.elim (id : Option α → Option α) (fun _ : PUnit => (none : Option α))) :=
    measurable_id.sumElim measurable_const
  have h := hElim.comp hEquiv
  convert h using 1
  funext value
  cases value <;> rfl

/-- Select a numerical readout from the same trace cell that carries the
actual dispatch phase, then remove only the outer absent-call option. -/
private def branchFromTraceCell (traceCell : Option (TraceCellData rate))
    (liveCells collectionCells : Option (NumericalCoordinates p)) :
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p) :=
  flattenOptionalReadout (traceCell.map fun observed =>
    if observed.2.1 then liveCells.map Sum.inl else collectionCells.map Sum.inr)

private theorem branchReadout_eq_traceCell (b : ℕ) (record : RoundRecord rate) :
    branchReadout rate b record =
      branchFromTraceCell rate
        (ReferenceCoordinatorRecorderCallTrace.cell
          (ReferenceActiveHorizonMeasurability.roundRecordCode record))
        ((ReferenceLaterLiveNumericalReadout.laterLiveReadout b record).map encodeNumerical)
        ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).map
          encodeNumerical) := by
  classical
  cases hselection : ReferenceCoordinatorRecorderCallTrace.selection
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
  | none =>
      simp [branchFromTraceCell, ReferenceCoordinatorRecorderCallTrace.cell,
        flattenOptionalReadout, branchReadout, hselection]
  | some selected =>
      by_cases hphase : ReferenceCoordinatorRecorderCallTrace.live
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected = true
      · simp [branchFromTraceCell, ReferenceCoordinatorRecorderCallTrace.cell,
          flattenOptionalReadout, branchReadout, hselection, hphase]
      · have hphaseFalse : ReferenceCoordinatorRecorderCallTrace.live
            (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected = false := by
          cases h : ReferenceCoordinatorRecorderCallTrace.live
              (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected <;>
            simp_all
        simp [branchFromTraceCell, ReferenceCoordinatorRecorderCallTrace.cell,
          flattenOptionalReadout, branchReadout, hselection, hphaseFalse]

private def selectTraceCellBranch (observed : TraceCellData rate)
    (cells : Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) :
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p) :=
  if observed.2.1 then cells.1.map Sum.inl else cells.2.map Sum.inr

private theorem measurable_selectTraceCellBranch :
    Measurable (fun z : TraceCellData rate ×
      (Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) =>
        selectTraceCellBranch rate z.1 z.2) := by
  have hleft : Measurable (fun z : TraceCellData rate ×
      (Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) =>
        z.2.1.map Sum.inl) :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun q : NumericalCoordinates p × (TraceCellData rate ×
        (Option (NumericalCoordinates p) × Option (NumericalCoordinates p))) =>
          (Sum.inl q.1 : NumericalCoordinates p ⊕ NumericalCoordinates p))
      (measurable_inl.comp measurable_fst) (fun z => z.2.1)
      (measurable_fst.comp measurable_snd)
  have hright : Measurable (fun z : TraceCellData rate ×
      (Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) =>
        z.2.2.map Sum.inr) :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun q : NumericalCoordinates p × (TraceCellData rate ×
        (Option (NumericalCoordinates p) × Option (NumericalCoordinates p))) =>
          (Sum.inr q.1 : NumericalCoordinates p ⊕ NumericalCoordinates p))
      (measurable_inr.comp measurable_fst) (fun z => z.2.2)
      (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hbit : Measurable (fun z : TraceCellData rate ×
      (Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) => z.1.2.1) :=
    (measurable_fst.comp measurable_snd).comp measurable_fst
  exact Measurable.ite ((measurableSet_singleton true).preimage hbit) hleft hright

private theorem measurable_branchFromTraceCell :
    Measurable (fun z : Option (TraceCellData rate) ×
      (Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) =>
        branchFromTraceCell rate z.1 z.2.1 z.2.2) := by
  have hnested :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun q : TraceCellData rate ×
        (Option (TraceCellData rate) ×
          (Option (NumericalCoordinates p) × Option (NumericalCoordinates p))) =>
          selectTraceCellBranch rate q.1 q.2.2)
      ((measurable_selectTraceCellBranch rate).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      (fun z => z.1) measurable_fst
  have hflat := measurable_flattenOptionalReadout.comp hnested
  have heq : (fun z : Option (TraceCellData rate) ×
      (Option (NumericalCoordinates p) × Option (NumericalCoordinates p)) =>
        branchFromTraceCell rate z.1 z.2.1 z.2.2) =
      flattenOptionalReadout ∘ (fun z => z.1.map fun observed =>
        selectTraceCellBranch rate observed z.2) := by
    funext z
    rfl
  rw [heq]
  exact hflat

private abbrev CompleteIndexedSource (k : ℕ) :=
  ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k

private def indexedBranchReadout (k : ℕ)
    (z : ℕ × CompleteIndexedSource rate rewards C_star C_h k) :
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p) :=
  branchReadout rate z.1
    (ReferenceLaterLiveCalendarMeasurability.indexedRecord rate rewards C_star C_h k z.2)

private theorem measurable_indexedBranchReadout (k : ℕ) :
    Measurable (indexedBranchReadout rate rewards C_star C_h k) := by
  have hcode : Measurable (fun z : ℕ × CompleteIndexedSource rate rewards C_star C_h k =>
      ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
        rate rewards C_star C_h k z.2) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_actualRecordCodeAt
      rate rewards C_star C_h k).comp measurable_snd
  have htrace :=
    (ReferenceCoordinatorRecorderCallTrace.measurable_cell (p := p) (rate := rate)).comp hcode
  have hlive := ReferenceLaterLiveCalendarMeasurability.measurable_indexedNumericalReadout
    rate rewards C_star C_h k
  have hcollection :=
    ReferenceLaterCollectionSourceReadoutMeasurability.measurable_actualReadout_numerical
      rate rewards C_star C_h k
  have hproduct := htrace.prodMk (hlive.prodMk hcollection)
  have heq : indexedBranchReadout rate rewards C_star C_h k =
      (fun z => branchFromTraceCell rate
        (ReferenceCoordinatorRecorderCallTrace.cell
          (ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
            rate rewards C_star C_h k z.2))
        ((ReferenceLaterLiveCalendarMeasurability.indexedReadout
          rate rewards C_star C_h k z).map
            ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates)
        ((ReferenceLaterCollectionSourceReadoutMeasurability.actualReadout
          rate rewards C_star C_h k z).map
            ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates)) := by
    funext z
    change branchReadout rate z.1
      (ReferenceLaterLiveCalendarMeasurability.indexedRecord rate rewards C_star C_h k z.2) = _
    rw [branchReadout_eq_traceCell]
    rfl
  rw [heq]
  exact (measurable_branchFromTraceCell rate).comp hproduct

/-- The literal strict-sigma mask carried by the original selected payload. -/
def strictSigmaMask (start : ℕ) (code : RoundRecordCode rate) : Bool :=
  match ReferenceCoordinatorRecorderCallTrace.selection code with
  | none => false
  | some selected => decide (start < selected.1.payload.sigma.val)

/-- The incoming coordinator tag retained in the original pre-state code. -/
def incomingLiveTag (code : RoundRecordCode rate) : Bool :=
  match code.2.1.1 with
  | .inr (.inl _) => true
  | _ => false

/-- The left partial projection of a dispatcher-tagged readout. -/
def leftProjection :
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p) →
      Option (NumericalCoordinates p)
  | none => none
  | some (.inl value) => some value
  | some (.inr _) => none

/-- The right partial projection of a dispatcher-tagged readout. -/
def rightProjection :
    Option (NumericalCoordinates p ⊕ NumericalCoordinates p) →
      Option (NumericalCoordinates p)
  | none => none
  | some (.inl _) => none
  | some (.inr value) => some value

@[simp] theorem leftProjection_map_inl (value : Option (NumericalCoordinates p)) :
    leftProjection (value.map Sum.inl) = value := by
  cases value <;> rfl

@[simp] theorem rightProjection_map_inl (value : Option (NumericalCoordinates p)) :
    rightProjection (value.map Sum.inl) = none := by
  cases value <;> rfl

@[simp] theorem leftProjection_map_inr (value : Option (NumericalCoordinates p)) :
    leftProjection (value.map Sum.inr) = none := by
  cases value <;> rfl

@[simp] theorem rightProjection_map_inr (value : Option (NumericalCoordinates p)) :
    rightProjection (value.map Sum.inr) = value := by
  cases value <;> rfl

@[simp] theorem leftProjection_map_inl_encode
    (value : Option (RecordedQueueRun.RoundInput p.K)) :
    leftProjection (value.map (Sum.inl ∘ encodeNumerical)) =
      value.map encodeNumerical := by
  cases value <;> rfl

@[simp] theorem rightProjection_map_inl_encode
    (value : Option (RecordedQueueRun.RoundInput p.K)) :
    rightProjection (value.map (Sum.inl ∘ encodeNumerical)) = none := by
  cases value <;> rfl

@[simp] theorem leftProjection_map_inr_encode
    (value : Option (RecordedQueueRun.RoundInput p.K)) :
    leftProjection (value.map (Sum.inr ∘ encodeNumerical)) = none := by
  cases value <;> rfl

@[simp] theorem rightProjection_map_inr_encode
    (value : Option (RecordedQueueRun.RoundInput p.K)) :
    rightProjection (value.map (Sum.inr ∘ encodeNumerical)) =
      value.map encodeNumerical := by
  cases value <;> rfl

private theorem recordPreparation_eq_prepare (record : RoundRecord rate) :
    record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
  simpa [ReferenceActivePhysicalStep.step] using
    congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
      output.preparation) record.output_eq

private theorem traceSelection_eq_dispatch (record : RoundRecord rate) :
    ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      (ReferenceActivePhysicalStep.dispatch record.input).selection.map
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection) :=
  (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).1

private theorem traceSelection_eq_preparation (record : RoundRecord rate) :
    ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      record.output.preparation.coordinator.selection.map
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection) := by
  rw [traceSelection_eq_dispatch]
  rw [recordPreparation_eq_prepare]
  rfl

private theorem dispatch_eq_preparedCoordinator (record : RoundRecord rate) :
    ReferenceActivePhysicalStep.dispatch record.input = record.output.preparation.coordinator := by
  have hprep := recordPreparation_eq_prepare rate record
  have hcoord := congrArg
    (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input => prepared.coordinator)
    hprep
  simpa [ReferenceActivePhysicalStep.prepare] using hcoord.symm

private theorem incomingLiveTag_true_of_livePreparation (record : RoundRecord rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput record.input registers owned base))
    (hcoord : record.output.preparation.coordinator =
      .live registers owned base outcome) :
    incomingLiveTag rate (ReferenceActiveHorizonMeasurability.roundRecordCode record) = true := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
      .live registers owned base outcome := by
    exact (dispatch_eq_preparedCoordinator rate record).trans hcoord
  cases hstate : record.input.state.coordinator with
  | live _ _ _ =>
      simp [incomingLiveTag, ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
  | first =>
      have hfirst := ReferenceActivePhysicalStep.dispatch_first record.input hstate
      rw [hfirst] at hdispatch
      cases hdispatch
  | collection payload ledger savedProposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff
        let input := ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff
        cases hcall : CoordinatorRoundDispatch.dispatch (.collection input) with
        | collection outcome =>
            have houter : ReferenceActivePhysicalStep.dispatch record.input =
                .collection payload ledger clock cutoff outcome := by
              simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff, hcall, input, clock, cutoff] <;>
                rfl
            rw [houter] at hdispatch
            cases hdispatch
      · have houter := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff
          record.input payload ledger savedProposal hstate hcutoff
        rw [houter.1] at hdispatch
        cases hdispatch
  | dagger =>
      have houter := ReferenceActivePhysicalStep.dispatch_dagger record.input hstate
      rw [houter] at hdispatch
      cases hdispatch

private theorem incomingLiveTag_false_of_collectionPreparation (record : RoundRecord rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (hcoord : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff outcome) :
    incomingLiveTag rate (ReferenceActiveHorizonMeasurability.roundRecordCode record) = false := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
      .collection payload ledger clock cutoff outcome := by
    exact (dispatch_eq_preparedCoordinator rate record).trans hcoord
  cases hstate : record.input.state.coordinator with
  | live registers owned base =>
      let input := ReferenceActivePhysicalStep.liveInput record.input registers owned base
      cases hcall : CoordinatorRoundDispatch.dispatch (.live input) with
      | live outcome =>
          have houter : ReferenceActivePhysicalStep.dispatch record.input =
              .live registers owned base outcome := by
            simp [ReferenceActivePhysicalStep.dispatch, hstate, hcall, input] <;> rfl
          rw [houter] at hdispatch
          cases hdispatch
  | first =>
      simp [incomingLiveTag, ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
  | collection _ _ _ =>
      simp [incomingLiveTag, ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]
  | dagger =>
      simp [incomingLiveTag, ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]

private theorem selectedDispatch_of_collectionBranch
    (record : RoundRecord rate)
    (hbranch : ReferenceCoordinatorRecorderCallTrace.actualBranchInput record ≠ none) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      (ReferenceActivePhysicalStep.dispatch record.input).selection = some selected := by
  have hne : (ReferenceActivePhysicalStep.dispatch record.input).selection ≠ none := by
    intro hnone
    exact hbranch
      ((ReferenceCoordinatorRecorderCallCorrespondence.actualBranchInput_eq_none_iff
        record).2 hnone)
  cases hsel : (ReferenceActivePhysicalStep.dispatch record.input).selection with
  | none => exact (hne hsel).elim
  | some selected => exact ⟨selected, rfl⟩

private theorem collectionReadout_phase
    (b : ℕ) (record : RoundRecord rate) (cell : RecordedQueueRun.RoundInput p.K)
    (hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record =
      some cell) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
          some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) ∧
      ReferenceCoordinatorRecorderCallTrace.live
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false := by
  classical
  have hsome :
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).isSome = true := by
    simp [hreadout]
  have hdomain :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain b record).mp hsome
  cases hcoord : record.output.preparation.coordinator with
  | live registers owned base outcome =>
      cases houtcome : outcome with
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
          have hcoordExact : record.output.preparation.coordinator =
              .live registers owned base
                (.cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm) := by
            rw [hcoord, houtcome]
          have hbranch :
              ReferenceCoordinatorRecorderCallTrace.actualBranchInput record ≠ none := by
            simp [ReferenceCoordinatorRecorderCallTrace.actualBranchInput, hcoordExact]
          obtain ⟨selected, hselected⟩ := selectedDispatch_of_collectionBranch
            rate record hbranch
          have hprepSelected : record.output.preparation.coordinator.selection = some selected := by
            rw [recordPreparation_eq_prepare]
            simpa [ReferenceActivePhysicalStep.prepare] using hselected
          have hselection :
              ReferenceCoordinatorRecorderCallTrace.selection
                (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
                some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
            rw [traceSelection_eq_preparation]
            simp [hprepSelected]
          have hphase := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits
            record selected hselected
          rw [hcoordExact] at hphase
          have hphaseFalse :
              ReferenceCoordinatorRecorderCallTrace.live
                (ReferenceActiveHorizonMeasurability.roundRecordCode record)
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false := by
            exact hphase.1
          exact ⟨selected, hselection, hphaseFalse⟩
      | _ =>
          have hdomainFalse : False := by simp [hcoord, houtcome] at hdomain
          exact hdomainFalse.elim
  | collection payload ledger clock cutoff outcome =>
      cases houtcome : outcome with
      | continuing core snapshot boundary scores =>
          have hcoordExact : record.output.preparation.coordinator =
              .collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores) := by
            rw [hcoord, houtcome]
          have hbranch :
              ReferenceCoordinatorRecorderCallTrace.actualBranchInput record ≠ none := by
            simp [ReferenceCoordinatorRecorderCallTrace.actualBranchInput, hcoordExact]
          obtain ⟨selected, hselected⟩ := selectedDispatch_of_collectionBranch
            rate record hbranch
          have hprepSelected : record.output.preparation.coordinator.selection = some selected := by
            rw [recordPreparation_eq_prepare]
            simpa [ReferenceActivePhysicalStep.prepare] using hselected
          have hselection :
              ReferenceCoordinatorRecorderCallTrace.selection
                (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
                some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
            rw [traceSelection_eq_preparation]
            simp [hprepSelected]
          have hphase := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits
            record selected hselected
          rw [hcoordExact] at hphase
          have hphaseFalse :
              ReferenceCoordinatorRecorderCallTrace.live
                (ReferenceActiveHorizonMeasurability.roundRecordCode record)
                (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false := by
            exact hphase.1
          exact ⟨selected, hselection, hphaseFalse⟩
      | _ =>
          have hdomainFalse : False := by simp [hcoord, houtcome] at hdomain
          exact hdomainFalse.elim
  | first _ =>
      have hdomainFalse : False := by simp [hcoord] at hdomain
      exact hdomainFalse.elim
  | invalidCollectionCutoff =>
      have hdomainFalse : False := by simp [hcoord] at hdomain
      exact hdomainFalse.elim
  | dagger =>
      have hdomainFalse : False := by simp [hcoord] at hdomain
      exact hdomainFalse.elim

private theorem liveReadout_phase
    (b : ℕ) (record : RoundRecord rate) (cell : RecordedQueueRun.RoundInput p.K)
    (hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout b record = some cell) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
          some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) ∧
      ReferenceCoordinatorRecorderCallTrace.live
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
  obtain ⟨selected, hselectedPrep, _, hlive, _⟩ :=
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain b record).mp
      (by simp [hreadout])
  have hselection :
      ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
        some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
    rw [traceSelection_eq_preparation]
    simp [hselectedPrep]
  have hphase :
      ReferenceCoordinatorRecorderCallTrace.live
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
    rw [ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode record)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
      record.input.time rfl]
    simp [ReferenceLiveDispatchOutputMeasurability.encodeSelection, hlive]
  exact ⟨selected, hselection, hphase⟩

/-- Moving the comparison argument from zero to the original start removes a
live numerical cell exactly when the retained selected payload fails the
strict-sigma comparison. -/
theorem liveReadout_start_mask (start : ℕ) (record : RoundRecord rate) :
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout start record).map
        encodeNumerical =
      if strictSigmaMask rate start
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map encodeNumerical
      else none := by
  classical
  cases hselection : record.output.preparation.coordinator.selection with
  | none =>
      have htrace : ReferenceCoordinatorRecorderCallTrace.selection
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) = none := by
        rw [traceSelection_eq_preparation, hselection]
        rfl
      simp [strictSigmaMask,
        ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselection, htrace]
  | some selected =>
      have htrace : ReferenceCoordinatorRecorderCallTrace.selection
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
            some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
        rw [traceSelection_eq_preparation, hselection]
        rfl
      by_cases hs : start < selected.view.payload.sigma.val
      · have hzero : 0 < selected.view.payload.sigma.val := by omega
        simp [strictSigmaMask, htrace,
          ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselection, hs, hzero,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]
      · simp [strictSigmaMask, htrace,
          ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselection, hs,
          ReferenceLiveDispatchOutputMeasurability.encodeSelection]

/-- The original later-collection readout depends on its start comparison
only on an incoming live cutoff branch. -/
theorem collectionReadout_start_mask (start : ℕ) (record : RoundRecord rate) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start record).map
        encodeNumerical =
      if incomingLiveTag rate
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
        if strictSigmaMask rate start
            (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
            encodeNumerical
        else none
      else
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
          encodeNumerical := by
  classical
  cases hcoord : record.output.preparation.coordinator with
  | live registers owned base outcome =>
      cases houtcome : outcome with
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
          have hcoordExact : record.output.preparation.coordinator =
              .live registers owned base
                (.cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm) := by
            rw [hcoord, houtcome]
          have htag := incomingLiveTag_true_of_livePreparation rate record registers owned base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm)
            hcoordExact
          have htrace := traceSelection_eq_preparation rate record
          rw [hcoordExact] at htrace
          simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt] at htrace
          have hmask : strictSigmaMask rate start
              (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
                decide (start < registers.payload.sigma.val) := by
            unfold strictSigmaMask
            rw [htrace]
            simp [ReferenceLiveDispatchOutputMeasurability.encodeSelection]
          by_cases hunoccupied :
              ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record
          · by_cases hs : start < registers.payload.sigma.val
            · have hzero : 0 < registers.payload.sigma.val := by omega
              simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
                hcoordExact, hunoccupied, hs, hzero, htag, hmask]
            · simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
                hcoordExact, hunoccupied, hs, htag, hmask]
          · simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              hcoordExact, hunoccupied, htag, hmask]
      | _ =>
          simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord, houtcome]
  | collection payload ledger clock cutoff outcome =>
      cases houtcome : outcome with
      | continuing core snapshot boundary scores =>
          have hcoordExact : record.output.preparation.coordinator =
              .collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores) := by
            rw [hcoord, houtcome]
          have htag := incomingLiveTag_false_of_collectionPreparation rate record payload ledger
            clock cutoff (.continuing core snapshot boundary scores) hcoordExact
          simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            hcoordExact, htag]
      | _ =>
          simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord, houtcome]
  | first outcome => simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord]
  | invalidCollectionCutoff =>
      simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord]
  | dagger => simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hcoord]

/-- The live and collection readout domains are disjoint on every actual
round, by their phase bits in the same selected dispatcher frame. -/
theorem readouts_disjoint (b : ℕ) (record : RoundRecord rate) :
    ¬ ((ReferenceLaterLiveNumericalReadout.laterLiveReadout b record).isSome = true ∧
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).isSome = true) := by
  intro hboth
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout b record with
  | none => simp [hl] at hboth
  | some liveCell =>
      cases hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record with
      | none => simp [hc] at hboth
      | some collectionCell =>
          obtain ⟨liveSelection, hliveSelection, hphaseLive⟩ :=
            liveReadout_phase rate b record liveCell hl
          obtain ⟨collectionSelection, hcollectionSelection, hphaseCollection⟩ :=
            collectionReadout_phase rate b record collectionCell hc
          have hsame :
              ReferenceLiveDispatchOutputMeasurability.encodeSelection liveSelection =
                ReferenceLiveDispatchOutputMeasurability.encodeSelection collectionSelection :=
            Option.some.inj (hliveSelection.symm.trans hcollectionSelection)
          rw [hsame] at hphaseLive
          rw [hphaseLive] at hphaseCollection
          cases hphaseCollection

/-- The branch projections reconstruct both original optional numerical
readouts exactly. -/
theorem branch_readout_projections (b : ℕ) (record : RoundRecord rate) :
    (leftProjection (branchReadout rate b record),
      rightProjection (branchReadout rate b record)) =
      ((ReferenceLaterLiveNumericalReadout.laterLiveReadout b record).map
          encodeNumerical,
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).map
          encodeNumerical) := by
  classical
  cases hselection : ReferenceCoordinatorRecorderCallTrace.selection
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
  | none =>
      have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout b record = none := by
        cases hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout b record with
        | none => rfl
        | some cell =>
            obtain ⟨selected, hsel, _⟩ :=
              liveReadout_phase rate b record cell hreadout
            rw [hselection] at hsel
            cases hsel
      have hcollectionNone : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
          b record = none := by
        cases hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record with
        | none => rfl
        | some cell =>
            obtain ⟨selected, hsel, _⟩ :=
              collectionReadout_phase rate b record cell hreadout
            rw [hselection] at hsel
            cases hsel
      simp [branchReadout, hselection, hliveNone, hcollectionNone,
        leftProjection, rightProjection]
  | some selected =>
      by_cases hphase : ReferenceCoordinatorRecorderCallTrace.live
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected = true
      · have hcollectionNone :
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record = none := by
          cases hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
              b record with
          | none => rfl
          | some cell =>
              obtain ⟨other, hsel, hotherPhase⟩ :=
                collectionReadout_phase rate b record cell hreadout
              have hsame : selected =
                  ReferenceLiveDispatchOutputMeasurability.encodeSelection other :=
                Option.some.inj (hselection.symm.trans hsel)
              rw [hsame] at hphase
              rw [hphase] at hotherPhase
              cases hotherPhase
        simp [branchReadout, hselection, hphase, hcollectionNone]
      · have hliveNone :
            ReferenceLaterLiveNumericalReadout.laterLiveReadout b record = none := by
          cases hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout b record with
          | none => rfl
          | some cell =>
              obtain ⟨other, hsel, hotherPhase⟩ :=
                liveReadout_phase rate b record cell hreadout
              have hsame : selected =
                  ReferenceLiveDispatchOutputMeasurability.encodeSelection other :=
                Option.some.inj (hselection.symm.trans hsel)
              rw [hsame] at hphase
              exact (hphase hotherPhase).elim
        have hphaseFalse :
            ReferenceCoordinatorRecorderCallTrace.live
              (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected = false := by
          cases h : ReferenceCoordinatorRecorderCallTrace.live
              (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected <;>
            simp_all
        simp [branchReadout, hselection, hphaseFalse, hliveNone]

/-- The right tagged projection recovers the collection readout with the
special strict-sigma mask for an incoming live cutoff. -/
theorem collection_projection_start_factor (start : ℕ) (record : RoundRecord rate) :
    (if incomingLiveTag rate
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
      if strictSigmaMask rate start
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
        rightProjection (branchReadout rate 0 record)
      else none
    else rightProjection (branchReadout rate 0 record)) =
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start record).map
        encodeNumerical := by
  have hprojection :
      rightProjection (branchReadout rate 0 record) =
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
          encodeNumerical := by
    simpa using congrArg Prod.snd (branch_readout_projections rate 0 record)
  rw [hprojection]
  exact (collectionReadout_start_mask rate start record).symm

/-- The left tagged projection recovers the original later-live readout at
its requested start by applying the retained strict-sigma mask. -/
theorem live_projection_start_factor (start : ℕ) (record : RoundRecord rate) :
    (if strictSigmaMask rate start
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
      leftProjection (branchReadout rate 0 record) else none) =
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout start record).map
        encodeNumerical := by
  have hprojection :
      leftProjection (branchReadout rate 0 record) =
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map encodeNumerical := by
    simpa using congrArg Prod.fst (branch_readout_projections rate 0 record)
  rw [hprojection]
  exact (liveReadout_start_mask rate start record).symm

/-- The enriched calendar is a literal map of the complete actual suffix. -/
def branchCalendar (b : ℕ) (source : SourceInput p) :
    List (NumericalEntry rate) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).map fun record =>
      (record.input.time,
        (ReferenceActiveHorizonMeasurability.roundRecordCode record,
          branchReadout rate b record))

/-- Apply the retained live mask entrywise to the enriched calendar. -/
def maskedLiveCalendar (start : ℕ) (source : SourceInput p) :
    List (Fin p.T × Option (NumericalCoordinates p)) :=
  (branchCalendar rate rewards C_star C_h 0 source).map fun entry =>
    (entry.1,
      if strictSigmaMask rate start entry.2.1 then leftProjection entry.2.2 else none)

/-- The masked left projection of the one enriched suffix recovers the
original later-live numerical calendar at the actual physical start. -/
theorem original_live_calendar_factor (source : SourceInput p) :
    maskedLiveCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
      ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
        rate rewards C_star C_h source := by
  unfold maskedLiveCalendar branchCalendar
  simp only [ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar,
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro record _
  exact congrArg (fun cell : Option (NumericalCoordinates p) =>
      (record.input.time, cell))
    (live_projection_start_factor rate
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record)

/-- Apply the actual input-state and incoming-live strict-sigma masks to the
right projection, retaining collection readout NONE entries. -/
def maskedCollectionCalendar (start : ℕ) (source : SourceInput p) :
    List (Fin p.T × Option (NumericalCoordinates p)) :=
  (branchCalendar rate rewards C_star C_h 0 source).map fun entry =>
    (entry.1,
      if incomingLiveTag rate entry.2.1 then
        if strictSigmaMask rate start entry.2.1 then rightProjection entry.2.2 else none
      else rightProjection entry.2.2)

/-- The masked right projection recovers the original later-collection
numerical calendar at the same physical start. -/
theorem original_collection_calendar_factor (source : SourceInput p) :
    maskedCollectionCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
      ReferenceLaterCollectionCalendarMeasurability.numericalCalendar
        rate rewards C_star C_h source := by
  unfold maskedCollectionCalendar branchCalendar
  simp only [ReferenceLaterCollectionCalendarMeasurability.numericalCalendar,
    ReferenceLaterCollectionArrivalReadout.partialCalendar,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro record _
  exact congrArg (fun cell : Option (NumericalCoordinates p) =>
      (record.input.time, cell))
    (collection_projection_start_factor rate
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record)

/-- The admitted collection arithmetic sends the same enabled bit and full
numerical cell to the existing integer-arrival coordinates. -/
theorem arrivalCoordinates_from_numerical
    (cell : RecordedQueueRun.RoundInput p.K) :
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical
        rate (encodeNumerical cell) =
      ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate cell := by
  simpa [encodeNumerical,
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates,
    ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates,
    ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates,
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates] using
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates
      rate cell

/-- The two public arrival projections agree on the same literal source
cell. -/
theorem collectionArrivalCoordinates_eq_live
    (cell : RecordedQueueRun.RoundInput p.K) :
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell =
      ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate cell := by
  have hcoordinates :
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell =
        encodeNumerical cell := rfl
  calc
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell =
        ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
          (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell) :=
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates
        rate cell).symm
    _ = ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
          (encodeNumerical cell) := by rw [hcoordinates]
    _ = ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate cell :=
      arrivalCoordinates_from_numerical rate cell

/-- Apply the retained left mask and then the admitted numerical-to-arrival
map entrywise. -/
def maskedLiveArrivalCalendar (start : ℕ) (source : SourceInput p) :
    List (Fin p.T × Option (Bool × (Fin p.K → ℕ))) :=
  (branchCalendar rate rewards C_star C_h 0 source).map fun entry =>
    (entry.1,
      (if strictSigmaMask rate start entry.2.1 then
        leftProjection entry.2.2 else none).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

/-- The original later-live arrival calendar is the same masked projection of
the enriched numerical observation. -/
theorem original_live_arrival_calendar_factor (source : SourceInput p) :
    maskedLiveArrivalCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
      ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar
        rate rewards C_star C_h source := by
  unfold maskedLiveArrivalCalendar branchCalendar
  simp only [ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar,
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro record _
  have hcell := live_projection_start_factor rate
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record
  have harrival :
      (if strictSigmaMask rate
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
        leftProjection (branchReadout rate 0 record) else none).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate) =
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record).map
          (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate) := by
    calc
      _ = ((ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record).map
            encodeNumerical).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate) :=
        congrArg (fun cells : Option (NumericalCoordinates p) =>
          cells.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))
          hcell
      _ = _ := by
        simp only [Option.map_map, Function.comp_def]
        congr 1
  exact congrArg (fun cell : Option (Bool × (Fin p.K → ℕ)) =>
      (record.input.time, cell)) harrival

/-- Apply the incoming-live and strict-sigma masks, then project every
present numerical cell through the admitted arithmetic. -/
def maskedCollectionArrivalCalendar (start : ℕ) (source : SourceInput p) :
    List (Fin p.T × Option (Bool × (Fin p.K → ℕ))) :=
  (branchCalendar rate rewards C_star C_h 0 source).map fun entry =>
    (entry.1,
      (if incomingLiveTag rate entry.2.1 then
        if strictSigmaMask rate start entry.2.1 then rightProjection entry.2.2 else none
      else rightProjection entry.2.2).map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

/-- The original later-collection arrival calendar factors through the same
masked numerical observation and the public floor map. -/
theorem original_collection_arrival_calendar_factor (source : SourceInput p) :
    maskedCollectionArrivalCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
      ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar
        rate rewards C_star C_h source := by
  unfold maskedCollectionArrivalCalendar branchCalendar
  simp only [ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar,
    ReferenceLaterCollectionArrivalReadout.partialCalendar,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro record _
  have hcell := collection_projection_start_factor rate
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record
  have harrival :
      (if incomingLiveTag rate
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
        if strictSigmaMask rate
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (ReferenceActiveHorizonMeasurability.roundRecordCode record) then
          rightProjection (branchReadout rate 0 record)
        else none
      else rightProjection (branchReadout rate 0 record)).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate) =
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate) := by
    calc
      _ = ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) record).map
            encodeNumerical).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate) :=
        congrArg (fun cells : Option (NumericalCoordinates p) =>
          cells.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))
          hcell
      _ = _ := by
        simp only [Option.map_map, Function.comp_def]
        congr 1
  exact congrArg (fun cell : Option (Bool × (Fin p.K → ℕ)) =>
      (record.input.time, cell)) harrival

/-- The four existing numerical and integer-arrival calendars factor through
the same phase-tagged complete-suffix observation, with their original masks. -/
theorem original_calendars_factor (source : SourceInput p) :
    maskedLiveCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
        ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
          rate rewards C_star C_h source ∧
    maskedCollectionCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
        ReferenceLaterCollectionCalendarMeasurability.numericalCalendar
          rate rewards C_star C_h source ∧
    maskedLiveArrivalCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
        ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar
          rate rewards C_star C_h source ∧
    maskedCollectionArrivalCalendar rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) source =
        ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar
          rate rewards C_star C_h source := by
  exact ⟨original_live_calendar_factor rate rewards C_star C_h source,
    original_collection_calendar_factor rate rewards C_star C_h source,
    original_live_arrival_calendar_factor rate rewards C_star C_h source,
    original_collection_arrival_calendar_factor rate rewards C_star C_h source⟩

/-- The original later-live integer-arrival readout at one actual record. -/
def liveArrivalReadout (b : ℕ) (record : RoundRecord rate) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout b record).map
    (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)

/-- The original later-collection integer-arrival readout at one actual
record. -/
def collectionArrivalReadout (b : ℕ) (record : RoundRecord rate) :=
  (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout b record).map
    (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate)

/-- Project each tagged numerical branch through the one admitted
numerical-to-arrival map. Option and sum tags are preserved entrywise. -/
def arrivalBranchReadout (b : ℕ) (record : RoundRecord rate) :=
  (branchReadout rate b record).map
    (Sum.map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

/-- The tagged integer-arrival readout is exactly the selected original
later-live or later-collection arrival readout. -/
theorem arrival_factor (b : ℕ) (record : RoundRecord rate) :
    arrivalBranchReadout rate b record =
      match ReferenceCoordinatorRecorderCallTrace.selection
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
      | none => none
      | some selected =>
          if ReferenceCoordinatorRecorderCallTrace.live
              (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected then
            (liveArrivalReadout rate b record).map Sum.inl
          else (collectionArrivalReadout rate b record).map Sum.inr := by
  classical
  cases hselection : ReferenceCoordinatorRecorderCallTrace.selection
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
  | none => simp [arrivalBranchReadout, branchReadout, hselection]
  | some selected =>
      by_cases hphase : ReferenceCoordinatorRecorderCallTrace.live
          (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected = true
      · simp [arrivalBranchReadout, branchReadout, liveArrivalReadout,
          collectionArrivalReadout, hselection, hphase, Option.map_map,
          Function.comp_def, arrivalCoordinates_from_numerical,
          collectionArrivalCoordinates_eq_live]
      · have hphaseFalse : ReferenceCoordinatorRecorderCallTrace.live
            (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected = false := by
          cases h : ReferenceCoordinatorRecorderCallTrace.live
              (ReferenceActiveHorizonMeasurability.roundRecordCode record) selected <;>
            simp_all
        simp [arrivalBranchReadout, branchReadout, liveArrivalReadout,
          collectionArrivalReadout, hselection, hphaseFalse, Option.map_map,
          Function.comp_def, arrivalCoordinates_from_numerical,
          collectionArrivalCoordinates_eq_live]

/-- The enriched observation uses zero only as the comparison-guard argument. -/
def completeBranchObservation (source : SourceInput p) :=
  branchCalendar rate rewards C_star C_h 0 source

/-- Every actual suffix index retains its original date, code, and optional
tagged readout. -/
theorem branchCalendar_get (b : ℕ) (source : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (branchCalendar rate rewards C_star C_h b source).get
        ⟨k.val, by simp [branchCalendar]⟩ =
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.time,
        (ReferenceActiveHorizonMeasurability.roundRecordCode
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k),
          branchReadout rate b
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h).get k))) := by
  simp [branchCalendar]

/-- The tagged calendar has exactly one entry for every original suffix
record. -/
theorem branchCalendar_length (b : ℕ) (source : SourceInput p) :
    (branchCalendar rate rewards C_star C_h b source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h := by
  simp [branchCalendar,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length]

/-- The tagged calendar retains the exact original physical dates. -/
theorem branchCalendar_times (b : ℕ) (source : SourceInput p) :
    (branchCalendar rate rewards C_star C_h b source).map (fun entry => entry.1.val) =
      List.range'
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        1 := by
  unfold branchCalendar
  rw [List.map_map]
  change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
      (fun record => record.input.time.val) = _
  simpa [ReferenceActivePhysicalHorizon.calendar] using
    ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h

private def branchEntryOfRecord (b : ℕ) (record : RoundRecord rate) : NumericalEntry rate :=
  (record.input.time,
    (ReferenceActiveHorizonMeasurability.roundRecordCode record, branchReadout rate b record))

private def indexedBranchEntry (k : ℕ)
    (z : ℕ × CompleteIndexedSource rate rewards C_star C_h k) : NumericalEntry rate :=
  branchEntryOfRecord rate z.1
    (ReferenceLaterLiveCalendarMeasurability.indexedRecord rate rewards C_star C_h k z.2)

private theorem measurable_indexedBranchEntry (k : ℕ) :
    Measurable (indexedBranchEntry rate rewards C_star C_h k) := by
  have hreadout := measurable_indexedBranchReadout rate rewards C_star C_h k
  have htime := (ReferenceActivePhysicalStepMeasurability.measurable_time.comp
    (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
      rate rewards C_star C_h k)).comp
        (measurable_snd : Measurable
          (fun z : ℕ × CompleteIndexedSource rate rewards C_star C_h k => z.2))
  have hcode := (ReferenceCompleteSuffixInputMeasurability.measurable_actualRecordCodeAt
    rate rewards C_star C_h k).comp
      (measurable_snd : Measurable
        (fun z : ℕ × CompleteIndexedSource rate rewards C_star C_h k => z.2))
  exact htime.prodMk (hcode.prodMk hreadout)

private abbrev BranchPhysicalStartFiber (s : Fin (p.T + 1)) :=
  {source : SourceInput p //
    ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s.val}

private def branchSuffixIndexOnFiber (s : Fin (p.T + 1))
    (k : Fin (p.T - s.val)) (x : BranchPhysicalStartFiber rate rewards C_star C_h s) :
    Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h).length :=
  ⟨k.val, by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, x.property]
    exact k.isLt⟩

private def branchIndexedOnFiber (s : Fin (p.T + 1))
    (k : Fin (p.T - s.val)) (x : BranchPhysicalStartFiber rate rewards C_star C_h s) :
    CompleteIndexedSource rate rewards C_star C_h k.val :=
  ⟨x.val, (branchSuffixIndexOnFiber rate rewards C_star C_h s k x).isLt⟩

private theorem measurable_branchIndexedOnFiber (s : Fin (p.T + 1))
    (k : Fin (p.T - s.val)) :
    Measurable (branchIndexedOnFiber rate rewards C_star C_h s k) :=
  measurable_subtype_coe.subtype_mk
    (h := fun x => (branchSuffixIndexOnFiber rate rewards C_star C_h s k x).isLt)

private def branchFiberEntry (s : Fin (p.T + 1)) (k : Fin (p.T - s.val))
    (z : ℕ × BranchPhysicalStartFiber rate rewards C_star C_h s) : NumericalEntry rate :=
  branchEntryOfRecord rate z.1
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z.2.val rewards C_star C_h).get
        (branchSuffixIndexOnFiber rate rewards C_star C_h s k z.2))

private theorem branchFiberRecord_eq_indexed (s : Fin (p.T + 1))
    (k : Fin (p.T - s.val)) (x : BranchPhysicalStartFiber rate rewards C_star C_h s) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h).get
        (branchSuffixIndexOnFiber rate rewards C_star C_h s k x) =
      ReferenceLaterLiveCalendarMeasurability.indexedRecord rate rewards C_star C_h
        k.val (branchIndexedOnFiber rate rewards C_star C_h s k x) := by
  unfold ReferenceLaterLiveCalendarMeasurability.indexedRecord
  apply congrArg
  apply Fin.ext
  rfl

private theorem measurable_branchFiberEntry (s : Fin (p.T + 1))
    (k : Fin (p.T - s.val)) :
    Measurable (branchFiberEntry rate rewards C_star C_h s k) := by
  have hindex := measurable_branchIndexedOnFiber rate rewards C_star C_h s k
  have hmap : Measurable (fun z : ℕ × BranchPhysicalStartFiber rate rewards C_star C_h s =>
      (z.1, branchIndexedOnFiber rate rewards C_star C_h s k z.2)) :=
    measurable_fst.prodMk (hindex.comp measurable_snd)
  have heq : branchFiberEntry rate rewards C_star C_h s k =
      indexedBranchEntry rate rewards C_star C_h k.val ∘
        (fun z : ℕ × BranchPhysicalStartFiber rate rewards C_star C_h s =>
          (z.1, branchIndexedOnFiber rate rewards C_star C_h s k z.2)) := by
    funext z
    change branchEntryOfRecord rate z.1
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z.2.val rewards C_star C_h).get
            (branchSuffixIndexOnFiber rate rewards C_star C_h s k z.2)) =
      branchEntryOfRecord rate z.1
        (ReferenceLaterLiveCalendarMeasurability.indexedRecord rate rewards C_star C_h
          k.val (branchIndexedOnFiber rate rewards C_star C_h s k z.2))
    rw [branchFiberRecord_eq_indexed rate rewards C_star C_h s k z.2]
  rw [heq]
  exact (measurable_indexedBranchEntry rate rewards C_star C_h k.val).comp hmap

private def branchFiberCalendar (s : Fin (p.T + 1)) :
    ℕ × BranchPhysicalStartFiber rate rewards C_star C_h s → List (NumericalEntry rate) :=
  fun z => List.ofFn (fun k : Fin (p.T - s.val) =>
    branchFiberEntry rate rewards C_star C_h s k z)

private theorem measurable_branchListOfFn {X α : Type*} [MeasurableSpace X]
    [MeasurableSpace α] (n : ℕ) (f : X → Fin n → α) (hf : Measurable f) :
    Measurable (fun x => List.ofFn (f x)) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    ((List.ofFn (f x)).length,
      fun j => ReferenceActiveHorizonMeasurability.listObservationAt
        (List.ofFn (f x)) j))
  simp only [List.length_ofFn]
  apply measurable_const.prodMk
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j < n
  · let i : Fin n := ⟨j, hj⟩
    have heq : (fun x => ReferenceActiveHorizonMeasurability.listObservationAt
        (List.ofFn (f x)) j) = fun x => Sum.inr (f x i) := by
      funext x
      simp [ReferenceActiveHorizonMeasurability.listObservationAt, i, hj]
    rw [heq]
    exact measurable_inr.comp ((measurable_pi_apply i).comp hf)
  · have heq : (fun x => ReferenceActiveHorizonMeasurability.listObservationAt
        (List.ofFn (f x)) j) = fun _ => (Sum.inl () : Unit ⊕ α) := by
      funext x
      simp [ReferenceActiveHorizonMeasurability.listObservationAt, hj]
    rw [heq]
    exact measurable_const

private theorem measurable_branchFiberCalendar (s : Fin (p.T + 1)) :
    Measurable (branchFiberCalendar rate rewards C_star C_h s) := by
  apply measurable_branchListOfFn (p.T - s.val)
  apply measurable_pi_iff.mpr
  intro k
  exact measurable_branchFiberEntry rate rewards C_star C_h s k

private theorem branchFiberEntry_eq_record (s : Fin (p.T + 1))
    (k : Fin (p.T - s.val)) (z : ℕ × BranchPhysicalStartFiber rate rewards C_star C_h s) :
    branchFiberEntry rate rewards C_star C_h s k z =
      let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z.2.val rewards C_star C_h).get
          (branchSuffixIndexOnFiber rate rewards C_star C_h s k z.2)
      (record.input.time,
        (ReferenceActiveHorizonMeasurability.roundRecordCode record,
          branchReadout rate z.1 record)) := by
  simp [branchFiberEntry, branchEntryOfRecord]

private theorem branchCalendar_eq_fiberCalendar (s : Fin (p.T + 1))
    (b : ℕ) (x : BranchPhysicalStartFiber rate rewards C_star C_h s) :
    branchCalendar rate rewards C_star C_h b x.val =
      branchFiberCalendar rate rewards C_star C_h s (b, x) := by
  apply List.ext_getElem
  · simp [branchFiberCalendar, branchCalendar_length, x.property]
  · intro i hleft _
    have hi : i < p.T - s.val := by
      simpa [branchCalendar_length, x.property] using hleft
    let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate x.val rewards C_star C_h).length := ⟨i, by
          rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length, x.property]
          exact hi⟩
    have hget := branchCalendar_get rate rewards C_star C_h b x.val k
    have hactual : (branchCalendar rate rewards C_star C_h b x.val)[i] =
        let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate x.val rewards C_star C_h).get k
        (record.input.time,
          (ReferenceActiveHorizonMeasurability.roundRecordCode record,
            branchReadout rate b record)) := by
      simpa only [List.get_eq_getElem] using hget
    let j : Fin (p.T - s.val) := ⟨i, hi⟩
    have hindex : branchSuffixIndexOnFiber rate rewards C_star C_h s j x = k := by
      apply Fin.ext
      rfl
    have hentry := branchFiberEntry_eq_record rate rewards C_star C_h s j (b, x)
    simpa only [branchFiberCalendar, List.getElem_ofFn, hindex] using
      hactual.trans hentry.symm

private abbrev BranchObservationFiber (s : Fin (p.T + 1)) :=
  {z : ℕ × SourceInput p //
    ReferenceCompletePhysicalHistory.physicalStart rate z.2 rewards C_star C_h = s.val}

private def branchObservationFiberCoordinates (s : Fin (p.T + 1))
    (z : BranchObservationFiber rate rewards C_star C_h s) :
    ℕ × BranchPhysicalStartFiber rate rewards C_star C_h s :=
  (z.1.1, ⟨z.1.2, z.2⟩)

private theorem measurable_branchObservationFiberCoordinates (s : Fin (p.T + 1)) :
    Measurable (branchObservationFiberCoordinates rate rewards C_star C_h s) := by
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)

private theorem measurable_branchCalendar_onFiber (s : Fin (p.T + 1)) :
    Measurable (fun z : BranchObservationFiber rate rewards C_star C_h s =>
      branchCalendar rate rewards C_star C_h z.1.1 z.1.2) := by
  have heq : (fun z : BranchObservationFiber rate rewards C_star C_h s =>
      branchCalendar rate rewards C_star C_h z.1.1 z.1.2) =
        branchFiberCalendar rate rewards C_star C_h s ∘
          branchObservationFiberCoordinates rate rewards C_star C_h s := by
    funext z
    exact branchCalendar_eq_fiberCalendar rate rewards C_star C_h s z.1.1
      ⟨z.1.2, z.2⟩
  rw [heq]
  exact (measurable_branchFiberCalendar rate rewards C_star C_h s).comp
    (measurable_branchObservationFiberCoordinates rate rewards C_star C_h s)

/-- The complete dispatcher-tagged calendar is Borel on the original source
and the natural-valued comparison argument. -/
theorem measurable_branchCalendar :
    Measurable (fun z : ℕ × SourceInput p =>
      branchCalendar rate rewards C_star C_h z.1 z.2) := by
  intro target htarget
  have hstart : Measurable (fun z : ℕ × SourceInput p =>
      ReferenceCompletePhysicalHistory.physicalStart rate z.2 rewards C_star C_h) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_snd
  have hfiberSet (s : Fin (p.T + 1)) :
      MeasurableSet {z : ℕ × SourceInput p |
        ReferenceCompletePhysicalHistory.physicalStart rate z.2 rewards C_star C_h = s.val} :=
    (measurableSet_singleton s.val).preimage hstart
  have heq : (fun z : ℕ × SourceInput p =>
      branchCalendar rate rewards C_star C_h z.1 z.2) ⁻¹' target =
      ⋃ s : Fin (p.T + 1), Subtype.val ''
        ((fun z : BranchObservationFiber rate rewards C_star C_h s =>
          branchCalendar rate rewards C_star C_h z.1.1 z.1.2) ⁻¹' target) := by
    ext z
    constructor
    · intro hz
      let s : Fin (p.T + 1) := ⟨
        ReferenceCompletePhysicalHistory.physicalStart rate z.2 rewards C_star C_h,
        by
          have h := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate z.2 rewards C_star C_h
          omega⟩
      refine Set.mem_iUnion.mpr ⟨s, ?_⟩
      exact ⟨⟨z, rfl⟩, hz, rfl⟩
    · intro hz
      obtain ⟨s, x, hx, hvalue⟩ := Set.mem_iUnion.mp hz
      subst z
      exact hx
  rw [heq]
  exact MeasurableSet.iUnion fun s =>
    MeasurableSet.subtype_image (hfiberSet s)
      (measurable_branchCalendar_onFiber rate rewards C_star C_h s htarget)

/-- The zero-guard enriched observation is Borel on every original source
coordinate. -/
theorem measurable_completeBranchObservation :
    Measurable (completeBranchObservation rate rewards C_star C_h) := by
  have hzero : Measurable (fun source : SourceInput p => (0, source)) :=
    measurable_const.prodMk measurable_id
  change Measurable (fun source : SourceInput p => branchCalendar rate rewards C_star C_h 0 source)
  exact (measurable_branchCalendar rate rewards C_star C_h).comp hzero

abbrev BranchArrivalCoordinates (p : ConstructorDimensions.Parameters) :=
  Bool × (Fin p.K → ℕ)

abbrev BranchArrivalEntry (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Fin p.T × Option (BranchArrivalCoordinates p ⊕ BranchArrivalCoordinates p)

local instance branchArrivalOptionMeasurableSpace :
    MeasurableSpace (Option (BranchArrivalCoordinates p ⊕ BranchArrivalCoordinates p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The tagged arrival-coordinate projection of the numerical observation.
It keeps every time and branch tag and forgets only the recorded-arm marker
inside each projected arrival cell. -/
def branchArrivalProjection (b : ℕ) (source : SourceInput p) :
    List (BranchArrivalEntry rate) :=
  (branchCalendar rate rewards C_star C_h b source).map fun entry =>
    (entry.1, entry.2.2.map
      (Sum.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))

private def branchArrivalProjectionEntry (entry : NumericalEntry rate) :
    BranchArrivalEntry rate :=
  (entry.1, entry.2.2.map
    (Sum.map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))

private theorem measurable_branchArrivalProjectionEntry :
    Measurable (branchArrivalProjectionEntry rate) := by
  let phi := ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
  have hphi := ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical
    rate
  have hsum : Measurable (Sum.map phi phi) := by
    apply Measurable.sumElim
    · exact measurable_inl.comp hphi
    · exact measurable_inr.comp hphi
  have hoption : Measurable (fun cell : Option (NumericalCoordinates p ⊕
      NumericalCoordinates p) => cell.map (Sum.map phi phi)) :=
    ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun q : (NumericalCoordinates p ⊕ NumericalCoordinates p) ×
        Option (NumericalCoordinates p ⊕ NumericalCoordinates p) => Sum.map phi phi q.1)
      (hsum.comp measurable_fst) (fun cell => cell) measurable_id
  have hcell : Measurable (fun entry : NumericalEntry rate => entry.2.2) :=
    measurable_snd.comp measurable_snd
  exact measurable_fst.prodMk (hoption.comp hcell)

/-- The derived arrival-coordinate projection is Borel, using the admitted
full-vector division-and-floor map on each unchanged optional branch cell. -/
theorem measurable_branchArrivalProjection :
    Measurable (fun z : ℕ × SourceInput p =>
      branchArrivalProjection rate rewards C_star C_h z.1 z.2) := by
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (fun z : ℕ × SourceInput p => branchCalendar rate rewards C_star C_h z.1 z.2)
    (measurable_branchCalendar rate rewards C_star C_h)
    (branchArrivalProjectionEntry rate)
    (measurable_branchArrivalProjectionEntry rate)

/-- Without a corrected launch, the actual complete suffix and tagged
observation are empty. -/
theorem empty_no_launch (b : ℕ) (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    branchCalendar rate rewards C_star C_h b source = [] := by
  have hempty :=
    (ReferenceCompletePhysicalHistory.no_launch_complete_history
      rate source rewards C_star C_h hlaunch).2.1
  simp [branchCalendar, hempty]

/-- A launch at the terminal boundary has no actual suffix dates. -/
theorem empty_terminal (b : ℕ) (source : SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    branchCalendar rate rewards C_star C_h b source = [] := by
  have hempty :=
    (ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
      rate source rewards C_star C_h active hlaunch hstart).1
  simp [branchCalendar, hempty]

end Bandits.Support.ReferenceCompleteNumericalBranchObservation

end
