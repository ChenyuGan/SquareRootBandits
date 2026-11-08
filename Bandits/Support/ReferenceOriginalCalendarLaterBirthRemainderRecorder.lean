/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInstallationCollectionPrefixNumericalTruth

import Mathlib.Tactic

/-!
# Actual later-birth recording with a fixed whole assignment vector

The source remains the original calendar source. Fixing the whole assignment
vector leaves every original remainder coordinate in the recording map.

Sources: ZIP4 `04_slow_fast_learner.tex:157-188,218-288`,
`06_interruptions.tex:355-426`, and `appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarLaterBirthRemainderRecorder

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput)
open ContinuousLearningRows (TimeControl)
open AssignmentParameterFibreKernel (AssignmentVector)
open ReferenceLaterOptionalControlResampling (ControlRemainder)

variable {p : Parameters}

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

private theorem viewRecordingMap_time_irrel (t₁ t₂ : Fin p.T)
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (valid₁ : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t₁
      view.complementWeights)
    (valid₂ : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t₂
      view.complementWeights)
    (v : AssignmentVector p) (w : ControlRemainder p) :
    ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t₁ view valid₁ v w =
      ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t₂ view valid₂ v w := by
  unfold ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap
  congr 1

private theorem record_of_calendarParameters
    (t : Fin p.T) (source : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameter : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t source = some theta) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
        some r ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta := by
  unfold ReferenceCalendarLaterSamplerPredictability.calendarParameters at hparameter
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source with
  | none => simp only [hr, Option.bind_none] at hparameter; cases hparameter
  | some r =>
      simp only [hr, Option.bind_some] at hparameter
      exact ⟨r, rfl, hparameter⟩

/-- The original actual calendar parameter is unchanged under a current-source
replacement at every value of the original remainder coordinates. -/
theorem calendarParameters_currentSource (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (v : AssignmentVector p) (w : ControlRemainder p) :
    ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) =
      ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t z := by
  calc
    ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) =
      ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)) :=
        ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
          rate rewards C_star C_h control0 t _
    _ = ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
          rw [ReferenceFirstCollectionCurrentRemainderLaw.currentSource_prefix]
    _ = ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t z :=
        (ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
          rate rewards C_star C_h control0 t z).symm

/-- With an actual present sampler parameter, fixing all K+1 assignment
coordinates fixes the full checked output, every dispatch diagnostic, the
chosen flag, and the selected view/start for every remainder vector. -/
theorem currentRemainder_laterParameters_factor (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameter : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z = some theta)
    (v : AssignmentVector p) (w : ControlRemainder p) :
    let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
    ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) = some theta ∧
      ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) =
        ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) ∧
      ReferenceFirstCollectionCurrentRemainderLaw.currentParameters rate rewards C_star C_h
          control0 t z v w =
        ReferenceFirstCollectionCurrentRemainderLaw.currentParameters rate rewards C_star C_h
          control0 t z v w0 ∧
      ReferenceFirstCollectionCurrentRemainderLaw.currentChosen rate rewards C_star C_h
          control0 t z v w =
        ReferenceFirstCollectionCurrentRemainderLaw.currentChosen rate rewards C_star C_h
          control0 t z v w0 ∧
      ReferenceFirstCollectionCurrentRemainderLaw.currentDispatchTag rate rewards C_star C_h
          control0 t z v w =
        ReferenceFirstCollectionCurrentRemainderLaw.currentDispatchTag rate rewards C_star C_h
          control0 t z v w0 := by
  let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  have hparamW := calendarParameters_currentSource rate rewards C_star C_h control0 t z v w
  have hparam0 := calendarParameters_currentSource rate rewards C_star C_h control0 t z v w0
  rw [hparameter] at hparamW hparam0
  obtain ⟨a, ha, hpa⟩ := record_of_calendarParameters rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) theta hparamW
  obtain ⟨b, hb, hpb⟩ := record_of_calendarParameters rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) theta hparam0
  have hin := (ReferenceFirstCollectionCurrentRemainderLaw.currentSource_incoming
    rate rewards C_star C_h control0 t z v w).trans
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource_incoming
      rate rewards C_star C_h control0 t z v w0).symm
  simp only [ReferenceSourcePrefixHistoryFiltration.incoming, ha, hb,
    Option.map_some, Option.some.injEq] at hin
  have hstate : a.input.state = b.input.state := by
    simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using
      congrArg ReferenceActivePhysicalStepMeasurability.decodeState hin
  obtain ⟨harows, haj, _⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) a ha
  obtain ⟨hbrows, hbj, _⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) b hb
  have htime : a.input.time = b.input.time := by
    exact (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) a ha).2.2.1.trans
        (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
          rate rewards C_star C_h t
            (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) b hb).2.2.1.symm
  have hva : LaterAssignmentStartOperation.ownAssignmentVector a.input.row a.input.time = v := by
    change ContinuousControlSlice.assignmentVector
      ((a.input.rows a.input.selected).2 a.input.time).1 = v
    rw [harows, haj, (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) a ha).2.2.1]
    exact ReferenceFirstCollectionCurrentRemainderLaw.currentSource_assignmentVector
      control0 t z v w
  have hvb : LaterAssignmentStartOperation.ownAssignmentVector b.input.row b.input.time = v := by
    change ContinuousControlSlice.assignmentVector
      ((b.input.rows b.input.selected).2 b.input.time).1 = v
    rw [hbrows, hbj, (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) b hb).2.2.1]
    exact ReferenceFirstCollectionCurrentRemainderLaw.currentSource_assignmentVector
      control0 t z v w0
  have hdiag := ReferenceCalendarLaterSamplerOutputSections.canonicalDiagnostics_eq_of_reads
    a.input b.input hstate htime (hva.trans hvb.symm)
  have hout : ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) =
    ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) := by
    unfold ReferenceCalendarLaterSamplerOutputSections.outputAt
    rw [ha, hb]
    simp only [Option.bind_some, ReferenceCalendarLaterSamplerOutputSections.outputOnInput]
    rw [hdiag]
  obtain ⟨htag, hchosen, hselection⟩ :=
    ReferenceFirstCollectionCurrentRemainderLaw.roundDispatch_factor rate a.input b.input
      hstate htime theta hpa (hva.trans hvb.symm)
  have hbase : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0) = some b := hb
  have hparams : ReferenceFirstCollectionCurrentRemainderLaw.currentParameters rate rewards
      C_star C_h control0 t z v w =
    ReferenceFirstCollectionCurrentRemainderLaw.currentParameters rate rewards C_star C_h
      control0 t z v w0 := by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentParameters, ha, hbase,
      Option.bind_some]
    rw [ReferenceLaterLiveReadoutDomain.roundRecordSelection_eq_dispatch,
      ReferenceLaterLiveReadoutDomain.roundRecordSelection_eq_dispatch]
    exact hselection
  have hchosen' : ReferenceFirstCollectionCurrentRemainderLaw.currentChosen rate rewards
      C_star C_h control0 t z v w =
    ReferenceFirstCollectionCurrentRemainderLaw.currentChosen rate rewards C_star C_h
      control0 t z v w0 := by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentChosen, ha, hbase,
      Option.map_some]
    exact congrArg some hchosen
  have htag' : ReferenceFirstCollectionCurrentRemainderLaw.currentDispatchTag rate rewards
      C_star C_h control0 t z v w =
    ReferenceFirstCollectionCurrentRemainderLaw.currentDispatchTag rate rewards C_star C_h
      control0 t z v w0 := by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentDispatchTag, ha, hbase,
      Option.map_some]
    exact congrArg some htag
  dsimp only [w0]
  exact ⟨hparamW, hout, hparams, hchosen', htag'⟩

private theorem actualRecord_index
    (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
      some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k = r := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hstart
  · obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hr
    let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length :=
      ⟨t.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h,
        by simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk⟩
    exact ⟨k, hget⟩

/-- An actual later selection has its canonical birth row, including the
ordinary PREPARE state, empty pending reset, full physical mark, original
reward table, and payload rates, for every fixed-vector remainder. -/
theorem currentRemainder_laterBirth_marker_on_present (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (theta : AssignmentParameterFibreKernel.Theta p)
    (hparameter : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z = some theta)
    (v : AssignmentVector p) (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hphi : ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
      rate rewards C_star C_h control0 t z v
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2 =
        some (view, started)) :
    ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
        view.complementWeights,
      ∀ w : ControlRemainder p,
        ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
            rate rewards C_star C_h control0 t z v w =
          some (ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap
            rate t view valid v w) ∧
        ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (c : RecordedQueueRun.RoundInput p.K)
          (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
              (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) =
            some r ∧
          ReferenceLaterLiveNumericalReadout.laterLiveReadout
              (ReferenceCompletePhysicalHistory.physicalStart rate
                (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
                rewards C_star C_h) r = some c ∧
          (∀ i, (ReferenceLaterLiveNumericalReadout.preparedStates r ho i).status =
            .unoccupied ∧
            (r.output.preparation.followers.followers i).configuration = .ordinary
              (ReferenceLaterLiveNumericalReadout.preparedStates r ho i)
              (ReferenceLaterLiveNumericalReadout.preparedMemories r ho i)) ∧
          view.pendingAtChoice = Finset.univ ∧
          c.enabled = true ∧ c.rate = view.payload.rate ∧
          c.reward = (fun arm => ((rewards t arm).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧
          c.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
            r view.payload true ∧
          ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r view.payload true =
            ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t view valid v w ∧
          r.input.rows =
            (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w).1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p
            (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) ∧
          r.input.rewards = rewards := by
  let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  have hparameter0 := calendarParameters_currentSource rate rewards C_star C_h
    control0 t z v w0
  rw [hparameter] at hparameter0
  obtain ⟨r0, hr0, hparameterR0⟩ := record_of_calendarParameters rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0)
    theta hparameter0
  have hphi0 := hphi
  change ReferenceFirstCollectionCurrentRemainderLaw.currentParameters rate rewards C_star C_h
      control0 t z v w0 = some (view, started) at hphi0
  have hselected0 : r0.output.preparation.coordinator.selection.map
      (fun s => (s.view, s.started)) = some (view, started) := by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentParameters, hr0,
      Option.bind_some] at hphi0
    exact hphi0
  obtain ⟨selected0, _hselection0, hpair0⟩ := Option.map_eq_some_iff.mp hselected0
  have hview0 : selected0.view = view := congrArg Prod.fst hpair0
  have htime0 := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w0)
    r0 hr0).2.2.1
  have valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
      view.complementWeights := by
    cases hview0
    simpa only [htime0] using
      ReferenceLaterLiveNumericalReadout.selection_choiceValid selected0
  refine ⟨valid, ?_⟩
  intro w
  have hfactor := currentRemainder_laterParameters_factor rate rewards C_star C_h
    control0 t z theta hparameter v w
  dsimp only [w0] at hfactor
  have hparameterW := hfactor.1
  obtain ⟨r', hr', hparameterR'⟩ := record_of_calendarParameters rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
    theta hparameterW
  have hcurrent : ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
      rate rewards C_star C_h control0 t z v w = some (view, started) :=
    hfactor.2.2.1.trans hphi
  have hselected : r'.output.preparation.coordinator.selection.map
      (fun s => (s.view, s.started)) = some (view, started) := by
    simpa only [ReferenceFirstCollectionCurrentRemainderLaw.currentParameters, hr',
      Option.bind_some] using hcurrent
  obtain ⟨selected, hselection, hpair⟩ := Option.map_eq_some_iff.mp hselected
  have hview : selected.view = view := congrArg Prod.fst hpair
  have hstarted : selected.started = started := congrArg Prod.snd hpair
  have hprep : r'.output.preparation = ReferenceActivePhysicalStep.prepare r'.input := by
    rw [r'.output_eq]
    rfl
  have hchosen := ReferenceFirstCollectionCurrentRemainderLaw.selected_laterChosen
    rate r'.input theta hparameterR' selected (by rw [← hprep]; exact hselection)
  have htRecord := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
    r' hr').2.2.1
  obtain ⟨old, ledger, saved, hstate, hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty r'.input hchosen
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
      rewards C_star C_h
  obtain ⟨k, hindex⟩ := actualRecord_index rate rewards C_star C_h t
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) r' hr'
  cases hindex
  have hstateIndex :
      (R.get k).input.state.coordinator =
        .collection old ledger saved := by
    exact hstate
  have hstateIndex' :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
        rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection old ledger saved := by
    simpa only [List.get_eq_getElem] using hstateIndex
  have hE := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h
    (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) k
  dsimp only at hE
  rw [hstateIndex'] at hE
  rcases hE hempty with ⟨u, hu, core, startedActual, hstart, instruction,
    hassignment, htime, hkind, consistent, output, hlocal, hoperation, clockData,
    installation, selectedBirth, hinstall, hresult, hdispatch, hprepared,
    hpayload, hvector, hownVector, hbase, hqueues, hanchor, selectedBirthArm,
    hselectionBirth, hvpayload, hvcutoff, hlive, hstrict, c, ho, cell, hread,
    hcell, hcellSelected, hcellStates, hcellMemories, hunoccupied, henabled,
    hrate, hreward, hmarker, hrows, hselectedRow, hrewards, hquantized,
    hcontribution, hrawArrival, howners, recording, serviced, pending, finished,
    hrecording, hrecorded, hservicedRecording, hraw, hservice, hconfirmation,
    hfinish, hpost, hcoordinator, hnext, hbank⟩
  let birthRecord := R.get k
  have hselectionEq : selectedBirthArm = selected :=
    Option.some.inj (hselectionBirth.symm.trans hselection)
  have hcellSelectedCurrent : cell.selected = selected := hcellSelected.trans hselectionEq
  have hselectedPayload : selected.view.payload = installation.registers.payload := by
    calc
      selected.view.payload = selectedBirthArm.view.payload := congrArg
        (fun s : ReferenceActivePhysicalStep.Selection (R.get k).input => s.view.payload)
          hselectionEq.symm
      _ = installation.registers.payload := hvpayload
  have hstrictSelected : ReferenceCompletePhysicalHistory.physicalStart rate
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
      rewards C_star C_h < selected.view.payload.sigma.val := by
    rw [hselectedPayload]
    exact hstrict
  have hprepared' : birthRecord.output.preparation.coordinator =
      .collection old ledger (ReferenceActivePhysicalStep.collectionClock old ledger saved u) u
        (.laterChosen core consistent startedActual hstart instruction hassignment output hlocal
          clockData installation selectedBirth) := by
    simpa only [birthRecord, R, List.get_eq_getElem] using hprepared
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames birthRecord
  rw [hprepared'] at hframes
  dsimp only at hframes
  have hselectedAt : birthRecord.output.preparation.coordinator.selection =
      some (ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm birthRecord.input
        installation.registers.payload startedActual instruction.time
        installation.registers.complementWeights selectedBirth hframes.1) := by
    rw [hprepared']
    exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq birthRecord.input
      installation.registers.payload startedActual instruction.time
      installation.registers.complementWeights selectedBirth hframes.1
  have hselectedBirthEq : selectedBirthArm =
      ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm (R.get k).input
        installation.registers.payload startedActual instruction.time
        installation.registers.complementWeights selectedBirth hframes.1 :=
    Option.some.inj (hselectionBirth.symm.trans hselectedAt)
  have hstartedActual : selected.started = startedActual := by
    rw [← hselectionEq, hselectedBirthEq]
    rfl
  subst selectedBirthArm
  rw [hcellSelectedCurrent] at hlive
  let birthClock := ReferenceActivePhysicalStep.collectionClock old ledger saved u
  have hstartAtInstruction : CoordinatorPhaseClock.startRound p rate.eta.val instruction.time
      birthClock ledger.pending = .ok startedActual := by
    rw [htime]
    simpa only [birthClock, ReferenceActivePhysicalStep.collectionInput] using hstart
  have hparamValid : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
    simpa only [ReferenceActivePhysicalStep.collectionInput] using core.clock_parameter_valid
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val birthClock := by
    simpa only [birthClock, ReferenceActivePhysicalStep.collectionInput] using
      core.clock_registers_valid
  have htimeValid : CoordinatorPhaseClock.startRoundTimeValid p instruction.time birthClock := by
    rw [htime]
    simpa only [birthClock, ReferenceActivePhysicalStep.collectionInput] using
      core.clock_start_time_valid
  have hstartEffects := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
    instruction.time birthClock ledger.pending startedActual instruction hparamValid
    hclockValid htimeValid hstartAtInstruction hassignment
  have hpendingSelected : selected.view.pendingAtChoice = Finset.univ := by
    exact Eq.trans selected.pending_eq
      (Eq.trans (congrArg (fun q : CoordinatorPhaseClock.StartRoundResult p => q.pending)
        hstartedActual) hstartEffects.2.2.2.2.2.2.1)
  have hpending : view.pendingAtChoice = Finset.univ := by
    calc
      view.pendingAtChoice = selected.view.pendingAtChoice := congrArg
        (fun q : ReferenceDownReception.ChoiceTimeView p rate.eta => q.pendingAtChoice) hview.symm
      _ = Finset.univ := hpendingSelected
  have ht : (R.get k).input.time = t := by
    simpa only [List.get_eq_getElem] using htRecord
  have hcellStates' : cell.states =
      ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho := by
    simpa only [birthRecord, R, List.get_eq_getElem] using hcellStates
  have hstatus : (fun i => (ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho i).status) =
      fun _ => ActiveRoundActions.FollowerStatus.unoccupied := funext (fun i => by
        simpa only [congrFun hcellStates' i] using hunoccupied i)
  have hsnapshot :
      (ActiveRoundActions.Snapshot.mk selected.view.pendingAtChoice
        (fun i => (ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho i).status) :
        ActiveRoundActions.Snapshot selected.view.payload.assignment) =
      ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot selected.view.payload.assignment :=
    congrArg₂ (fun missing status =>
      (ActiveRoundActions.Snapshot.mk missing status :
        ActiveRoundActions.Snapshot selected.view.payload.assignment)) hpendingSelected hstatus
  have hrow : ((R.get k).input.row.2 (R.get k).input.time).1 =
      (ReferenceFirstCollectionCurrentRemainderLaw.currentControl v w).1 := by
    rw [ht]
    change (((R.get k).input.rows (R.get k).input.selected).2 t).1 = _
    have hrows' : (R.get k).input.rows =
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w).1.2 := by
      simpa only [birthRecord, R, List.get_eq_getElem] using hrows
    have hselectedRow' : (R.get k).input.selected =
        ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) := by
      simpa only [birthRecord, R, List.get_eq_getElem] using hselectedRow
    rw [hrows', hselectedRow']
    simp [ReferenceFirstCollectionCurrentRemainderLaw.currentSource,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix, ActualInitializationPhysicalStep.selectedRowIndex]
  have hsourceRead : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
        rewards C_star C_h) (R.get k) =
      some (ReferenceFirstWindowNumericalStream.sourceCell (R.get k) selected.view.payload
        selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho)
        selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) := by
    let ri := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
      rewards C_star C_h)[k.val]'k.isLt
    have hselectionIndex : ri.output.preparation.coordinator.selection = some selected := by
      simpa only [ri, birthRecord, R, List.get_eq_getElem] using hselection
    have hliveIndex : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff ri.input.time := by
      simpa only [ri, birthRecord, R, List.get_eq_getElem] using hlive
    have hoIndex : ReferenceLaterLiveNumericalReadout.preparedOrdinary ri := by
      simpa only [ri, birthRecord, R, List.get_eq_getElem] using ho
    have hindexRead : ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
          rewards C_star C_h) ri =
        some (ReferenceFirstWindowNumericalStream.sourceCell ri selected.view.payload
          selected.view.pendingAtChoice
          (ReferenceLaterLiveNumericalReadout.preparedStates ri hoIndex)
          selected.view.complementWeights selected.view.cutoff
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)) := by
      simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hselectionIndex,
        ite_eq_left (And.intro hstrictSelected hliveIndex), dite_eq_left hoIndex]
    simpa only [ri, birthRecord, R, List.get_eq_getElem] using hindexRead
  have hcellEq := Option.some.inj (hread.symm.trans hsourceRead)
  have hsourceMark :
      (ReferenceFirstWindowNumericalStream.sourceCell (R.get k) selected.view.payload
        selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho)
        selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)).recordedArm =
      ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t view valid v w := by
    cases hview
    have validRecord : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
        selected.view.cutoff (R.get k).input.time selected.view.complementWeights := by
      simpa only [← ht] using valid
    calc
      (ReferenceFirstWindowNumericalStream.sourceCell (R.get k) selected.view.payload
        selected.view.pendingAtChoice
        (ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho)
        selected.view.complementWeights selected.view.cutoff
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)).recordedArm =
          ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate
            (R.get k).input.time selected.view validRecord v w := by
        dsimp only [ReferenceFirstWindowNumericalStream.sourceCell,
          ReferenceFirstWindowNumericalStream.sourceArm,
          ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap]
        rw [hsnapshot, hrow]
      _ = ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t selected.view valid v w :=
        (viewRecordingMap_time_irrel rate (R.get k).input.time t selected.view validRecord valid v w).symm
  have hmark : c.recordedArm =
      ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t view valid v w :=
    congrArg (fun q : RecordedQueueRun.RoundInput p.K => q.recordedArm) hcellEq |>.trans hsourceMark
  have hmarkerView : ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
      (R.get k) view.payload true =
      ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t view valid v w := by
    simpa only [birthRecord, R, List.get_eq_getElem, hcellSelectedCurrent, hview] using
      hmarker.symm.trans hmark
  have hunoccupied' (i : Fin (p.m - 1)) :
      (ReferenceLaterLiveNumericalReadout.preparedStates (R.get k) ho i).status =
        ActiveRoundActions.FollowerStatus.unoccupied := by
    simpa only [congrFun hcellStates' i] using hunoccupied i
  have hrate' : c.rate = view.payload.rate := by
    calc
      c.rate = installation.registers.payload.rate := hrate
      _ = selected.view.payload.rate := by rw [hselectedPayload]
      _ = view.payload.rate := by rw [hview]
  have hreward' : c.reward = fun arm => ((rewards t arm).val : ℝ) /
      (ConstructorDimensions.D p : ℝ) := by
    have hrewardIndex : c.reward = fun arm =>
        ((rewards (((ReferenceCompletePhysicalHistory.completeSuffixRecords rate
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
          rewards C_star C_h)[k.val]'k.isLt).input.time) arm).val : ℝ) /
          (ConstructorDimensions.D p : ℝ) := by
      simpa only [birthRecord, R, List.get_eq_getElem] using hreward
    have htIndex : ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
        rewards C_star C_h)[k.val]'k.isLt).input.time = t := by
      simpa only [R, List.get_eq_getElem] using ht
    rw [htIndex] at hrewardIndex
    exact hrewardIndex
  have hphysical : c.recordedArm =
      ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord (R.get k) view.payload true := by
    simpa only [birthRecord, R, List.get_eq_getElem, hcellSelectedCurrent, hview] using hmarker
  have hreadIndex : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
        rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
        rewards C_star C_h)[k.val]'k.isLt) = some c := by
    simpa only [R, List.get_eq_getElem] using hread
  have hcurrentMarker :
      ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
          rate rewards C_star C_h control0 t z v w = some c.recordedArm := by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentMarker, hr',
      Option.bind_some]
    change Option.map (fun x : RecordedQueueRun.RoundInput p.K => x.recordedArm)
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
          rewards C_star C_h)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate
          (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
          rewards C_star C_h)[k.val]'k.isLt)) = some c.recordedArm
    rw [hreadIndex]
    rfl
  refine ⟨hcurrentMarker.trans (congrArg some hmark), R.get k, c, ho, hr', hread, ?_,
    hpending, henabled, hrate', hreward', hphysical, hmarkerView, hrows, hselectedRow, hrewards⟩
  · intro i
    exact ⟨hunoccupied' i, ReferenceLaterLiveNumericalReadout.prepared_configuration
      (R.get k) ho i⟩

/-- Measurability of the actual arbitrary-calendar marker on the present
calendar-parameter branch. -/
theorem currentRemainder_laterMarker_measurable (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (v : AssignmentVector p) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p,
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z = some theta →
      Measurable (fun w : ControlRemainder p =>
        ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
          rate rewards C_star C_h control0 t z v w) := by
  intro theta hparameter
  let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  cases hp : ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
      rate rewards C_star C_h control0 t z v w0 with
  | none =>
      have heq : ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
          rate rewards C_star C_h control0 t z v = fun _ => none := by
        funext w
        have hfactor := currentRemainder_laterParameters_factor rate rewards C_star C_h
          control0 t z theta hparameter v w
        dsimp only [w0] at hfactor
        exact ReferenceFirstCollectionCurrentRemainderLaw.currentMarker_none_of_parameters_none
          rate rewards C_star C_h control0 t z v w (hfactor.2.2.1.trans hp)
      rw [heq]
      exact measurable_const
  | some q =>
      obtain ⟨valid, hpoint⟩ := currentRemainder_laterBirth_marker_on_present
        rate rewards C_star C_h control0 t z theta hparameter v q.1 q.2 hp
      have heq : ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
          rate rewards C_star C_h control0 t z v =
          fun w => some (ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap
            rate t q.1 valid v w) := funext (fun w => (hpoint w).1)
      rw [heq]
      exact (measurable_of_countable
        (some : Option (Fin p.K) → Option (Option (Fin p.K)))).comp
          (ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap_measurable
            rate t q.1 valid v)

/-- The arbitrary-calendar optional marker law on the actual present
sampler-parameter branch. -/
theorem currentRemainder_laterBirth_optionalMarker_law (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (v : AssignmentVector p) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p,
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z = some theta →
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
          (ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
            rate rewards C_star C_h control0 t z v) =
        match ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
            rate rewards C_star C_h control0 t z v
            (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2 with
        | none => Measure.dirac none
        | some (view, _started) =>
            ((RecordedRoundMoments.recordingOutcomePMF
              (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
                rate.sourceCap view.payload.anchor view.payload.anchor_pos)).toMeasure).map some := by
  intro theta hparameter
  let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  cases hp : ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
      rate rewards C_star C_h control0 t z v w0 with
  | none =>
      have heq : ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
          rate rewards C_star C_h control0 t z v = fun _ => none := by
        funext w
        have hfactor := currentRemainder_laterParameters_factor rate rewards C_star C_h
          control0 t z theta hparameter v w
        dsimp only [w0] at hfactor
        exact ReferenceFirstCollectionCurrentRemainderLaw.currentMarker_none_of_parameters_none
          rate rewards C_star C_h control0 t z v w (hfactor.2.2.1.trans hp)
      rw [heq]
      simp
  | some q =>
      obtain ⟨valid, hpoint⟩ := currentRemainder_laterBirth_marker_on_present
        rate rewards C_star C_h control0 t z theta hparameter v q.1 q.2 hp
      have heq : ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
          rate rewards C_star C_h control0 t z v =
          some ∘ ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap
            rate t q.1 valid v := funext (fun w => (hpoint w).1)
      have hsome : Measurable (some : Option (Fin p.K) → Option (Option (Fin p.K))) :=
        measurable_of_countable _
      rw [heq, ← Measure.map_map hsome
        (ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap_measurable
          rate t q.1 valid v)]
      change ((ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t q.1 valid v)).map
          some = _
      congr 1
      exact ReferenceFirstCollectionCurrentRemainderLaw.map_recordingMap_currentRemainder
        rate (.live q.1.payload.assignment
          (ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot q.1.payload.assignment))
        q.1.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights q.1.payload q.1.complementWeights)
        q.1.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower _ _ _ _ valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper _ _ _ _ valid) v

end Bandits.Support.ReferenceOriginalCalendarLaterBirthRemainderRecorder
