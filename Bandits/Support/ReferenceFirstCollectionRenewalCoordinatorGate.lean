/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalInstalledServiceTail

/-!
# Actual first-renewal coordinator recording gate

On the original first-renewal pair law, this projects the successful literal
coordinator recording operation from the installed service tail. The arm gate
is expressed on the actual continuous row slice and the original auxiliary
slow set. Its arrival remains the floor of the actual typed observation.

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-215`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

namespace Bandits.Support.ReferenceFirstCollectionRenewalCoordinatorGate

open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.ConstructorDimensions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
open Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling

abbrev Parameters := ConstructorDimensions.Parameters

/-- The successful coordinator recorder in the actual later assignment
installation has the literal pilot gate on the original renewal slow set.
Only the exact public installation/service tail is used; the actual typed
observation and recording output are retained. -/
theorem ae_pairLaw_actual_coordinator_gate
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ b : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalBase
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalInstallationCoupling.Source
        rate rewards C_star C_h u t ∂
        ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t,
    let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
      rate rewards C_star C_h u t b.1.1 b.1.2
    ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
        rate rewards C_star C_h u t b.2,
      ∃ recording : CoordinatorRecordingOperation.Output p,
        d.record.output.coordinator.recording = some recording ∧
        ∀ j : Fin p.K,
          recording.gateArm = some j ↔
            j ∉ U.val ∧
              CanonicalRecordingSlice.pilotRecordingGate
                p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
                (ActiveRoundActions.coordinator p.two_le_m) j
                (CanonicalRecordingRates.xi p rate.eta.val
                  (AssignmentScoreReconstruction.currentWeight d.out) j /
                  CanonicalRecordingSlice.pilotRecordingGateRawProbability
                    (K := p.K) (ActiveRoundActions.coordinator p.two_le_m))
                (ContinuousLearningRows.sliceAt d.record.input.time
                  d.record.input.row.2) := by
  classical
  filter_upwards
    [ReferenceFirstCollectionRenewalInstalledServiceTail.ae_pairLaw_actual_service_tail
      rate rewards C_star C_h u t] with b hb
  dsimp only at hb
  rcases hb with ⟨d, consistent, output, hlocal, hstart, hv, hreconstruction,
    hsample, hslow, hpayloadSlow, htail⟩
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
      output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [x,
        ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
        d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [x,
        ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using
        d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  rcases htail with ⟨hinstalledPayload, hinstalledVector, hinstalledReconstruction,
    hanchor, hqueues, hbase, hinstalledSlow, selection, hselection, hdispatch,
    hpreparation, hpreparationCoordinator, hselectedArm, hpostChoice, hnextChoice,
    recording, serviced, pending, finished, hrecord, hservice, hconfirmation,
    hfinish, hcoordinator, hfailure, hrecordingField, hupField, hconfiguration,
    hnextConfiguration, hserviceBudget, htotalHorizon⟩
  let r := installed.registers
  let P := ReferenceActivePhysicalStep.prepare d.record.input
  let input := ReferenceActivePhysicalStep.liveRecordingInput P r d.started
  let zeroObservation : Fin (D p + 1) := ⟨0, by omega⟩
  let inputZero : CoordinatorRecorderComplementBridge.Input r.payload :=
    { input with observation := zeroObservation }
  have hlaterFrame :=
    CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
      output clockData
  rcases hlaterFrame with ⟨_, hsigma, hu, hgrid, _, hpending, _, _, _⟩
  have hsigma' : d.started.clock.sigma = some d.instruction.time := by
    change clockData.result.clock.sigma = some d.instruction.time
    exact hsigma
  have hgridDomain :
      d.instruction.time.val + 1 < d.started.clock.g ∧
        d.started.clock.g ≤ p.T + 1 := by
    have hgd := d.started.gridDomain
    simp only [CoordinatorPhaseClock.clockGridDomain, hsigma'] at hgd
    exact hgd
  have hsourceScore : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j = AssignmentScoreReconstruction.sourceScore d.out j.1 := by
    intro j
    change (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementScores j = _
    rw [CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score
      output clockData j, hreconstruction]
  have hweight : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementWeights j = r.payload.anchor j.1 := by
    intro j
    change ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (r.complementScores j) = r.payload.anchor j.1
    rw [hsourceScore j]
    exact (congrArg (fun weights : Fin p.K → ℝ => weights j.1) hanchor).symm
  have hlocalInputs : CoordinatorRecorderComplementBridge.LocalInputsValid input := by
    constructor
    · change d.started.clock.g ≤ p.T + 1
      exact hgridDomain.2
    · intro j
      change r.payload.anchor j.1 ≤ r.complementWeights j ∧
        r.complementWeights j ≤ 2 * r.payload.anchor j.1
      rw [hweight j]
      exact ⟨le_rfl, by linarith [r.payload.anchor_pos j.1]⟩
  have hlocalInputsZero :
      CoordinatorRecorderComplementBridge.LocalInputsValid inputZero := by
    constructor
    · exact hlocalInputs.1
    · intro j
      exact hlocalInputs.2 j
  have hvalid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    input hlocalInputs
  have hvalidZero := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    inputZero hlocalInputsZero
  have hslowEq : r.payload.slowSet =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u t b.1.1 b.1.2 := by
    exact hinstalledSlow
  have hmode : input.mode = .live false := by
    change CoordinatorRecorderComplementBridge.LocalMode.live
      (decide (d.started.pending = ∅)) =
        CoordinatorRecorderComplementBridge.LocalMode.live false
    have hpendingNe : d.started.pending ≠ (∅ : Finset (Fin (p.m - 1))) := by
      have hmminus : 0 < p.m - 1 := by
        have hm := p.two_le_m
        omega
      have hne : (Finset.univ : Finset (Fin (p.m - 1))) ≠ ∅ := by
        intro he
        have hmem : (⟨0, hmminus⟩ : Fin (p.m - 1)) ∈
            (Finset.univ : Finset (Fin (p.m - 1))) := Finset.mem_univ _
        rw [he] at hmem
        simp at hmem
      intro hempty
      have hfull : d.started.pending = Finset.univ := by
        change clockData.result.pending = Finset.univ
        exact hpending
      rw [hfull] at hempty
      exact hne hempty
    simp [hpendingNe]
  have hmodeZero : inputZero.mode = .live false := by
    change input.mode = CoordinatorRecorderComplementBridge.LocalMode.live false
    exact hmode
  have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen input := by
    intro hfrozen
    have hfrozen' : CoordinatorRecordingOperation.isFrozen
        (CoordinatorRecorderComplementBridge.recorderInput input) := by
      simpa [CoordinatorRecorderComplementBridge.isFrozen] using hfrozen
    have hround : CoordinatorRecordingOperation.sourceCalendarRound
        (CoordinatorRecorderComplementBridge.recorderInput input) <
          (CoordinatorRecorderComplementBridge.recorderInput input).gridBoundary := by
      simpa [CoordinatorRecordingOperation.sourceCalendarRound,
        CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights,
        CoordinatorRecorderComplementBridge.sourceStart,
        ReferenceActivePhysicalStep.liveRecordingInput, input, P,
        d.instruction_time] using hgridDomain.1
    exact (not_le_of_gt hround) hfrozen'.2
  have hnotFrozenZero : ¬ CoordinatorRecorderComplementBridge.isFrozen inputZero := by
    change ¬ CoordinatorRecorderComplementBridge.isFrozen input
    exact hnotFrozen
  let timeControl : ContinuousLearningRows.TimeControl p :=
    d.record.input.row.2 d.instruction.time
  have hsliceEq : timeControl.1 =
      ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2 := by
    simp [timeControl, ContinuousLearningRows.sliceAt, d.instruction_time]
  have hdataSliceOfLocal :
      CoordinatorRecorderComplementBridge.selectedSlot inputZero =
        PublicDiscreteDraws.dataSlot →
      PublicDiscreteDraws.slotDraw timeControl.1 = PublicDiscreteDraws.dataSlot := by
    intro hdata
    have hdataAtSlice : PublicDiscreteDraws.slotDraw
        (ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2) =
          PublicDiscreteDraws.dataSlot := by
      simpa [inputZero, input, ReferenceActivePhysicalStep.liveRecordingInput,
      CoordinatorRecorderComplementBridge.selectedSlot,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecordingOperation.selectedSlot, timeControl,
      d.instruction_time] using hdata
    rw [← hsliceEq] at hdataAtSlice
    exact hdataAtSlice
  have hsourceSliceOfLocal :
      CoordinatorRecorderComplementBridge.selectedRecorder inputZero =
        ActiveRoundActions.coordinator p.two_le_m →
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K timeControl.1 =
        ActiveRoundActions.coordinator p.two_le_m := by
    intro hsource
    have hsourceAtSlice : PublicDiscreteDraws.recorderSourceDraw
        p.two_le_m p.m_lt_K
        (ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2) =
          ActiveRoundActions.coordinator p.two_le_m := by
      have hsourceScalar : CanonicalRecordingSlice.recorderSourceFromScalar
          p.two_le_m
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
            (ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2)) =
            ActiveRoundActions.coordinator p.two_le_m := by
        simpa [inputZero, input, ReferenceActivePhysicalStep.liveRecordingInput,
          CoordinatorRecorderComplementBridge.selectedRecorder,
          CoordinatorRecorderComplementBridge.recorderInput,
          CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          CoordinatorRecordingOperation.selectedRecorder, d.instruction_time]
          using hsource
      rw [CanonicalRecordingSlice.recorderSourceFromScalar_coordinate
        p.two_le_m p.m_lt_K
        (ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2)]
        at hsourceScalar
      exact hsourceScalar
    rw [← hsliceEq] at hsourceAtSlice
    exact hsourceAtSlice
  have hnotFast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
      d.instruction.time ∧ d.started.pending = ∅) := by
    intro h
    have hpendingNe : d.started.pending ≠ (∅ : Finset (Fin (p.m - 1))) := by
      have hmminus : 0 < p.m - 1 := by
        have hm := p.two_le_m
        omega
      have hne : (Finset.univ : Finset (Fin (p.m - 1))) ≠ ∅ := by
        intro he
        have hmem : (⟨0, hmminus⟩ : Fin (p.m - 1)) ∈
            (Finset.univ : Finset (Fin (p.m - 1))) := Finset.mem_univ _
        rw [he] at hmem
        simp at hmem
      intro hempty
      have hfull : d.started.pending = Finset.univ := by
        change clockData.result.pending = Finset.univ
        exact hpending
      rw [hfull] at hempty
      exact hne hempty
    exact hpendingNe h.2
  have hcoreData := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data
    r.payload d.started.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
    d.instruction.time r.complementWeights timeControl selection.choiceInputsValid
    hnotFast
  have hpilotOfData :
      CoordinatorRecorderComplementBridge.selectedSlot inputZero =
        PublicDiscreteDraws.dataSlot →
      input.ownArm = PublicDiscreteDraws.pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) timeControl.1 := by
    intro hdata
    have hcoreData' := hcoreData (hdataSliceOfLocal hdata)
    have hselectionData :
        CoordinatorLocalArmChoice.coordinatorArmChoice r.payload d.started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
          d.instruction.time r.complementWeights d.record.input.row =
            some (PublicDiscreteDraws.pilotDraw (K_pos p)
              (ActiveRoundActions.coordinator p.two_le_m) timeControl.1) := by
      change CoordinatorLocalArmChoice.coordinatorArmChoiceCore r.payload
        d.started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
        d.instruction.time r.complementWeights timeControl =
          some (PublicDiscreteDraws.pilotDraw (K_pos p)
            (ActiveRoundActions.coordinator p.two_le_m) timeControl.1)
      exact hcoreData'
    have hselectionArm : selection.arm =
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) timeControl.1 :=
      Option.some.inj (hselection.symm.trans hselectionData)
    change P.coordinator.arm = _
    calc
      P.coordinator.arm = d.record.output.preparation.coordinator.arm := by
        rw [hpreparation]
      _ = selection.arm := hselectedArm
      _ = _ := hselectionArm
  have hcanonicalRaw :
      CoordinatorRecordingOperation.coordinatorRawGateMass
        (CoordinatorRecorderComplementBridge.recorderInput inputZero) hvalidZero =
        CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K)
          (ActiveRoundActions.coordinator p.two_le_m) := by
    have hprob := CoordinatorRecorderComplementBridge.armProbability_live_confirmations_missing
      inputZero hlocalInputsZero hmodeZero
    calc
      CoordinatorRecordingOperation.coordinatorRawGateMass
          (CoordinatorRecorderComplementBridge.recorderInput inputZero) hvalidZero =
        (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / (p.K : ℝ)) *
          CanonicalRecordingSlice.recordingZeta p.m p.K := by
            simp [CoordinatorRecordingOperation.coordinatorRawGateMass, hprob]
      _ = CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K)
          (ActiveRoundActions.coordinator p.two_le_m) := by
            change (1 / 2 : ℝ) * (1 / 2 : ℝ) * (1 / (p.K : ℝ)) *
              CanonicalRecordingSlice.recordingZeta p.m p.K =
                CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K)
                  (⟨0, by omega⟩ : Fin p.m)
            rw [CanonicalRecordingSlice.pilotRecordingGateRawProbability_coordinator
              p.two_le_m p.m_lt_K]
  have hthresholdAt (j : Fin p.K) (harmj : inputZero.ownArm = j) :
      CoordinatorRecorderComplementBridge.threshold inputZero hlocalInputsZero =
        CanonicalRecordingRates.xi p rate.eta.val
          (AssignmentScoreReconstruction.currentWeight d.out) j /
            CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K)
              (ActiveRoundActions.coordinator p.two_le_m) := by
    have hxi : CanonicalRecordingRates.xi p rate.eta.val
        (AssignmentScoreReconstruction.currentWeight d.out) j =
          CanonicalRecordingRates.xi p rate.eta.val r.payload.anchor inputZero.ownArm := by
      rw [← hanchor, ← harmj]
    unfold CoordinatorRecorderComplementBridge.threshold
      CoordinatorRecordingOperation.coordinatorThreshold
    rw [hcanonicalRaw, hxi]
    rfl
  have hinputZero : CoordinatorRecorderComplementBridge.recorderInput inputZero =
      CoordinatorRecordingOperation.withObservation
        (CoordinatorRecorderComplementBridge.recorderInput input) zeroObservation := by
    rfl
  have hrunActual : CoordinatorRecorderComplementBridge.run input =
      CoordinatorRecordingOperation.run
        (CoordinatorRecorderComplementBridge.recorderInput input) := by
    calc
      CoordinatorRecorderComplementBridge.run input =
          CoordinatorRecordingOperation.executeValid
            (CoordinatorRecorderComplementBridge.recorderInput input) hvalid :=
        CoordinatorRecorderComplementBridge.run_eq_executeValid input hlocalInputs
      _ = CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput input) := by
        simp [CoordinatorRecordingOperation.run, hvalid]
  have hrunZero : CoordinatorRecorderComplementBridge.run inputZero =
      CoordinatorRecordingOperation.run
        (CoordinatorRecorderComplementBridge.recorderInput inputZero) := by
    calc
      CoordinatorRecorderComplementBridge.run inputZero =
          CoordinatorRecordingOperation.executeValid
            (CoordinatorRecorderComplementBridge.recorderInput inputZero) hvalidZero :=
        CoordinatorRecorderComplementBridge.run_eq_executeValid inputZero hlocalInputsZero
      _ = CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput inputZero) := by
        simp [CoordinatorRecordingOperation.run, hvalidZero]
  have hinvariant := CoordinatorRecordingOperation.run_gateArm_eq_of_observation_change
    (CoordinatorRecorderComplementBridge.recorderInput input) hvalid zeroObservation
  have hactualMap :
      (CoordinatorRecordingOperation.run
        (CoordinatorRecorderComplementBridge.recorderInput input)).map
          CoordinatorRecordingOperation.Output.gateArm = some recording.gateArm := by
    rw [← hrunActual, hrecord]
    rfl
  have hzeroMap :
      (CoordinatorRecorderComplementBridge.run inputZero).map
          CoordinatorRecordingOperation.Output.gateArm = some recording.gateArm := by
    calc
      (CoordinatorRecorderComplementBridge.run inputZero).map
          CoordinatorRecordingOperation.Output.gateArm =
        (CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput inputZero)).map
            CoordinatorRecordingOperation.Output.gateArm := by rw [hrunZero]
      _ = (CoordinatorRecordingOperation.run
          (CoordinatorRecordingOperation.withObservation
            (CoordinatorRecorderComplementBridge.recorderInput input) zeroObservation)).map
            CoordinatorRecordingOperation.Output.gateArm := by rw [hinputZero]
      _ = (CoordinatorRecordingOperation.run
          (CoordinatorRecorderComplementBridge.recorderInput input)).map
            CoordinatorRecordingOperation.Output.gateArm := hinvariant.symm
      _ = some recording.gateArm := hactualMap
  have hnoneOfZero :
      (CoordinatorRecorderComplementBridge.run inputZero =
        some (CoordinatorRecordingOperation.zeroOutput p)) →
        recording.gateArm = none := by
    intro hz
    have hmapZero :
        (CoordinatorRecorderComplementBridge.run inputZero).map
          CoordinatorRecordingOperation.Output.gateArm = some none := by
      simp [hz, CoordinatorRecordingOperation.zeroOutput]
    exact Option.some.inj (hzeroMap.symm.trans hmapZero)
  have hrecordGate (j : Fin p.K) :
      recording.gateArm = some j ↔
        (CoordinatorRecorderComplementBridge.run inputZero).map
          CoordinatorRecordingOperation.Output.gateArm = some (some j) := by
    constructor
    · intro hgate
      rw [hzeroMap]
      exact congrArg some hgate
    · intro hgate
      rw [hzeroMap] at hgate
      exact Option.some.inj hgate
  have hslowSet :
      r.payload.slowSet =
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
          rate rewards C_star C_h u t b.1.1 b.1.2 := hslowEq
  refine ⟨d, recording, hrecordingField, ?_⟩
  intro j
  constructor
  · intro hgate
    have hdata : CoordinatorRecorderComplementBridge.selectedSlot inputZero =
        PublicDiscreteDraws.dataSlot := by
      by_contra hbad
      have hz := CoordinatorRecorderComplementBridge.run_zero_of_not_data
        inputZero hlocalInputsZero hbad
      have hnone := hnoneOfZero hz
      have hfalse : (some j : Option (Fin p.K)) = none := hgate.symm.trans hnone
      cases hfalse
    have hsource : CoordinatorRecorderComplementBridge.selectedRecorder inputZero =
        ActiveRoundActions.coordinator p.two_le_m := by
      by_contra hbad
      have hz := CoordinatorRecorderComplementBridge.run_zero_of_other_source
        inputZero hlocalInputsZero hdata hbad
      have hnone := hnoneOfZero hz
      have hfalse : (some j : Option (Fin p.K)) = none := hgate.symm.trans hnone
      cases hfalse
    have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen inputZero := by
      by_contra hbad
      have hz := CoordinatorRecorderComplementBridge.run_zero_of_frozen
        inputZero hlocalInputsZero hdata hsource hbad
      have hnone := hnoneOfZero hz
      have hfalse : (some j : Option (Fin p.K)) = none := hgate.symm.trans hnone
      cases hfalse
    have howns : CoordinatorRecorderComplementBridge.ownsArm inputZero := by
      by_contra hbad
      have hnotOwned :
          ¬ CoordinatorRecordingOperation.ownsArm
            (.live r.payload.assignment false) inputZero.ownArm := by
        simpa [CoordinatorRecorderComplementBridge.ownsArm,
          CoordinatorRecorderComplementBridge.operationMode, hmodeZero] using hbad
      have hslow : inputZero.ownArm ∈ r.payload.slowSet.val := by
        have hmem : inputZero.ownArm ∈
            (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment).val := by
          have hmem' := not_not.mp (by
            simpa [CoordinatorRecordingOperation.ownsArm] using hnotOwned)
          exact hmem'
        simpa [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload]
          using hmem
      have hz := CoordinatorRecorderComplementBridge.run_zero_of_live_slow_arm
        inputZero hlocalInputsZero hdata hsource hnotFrozen false hmodeZero hslow
      have hnone := hnoneOfZero hz
      have hfalse : (some j : Option (Fin p.K)) = none := hgate.symm.trans hnone
      cases hfalse
    have hmask : CoordinatorRecorderComplementBridge.ownMaskPasses inputZero := by
      by_contra hbad
      have hz := CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected
        inputZero hlocalInputsZero hdata hsource hnotFrozen howns hbad
      have hnone := hnoneOfZero hz
      have hfalse : (some j : Option (Fin p.K)) = none := hgate.symm.trans hnone
      cases hfalse
    have hthin : CoordinatorRecorderComplementBridge.thinScalar inputZero ≤
        CoordinatorRecorderComplementBridge.threshold inputZero hlocalInputsZero := by
      by_contra hbad
      have hz := CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected
        inputZero hlocalInputsZero hdata hsource hnotFrozen howns hmask hbad
      have hnone := hnoneOfZero hz
      have hfalse : (some j : Option (Fin p.K)) = none := hgate.symm.trans hnone
      cases hfalse
    have hsuccess := CoordinatorRecorderComplementBridge.run_gate_and_floor
      inputZero hlocalInputsZero hdata hsource hnotFrozen howns hmask hthin
    rcases hsuccess with ⟨out, hout, houtGate, _⟩
    have hrunMap :
        (CoordinatorRecorderComplementBridge.run inputZero).map
          CoordinatorRecordingOperation.Output.gateArm = some (some inputZero.ownArm) := by
      rw [hout]
      change some out.gateArm = some (some inputZero.ownArm)
      exact congrArg some houtGate
    have hinner : some inputZero.ownArm = some j :=
      Option.some.inj (hrunMap.symm.trans ((hrecordGate j).mp hgate))
    have harmj : inputZero.ownArm = j := Option.some.inj hinner
    have harm := hpilotOfData hdata
    have hownAssignment : inputZero.ownArm ∉
        (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment).val := by
      have hownOp : CoordinatorRecordingOperation.ownsArm
          (.live r.payload.assignment false) inputZero.ownArm := by
        simpa [CoordinatorRecorderComplementBridge.ownsArm,
          CoordinatorRecorderComplementBridge.operationMode, hmodeZero] using howns
      simpa [CoordinatorRecordingOperation.ownsArm] using hownOp
    have hownPayload : inputZero.ownArm ∉ r.payload.slowSet.val := by
      simpa [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload]
        using hownAssignment
    have hnotSlow : j ∉
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
          rate rewards C_star C_h u t b.1.1 b.1.2).val := by
      rw [← hslowSet, ← harmj]
      exact hownPayload
    have hpilot :
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) timeControl.1 = j := by
      calc
        _ = input.ownArm := harm.symm
        _ = inputZero.ownArm := by simp [inputZero]
        _ = j := harmj
    have hprepareArm : P.coordinator.arm = j := by
      change input.ownArm = j
      exact harm.trans hpilot
    have hmaskCanonical : CanonicalRecordingSlice.recordingMask
        (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) j timeControl.1 := by
      have hmaskAtControl := hmask
      change CanonicalRecordingSlice.recordingMask (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) inputZero.ownArm
        (ContinuousLearningRows.sliceAt inputZero.time inputZero.row.2) at hmaskAtControl
      simpa [inputZero, input, ReferenceActivePhysicalStep.liveRecordingInput, P,
        hprepareArm, d.instruction_time, ← hsliceEq] using hmaskAtControl
    have hthreshold := hthresholdAt j harmj
    have hthinCanonical :
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          timeControl.1).val ≤
          CanonicalRecordingRates.xi p rate.eta.val
            (AssignmentScoreReconstruction.currentWeight d.out) j /
              CanonicalRecordingSlice.pilotRecordingGateRawProbability
                (K := p.K) (ActiveRoundActions.coordinator p.two_le_m) := by
      rw [← hthreshold]
      have hthinAtSlice :
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
            (ContinuousLearningRows.sliceAt d.record.input.time
              d.record.input.row.2)).val ≤
            CoordinatorRecorderComplementBridge.threshold inputZero
              hlocalInputsZero := by
        simpa [CoordinatorRecorderComplementBridge.thinScalar, inputZero, input,
          ReferenceActivePhysicalStep.liveRecordingInput, P,
          d.instruction_time] using hthin
      have hthinAtControl := hthinAtSlice
      rw [← hsliceEq] at hthinAtControl
      exact hthinAtControl
    have hgateSlice : CanonicalRecordingSlice.pilotRecordingGate
        p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j
        (CanonicalRecordingRates.xi p rate.eta.val
          (AssignmentScoreReconstruction.currentWeight d.out) j /
            CanonicalRecordingSlice.pilotRecordingGateRawProbability
              (K := p.K) (ActiveRoundActions.coordinator p.two_le_m))
        timeControl.1 := by
      exact ⟨hdataSliceOfLocal hdata, hsourceSliceOfLocal hsource,
        hpilot, hmaskCanonical, hthinCanonical⟩
    refine ⟨hnotSlow, ?_⟩
    rw [← hsliceEq]
    exact hgateSlice
  · rintro ⟨hnotSlow, hgateSlice⟩
    rcases hgateSlice with ⟨hslot, hrecorder, hpilot, hmaskCanonical, hthinCanonical⟩
    have hslotTime :
        PublicDiscreteDraws.slotDraw timeControl.1 = PublicDiscreteDraws.dataSlot := by
      simpa [hsliceEq] using hslot
    have hrecorderTime :
        PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K timeControl.1 =
          ActiveRoundActions.coordinator p.two_le_m := by
      simpa [hsliceEq] using hrecorder
    have hpilotTime : PublicDiscreteDraws.pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) timeControl.1 = j := by
      simpa [hsliceEq] using hpilot
    have hmaskCanonicalTime : CanonicalRecordingSlice.recordingMask
        (K_pos p) (ActiveRoundActions.coordinator p.two_le_m) j timeControl.1 := by
      rw [← hsliceEq] at hmaskCanonical
      exact hmaskCanonical
    have hthinCanonicalTime :
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          timeControl.1).val ≤
          CanonicalRecordingRates.xi p rate.eta.val
            (AssignmentScoreReconstruction.currentWeight d.out) j /
              CanonicalRecordingSlice.pilotRecordingGateRawProbability
                (K := p.K) (ActiveRoundActions.coordinator p.two_le_m) := by
      rw [← hsliceEq] at hthinCanonical
      exact hthinCanonical
    have hdata : CoordinatorRecorderComplementBridge.selectedSlot inputZero =
        PublicDiscreteDraws.dataSlot := by
      simpa [inputZero, input, ReferenceActivePhysicalStep.liveRecordingInput,
        CoordinatorRecorderComplementBridge.selectedSlot,
        CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights,
        CoordinatorRecordingOperation.selectedSlot, timeControl,
        d.instruction_time] using hslot
    have hsource : CoordinatorRecorderComplementBridge.selectedRecorder inputZero =
        ActiveRoundActions.coordinator p.two_le_m := by
      change CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
          (ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2)) =
          ActiveRoundActions.coordinator p.two_le_m
      rw [CanonicalRecordingSlice.recorderSourceFromScalar_coordinate
        p.two_le_m p.m_lt_K
        (ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2)]
      exact hrecorder
    have hpilotInput : inputZero.ownArm = j := by
      have harm := hpilotOfData hdata
      calc
        inputZero.ownArm = input.ownArm := by simp [inputZero]
        _ = j := harm.trans hpilotTime
    have howns : CoordinatorRecorderComplementBridge.ownsArm inputZero := by
      have hownU : inputZero.ownArm ∉
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u t b.1.1 b.1.2).val := by
        simpa [hpilotInput] using hnotSlow
      have hownPayload : inputZero.ownArm ∉ r.payload.slowSet.val := by
        rw [hslowSet]
        exact hownU
      have hownAssignment : inputZero.ownArm ∉
          (SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment).val := by
        rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload r.payload]
        exact hownPayload
      have hownOp : CoordinatorRecordingOperation.ownsArm
          (.live r.payload.assignment false) inputZero.ownArm := by
        simpa [CoordinatorRecordingOperation.ownsArm] using hownAssignment
      simpa [CoordinatorRecorderComplementBridge.ownsArm,
        CoordinatorRecorderComplementBridge.operationMode, hmodeZero] using hownOp
    have hmask : CoordinatorRecorderComplementBridge.ownMaskPasses inputZero := by
      change CanonicalRecordingSlice.recordingMask (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) inputZero.ownArm
        (ContinuousLearningRows.sliceAt inputZero.time inputZero.row.2)
      rw [hpilotInput]
      rw [hsliceEq] at hmaskCanonicalTime
      simpa [inputZero, input, ReferenceActivePhysicalStep.liveRecordingInput, P,
        d.instruction_time] using hmaskCanonicalTime
    have hthin : CoordinatorRecorderComplementBridge.thinScalar inputZero ≤
        CoordinatorRecorderComplementBridge.threshold inputZero hlocalInputsZero := by
      have hthreshold := hthresholdAt j hpilotInput
      rw [hthreshold]
      rw [hsliceEq] at hthinCanonicalTime
      simpa [CoordinatorRecorderComplementBridge.thinScalar,
        CoordinatorRecorderComplementBridge.threshold,
        inputZero, input, ReferenceActivePhysicalStep.liveRecordingInput, P,
        hpilotInput, d.instruction_time] using hthinCanonicalTime
    obtain ⟨out, hout, houtGate, _⟩ :=
      CoordinatorRecorderComplementBridge.run_gate_and_floor inputZero
        hlocalInputsZero hdata hsource hnotFrozenZero howns hmask hthin
    have hrunMap :
        (CoordinatorRecorderComplementBridge.run inputZero).map
          CoordinatorRecordingOperation.Output.gateArm = some (some inputZero.ownArm) := by
      rw [hout]
      exact congrArg some houtGate
    have hrecordMap := hrunMap.symm.trans hzeroMap
    have houtRecording : out.gateArm = recording.gateArm :=
      houtGate.trans (Option.some.inj hrecordMap)
    have hgateOut : out.gateArm = some j := by
      rw [houtGate, hpilotInput]
    have hinner : some inputZero.ownArm = some j := by
      exact houtGate.symm.trans hgateOut
    have harmj : inputZero.ownArm = j := Option.some.inj hinner
    have hnotSlowInput : j ∉
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
          rate rewards C_star C_h u t b.1.1 b.1.2).val := by
      simpa [harmj] using hnotSlow
    have hpilot' :
        PublicDiscreteDraws.pilotDraw (K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) timeControl.1 = j := by
      have harm := hpilotOfData hdata
      calc
        _ = input.ownArm := harm.symm
        _ = inputZero.ownArm := by simp [inputZero]
        _ = j := harmj
    have hgateSlice : CanonicalRecordingSlice.pilotRecordingGate
        p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j
        (CanonicalRecordingRates.xi p rate.eta.val
          (AssignmentScoreReconstruction.currentWeight d.out) j /
            CanonicalRecordingSlice.pilotRecordingGateRawProbability
              (K := p.K) (ActiveRoundActions.coordinator p.two_le_m))
        timeControl.1 := by
      exact ⟨hslotTime, hrecorderTime, hpilot', hmaskCanonicalTime,
        hthinCanonicalTime⟩
    have hrecorded : recording.gateArm = some j := by
      calc
        recording.gateArm = out.gateArm := houtRecording.symm
        _ = some j := hgateOut
    exact hrecorded

end Bandits.Support.ReferenceFirstCollectionRenewalCoordinatorGate
