/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveWeightEnvelope
public import Bandits.Support.ReferenceFirstAssignmentFibreStep
public import Bandits.Support.ReferenceCoordinatorLiveRecording

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual coordinator safety on the first live window

For the original complete rows, selected private row, and whole grid reward
table, every retained record before the first chosen cutoff performs the
coordinator's actual recorder, complement service, confirmation, and finish
operations successfully. The retained coordinator diagnostic has no failure,
and its next state is live. At every completed prefix the coordinator is
still first at length zero and is an actual live state at every positive
length. Followers remain unrestricted, including dagger configurations.

The window is exactly the accepted `firstLiveWindow` takeWhile predicate.
Failed rounds are not filtered out. If a chosen cutoff lies in the finite
physical run, its record is the explicit next boundary outside this window.
No nonexistent round is introduced at the terminal endpoint.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-104,140-174,219-241`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceFirstComplementMassBudget
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceRunClockPreservation
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.FollowerCutoffScan

namespace Bandits.Support.ReferenceFirstLiveCoordinatorSafety

abbrev Parameters := ReferenceFirstLiveWeightEnvelope.Parameters
abbrev RateInput := ReferenceFirstLiveWeightEnvelope.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem firstWindow_record_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (k : ℕ) (hkcount : k < count)
    (hkwindow : k <
      (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
        start count hspan active).length) :
    (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
      start count hspan active)[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k (by omega) active := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let W := ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
    start count hspan active
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclock := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start count hspan active hseed
  have hwindowPrefix : W.IsPrefix E.records := by
    exact List.takeWhile_prefix _
  have hkE : k < E.records.length := by
    exact lt_of_lt_of_le hkwindow hwindowPrefix.length_le
  have hwindowElem : W[k] = E.records[k] := hwindowPrefix.getElem hkwindow
  have htimeMap := hclock.2.2.1
  have hkMap : k < (E.records.map (fun record => record.input.time.val)).length := by
    simpa using hkE
  have htimeElem :
      (E.records.map (fun record => record.input.time.val))[k] = W[k].input.time.val := by
    calc
      (E.records.map (fun record => record.input.time.val))[k] = E.records[k].input.time.val := by
        simp
      _ = W[k].input.time.val := by rw [← hwindowElem]
  have hwindowTime : W[k].input.time.val = start + k := by
    have htimeMap' : E.records.map (fun record => record.input.time.val) =
        ReferenceActivePhysicalHorizon.calendar start count := by
      simpa [E, ReferenceFirstComplementMassBudget.originalRun] using htimeMap
    have hkCalendar : k < (ReferenceActivePhysicalHorizon.calendar start count).length := by
      simpa [ReferenceActivePhysicalHorizon.calendar] using hkcount
    have hmapElem :
        (E.records.map (fun record => record.input.time.val))[k] =
          (ReferenceActivePhysicalHorizon.calendar start count)[k] :=
      List.getElem_of_eq htimeMap' hkMap
    have hcalendar :
        (ReferenceActivePhysicalHorizon.calendar start count)[k] = start + k := by
      simp [ReferenceActivePhysicalHorizon.calendar]
    calc
      W[k].input.time.val = (E.records.map (fun record => record.input.time.val))[k] :=
        htimeElem.symm
      _ = (ReferenceActivePhysicalHorizon.calendar start count)[k] := hmapElem
      _ = start + k := hcalendar
  let priorRun := ReferenceFirstComplementMassBudget.originalPrefix
    initial rows J rewards start count hspan active (k + 1) (by omega)
  let actual := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hprefixRecords : ∃ suffix, E.records = priorRun.records ++ suffix := by
    obtain ⟨suffix, hrecords⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
      initial rows J rewards start (k + 1) (count - (k + 1)) (by omega) active
    refine ⟨suffix, ?_⟩
    have hkNext : k + 1 ≤ count := by omega
    simpa [E, priorRun, ReferenceFirstComplementMassBudget.originalRun,
      ReferenceFirstComplementMassBudget.originalPrefix,
      Nat.add_sub_of_le hkNext] using hrecords
  obtain ⟨suffix, hrecords⟩ := hprefixRecords
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hactualMemPrefix : actual ∈ priorRun.records := by
    rw [hsuccessor]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hactualMemE : actual ∈ E.records := by
    rw [hrecords]
    exact List.mem_append_left _ hactualMemPrefix
  have hwindowMemE : W[k] ∈ E.records := by
    rw [hwindowElem]
    exact List.getElem_mem hkE
  have hactualTime : actual.input.time.val = start + k := rfl
  exact ReferenceAssignmentPayloadChronology.run_records_time_injective
    initial rows J rewards start count hspan active hwindowMemE hactualMemE
    (hwindowTime.trans hactualTime.symm)

private theorem executeValid_some_of_inputsValid
    (input : CoordinatorRecordingOperation.Input p)
    (hvalid : CoordinatorRecordingOperation.InputsValid input) :
    ∃ output, CoordinatorRecordingOperation.executeValid input hvalid = some output := by
  classical
  by_cases hdata : CoordinatorRecordingOperation.selectedSlot input =
      PublicDiscreteDraws.dataSlot
  · by_cases hsource : CoordinatorRecordingOperation.selectedRecorder input =
        ActiveRoundActions.coordinator p.two_le_m
    · by_cases hfrozen : CoordinatorRecordingOperation.isFrozen input
      · exact ⟨CoordinatorRecordingOperation.zeroOutput p, by
          simp [CoordinatorRecordingOperation.executeValid, hdata, hsource, hfrozen]⟩
      · by_cases howns : CoordinatorRecordingOperation.ownsArm input.mode input.ownArm
        · by_cases hmask : CoordinatorRecordingOperation.ownMaskPasses input
          · have hraw := CoordinatorRecordingOperation.rawGateMass_feasible
              input hvalid howns
            have hthreshold :=
              CoordinatorRecordingOperation.coordinatorThreshold_mem_Icc_of_owned
                input hvalid howns
            have hparameter :
                CanonicalRecordingRates.xi p input.eta input.anchor input.ownArm /
                  CoordinatorRecordingOperation.coordinatorRawGateMass input hvalid ∈
                  Set.Icc (0 : ℝ) 1 := by
              simpa [CoordinatorRecordingOperation.coordinatorThreshold] using hthreshold
            have hfloor := CoordinatorRecordingOperation.floorArrival_le_D input hvalid
            by_cases hthin :
                (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                  (ContinuousLearningRows.sliceAt input.time input.row.2)).val ≤
                  CoordinatorRecordingOperation.coordinatorThreshold input hvalid
            · have hthin' :
                  (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                    (ContinuousLearningRows.sliceAt input.time input.row.2)).val ≤
                  CanonicalRecordingRates.xi p input.eta input.anchor input.ownArm /
                      CoordinatorRecordingOperation.coordinatorRawGateMass input hvalid := by
                simpa [CoordinatorRecordingOperation.coordinatorThreshold] using hthin
              refine ⟨⟨some input.ownArm,
                CoordinatorRecordingOperation.floorArrival input, hfloor⟩, ?_⟩
              simp [CoordinatorRecordingOperation.executeValid, hdata, hsource,
                hfrozen, howns, hmask, hraw.1, hparameter, hthin', hfloor]
            · refine ⟨CoordinatorRecordingOperation.zeroOutput p, ?_⟩
              have hthin' :
                  ¬ (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                    (ContinuousLearningRows.sliceAt input.time input.row.2)).val ≤
                    CanonicalRecordingRates.xi p input.eta input.anchor input.ownArm /
                      CoordinatorRecordingOperation.coordinatorRawGateMass input hvalid := by
                simpa [CoordinatorRecordingOperation.coordinatorThreshold] using hthin
              simp [CoordinatorRecordingOperation.executeValid, hdata, hsource,
                hfrozen, howns, hmask, hraw.1, hparameter, hthin']
          · exact ⟨CoordinatorRecordingOperation.zeroOutput p, by
              simp [CoordinatorRecordingOperation.executeValid, hdata, hsource,
                hfrozen, howns, hmask]⟩
        · exact ⟨CoordinatorRecordingOperation.zeroOutput p, by
            simp [CoordinatorRecordingOperation.executeValid, hdata, hsource,
              hfrozen, howns]⟩
    · exact ⟨CoordinatorRecordingOperation.zeroOutput p, by
        simp [CoordinatorRecordingOperation.executeValid, hdata, hsource]⟩
  · exact ⟨CoordinatorRecordingOperation.zeroOutput p, by
      simp [CoordinatorRecordingOperation.executeValid, hdata]⟩

private theorem actual_live_recording_some
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload started time
      r.complementWeights x.row) :
    ∃ recording,
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) = some recording := by
  let input := ReferenceActivePhysicalStep.liveRecordingInput prepared r started
  have hlocal := ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
    prepared r started time selection
  have hvalid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hlocal
  obtain ⟨recording, hrecording⟩ := executeValid_some_of_inputsValid
    (CoordinatorRecorderComplementBridge.recorderInput input) hvalid
  refine ⟨recording, ?_⟩
  rw [CoordinatorRecorderComplementBridge.run_eq_executeValid input hlocal]
  exact hrecording

private theorem actual_confirmation_update_some
    (payload : AssignmentStartPayload.Input p rate.eta)
    (pending : Finset (Fin (p.m - 1))) (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (observation : Fin (D p + 1))
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid payload cutoff time weights) :
    ∃ pendingAfter,
      CoordinatorLocalArmChoice.confirmationUpdate payload pending cutoff time row
        observation = some pendingAfter := by
  classical
  let checked := CoordinatorLocalArmChoice.confirmationInputsValid_mk payload cutoff time
    choiceValid.time.assignment_started choiceValid.time.cutoff_after_start
  let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
    p.m_lt_K (row.2 time).1
  let pendingAfter :=
    if CoordinatorLocalArmChoice.downConfirmationEvent payload pending cutoff time
        (row.2 time) observation then pending.erase selected else pending
  refine ⟨pendingAfter, ?_⟩
  simp [pendingAfter, selected, CoordinatorLocalArmChoice.confirmationUpdate,
    CoordinatorLocalArmChoice.confirmationUpdateCore, checked]
  rfl

private theorem actual_first_finish_success
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput
        (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selection)
    (pending : Finset (Fin (p.m - 1))) :
    ∃ finished,
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time
        installed.startRoundResult.clock pending x.row = .ok finished := by
  have hinstalled := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    x installed selection hchosen
  let launch := CoordinatorRoundDispatch.firstLaunchInput
    (ReferenceActivePhysicalStep.firstInput x)
  have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    x installed selection hchosen
  rw [hinstalled] at htime
  have hinstalledTime :
      (CoordinatorAssignmentRegisterInstall.installFirst launch).registers.time = x.time := by
    change (CoordinatorAssignmentRegisterInstall.installFirst launch).registers.time = x.time at htime
    exact htime
  have hlaunchTime : launch.sigma =
      (CoordinatorAssignmentRegisterInstall.installFirst launch).registers.time := by
    rw [CoordinatorAssignmentRegisterInstall.first_registers_time]
    rfl
  have hsourceTime : launch.sigma = x.time := by
    exact hlaunchTime.trans hinstalledTime
  have hgrid := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
    rate.eta.property launch.eta_le_source_cap launch.sigma
  have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val
      (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).clock := by
    rcases hgrid with ⟨hafter, hbound⟩
    simpa [CoordinatorPhaseClock.clockRegistersValid,
      CoordinatorAssignmentRegisterInstall.firstStartRoundResult,
      CoordinatorPhaseClock.boundaryFromSigma, launch,
      CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput] using And.intro hafter hbound
  have htimeValid : CoordinatorPhaseClock.finishRoundTimeValid x.time
      (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).clock := by
    rw [← hsourceTime]
    simpa [CoordinatorPhaseClock.finishRoundTimeValid,
      CoordinatorAssignmentRegisterInstall.firstStartRoundResult,
      FollowerCutoffScan.calendarRound, launch,
      CoordinatorRoundDispatch.firstLaunchInput,
      ReferenceActivePhysicalStep.firstInput] using
        And.intro (Nat.le_refl launch.sigma.val) (Nat.le_of_lt hgrid.1)
  have hsigma :
      (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).clock.sigma ≠ none := by
    simp [CoordinatorAssignmentRegisterInstall.firstStartRoundResult]
  have hu :
      (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).clock.u = none := rfl
  obtain ⟨finished, hfinish, _, _, _⟩ :=
    CoordinatorPhaseClock.finishRound_live_savedProposal p rate.eta.val x.time
      (CoordinatorAssignmentRegisterInstall.firstStartRoundResult launch).clock pending x.row
      hclock htimeValid hsigma hu
      (CoordinatorAssignmentRegisterInstall.first_proposal_parameter_valid launch)
  refine ⟨finished, ?_⟩
  rw [hinstalled]
  simpa [launch, CoordinatorAssignmentRegisterInstall.installFirst] using hfinish

private def liveContinuationResultPair {x : CoordinatorRoundDispatch.LiveInput p}
    (outcome : CoordinatorRoundDispatch.LiveOutcome x) :
    Option (CoordinatorPhaseClock.StartRoundResult p ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  match outcome with
  | .continuingChosen dispatched _ continuation _ =>
      some (dispatched.startResult, continuation.startRoundResult)
  | _ => none

private theorem live_dispatch_continuation_result
    {x : CoordinatorRoundDispatch.LiveInput p}
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation x.registers x.row)
    (selection : CoordinatorRoundDispatch.ArmSelection x.registers.payload
      dispatched.startResult x.registers.time x.registers.complementWeights x.row)
    (hstart : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok dispatched.startResult)
    (hactual : CoordinatorRoundDispatch.dispatchLive x =
      .continuingChosen dispatched hstart continuation selection) :
    continuation.startRoundResult = dispatched.startResult := by
  unfold CoordinatorRoundDispatch.dispatchLive at hactual
  dsimp only at hactual
  repeat' (first | split at hactual <;> try cases hactual)
  case h_3 =>
    rename_i actualDispatched hdispatch hinitialization
    by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        x.registers actualDispatched.startResult
    · simp only [dite_eq_left hframe] at hactual
      by_cases hpayload : x.registers.priorClock.sigma = some x.registers.payload.sigma
      · simp only [dite_eq_left hpayload] at hactual
        by_cases hgrid : x.registers.gridBoundary = x.registers.priorClock.g
        · simp only [dite_eq_left hgrid] at hactual
          by_cases hscore : x.registers.scoreDomainValid
          · simp only [dite_eq_left hscore] at hactual
            by_cases hqueue : x.ownedRegisters.queueDomainValid
            · simp only [dite_eq_left hqueue] at hactual
              by_cases hprevious : x.ownedRegisters.previousServiceDomainValid
              · simp only [dite_eq_left hprevious] at hactual
                by_cases hbase : ∀ i, x.followerBaseScore i ≤ p.T * D p
                · simp only [dite_eq_left hbase] at hactual
                  by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                      x.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        actualDispatched.startResult.clock.u) x.registers.time
                  · simp only [dite_eq_left hlive] at hactual
                    by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                        x.registers.payload
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          actualDispatched.startResult.clock.u)
                        x.registers.time x.registers.complementWeights
                    · simp only [dite_eq_left hchoice] at hactual
                      by_cases hboundary : actualDispatched.startResult.clock.g ≤ p.T + 1
                      · simp only [dite_eq_left hboundary] at hactual
                        by_cases henvelope : x.registers.complementEnvelopeValid
                        · simp only [dite_eq_left henvelope] at hactual
                          have hnonempty :=
                            CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                              x.registers.payload actualDispatched.startResult.pending
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                actualDispatched.startResult.clock.u)
                              x.registers.time x.registers.complementWeights x.row hchoice
                          split at hactual
                          · rename_i hselected
                            exact False.elim (hnonempty hselected)
                          · have hp := congrArg liveContinuationResultPair hactual
                            have hp' := by
                              simpa only [liveContinuationResultPair] using hp
                            have hpair := Option.some.inj hp'
                            have hfirst := congrArg Prod.fst hpair
                            have hsecond := congrArg Prod.snd hpair
                            exact hsecond.symm.trans hfirst
                        · simp only [dite_eq_right henvelope] at hactual
                          cases hactual
                      · simp only [dite_eq_right hboundary] at hactual
                        cases hactual
                    · simp only [dite_eq_right hchoice] at hactual
                      cases hactual
                  · simp only [dite_eq_right hlive] at hactual
                    cases hactual
                · simp only [dite_eq_right hbase] at hactual
                  cases hactual
              · simp only [dite_eq_right hprevious] at hactual
                cases hactual
            · simp only [dite_eq_right hqueue] at hactual
              cases hactual
          · simp only [dite_eq_right hscore] at hactual
            cases hactual
        · simp only [dite_eq_right hgrid] at hactual
          cases hactual
      · simp only [dite_eq_right hpayload] at hactual
        cases hactual
    · simp only [dite_eq_right hframe] at hactual
      cases hactual
  case h_1 =>
    rename_i actualDispatched hdispatch ledger hinitialization hchoice hboundary
      henvelope hselected
    have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
      x.registers.payload actualDispatched.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        actualDispatched.startResult.clock.u)
      x.registers.time x.registers.complementWeights x.row hchoice
    exact False.elim (hnonempty hselected)

private theorem actual_live_finish_success
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output r q base)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation r x.row)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val r.time r.priorClock
      r.clockPending = .ok dispatched.startResult)
    (hresult : continuation.startRoundResult = dispatched.startResult)
    (htime : r.time = x.time)
    (hu : r.priorClock.u = none) :
    ∀ pending,
      ∃ finished,
        CoordinatorPhaseClock.finishRound p rate.eta.val x.time
          dispatched.startResult.clock pending x.row = .ok finished := by
  intro pending
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
      r.time r.complementWeights := continuation.choiceInputsValid
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u) r.time := by
    change CoordinatorLocalArmChoice.assignmentStart r.payload ≤
        CoordinatorLocalArmChoice.sourceRound r.time ∧
      CoordinatorLocalArmChoice.sourceRound r.time <
        CoordinatorLocalArmChoice.cutoffRound
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u)
    constructor
    · exact hchoice.time.assignment_started
    · simp [CoordinatorLiveChoiceRecorderStep.cutoffFromClock, hu,
        CoordinatorLocalArmChoice.cutoffRound, CoordinatorLocalArmChoice.sourceRound]
  let domain : CoordinatorLiveChoiceRecorderStep.PreparationDomain r := {
    startResult := dispatched.startResult
    startRound_eq := hstart
    clockFrame := by
      simpa only [hresult] using continuation.clockFrame
    payloadClockStart := continuation.payloadClockStart
    gridBoundary_eq_clock := continuation.gridBoundary_eq_clock
    scoreDomainValid := continuation.scoreDomainValid
    assignmentLive := hlive
    choiceInputsValid := continuation.choiceInputsValid
    recorderInputsValid := continuation.recorderInputsValid }
  obtain ⟨prepared, hprepare, hpreparedStart⟩ :=
    CoordinatorLiveChoiceRecorderStep.prepare_success_of_domain domain x.row
  obtain ⟨finished, hfinish, _, _, _⟩ :=
    CoordinatorLiveServiceFinish.finishRound_live_success domain prepared hprepare pending
  refine ⟨finished, ?_⟩
  simpa [domain, hpreparedStart, hresult, htime] using hfinish

private theorem actual_postChoice_record_safety
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (prepared : ReferenceActivePhysicalStep.PreparedRound record.input)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r q)
    (finished : CoordinatorPhaseClock.FinishRoundResult p)
    (hobserve : prepared.observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice prepared r q base started)
    (hpreparedOutput : prepared = record.output.preparation)
    (hpost : ReferenceActivePhysicalStep.livePostChoice prepared r q base started =
      ⟨.live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        record.input.state.upDecoderBank, none, some recording, none⟩) :
    record.output.coordinator.failure = none ∧
      record.output.coordinator.recording = some recording ∧
      ∃ nextRegisters nextOwned nextBase,
        record.output.next.coordinator = .live nextRegisters nextOwned nextBase := by
  have hprepared : prepared = ReferenceActivePhysicalStep.prepare record.input := by
    calc
      prepared = record.output.preparation := hpreparedOutput
      _ = (ReferenceActivePhysicalStep.step record.input).preparation := by
        rw [record.output_eq]
      _ = ReferenceActivePhysicalStep.prepare record.input := rfl
  have hcoordinator : record.output.coordinator =
      ⟨.live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base,
        record.input.state.upDecoderBank, none, some recording, none⟩ := by
    calc
      record.output.coordinator = (ReferenceActivePhysicalStep.step record.input).coordinator := by
        rw [record.output_eq]
      _ = (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := rfl
      _ = prepared.observeCoordinator := by rw [← hprepared]
      _ = ReferenceActivePhysicalStep.livePostChoice prepared r q base started := hobserve
      _ = _ := hpost
  have hstepNext := (ReferenceActivePhysicalStep.step_next_fields record.input).1
  rw [← hprepared] at hstepNext
  have hnext : record.output.next.coordinator =
      .live {
          payload := r.payload
          priorClock := finished.clock
          pendingAtChoice := finished.pending
          time := record.input.time
          gridBoundary := finished.clock.g
          complementScores := serviced.score }
        { queue := serviced.queue, previousService := serviced.previousService } base := by
    calc
      record.output.next.coordinator = (ReferenceActivePhysicalStep.step record.input).next.coordinator := by
        rw [record.output_eq]
      _ = prepared.observeCoordinator.configuration := hstepNext
      _ = (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).configuration := by
        rw [hobserve]
      _ = _ := by rw [hpost]
  exact ⟨by rw [hcoordinator], by rw [hcoordinator], _, _, _, hnext⟩

private theorem run_first_window_prefix_safety
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (window : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hwindow : window = ReferenceFirstComplementMassBudget.firstWindow
      initial rows J rewards start count hspan active) :
    ∀ k (hk : k ≤ window.length) (hspanK : start + k ≤ p.T),
      (∀ j (hj : j < k),
        let record := window[j]
        record.output.coordinator.failure = none ∧
          ∃ recording, record.output.coordinator.recording = some recording ∧
            ∃ nextRegisters nextOwned nextBase,
              record.output.next.coordinator = .live nextRegisters nextOwned nextBase) ∧
      (k = 0 →
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
          hspanK active).finalState.coordinator = .first) ∧
      (0 < k →
        ∃ registers owned base,
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
            hspanK active).finalState.coordinator = .live registers owned base) := by
  intro k
  induction k with
  | zero =>
      intro hk hspanK
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        omega
      · intro _
        simpa [ReferenceActivePhysicalHorizon.run_zero_final] using hfirst
      · intro hpos
        omega
  | succ k ih =>
      intro hk hspanK
      have hkprev : k ≤ window.length := by omega
      have hklt : k < window.length := by omega
      have hwindowCount : window.length ≤ count := by
        rw [hwindow]
        calc
          (ReferenceFirstComplementMassBudget.firstWindow
              initial rows J rewards start count hspan active).length ≤
              (ReferenceActivePhysicalHorizon.run initial rows J rewards
                start count hspan active).records.length :=
            (List.takeWhile_prefix _).length_le
          _ = count := ReferenceActivePhysicalHorizon.run_record_count
            initial rows J rewards start count hspan active
      have hkcount : k < count := by omega
      have hspanPrev : start + k ≤ p.T := by
        calc
          start + k ≤ start + (k + 1) := Nat.add_le_add_left (Nat.le_succ k) start
          _ ≤ p.T := by simpa [Nat.add_assoc] using hspanK
      have hkWindow : k <
          (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards start count
            hspan active).length := by
        rw [← hwindow]
        exact hklt
      let record := (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
        start count hspan active)[k]
      have hrecordEq : record =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt
            initial rows J rewards start k (by omega) active := by
        exact firstWindow_record_eq_actualRunRecordAt initial rows J rewards
          start count hspan active hfirst k hkcount hkWindow
      let priorRun := ReferenceActivePhysicalHorizon.run initial rows J rewards
        start k hspanPrev active
      have hrecordState : record.input.state = priorRun.finalState := by
        rw [hrecordEq]
        rfl
      have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start count hspan active hseed
      have hclockRecord : ReferenceCoordinatorClockDomains.clockAt rows J
          record.input.time.val record.input.state := by
        rw [hrecordEq]
        simpa [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
          ReferenceActivePhysicalHorizon.roundInputAt, priorRun] using
          (hclockRun.2.1 k (Nat.le_of_lt hkcount))
      have hwindowMember : record ∈ window := by
        simpa only [record, hwindow] using List.getElem_mem hkWindow
      have hwindowMember' : record ∈
          ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards start count
            hspan active := by
        exact List.getElem_mem hkWindow
      have hnotCutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        have htake := List.mem_takeWhile_imp hwindowMember'
        change (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true at htake
        simpa only [Bool.not_eq_true'] using htake
      have hprev := ih hkprev hspanPrev
      have hprevFirst : k = 0 → priorRun.finalState.coordinator = .first := by
        simpa only [priorRun] using hprev.2.1
      have hprevLive : 0 < k →
          ∃ registers owned base, priorRun.finalState.coordinator = .live registers owned base := by
        simpa only [priorRun] using hprev.2.2
      have hstepSuccess :
          record.output.coordinator.failure = none ∧
            ∃ recording, record.output.coordinator.recording = some recording ∧
              ∃ nextRegisters nextOwned nextBase,
                record.output.next.coordinator = .live nextRegisters nextOwned nextBase := by
        cases hkzero : k with
        | zero =>
            have hinputFirst : record.input.state.coordinator = .first := by
              rw [hrecordState]
              exact hprevFirst hkzero
            obtain ⟨installed, selection, hchosen⟩ :=
              ReferenceFirstAssignmentFibreStep.dispatchFirst_chosen_exists
                (ReferenceActivePhysicalStep.firstInput record.input)
            have hpreparedChoice :
                record.output.preparation.coordinator = .first (.chosen installed selection) := by
              rw [record.output_eq]
              calc
                (ReferenceActivePhysicalStep.step record.input).preparation.coordinator =
                    (ReferenceActivePhysicalStep.prepare record.input).coordinator := rfl
                _ = .first (CoordinatorRoundDispatch.dispatchFirst
                    (ReferenceActivePhysicalStep.firstInput record.input)) :=
                  ReferenceActivePhysicalStep.dispatch_first record.input hinputFirst
                _ = .first (.chosen installed selection) := by rw [hchosen]
            have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
              record.input installed selection hchosen
            have htimeAligned : installed.registers.time = record.input.time := htime
            let prepared := record.output.preparation
            have hrecording := actual_live_recording_some prepared installed.registers
              installed.startRoundResult installed.registers.time selection
            obtain ⟨recording, hrecording⟩ := hrecording
            have hbudget := ReferenceFirstComplementMassBudget.run_first_service_pass_budget
              initial rows J rewards start count hspan active hfirst ⟨k, hkWindow⟩
            dsimp only at hbudget
            have hpreparedChoiceBudget := by
              simpa only [record] using hpreparedChoice
            simp only [hpreparedChoiceBudget] at hbudget
            obtain ⟨serviced, hservice, hbudgetScore, hretained⟩ :=
              hbudget recording hrecording
            have hchoiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid
                installed.registers.payload
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  installed.startRoundResult.clock.u)
                record.input.time installed.registers.complementWeights := by
              simpa [htimeAligned] using selection.choiceInputsValid
            obtain ⟨pending, hconfirmation⟩ := actual_confirmation_update_some
              installed.registers.payload installed.startRoundResult.pending
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                installed.startRoundResult.clock.u)
              record.input.time record.input.row record.output.preparation.coordinatorObservation
              installed.registers.complementWeights hchoiceValid
            obtain ⟨finished, hfinish⟩ := actual_first_finish_success
              installed selection hchosen pending
            have hpost := ReferenceActivePhysicalStep.livePostChoice_success
              prepared installed.registers installed.ownedRegisters installed.followerBaseScore
              installed.startRoundResult recording serviced pending finished hrecording
              hservice hconfirmation hfinish
            have hobserve : prepared.observeCoordinator =
                ReferenceActivePhysicalStep.livePostChoice prepared installed.registers
                  installed.ownedRegisters installed.followerBaseScore installed.startRoundResult := by
              rw [ReferenceActivePhysicalStep.observeCoordinator_first_equation
                prepared (.chosen installed selection) hpreparedChoice]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt, htimeAligned]
            have hrecordSafety := actual_postChoice_record_safety (record := record) prepared installed.registers
              installed.ownedRegisters installed.followerBaseScore installed.startRoundResult
              recording serviced finished hobserve rfl hpost
            exact ⟨hrecordSafety.1, ⟨recording, hrecordSafety.2⟩⟩
        | succ j =>
            have hinputLive : ∃ registers owned base,
                record.input.state.coordinator = .live registers owned base := by
              obtain ⟨registers, owned, base, hlive⟩ := hprevLive (by omega)
              exact ⟨registers, owned, base, by rw [hrecordState]; exact hlive⟩
            obtain ⟨oldRegisters, oldOwned, oldBase, hcoord⟩ := hinputLive
            have hclockLive := hclockRecord
            simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclockLive
            rcases hclockLive with ⟨_, hclockValid, hsigma, hu, hgrid, hsourceBefore,
              hnextGrid, _⟩
            have hpre := ReferenceFirstLiveWeightEnvelope.run_first_live_prechoice_dispatch_success
              initial rows J rewards start count hspan active hfirst k hkcount
              (Nat.le_of_lt hkWindow)
            dsimp only at hpre
            rw [← hrecordEq] at hpre
            simp only [hcoord] at hpre
            let liveInput := ReferenceActivePhysicalStep.liveInput record.input
              oldRegisters oldOwned oldBase
            cases hdispatchEq : CoordinatorRoundDispatch.dispatchLive liveInput with
            | continuingChosen dispatched hstart continuation selection =>
                have hdispatchLive : CoordinatorRoundDispatch.dispatchLive liveInput =
                    .continuingChosen dispatched hstart continuation selection := by
                  exact hdispatchEq
                have hpreparedChoice : record.output.preparation.coordinator =
                    .live oldRegisters oldOwned oldBase
                      (.continuingChosen dispatched hstart continuation selection) := by
                  rw [record.output_eq]
                  simp [ReferenceActivePhysicalStep.step,
                    ReferenceActivePhysicalStep.prepare,
                    ReferenceActivePhysicalStep.dispatch, hcoord, liveInput,
                    CoordinatorRoundDispatch.dispatch, hdispatchLive]
                  rfl
                let actualRegisters := ReferenceActivePhysicalStep.liveRegistersAt
                  oldRegisters record.input.time
                let actualOwned := ReferenceActivePhysicalStep.liveOwnedAt
                  oldRegisters oldOwned record.input.time
                let prepared := record.output.preparation
                have hrecording := actual_live_recording_some prepared actualRegisters
                  dispatched.startResult actualRegisters.time selection
                obtain ⟨recording, hrecording⟩ := hrecording
                have hbudget := ReferenceFirstComplementMassBudget.run_first_service_pass_budget
                  initial rows J rewards start count hspan active hfirst ⟨k, hkWindow⟩
                dsimp only at hbudget
                have hpreparedChoiceBudget := by
                  simpa only [record] using hpreparedChoice
                simp only [hpreparedChoiceBudget] at hbudget
                obtain ⟨serviced, hservice, hbudgetScore, hretained⟩ :=
                  hbudget recording hrecording
                have hchoiceValid : CoordinatorLocalArmChoice.ChoiceInputsValid
                    actualRegisters.payload
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                      dispatched.startResult.clock.u)
                    record.input.time actualRegisters.complementWeights := by
                  simpa [liveInput, ReferenceActivePhysicalStep.liveInput, actualRegisters,
                    ReferenceActivePhysicalStep.liveRegistersAt] using
                    selection.choiceInputsValid
                have hcontinuationResult :
                    continuation.startRoundResult = dispatched.startResult := by
                  exact live_dispatch_continuation_result dispatched continuation
                    selection hstart hdispatchEq
                obtain ⟨pending, hconfirmation⟩ := actual_confirmation_update_some
                  actualRegisters.payload dispatched.startResult.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    dispatched.startResult.clock.u)
                  record.input.time record.input.row
                  record.output.preparation.coordinatorObservation
                  actualRegisters.complementWeights hchoiceValid
                have hfinish := actual_live_finish_success (x := record.input) actualRegisters
                  actualOwned oldBase dispatched continuation hstart hcontinuationResult
                  rfl hu pending
                obtain ⟨finished, hfinish⟩ := hfinish
                have hpost := ReferenceActivePhysicalStep.livePostChoice_success
                  prepared actualRegisters actualOwned oldBase dispatched.startResult recording
                  serviced pending finished hrecording hservice hconfirmation hfinish
                have hobserve : prepared.observeCoordinator =
                    ReferenceActivePhysicalStep.livePostChoice prepared actualRegisters
                      actualOwned oldBase dispatched.startResult := by
                  rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation
                    prepared oldRegisters oldOwned oldBase
                    (.continuingChosen dispatched hstart continuation selection)
                    hpreparedChoice]
                  simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                    ReferenceActivePhysicalStep.selectionAt,
                    actualRegisters, actualOwned,
                    ReferenceActivePhysicalStep.liveRegistersAt,
                    ReferenceActivePhysicalStep.liveOwnedAt]
                have hrecordSafety := actual_postChoice_record_safety (record := record) prepared
                  actualRegisters actualOwned
                  oldBase dispatched.startResult recording serviced finished
                  hobserve rfl hpost
                exact ⟨hrecordSafety.1, ⟨recording, hrecordSafety.2⟩⟩
            | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
                hclock hpending hassignment selection =>
                have hdispatchLive : CoordinatorRoundDispatch.dispatchLive liveInput =
                    .cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
                      hclock hpending hassignment selection := by
                  exact hdispatchEq
                have hcutoff :
                    ReferenceCollectionPhaseHistory.cutoffChosen record.input = true := by
                  simp [ReferenceCollectionPhaseHistory.cutoffChosen,
                    ReferenceActivePhysicalStep.prepare,
                    ReferenceActivePhysicalStep.dispatch, hcoord, liveInput,
                    CoordinatorRoundDispatch.dispatch, hdispatchLive]
                  rfl
                have hfalse := hnotCutoff
                rw [hcutoff] at hfalse
                cases hfalse
            | clockFailure failure hfailure =>
                simp [liveInput, hdispatchEq] at hpre
            | initializerFailure dispatched hstart checked hchecked =>
                simp [liveInput, hdispatchEq] at hpre
            | localFailure dispatched hstart reason =>
                simp [liveInput, hdispatchEq] at hpre
      have hnextEndpoint :
          ∃ registers owned base,
            (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1)
              hspanK active).finalState.coordinator = .live registers owned base := by
        obtain ⟨recording', hrecorded, registers, owned, base, hrecordNext⟩ :=
          hstepSuccess.2
        have hactualNext :=
          ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
            initial rows J rewards start k hspanK active
        have hrecordNext' :
            (ReferenceAssignmentPayloadChronology.actualRunRecordAt
              initial rows J rewards start k hspanK active).output.next.coordinator =
              .live registers owned base := by
          have hnextRecordEq := congrArg
            (fun actual : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
              actual.output.next.coordinator) hrecordEq
          exact hnextRecordEq.symm.trans hrecordNext
        refine ⟨registers, owned, base, ?_⟩
        rw [hactualNext]
        exact hrecordNext'
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        by_cases hiless : i < k
        · exact hprev.1 i hiless
        · have hieq : i = k := by omega
          subst i
          have hrecordWindow : window[k] = record := by
            simp only [record, hwindow]
          rw [hrecordWindow]
          exact hstepSuccess
      · intro hzero
        omega
      · intro _
        exact hnextEndpoint

private theorem not_predicate_at_takeWhile_end
    {α : Type} (predicate : α → Bool) (records : List α)
    (hidx : (records.takeWhile predicate).length < records.length) :
    predicate (records[(records.takeWhile predicate).length]'hidx) = false := by
  induction records with
  | nil => simp at hidx
  | cons record records ih =>
      cases hpredicate : predicate record with
      | false =>
          simp [hpredicate] at hidx ⊢
      | true =>
          have htail : (records.takeWhile predicate).length < records.length := by
            simpa [List.takeWhile_cons, hpredicate] using hidx
          simpa [List.takeWhile_cons, hpredicate] using ih htail

/-- Actual coordinator-only safety throughout the exact FIRST live takeWhile
window, together with the coordinator endpoint at every completed prefix.
Every root input is the original full row table, private row, reward table,
and active physical run. No success trace, recorder result, numerical envelope,
or follower-state restriction is assumed. The first chosen cutoff is excluded
by the unchanged window predicate and is exposed separately as its next
record when it occurs before the physical run ends.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-104,140-174,219-241`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`.
-/
theorem run_first_live_coordinator_safety
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    (∀ k : Fin window.length,
      let record := window[k.val]
      record.output.coordinator.failure = none ∧
        ∃ recording, record.output.coordinator.recording = some recording ∧
          ∃ nextRegisters nextOwned nextBase,
            record.output.next.coordinator = .live nextRegisters nextOwned nextBase) ∧
    (∀ k (hk : k ≤ window.length),
      (k = 0 →
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
          (by
            have hlength : window.length ≤ count := by
              calc
                window.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
                _ = count := by
                  dsimp [E]
                  exact ReferenceActivePhysicalHorizon.run_record_count
                    initial rows J rewards start count hspan active
            omega) active).finalState.coordinator = .first) ∧
      (0 < k →
        ∃ registers owned base,
          (ReferenceActivePhysicalHorizon.run initial rows J rewards start k
            (by
              have hlength : window.length ≤ count := by
                calc
                  window.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
                  _ = count := by
                    dsimp [E]
                    exact ReferenceActivePhysicalHorizon.run_record_count
                      initial rows J rewards start count hspan active
              omega) active).finalState.coordinator = .live registers owned base)) ∧
    (window.length < count →
      ∃ hidx : window.length < E.records.length,
        let boundary := E.records[window.length]'hidx
        ReferenceCollectionPhaseHistory.cutoffChosen boundary.input = true ∧
          boundary ∉ window) := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hprefix := run_first_window_prefix_safety initial rows J rewards start count
    hspan active hfirst window rfl
  have hprefix' := hprefix
  have hwindowCount : window.length ≤ count := by
    calc
      window.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
      _ = count := by
        dsimp [E]
        exact ReferenceActivePhysicalHorizon.run_record_count
          initial rows J rewards start count hspan active
  have hspanWindow : start + window.length ≤ p.T := by omega
  have hwindowPrefix := hprefix' window.length le_rfl hspanWindow
  have hrecords := hwindowPrefix.1
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hsafe := hrecords k.val k.isLt
    simpa [window, E, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
      ReferenceFirstComplementMassBudget.firstWindow,
      ReferenceFirstComplementMassBudget.originalRun] using hsafe
  · intro k hk
    have hkcount : k ≤ count := le_trans hk hwindowCount
    have hspanK : start + k ≤ p.T :=
      le_trans (Nat.add_le_add_left hkcount start) hspan
    have hk' : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards start count
          hspan active).length := by
      simpa [window, E, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        ReferenceFirstComplementMassBudget.firstWindow,
        ReferenceFirstComplementMassBudget.originalRun] using hk
    have hprefixK := hprefix' k hk' hspanK
    have hendpointsFirst := hprefixK.2.1
    have hendpointsLive := hprefixK.2.2
    constructor
    · intro hzero
      simpa [window, E, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        ReferenceFirstComplementMassBudget.firstWindow,
        ReferenceFirstComplementMassBudget.originalRun] using hendpointsFirst hzero
    · intro hpositive
      simpa [window, E, ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        ReferenceFirstComplementMassBudget.firstWindow,
        ReferenceFirstComplementMassBudget.originalRun] using hendpointsLive hpositive
  · intro hshort
    have hidx : window.length < E.records.length := by
      have hcount : E.records.length = count := by
        simpa [E] using ReferenceActivePhysicalHorizon.run_record_count
          initial rows J rewards start count hspan active
      rw [hcount]
      exact hshort
    have hidxTake :
        (E.records.takeWhile
          (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.cutoffChosen record.input)).length < E.records.length := by
      simpa [window, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using hidx
    have hpredicate := not_predicate_at_takeWhile_end
      (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen record.input) E.records hidxTake
    refine ⟨hidx, ?_⟩
    let boundary := E.records[window.length]'hidx
    have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen
        boundary.input = true := by
      have hcutoffAtTake : ReferenceCollectionPhaseHistory.cutoffChosen
          (E.records[(E.records.takeWhile
            (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input)).length]'hidxTake).input =
            true := by
        cases hb : ReferenceCollectionPhaseHistory.cutoffChosen
            (E.records[(E.records.takeWhile
              (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input)).length]'hidxTake).input
          <;> simp [hb] at hpredicate ⊢
      exact hcutoffAtTake
    have hboundaryNotMember : boundary ∉ window := by
      intro hmember
      have hmemberTake : boundary ∈ E.records.takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
        simpa [boundary, window, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using hmember
      have htake := List.mem_takeWhile_imp hmemberTake
      change (!ReferenceCollectionPhaseHistory.cutoffChosen boundary.input) = true at htake
      simp [hcutoff] at htake
    exact ⟨hcutoff, hboundaryNotMember⟩

end Bandits.Support.ReferenceFirstLiveCoordinatorSafety
