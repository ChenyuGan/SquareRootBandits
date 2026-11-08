/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedOutsideCutoffNumericalJoin

/-!
# Numerical birth row of an actual empty-collection installation

The corrected and renewal constructors supply the same installation, selection,
recorder, service and FINISH witnesses used by the canonical later-live readout.
This is a current-round result, without an initialized seed or a calendar
coverage assertion.

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
`sources/zip4/manuscript/06_interruptions.tex:40-100,246-299`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.CanonicalFastSampling

namespace Bandits.Support.ReferenceCompleteEmptyInstallationNumericalStep

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- Retain the common actual installation witnesses from the two accepted
empty-collection constructors. Equality belongs to the renewal branch. -/
private theorem empty_installation
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .collection P l saved) (hempty : l.pending = ∅) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := R[k.val]'k.isLt
    let x := r.input
    ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
      let clock := collectionClock P l saved u
      let input := collectionInput x P l clock u
      ∃ (core : CollectionCoreValid input) (started : StartRoundResult p)
        (hstart : startRound p rate.eta.val x.time input.clock l.pending = .ok started)
        (instruction : AssignmentStartInstruction p)
        (hassignment : started.assignmentStart = some instruction),
        instruction.time = x.time ∧
        instruction.kind = (if x.time.val + 1 < l.freezeAt then .corrected else .renewal) ∧
        let operation := collectionOperationLedger input core.payload_n_eq
        ∃ (consistent : LocalConsistency P operation)
          (output : SuccessfulStart P operation instruction x.row)
          (hlocal : output.localConsistency = consistent),
          laterAssignmentStart P operation instruction x.row consistent = .success output hlocal ∧
          ∃ (clockData : LaterStartRoundEvidence output)
            (installation : LaterInstallation output clockData)
            (selected : ArmSelection installation.registers.payload started instruction.time
              installation.registers.complementWeights x.row),
            installation = installLater output clockData ∧
            clockData.result = started ∧
            dispatchCollection input = .laterChosen core consistent started hstart instruction
              hassignment output hlocal clockData installation selected ∧
            r.output.preparation.coordinator = .collection P l clock u
              (.laterChosen core consistent started hstart instruction hassignment output hlocal
                clockData installation selected) ∧
            (if x.time.val + 1 < l.freezeAt then
              installation.registers.payload.anchor = P.anchor else
              installation.registers.payload.anchor =
                AssignmentScoreReconstruction.currentWeight output.reconstruction) ∧
            ∃ v : Selection x,
              r.output.preparation.coordinator.selection = some v ∧
              v.view.payload = installation.registers.payload ∧ v.view.cutoff = none ∧
              CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff x.time := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  let x := r.input
  by_cases hbefore : x.time.val + 1 < l.freezeAt
  · obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, hkind,
      _hsigma, _hu, consistent, output, hlocal, hlater, clockData, installation,
      selected, _hprior, hresult, _hpending, hinstall, hdispatch, _hscore,
      _hqueue, _hprevious, _hbase, _henvelope, hpayload, hanchor, _hlawAnchor,
      _hcutoff, _hcurrent, _hsource, _hinitial, _hqueues, _hvector,
      v, _hprepareSelection, hselection, hvpayload, _hvstarted, hvcutoff,
      _hvarm, hlive, hprepared, _hservice⟩ :=
      ReferenceCompleteEmptyCorrectedCoordinatorStep.complete_empty_corrected_coordinator_step
        (rate := rate) rewards C_star C_h source k P l saved hstate hempty hbefore
    dsimp only [x, r, R] at hbefore
    refine ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
      ?_, consistent, output, hlocal, hlater, clockData, installation, selected,
      hinstall, hresult, hdispatch, hprepared, ?_, v, hselection, hvpayload, hvcutoff, hlive⟩
    · simpa only [ite_eq_left hbefore] using hkind
    · simpa only [ite_eq_left hbefore, hpayload] using hanchor
  · have hfreeze : l.freezeAt ≤ x.time.val + 1 := Nat.le_of_not_gt hbefore
    have hcase :=
      ReferenceCompleteEmptyRenewalCoordinatorStep.complete_empty_renewal_coordinator_step
        rate rewards C_star C_h source k P l saved hstate hempty hfreeze
    dsimp only at hcase
    rcases hcase with ⟨u, hu, core, _hscore, started, hstart, instruction,
      hassignment, htime, hkind, output, hlocal, hlater, _hsource, _hinitial,
      _hweight, hanchor, _hqueues, _hdomains, _hbase, hclock,
      mass, sampled, _hmass, _hsample, _hvector, selected, hdispatch,
      hprepared, v, _hprepareSelection, hvpayload, hvcutoff, hlive,
      hselection, _hservice⟩
    dsimp only [x, r, R] at hbefore
    refine ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
      ?_, _, output, hlocal, hlater, _, _, selected, rfl, rfl, hdispatch,
      ?_, ?_, v, hselection, hvpayload, ?_, hlive⟩
    · simpa only [ite_eq_right hbefore] using hkind
    · have hpreparation : r.output.preparation = prepare x := by
        rw [r.output_eq]
        rfl
      rw [hpreparation]
      exact hprepared.trans (congrArg (DispatchCut.collection P l _ u) hdispatch)
    · rw [ite_eq_right hbefore]
      exact hanchor
    · simpa only [hclock.2.2.1, CoordinatorLiveChoiceRecorderStep.cutoffFromClock, Option.map_none] using hvcutoff

/-- Every actual empty collection installs a canonical enabled numerical row.
The outside transition starts from that installation's own reconstruction and
ends in its actual recorder/service/FINISH output. The follower partition is
raw arrival evidence; it asserts no immediate follower service. -/
theorem complete_empty_installation_current_numerical_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let r := R[k.val]'k.isLt
    let x := r.input
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    match x.state.coordinator with
    | .collection P l saved => l.pending = ∅ →
      ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧
        let clock := collectionClock P l saved u
        let input := collectionInput x P l clock u
        ∃ (core : CollectionCoreValid input) (started : StartRoundResult p)
          (hstart : startRound p rate.eta.val x.time input.clock l.pending = .ok started)
          (instruction : AssignmentStartInstruction p)
          (hassignment : started.assignmentStart = some instruction),
          instruction.time = x.time ∧
          instruction.kind = (if x.time.val + 1 < l.freezeAt then .corrected else .renewal) ∧
          let operation := collectionOperationLedger input core.payload_n_eq
          ∃ (consistent : LocalConsistency P operation)
            (output : SuccessfulStart P operation instruction x.row)
            (hlocal : output.localConsistency = consistent),
            laterAssignmentStart P operation instruction x.row consistent = .success output hlocal ∧
            ∃ (clockData : LaterStartRoundEvidence output)
              (installation : LaterInstallation output clockData)
              (selected : ArmSelection installation.registers.payload started instruction.time
                installation.registers.complementWeights x.row),
              installation = installLater output clockData ∧ clockData.result = started ∧
              dispatchCollection input = .laterChosen core consistent started hstart instruction
                hassignment output hlocal clockData installation selected ∧
              r.output.preparation.coordinator = .collection P l clock u
                (.laterChosen core consistent started hstart instruction hassignment output hlocal
                  clockData installation selected) ∧
              installation.registers.payload = output.payload ∧
              installation.assignmentVector = output.assignmentVector ∧
              output.assignmentVector = ownAssignmentVector x.row x.time ∧
              (∀ i, installation.retainedBaseScore i =
                AssignmentScoreReconstruction.sourceScore output.reconstruction
                  (installation.registers.payload.assignment.assigned i)) ∧
              (∀ arm, installation.registers.payload.queues arm =
                AssignmentScoreReconstruction.initialQueue output.reconstruction arm) ∧
              (if x.time.val + 1 < l.freezeAt then
                installation.registers.payload.anchor = P.anchor else
                installation.registers.payload.anchor =
                  AssignmentScoreReconstruction.currentWeight output.reconstruction) ∧
              ∃ v : Selection x,
                r.output.preparation.coordinator.selection = some v ∧
                v.view.payload = installation.registers.payload ∧ v.view.cutoff = none ∧
                CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff x.time ∧
                s < installation.registers.payload.sigma.val ∧
              ∃ (c : RecordedQueueRun.RoundInput p.K)
                (ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r)
                (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
                ReferenceLaterLiveNumericalReadout.laterLiveReadout s r = some c ∧
                cell.input = c ∧ cell.selected = v ∧
                cell.states = ReferenceLaterLiveNumericalReadout.preparedStates r ho ∧
                cell.memories = ReferenceLaterLiveNumericalReadout.preparedMemories r ho ∧
                (∀ i, (cell.states i).status = .unoccupied) ∧
                c.enabled = true ∧ c.rate = installation.registers.payload.rate ∧
                c.reward = (fun arm => ((rewards x.time arm).val : ℝ) / (D p : ℝ)) ∧
                c.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
                  r v.view.payload true ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                (∀ arm, RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm =
                  if c.recordedArm = some arm then
                    Nat.floor ((D p : ℝ) * rate.eta.val *
                      (((rewards x.time arm).val : ℝ) / (D p : ℝ)) /
                        installation.registers.payload.rate arm) else 0) ∧
                (∀ i, ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
                    r v.view.payload i = RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                        (v.view.payload.assignment.assigned i)) ∧
                (∀ i, (cell.states i).status ≠ .unoccupied →
                  ActiveFollowerQueueOperation.rawArrival rate.eta i x.row x.time
                    (v.view.payload.downRecord i)
                    (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2 =
                      RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
                          (v.view.payload.assignment.assigned i)) ∧
                (∀ arm, ∃! owner : Fin p.m,
                  SnapshotRecordingKernel.owns p (.live v.view.payload.assignment
                    (ReferenceActiveDataOwnership.choiceSnapshot v cell.states)) owner arm) ∧
              ∃ (o : CoordinatorRecordingOperation.Output p)
                (serviced : CoordinatorLiveServiceFinish.ServicedRegisters
                  installation.registers installation.ownedRegisters)
                (pending : Finset (Fin (p.m - 1))) (finished : FinishRoundResult p),
                CoordinatorRecorderComplementBridge.run
                  (liveRecordingInput r.output.preparation installation.registers started) = some o ∧
                r.output.coordinator.recording = some o ∧ serviced.recording = o ∧
                (∀ arm, arm ∉ v.view.payload.slowSet.val →
                  ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                    (ReferenceActiveHorizonMeasurability.roundRecordCode r) arm =
                      some (RecordedQueueRun.quantizedArrival
                        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c arm)) ∧
                (∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
                    (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val ∧
                  (serviced.score j, serviced.queue j) = QueueReplay.transition (4 * rate.n)
                    (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val,
                     AssignmentScoreReconstruction.initialQueue output.reconstruction j.val)
                    (true, RecordedQueueRun.quantizedArrival
                      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val) ∧
                  serviced.previousService j = serviced.score j -
                    AssignmentScoreReconstruction.sourceScore output.reconstruction j.val) ∧
                CoordinatorLocalArmChoice.confirmationUpdate installation.registers.payload
                  started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  x.time x.row r.output.preparation.coordinatorObservation = some pending ∧
                finishRound p rate.eta.val x.time started.clock pending x.row = .ok finished ∧
                livePostChoice r.output.preparation installation.registers installation.ownedRegisters
                  installation.retainedBaseScore started =
                    ⟨.live {
                        payload := installation.registers.payload
                        priorClock := finished.clock
                        pendingAtChoice := finished.pending
                        time := x.time
                        gridBoundary := finished.clock.g
                        complementScores := serviced.score }
                      { queue := serviced.queue, previousService := serviced.previousService }
                      installation.retainedBaseScore,
                      x.state.upDecoderBank, none, some o, none⟩ ∧
                r.output.coordinator = livePostChoice r.output.preparation installation.registers
                  installation.ownedRegisters installation.retainedBaseScore started ∧
                r.output.next.coordinator =
                  (livePostChoice r.output.preparation installation.registers
                    installation.ownedRegisters installation.retainedBaseScore started).configuration ∧
                r.output.next.upDecoderBank = x.state.upDecoderBank
    | .first => x.state.coordinator = .first
    | .live a q base => x.state.coordinator = .live a q base
    | .dagger => x.state.coordinator = .dagger := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]'k.isLt
  let x := r.input
  cases hstate : x.state.coordinator with
  | first => rfl
  | live a q base => rfl
  | dagger => rfl
  | collection P l saved =>
    dsimp only
    intro hempty
    obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
      hkind, consistent, output, hlocal, hlater, clockData, installation,
      selected, hinstall, hresult, hdispatch, hprepared, hanchor,
      v, hselection, hvpayload, hvcutoff, hlive⟩ :=
      empty_installation rewards C_star C_h source k P l saved hstate hempty
    subst installation
    let installation := installLater output clockData
    have hinstall : installation = installLater output clockData := rfl
    change r.output.preparation.coordinator.selection = some v at hselection
    change instruction.time = x.time at htime
    have hpayload : installation.registers.payload = output.payload := by
      rw [hinstall]
      rfl
    have hvector : installation.assignmentVector = output.assignmentVector := by
      rw [hinstall]
      rfl
    have hbase : ∀ i, installation.retainedBaseScore i =
        AssignmentScoreReconstruction.sourceScore output.reconstruction
          (installation.registers.payload.assignment.assigned i) := by
      intro i
      exact output.baseScore_eq_source i
    have hqueues : ∀ arm, installation.registers.payload.queues arm =
        AssignmentScoreReconstruction.initialQueue output.reconstruction arm := by
      simpa only [hpayload] using output.payload_queues
    have hlookup : R[k.val]? = some r := List.getElem?_eq_getElem k.isLt
    have hindex := ReferenceFirstCollectionCurrentNumericalCell.collection_after_firstLive
      (rate := rate) rewards C_star C_h source k.val r hlookup P l saved hstate
    have htimeValue := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate source rewards C_star C_h k.val r hlookup
    have hstrict : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
        installation.registers.payload.sigma.val := by
      rw [hpayload, output.payload_start, htime]
      change ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
        r.input.time.val
      omega
    obtain ⟨states, memories, hord, _hfields⟩ :=
      ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
        (rate := rate) rewards C_star C_h source k v hselection
    have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary r := by
      intro i
      change (ReferenceLaterLiveNumericalReadout.ordinaryData
        (ReferenceFollowerFixedReply.actualChoice r i).configuration).isSome = true
      rw [hord i]
      rfl
    let c := ReferenceFirstWindowNumericalStream.sourceCell r v.view.payload
      v.view.pendingAtChoice (ReferenceLaterLiveNumericalReadout.preparedStates r ho)
      v.view.complementWeights v.view.cutoff
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)
    have hreadout : ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r = some c := by
      unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
      rw [hselection]
      dsimp only
      have hdomain : ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h < v.view.payload.sigma.val ∧
          CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff r.input.time :=
        ⟨by simpa only [hvpayload] using hstrict, hlive⟩
      rw [ite_eq_left hdomain, dite_eq_left ho]
    have hphysical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
      rate rewards C_star C_h source k c hreadout
    simp only [List.get_eq_getElem] at hphysical
    obtain ⟨cell, hcell, henabled, _hliveCall, _henabledCall, hrows, hselected,
      hrewards, hmarker, _hoccupiedFields, _howner, hoccupied, hunoccupied,
      _hlogging, hraw, hunoccupiedAll⟩ := hphysical
    have hcellSelected : cell.selected = v :=
      Option.some.inj (cell.selection_actual.symm.trans hselection)
    have hstates : cell.states = ReferenceLaterLiveNumericalReadout.preparedStates r ho := by
      funext i
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        ((cell.ordinary i).symm.trans
          (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i))).1
    have hmemories : cell.memories = ReferenceLaterLiveNumericalReadout.preparedMemories r ho := by
      funext i
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        ((cell.ordinary i).symm.trans
          (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i))).2
    have hunoccupiedAll' : ∀ i, (cell.states i).status = .unoccupied := by
      rw [hprepared] at hunoccupiedAll
      exact hunoccupiedAll
    obtain ⟨_, v', hselection', hreward, hrate, hfloor⟩ :=
      ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical _ r c hreadout
    have hv' : v' = v := Option.some.inj (hselection'.symm.trans hselection)
    subst v'
    change r.input.rewards = rewards at hrewards
    rw [hrewards] at hreward hfloor
    have hall : ∀ arm, ∃! owner : Fin p.m,
        SnapshotRecordingKernel.owns p (.live v.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot v cell.states)) owner arm := by
      intro arm
      have hpartitionAll := ReferenceLaterLiveNumericalReadout.laterLiveReadout_all_arm_numerical
        rate rewards C_star C_h source k c hreadout arm
      simp only [List.get_eq_getElem] at hpartitionAll
      obtain ⟨other, _hinput, howners, _hpartition⟩ := hpartitionAll
      have hotherSelected : other.selected = v :=
        Option.some.inj (other.selection_actual.symm.trans hselection)
      have hotherStates : other.states = cell.states := by
        funext i
        exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          ((other.ordinary i).symm.trans (cell.ordinary i))).1
      rw [hotherSelected, hotherStates] at howners
      exact howners
    obtain ⟨a, owned, base, liveStarted, hmatch, valid, o, serviced, pending,
      finished, _hrun, hrecord, _hgate, _hraw, _hdiagnostic, _hcall,
      hbridge, _hqueueDomain, _hpreviousDomain, hserviceRecord, harrival,
      _hservice, _hresidual, _hscore, _hprevious, hconfirmation, _hpending,
      hfinish, hpost, hout, hnext, hup⟩ :=
      ReferenceCompleteSelectedLiveCoordinatorServiceFinish.complete_selected_live_coordinator_service_finish
        (rate := rate) rewards C_star C_h source k v hselection hlive
    rw [hprepared] at hmatch
    rcases hmatch with ⟨ha, howned, hbase', hstarted⟩
    subst a
    have howned' := eq_of_heq howned
    subst owned
    subst base
    subst liveStarted
    obtain ⟨_physicalRecording, _hphysicalRecording, hrawAll⟩ := hraw
    have harrivals : ∀ j, serviced.arrival j = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c j.val := by
      intro j
      have hfast : j.val ∉ cell.selected.view.payload.slowSet.val := by
        rw [hcellSelected, hvpayload]
        exact (Finset.mem_sdiff.mp j.property).2
      have hrawCanonical := hrawAll j.val hfast
      have hrecording : ReferenceCoordinatorRecorderCallTrace.recording
          (ReferenceActiveHorizonMeasurability.roundRecordCode r) = some o := by
        rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
        exact hrecord
      unfold ReferenceCoordinatorRecorderCallTrace.coordinatorRaw at hrawCanonical
      rw [hrecording, Option.map_some] at hrawCanonical
      rw [harrival j, CoordinatorLiveServiceFinish.complementArrival]
      exact Option.some.inj hrawCanonical
    refine ⟨u, hu, core, started, hstart, instruction, hassignment, htime,
      hkind, consistent, output, hlocal, hlater, clockData, installation,
      selected, hinstall, hresult, hdispatch, hprepared, hpayload, hvector,
      ?_, hbase, hqueues, hanchor, v, hselection, hvpayload, hvcutoff,
      hlive, hstrict, c, ho, cell, hreadout, hcell, hcellSelected, hstates,
      hmemories, hunoccupiedAll', henabled, ?_, ?_, ?_, hrows, hselected,
      hrewards, ?_, ?_, ?_, hall, o, serviced, pending, finished,
      hbridge, hrecord, hserviceRecord, ?_, ?_, hconfirmation, hfinish,
      hpost, ?_, hnext, ?_⟩
    · simpa only [htime] using output.assignmentVector_eq_row_projection
    · simpa only [hvpayload] using hrate
    · exact hreward
    · simpa only [hcellSelected] using hmarker
    · simpa only [hvpayload] using hfloor
    · intro i
      simpa only [hcellSelected] using hunoccupied i (hunoccupiedAll' i)
    · intro i hi
      simpa only [hcellSelected] using (hoccupied i hi).2
    · simpa only [hcellSelected] using hrawAll
    · intro j
      refine ⟨harrivals j, ?_, ?_⟩
      · have htransition := CoordinatorLiveServiceFinish.serviced_queueReplay_transition
          installation.registers installation.ownedRegisters serviced j
        rw [ReferenceActivePhysicalStep.payload_n_eq, harrivals] at htransition
        exact htransition.symm
      · rw [serviced.score_eq j, serviced.previousService_eq j]
        have hsource : installation.registers.complementScores j =
            AssignmentScoreReconstruction.sourceScore output.reconstruction j.val := by
          rfl
        rw [hsource, Nat.add_sub_cancel_left]
    · exact hout.trans hpost.symm
    · rw [hup, hpost]

end Bandits.Support.ReferenceCompleteEmptyInstallationNumericalStep

end
