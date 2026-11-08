/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedRetainedCollectionStaleWordCut
public import Bandits.Support.ReferenceLaterStartUnoccupiedChoice

import Lean.Elab.Tactic.Omega

/-!
# Actual follower state at a generated assignment installation

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/05_binary_transport.tex:60-88,100-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,246-295,303-348`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The exported initializer identifies the actual incoming follower state at a
generated installation. Later collection births retain the follower's actual
reply fields, decoder bank, buffer, initialization-failure flag, and local
memory through PREPARE. The separate live erasure induction and stale-word
exclusion remain downstream work.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness
open ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceGeneratedInstallationFollowerSeed

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem generatedSeed_source_facts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs) :
    let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
      rate rewards C_star C_h s hs x
    ReferenceActivePhysicalHorizon.allActiveAtStart seed s ∧
      seed.coordinator = .first ∧
      ReferenceFollowerDecoderChronology.downBatchSeed seed s ∧
      ∀ i : Fin (p.m - 1), ∃ sourceState sourceMemory,
        seed.followers i = .ordinary sourceState sourceMemory ∧
        sourceState.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart sourceState = 0 ∧
        sourceState.S = 0 ∧ sourceState.delta = 0 ∧ sourceState.backlog = 0 ∧
        sourceState.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid sourceState ∧
        sourceMemory = ActiveFollowerLifecycle.initialMemory p := by
  classical
  dsimp only
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed_spec
    rate rewards C_star C_h s hs x
  obtain ⟨active, hactive, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have hseedActive : seed = active :=
    Option.some.inj (hseed.1.symm.trans hactive.1)
  obtain ⟨activeFields, hfieldsLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.val rewards C_star C_h x.property.1
  have hseedFields : seed = activeFields :=
    Option.some.inj (hseed.1.symm.trans hfieldsLaunch)
  have hfirst : seed.coordinator = .first := by
    rw [hseedActive]
    exact hactive.2.1
  refine ⟨hseed.2.1, hfirst, hseed.2.2, ?_⟩
  intro i
  rcases hfields i with
    ⟨hconfiguration, hlastDown, hstart, hscore, hdelta, hbacklog,
      hunoccupied, hdomain⟩
  refine ⟨ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower i),
    ActiveFollowerLifecycle.initialMemory p, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, rfl⟩
  · change seed.followers i = _
    rw [hseedFields]
    exact hconfiguration
  · exact hlastDown
  · exact hstart
  · exact hscore
  · exact hdelta
  · exact hbacklog
  · exact hunoccupied
  · exact hdomain

private theorem generatedRecord_input_eq_nextInput
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) :
    (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
      rate rewards C_star C_h s hs x n).input =
    ReferenceCollectionPhaseHistory.nextInput
      (ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
        rate rewards C_star C_h s hs x)
      x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards s n.val
      (by omega)
      (generatedSeed_source_facts rate rewards C_star C_h s hs x).1 := by
  classical
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  have hseed := generatedSeed_source_facts rate rewards C_star C_h s hs x
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseed.1
  let rows := x.val.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  let total := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
    (p.T - s) (by omega) hmode
  let prefixRun := ReferenceActivePhysicalHorizon.run seed rows selected rewards s n.val
    (by omega) hmode
  let through := ReferenceActivePhysicalHorizon.run seed rows selected rewards s (n.val + 1)
    (by omega) hmode
  have hgenerated : ReferenceGeneratedDownBatchCalendar.generatedSourceRun
      rate rewards C_star C_h s hs x = total := rfl
  have htotalCount : total.records.length = p.T - s :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s
      (p.T - s) (by omega) hmode
  have hrecord (j : Fin (p.T - s)) :
      total.records[j.val]'(by omega) =
        ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x j := by
    have hget := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt_getElem?
      rate rewards C_star C_h s hs x j
    rw [hgenerated,
      List.getElem?_eq_getElem (by rw [htotalCount]; exact j.isLt)] at hget
    exact Option.some.inj hget
  obtain ⟨suffix, hrecords⟩ :=
    ReferenceCollectionPhaseHistory.run_records_prefix seed rows selected rewards s
      (n.val + 1) (p.T - s - (n.val + 1)) (by omega) hmode
  have hrecordsTotal : total.records = through.records ++ suffix := by
    simpa [total, through, hgenerated] using hrecords
  have hthroughSuccessor : through.records = prefixRun.records ++
      [ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode] := by
      simpa only [through, prefixRun] using
      ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt seed rows selected
        rewards s n.val (by omega) hmode
  have hprefixCount : prefixRun.records.length = n.val :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s n.val
      (by omega) hmode
  have hthroughCount : through.records.length = n.val + 1 :=
    ReferenceActivePhysicalHorizon.run_record_count seed rows selected rewards s (n.val + 1)
      (by omega) hmode
  have hcalendarRecord? : total.records[n.val]? =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode) := by
    rw [hrecordsTotal]
    rw [List.getElem?_append_left (by rw [hthroughCount]; omega)]
    rw [hthroughSuccessor]
    rw [List.getElem?_append_right (by omega)]
    simp [hprefixCount]
  have hgeneratedRecord? : total.records[n.val]? = some
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) := by
    rw [List.getElem?_eq_getElem (by rw [htotalCount]; exact n.isLt)]
    rw [hrecord n]
  have hcalendarRecord := Option.some.inj (hcalendarRecord?.symm.trans hgeneratedRecord?)
  have hrecordIdentity := hcalendarRecord
  have hinput :
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).input =
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode).input := by
    exact congrArg (fun record : Record => record.input) hrecordIdentity.symm
  calc
    _ = (ReferenceAssignmentPayloadChronology.actualRunRecordAt seed rows selected rewards s n.val
        (by omega) hmode).input := hinput
    _ = ReferenceCollectionPhaseHistory.nextInput seed rows selected rewards s n.val
        (by omega) hmode := rfl

private theorem livePostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason =>
                  simp [hservice, hfinish, ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem collectionPostChoice_configuration_ne_first
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice
      prepared payload ledger started weights).configuration ≠ .first := by
  rcases ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
      prepared payload ledger started weights with hd | ⟨nextPayload, nextLedger, proposal, h⟩
  · rw [hd]
    exact fun hfirst => by cases hfirst
  · rw [h]
    exact fun hfirst => by cases hfirst

private theorem step_coordinator_ne_first
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.step x).next.coordinator ≠ .first := by
  rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
  cases hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator with
  | dagger =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord]
  | first outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_first_equation
        (ReferenceActivePhysicalStep.prepare x) outcome hcoord
      by_cases hnone : (ReferenceActivePhysicalStep.DispatchCut.first outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | chosen installed choice =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.followerBaseScore installed.startRoundResult
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | live registers owned base outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_live_equation
        (ReferenceActivePhysicalStep.prepare x) registers owned base outcome hcoord
      by_cases hnone :
          (ReferenceActivePhysicalStep.DispatchCut.live registers owned base outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuingChosen dispatched _ _ _ =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x)
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
              (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base
              dispatched.startResult
        | cutoffChosen dispatched _ ledger _ _ _ _ _ _ _ =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) registers.payload
              (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | collection payload ledger clock cutoff outcome =>
      have hobserve := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcoord
      by_cases hnone :
          (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff outcome).selection = none
      · rw [hobserve, ite_eq_left hnone]
        simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · rw [hobserve, ite_eq_right hnone]
        cases outcome with
        | continuing _ snapshot _ _ =>
            exact collectionPostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
        | laterChosen _ _ started _ _ _ _ _ _ installed _ =>
            exact livePostChoice_configuration_ne_first
              (ReferenceActivePhysicalStep.prepare x) installed.registers installed.ownedRegisters
              installed.retainedBaseScore started
        | _ => simp [ReferenceActivePhysicalStep.DispatchCut.selection] at hnone
  | invalidCollectionCutoff =>
      simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.DispatchCut.selection, hcoord,
        ReferenceActivePhysicalStep.coordinatorFailure]

private theorem input_coordinator_first_of_prepared_first
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome
      (ReferenceActivePhysicalStep.firstInput x))
    (hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator = .first outcome) :
    x.state.coordinator = .first := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x = .first outcome := by
    calc
      ReferenceActivePhysicalStep.dispatch x = (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .first outcome := hprepared
  cases hstate : x.state.coordinator with
  | first => rfl
  | live registers owned base =>
      cases hrun : CoordinatorRoundDispatch.dispatch
          (.live (ReferenceActivePhysicalStep.liveInput x registers owned base)) with
      | live actual =>
          have hcut : ReferenceActivePhysicalStep.dispatch x =
              .live registers owned base actual := by
            simp [ReferenceActivePhysicalStep.dispatch, hstate, hrun]
            rfl
          rw [hcut] at hdispatch
          cases hdispatch
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hrun : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) with
        | collection actual =>
            have hcut : ReferenceActivePhysicalStep.dispatch x =
                .collection payload ledger clock cutoff actual := by
              simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid, cutoff, clock, hrun]
              rfl
            rw [hcut] at hdispatch
            cases hdispatch
      · have hcut : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hvalid]
        rw [hcut] at hdispatch
        cases hdispatch
  | dagger =>
      have hcut : ReferenceActivePhysicalStep.dispatch x = .dagger := by
        simp [ReferenceActivePhysicalStep.dispatch, hstate]
      rw [hcut] at hdispatch
      cases hdispatch

private theorem run_final_coordinator_first_only
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.coordinator = .first) :
    count = 0 := by
  cases count with
  | zero => rfl
  | succ count =>
      have hlast := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows selected rewards start count (by omega) hmode
      have hne : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
          start (count + 1) (by omega) hmode).finalState.coordinator ≠ .first := by
        rw [hlast]
        exact step_coordinator_ne_first
          (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards
            start count (by omega) hmode).input
      exact False.elim (hne hfirst)

private theorem actualChoice_prepare_frame
    (record : Record (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice record i).configuration =
      .ordinary state memory) :
    ∃ before beforeMemory,
      record.input.state.followers i = .ordinary before beforeMemory ∧
      ReferenceFollowerReplyChronology.reply state =
        ReferenceFollowerReplyChronology.reply before ∧
      state.downBatch = before.downBatch ∧ state.buffer = before.buffer ∧
      state.initializationFailure = before.initializationFailure ∧
      (before.status = .unoccupied → state.status = .unoccupied) ∧
      memory = beforeMemory := by
  have hactualChoice : ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) :=
    record.output.preparation.followers.followers_eq i
  rw [hactualChoice] at hc
  obtain ⟨before, beforeMemory, hinput, hstart, hreply, hunoccupied⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i) state memory hc
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time
    before state beforeMemory memory hstart
  exact ⟨before, beforeMemory, hinput, hreply,
    hframe.2.2.2.2.1, hframe.2.2.2.2.2.1,
    hframe.2.2.2.2.2.2.1, hunoccupied, hframe.2.2.2.2.2.2.2⟩

/-- At the actual generated DOWN installation, an ordinary focal choice is
unoccupied and is framed by its real pre-PREPARE state. The first chosen
installation is tied to the canonical initial `.first` boundary; a later
chosen installation uses the actual collection prefix. The incoming partial
decoder bank, buffer, reply registers, initialization flag, and local memory
are preserved exactly by `startRound`.
-/
theorem generated_installation_choice_unoccupied
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : ReferenceGeneratedDownBatchCalendar.LaunchSource rate rewards C_star C_h s hs)
    (i : Fin (p.m - 1)) (n : Fin (p.T - s))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) payload)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n) i).configuration = .ordinary state memory) :
    state.status = .unoccupied ∧
      ∃ before beforeMemory,
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x n).input.state.followers i =
            .ordinary before beforeMemory ∧
        before.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state =
          ReferenceFollowerReplyChronology.reply before ∧
        state.downBatch = before.downBatch ∧
        state.buffer = before.buffer ∧
        state.initializationFailure = before.initializationFailure ∧
        memory = beforeMemory ∧
      payload.sigma.val =
        (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
          rate rewards C_star C_h s hs x n).input.time.val ∧
      (ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
        rate rewards C_star C_h s hs x n).input.time.val = s + n.val ∧
      s + n.val < p.T := by
  classical
  let seed := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed
    rate rewards C_star C_h s hs x
  let rows := x.val.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p x.val
  have hseed := generatedSeed_source_facts rate rewards C_star C_h s hs x
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart seed s := hseed.1
  let xn := ReferenceCollectionPhaseHistory.nextInput seed rows selected rewards s n.val
    (by omega) hmode
  let record := ReferenceGeneratedInheritedDownWrongCompletionWitness.generatedSourceRecordAt
    rate rewards C_star C_h s hs x n
  change ReferenceAssignmentPayloadPersistence.InstallationBirth record payload at hbirth
  have hrecordInput : record.input = xn := by
    simpa only [seed, rows, selected] using
      generatedRecord_input_eq_nextInput rate rewards C_star C_h s hs x n
  have htime : record.input.time.val = s + n.val := by
    rw [hrecordInput]
    rfl
  have htime_lt : s + n.val < p.T := by omega
  have hbirthTime :=
    ReferenceAssignmentPayloadChronology.installationBirth_time_eq record payload hbirth
  have hframe := actualChoice_prepare_frame record i state memory hc
  rcases hframe with
    ⟨before, beforeMemory, hbeforeInput, hreply, hbank, hbuffer, hfailure,
      hstatusFrame, hmemory⟩
  have hbeforeInputNext : xn.state.followers i = .ordinary before beforeMemory := by
    rw [← hrecordInput]
    exact hbeforeInput
  have hstatuses : before.status = .unoccupied ∧ state.status = .unoccupied := by
    cases hprep : record.output.preparation.coordinator with
    | first outcome =>
        unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
        rw [hprep] at hbirth
        cases outcome with
        | chosen installed choice =>
            simp at hbirth
            have hprepInput :
                (ReferenceActivePhysicalStep.prepare record.input).coordinator =
                  .first (.chosen installed choice) := by
              change (ReferenceActivePhysicalStep.step record.input).preparation.coordinator = _
              rw [← record.output_eq]
              exact hprep
            have hinputFirst := input_coordinator_first_of_prepared_first record.input
              (.chosen installed choice) hprepInput
            have hinputFirstNext : xn.state.coordinator = .first := by
              rw [← hrecordInput]
              exact hinputFirst
            have hprefixFirst :
                (ReferenceActivePhysicalHorizon.run seed rows selected rewards s n.val
                  (by omega) hmode).finalState.coordinator = .first := by
              change xn.state.coordinator = .first
              exact hinputFirstNext
            have hnzero := run_final_coordinator_first_only seed rows selected rewards s n.val
              (by omega) hmode hprefixFirst
            have hnval : n.val = 0 := hnzero
            have hrecordState : record.input.state = seed := by
              rw [hrecordInput]
              change (ReferenceActivePhysicalHorizon.run seed rows selected rewards s n.val
                (by omega) hmode).finalState = seed
              simpa [hnval] using ReferenceActivePhysicalHorizon.run_zero_final seed rows
                selected rewards s (by omega) hmode
            obtain ⟨seedState, seedMemory, hseedFollower, _, _, _, _, _, hseedStatus,
              _, _⟩ := hseed.2.2.2 i
            have hbeforeEq : (before, beforeMemory) = (seedState, seedMemory) := by
              have hleft : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                    before beforeMemory =
                  DeclaredFollowerLocalRound.LocalConfiguration.ordinary seedState seedMemory := by
                have hstateInput := hbeforeInput
                rw [hrecordState] at hstateInput
                exact hstateInput.symm.trans hseedFollower
              cases hleft
              rfl
            rcases hbeforeEq with ⟨rfl, rfl⟩
            exact ⟨hseedStatus, hstatusFrame hseedStatus⟩
        | _ =>
            simp at hbirth
    | collection oldPayload ledger clock cutoff outcome =>
        unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
        rw [hprep] at hbirth
        cases outcome with
        | laterChosen core consistent started startRound_eq instruction assignmentStart_eq output
            localConsistency_eq clockData installation selection =>
            simp at hbirth
            have hprepInput :
                (ReferenceActivePhysicalStep.prepare record.input).coordinator =
                  .collection oldPayload ledger clock cutoff
                    (.laterChosen core consistent started startRound_eq instruction assignmentStart_eq
                      output localConsistency_eq clockData installation selection) := by
              change (ReferenceActivePhysicalStep.step record.input).preparation.coordinator = _
              rw [← record.output_eq]
              exact hprep
            have hlaterRecord : ReferenceCollectionPhaseHistory.laterChosen record.input = true := by
              unfold ReferenceCollectionPhaseHistory.laterChosen
              rw [hprepInput]
            have hlater : ReferenceCollectionPhaseHistory.laterChosen xn = true := by
              rw [← hrecordInput]
              exact hlaterRecord
            have hbeforeStatus :=
              ReferenceLaterStartUnoccupiedChoice.run_laterChosen_ordinary_input_unoccupied
                seed rows selected rewards s n.val (by omega) hmode hseed.2.1 hlater i
                before beforeMemory hbeforeInputNext
            exact ⟨hbeforeStatus, hstatusFrame hbeforeStatus⟩
        | _ =>
            simp at hbirth
    | live _ _ _ outcome =>
        unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
        rw [hprep] at hbirth
        simp at hbirth
    | invalidCollectionCutoff =>
        unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
        rw [hprep] at hbirth
        simp at hbirth
    | dagger =>
        unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
        rw [hprep] at hbirth
        simp at hbirth
  have hstateStatus : state.status = .unoccupied := by
    exact hstatuses.2
  exact ⟨hstateStatus, before, beforeMemory, hbeforeInput, hstatuses.1,
    hreply, hbank, hbuffer, hfailure,
    hmemory, hbirthTime, htime, htime_lt⟩

end Bandits.Support.ReferenceGeneratedInstallationFollowerSeed

end
