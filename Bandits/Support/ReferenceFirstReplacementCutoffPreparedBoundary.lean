/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementFollowerBoundary

import Lean.Elab.Tactic.Omega

/-!
# Follower preparation at the first replacement cutoff

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,246-295` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module proves the actual next cutoff PREPARE transition while preserving
the installed payload, source row, follower DOWN records, buffers, and memory.
Its selectors are conditional and assert nothing after PREPARE.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception PublicDiscreteDraws
open ReferenceFirstReplacementLiveFollowerPrefix ReferenceFirstReplacementNextFollowerStep
variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}


private theorem complete_record_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k.val ∧
    r.input.rows = source.1.2 ∧
    r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    r.input.rewards = rewards := by
  obtain ⟨_, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  rw [hr]
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem complete_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (k : ℕ) (hk : k + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    (R.get ⟨k + 1, hk⟩).input.state =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).output.next ∧
    (R.get ⟨k + 1, hk⟩).input.time.val =
      (R.get ⟨k, (Nat.lt_succ_self k).trans hk⟩).input.time.val + 1 := by
  dsimp only
  obtain ⟨_, _, hr0⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k, by omega⟩
  obtain ⟨_, _, hr1⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨k + 1, hk⟩
  rw [hr0, hr1]
  exact ⟨ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    _ source.1.2 _ rewards _ k _ _, rfl⟩

private theorem stateInputDomain_of_localStateDomainValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state := by
  rcases h with ⟨⟨hS, hdelta, hbacklog⟩, hbuffer, _⟩
  have htimestamps := ActiveFollowerLifecycle.localBufferValid_timestamp hbuffer
  have hkeys := ActiveFollowerLifecycle.localBufferValid_keys_nodup hbuffer
  change state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p ∧
    (∀ record ∈ state.buffer, 1 ≤ record.calendarRound ∧
      record.calendarRound ≤ p.T) ∧
    (state.buffer.map ActiveFollowerQueueOperation.bufferKey).Nodup
  exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩

private theorem up_admissible_of_localStateDomainValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state)
    (hzero : state.lastDown = none → state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) :
    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
  cases hlast : state.lastDown with
  | none =>
      obtain ⟨hS, hdelta, hbacklog⟩ := hzero hlast
      simp [OrdinaryMessageCodec.upAdmissible,
        OrdinaryMessageCodec.upPlaceholder,
        ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast, hS, hdelta, hbacklog]
  | some M =>
      have hM := M.property
      change 1 ≤ M.val.sigma ∧ M.val.sigma ≤ p.T ∧
        1 ≤ M.val.a ∧ M.val.a ≤ p.K ∧ 1 ≤ M.val.e ∧ M.val.e ≤ p.K ∧
        M.val.a ≠ M.val.e ∧ M.val.h ≤ (ReferencePrelaunchFollower.codecParams p rate.eta).bN ∧
        (ReferencePrelaunchFollower.codecParams p rate.eta).beta ≤ OrdinaryMessageCodec.dyadicRate M.val.h ∧
        OrdinaryMessageCodec.dyadicRate M.val.h ≤
          1 / ((16 : ℝ) * (p.m : ℝ) * (p.K : ℝ)) ∧
        M.val.q ≤ p.T * D p at hM
      unfold OrdinaryMessageCodec.upAdmissible ActiveFollowerQueueOperation.upOfferFields
      simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
      exact Or.inr ⟨hM.1, hM.2.1, h.1.1, h.1.2.1,
        h.1.2.2⟩

private theorem prepare_configuration_of_unoccupied_start
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (old choiceState : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hstatus : choiceState.status = .unoccupied)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta t old memory =
      .ok (choiceState, choiceMemory))
    (hinput : ActiveFollowerQueueOperation.stateInputDomain choiceState)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields choiceState)) :
    (DeclaredFollowerLocalRound.prepare rate i row activation t active
      (.ordinary old memory)).configuration = .ordinary choiceState choiceMemory := by
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields choiceState, hadmissible⟩
  by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t
  · have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
        choiceState = .offer offered := by
      unfold ActiveFollowerQueueOperation.checkedUpOffer
      rw [dite_eq_left hinput, dite_eq_left ⟨hselected, hstatus⟩, dite_eq_left hadmissible]
    have hvalid : ActiveFollowerArmChoice.upStateDomain choiceState ∧
        ActiveFollowerArmChoice.offeredUpMatchesState choiceState offered := by
      constructor
      · exact ⟨hinput.1, hinput.2.1, hinput.2.2.1⟩
      · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
          ActiveFollowerQueueOperation.upOfferFields]
    rcases hselected with ⟨_, hslot, hdraw⟩
    have hchoiceCore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      choiceState (row.2 t) i offered hstatus hslot hdraw hvalid
    have hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i
        (some offered) = some (ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 t) i offered)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (ActiveRoundActions.coordinator p.two_le_m))) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hchoiceCore
    simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice, offered]
  · have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer
      rate.eta i row activation t choiceState hinput (fun h => hselected h.1)
    by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 t).1 =
        PublicDiscreteDraws.dataSlot
    · have hchoiceCore :=
        ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
          choiceState (row.2 t) i none hstatus hdata
      have hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i none =
          some (PublicDiscreteDraws.pilotDraw (K_pos p)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 t).1) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hchoiceCore
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
    · have hup : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 =
          PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (row.2 t).1 = i) := by
        intro h
        exact hselected ⟨active, h.1, h.2⟩
      have hchoiceCore :=
        ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
          choiceState (row.2 t) i none hstatus hdata hup
      have hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i none =
          some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hchoiceCore
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

private theorem takeWhile_endpoint_false {α : Type}
    (predicate : α → Bool) (xs : List α) (n : ℕ) (item : α)
    (hget : xs[n]? = some item)
    (hlen : (xs.takeWhile predicate).length = n) : predicate item = false := by
  induction xs generalizing n with
  | nil => simp at hget
  | cons head tail ih =>
      by_cases hhead : predicate head
      · cases n with
        | zero => simp [List.takeWhile, hhead] at hlen
        | succ n =>
            have htailGet : tail[n]? = some item := by simpa using hget
            have htailLength : (tail.takeWhile predicate).length = n := by
              simpa [List.takeWhile, hhead] using hlen
            exact ih n htailGet htailLength
      · cases n with
        | zero =>
            have hitem : head = item := by simpa using hget
            have hfalse : predicate head = false := by
              cases hpred : predicate head with
              | false => rfl
              | true => exact (hhead hpred).elim
            simpa [hitem] using hfalse
        | succ n =>
            simp [List.takeWhile, hhead] at hlen

private theorem continuing_not_installation_birth
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcontinuing : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen record = true)
    (payload : ReferenceActivePhysicalStep.Payload rate) :
    ¬ ReferenceAssignmentPayloadPersistence.InstallationBirth record payload := by
  cases hcoord : record.output.preparation.coordinator with
  | first firstOutcome =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hcontinuing
  | collection payload ledger clock cutoff outcome =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hcontinuing
  | invalidCollectionCutoff =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hcontinuing
  | live registers owned base outcome =>
      cases outcome <;>
        simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen,
          ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hcontinuing ⊢
  | dagger =>
      simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hcontinuing

private theorem selected_payload_continues_to_successor
    (previous current : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : current.input.state = previous.output.next)
    (hprevious : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen previous = true)
    (hcurrent : ¬ ∃ payload, ReferenceAssignmentPayloadPersistence.InstallationBirth current payload)
    (left : ReferenceActivePhysicalStep.Selection previous.input)
    (right : ReferenceActivePhysicalStep.Selection current.input)
    (hleft : previous.output.preparation.coordinator.selection = some left)
    (hright : current.output.preparation.coordinator.selection = some right) :
    right.view.payload = left.view.payload := by
  have hstoredLeft := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
    previous left hleft
  rcases hstoredLeft with hstoredLeft | hbirthLeft
  · have hstoredRight := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
      current right hright
    rcases hstoredRight with hstoredRight | hbirthRight
    · have hrecord : ReferenceAssignmentPayloadChronology.actualStepRecord previous.input =
          previous := by
        cases previous with
        | mk input output houtput => cases houtput; rfl
      have hclassification := ReferenceAssignmentPayloadChronology.actualStep_payload_classification
        previous.input
      rw [← previous.output_eq, hrecord] at hclassification
      rw [hstate] at hstoredRight
      rcases hclassification with hnone | ⟨old, hinput, houtput⟩ |
        ⟨fresh, hbirth, hstoredFresh⟩
      · rw [hnone] at hstoredRight
        cases hstoredRight
      · exact (Option.some.inj (hstoredRight.symm.trans houtput)).trans
          (Option.some.inj (hinput.symm.trans hstoredLeft))
      · exact (continuing_not_installation_birth previous hprevious fresh hbirth).elim
    · exact (hcurrent ⟨right.view.payload, hbirthRight⟩).elim
  · exact (continuing_not_installation_birth previous hprevious left.view.payload hbirthLeft).elim

private theorem dispatch_live_origin
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    match ReferenceActivePhysicalStep.dispatch x with
    | .live registers owned base _ => x.state.coordinator = .live registers owned base
    | _ => True := by
  unfold ReferenceActivePhysicalStep.dispatch
  cases x.state.coordinator with
  | first => trivial
  | live registers owned base =>
      simp only [CoordinatorRoundDispatch.dispatch]
      cases CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x registers owned base) <;> rfl
  | collection payload ledger saved =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_left hcutoff]
        cases CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved
              ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩) <;> trivial
      · simp only [CoordinatorRoundDispatch.dispatch, dite_eq_right hcutoff]
  | dagger => trivial

private theorem startRound_initializeAt_detectCutoff
    (eta : ℝ) (time : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (result : CoordinatorPhaseClock.StartRoundResult p)
    (hparam : CoordinatorPhaseClock.proposalParameterValid p eta)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p eta clock)
    (htime : CoordinatorPhaseClock.startRoundTimeValid p time clock)
    (hstart : CoordinatorPhaseClock.startRound p eta time clock pending = .ok result)
    (hcommand : result.ledgerCommand = some (.initializeAt time)) :
    ∃ sigma : Fin p.T, ∃ hsigma : clock.sigma = some sigma,
      CoordinatorPhaseClock.detectCutoff clock time = .ok (.cutoff sigma hsigma) := by
  classical
  cases hdetect : CoordinatorPhaseClock.detectCutoff clock time with
  | error failure =>
      simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime, hdetect] at hstart
  | ok decision =>
      cases decision with
      | cutoff sigma hsigma => exact ⟨sigma, hsigma, rfl⟩
      | noCutoff =>
          by_cases hsource : CoordinatorPhaseClock.sourceStartTest
              clock.sigma clock.u time pending
          · by_cases hgrid : CoordinatorPhaseClock.newGridBoundaryValid p time
                (FollowerCutoffScan.gridBoundary p eta time)
            · simp only [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
                hdetect, hsource, hgrid] at hstart
              have hcmd := congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand
                (Except.ok.inj hstart)
              simp [hcommand] at hcmd
            · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
                hdetect, hsource, hgrid] at hstart
          · simp only [CoordinatorPhaseClock.startRound, hparam, hclock, htime,
              hdetect, hsource] at hstart
            have hcmd := congrArg CoordinatorPhaseClock.StartRoundResult.ledgerCommand
              (Except.ok.inj hstart)
            simp [hcommand] at hcmd

private theorem cutoff_decision_fields
    (sigma : Fin p.T) (g : ℕ) (lastProposal : Option (Fin p.T × Bool))
    (time : Fin p.T)
    (h : CoordinatorPhaseClock.detectCutoff
      { sigma := some sigma, u := none, g := g, lastProposal := lastProposal } time =
      .ok (.cutoff sigma rfl)) :
    FollowerCutoffScan.calendarRound time = g ∨
      ∃ stamp, lastProposal = some (stamp, true) ∧ stamp.val + 1 = time.val := by
  classical
  by_cases hgrid : FollowerCutoffScan.calendarRound time = g
  · exact Or.inl hgrid
  · right
    cases lastProposal with
    | none =>
        simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
          CoordinatorPhaseClock.savedPriorProposal] at h
        change Except.error CoordinatorPhaseClock.ClockFailure.missingPriorProposal =
          Except.ok (CoordinatorPhaseClock.CutoffDecision.cutoff sigma rfl) at h
        cases h
    | some token =>
        rcases token with ⟨stamp, bit⟩
        by_cases hstamp : stamp.val + 1 = time.val
        · cases bit with
          | false =>
              simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
                CoordinatorPhaseClock.savedPriorProposal, hstamp] at h
              change Except.ok CoordinatorPhaseClock.CutoffDecision.noCutoff =
                Except.ok (CoordinatorPhaseClock.CutoffDecision.cutoff sigma rfl) at h
              cases h
          | true => exact ⟨stamp, rfl, hstamp⟩
        · simp only [CoordinatorPhaseClock.detectCutoff, hgrid,
            CoordinatorPhaseClock.savedPriorProposal, hstamp] at h
          change Except.error CoordinatorPhaseClock.ClockFailure.stalePriorProposal =
            Except.ok (CoordinatorPhaseClock.CutoffDecision.cutoff sigma rfl) at h
          cases h

private theorem detectCutoff_cutoff_inputs
    (clock : CoordinatorPhaseClock.ClockRegisters p) (sigma time : Fin p.T)
    (hsigma : clock.sigma = some sigma)
    (hcutoff : CoordinatorPhaseClock.detectCutoff clock time =
      .ok (.cutoff sigma hsigma)) :
    clock.u = none ∧
      (FollowerCutoffScan.calendarRound time = clock.g ∨
        ∃ stamp, clock.lastProposal = some (stamp, true) ∧ stamp.val + 1 = time.val) := by
  cases clock with
  | mk sigmaOpt uOpt g lastProposal =>
      change sigmaOpt = some sigma at hsigma
      cases sigmaOpt with
      | none => simp at hsigma
      | some actualSigma =>
          have hsigma' : actualSigma = sigma := Option.some.inj hsigma
          subst sigma
          cases uOpt with
          | some u =>
              let c : CoordinatorPhaseClock.ClockRegisters p :=
                ⟨some actualSigma, some u, g, lastProposal⟩
              have hu : c.u = some u := rfl
              have hno := CoordinatorPhaseClock.detectCutoff_collection_noRead c time u hu
              rw [hno] at hcutoff
              cases hcutoff
          | none =>
              let c : CoordinatorPhaseClock.ClockRegisters p :=
                ⟨some actualSigma, none, g, lastProposal⟩
              have hliteral : CoordinatorPhaseClock.detectCutoff c time =
                  .ok (.cutoff actualSigma rfl) := by
                simpa [c] using hcutoff
              obtain hgrid | ⟨stamp, htoken, hstamp⟩ :=
                cutoff_decision_fields actualSigma g lastProposal time hliteral
              · exact ⟨rfl, Or.inl hgrid⟩
              · exact ⟨rfl, Or.inr ⟨stamp, htoken, hstamp⟩⟩

private theorem dispatchLive_cutoff_raw_dispatch
    (x : CoordinatorRoundDispatch.LiveInput p)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (hs : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok dispatched.startResult)
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger x.registers)
    (hi : dispatched.collectionInitialization = .success (some ledger))
    (he : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      x.registers x.ownedRegisters x.followerBaseScore x.registers.time)
    (hd : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      x.registers x.ownedRegisters x.followerBaseScore x.registers.time)
    (hc : dispatched.startResult.clock =
      { x.registers.priorClock with u := some x.registers.time })
    (hp : dispatched.startResult.pending = Finset.univ)
    (hn : dispatched.startResult.assignmentStart = none)
    (selected : CoordinatorRoundDispatch.ArmSelection x.registers.payload
      dispatched.startResult x.registers.time x.registers.complementWeights x.row)
    (houtcome : CoordinatorRoundDispatch.dispatchLive x =
      .cutoffChosen dispatched hs ledger hi he hd hc hp hn selected) :
    CoordinatorStartRoundCutoffDispatch.dispatch x.registers x.ownedRegisters
      x.followerBaseScore = .ok dispatched := by
  have hobs := congrArg
    (ReferenceLiveDispatchOutputMeasurability.outcomeData (x := x)) houtcome
  rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive] at hobs
  have hformula : ReferenceLiveDispatchOutputMeasurability.dataFormula x =
      ReferenceLiveDispatchOutputMeasurability.OutcomeData.cutoffChosen
        (ReferenceLiveDispatchOutputMeasurability.dispatchData dispatched)
        (ReferenceLiveDispatchOutputMeasurability.ledgerData ledger) selected.arm := by
    simpa only [ReferenceLiveDispatchOutputMeasurability.outcomeData] using hobs
  unfold ReferenceLiveDispatchOutputMeasurability.dataFormula at hformula
  cases hraw : CoordinatorStartRoundCutoffDispatch.dispatch x.registers
      x.ownedRegisters x.followerBaseScore with
  | error failure => simp [hraw] at hformula
  | ok actual =>
      rw [hraw] at hformula
      cases hinit : actual.collectionInitialization with
      | invalid => simp [hinit] at hformula
      | rejected value => simp [hinit] at hformula
      | success value =>
          cases value with
          | none =>
              simp only [hinit] at hformula
              by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
                  x.registers actual.startResult <;>
              by_cases hpayload : x.registers.priorClock.sigma =
                  some x.registers.payload.sigma <;>
              by_cases hgrid : x.registers.gridBoundary = x.registers.priorClock.g <;>
              by_cases hscore : x.registers.scoreDomainValid <;>
              by_cases hqueue : x.ownedRegisters.queueDomainValid <;>
              by_cases hprevious : x.ownedRegisters.previousServiceDomainValid <;>
              by_cases hbase : ∀ j, x.followerBaseScore j ≤ p.T * D p <;>
              by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                  x.registers.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
                  x.registers.time <;>
              by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                  x.registers.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
                  x.registers.time x.registers.complementWeights <;>
              by_cases hboundary : actual.startResult.clock.g ≤ p.T + 1 <;>
              by_cases henvelope : x.registers.complementEnvelopeValid
              all_goals
                simp [ReferenceLiveDispatchOutputMeasurability.choiceData,
                  hframe, hpayload, hgrid, hscore, hqueue, hprevious, hbase, hlive,
                  hchoice, hboundary, henvelope] at hformula
          | some actualLedger =>
              simp only [hinit] at hformula
              by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                  x.registers.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
                  x.registers.time x.registers.complementWeights <;>
              by_cases hboundary : actual.startResult.clock.g ≤ p.T + 1 <;>
              by_cases henvelope : x.registers.complementEnvelopeValid
              all_goals
                first
                | rw [ReferenceLiveDispatchOutputMeasurability.choiceData,
                    ite_eq_left hchoice, ite_eq_left hboundary, ite_eq_left henvelope] at hformula
                  have hcodes :=
                    ReferenceLiveDispatchOutputMeasurability.OutcomeData.cutoffChosen.inj hformula
                  have hactual :=
                    ReferenceLiveDispatchOutputMeasurability.dispatchData_injective hcodes.1
                  subst actual
                  rfl
                | simp [ReferenceLiveDispatchOutputMeasurability.choiceData,
                    hchoice, hboundary, henvelope] at hformula

private theorem cutoff_startRound_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T) (payload : ReferenceActivePhysicalStep.Payload rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (row : CompletePublicTable.CompleteRow p)
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid old)
    (hgridBound : t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hMcoord : ActiveFollowerLifecycle.acceptedStartCoordinate M = payload.sigma)
    (hMstarted : M.val.sigma ≤ t.val)
    (hstatus : old.status ≠ .unoccupied)
    (hcause : FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma = t.val + 1 ∨
      ∃ stamp : Fin p.T,
        clock.lastProposal = some (stamp, true) ∧ stamp.val + 1 = t.val ∧
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp = true)
    (hdown : old.lastDown = some M)
    (token : ActiveFollowerLifecycle.ProposalRead p)
    (hread : memory.lastProposalRead = some token)
    (htokenTime : token.timestamp.val + 1 = t.val)
    (htokenBit : token.bit =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val row token.timestamp) :
    ActiveFollowerLifecycle.interruptionDecision rate.eta t old memory = .ok true ∧
      ActiveFollowerLifecycle.startRound rate.eta t old memory =
        .ok ({old with status := .unoccupied}, memory) := by
  have hcauseForStart :
      FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerLifecycle.acceptedStartCoordinate M) = t.val + 1 ∨ token.bit = true := by
    rcases hcause with hgrid | ⟨stamp, _, hstamp, hbit⟩
    · exact Or.inl (by rw [hMcoord]; exact hgrid)
    · right
      have hstampEq : stamp = token.timestamp := by
        apply Fin.ext
        omega
      calc
        token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val row token.timestamp := htokenBit
        _ = FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp := by rw [hstampEq]
        _ = true := hbit
  have hnotmissed : t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val
      (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
    simpa [hMcoord] using hgridBound
  have hdecision : ActiveFollowerLifecycle.interruptionDecision rate.eta t old memory = .ok true := by
    simp [ActiveFollowerLifecycle.interruptionDecision, hstatus, hdomain, hdown, hMstarted,
      hnotmissed, hread, htokenTime, hcauseForStart]
  have hstart := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta t old memory
    hstatus hdomain M hdown hMstarted hnotmissed token hread
    (by change token.timestamp.val + 1 = t.val; exact htokenTime)
  refine ⟨hdecision, ?_⟩
  have hinterrupt :
      FollowerCutoffScan.gridBoundary p rate.eta.val
          (ActiveFollowerLifecycle.acceptedStartCoordinate M) = t.val + 1 || token.bit := by
    rcases hcauseForStart with hgrid | hbit
    · simp [hgrid]
    · simp [hbit]
  rw [hstart, hinterrupt]
  rfl

private theorem prepare_current_cutoff_follower
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (i : Fin (p.m - 1))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary old memory)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid old)
    (hmass : old.S + old.backlog ≤ record.input.time.val * D p)
    (hzero : old.lastDown = none → old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0)
    (hbusy : old.status ≠ .unoccupied →
      old.lastDown = some (payload.downRecord i) ∧
      ∃ token : ActiveFollowerLifecycle.ProposalRead p,
        memory.lastProposalRead = some token ∧
        token.timestamp.val + 1 = record.input.time.val ∧
        token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          record.input.row token.timestamp)
    (hgridBound : record.input.time.val + 1 ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hcause : FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma =
        record.input.time.val + 1 ∨
      ∃ stamp : Fin p.T,
        clock.lastProposal = some (stamp, true) ∧ stamp.val + 1 = record.input.time.val ∧
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp = true)
    (hMstarted : (payload.downRecord i).val.sigma ≤ record.input.time.val)
    (hMcredit : (payload.downRecord i).val.q ≤
      ((payload.downRecord i).val.sigma - 1) * D p)
    (hchron : ActiveFollowerLifecycle.localBufferValid old ∧
      old.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ old.buffer, saved.calendarRound < record.input.time.val + 1) :
    let c : ReferencePrelaunchFollower.State p rate.eta :=
      { old with status := .unoccupied }
    ActiveFollowerLifecycle.interruptionDecision rate.eta record.input.time old memory =
        .ok (decide (old.status ≠ .unoccupied)) ∧
      ActiveFollowerLifecycle.startRound rate.eta record.input.time old memory = .ok (c, memory) ∧
      (record.output.preparation.followers.followers i).configuration = .ordinary c memory ∧
      ActiveFollowerLifecycle.localStateDomainValid c ∧
      c.S + c.backlog ≤ record.input.time.val * D p ∧
      c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ c.buffer, saved.calendarRound < record.input.time.val + 1) ∧
      OrdinaryMessageCodec.upAdmissible
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ActiveFollowerQueueOperation.upOfferFields c) ∧
      (payload.downRecord i).val.sigma ≤ record.input.time.val ∧
      (payload.downRecord i).val.q ≤
        ((payload.downRecord i).val.sigma - 1) * D p := by
  classical
  let c : ReferencePrelaunchFollower.State p rate.eta := { old with status := .unoccupied }
  have hdomainC : ActiveFollowerLifecycle.localStateDomainValid c := by
    change ActiveFollowerLifecycle.localStateDomainValid old
    exact hdomain
  have hmassC : c.S + c.backlog ≤ record.input.time.val * D p := by
    change old.S + old.backlog ≤ record.input.time.val * D p
    exact hmass
  have hzeroC : c.lastDown = none → c.S = 0 ∧ c.delta = 0 ∧ c.backlog = 0 := by
    change old.lastDown = none → old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0
    exact hzero
  have hdecision : ActiveFollowerLifecycle.interruptionDecision rate.eta record.input.time old memory =
      .ok (decide (old.status ≠ .unoccupied)) := by
    by_cases hu : old.status = .unoccupied
    · rw [ActiveFollowerLifecycle.interruptionDecision_unoccupied rate.eta record.input.time
        old memory hdomain hu]
      simp [hu]
    · obtain ⟨hdown, token, hread, htime, hbit⟩ := hbusy hu
      obtain ⟨hdecision, _⟩ := cutoff_startRound_fields rate record.input.time payload clock
        record.input.row old memory (payload.downRecord i) hdomain hgridBound
        (by apply Fin.ext; exact Nat.add_sub_cancel _ _) hMstarted hu hcause
        hdown token hread htime hbit
      simpa [hu] using hdecision
  have hstart : ActiveFollowerLifecycle.startRound rate.eta record.input.time old memory =
      .ok (c, memory) := by
    by_cases hu : old.status = .unoccupied
    · have h := ActiveFollowerLifecycle.startRound_unoccupied rate.eta record.input.time
        old memory hdomain hu
      have heq : old = c := by
        cases old; simp_all [c]
      rw [← heq]
      exact h
    · obtain ⟨hdown, token, hread, htime, hbit⟩ := hbusy hu
      obtain ⟨_, hstart⟩ := cutoff_startRound_fields rate record.input.time payload clock
        record.input.row old memory (payload.downRecord i) hdomain hgridBound
        (by apply Fin.ext; exact Nat.add_sub_cancel _ _) hMstarted hu hcause
        hdown token hread htime hbit
      exact hstart
  have hdomainInput := stateInputDomain_of_localStateDomainValid c hdomainC
  have hup := up_admissible_of_localStateDomainValid c hdomainC hzeroC
  have hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary c memory := by
    rw [record.output.preparation.followers.followers_eq i]
    change (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i)).configuration = .ordinary c memory
    rw [hinput]
    exact prepare_configuration_of_unoccupied_start i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      old c memory memory (by simp [c]) hstart hdomainInput hup
  refine ⟨hdecision, hstart, hprepared, hdomainC, hmassC, ?_, ?_, hup, hMstarted, hMcredit⟩
  · simpa [c] using hchron.2.1
  · simpa [c] using hchron.2.2

/-- At the actual next replacement cutoff, preserve the whole installed
payload, source row and follower frame through PREPARE. The record is selected
inside the telescope, so absent successors and non-cutoff dispatcher outcomes
remain vacuous. This result stops at PREPARE and does not assert recovery or
FINISH after the cutoff. -/
theorem complete_first_replacement_cutoff_follower_boundary
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        match R[v + 1 + tail.length]? with
        | none => True
        | some r =>
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = false ∧
          match r.output.preparation.coordinator with
          | .live registers _ _
              (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            registers.payload = payload ∧
            r.input.time.val = birth.input.time.val + 1 + tail.length ∧
            r.input.time.val = s + v + 1 + tail.length ∧
            r.input.rows = source.1.2 ∧
            r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            r.input.rewards = rewards ∧
            payload.sigma.val = birth.input.time.val ∧
            s < payload.sigma.val ∧
            FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) =
                r.input.time.val + 1 ∧
            r.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
            (FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma = r.input.time.val + 1 ∨
              ∃ stamp : Fin p.T,
                registers.priorClock.lastProposal = some (stamp, true) ∧
                stamp.val + 1 = r.input.time.val ∧
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row stamp = true) ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
              r.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = payload ∧
              selected.view.pendingAtChoice = Finset.univ ∧
              selected.view.cutoff = some
                (CoordinatorCollectionUpRoundStep.localCutoff r.input.time) ∧
              ∀ i : Fin (p.m - 1),
                ∃ old : ReferencePrelaunchFollower.State p rate.eta,
                  ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                    r.input.state.followers i = .ordinary old memory ∧
                    ActiveFollowerLifecycle.localStateDomainValid old ∧
                    old.S + old.backlog ≤ r.input.time.val * D p ∧
                    (old.lastDown = none → old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∧
                    (old.status = .unoccupied →
                      ReferencePrelaunchFollower.acceptedStart old <
                        (payload.downRecord i).val.sigma) ∧
                    (old.status ≠ .unoccupied →
                      old.lastDown = some (payload.downRecord i) ∧
                      ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                        memory.lastProposalRead = some token ∧
                        token.timestamp.val + 1 = r.input.time.val ∧
                        token.bit = FollowerCutoffScan.completeRowProposalBit
                          p rate.eta.val r.input.row token.timestamp) ∧
                    let c : ReferencePrelaunchFollower.State p rate.eta :=
                      { old with status := .unoccupied }
                    ActiveFollowerLifecycle.interruptionDecision rate.eta r.input.time old memory =
                      .ok (decide (old.status ≠ .unoccupied)) ∧
                    ActiveFollowerLifecycle.startRound rate.eta r.input.time old memory =
                      .ok (c, memory) ∧
                    (r.output.preparation.followers.followers i).configuration =
                      .ordinary c memory ∧
                    ActiveFollowerLifecycle.localStateDomainValid c ∧
                    c.S + c.backlog ≤ r.input.time.val * D p ∧
                    c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                    (∀ saved ∈ c.buffer, saved.calendarRound < r.input.time.val + 1) ∧
                    OrdinaryMessageCodec.upAdmissible
                      (ReferencePrelaunchFollower.codecParams p rate.eta)
                      (ActiveFollowerQueueOperation.upOfferFields c) ∧
                    (payload.downRecord i).val.sigma ≤ r.input.time.val ∧
                    (payload.downRecord i).val.q ≤
                      ((payload.downRecord i).val.sigma - 1) * D p
          | _ => True
      | _ => True := by
  classical
  have hboundary := ReferenceFirstReplacementFollowerBoundary.complete_first_replacement_follower_boundary
    rate source rewards C_star C_h
  have hgeometry := ReferenceFirstReplacementLiveFollowerPrefix.complete_first_replacement_continuing_geometry
    rate source rewards C_star C_h
  have hbirth := ReferenceFirstReplacementDownRecovery.complete_first_replacement_down_recovery_and_finish
    rate source rewards C_star C_h
  have hseed := ReferenceFirstReplacementFollowerLoggingSeed.complete_first_replacement_follower_logging_seed
    rate source rewards C_star C_h
  have hbirthReadout := ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_birth_live_readout
    rate source rewards C_star C_h
  have hsuccessor := ReferenceFirstReplacementNextFollowerStep.complete_first_replacement_actual_successor
    rate source rewards C_star C_h
  dsimp only at hboundary hgeometry hbirth hseed hbirthReadout ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set Cwin := ReferenceCollectionPhaseHistory.collectionWindow R w
  set v := w + Cwin.length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hbirthGet] at hboundary hgeometry hbirth hseed hbirthReadout ⊢
      cases hbirthCoord : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection oldPayload oldLedger oldClock oldCutoff outcome =>
          rw [hbirthCoord] at hboundary hgeometry hbirth hseed hbirthReadout
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hinstruction output hconsistent
            clockData installed birthArm
          dsimp only at hboundary hgeometry hbirth hseed hbirthReadout ⊢
          let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
          let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          cases hcurrentGet : R[v + 1 + tail.length]? with
          | none => trivial
          | some current =>
              simp only at hboundary hgeometry hbirth hseed hbirthReadout ⊢
              have hdropEndpoint : (R.drop (v + 1))[tail.length]? = some current := by
                have hget : R[v + 1 + tail.length]? = some current := hcurrentGet
                simpa [tail, ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
                  List.getElem?_drop] using hget
              have hnotContinuing :
                  ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen current = false := by
                apply takeWhile_endpoint_false
                  ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
                  (R.drop (v + 1)) tail.length current hdropEndpoint
                rfl
              refine ⟨hnotContinuing, ?_⟩
              cases hcurrentCoord : current.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live registers owned base outcome =>
                  cases outcome <;> try trivial
                  rename_i dispatched hs ledger hi he hd hc hp hn chosen
                  dsimp only at ⊢
                  let currentIndex : Fin R.length :=
                    ⟨v + 1 + tail.length, (List.getElem?_eq_some_iff.mp hcurrentGet).1⟩
                  have hcurrentAt : R.get currentIndex = current :=
                    (List.getElem?_eq_some_iff.mp hcurrentGet).2
                  have hcurrentFields := complete_record_fields rate source rewards C_star C_h currentIndex
                  rw [hcurrentAt] at hcurrentFields
                  dsimp only at hcurrentFields
                  have hbirthIndex : v < R.length := (List.getElem?_eq_some_iff.mp hbirthGet).1
                  let birthIndex : Fin R.length := ⟨v, hbirthIndex⟩
                  have hbirthAt : R.get birthIndex = birth :=
                    (List.getElem?_eq_some_iff.mp hbirthGet).2
                  have hbirthFields := complete_record_fields rate source rewards C_star C_h birthIndex
                  rw [hbirthAt] at hbirthFields
                  dsimp only at hbirthFields
                  have htimeCurrent : current.input.time.val = s + v + 1 + tail.length := by
                    simpa [s, currentIndex, Nat.add_assoc] using hcurrentFields.1
                  have htimeBirth : birth.input.time.val = s + v := by
                    simpa [s, birthIndex] using hbirthFields.1
                  have hsigmaPayload : payload.sigma.val = birth.input.time.val := hgeometry.1
                  have hstrictStart : s < payload.sigma.val := by
                    rw [hsigmaPayload]
                    exact hbirth.1
                  let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
                    current.input registers.payload dispatched.startResult current.input.time
                    registers.complementWeights chosen rfl
                  have hselection : current.output.preparation.coordinator.selection = some selected := by
                    rw [hcurrentCoord]
                    exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq _ _ _ _ _ _ rfl
                  have hprepared : current.output.preparation =
                      ReferenceActivePhysicalStep.prepare current.input := by
                    rw [current.output_eq]
                    rfl
                  have hprepDispatch : (ReferenceActivePhysicalStep.prepare current.input).coordinator =
                      .live registers owned base
                        (.cutoffChosen dispatched hs ledger hi he hd hc hp hn chosen) := by
                    rw [← hprepared]
                    exact hcurrentCoord
                  have hdispatchEq : ReferenceActivePhysicalStep.dispatch current.input =
                      .live registers owned base
                        (.cutoffChosen dispatched hs ledger hi he hd hc hp hn chosen) :=
                    (ReferenceActivePhysicalStep.prepare current.input).coordinator_eq.symm.trans
                      hprepDispatch
                  have hstateLive : current.input.state.coordinator = .live registers owned base := by
                    have horigin := dispatch_live_origin current.input
                    rw [hdispatchEq] at horigin
                    exact horigin
                  have hcall := ReferenceFirstReplacementNextFollowerStep.complete_suffix_record_clock
                    rate source rewards C_star C_h currentIndex
                  rw [hcurrentAt] at hcall
                  simp only [ReferenceCoordinatorClockDomains.clockAt, hstateLive] at hcall
                  rcases hcall with ⟨hcallStamp, hclockValid, hclockSigma, hclockU,
                    hclockGrid, hsigmaPast, hbeforeGrid, hproposal⟩
                  let callInput := ReferenceActivePhysicalStep.liveInput current.input
                    registers owned base
                  have hdomains : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
                      callInput.registers callInput.ownedRegisters base current.input.time := by
                    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt,
                      ReferenceActivePhysicalStep.liveOwnedAt] using hd
                  have hsourceOutcome : CoordinatorRoundDispatch.dispatchLive callInput =
                      .cutoffChosen dispatched hs ledger hi he hd hc hp hn chosen := by
                    have hh := hdispatchEq
                    simp only [ReferenceActivePhysicalStep.dispatch, hstateLive,
                      CoordinatorRoundDispatch.dispatch,
                      ReferenceActivePhysicalStep.liveInput] at hh
                    exact eq_of_heq (ReferenceActivePhysicalStep.DispatchCut.live.inj hh).2.2.2
                  have hraw := dispatchLive_cutoff_raw_dispatch callInput dispatched hs ledger hi
                    he hdomains hc hp hn chosen hsourceOutcome
                  have hcommand := (CoordinatorRoundDispatch.cutoffDispatch_ledger_eq_candidate
                    callInput.registers callInput.ownedRegisters base dispatched ledger hraw hi).1
                  have hstartClock : CoordinatorPhaseClock.startRound p rate.eta.val
                      current.input.time registers.priorClock registers.clockPending =
                        .ok dispatched.startResult := by
                    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt,
                      CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq] using hs
                  have htimeValid : CoordinatorPhaseClock.startRoundTimeValid p
                      current.input.time registers.priorClock := by
                    simp only [CoordinatorPhaseClock.startRoundTimeValid,
                      hclockSigma, hclockU, FollowerCutoffScan.calendarRound]
                    exact ⟨hsigmaPast, by omega⟩
                  have hdetected := startRound_initializeAt_detectCutoff rate.eta.val
                    current.input.time registers.priorClock registers.clockPending
                    dispatched.startResult
                    (ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate)
                    hclockValid htimeValid hstartClock hcommand
                  obtain ⟨sigma, hsigma, hcutoff⟩ := hdetected
                  have hsigmaEq : sigma = registers.payload.sigma :=
                    Option.some.inj (hsigma.symm.trans hclockSigma)
                  subst sigma
                  have hcutInputs := detectCutoff_cutoff_inputs registers.priorClock
                    registers.payload.sigma current.input.time hclockSigma hcutoff
                  have hboundaryClock : registers.priorClock.g =
                      FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
                    simpa only [CoordinatorPhaseClock.boundaryFromSigma, hclockSigma] using
                      hclockValid.1
                  have hgridFrame : registers.gridBoundary = registers.priorClock.g := by
                    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
                      ReferenceActivePhysicalStep.liveRegistersAt] using hdomains.2.1
                  have hgridBound : current.input.time.val + 1 ≤
                      FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := by
                    calc
                      current.input.time.val + 1 ≤ registers.gridBoundary := by
                        simpa [callInput, ReferenceActivePhysicalStep.liveInput,
                          ReferenceActivePhysicalStep.liveRegistersAt] using hdomains.2.2.2.1
                      _ = registers.priorClock.g := hgridFrame
                      _ = FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma := hboundaryClock
                  have hcause : FollowerCutoffScan.gridBoundary p rate.eta.val registers.payload.sigma =
                      current.input.time.val + 1 ∨
                      ∃ stamp : Fin p.T,
                        registers.priorClock.lastProposal = some (stamp, true) ∧
                        stamp.val + 1 = current.input.time.val ∧
                        FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                          current.input.row stamp = true := by
                    rcases hcutInputs.2 with hgrid | ⟨stamp, htoken, hstamp⟩
                    · left
                      simpa [FollowerCutoffScan.calendarRound] using
                        (hgrid.trans hboundaryClock).symm
                    · right
                      have htokenEq := Option.some.inj (htoken.symm.trans hproposal)
                      have htokenBit := congrArg Prod.snd htokenEq
                      have hstampEq : stamp = registers.time := by
                        apply Fin.ext
                        omega
                      refine ⟨stamp, htoken, hstamp, ?_⟩
                      simpa [ReferenceActivePhysicalStep.RoundInput.row, hstampEq] using htokenBit.symm
                  have hselectedPayload : selected.view.payload = registers.payload := rfl
                  have hselectedPending : selected.view.pendingAtChoice = Finset.univ := by
                    change dispatched.startResult.pending = Finset.univ
                    exact hp
                  have hselectedCutoff : selected.view.cutoff =
                      some (CoordinatorCollectionUpRoundStep.localCutoff current.input.time) := by
                    change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                      dispatched.startResult.clock.u = _
                    rw [hc]
                    rfl
                  -- The payload in the dispatcher is the same installation carried by the birth.
                  have hregistersPayload : registers.payload = payload := by
                    by_cases htailEmpty : tail.length = 0
                    · have hnextRoot := hsuccessor
                      dsimp only at hnextRoot
                      have hcurrentGet0 : R[v + 1]? = some current := by
                        simpa [tail, htailEmpty] using hcurrentGet
                      have hbirthGet' : R[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
                          (ReferenceCollectionPhaseHistory.collectionWindow R
                            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length]? =
                            some birth := by
                        simpa [R, w, Cwin, v] using hbirthGet
                      have hcurrentGet0' : R[(ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length +
                          (ReferenceCollectionPhaseHistory.collectionWindow R
                            (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length).length + 1]? =
                            some current := by
                        simpa [R, w, Cwin, v] using hcurrentGet0
                      rw [hbirthGet', hcurrentGet0'] at hnextRoot
                      rcases hnextRoot with ⟨_, _, _, _, _, hstateNext, _⟩
                      let birthSelectedData := hbirthReadout
                      simp only [R, s, w, Cwin, v] at birthSelectedData
                      obtain ⟨_, _, _, birthSelected, hbirthSelected, hbirthPayload, _, _, _⟩ :=
                        birthSelectedData
                      have hbirthSelected' :
                          birth.output.preparation.coordinator.selection = some birthSelected := by
                        rw [hbirthCoord]
                        exact hbirthSelected
                      have hbirthNext : birth.output.next.coordinator =
                          (ReferenceActivePhysicalStep.livePostChoice birth.output.preparation
                            installed.registers installed.ownedRegisters installed.retainedBaseScore started).configuration := by
                        have hnext' : birth.output.next.coordinator =
                            birth.output.preparation.observeCoordinator.configuration := by
                          rw [birth.output_eq]
                          rfl
                        rw [hnext']
                        unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
                        rw [dite_eq_right (by rw [hbirthSelected']; exact Option.some_ne_none _),
                          hbirthCoord]
                      have hstoredCurrent : ReferenceAssignmentPayloadPersistence.storedPayload
                          current.input.state.coordinator = some registers.payload := by
                        rw [hstateLive]
                        rfl
                      have hstoredNext : ReferenceAssignmentPayloadPersistence.storedPayload
                          birth.output.next.coordinator = some registers.payload := by
                        rw [← hstateNext]
                        exact hstoredCurrent
                      rw [hbirthNext] at hstoredNext
                      have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
                        birth.output.preparation installed.registers installed.ownedRegisters
                        installed.retainedBaseScore started
                      rcases hframe with hnone | hsome
                      · rw [hnone] at hstoredNext
                        cases hstoredNext
                      · exact Option.some.inj (hstoredNext.symm.trans hsome)
                    · have htailPositive : 0 < tail.length := Nat.pos_of_ne_zero htailEmpty
                      let k : Fin tail.length := ⟨tail.length - 1, by omega⟩
                      let previous := tail.get k
                      have hprevMember : previous ∈ tail := List.get_mem _ _
                      have hprevContinuing := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem
                        R v previous hprevMember
                      have hprevIndex : R[v + tail.length]? = some previous := by
                        have hget := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
                        have hidx : v + 1 + k.val = v + tail.length := by
                          dsimp [k]
                          omega
                        simpa only [hidx] using hget
                      have hprevFin : (R.get ⟨v + tail.length,
                          (List.getElem?_eq_some_iff.mp hprevIndex).1⟩) = previous :=
                        (List.getElem?_eq_some_iff.mp hprevIndex).2
                      have hprevBoundary := hboundary k
                      obtain ⟨_, _, _, _, prevSelected, hprevSelection, hprevPayload,
                        _, _, _, hprevFollowers⟩ := hprevBoundary
                      have hprevInputIndex : v + tail.length + 1 < R.length := by
                        have h := (List.getElem?_eq_some_iff.mp hcurrentGet).1
                        omega
                      have hadj := complete_adjacent rate source rewards C_star C_h
                        (v + tail.length) (by omega)
                      have hstateLink : current.input.state = previous.output.next := by
                        have hcurrentGet' : R[v + tail.length + 1]? = some current := by
                          have hidx : v + 1 + tail.length = v + tail.length + 1 := by omega
                          simpa only [hidx] using hcurrentGet
                        let pi : Fin R.length := ⟨v + tail.length, by omega⟩
                        let ci : Fin R.length := ⟨v + tail.length + 1, hprevInputIndex⟩
                        have hp : R.get pi = previous := hprevFin
                        have hc' : R.get ci = current := (List.getElem?_eq_some_iff.mp hcurrentGet').2
                        rw [← hp, ← hc']
                        exact hadj.1
                      have hnotBirthCurrent :
                          ¬ ∃ q : ReferenceActivePhysicalStep.Payload rate,
                            ReferenceAssignmentPayloadPersistence.InstallationBirth current q := by
                        rintro ⟨q, hbirthCurrent⟩
                        simp [ReferenceAssignmentPayloadPersistence.InstallationBirth,
                          hcurrentCoord] at hbirthCurrent
                      have hcurrentSelectedPayload := selected_payload_continues_to_successor
                        previous current hstateLink hprevContinuing hnotBirthCurrent prevSelected
                        selected hprevSelection hselection
                      calc
                        registers.payload = selected.view.payload := hselectedPayload.symm
                        _ = prevSelected.view.payload := hcurrentSelectedPayload
                        _ = payload := hprevPayload

                  have hgridBoundPayload : current.input.time.val + 1 ≤
                      FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
                    simpa [hregistersPayload] using hgridBound
                  have hcausePayload :
                      FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma =
                          current.input.time.val + 1 ∨
                        ∃ stamp : Fin p.T,
                          registers.priorClock.lastProposal = some (stamp, true) ∧
                          stamp.val + 1 = current.input.time.val ∧
                          FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                            current.input.row stamp = true := by
                    simpa [hregistersPayload] using hcause
                  have hbitsPrior : ∀ j : Fin p.T, payload.sigma.val ≤ j.val →
                      j.val + 1 < current.input.time.val →
                      FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                        current.input.row j = false := by
                    intro j hsigmaJ hbefore
                    by_cases htailEmpty : tail.length = 0
                    · have htimeZero : current.input.time.val = birth.input.time.val + 1 := by
                        rw [htimeCurrent, htailEmpty, htimeBirth]
                      exact False.elim (by
                        rw [hsigmaPayload] at hsigmaJ
                        rw [htimeZero] at hbefore
                        omega)
                    · have htailPositive : 0 < tail.length := Nat.pos_of_ne_zero htailEmpty
                      let k : Fin tail.length := ⟨tail.length - 1, by omega⟩
                      let previous := tail.get k
                      have hget := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
                      have hidx : v + 1 + k.val = v + tail.length := by
                        dsimp [k]
                        omega
                      have hprevGet : R[v + tail.length]? = some previous := by
                        simpa only [hidx, previous] using hget
                      have hprevGeometry := hgeometry.2 k
                      obtain ⟨_, hprevTime, hprevRows, hprevSelected, _, _, _, hprevPayload,
                        _, _, hprevBits⟩ := hprevGeometry
                      have hprevRow : previous.input.row = current.input.row := by
                        change previous.input.rows previous.input.selected =
                          current.input.rows current.input.selected
                        rw [hprevRows, hprevSelected, hcurrentFields.2.1,
                          hcurrentFields.2.2.1]
                      have hbeforePrev : j.val < previous.input.time.val := by
                        rw [hprevTime]
                        omega
                      rw [← hprevRow]
                      exact hprevBits j hsigmaJ hbeforePrev
                  have hfirstCutoff : FollowerCutoffScan.firstCutoff p rate.eta.val
                      payload.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val current.input.row) =
                        current.input.time.val + 1 := by
                    let endpoint := current.input.time.val + 1
                    have hendpointGrid : endpoint ≤
                        FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma := by
                      simpa [endpoint] using hgridBoundPayload
                    have hmem : endpoint ∈ FollowerCutoffScan.firstCutoffCarrier p rate.eta.val
                        payload.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                          current.input.row) := by
                      rcases hcausePayload with hgrid | ⟨stamp, _, hstamp, hbit⟩
                      · exact Finset.mem_insert.mpr (Or.inl (by simpa [endpoint] using hgrid.symm))
                      · apply Finset.mem_insert_of_mem
                        unfold FollowerCutoffScan.trueProposalEndpoints
                        apply Finset.mem_image.mpr
                        have hcoordinate : stamp ∈ FollowerCutoffScan.proposalCoordinates p payload.sigma := by
                          simp only [FollowerCutoffScan.proposalCoordinates,
                            Finset.mem_filter, Finset.mem_univ, true_and]
                          constructor
                          · rw [hsigmaPayload, htimeBirth]
                            omega
                          · have ht := current.input.time.isLt
                            omega
                        refine ⟨stamp, Finset.mem_filter.mpr ⟨hcoordinate, hbit⟩, ?_⟩
                        simp [FollowerCutoffScan.proposalEndpoint, endpoint]
                        omega
                    have hleast : ∀ y, y ∈ FollowerCutoffScan.firstCutoffCarrier p rate.eta.val
                        payload.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                          current.input.row) → endpoint ≤ y := by
                      intro y hy
                      simp only [FollowerCutoffScan.firstCutoffCarrier,
                        Finset.mem_insert] at hy
                      rcases hy with hgrid | hevent
                      · rw [hgrid]
                        exact hendpointGrid
                      · obtain ⟨stamp, hfiltered, hendpoint⟩ := Finset.mem_image.mp hevent
                        have hparts := Finset.mem_filter.mp hfiltered
                        have hcoords := Finset.mem_filter.mp hparts.1
                        have hsigmaStamp : payload.sigma.val ≤ stamp.val := by
                          have hpair : payload.sigma.val ≤ stamp.val ∧ stamp.val + 1 < p.T := by
                            simpa [FollowerCutoffScan.proposalCoordinates] using hcoords.2
                          exact hpair.1
                        by_cases hbefore : stamp.val + 1 < current.input.time.val
                        · have hfalse := hbitsPrior stamp hsigmaStamp hbefore
                          have htrue : FollowerCutoffScan.completeRowProposalBit
                              p rate.eta.val current.input.row stamp = true := hparts.2
                          rw [hfalse] at htrue
                          cases htrue
                        · rw [FollowerCutoffScan.proposalEndpoint] at hendpoint
                          omega
                    have hmin : (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val
                        payload.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                          current.input.row)).min'
                          (FollowerCutoffScan.firstCutoffCarrier_nonempty p rate.eta.val
                            payload.sigma (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                              current.input.row)) = endpoint := by
                      apply (Finset.min'_eq_iff _ _ endpoint).2
                      exact ⟨hmem, hleast⟩
                    simpa [FollowerCutoffScan.firstCutoff, endpoint] using hmin
                  have hlocal : ∀ i : Fin (p.m - 1),
                      ∃ old : ReferencePrelaunchFollower.State p rate.eta,
                        ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                          current.input.state.followers i = .ordinary old memory ∧
                          ActiveFollowerLifecycle.localStateDomainValid old ∧
                          old.S + old.backlog ≤ current.input.time.val * D p ∧
                          (old.lastDown = none → old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∧
                          (old.status = .unoccupied →
                            ReferencePrelaunchFollower.acceptedStart old <
                              (payload.downRecord i).val.sigma) ∧
                          (old.status ≠ .unoccupied →
                            old.lastDown = some (payload.downRecord i) ∧
                            ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                              memory.lastProposalRead = some token ∧
                              token.timestamp.val + 1 = current.input.time.val ∧
                              token.bit = FollowerCutoffScan.completeRowProposalBit
                                p rate.eta.val current.input.row token.timestamp) ∧
                          let c : ReferencePrelaunchFollower.State p rate.eta :=
                            { old with status := .unoccupied }
                          ActiveFollowerLifecycle.interruptionDecision rate.eta current.input.time
                              old memory = .ok (decide (old.status ≠ .unoccupied)) ∧
                            ActiveFollowerLifecycle.startRound rate.eta current.input.time old memory =
                              .ok (c, memory) ∧
                            (current.output.preparation.followers.followers i).configuration =
                              .ordinary c memory ∧
                            ActiveFollowerLifecycle.localStateDomainValid c ∧
                            c.S + c.backlog ≤ current.input.time.val * D p ∧
                            c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                            (∀ saved ∈ c.buffer, saved.calendarRound < current.input.time.val + 1) ∧
                            OrdinaryMessageCodec.upAdmissible
                              (ReferencePrelaunchFollower.codecParams p rate.eta)
                              (ActiveFollowerQueueOperation.upOfferFields c) ∧
                            (payload.downRecord i).val.sigma ≤ current.input.time.val ∧
                            (payload.downRecord i).val.q ≤
                              ((payload.downRecord i).val.sigma - 1) * D p := by
                    intro i
                    have hdownData := hbirth.2 i
                    obtain ⟨_, _, _, _, _, _, _, _, _, hMbirth, hqBirth, _⟩ := hdownData
                    have hMbirth' : (payload.downRecord i).val.sigma =
                        birth.input.time.val + 1 := by
                      change (installed.registers.payload.downRecord i).val.sigma =
                        birth.input.time.val + 1
                      exact hMbirth
                    have hqBirth' : (payload.downRecord i).val.q ≤ birth.input.time.val * D p := by
                      change (installed.registers.payload.downRecord i).val.q ≤
                        birth.input.time.val * D p
                      exact hqBirth
                    have hMcredit : (payload.downRecord i).val.q ≤
                        ((payload.downRecord i).val.sigma - 1) * D p := by
                      calc
                        (payload.downRecord i).val.q ≤ birth.input.time.val * D p := hqBirth'
                        _ = ((payload.downRecord i).val.sigma - 1) * D p := by
                          rw [hMbirth']
                          simp
                    have hbase :
                        ∃ old : ReferencePrelaunchFollower.State p rate.eta,
                          ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                            current.input.state.followers i = .ordinary old memory ∧
                            ActiveFollowerLifecycle.localStateDomainValid old ∧
                            old.S + old.backlog ≤ current.input.time.val * D p ∧
                            (old.lastDown = none → old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∧
                            (old.status = .unoccupied →
                              ReferencePrelaunchFollower.acceptedStart old <
                                (payload.downRecord i).val.sigma) ∧
                            (old.status ≠ .unoccupied →
                              old.lastDown = some (payload.downRecord i) ∧
                              ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                                memory.lastProposalRead = some token ∧
                                token.timestamp.val + 1 = current.input.time.val ∧
                                token.bit = FollowerCutoffScan.completeRowProposalBit
                                  p rate.eta.val current.input.row token.timestamp) := by
                      by_cases htailEmpty : tail.length = 0
                      · have hcurrentGet0 : R[v + 1]? = some current := by
                          simpa [tail, htailEmpty] using hcurrentGet
                        have hsucc := hsuccessor
                        dsimp only at hsucc
                        rw [hbirthGet, hcurrentGet0] at hsucc
                        rcases hsucc with ⟨_, _, _, _, _, hstateLink, hcalendar⟩
                        obtain ⟨_, hfollowersBirth⟩ := hbirth
                        rcases hseed with ⟨_, _, _, _, _, _, _, hseedFollowers⟩
                        obtain ⟨birthOld, birthMemory, logged, hstateOld, hstatusOld,
                          _hconfigurationOld, hrest⟩ := hfollowersBirth i
                        obtain ⟨oldSeed, memorySeed, loggedSeed, hstateSeed, hstatusSeed,
                          _hdomainSeed, _hbufferSeed, _hdecoderSeed, _hendpointSeed, _hmassSeed,
                          _htimestampsSeed, _hkeysSeed, _hquantizedSeed, _hpairwiseSeed,
                          _hbeforeSeed, hzeroSeed, _hseedTail⟩ := hseedFollowers i
                        have hsameState := hstateOld.symm.trans hstateSeed
                        simp only [DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq]
                          at hsameState
                        rcases hsameState with ⟨rfl, rfl⟩
                        rcases hrest with
                          ⟨hlogging, _hoperationDomain, hacceptedBefore, hnewSigma, _hnewQ,
                            _hdownAlternatives, hnextExists⟩
                        rcases hnextExists with ⟨next, hnextUpdate, hnextAlternatives⟩
                        rcases hnextUpdate with
                          ⟨_hconsume, _hrelease, _hfinish, _hreleaseFinish, houtputFollower,
                            hnextDomain, hnextMass, _hnextDelta, _hnextFailure⟩
                        let nextMemory : ActiveFollowerLifecycle.LocalMemory p :=
                          if next.status = .unoccupied then birthMemory else
                            ⟨some ⟨birth.input.time,
                              FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                                birth.input.row birth.input.time⟩⟩
                        have houtputConfig : (birth.output.followers i).configuration =
                            .ordinary next nextMemory := by
                          have h := congrArg
                            ReferenceActivePhysicalStep.FollowerObservation.configuration
                            houtputFollower
                          simpa only [nextMemory] using h
                        have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
                          i birth.input.row (birth.input.state.activations i) birth.input.time
                          ((birth.output.preparation.followers.followers i).arm,
                            birth.output.preparation.feedback.observations
                              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                          birthOld logged hlogging
                        have hzeroOld : birthOld.lastDown = none →
                            birthOld.S = 0 ∧ birthOld.delta = 0 ∧ birthOld.backlog = 0 := by
                          intro hnone
                          rcases hzeroSeed with hzero | hprior
                          · exact ⟨hzero.2.1, hzero.2.2.1, hzero.2.2.2⟩
                          · rw [hprior] at hnone
                            cases hnone
                        have hstateAfter : birth.output.next.followers i =
                            .ordinary next nextMemory := by
                          have hnextConfig : birth.output.next.followers i =
                              (birth.output.preparation.observeFollower i).configuration := by
                            rw [birth.output_eq]
                            rfl
                          have hobserve : birth.output.preparation.observeFollower i =
                              birth.output.followers i := by
                            rw [birth.output_eq]
                            rfl
                          rw [hobserve] at hnextConfig
                          exact hnextConfig.trans houtputConfig
                        have hinputAfter : current.input.state.followers i =
                            .ordinary next nextMemory := by
                          rw [hstateLink]
                          exact hstateAfter
                        have hbranch :
                            (next.status = .unoccupied ∧
                              (next.lastDown = none →
                                next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0) ∧
                              next.lastDown = logged.lastDown) ∨
                            (next.status = .pending ∧
                              next.lastDown = some (payload.downRecord i) ∧
                              (payload.downRecord i).val.sigma = birth.input.time.val + 1) := by
                          rcases hnextAlternatives with hskip | hreject | haccepted
                          · rcases hskip with ⟨_, _, hnextEq⟩
                            subst next
                            have hlogLast := hloggingFrame.1
                            have hlogS := hloggingFrame.2.1
                            have hlogDelta := hloggingFrame.2.2.1
                            have hlogBacklog := hloggingFrame.2.2.2.1
                            have hlogStatus := hloggingFrame.2.2.2.2.1
                            have hzero : logged.lastDown = none →
                                logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0 := by
                              intro hnone
                              have holdNone : birthOld.lastDown = none := by
                                rw [← hlogLast]
                                exact hnone
                              have hz := hzeroOld holdNone
                              rw [hlogS, hlogDelta, hlogBacklog]
                              exact hz
                            exact Or.inl ⟨hlogStatus.trans hstatusOld, hzero, rfl⟩
                          · rcases hreject with ⟨_, _, _, _, _, hnextEq⟩
                            have hlogLast := hloggingFrame.1
                            have hlogS := hloggingFrame.2.1
                            have hlogDelta := hloggingFrame.2.2.1
                            have hlogBacklog := hloggingFrame.2.2.2.1
                            have hlogStatus := hloggingFrame.2.2.2.2.1
                            have hzero : next.lastDown = none →
                                next.S = 0 ∧ next.delta = 0 ∧ next.backlog = 0 := by
                              intro hnone
                              have hnone' : logged.lastDown = none := by
                                simpa [hnextEq] using hnone
                              have holdNone : birthOld.lastDown = none := by
                                rw [← hlogLast]
                                exact hnone'
                              have hz := hzeroOld holdNone
                              constructor
                              · have hnextS : next.S = logged.S := by simp [hnextEq]
                                rw [hnextS, hlogS]
                                exact hz.1
                              · constructor
                                · have hnextDelta : next.delta = logged.delta := by simp [hnextEq]
                                  rw [hnextDelta, hlogDelta]
                                  exact hz.2.1
                                · have hnextBacklog : next.backlog = logged.backlog := by
                                    simp [hnextEq]
                                  rw [hnextBacklog, hlogBacklog]
                                  exact hz.2.2
                            have hstatusNext : next.status = .unoccupied := by
                              rw [hnextEq]
                              simp [hlogStatus, hstatusOld]
                            exact Or.inl ⟨hstatusNext, hzero, by simp [hnextEq]⟩
                          · rcases haccepted with
                              ⟨_, _, _, _, _, _, _, _, _, _, _, _, hnextEq⟩
                            refine Or.inr ⟨?_, ?_, ?_⟩
                            · rw [hnextEq]
                            · rw [hnextEq]
                              rfl
                            · rw [payload.downRecord_fields i]
                              exact hnewSigma
                        have hstrictNext : next.status = .unoccupied →
                            ReferencePrelaunchFollower.acceptedStart next <
                              (payload.downRecord i).val.sigma := by
                          intro hu
                          rcases hbranch with ⟨hstatus, _, hlast⟩ | ⟨hstatus, _, _⟩
                          · have : next.status = .unoccupied := hstatus
                            have hacceptedBefore' :
                                ReferencePrelaunchFollower.acceptedStart logged <
                                  (payload.downRecord i).val.sigma := by
                              change ReferencePrelaunchFollower.acceptedStart logged <
                                (installed.registers.payload.downRecord i).val.sigma
                              exact hacceptedBefore
                            simpa [ReferencePrelaunchFollower.acceptedStart, hlast] using
                              hacceptedBefore'
                          · rw [hstatus] at hu
                            cases hu
                        have hbusyNext : next.status ≠ .unoccupied →
                            next.lastDown = some (payload.downRecord i) ∧
                            ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                              nextMemory.lastProposalRead = some token ∧
                              token.timestamp.val + 1 = current.input.time.val ∧
                              token.bit = FollowerCutoffScan.completeRowProposalBit
                                p rate.eta.val current.input.row token.timestamp := by
                          intro hbusy
                          rcases hbranch with ⟨hstatus, _, _⟩ | ⟨hstatus, hdown, _⟩
                          · exact (hbusy hstatus).elim
                          · let token : ActiveFollowerLifecycle.ProposalRead p :=
                              ⟨birth.input.time,
                                FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                                  birth.input.row birth.input.time⟩
                            have hread : nextMemory.lastProposalRead = some token := by
                              simp [nextMemory, hstatus, token]
                            have htime : token.timestamp.val + 1 = current.input.time.val := by
                              dsimp [token]
                              omega
                            have hrowEq : birth.input.row = current.input.row := by
                              change birth.input.rows birth.input.selected =
                                current.input.rows current.input.selected
                              rw [hbirthFields.2.1, hbirthFields.2.2.1,
                                hcurrentFields.2.1, hcurrentFields.2.2.1]
                            have hbit : token.bit =
                                FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                                  current.input.row token.timestamp := by
                              dsimp [token]
                              rw [hrowEq]
                            exact ⟨hdown, token, hread, htime, hbit⟩
                        refine ⟨next, nextMemory, hinputAfter, hnextDomain, ?_, ?_,
                          hstrictNext, hbusyNext⟩
                        · rw [hcalendar]
                          exact hnextMass
                        · intro hnone
                          rcases hbranch with ⟨_, hzero, _⟩ | ⟨_, hdown, _⟩
                          · exact hzero hnone
                          · rw [hdown] at hnone
                            cases hnone
                      · have htailPositive : 0 < tail.length := Nat.pos_of_ne_zero htailEmpty
                        let k : Fin tail.length := ⟨tail.length - 1, by omega⟩
                        let previous := tail.get k
                        have hprevGet :=
                          ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_get R v k
                        have hidx : v + 1 + k.val = v + tail.length := by
                          dsimp [k]
                          omega
                        have hprevIndex : R[v + tail.length]? = some previous := by
                          simpa only [hidx, previous] using hprevGet
                        have hprevFin : R.get ⟨v + tail.length,
                            (List.getElem?_eq_some_iff.mp hprevIndex).1⟩ = previous :=
                          (List.getElem?_eq_some_iff.mp hprevIndex).2
                        have hprevBoundary := hboundary k
                        obtain ⟨_, hprevRows, hprevSelected, _, _, _, _, _, _, _,
                          hfollowersPrev⟩ := hprevBoundary
                        obtain ⟨state, memory, next, nextMemory, hinputPrev, hdomainPrev,
                          hmassPrev, hzeroPrev, hstrictPrev, hbusyPrev, _, _, _, _, _, _, _,
                          houtPrev, _, _, hdomainNext, hmassNext, _, hzeroNext, hstrictNext,
                          hbusyNext, _⟩ := hfollowersPrev i
                        have hprevInputIndex : v + tail.length + 1 < R.length := by
                          have h := (List.getElem?_eq_some_iff.mp hcurrentGet).1
                          omega
                        have hcurrentGet' : R[v + tail.length + 1]? = some current := by
                          have hidx' : v + 1 + tail.length = v + tail.length + 1 := by omega
                          simpa only [hidx'] using hcurrentGet
                        let pi : Fin R.length := ⟨v + tail.length, by omega⟩
                        let ci : Fin R.length := ⟨v + tail.length + 1, hprevInputIndex⟩
                        have hprevAt : R.get pi = previous := hprevFin
                        have hcurrentAt' : R.get ci = current :=
                          (List.getElem?_eq_some_iff.mp hcurrentGet').2
                        have hadj := complete_adjacent rate source rewards C_star C_h
                          (v + tail.length) (by omega)
                        have hstateLink : current.input.state = previous.output.next := by
                          rw [← hprevAt, ← hcurrentAt']
                          exact hadj.1
                        have hcalendar : current.input.time.val = previous.input.time.val + 1 := by
                          rw [← hprevAt, ← hcurrentAt']
                          exact hadj.2
                        have hrowEq : previous.input.row = current.input.row := by
                          change previous.input.rows previous.input.selected =
                            current.input.rows current.input.selected
                          rw [hprevRows, hprevSelected,
                            hcurrentFields.2.1, hcurrentFields.2.2.1]
                        have hinput : current.input.state.followers i = .ordinary next nextMemory := by
                          rw [hstateLink]
                          have hnextConfig : previous.output.next.followers i =
                              (previous.output.preparation.observeFollower i).configuration := by
                            rw [previous.output_eq]
                            rfl
                          have hobserve : previous.output.preparation.observeFollower i =
                              previous.output.followers i := by
                            rw [previous.output_eq]
                            rfl
                          rw [hobserve] at hnextConfig
                          exact hnextConfig.trans houtPrev
                        have hmass : next.S + next.backlog ≤ current.input.time.val * D p := by
                          rw [hcalendar]
                          exact hmassNext
                        have hbusy : next.status ≠ .unoccupied →
                            next.lastDown = some (payload.downRecord i) ∧
                            ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                              nextMemory.lastProposalRead = some token ∧
                              token.timestamp.val + 1 = current.input.time.val ∧
                              token.bit = FollowerCutoffScan.completeRowProposalBit
                                p rate.eta.val current.input.row token.timestamp := by
                          intro hoccupied
                          obtain ⟨hdown, token, hread, htime, hbit⟩ := hbusyNext hoccupied
                          refine ⟨hdown, token, hread, ?_, ?_⟩
                          · rw [hcalendar]
                            exact htime
                          · rw [← hrowEq]
                            exact hbit
                        exact ⟨next, nextMemory, hinput, hdomainNext, hmass, hzeroNext,
                          hstrictNext, hbusy⟩
                    obtain ⟨old, memory, hinput, hdomain, hmass, hzero, hstrict, hbusy⟩ := hbase
                    have hinputAt : (R.get currentIndex).input.state.followers i =
                        .ordinary old memory := by
                      rw [hcurrentAt]
                      exact hinput
                    have hchron0 :=
                      ReferenceFirstReplacementLiveFollowerPrefix.complete_input_buffer_chronological
                        rate source rewards C_star C_h currentIndex i old memory hinputAt
                    have hchron : ActiveFollowerLifecycle.localBufferValid old ∧
                        old.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                        (∀ saved ∈ old.buffer,
                          saved.calendarRound < current.input.time.val + 1) := by
                      rw [hcurrentAt] at hchron0
                      exact hchron0
                    have hMstarted : (payload.downRecord i).val.sigma ≤ current.input.time.val := by
                      omega
                    obtain ⟨hdecision, hstart, hprepared, hdomainC, hmassC, hpairwise,
                      htimestamps, hup, _, _⟩ := prepare_current_cutoff_follower current payload
                        registers.priorClock i old memory hinput hdomain hmass hzero hbusy
                        hgridBoundPayload hcausePayload hMstarted hMcredit hchron
                    refine ⟨old, memory, hinput, hdomain, hmass, hzero, hstrict, hbusy,
                      hdecision, hstart, hprepared, hdomainC, hmassC, hpairwise, htimestamps,
                      hup, hMstarted, hMcredit⟩
                  have htimeFromBirth : current.input.time.val =
                      birth.input.time.val + 1 + tail.length := by
                    rw [htimeCurrent, htimeBirth]
                  refine ⟨hregistersPayload, htimeFromBirth, htimeCurrent,
                    hcurrentFields.2.1, hcurrentFields.2.2.1, hcurrentFields.2.2.2,
                    hsigmaPayload, hstrictStart, hfirstCutoff, hgridBoundPayload, hcausePayload,
                    selected, ?_, ?_, hselectedPending, hselectedCutoff, hlocal⟩
                  · simpa [hcurrentCoord] using hselection
                  · calc
                      selected.view.payload = registers.payload := hselectedPayload
                      _ = payload := hregistersPayload
end Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary
end
end
