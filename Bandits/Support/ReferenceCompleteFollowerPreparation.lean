/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteUnoccupiedNonacceptingForward

/-!
# PREPARE from an actual complete-suffix follower input

For a follower that is ordinary in an actual complete-suffix round input, this
module derives the source local domains from that same run and evaluates the
literal start, UP-offer, and arm-choice branches. It assumes neither a
successful arm nor an ordinary choice snapshot.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferenceCompletePhysicalHistory

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

namespace Bandits.Support.ReferenceCompleteFollowerPreparation

private theorem operation_input_of_local_domains
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hregisters : ActiveFollowerLifecycle.serviceRegistersValid p state)
    (hbuffer : ActiveFollowerLifecycle.localBufferValid state)
    (hdecoder : ActiveFollowerLifecycle.downDecoderStateValid state) :
    ActiveFollowerDownAcceptance.operationInputDomain p rate state := by
  refine ⟨hregisters, hdecoder, ?_⟩
  refine ⟨?_, hbuffer.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, hquantized⟩ := hbuffer.2.2 saved hsaved
  exact ⟨(hbuffer.1 saved hsaved).1, (hbuffer.1 saved hsaved).2,
    ⟨⟨q, by omega⟩, hquantized⟩⟩

private theorem started_state_domains
    (time : Fin p.T) (before choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time before memory =
      .ok (choice, memory))
    (hregisters : ActiveFollowerLifecycle.serviceRegistersValid p before)
    (hbuffer : ActiveFollowerLifecycle.localBufferValid before)
    (hdecoder : ActiveFollowerLifecycle.downDecoderStateValid before) :
    ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerQueueOperation.stateInputDomain choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice := by
  obtain ⟨hdown, hS, hdelta, hbacklog, hbatch, hbufferEq, _hmarker, _hmemory⟩ :=
    ActiveFollowerLifecycle.startRound_frame rate.eta time before choice memory memory hstart
  have hregisters' : ActiveFollowerLifecycle.serviceRegistersValid p choice := by
    exact ⟨by simpa [hS] using hregisters.1,
      by simpa [hdelta] using hregisters.2.1,
      by simpa [hbacklog] using hregisters.2.2⟩
  have hbuffer' : ActiveFollowerLifecycle.localBufferValid choice := by
    simpa only [ActiveFollowerLifecycle.localBufferValid, hbufferEq] using hbuffer
  have hdecoder' : ActiveFollowerLifecycle.downDecoderStateValid choice := by
    simpa only [ActiveFollowerLifecycle.downDecoderStateValid, hbatch] using hdecoder
  have hlocal : ActiveFollowerLifecycle.localStateDomainValid choice :=
    ⟨hregisters', hbuffer', hdecoder'⟩
  have hstateInput : ActiveFollowerQueueOperation.stateInputDomain choice := by
    refine ⟨hregisters'.1, hregisters'.2.1, hregisters'.2.2,
      hbuffer'.1, ?_⟩
    change (choice.buffer.map (fun record => (record.calendarRound, record.pilot))).Nodup
    exact hbuffer'.2.1
  exact ⟨hlocal, hstateInput,
    operation_input_of_local_domains choice hregisters' hbuffer' hdecoder'⟩

private theorem prepare_ordinary_from_actual_start
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstart : ActiveFollowerLifecycle.startRound rate.eta time before beforeMemory =
      .ok (state, memory))
    (hdomain : ActiveFollowerQueueOperation.stateInputDomain state)
    (hzero : state.status = .unoccupied → state.lastDown = none →
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0)
    (hrecord : state.status ≠ .unoccupied → ∃ M, state.lastDown = some M) :
    (DeclaredFollowerLocalRound.prepare rate i row activation time active
      (.ordinary before beforeMemory)).configuration = .ordinary state memory := by
  classical
  have hupAdmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    cases hlast : state.lastDown with
    | some M =>
      simp only [OrdinaryMessageCodec.upAdmissible,
        ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast]
      exact Or.inr ⟨M.property.1, M.property.2.1, hdomain.1,
        hdomain.2.1, hdomain.2.2.1⟩
    | none =>
      have hu : state.status = .unoccupied := by
        by_contra h
        obtain ⟨M, hM⟩ := hrecord h
        rw [hlast] at hM
        cases hM
      obtain ⟨hS, hdelta, hbacklog⟩ := hzero hu hlast
      simp [OrdinaryMessageCodec.upAdmissible,
        ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hlast, hS, hdelta,
        hbacklog, OrdinaryMessageCodec.upPlaceholder]
  have hqueueDomain : ActiveFollowerArmChoice.upStateDomain state :=
    ⟨hdomain.1, hdomain.2.1, hdomain.2.2.1⟩
  by_cases hu : state.status = .unoccupied
  · by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound
        i row activation time
    · have hslot : PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.upSlot := hselected.2.1
      have hi : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row.2 time).1 = i := hselected.2.2
      let offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) :=
        ⟨ActiveFollowerQueueOperation.upOfferFields state, hupAdmissible⟩
      have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row
          activation time state = .offer offered := by
        simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain,
          hselected, hu, hupAdmissible, offered]
      have hmatch : ActiveFollowerArmChoice.offeredUpMatchesState state offered :=
        ⟨rfl, rfl, rfl, rfl⟩
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (row.2 time) i offered hu hslot hi ⟨hqueueDomain, hmatch⟩
      obtain ⟨_, hprepared⟩ := DeclaredFollowerLocalRound.prepare_offer_arm_equation
        rate i row activation time active before state beforeMemory memory hstart
        offered hoff
      have hresult := hprepared _ (by
        simpa only [ActiveFollowerArmChoice.followerArmChoice] using hchoice)
      exact hresult.2
    · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound
          i row activation time ∧ state.status = .unoccupied) :=
        fun h => hselected h.1
      have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row
        activation time state hdomain hnot
      have hnotUp : ¬ (PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (row.2 time).1 = i) := by
        intro h
        exact hselected ⟨active, h.1, h.2⟩
      by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.dataSlot
      · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
          state (row.2 time) i none hu hdata
        obtain ⟨_, hprepared⟩ := DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
          rate i row activation time active before state beforeMemory memory hstart hoff
        have hresult := hprepared _ (by
          simpa only [ActiveFollowerArmChoice.followerArmChoice] using hchoice)
        exact hresult.2
      · have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
          state (row.2 time) i none hu hdata hnotUp
        obtain ⟨_, hprepared⟩ := DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
          rate i row activation time active before state beforeMemory memory hstart hoff
        have hresult := hprepared _ (by
          simpa only [ActiveFollowerArmChoice.followerArmChoice] using hchoice)
        exact hresult.2
  · have hnot : ¬ (ActiveFollowerQueueOperation.selectedUpRound
        i row activation time ∧ state.status = .unoccupied) :=
      fun h => hu h.2
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row
      activation time state hdomain hnot
    obtain ⟨M, hM⟩ := hrecord hu
    have hchoice : ∃ arm, ActiveFollowerArmChoice.followerArmChoiceCore state
        (row.2 time) i none = some arm := by
      cases hstatus : state.status with
      | unoccupied => exact (hu hstatus).elim
      | released =>
          exact ⟨PrelaunchBufferRecovery.downArm rate.eta M,
            ActiveFollowerArmChoice.followerArmChoiceCore_occupied_data_or_released
              state (row.2 time) i none M hu hM (Or.inl hstatus)⟩
      | pending =>
          by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 time).1 =
              PublicDiscreteDraws.dataSlot
          · exact ⟨PrelaunchBufferRecovery.downArm rate.eta M,
              ActiveFollowerArmChoice.followerArmChoiceCore_occupied_data_or_released
                state (row.2 time) i none M hu hM (Or.inr hdata)⟩
          · have hnotdata : PublicDiscreteDraws.slotDraw (row.2 time).1 ≠
                PublicDiscreteDraws.dataSlot := hdata
            by_cases hfirst :
                PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot ∧
                  PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                    (row.2 time).1 = i ∧
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                    (row.2 time).1).val
                    (ActiveRoundActions.coordinator p.two_le_m) =
                    ActiveFollowerArmChoice.downAuxiliaryArm rate.eta M
            · exact ⟨ActiveFollowerArmChoice.downAuxiliaryArm rate.eta M,
                ActiveFollowerArmChoice.followerArmChoiceCore_pending_selected_up_escape
                  state (row.2 time) i none M hstatus hM hfirst.1 hfirst.2.1
                  hfirst.2.2⟩
            · by_cases hcollision :
                  (PublicDiscreteDraws.slotDraw (row.2 time).1 =
                      PublicDiscreteDraws.downSlot ∧
                    PrelaunchBufferRecovery.downArm rate.eta M =
                      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                        (row.2 time).1).val
                        (PublicDiscreteDraws.followerPlayer p.two_le_m
                          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m
                            p.m_lt_K (row.2 time).1))) ∨
                  (PublicDiscreteDraws.slotDraw (row.2 time).1 =
                      PublicDiscreteDraws.upSlot ∧
                    PrelaunchBufferRecovery.downArm rate.eta M =
                      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                        (row.2 time).1).val
                        (ActiveRoundActions.coordinator p.two_le_m))
              · exact ⟨ActiveFollowerArmChoice.downAuxiliaryArm rate.eta M,
                  ActiveFollowerArmChoice.followerArmChoiceCore_pending_collision_escape
                    state (row.2 time) i none M hstatus hM hcollision⟩
              · exact ⟨PrelaunchBufferRecovery.downArm rate.eta M,
                  ActiveFollowerArmChoice.followerArmChoiceCore_pending_own_arm
                    state (row.2 time) i none M hstatus hM hnotdata hfirst hcollision⟩
    obtain ⟨arm, hcore⟩ := hchoice
    have hchoice' : ActiveFollowerArmChoice.followerArmChoice state row time i none =
        some arm := by
      simpa only [ActiveFollowerArmChoice.followerArmChoice] using hcore
    obtain ⟨_, hprepared⟩ := DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
      rate i row activation time active before state beforeMemory memory hstart hoff
    have hresult := hprepared arm hchoice'
    exact hresult.2

private theorem actual_choice_eq_prepare
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : record.input.state.followers i = .ordinary state memory) :
    ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (.ordinary state memory) := by
  change record.output.preparation.followers.followers i = _
  rw [record.output_eq]
  change (ReferenceActivePhysicalStep.prepare record.input).followers.followers i = _
  rw [(ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i]
  rw [ReferenceActiveFeedbackCut.prepareFollowers_apply]
  dsimp only [ReferenceActivePhysicalStep.followerInput]
  rw [hinput]
  rfl

/-- Construct the actual ordinary PREPARE choice from its ordinary INPUT on
every record of the complete original-source suffix. All local domains,
start-round evidence, offer validity, and arm branches come from that record
and the admitted public history APIs. -/
theorem complete_ordinary_input_prepare
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
    let r := R[k.val]
    ∀ (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
    r.input.state.followers i = .ordinary state memory →
    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
      ActiveFollowerLifecycle.localStateDomainValid state ∧
      ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
        .ok (choice, memory) ∧
      (ReferenceFollowerFixedReply.actualChoice r i).configuration =
        .ordinary choice memory ∧
      ActiveFollowerLifecycle.localStateDomainValid choice ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate choice := by
  classical
  dsimp only
  intro k i state memory hinput
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let r := R[k.val]
  change r.input.state.followers i = .ordinary state memory at hinput
  have hinputGet : (R.get k).input.state.followers i = .ordinary state memory := by
    simpa only [List.get_eq_getElem] using hinput
  have hactive : (r.input.state.activations i).val ≤ r.input.time.val + 1 :=
    r.input.active i
  have hbufferFull :=
    ReferenceFirstReplacementLiveFollowerPrefix.complete_input_buffer_chronological
    rate source rewards C_star C_h k i state memory (by
      simpa only [r, List.get_eq_getElem] using hinputGet)
  have hbuffer : ActiveFollowerLifecycle.localBufferValid state := hbufferFull.1
  obtain ⟨hc, hspan, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source k
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hc
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate source rewards C_star C_h hc
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  have hspanPrefix : start + k.val ≤ p.T := by
    dsimp only [start] at hspan ⊢
    omega
  obtain ⟨launched, hlaunch, hseed⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
      rate source rewards C_star C_h hc
  have hlaunchInitial : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hc
  have hlaunched : launched = initial := Option.some.inj (hlaunch.symm.trans hlaunchInitial)
  subst launched
  have hinputPrefix :
      (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start k.val hspanPrefix seed.activeAtStart).finalState.followers i =
        .ordinary state memory := by
    have hinputActualRecord :
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start k.val hspan seed.activeAtStart).input.state.followers i =
          .ordinary state memory := by
      rw [hrecord] at hinputGet
      simpa only [R] using hinputGet
    have hinputRun :
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start k.val (by omega) seed.activeAtStart).input.state.followers i =
          .ordinary state memory := by
      exact hinputActualRecord
    simpa only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt] using hinputRun
  have hdownEndpoint := ReferenceFollowerDecoderChronology.run_downBatch_spec
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    start k.val hspanPrefix seed.activeAtStart hseed i state memory hinputPrefix
  have hdecoder : ActiveFollowerLifecycle.downDecoderStateValid state :=
    hdownEndpoint.1.1
  cases hlast : state.lastDown with
  | none =>
      have hnoDown := ReferenceAssignmentFollowerMassSteps.complete_no_down_input
        rate rewards C_star C_h source k i state memory hinput hlast
      have hregisters : ActiveFollowerLifecycle.serviceRegistersValid p state := by
        rcases hnoDown with ⟨hS, hdelta, hbacklog, _hstatus⟩
        exact ⟨by simp [hS], by simp [hdelta], by simp [hbacklog]⟩
      have hzero : state.status = .unoccupied → state.lastDown = none →
          state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 := by
        intro _ hnone
        obtain ⟨hS, hdelta, hbacklog, _⟩ :=
          ReferenceAssignmentFollowerMassSteps.complete_no_down_input
            rate rewards C_star C_h source k i state memory hinput hnone
        exact ⟨hS, hdelta, hbacklog⟩
      have hunoccupied : state.status = .unoccupied := hnoDown.2.2.2
      have hlocal : ActiveFollowerLifecycle.localStateDomainValid state :=
        ⟨hregisters, hbuffer, hdecoder⟩
      let choice := state
      have hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
          .ok (choice, memory) := by
        simpa only [choice] using ActiveFollowerLifecycle.startRound_unoccupied
          rate.eta r.input.time state memory hlocal hunoccupied
      have hdomains := started_state_domains r.input.time state choice memory hstart
        hregisters hbuffer hdecoder
      have hstateInput : ActiveFollowerQueueOperation.stateInputDomain choice :=
        hdomains.2.1
      have hrecord : choice.status ≠ .unoccupied → ∃ M, choice.lastDown = some M := by
        intro hbusy
        exact (hbusy hunoccupied).elim
      have hprepared := prepare_ordinary_from_actual_start i r.input.row
        (r.input.state.activations i) r.input.time hactive state memory choice memory
        hstart hstateInput hzero hrecord
      have hactual := actual_choice_eq_prepare r i state memory hinput
      refine ⟨choice, hlocal, hstart, ?_, hdomains.1, hdomains.2.2⟩
      have hconfiguration := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
        hactual
      exact hconfiguration.trans hprepared
  | some M =>
      obtain ⟨b, j, P, beta, hbj, hjk, hbirth, hbase, hretained, hpayload, hmass,
        hdelta⟩ := ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_input_mass
          (rate := rate) rewards C_star C_h source k i state memory hinput M hlast
      have hserviceBound : beta i + state.S + state.backlog ≤ p.T * D p := by
        have hcutoffBound :
            Nat.min r.input.time.val
              (FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
                (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) - 1)
              ≤ p.T := by
          exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_of_lt r.input.time.isLt)
        exact Nat.le_trans hmass (Nat.mul_le_mul_right (D p) hcutoffBound)
      have hregisters : ActiveFollowerLifecycle.serviceRegistersValid p state := by
        exact ⟨by omega, hdelta, by omega⟩
      have hzero : state.status = .unoccupied → state.lastDown = none →
          state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 := by
        intro _ hnone
        rw [hlast] at hnone
        cases hnone
      have hrecord : state.status ≠ .unoccupied → ∃ M, state.lastDown = some M := by
        intro _
        exact ⟨M, hlast⟩
      have hlocal : ActiveFollowerLifecycle.localStateDomainValid state :=
        ⟨hregisters, hbuffer, hdecoder⟩
      have htimeBirth := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[b.val] P hbirth
      have hfields := congrArg OrdinaryMessageCodec.DownFields.sigma (P.downRecord_fields i)
      have hstoredSigma : M.val.sigma = P.sigma.val + 1 := by
        rw [hpayload]
        exact hfields
      have htimeBirthRecord := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source b
      have htimeCurrent := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h source k
      have hstarted : M.val.sigma ≤ r.input.time.val := by
        rw [hstoredSigma, htimeBirth, htimeBirthRecord, htimeCurrent]
        omega
      by_cases hunoccupied : state.status = .unoccupied
      · let choice := state
        have hstart : ActiveFollowerLifecycle.startRound rate.eta r.input.time state memory =
            .ok (choice, memory) := by
          simpa only [choice] using ActiveFollowerLifecycle.startRound_unoccupied
            rate.eta r.input.time state memory hlocal hunoccupied
        have hdomains := started_state_domains r.input.time state choice memory hstart
          hregisters hbuffer hdecoder
        have hlastChoice : choice.lastDown = some M := by
          simpa only [choice] using hlast
        have hzeroChoice : choice.status = .unoccupied → choice.lastDown = none →
            choice.S = 0 ∧ choice.delta = 0 ∧ choice.backlog = 0 := by
          intro _ hnone
          rw [hlastChoice] at hnone
          cases hnone
        have hrecordChoice : choice.status ≠ .unoccupied →
            ∃ M, choice.lastDown = some M := by
          intro _
          exact ⟨M, hlastChoice⟩
        have hprepared := prepare_ordinary_from_actual_start i r.input.row
          (r.input.state.activations i) r.input.time hactive state memory choice memory
          hstart hdomains.2.1 hzeroChoice hrecordChoice
        have hactual := actual_choice_eq_prepare r i state memory hinput
        refine ⟨choice, hlocal, hstart, ?_, hdomains.1, hdomains.2.2⟩
        have hconfiguration := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
          hactual
        exact hconfiguration.trans hprepared
      · have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
          rate rewards C_star C_h source k i state memory hinput M hlast
        have hcutoffPast : ¬ FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate M)
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤
              r.input.time.val := by
          intro hcutoff
          exact hunoccupied (hphase.mpr hcutoff)
        have hcutoffBounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
          rate.eta.property rate.sourceCap (ActiveFollowerLifecycle.acceptedStartCoordinate M)
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row)
        have hnotmissed : r.input.time.val + 1 ≤
            FollowerCutoffScan.gridBoundary p rate.eta.val
              (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
          have hcutoffAfter := Nat.lt_of_not_ge hcutoffPast
          have hacceptedStart :
              (ActiveFollowerLifecycle.acceptedStartCoordinate M).val + 1 = M.val.sigma := by
            have hsigma := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
            dsimp only [ActiveFollowerLifecycle.acceptedStartCoordinate]
            exact Nat.sub_add_cancel hsigma
          have hsameStart :
              ActiveFollowerDownAcceptance.downStart p rate M =
                ActiveFollowerLifecycle.acceptedStartCoordinate M := by
            apply Fin.ext
            exact Nat.add_right_cancel (by
              rw [ActiveFollowerDownAcceptance.downStart_val_add_one,
                hacceptedStart])
          rw [hsameStart] at hcutoffAfter
          exact Nat.le_trans (by omega) hcutoffBounds.2
        obtain ⟨stamp, hstamp, htoken⟩ :=
          ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
            rate rewards C_star C_h source k i state memory hinput hunoccupied
        let token : ActiveFollowerLifecycle.ProposalRead p :=
          ⟨stamp, FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row stamp⟩
        have hread : memory.lastProposalRead = some token := by
          simpa only [token] using htoken
        have hprior : ActiveFollowerLifecycle.isPriorProposalRead r.input.time token := by
          simpa only [ActiveFollowerLifecycle.isPriorProposalRead, token] using hstamp
        let choice : ReferencePrelaunchFollower.State p rate.eta :=
          { state with status :=
              if (FollowerCutoffScan.gridBoundary p rate.eta.val
                  (ActiveFollowerLifecycle.acceptedStartCoordinate M) =
                    r.input.time.val + 1 || token.bit) then
                .unoccupied else state.status }
        have hstart := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta
          r.input.time state memory hunoccupied hlocal M hlast hstarted hnotmissed
          token hread hprior
        have hdomains := started_state_domains r.input.time state choice memory hstart
          hregisters hbuffer hdecoder
        have hlastChoice : choice.lastDown = some M := by
          simpa only [choice] using hlast
        have hzeroChoice : choice.status = .unoccupied → choice.lastDown = none →
            choice.S = 0 ∧ choice.delta = 0 ∧ choice.backlog = 0 := by
          intro _ hnone
          rw [hlastChoice] at hnone
          cases hnone
        have hrecordChoice : choice.status ≠ .unoccupied →
            ∃ M, choice.lastDown = some M := by
          intro _
          exact ⟨M, hlastChoice⟩
        have hprepared := prepare_ordinary_from_actual_start i r.input.row
          (r.input.state.activations i) r.input.time hactive state memory choice memory
          hstart hdomains.2.1 hzeroChoice hrecordChoice
        have hactual := actual_choice_eq_prepare r i state memory hinput
        refine ⟨choice, hlocal, hstart, ?_, hdomains.1, hdomains.2.2⟩
        have hconfiguration := congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
          hactual
        exact hconfiguration.trans hprepared

end Bandits.Support.ReferenceCompleteFollowerPreparation

end
