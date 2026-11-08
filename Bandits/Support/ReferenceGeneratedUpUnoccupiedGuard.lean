/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpFalseDiagnosticCut
public import Bandits.Support.ReferenceCollectionUpReceiverLocal
public import Bandits.Support.ReferenceFollowerBufferProvenance

/-!
# Original-source unoccupied follower guards

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,28-64,92-109,139-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,195-233,246-296,327-348`,
and `sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The exports below are conditional local facts on the actual original-source
execution.  They preserve its source rows, selected private index, rewards,
and carried follower state.  They do not assert a repeated-word exclusion or
close a source-level regret claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceActiveHorizonMeasurability
open ReferenceGeneratedUpBatchPrefixEvent
open ReferenceGeneratedActivePrefixFactor
open ReferenceCorrectedInitializationLaunch
open ReferenceFollowerDecoderChronology
open ReferencePrelaunchFollower
open ActiveFollowerLifecycle
open ReferenceFollowerBufferProvenance
open ReferenceFollowerReplyChronology
open DeclaredFollowerLocalRound
open ReferenceAssignmentPayloadChronology

namespace Bandits.Support.ReferenceGeneratedUpUnoccupiedGuard

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev BufferRecord (p : Parameters) := SparseCalendarReplay.SparseCalendarRecord p.K

variable {p : Parameters} {rate : RateInput p}

private theorem finishRound_success_domain
    (eta : LearningRate) (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (state next : ReferencePrelaunchFollower.State p eta)
    (memory nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hsuccess : ActiveFollowerLifecycle.finishRound eta time row state memory =
      .ok (next, nextMemory)) :
    ActiveFollowerLifecycle.localStateDomainValid next := by
  unfold ActiveFollowerLifecycle.finishRound at hsuccess
  by_cases hdomain : ActiveFollowerLifecycle.localStateDomainValid state
  · simp only [dif_pos hdomain] at hsuccess
    by_cases hunoccupied : state.status = .unoccupied
    · simp only [hunoccupied] at hsuccess
      have hpair : (state, memory) = (next, nextMemory) :=
        Except.ok.inj hsuccess
      have hstate : state = next := congrArg Prod.fst hpair
      simpa [hstate] using hdomain
    · cases hlast : state.lastDown with
      | none => simp [hunoccupied, hlast] at hsuccess
      | some lastDown =>
          by_cases htime : lastDown.val.sigma ≤ time.val + 1
          · simp only [hunoccupied, hlast, htime] at hsuccess
            have hpair : (state, ⟨some ⟨time,
                FollowerCutoffScan.completeRowProposalBit p eta.val row time⟩⟩) =
                (next, nextMemory) := Except.ok.inj hsuccess
            have hstate : state = next := congrArg Prod.fst hpair
            simpa [hstate] using hdomain
          · simp [hunoccupied, hlast, htime] at hsuccess
  · simp [hdomain] at hsuccess

private theorem ordinary_record_output_domain
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hnext : record.output.next.followers i = .ordinary next nextMemory) :
    ActiveFollowerLifecycle.localStateDomainValid next := by
  rcases record with ⟨input, output, houtput⟩
  cases houtput
  let output := ReferenceActivePhysicalStep.step input
  let prepared := output.preparation.followers.followers i
  let observation := output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  change (ReferenceActivePhysicalStep.finishFollower _ prepared observation).configuration =
    .ordinary next nextMemory at hnext
  obtain ⟨choice, memory, post, hprepared, hrecord, hfinish, _, _⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      output.preparation.coordinator.downView
      prepared observation
      next nextMemory (by
        exact hnext)
  unfold DeclaredFollowerLocalRound.releaseAndFinish at hfinish
  cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta prepared.follower
      prepared.time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
      observation
      choice post with
  | error reason => simp [hrelease] at hfinish
  | ok released =>
      cases hround : ActiveFollowerLifecycle.finishRound rate.eta prepared.time
          prepared.row released memory with
      | error reason => simp [hrelease, hround] at hfinish
      | ok pair =>
          have hp : pair = (next, nextMemory) := by
            simpa [hrelease, hround] using hfinish
          cases hp
          exact finishRound_success_domain rate.eta prepared.time prepared.row
            released next memory nextMemory hround

private theorem original_source_seed
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
      (rate := rate) rewards C_star C_h q t s hs control0 i z
    ∃ seed : ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
        input.val.1.followers i = .ordinary seed memory ∧
        ActiveFollowerLifecycle.localStateDomainValid seed ∧
        seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ seed.buffer, saved.calendarRound ≤ s) ∧
        ReferenceFollowerDecoderChronology.downBatchEndpoint seed s ∧
        ReferenceFollowerDecoderChronology.downBatchSeed input.val.1 s := by
  dsimp only
  let launch := ReferenceGeneratedAffineHashHalf.retainedLaunchStartInputOfBranch
    (rate := rate) rewards C_star C_h q t (1, i) s hs control0 z
  let control := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s launch.1 launch.2.1 control0 control).mp launch.2.2
  let fields := ReferenceGeneratedUpBatchCalendar.retained_launch_start_fields
    rate rewards C_star C_h q t s hs control0 launch
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control launch.1
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  have hsourceFacts := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control launch.1 fields.1 s hs hstart
  have hsource : source = z.1 := by
    dsimp [source, control]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply z.1
  have hinputLaunch := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput_launch
    rewards C_star C_h q t s hs control0 i z
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active := by
    simpa [active, source, generated] using generated.1
  obtain ⟨seedActive, hseedLaunch, hseedFields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate source rewards C_star C_h hsourceFacts.1
  have hactiveEq : seedActive = active := Option.some.inj (hseedLaunch.symm.trans hlaunch)
  have hinputActive : active = input.val.1 := by
    have hinputLaunch' :
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
          some input.val.1 := by
      rw [hsource]
      exact hinputLaunch
    exact Option.some.inj (hlaunch.symm.trans hinputLaunch')
  let initializationInput := ActualReferenceInitializationBlock.referenceInput
    source rewards C_star C_h rate
  let boundary := ReferenceInitializationRun.output initializationInput
  let seed := ReferenceInitializationRun.ordinary initializationInput boundary
    (ActualReferenceInitializationBlock.refFollower i)
  have hseedConfig : input.val.1.followers i =
      .ordinary seed (ActiveFollowerLifecycle.initialMemory p) := by
    calc
      input.val.1.followers i = active.followers i := by rw [← hinputActive]
      _ = seedActive.followers i := by rw [hactiveEq]
      _ = .ordinary seed (ActiveFollowerLifecycle.initialMemory p) := by
        simpa [seed, initializationInput, boundary] using (hseedFields i).1
  have hdomain : ActiveFollowerLifecycle.localStateDomainValid seed :=
    ReferenceActiveDataOwnership.initialization_ordinary_domain initializationInput boundary
      (ActualReferenceInitializationBlock.refFollower i)
  have hbuffer := ReferenceFollowerBufferProvenance.initialization_ordinary_buffer_valid
    initializationInput boundary (ActualReferenceInitializationBlock.refFollower i)
  have hseedStamps : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ s := by
    intro saved hsaved
    calc
      saved.calendarRound ≤ ReferenceInitializationRun.elapsed p boundary.completed :=
        hbuffer.2.2 saved hsaved
      _ = s := by simpa [boundary] using hsourceFacts.2
  have hbatchSeed : ReferenceFollowerDecoderChronology.downBatchSeed active s :=
    generated.2.2
  obtain ⟨batchSeed, batchMemory, hbatchConfig, hbatchStatus, hbatchWell,
    hbatchChronological, hbatchStamps⟩ := hbatchSeed i
  have hbatchEq : batchSeed = seed := by
    have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary batchSeed batchMemory =
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary seed
          (ActiveFollowerLifecycle.initialMemory p) :=
      hbatchConfig.symm.trans (hinputActive ▸ hseedConfig)
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
  subst batchSeed
  refine ⟨seed, ActiveFollowerLifecycle.initialMemory p, hseedConfig, hdomain,
    hbuffer.2.1, hseedStamps, ?_, ?_⟩
  · refine ⟨hbatchWell, hbatchChronological, ?_⟩
    intro entry hentry
    exact hbatchStamps entry hentry
  · rw [← hinputActive]
    exact generated.2.2

/-! The first three exports all use the same original source input and the
literal actual record at its physical calendar coordinate. -/

theorem original_source_ordinary_follower_domains
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (k : ℕ) (hk : s + k ≤ p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary :
      (ReferenceActiveHorizonMeasurability.runOfInput s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z)).finalState.followers i =
        .ordinary state memory) :
    ActiveFollowerLifecycle.localStateDomainValid state ∧
      state.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ state.buffer, saved.calendarRound ≤ s + k) ∧
      ReferenceFollowerDecoderChronology.downBatchEndpoint state (s + k) := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let run := ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s k hk input.property
  change run.finalState.followers i = .ordinary state memory at hordinary
  obtain ⟨seed, seedMemory, hseed, hseedDomain, hseedPair, hseedTimes,
    hseedEndpoint, hseedAllDecoder⟩ :=
    original_source_seed rewards C_star C_h q t s hs control0 i z
  have hbuffer := ReferenceFollowerBufferProvenance.run_buffer_chronological i
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s k hk input.property seed seedMemory hseed hseedDomain.2.1 hseedPair hseedTimes
    state memory hordinary
  have hdecoder := ReferenceFollowerDecoderChronology.run_downBatch_spec
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s k hk input.property
    hseedAllDecoder i state memory hordinary
  have hdomain : ActiveFollowerLifecycle.localStateDomainValid state := by
    by_cases hk0 : k = 0
    · subst k
      have hrun := ReferenceActivePhysicalHorizon.run_zero_final input.val.1
        input.val.2.1 input.val.2.2.1 input.val.2.2.2 s hk input.property
      rw [hrun] at hordinary
      have hconfig := hseed.symm.trans hordinary
      have hstate : seed = state :=
        (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfig).1
      simpa [hstate] using hseedDomain
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hprevSpan : s + n ≤ p.T := by omega
      let previous := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n
        (by omega) input.property
      have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s n
        (by omega) input.property
      have hsuccessor' : run.finalState = previous.output.next := by
        simpa [run, Nat.succ_eq_add_one] using hsuccessor
      have hpreviousOutput : previous.output.next.followers i = .ordinary state memory := by
        have hfinal := hordinary
        rw [hsuccessor'] at hfinal
        exact hfinal
      exact ordinary_record_output_domain previous i state memory hpreviousOutput
  refine ⟨hdomain, hbuffer.2.1, ?_, hdecoder.1⟩
  intro saved hsaved
  have hstamp := hbuffer.2.2 saved hsaved
  omega

private theorem unoccupied_prepare_config
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (time : Fin p.T)
    (active : activation.val ≤ time.val + 1)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hunoccupied : state.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state) :
    (DeclaredFollowerLocalRound.prepare rate i row activation time active
      (.ordinary state memory)).configuration = .ordinary state memory := by
  have hstart := ActiveFollowerLifecycle.startRound_unoccupied rate.eta time state memory
    hdomain hunoccupied
  have hstateInput := ActualReferenceInitializationBlock.up_domain_of_local_domain state hdomain
  have hstartBound : ReferencePrelaunchFollower.acceptedStart state ≤ p.T := by
    cases hlast : state.lastDown with
    | none => simp [ReferencePrelaunchFollower.acceptedStart, hlast] at hpositive
    | some down =>
        have hbound : down.val.sigma ≤ p.T := by
          simpa only [ReferencePrelaunchFollower.codecParams] using down.property.2.1
        simpa [ReferencePrelaunchFollower.acceptedStart, hlast] using hbound
  have hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields state) := by
    unfold OrdinaryMessageCodec.upAdmissible ActiveFollowerQueueOperation.upOfferFields
    exact Or.inr ⟨hpositive, hstartBound, hdomain.1.1, hdomain.1.2.1,
      hdomain.1.2.2⟩
  let offered : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields state, hadmissible⟩
  have hoffSelected : ∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i row
      activation time,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
        .offer offered := by
    intro hselected
    unfold ActiveFollowerQueueOperation.checkedUpOffer
    rw [dif_pos hstateInput, dif_pos ⟨hselected, hunoccupied⟩, dif_pos hadmissible]
  have hoffNotSelected : ∀ hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row
      activation time,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation time state =
        .noOffer := by
    intro hnot
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row activation time
      state hstateInput
    intro hselected
    exact hnot hselected.1
  by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.dataSlot
  · have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation time := by
      rintro ⟨_, hslot, _⟩
      have hne : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by
        decide
      exact hne (hdata.symm.trans hslot)
    have hoff := hoffNotSelected hnotSelected
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data state
      (row.2 time) i none hunoccupied hdata
    have hchoice : ActiveFollowerArmChoice.followerArmChoice state row time i none =
        some (PublicDiscreteDraws.pilotDraw (K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 time).1) := by
      rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
      exact hcore
    simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

  · by_cases hup : PublicDiscreteDraws.slotDraw (row.2 time).1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 time).1 = i
    · have hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation time :=
        ⟨active, hup.1, hup.2⟩
      have hoff := hoffSelected hselected
      have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta i row
        activation time state offered hoff
      have hvalid : ActiveFollowerArmChoice.upStateDomain state ∧
          ActiveFollowerArmChoice.offeredUpMatchesState state offered := by
        constructor
        · exact hdomain.1
        · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
            ActiveFollowerQueueOperation.upOfferFields]
      have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        state (row.2 time) i offered hunoccupied hup.1 hup.2 hvalid
      have hchoice : ActiveFollowerArmChoice.followerArmChoice state row time i (some offered) =
          some (ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 time) i offered)
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
              (ActiveRoundActions.coordinator p.two_le_m))) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]
    · have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation time := by
        intro hselected
        exact hup ⟨hselected.2.1, hselected.2.2⟩
      have hoff := hoffNotSelected hnotSelected
      have hnotPair : ¬ (PublicDiscreteDraws.slotDraw (row.2 time).1 =
          PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 time).1 = i) :=
        fun hp => hup hp
      have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
        state (row.2 time) i none hunoccupied (by simpa [hdata]) hnotPair
      have hchoice : ActiveFollowerArmChoice.followerArmChoice state row time i none =
          some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      simp [DeclaredFollowerLocalRound.prepare, hstart, hoff, hchoice]

private theorem matching_selected_down_is_unaccepted
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hfront : selected.view.payload.sigma.val + 1 ≤
      ReferencePrelaunchFollower.acceptedStart state)
    (hraw : (ActiveFollowerDownAcceptance.currentDecodeStep p i row time
      observation rate state).2 =
        ReferenceDownReception.expectedDownFlatWord (some selected.view) i row time)
    (parsed : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hparsed : ReferenceDownReception.ordinaryParse p rate
      (ActiveFollowerDownAcceptance.currentDecodeStep p i row time
        observation rate state).2 = some parsed) :
    ¬ OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart state) (time.val + 1) parsed := by
  have hparseExpected : ReferenceDownReception.ordinaryParse p rate
      (ReferenceDownReception.expectedDownFlatWord (some selected.view) i row time) =
        some parsed := by rw [← hraw]; exact hparsed
  have hmessage := ReferenceActiveDataOwnership.parse_expectedDown
    selected.view i row time parsed hparseExpected
  have hsigma : parsed.val.sigma = selected.view.payload.sigma.val + 1 := by
    rw [hmessage]
    exact congrArg OrdinaryMessageCodec.DownFields.sigma
      (selected.view.payload.downRecord_fields i)
  intro haccept
  change ReferencePrelaunchFollower.acceptedStart state < parsed.val.sigma ∧
    parsed.val.sigma ≤ time.val + 1 at haccept
  have hstrict := haccept.1
  rw [hsigma] at hstrict
  omega

private theorem unoccupied_cut_successful_rejection
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hfront : selected.view.payload.sigma.val + 1 ≤
      ReferencePrelaunchFollower.acceptedStart state)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hbatch : ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer) :
    ∃ post, DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p (some selected.view) i row time observation
        rate state).outcome = .ok post ∧
      post.status = state.status ∧ post.lastDown = state.lastDown ∧
      post.S = state.S ∧ post.delta = state.delta ∧ post.backlog = state.backlog ∧
      post.buffer = state.buffer ∧
      post.initializationFailure = state.initializationFailure ∧
      ReferenceFollowerDecoderChronology.downBatchWellFormed post.downBatch ∧
      (¬ ∃ before after raw message scan registers lastService,
        (ReferenceDownReception.referenceDownCut p (some selected.view) i row time observation
          rate state).outcome = .accepted before after raw message scan registers lastService) ∧
      (¬ ∃ before reason,
        (ReferenceDownReception.referenceDownCut p (some selected.view) i row time observation
          rate state).outcome = .outputFailure before reason) := by
  classical
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i row time observation rate state
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i row time
  · have hdecoder : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch := by
      simpa [ReferenceFollowerDecoderChronology.downBatchWellFormed,
        ActiveFollowerDownAcceptance.decoderInputDomain] using hbatch
    by_cases hmatches : decoded.2 =
        ReferenceDownReception.expectedDownFlatWord (some selected.view) i row time
    · by_cases hparsed : ReferenceDownReception.ordinaryParse p rate decoded.2 = none
      · have hparsedExpected : ReferenceDownReception.ordinaryParse p rate
            (ReferenceDownReception.expectedDownFlatWord (some selected.view) i row time) = none := by
          simpa [decoded, hmatches] using hparsed
        have hcut : (ReferenceDownReception.referenceDownCut p (some selected.view)
            i row time observation rate state).outcome =
              .decodeOrParseRejected state {state with downBatch := decoded.1} decoded.2 := by
          simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
            hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected]
        have hnextBatch : ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 := by
          simpa [decoded] using (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
            i row time observation state hbatch).1
        refine ⟨{state with downBatch := decoded.1}, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          ⟨hnextBatch, by simp [hcut], by simp [hcut]⟩⟩
        rw [hcut]
        rfl
      · cases hparsed' : ReferenceDownReception.ordinaryParse p rate decoded.2 with
        | none => exact False.elim (hparsed hparsed')
        | some parsed =>
            have hparsedExpected : ReferenceDownReception.ordinaryParse p rate
                (ReferenceDownReception.expectedDownFlatWord (some selected.view) i row time) =
                  some parsed := by
              simpa [decoded, hmatches] using hparsed'
            have hnotaccepted := matching_selected_down_is_unaccepted x selected i row time
              observation state hfront hmatches parsed hparsed'
            have hcut : (ReferenceDownReception.referenceDownCut p (some selected.view)
                i row time observation rate state).outcome =
                  .parsedButUnaccepted state {state with downBatch := decoded.1}
                    decoded.2 parsed := by
              simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
                hregisters, hdecoder, hbuffer, decoded, hmatches, hparsedExpected,
                hnotaccepted]
            have hnextBatch : ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 := by
              simpa [decoded] using (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
                i row time observation state hbatch).1
            refine ⟨{state with downBatch := decoded.1}, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              ⟨hnextBatch, by simp [hcut], by simp [hcut]⟩⟩
            rw [hcut]
            rfl
    · have hcut : (ReferenceDownReception.referenceDownCut p (some selected.view)
          i row time observation rate state).outcome =
            .decodeOrParseRejected state {state with downBatch := decoded.1} decoded.2 := by
        simp [ReferenceDownReception.referenceDownCut, hselected, hstatus,
          hregisters, hdecoder, hbuffer, decoded, hmatches]
      have hnextBatch : ReferenceFollowerDecoderChronology.downBatchWellFormed decoded.1 := by
        simpa [decoded] using (ReferenceFollowerDecoderChronology.currentDecodeStep_batch_spec
          i row time observation state hbatch).1
      refine ⟨{state with downBatch := decoded.1}, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        ⟨hnextBatch, by simp [hcut], by simp [hcut]⟩⟩
      rw [hcut]
      rfl
  · have hcut : (ReferenceDownReception.referenceDownCut p (some selected.view)
        i row time observation rate state).outcome = .skipped state .notSelectedDown := by
      simp [ReferenceDownReception.referenceDownCut, hselected]
    refine ⟨state, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      ⟨hbatch, by simp [hcut], by simp [hcut]⟩⟩
    rw [hcut]
    rfl

private theorem bufferInputDomain_of_localBufferValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid state) :
    ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
  rcases hvalid with ⟨htime, hkeys, hquantized⟩
  refine ⟨?_, hkeys⟩
  intro saved hsaved
  obtain ⟨hpositive, htimeBound⟩ := htime saved hsaved
  obtain ⟨q, hq, hobs⟩ := hquantized saved hsaved
  refine ⟨hpositive, htimeBound, ⟨⟨q, by omega⟩, ?_⟩⟩
  simpa using hobs

private theorem actual_unoccupied_selected_front_step
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hfront : selected.view.payload.sigma.val + 1 ≤
      ReferencePrelaunchFollower.acceptedStart state)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid state)
    (hbefore : ∀ saved ∈ state.buffer,
      saved.calendarRound < record.input.time.val + 1)
    (hendpoint : ReferenceFollowerDecoderChronology.downBatchEndpoint state
      record.input.time.val) :
    ∃ post,
      record.output.next.followers i = .ordinary post memory ∧
      (record.output.followers i).failure = none ∧
      ReferenceFollowerReplyChronology.reply post =
        ReferenceFollowerReplyChronology.reply state ∧
      post.status = .unoccupied ∧
      post.initializationFailure = state.initializationFailure ∧
      post.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record ∧
      ActiveFollowerLifecycle.localStateDomainValid post ∧
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
  have hlogging := ReferenceFollowerBufferProvenance.actualPreparedLogging_success
    i record state memory hprepared hdomain.2.1 hbefore hunoccupied
  obtain ⟨logged, hlogged, hown, hloggedBuffer, hloggedBufferValid⟩ := hlogging
  have halign := record.output.preparation.follower_alignment i
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hloggingPrepared : ActiveFollowerLogging.checkedLogging i prepared.row
      prepared.activation prepared.time (prepared.arm, observation) state = .ok logged := by
    rw [halign.1, halign.2.2.2, halign.2.2.1, ← hown]
    exact hlogged
  have hloggingPrepared' : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
      prepared.activation prepared.time (prepared.arm, observation) state = .ok logged := by
    rw [halign.2.1]
    exact hloggingPrepared
  obtain ⟨hlast, hS, hdelta, hbacklog, hstatus, hbatch, hinitializationFailure⟩ :=
    ActiveFollowerLogging.checkedLogging_success_frame i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      state logged hlogged
  have hloggedDomain : ActiveFollowerLifecycle.localStateDomainValid logged := by
    unfold ActiveFollowerLifecycle.localStateDomainValid
    refine ⟨?_, hloggedBufferValid, ?_⟩
    · unfold ActiveFollowerLifecycle.serviceRegistersValid
      exact ⟨by simpa [hS] using hdomain.1.1,
        by simpa [hdelta] using hdomain.1.2.1,
        by simpa [hbacklog] using hdomain.1.2.2⟩
    · simpa [ActiveFollowerLifecycle.downDecoderStateValid, hbatch] using hdomain.2.2
  have hloggedReply : ReferenceFollowerReplyChronology.reply logged =
      ReferenceFollowerReplyChronology.reply state := by
    simp [ReferenceFollowerReplyChronology.reply, hlast, hS, hdelta, hbacklog]
  have hloggedStart : ReferencePrelaunchFollower.acceptedStart logged =
      ReferencePrelaunchFollower.acceptedStart state :=
    ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hloggedReply
  have hloggedFront : selected.view.payload.sigma.val + 1 ≤
      ReferencePrelaunchFollower.acceptedStart logged := by
    calc
      selected.view.payload.sigma.val + 1 ≤
          ReferencePrelaunchFollower.acceptedStart state := hfront
      _ = ReferencePrelaunchFollower.acceptedStart logged := hloggedStart.symm
  have hloggedEndpoint : ReferenceFollowerDecoderChronology.downBatchEndpoint logged
      record.input.time.val := by
    simpa [ReferenceFollowerDecoderChronology.downBatchEndpoint, hbatch] using hendpoint
  have hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    simpa [ActiveFollowerDownAcceptance.registerInputDomain,
      ActiveFollowerLifecycle.serviceRegistersValid, hlast, hS, hdelta, hbacklog] using
      hdomain.1
  have hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer :=
    bufferInputDomain_of_localBufferValid logged hloggedBufferValid
  have hview : record.output.preparation.coordinator.downView = some selected.view := by
    simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselected]
  have hcutActual := unoccupied_cut_successful_rejection record.input selected i
    record.input.row record.input.time observation logged
    (hstatus.trans hunoccupied) hloggedFront hregisters hloggedEndpoint.1 hbuffer
  obtain ⟨afterDown, hconsume, hafterStatus, hafterLastDown, hafterS, hafterDelta,
    hafterBacklog, hafterBuffer, hafterInitializationFailure, hafterBatch,
    hnoAccepted, hnoOutputFailure⟩ := hcutActual
  have hcutPrepared : ReferenceDownReception.referenceDownCut p
      record.output.preparation.coordinator.downView
      prepared.follower prepared.row prepared.time observation rate logged =
        ReferenceDownReception.referenceDownCut p (some selected.view) i record.input.row
          record.input.time observation rate logged := by
    simp [hview, prepared, halign.1, halign.2.1, halign.2.2.1]
  have hrecordResult :
      (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).result =
          .ok afterDown := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hunoccupied,
      hloggingPrepared', hcutPrepared]
    exact hconsume
  have hafterDomain : ActiveFollowerLifecycle.localStateDomainValid afterDown := by
    unfold ActiveFollowerLifecycle.localStateDomainValid
    refine ⟨?_, ?_, ?_⟩
    · unfold ActiveFollowerLifecycle.serviceRegistersValid
      exact ⟨by simpa [hafterS, hS] using hdomain.1.1,
        by simpa [hafterDelta, hdelta] using hdomain.1.2.1,
        by simpa [hafterBacklog, hbacklog] using hdomain.1.2.2⟩
    · simpa [ActiveFollowerLifecycle.localBufferValid, hafterBuffer] using hloggedBufferValid
    · simpa [ActiveFollowerLifecycle.downDecoderStateValid,
        ReferenceFollowerDecoderChronology.downBatchWellFormed] using hafterBatch
  have hafterUnoccupied : afterDown.status = .unoccupied := by
    calc
      afterDown.status = logged.status := hafterStatus
      _ = state.status := hstatus
      _ = .unoccupied := hunoccupied
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta prepared.follower
    prepared.time (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
    observation state afterDown hunoccupied
  have hfinishRound := ActiveFollowerLifecycle.finishRound_unoccupied rate.eta prepared.time
    prepared.row afterDown memory hafterDomain hafterUnoccupied
  have hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
      observation state memory afterDown = .ok (afterDown, memory) := by
    unfold DeclaredFollowerLocalRound.releaseAndFinish
    rw [hrelease]
    simp [hfinishRound]
  have hfinishFollower := ReferenceActivePhysicalStep.finishFollower_success
    record.output.preparation.coordinator.downView prepared
    observation state afterDown afterDown memory memory hprepared hrecordResult hfinish
  have houtFollower : (record.output.followers i).configuration =
      .ordinary afterDown memory := by
    rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record]
    exact hfinishFollower.1
  have hfailure : (record.output.followers i).failure = none := by
    rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record]
    exact hfinishFollower.2
  have hnextField : record.output.next.followers i = (record.output.followers i).configuration := by
    rw [record.output_eq]
    rfl
  have hnext : record.output.next.followers i = .ordinary afterDown memory :=
    hnextField.trans houtFollower
  have hreply : ReferenceFollowerReplyChronology.reply afterDown =
      ReferenceFollowerReplyChronology.reply state := by
    calc
      ReferenceFollowerReplyChronology.reply afterDown =
          ReferenceFollowerReplyChronology.reply logged := by
        simp [ReferenceFollowerReplyChronology.reply, hafterLastDown, hafterS,
          hafterDelta, hafterBacklog]
      _ = ReferenceFollowerReplyChronology.reply state := hloggedReply
  have hbufferFinal : afterDown.buffer =
      state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record :=
    hafterBuffer.trans hloggedBuffer
  have hmarker : afterDown.initializationFailure = state.initializationFailure :=
    hafterInitializationFailure.trans hinitializationFailure
  have hnoReset : ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i record := by
    intro hreset
    rcases hreset with ⟨cut, hcut, before, after, raw, message, scan, registers,
      lastService, haccepted⟩
    let actualCut := ReferenceDownReception.referenceDownCut p (some selected.view)
      i record.input.row record.input.time observation rate logged
    have hrecordDown :
        (ReferenceActivePhysicalStep.recordFollower
          record.output.preparation.coordinator.downView prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).down =
          some actualCut := by
      simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied,
        hloggingPrepared', hcutPrepared, actualCut]
    have hfinishDown :
        (ReferenceActivePhysicalStep.finishFollower
          record.output.preparation.coordinator.downView prepared observation).down =
            some actualCut := by
      unfold ReferenceActivePhysicalStep.finishFollower
      rw [hprepared]
      simp [hrecordResult, hfinish, hrecordDown]
    have hdiagnostic : (record.output.followers i).down = some actualCut := by
      rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i record]
      simpa [prepared, observation] using hfinishDown
    have hcutEq : cut = actualCut := Option.some.inj (hcut.symm.trans hdiagnostic)
    subst cut
    exact hnoAccepted ⟨before, after, raw, message, scan, registers, lastService, haccepted⟩
  exact ⟨afterDown, hnext, hfailure, hreply, hafterUnoccupied, hmarker,
    hbufferFinal, hafterDomain, hnoReset⟩

theorem original_source_unoccupied_prepare
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (k : ℕ) (hk : s + (k + 1) ≤ p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hord :
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input.state.followers i =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state) :
    ((ReferenceActivePhysicalStep.prepare
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input).followers.followers i).configuration =
      .ordinary state memory := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s k hk input.property
  let runPrefix := ReferenceActiveHorizonMeasurability.runOfInput s k (by omega) input
  have hrecordState : record.input.state = runPrefix.finalState := by rfl
  have hprefixOrdinary : runPrefix.finalState.followers i = .ordinary state memory := by
    rw [← hrecordState]
    exact hord
  have hdomains := original_source_ordinary_follower_domains
    rewards C_star C_h q t s hs control0 i z k (by omega) state memory hprefixOrdinary
  have hdeclared := unoccupied_prepare_config i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    state memory hdomains.1 hunoccupied hpositive
  have hprepareEq : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hfollowersEq : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := by
    calc
      _ = (ReferenceActivePhysicalStep.prepare record.input).followers.followers i := by
        rw [hprepareEq]
      _ = ReferenceActiveFeedbackCut.prepareFollowers
          (ReferenceActivePhysicalStep.followerInput record.input) i :=
        (ReferenceActivePhysicalStep.prepare record.input).followers.followers_eq i
      _ = DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i) := by
        rfl
  have hactualConfig :
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory := by
    rw [hfollowersEq, hord]
    exact hdeclared
  change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
    .ordinary state memory
  rw [← hprepareEq]
  exact hactualConfig

theorem original_source_unoccupied_step_of_selected_start_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (k : ℕ) (hk : s + (k + 1) ≤ p.T)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hord :
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input.state.followers i =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart state)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input)
    (hselected :
      (ReferenceActivePhysicalStep.prepare
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
          s k hk
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input).coordinator.selection =
        some selected)
    (hfront : selected.view.payload.sigma.val + 1 ≤
      ReferencePrelaunchFollower.acceptedStart state) :
    (((ReferenceActivePhysicalStep.prepare
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).input).followers.followers i).configuration =
      .ordinary state memory) ∧
    ∃ post : ReferencePrelaunchFollower.State p rate.eta,
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).output.next.followers i =
          .ordinary post memory ∧
      ((ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
        s k hk
        (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
          (rate := rate) rewards C_star C_h q t s hs control0 i z).property).output.followers i).failure =
        none ∧
      ReferenceFollowerReplyChronology.reply post =
        ReferenceFollowerReplyChronology.reply state ∧
      post.status = .unoccupied ∧
      post.initializationFailure = state.initializationFailure ∧
      post.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
          s k hk
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).property) ∧
      ActiveFollowerLifecycle.localStateDomainValid post ∧
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ post.buffer, saved.calendarRound ≤ s + (k + 1)) ∧
      ReferenceFollowerDecoderChronology.downBatchEndpoint post (s + (k + 1)) ∧
      ¬ ReferenceFollowerBufferProvenance.acceptedDownReset i
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.1
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).val.2.2.2
          s k hk
          (ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
            (rate := rate) rewards C_star C_h q t s hs control0 i z).property) := by
  let input := ReferenceGeneratedUpBatchPrefixEvent.originalSourceRunInput
    (rate := rate) rewards C_star C_h q t s hs control0 i z
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s k hk input.property
  let runPrefix := ReferenceActiveHorizonMeasurability.runOfInput s k (by omega) input
  have hrecordState : record.input.state = runPrefix.finalState := by rfl
  have hprefixOrdinary : runPrefix.finalState.followers i = .ordinary state memory := by
    rw [← hrecordState]
    exact hord
  have hdomains := original_source_ordinary_follower_domains
    rewards C_star C_h q t s hs control0 i z k (by omega) state memory hprefixOrdinary
  have hprepared := original_source_unoccupied_prepare
    rewards C_star C_h q t s hs control0 i z k hk state memory hord hunoccupied hpositive
  have hprepareEq : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hselectedPrepare :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    simpa [record, input] using hselected
  have hselectedActual : record.output.preparation.coordinator.selection = some selected := by
    rw [hprepareEq]
    exact hselectedPrepare
  have hbefore : ∀ saved ∈ state.buffer,
      saved.calendarRound < record.input.time.val + 1 := by
    intro saved hsaved
    have hstamp := hdomains.2.2.1 saved hsaved
    have htime : record.input.time.val = s + k := by rfl
    omega
  have hstep := actual_unoccupied_selected_front_step record i state memory hprepared
    hunoccupied selected hselectedActual hfront hdomains.1 hbefore hdomains.2.2.2
  obtain ⟨post, hnext, hfailure, hreply, hstatus, hinitializationFailure,
    hbuffer, hpostDomain, hnoReset⟩ := hstep
  let runPost := ReferenceActiveHorizonMeasurability.runOfInput s (k + 1) (by omega) input
  have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s k (by omega) input.property
  have hsuccessor' : runPost.finalState = record.output.next := by
    simpa [runPost, ReferenceActiveHorizonMeasurability.runOfInput,
      record, Nat.succ_eq_add_one] using hsuccessor
  have hpostOrdinary : runPost.finalState.followers i = .ordinary post memory := by
    rw [hsuccessor']
    exact hnext
  have hpostDomains := original_source_ordinary_follower_domains
    rewards C_star C_h q t s hs control0 i z (k + 1) (by omega) post memory hpostOrdinary
  refine ⟨hprepared, post, hnext, hfailure, hreply, hstatus, hinitializationFailure,
    hbuffer, hpostDomains.1, hpostDomains.2.1, hpostDomains.2.2.1,
    hpostDomains.2.2.2, hnoReset⟩

end Bandits.Support.ReferenceGeneratedUpUnoccupiedGuard

end
