/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpSitePayloadOrder
public import Bandits.Support.ReferenceGeneratedUpUnoccupiedGuard

/-!
# Actual repeated-UP fixed-reply suffix

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,92-109,139-157`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-296,327-348,355-361`,
and `sources/zip4/manuscript/08_main_theorem.tex:29-42`.

A repeated actual checked offer seeds an ordinary unoccupied suffix. At every
subsequent real round, terminal-site ancestry and the local guard producer
construct its successor. This removes the terminal ordinary premise from UP
stale-candidate survival on the same actual completed batch. These are internal
deterministic results through the physical horizon, without an overflow stop,
DOWN counterpart, global exceptional-event inclusion, tail bound, or closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceAssignmentPayloadChronology
open ReferenceFollowerFixedReply
open ReferenceFollowerReplyChronology
open ReferencePrelaunchFollower
open DeclaredFollowerLocalRound
open ReferenceGeneratedUpBatchPrefixEvent
open ReferenceGeneratedUpPrefixPositiveHalf
open ReferenceGeneratedUpSourceCalendar
open AdaptiveAffineBatchTail

namespace Bandits.Support.ReferenceGeneratedUpFixedReplySuffix

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem record_time_index
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records) :
    s ≤ record.input.time.val ∧
      (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records[
        record.input.time.val - s]? = some record := by
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hn
  have hlen := run_record_count input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s count hspan input.property
  have hnCount : n < count := by
    change n < (ReferenceActivePhysicalHorizon.run _ _ _ _ _ _ _ _).records.length at hlt
    omega
  have htimes := run_time_values input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
    s count hspan input.property
  have he := congrArg (fun xs : List ℕ => xs[n]?) htimes
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput] at hn
  rw [List.getElem?_map, hn] at he
  have htime : record.input.time.val = s + n := by
    simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hnCount, ite_true, Nat.one_mul,
      Option.map_some, Option.some.injEq] using he
  constructor
  · omega
  · simpa only [ReferenceActiveHorizonMeasurability.runOfInput, htime, Nat.add_sub_cancel_left] using hn

private theorem original_current_eq_actual_record
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z =
      actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
        s (t.val - s) (by omega) input.property := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hentry : (⟨t.val, hs, t.isLt⟩ : CalendarEntry p s) =
      ⟨s + (t.val - s), by omega, by omega⟩ := Subtype.ext (Nat.add_sub_of_le hs).symm
  exact congrArg (fun entry : CalendarEntry p s =>
    actualStepRecord (roundInputAt input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
      s input.property (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s (t.val - s) (by omega) input.property) entry)) hentry

private theorem channel_up_fields
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (h : ReferenceSelectedAffinePairLaw.selectedChannel p (x.row.2 x.time).1 = some (1, i)) :
    PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot ∧
      upSenderIndex x = i := by
  by_cases hd : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot
  · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hd] at h
    have hn : (0 : Fin 2) ≠ 1 := by decide
    exact (hn (congrArg Prod.fst (Option.some.inj h))).elim
  · by_cases hu : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot
    · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hu] at h
      exact ⟨hu, (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x).trans
        (congrArg Prod.snd (Option.some.inj h))⟩
    · simp only [ReferenceSelectedAffinePairLaw.selectedChannel,
        ReferenceSelectedAffinePairLaw.channelFromDraws, hd, hu, ite_false] at h
      cases h

private theorem record_test_fields (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : Test (AffineBatchDecoder.width p))
    (htest : upTestOfDiagnostic i record.output.coordinator.up = some test) :
    test.time = record.input.time.val ∧
      test.sample = ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.upSent record.input ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true ∧
      ReferenceSelectedAffinePairLaw.selectedChannel p (record.input.row.2 record.input.time).1 =
        some (1, i) := by
  obtain ⟨d, hd, htime, hsample, hsent⟩ :=
    ReferenceGeneratedUpResetPrefixBridge.evidenceUpTest_sender_fields i record test htest
  have hcondition : d.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
    rw [hd] at htest
    by_contra hn
    simp only [upTestOfDiagnostic, hn, ↓reduceIte, reduceCtorEq] at htest
  obtain ⟨other, ho, ht, hs, _⟩ := actualRecordUpTest_fields i record d hd
    hcondition.1 hcondition.2
  have htestD : upTestOfDiagnostic i (some d) = some test := by
    simpa only [hd] using htest
  have heq : test = other := Option.some.inj (htestD.symm.trans ho)
  obtain ⟨ledger, _, _, _, htime', _, hdraw, _, hslot, _, hgate, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record d hd
  have hselected := hcondition.2.1
  rw [hgate] at hselected
  have hup : d.input.slot = PublicDiscreteDraws.upSlot := (of_decide_eq_true hselected).2.1
  have hfollower : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i := hdraw.symm.trans hcondition.1
  refine ⟨htime.trans (congrArg Fin.val htime'), ?_, ?_, ?_, ?_⟩
  · exact (congrArg Test.sample heq).trans hs
  · exact hsent.trans (actualRecordUpDiagnostic_expected record d hd)
  · rw [ReferenceActiveAffinePositiveTest.record_upPositive, hd]
    simp only [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hcondition.2, decide_true]
  · change ReferenceSelectedAffinePairLaw.selectedChannel p
      ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i)
    have hfollower' : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((record.input.rows record.input.selected).2 record.input.time).1 = i := hfollower
    rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ (hslot.symm.trans hup),
      hfollower']
    rfl

private theorem no_selection_next_dagger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hnone : (prepare x).coordinator.selection = none) :
    (step x).next.coordinator = .dagger := by
  change (prepare x).observeCoordinator.configuration = .dagger
  unfold PreparedRound.observeCoordinator
  rw [dite_eq_left hnone]
  cases (prepare x).coordinator <;> rfl

/-- The seed round is selected UP: logging emits nothing, DOWN is skipped,
and unoccupied release/finish preserve the whole state and memory. -/
private theorem selected_up_seed_step
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hu : state.status = .unoccupied)
    (hslot : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
      PublicDiscreteDraws.upSlot)
    (hdom : ActiveFollowerLifecycle.localStateDomainValid state) :
    record.output.next.followers i = .ordinary state memory := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have halign := record.output.preparation.follower_alignment i
  have hnData : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
      PublicDiscreteDraws.dataSlot := by rw [hslot]; decide
  have hnDown : ¬ ActiveFollowerDownAcceptance.downSelected p i record.input.row
      record.input.time := by
    intro h
    exact (by decide : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.downSlot)
      (hslot.symm.trans h.1)
  have hlogNil : logAt i record.input.row (record.input.state.activations i)
      record.input.time (prepared.arm, observation) = [] := by
    apply ActiveFollowerLogging.logAt_eq_nil_of_not_tests
    intro h
    exact hnData ((loggingTestsPass_iff _ _ _ _ _).mp h).2.1
  have hlog : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
      prepared.activation prepared.time (prepared.arm, observation) state = .ok state := by
    rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    have hupdate : ActiveFollowerLogging.loggingUpdate i record.input.row
        (record.input.state.activations i) record.input.time
        (prepared.arm, observation) state = state := by
      unfold ActiveFollowerLogging.loggingUpdate
      split <;> simp only [hlogNil, List.append_nil]
    simp only [ActiveFollowerLogging.checkedLogging, dite_eq_left hdom.2.1, hupdate]
  have hrecord : (ReferenceActivePhysicalStep.recordFollower
      record.output.preparation.coordinator.downView prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation state).result =
        .ok state := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hu, hlog]
    rw [halign.1, halign.2.1, halign.2.2.1]
    simp only [ReferenceDownReception.referenceDownCut, dite_eq_right hnDown,
      DeclaredFollowerLocalRound.consumeDownResult]
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta
    prepared.follower prepared.time
    (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
    observation state state hu
  have hfinish := ActiveFollowerLifecycle.finishRound_unoccupied rate.eta
    prepared.time prepared.row state memory hdom hu
  have htail : releaseAndFinish rate prepared.follower prepared.row prepared.time
      observation state memory state = .ok (state, memory) := by
    unfold releaseAndFinish
    rw [hrelease]
    simp only [hfinish]
  have hf := ReferenceActivePhysicalStep.finishFollower_success
    record.output.preparation.coordinator.downView prepared observation
    state state state memory memory hprepared hrecord htail
  have hn : record.output.next.followers i = (record.output.followers i).configuration := by
    rw [record.output_eq]
    rfl
  rw [hn, ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower]
  exact hf.1


private theorem full_get_actual (s : ℕ)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (k : ℕ) (hk : s + (k + 1) ≤ p.T) :
    (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records[k]? =
      some (actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2
        s k hk input.property) := by
  obtain ⟨suffix, hsplit⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (k + 1)
      (p.T - s - (k + 1)) (by omega) input.property
  have hcount : k + 1 + (p.T - s - (k + 1)) = p.T - s := by omega
  simp only [hcount] at hsplit
  change (ReferenceActivePhysicalHorizon.run _ _ _ _ _ _ _ _).records[k]? = _
  rw [hsplit, List.getElem?_append_left (by rw [run_record_count]; omega),
    run_successor_actualRunRecordAt,
    List.getElem?_append_right (by rw [run_record_count])]
  simp only [run_record_count, Nat.sub_self, List.getElem?_cons_zero]

/-- A real earlier sent copy of the locally accepted wrong candidate produces
an ordinary terminal PREPARE. The additional inputs are one actual record's
membership, time bound, selected channel, and sent word; no suffix law, guard,
selection family, or ordinary endpoint is supplied. -/
theorem actual_wrong_local_up_repeated_record_prepare
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hv : d.raw = some v) (hl : d.locallyAccepted = true) (hw : some v ≠ d.expected)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmem : record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
      (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z)).records)
    (hle : record.input.time.val ≤ t.val)
    (hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      (record.input.row.2 record.input.time).1 = some (1, i))
    (hsent : ReferenceActiveAffinePositiveTest.upSent record.input = some v) :
    ∃ state memory,
      ((prepare (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).input).followers.followers i).configuration =
          .ordinary state memory ∧ state.status = .unoccupied ∧
      1 ≤ acceptedStart state := by
  classical
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  let c := t.val - s
  let a := record.input.time.val - s
  obtain ⟨L, M, hsite, _, _, _, hrawParsed, haccept, _, _, _⟩ :=
    ReferenceGeneratedUpFalseDiagnosticCut.actual_wrong_local_up_rejected
      rewards C_star C_h q t s hs control0 i z d hd hi v hv hl hw
  obtain ⟨_, _, _, _, _, hraw, _, _, _, hexpected, _⟩ :=
    ReferenceGeneratedUpBatchCalendar.record_up_executed_fields current d hd
  have hparse : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
      (some v) = some M := by
    simpa only [ReferenceUpReception.rawParsedOutput, ← hraw, hv] using hrawParsed
  have hsigma : M.val.sigma = L.sigma := by
    have hchecks := haccept
    simp only [CoordinatorCollectionLedger.acceptUpCheck, Bool.and_eq_true,
      decide_eq_true_eq] at hchecks
    exact hchecks.2.2
  have hpositive : 1 ≤ L.sigma := by
    obtain ⟨payload, _, selected, _, _, heq⟩ :=
      ReferenceGeneratedUpSitePayloadOrder.original_source_site_selected_payload
        rewards C_star C_h q t s hs control0 i z L hsite
    omega
  obtain ⟨hstart, hget⟩ := record_time_index s (p.T - s) (by omega) input record hmem
  have haSpan : s + (a + 1) ≤ p.T := by dsimp only [a]; omega
  have hrecord : record = actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1
      input.val.2.2.2 s a haSpan input.property :=
    Option.some.inj (hget.symm.trans (full_get_actual s input a haSpan))
  have hcurrent := original_current_eq_actual_record rewards C_star C_h q t s hs control0 i z
  have hac : a < c := by
    have hacle : a ≤ c := Nat.sub_le_sub_right hle s
    by_contra hn
    have he : a = c := by omega
    have heRecord : record = current := by
      rw [hrecord]
      dsimp only [current]
      rw [hcurrent]
      congr 1
    apply hw
    rw [heRecord] at hsent
    exact hsent.symm.trans hexpected.symm
  have hsender := (channel_up_fields record.input i hchannel).2
  rw [ReferenceUpPhysicalHashRule.upSent_eq_configuration, hsender] at hsent
  cases hchoice : ((prepare record.input).followers.followers i).configuration with
  | dagger => simp only [hchoice] at hsent; cases hsent
  | ordinary left memory =>
    rw [hchoice] at hsent
    dsimp only at hsent
    cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i record.input.row
        (record.input.state.activations i) record.input.time left with
    | failure => simp only [hoff] at hsent; cases hsent
    | noOffer => simp only [hoff] at hsent; cases hsent
    | offer old =>
      rw [hoff] at hsent
      have hword := Option.some.inj hsent
      have hparseOld : CoordinatorUpReception.parseDecoderOutput (p := p) (eta := rate.eta.val)
          (some (ActiveFollowerArmChoice.offeredUpWord rate.eta old)) = some old := by
        change OrdinaryMessageCodec.parseUp (codecParams p rate.eta)
          (some ((OrdinaryMessageCodec.wordEquivFlat (codecParams p rate.eta)).symm
            ((OrdinaryMessageCodec.wordEquivFlat (codecParams p rate.eta))
              (OrdinaryMessageCodec.encodeUp (codecParams p rate.eta) old)))) = some old
        rw [Equiv.symm_apply_apply, OrdinaryMessageCodec.parseUp_encode]
      rw [hword] at hparseOld
      have hM : old = M := Option.some.inj (hparseOld.symm.trans hparse)
      have hfields := ActiveFollowerQueueOperation.checkedUpOffer_fields rate.eta
        i record.input.row (record.input.state.activations i) record.input.time left old hoff
      have hleftStart : acceptedStart left = L.sigma := by
        have he := congrArg OrdinaryMessageCodec.UpFields.sigma hfields
        change old.val.sigma = acceptedStart left at he
        rw [hM, hsigma] at he
        exact he.symm
      have hu := (ReferenceUpPhysicalHashRule.checked_offer_facts
        i record.input.row (record.input.state.activations i) record.input.time left old hoff).2.1
      have hprep : (record.output.preparation.followers.followers i).configuration =
          .ordinary left memory := by rw [record.output_eq]; exact hchoice
      have hdeclared : (DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i)).configuration = .ordinary left memory := by
        have hp := record.output.preparation.followers.followers_eq i
        change record.output.preparation.followers.followers i =
          DeclaredFollowerLocalRound.prepare rate i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.input.state.followers i) at hp
        rw [← hp]
        exact hprep
      obtain ⟨before, beforeMemory, hbefore, hstarted, _, _⟩ :=
        prepare_ordinary_inversion i record.input.row (record.input.state.activations i)
          record.input.time (record.input.active i) _ left memory hdeclared
      have hbeforePrefix : (ReferenceActiveHorizonMeasurability.runOfInput s a
          (by omega) input).finalState.followers i = .ordinary before beforeMemory := by
        rw [hrecord] at hbefore
        exact hbefore
      have hdomBefore := (ReferenceGeneratedUpUnoccupiedGuard.original_source_ordinary_follower_domains
        rewards C_star C_h q t s hs control0 i z a (by omega) before beforeMemory hbeforePrefix).1
      have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time
        before left beforeMemory memory hstarted
      have hdom : ActiveFollowerLifecycle.localStateDomainValid left := by
        simpa only [ActiveFollowerLifecycle.localStateDomainValid,
          ActiveFollowerLifecycle.serviceRegistersValid, ActiveFollowerLifecycle.localBufferValid,
          ActiveFollowerLifecycle.downDecoderStateValid, hframe.2.1, hframe.2.2.1,
          hframe.2.2.2.1, hframe.2.2.2.2.1, hframe.2.2.2.2.2.1] using hdomBefore
      have hseed := selected_up_seed_step record i left memory hprep hu
        (channel_up_fields record.input i hchannel).1 hdom
      have hseedBoundary : (ReferenceActiveHorizonMeasurability.runOfInput s (a + 1)
          (by omega) input).finalState.followers i = .ordinary left memory := by
        rw [ReferenceActiveHorizonMeasurability.runOfInput,
          run_successor_finalState_eq_actualRunRecordAt, ← hrecord]
        exact hseed
      have hsuffix : ∀ k, a + 1 ≤ k → (hkc : k ≤ c) →
          ∃ state, (ReferenceActiveHorizonMeasurability.runOfInput s k
            (by dsimp only [c] at hkc; omega) input).finalState.followers i = .ordinary state memory ∧
            state.status = .unoccupied ∧ reply state = reply left := by
        intro k hak
        induction k, hak using Nat.le_induction with
        | base =>
          intro _
          exact ⟨left, hseedBoundary, hu, rfl⟩
        | succ k hak ih =>
          intro hkc
          obtain ⟨state, hord, hstatus, hreply⟩ := ih (by omega)
          have hk : s + (k + 1) ≤ p.T := by dsimp only [c] at hkc; omega
          let real := actualRunRecordAt input.val.1 input.val.2.1 input.val.2.2.1
            input.val.2.2.2 s k hk input.property
          have hnotDagger := ReferenceGeneratedUpSitePayloadOrder.original_source_site_coordinator_prefix
            rewards C_star C_h q t s hs control0 i z L hsite (k + 1) (by omega)
          have hselection : (prepare real.input).coordinator.selection ≠ none := by
            intro hn
            have he := no_selection_next_dagger real.input hn
            change real.output.next.coordinator = .dagger at he
            dsimp only at hnotDagger
            rw [run_successor_finalState_eq_actualRunRecordAt] at hnotDagger
            exact hnotDagger he
          obtain ⟨sel, hsel⟩ := Option.ne_none_iff_exists'.mp hselection
          have hfront := ReferenceGeneratedUpSitePayloadOrder.original_source_site_selected_start_le
            rewards C_star C_h q t s hs control0 i z L hsite k (by omega) hk sel hsel
          have hstartState : acceptedStart state = L.sigma :=
            (acceptedStart_eq_of_reply_eq hreply).trans hleftStart
          have hstep := ReferenceGeneratedUpUnoccupiedGuard.original_source_unoccupied_step_of_selected_start_le
            rewards C_star C_h q t s hs control0 i z k hk state memory hord hstatus
            (by omega) sel (by exact hsel) (by omega)
          obtain ⟨post, hpost, _, hsame, hpostStatus, _⟩ := hstep.2
          refine ⟨post, ?_, hpostStatus, hsame.trans hreply⟩
          rw [ReferenceActiveHorizonMeasurability.runOfInput,
            run_successor_finalState_eq_actualRunRecordAt]
          exact hpost
      obtain ⟨terminal, hterminal, hterminalStatus, hterminalReply⟩ := hsuffix c (by omega) (le_refl _)
      have hterminalStart : acceptedStart terminal = L.sigma :=
        (acceptedStart_eq_of_reply_eq hterminalReply).trans hleftStart
      have hprepared := ReferenceGeneratedUpUnoccupiedGuard.original_source_unoccupied_prepare
        rewards C_star C_h q t s hs control0 i z c (by dsimp only [c]; omega)
        terminal memory hterminal hterminalStatus (by omega)
      refine ⟨terminal, memory, ?_, hterminalStatus, by omega⟩
      rw [hcurrent]
      exact hprepared


private theorem source_test_record
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (alpha : ℕ) (test : Test (AffineBatchDecoder.width p))
    (htest : test ∈ originalSourceTests (rate := rate)
      rewards C_star C_h q t s hs control0 alpha i z) :
    ∃ record, record ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega)
        (originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z)).records ∧
      upTestOfDiagnostic i record.output.coordinator.up = some test := by
  rw [originalSourceTests, recordsUpTests] at htest
  obtain ⟨evidence, hevidence, hproject⟩ := List.mem_filterMap.mp htest
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hevidence
  exact ⟨record, List.mem_of_mem_drop hrecord, hproject⟩

private theorem same_time_record
    (s : ℕ) (hs : s ≤ p.T) (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hl : left ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records)
    (hr : right ∈ (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records)
    (ht : left.input.time.val = right.input.time.val) : left = right := by
  have hleft := (record_time_index s (p.T - s) (by omega) input left hl).2
  have hright := (record_time_index s (p.T - s) (by omega) input right hr).2
  rw [ht] at hleft
  exact Option.some.inj (hleft.symm.trans hright)

/-- Actual wrong-UP survival on the original completed batch, with precisely
its birth, quota, time/sample projection, absent-candidate tests, and literal
original-source event membership. Terminal ordinariness is produced only in
the conditional repeated-test proof and is not a premise of this theorem.
The next consumer is completed wrong-UP batch inclusion, then inclusive
first-overflow-stopped `E_false`; neither consumer is asserted here. -/
theorem actual_wrong_local_up_survival
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some d)
    (hi : d.input.selectedFollower = i)
    (v : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hv : d.raw = some v) (hl : d.locallyAccepted = true) (hw : some v ≠ d.expected) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    let batch := (current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
      (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
    ∃ alpha, s ≤ alpha ∧ alpha ≤ t.val ∧
      upBatchBirth i s alpha input.val.1
        (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      let kept := (originalSourceTests (rate := rate)
        rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p)
      kept.length = AffineBatchDecoder.quota p ∧
      kept.map (fun test => (test.time, test.sample)) =
        batch.map (fun entry => (entry.time.val, entry.sample)) ∧
      (∀ test ∈ kept, test.sent ≠ some v) ∧
      z.val ∈ ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha v i (AffineBatchDecoder.quota p) := by
  classical
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  let batch := (current.input.state.upDecoderBank i).pending ++ [AffineBatchDecoder.entry p
    (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]
  obtain ⟨_, _, _, _, _, _, _, _, hp, hQ, _⟩ :=
    ReferenceGeneratedUpFalseDiagnosticCut.actual_wrong_local_up_rejected
      rewards C_star C_h q t s hs control0 i z d hd hi v hv hl hw
  obtain ⟨alpha, ha, hat, hbirth, hlength, _, hprojection, hrecords,
      _, _, hbatchRaw, hcandidate⟩ :=
    ReferenceGeneratedUpAwaitedBatchCoverage.actual_completed_up_candidates
      rewards C_star C_h q t s hs control0 i z d hd hi hp hQ
  let kept := (originalSourceTests (rate := rate)
    rewards C_star C_h q t s hs control0 alpha i z).take (AffineBatchDecoder.quota p)
  -- This conditional producer uses exactly A's kept tests and actual records.
  have hrepeat : ∀ test ∈ kept, test.sent = some v →
      ∃ state memory, ((prepare current.input).followers.followers i).configuration =
        .ordinary state memory ∧ state.status = .unoccupied ∧ 1 ≤ acceptedStart state := by
    intro test htest hsent
    obtain ⟨record, hmem, _, _, _, hword, _, hchannel, htime⟩ := hrecords test htest
    exact actual_wrong_local_up_repeated_record_prepare
      rewards C_star C_h q t s hs control0 i z d hd hi v hv hl hw
      record hmem htime hchannel (hword.symm.trans hsent)
  obtain ⟨otherAlpha, _, _, _, _, hotherProjection, hforces⟩ :=
    ReferenceGeneratedUpOrdinaryStaleExclusion.actual_wrong_local_up_repeat_forces_dagger
      rewards C_star C_h q t s hs control0 i z d hd hi v hv hl hw
  have hnever : ∀ test ∈ kept, test.sent ≠ some v := by
    intro test htest hsent
    -- Both projections are the SAME actual batch. Equal time coordinates
    -- identify the actual record, hence its retained sent option as well.
    have hcoordinates : (test.time, test.sample) ∈
        ((originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0
          otherAlpha i z).take (AffineBatchDecoder.quota p)).map
            (fun x => (x.time, x.sample)) := by
      rw [hotherProjection, ← hprojection]
      exact List.mem_map_of_mem htest
    obtain ⟨other, hother, heq⟩ := List.mem_map.mp hcoordinates
    obtain ⟨record, hmem, _, htime, _, hword, _⟩ := hrecords test htest
    obtain ⟨otherRecord, hotherMem, hproject⟩ := source_test_record
      rewards C_star C_h q t s hs control0 i z otherAlpha other
        (List.mem_of_mem_take hother)
    have hfields := record_test_fields i otherRecord other hproject
    have hrecordEq : otherRecord = record := same_time_record s (by omega) input otherRecord record
      hotherMem hmem (hfields.1.symm.trans ((congrArg Prod.fst heq).trans htime))
    have hotherSent : other.sent = some v := by
      rw [hrecordEq] at hfields
      exact hfields.2.2.1.trans (hword.symm.trans hsent)
    have hdagger := hforces other hother hotherSent
    obtain ⟨state, memory, hprepared, _, _⟩ := hrepeat test htest hsent
    rw [hprepared] at hdagger
    cases hdagger
  have hsolution : AffineBatchDecoder.satisfies (batch.map AffineBatchDecoder.Entry.sample) v := by
    apply (AffineBatchDecoder.satisfies_samples_iff batch v).mpr
    exact ((AffineBatchDecoder.batchOutput_eq_some_iff batch v).mp
      (hbatchRaw.symm.trans hv)).1
  exact ⟨alpha, ha, hat, hbirth, hlength, hprojection, hnever,
    (hcandidate v hsolution).mpr hnever⟩

end Bandits.Support.ReferenceGeneratedUpFixedReplySuffix
