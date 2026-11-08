/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedDownBatchBankBridge

import Lean.Elab.Tactic.Omega

/-!
# Surviving DOWN prefix lists on the generated physical run

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The local converse selects an actual ordinary successor. It inverts the
physical logging and receiver checks, rather than treating an administrative
call as execution evidence. The forward diagnostic direction also covers a
test retained before a later failure. These are internal deterministic results.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support
open ReferenceFollowerDownDecoderReplay

namespace Bandits.Support.ReferenceGeneratedDownPrefixList

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem finishFollower_diagnostic_pair
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p) :
    ((ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput,
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down) =
    match prepared.configuration with
    | .dagger => (none, none)
    | .ordinary state _ =>
        let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower
          prepared.row prepared.activation prepared.time prepared.active prepared.arm
          observation state
        (recorded.downInput, recorded.down) := by
  cases hc : prepared.configuration with
  | dagger => simp only [ReferenceActivePhysicalStep.finishFollower, hc]
  | ordinary state memory =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hc]
      cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).result with
      | error failure => rfl
      | ok post =>
          dsimp only
          cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
              prepared.row prepared.time observation state memory post with
          | error failure => rfl
          | ok next => cases next; rfl

private theorem record_down_some_logged
    (record : Record p rate) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (record.output.followers i).down = some cut) :
    ∃ logged, (record.output.followers i).downInput = some logged := by
  classical
  rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics record i]
    at hcut ⊢
  have hp := finishFollower_diagnostic_pair record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i) (preparedOwnObservation record i)
  change ((record.output.preparation.observeFollower i).downInput,
    (record.output.preparation.observeFollower i).down) = _ at hp
  cases hc : (record.output.preparation.followers.followers i).configuration with
  | dagger =>
      rw [hc] at hp
      have he := congrArg Prod.snd hp
      rw [hcut] at he
      cases he
  | ordinary choice memory =>
      rw [hc] at hp
      have hd := (congrArg Prod.snd hp).symm.trans hcut
      by_cases hs : choice.status = .unoccupied
      · cases hl : ActiveFollowerLogging.checkedLogging
            (record.output.preparation.followers.followers i).follower
            (record.output.preparation.followers.followers i).row
            (record.output.preparation.followers.followers i).activation
            (record.output.preparation.followers.followers i).time
            ((record.output.preparation.followers.followers i).arm,
              preparedOwnObservation record i) choice with
        | error failure =>
            simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs, hl,
              reduceCtorEq] at hd
        | ok logged =>
            refine ⟨logged, ?_⟩
            have he := congrArg Prod.fst hp
            dsimp only at he
            rw [he]
            simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs, hl]
      · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hs,
          reduceCtorEq] at hd

private theorem preparedOwnObservation_eq_grid
    (record : Record p rate) (i : Fin (p.m - 1)) :
    preparedOwnObservation record i = ActualInitializationPhysicalStep.observationOfGrid p
      (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i) := by
  have hg := congrFun (ReferenceActiveHorizonMeasurability.roundRecordCode_front record).2.2.2
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  change ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i =
    record.gridFeedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) at hg
  rw [hg]
  exact record.output.preparation.feedback.observations_eq _

/-- Inverting D's literal selector recovers actual execution evidence and the
original sent tag, even if the follower's successor is dagger. -/
theorem executedTestOfRound_some_actual
    (record : Record p rate) (i : Fin (p.m - 1))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p)
    (htest : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some test) :
    ∃ call,
      actualDownCall i record = some call ∧ AffineBatchDecoder.eligible call.2 ∧
      test.time = call.1 ∧ test.sample = call.2.sample ∧
      test.time = record.input.time ∧
      test.sample = (record.input.row.2 record.input.time).2 (0, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.downSent record.input := by
  classical
  have htest0 := htest
  have hd := ReferenceGeneratedDownBatchBankBridge.roundDownObservation_diagnostics_eq_actual
    record i
  unfold ReferenceGeneratedDownBatchCalendar.executedTestOfRound at htest
  dsimp only at htest
  rw [hd] at htest
  change (match ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record,
      (record.output.followers i).down.map ReferenceDownCompletedAmbiguityMeasurability.cutFields with
    | some call, some cut =>
        if 0 < (ActualInitializationPhysicalStep.observationOfGrid p
              (ReferenceDownCompletedAmbiguityMeasurability.ownGrid record.input i)).val.val ∧
            cut.2.2.1.isSome then
          some ⟨call.1, call.2.2.2.1, cut.2.1⟩ else none
    | _, _ => none) = some test at htest
  cases hc : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
  | none => simp only [hc] at htest; cases htest
  | some callCode =>
      cases hcut : (record.output.followers i).down with
      | none => simp only [hc, hcut, Option.map_none] at htest; cases htest
      | some cut =>
          simp only [hc, hcut, Option.map_some] at htest
          split at htest
          next hpositive =>
            obtain ⟨logged, hlogged⟩ := record_down_some_logged record i cut hcut
            have hcomparison : cut.rawComparison.isSome = true := hpositive.2
            have hp : 0 < (preparedOwnObservation record i).val.val := by
              rw [preparedOwnObservation_eq_grid]
              exact hpositive.1
            have hcall : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation
                i record = some callCode := hc
            obtain ⟨heq, hexpected, hactual, heligible⟩ :=
              ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual
                record i callCode logged cut hcall hlogged hcut hcomparison hp
            have ht := Option.some.inj (heq.symm.trans htest0)
            obtain ⟨htime, hsample, _⟩ :=
              ReferenceDownCompletedAmbiguityMeasurability.actualDownCall_fields
                record i _ hactual
            refine ⟨_, hactual, heligible, ?_, ?_, ?_, ?_, ?_⟩
            · rw [← ht]; exact htime.symm
            · rw [← ht]; exact hsample.symm
            · rw [← ht]
            · rw [← ht]
            · rw [← ht]; exact hexpected
          next hnegative => cases htest

private theorem referenceDownCut_compared_of_success
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (time : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (logged post : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row time)
    (hstatus : logged.status = .unoccupied)
    (hout : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).outcome =
        .ok post) :
    (ReferenceDownReception.referenceDownCut p view i row time observation rate logged).rawComparison.isSome = true := by
  classical
  have hr : ActiveFollowerDownAcceptance.registerInputDomain p rate logged := by
    by_contra hn
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hout
  have hd : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch := by
    by_contra hn
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hr, hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hout
  have hb : ActiveFollowerDownAcceptance.bufferInputDomain p logged.buffer := by
    by_contra hn
    simp [ReferenceDownReception.referenceDownCut, hselected, hstatus, hr, hd, hn,
      DeclaredFollowerLocalRound.consumeDownResult] at hout
  rw [ReferenceActiveAffinePositiveTest.referenceDownCut_has_call]
  exact decide_eq_true ⟨hselected, hstatus, hr, hd, hb⟩

private theorem finishFollower_ordinary_record
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice after : ReferencePrelaunchFollower.State p rate.eta)
    (memory afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : prepared.configuration = .ordinary choice memory)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary after afterMemory) :
    ∃ post,
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation choice memory post = .ok (after, afterMemory) := by
  cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
  | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hc, hr] at hout
  | ok post =>
      cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
          prepared.time observation choice memory post with
      | error failure => simp [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf] at hout
      | ok result =>
          cases result with
          | mk final finalMemory =>
              simp only [ReferenceActivePhysicalStep.finishFollower, hc, hr, hf,
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary.injEq] at hout
              rcases hout with ⟨rfl, rfl⟩
              exact ⟨post, rfl, hf⟩

/-- The physical converse on an actual ordinary successor. Successful logging
and all receiver prechecks are derived from that computed successor; they are
not extra execution premises. Raw `some false` is sufficient. -/
theorem eligible_actualDownCall_executedTestOfRound
    (record : Record p rate) (i : Fin (p.m - 1))
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (afterMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hafter : record.output.next.followers i = .ordinary after afterMemory)
    (call : Call p) (hcall : actualDownCall i record = some call)
    (heligible : AffineBatchDecoder.eligible call.2) :
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) =
        some ⟨record.input.time, (record.input.row.2 record.input.time).2 (0, i),
          ReferenceActiveAffinePositiveTest.downSent record.input⟩ := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := preparedOwnObservation record i
  let view := record.output.preparation.coordinator.downView
  have hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary after afterMemory := by
    change (record.output.preparation.observeFollower i).configuration = _
    have hn := hafter
    rw [record.output_eq] at hn ⊢
    exact hn
  cases hc : preparedChoiceConfiguration record i with
  | dagger => simp only [actualDownCall, hc, reduceCtorEq] at hcall
  | ordinary choice memory =>
      have hcallEq := Option.some.inj
        ((actualDownCall_ordinary record i choice memory hc).symm.trans hcall)
      have he : AffineBatchDecoder.eligible
          (ActiveFollowerDownAcceptance.currentRoundInput p i (preparedChoiceRow record i)
            (preparedChoiceTime record i) observation rate choice) := by
        rw [← hcallEq] at heligible
        exact heligible
      obtain ⟨hselected, hstatus, hpositive⟩ :=
        (actualDownCall_eligible_iff record i choice).mp he
      have hconfig : prepared.configuration = .ordinary choice memory := hc
      obtain ⟨post, hrecord, hfinish⟩ := finishFollower_ordinary_record view prepared observation
        choice after memory afterMemory hconfig hout
      cases hl : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, observation) choice with
      | error failure =>
          simp [ReferenceActivePhysicalStep.recordFollower, hstatus, hl] at hrecord
      | ok logged =>
          have hframe := ActiveFollowerLogging.checkedLogging_success_frame prepared.follower
            prepared.row prepared.activation prepared.time (prepared.arm, observation)
            choice logged hl
          have hloggedStatus : logged.status = .unoccupied := hframe.2.2.2.2.1.trans hstatus
          have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
              (ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
                prepared.time observation rate logged).outcome = .ok post := by
            simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hl]
              using hrecord
          have hindex : prepared.follower = i :=
            (record.output.preparation.follower_alignment i).2.1
          have hselected' : ActiveFollowerDownAcceptance.downSelected p prepared.follower
              prepared.row prepared.time := by
            rw [hindex]
            exact hselected
          have hcomparison := referenceDownCut_compared_of_success view prepared.follower
            prepared.row prepared.time observation logged post hselected' hloggedStatus hconsume
          let cut := ReferenceDownReception.referenceDownCut p view prepared.follower prepared.row
            prepared.time observation rate logged
          have hdiag := ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
            record i
          have hlogged : (record.output.followers i).downInput = some logged := by
            rw [← hdiag]
            change (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = _
            simp only [ReferenceActivePhysicalStep.finishFollower, hconfig,
              ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hl, hconsume, hfinish]
          have hcut : (record.output.followers i).down = some cut := by
            rw [← hdiag]
            change (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = _
            simp only [ReferenceActivePhysicalStep.finishFollower, hconfig,
              ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hl, hconsume, hfinish]
            rfl
          obtain ⟨callCode, hcode⟩ : ∃ callCode,
              ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record =
                some callCode := by
            cases hc' : ReferenceDownCompletedAmbiguityMeasurability.downCallObservation i record with
            | none =>
                have hn := (ReferenceDownCompletedAmbiguityMeasurability.downCallObservation_eq_none_iff
                  i record).mp hc'
                rw [hc] at hn
                cases hn
            | some callCode => exact ⟨callCode, rfl⟩
          obtain ⟨htest, hexpected, _, _⟩ :=
            ReferenceGeneratedDownBatchBankBridge.executedTestOfRound_eq_actual record i
              callCode logged cut hcode hlogged hcut hcomparison hpositive
          rw [hexpected] at htest
          exact htest

/-- Erase only the sent-word tag; retain the original stamped equation. -/
def stampedTest (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) :
    AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p) :=
  ⟨test.time, test.sample⟩

/-- Exact one-record iff on the computed ordinary-successor branch. -/
theorem executedTestOfRound_isSome_iff
    (record : Record p rate) (i : Fin (p.m - 1))
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hafter : record.output.next.followers i = .ordinary after memory) :
    (ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).isSome = true ↔
    ∃ call, actualDownCall i record = some call ∧ AffineBatchDecoder.eligible call.2 := by
  constructor
  · intro h
    cases ht : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) with
    | none => simp only [ht, Option.isSome_none, Bool.false_eq_true] at h
    | some test =>
        obtain ⟨call, hc, he, _⟩ := executedTestOfRound_some_actual record i test ht
        exact ⟨call, hc, he⟩
  · rintro ⟨call, hc, he⟩
    rw [eligible_actualDownCall_executedTestOfRound record i after memory hafter call hc he]
    rfl

/-- On a surviving record, erasing the sent tag gives precisely its actual
positive decoder contribution. Eligibility is proved equivalent to execution. -/
theorem record_executedTest_entries_eq_actual
    (record : Record p rate) (i : Fin (p.m - 1))
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hafter : record.output.next.followers i = .ordinary after memory) :
    ((ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)).toList).map stampedTest =
      (actualDownCall i record).toList.flatMap (fun call =>
        AffineBatchDecoder.positiveAt p
          (ActiveFollowerDownAcceptance.currentInputExtension p call.2) call.1) := by
  classical
  cases ht : ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i) with
  | none =>
      cases hc : actualDownCall i record with
      | none => rfl
      | some call =>
          by_cases he : AffineBatchDecoder.eligible call.2
          · have hs := eligible_actualDownCall_executedTestOfRound record i after memory
              hafter call hc he
            rw [ht] at hs
            cases hs
          · simp only [Option.toList_none, List.map_nil, Option.toList_some,
              List.flatMap_singleton, AffineBatchDecoder.positiveAt,
              ActiveFollowerDownAcceptance.currentInputExtension]
            exact (ite_eq_right he).symm
  | some test =>
      obtain ⟨call, hc, he, htime, hsample, _⟩ :=
        executedTestOfRound_some_actual record i test ht
      simp only [hc, Option.toList_some, List.map_singleton, List.flatMap_singleton,
        AffineBatchDecoder.positiveAt, ActiveFollowerDownAcceptance.currentInputExtension,
        AffineBatchDecoder.entry, stampedTest, htime, hsample]
      exact (ite_eq_left he).symm

private theorem connected_ordinary_successors
    {initial final : ReferenceActivePhysicalHorizon.State p rate}
    {records : List (Record p rate)} (i : Fin (p.m - 1))
    (hc : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hf : ∃ state memory, final.followers i = .ordinary state memory) :
    (∃ state memory, initial.followers i = .ordinary state memory) ∧
    ∀ record ∈ records, ∃ state memory,
      record.output.next.followers i = .ordinary state memory := by
  induction records generalizing initial final with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hc
      subst final
      exact ⟨hf, by intro record hm; cases hm⟩
  | cons record rest ih =>
      rcases hc with ⟨hinput, htail⟩
      obtain ⟨hmiddle, hrest⟩ := ih htail hf
      have hbefore : ∃ state memory, initial.followers i = .ordinary state memory := by
        cases hb : record.input.state.followers i with
        | dagger =>
            have hd : record.output.next.followers i = .dagger := by
              rw [record.output_eq]
              exact ReferenceActivePhysicalStep.step_follower_dagger record.input i hb
            obtain ⟨state, memory, hs⟩ := hmiddle
            rw [hd] at hs
            cases hs
        | ordinary state memory => exact ⟨state, memory, by rw [← hinput]; exact hb⟩
      refine ⟨hbefore, ?_⟩
      intro current hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hmiddle
      · exact hrest current hm

private theorem records_executedTests_map_eq_actualDownPositives
    (records : List (Record p rate)) (i : Fin (p.m - 1))
    (hordinary : ∀ record ∈ records, ∃ state memory,
      record.output.next.followers i = .ordinary state memory) :
    (records.filterMap (fun record => ReferenceGeneratedDownBatchCalendar.executedTestOfRound
      rate (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))).map
        stampedTest = actualDownPositives i records := by
  simp only [List.filterMap_eq_flatMap_toList, List.map_flatMap,
    actualDownPositives, positiveCallEntries, actualDownCalls, List.flatMap_assoc]
  apply List.flatMap_congr
  intro record hm
  obtain ⟨state, memory, hs⟩ := hordinary record hm
  exact record_executedTest_entries_eq_actual record i state memory hs

/-- The uncapped executed-test list agrees with the actual positives in every
suffix of this same physical run. Dagger absorption produces all ordinary
record successors from the single computed endpoint selector. -/
theorem run_executedTests_map_eq_actualDownPositives
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).finalState.followers i = .ordinary state memory)
    (dropCount : ℕ) :
    (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.drop dropCount).filterMap (fun record =>
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))).map
            stampedTest = actualDownPositives i
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
        start count hspan hmode).records.drop dropCount) := by
  have hs := connected_ordinary_successors i
    (ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards
      start count hspan hmode) ⟨state, memory, hordinary⟩
  apply records_executedTests_map_eq_actualDownPositives
  intro record hm
  exact hs.2 record (List.mem_of_mem_drop hm)

private theorem filter_calendar_eq_drop
    (records : List (Record p rate)) (start count a : ℕ)
    (hcalendar : records.map (fun record => record.input.time.val) =
      List.range' start count 1) :
    records.filter (fun record => decide (start + a ≤ record.input.time.val)) =
      records.drop a := by
  induction records generalizing start count a with
  | nil => simp only [List.filter_nil, List.drop_nil]
  | cons record rest ih =>
      cases count with
      | zero => simp only [List.range'_zero, List.map_cons, List.cons_ne_nil] at hcalendar
      | succ count =>
          have hcalendar0 := hcalendar
          simp only [List.map_cons, List.range'_succ, List.cons.injEq] at hcalendar
          obtain ⟨htime, hrest⟩ := hcalendar
          cases a with
          | zero =>
              have hall : ∀ current ∈ record :: rest, start ≤ current.input.time.val := by
                intro current hm
                have ht : current.input.time.val ∈ List.range' start (count + 1) 1 := by
                  rw [← hcalendar0]
                  exact List.mem_map.mpr ⟨current, hm, rfl⟩
                obtain ⟨k, _, hk⟩ := List.mem_range'.mp ht
                omega
              simpa only [Nat.add_zero, List.drop_zero] using
                (List.filter_eq_self.mpr (fun current hm => decide_eq_true (hall current hm)))
          | succ a =>
              have hn : ¬ start + (a + 1) ≤ record.input.time.val := by omega
              simp only [List.filter_cons, decide_eq_false hn, Bool.false_eq_true,
                ite_false, List.drop_succ_cons]
              have he : start + (a + 1) = (start + 1) + a := by omega
              rw [he]
              exact ih (start + 1) count a (by simpa only [Nat.add_comm] using hrest)

/-- V's countable array, filtered at the original physical alpha, is exactly
D's uncapped executed list on the actual record suffix. Sent tags are kept. -/
theorem runDownObservation_uncapped_eq_records_drop
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) start)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : start ≤ alpha) :
    ((List.ofFn (ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
      start count hspan i input).2).filterMap (fun round =>
        if alpha ≤ round.1.val then
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round else none)) =
    (((ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records).drop (alpha - start)).filterMap (fun record =>
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i)) := by
  classical
  rw [(ReferenceDownCompletedAmbiguityMeasurability.runDownObservation_eq_actual
    start count hspan i input).2, List.filterMap_map]
  have hc := ReferenceActivePhysicalHorizon.run_time_values input.1.1 input.1.2.1
    input.1.2.2.1 input.1.2.2.2 start count hspan input.2
  change (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records.map
    (fun record => record.input.time.val) = List.range' start count 1 at hc
  have hf := filter_calendar_eq_drop
    (ReferenceActiveHorizonMeasurability.runOfInput start count hspan input).records
    start count (alpha - start) hc
  have ha : start + (alpha - start) = alpha := by omega
  rw [ha] at hf
  rw [← hf, List.filterMap_filter]
  apply List.filterMap_congr
  intro record _
  simp only [Function.comp_apply, ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation,
    decide_eq_true_eq]

/-- The uncapped test list retains the strict order of original physical
coordinates. This uses diagnostic inversion and does not require survival. -/
theorem run_executedTests_chronological
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1)) (dropCount : ℕ) :
    (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.drop dropCount).filterMap (fun record =>
        ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
          (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))).Pairwise
      (fun earlier later => earlier.time.val < later.time.val) := by
  have hc := ReferenceActivePhysicalHorizon.run_time_values initial rows selected rewards
    start count hspan hmode
  have ht : ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start count hspan hmode).records).Pairwise
        (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    apply List.pairwise_map.mp
    rw [hc]
    exact List.pairwise_lt_range'
  apply List.Pairwise.filterMap _ _ (ht.drop (i := dropCount))
  intro a b hab testA hA testB hB
  obtain ⟨_, _, _, _, _, htimeA, _⟩ := executedTestOfRound_some_actual a i testA hA
  obtain ⟨_, _, _, _, _, htimeB, _⟩ := executedTestOfRound_some_actual b i testB hB
  rw [htimeA, htimeB]
  exact hab

/-- The generated surviving-prefix producer. The only execution selectors
supplied by the caller are D's literal retained boundary, the computed ordinary
incoming branch at r, and the actual capped prefix length below Q. The alpha
reset comes from J; the bank identity consumes B on the original launch seed.
No restart or supplied uncapped count is used. Original sent tags and strict
physical chronology remain available in the uncapped-list equality. -/
theorem retainedBatchPrefix_bank_identity
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (qJ : Fin (M p)) (r : Fin p.T) (s : ℕ)
    (hs : s < p.T) (hsr : s ≤ r.val) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (halpha : s < alpha) (halphaR : alpha ≤ r.val)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h qJ r s hsr control0)
    (hboundary : ReferenceGeneratedDownBatchCalendar.retainedBatchBoundary
      rate rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x)
    (stateR : ReferencePrelaunchFollower.State p rate.eta)
    (memoryR : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ReferenceGeneratedDownBatchCalendar.retainedBatchIncoming
      rate rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x =
        .ordinary stateR memoryR)
    (hsmall : (ReferenceGeneratedDownBatchCalendar.retainedBatchPrefix
      rate rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x).length <
        AffineBatchDecoder.quota p) :
    let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
    let seed := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
      rate rewards C_star C_h qJ r s hsr control0 x
    let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2).2.1
    let runR := ReferenceActivePhysicalHorizon.run seed source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (r.val - s)
      (by omega) hmode
    let tests := (runR.records.drop (alpha - s)).filterMap (fun record =>
      ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
        (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))
    let prefixTests := ReferenceGeneratedDownBatchCalendar.retainedBatchPrefix
      rate rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x
    ActualInitializationPhysicalStep.selectedRowIndex p source = qJ ∧
    prefixTests = tests ∧
    prefixTests.map stampedTest = actualDownPositives i (runR.records.drop (alpha - s)) ∧
    tests.length < AffineBatchDecoder.quota p ∧
    tests.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
    ∃ stateA memoryA,
      (ReferenceActivePhysicalHorizon.run seed source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (alpha - s)
        (by omega) hmode).finalState.followers i = .ordinary stateA memoryA ∧
      stateA.downBatch.pending = [] ∧
      stateR.downBatch.pending = prefixTests.map stampedTest ∧
      stateR.downBatch.completed = stateA.downBatch.completed ∧
      ReferenceFollowerDecoderChronology.downBatchEndpoint stateA alpha ∧
      ReferenceFollowerDecoderChronology.downBatchEndpoint stateR r.val ∧
      (stateR.status ≠ .unoccupied → stateR.downBatch.pending = []) := by
  classical
  dsimp only
  let source := ReferenceGeneratedActivePrefixFactor.splitSource qJ r control0 x.1
  let seed := ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
    rate rewards C_star C_h qJ r s hsr control0 x
  let hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h qJ r control0 x.1 x.2.1 s hsr x.2.2
  let rows := source.1.2
  let selected := ActualInitializationPhysicalStep.selectedRowIndex p source
  let physicalRun := ReferenceActivePhysicalHorizon.run seed rows selected rewards s
    (r.val - s) (by omega) hspec.2.1
  let tests := (physicalRun.records.drop (alpha - s)).filterMap (fun record =>
    ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate
      (ReferenceDownCompletedAmbiguityMeasurability.roundDownObservation record.input i))
  let prefixTests := ReferenceGeneratedDownBatchCalendar.retainedBatchPrefix
    rate rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x
  have hselected : selected = qJ := by
    change ActualInitializationPhysicalStep.selectedRowIndex p source = qJ
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p qJ r control0 x.1 x.2.1
  let input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s := ⟨(seed, (rows, (qJ, rewards))), hspec.2.1⟩
  have hrun : ReferenceActiveHorizonMeasurability.runOfInput s (r.val - s) (by omega) input =
      physicalRun := by
    dsimp only [ReferenceActiveHorizonMeasurability.runOfInput, input, physicalRun]
    rw [hselected]
  have hordinaryRun : physicalRun.finalState.followers i = .ordinary stateR memoryR := by
    rw [← hrun]
    exact hordinary
  have hlist : tests.map stampedTest =
      actualDownPositives i (physicalRun.records.drop (alpha - s)) :=
    run_executedTests_map_eq_actualDownPositives seed rows selected rewards s (r.val - s)
      (by omega) hspec.2.1 i stateR memoryR hordinaryRun (alpha - s)
  have hprefixTake : prefixTests = tests.take (AffineBatchDecoder.quota p) := by
    change ((List.ofFn (ReferenceDownCompletedAmbiguityMeasurability.runDownObservation
      s (r.val - s) (by omega) i input).2).filterMap (fun round =>
        if alpha ≤ round.1.val then
          ReferenceGeneratedDownBatchCalendar.executedTestOfRound rate round else none)).take _ = _
    rw [runDownObservation_uncapped_eq_records_drop s (r.val - s) (by omega) input i alpha
      (by omega), hrun]
  have hsmallTests : tests.length < AffineBatchDecoder.quota p := by
    have hQ := AffineBatchDecoder.quota_pos p
    have hm : min (AffineBatchDecoder.quota p) tests.length < AffineBatchDecoder.quota p := by
      rw [← List.length_take, ← hprefixTake]
      exact hsmall
    omega
  have hprefix : prefixTests = tests := hprefixTake.trans
    ((List.take_eq_self_iff tests).mpr (Nat.le_of_lt hsmallTests))
  have hsmallActual : (actualDownPositives i
      (physicalRun.records.drop (alpha - s))).length < AffineBatchDecoder.quota p := by
    rw [← hlist, List.length_map]
    exact hsmallTests
  obtain ⟨stateA, memoryA, hordinaryA, hreset⟩ :=
    ReferenceGeneratedDownBatchBankBridge.retainedBatchBoundary_pending_empty
      rewards C_star C_h qJ r s hs hsr control0 i alpha halpha halphaR x hboundary
  have hbank := ReferenceExecutedDownBankRecurrence.run_interval_fresh_downBatch_identity
    seed rows selected rewards s (alpha - s) (r.val - s) (by omega) (by omega)
    hspec.2.1 hspec.2.2 i stateA memoryA hordinaryA stateR memoryR hordinaryRun
    hreset hsmallActual
  have hchron := run_executedTests_chronological seed rows selected rewards s (r.val - s)
    (by omega) hspec.2.1 i (alpha - s)
  have hentries : prefixTests.map stampedTest =
      actualDownPositives i (physicalRun.records.drop (alpha - s)) :=
    (congrArg (List.map stampedTest) hprefix).trans hlist
  have hpending : stateR.downBatch.pending = prefixTests.map stampedTest :=
    hbank.1.trans hentries.symm
  refine ⟨hselected, hprefix, hentries, hsmallTests, hchron, stateA, memoryA, hordinaryA,
    hreset, hpending, hbank.2.1, ?_, ?_, hbank.2.2.2.2⟩
  · simpa only [show s + (alpha - s) = alpha by omega] using hbank.2.2.1
  · simpa only [show s + (r.val - s) = r.val by omega] using hbank.2.2.2.1

end Bandits.Support.ReferenceGeneratedDownPrefixList

end
