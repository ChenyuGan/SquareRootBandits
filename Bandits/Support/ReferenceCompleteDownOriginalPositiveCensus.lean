/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOrdinaryWrongCompletionCharacterization

import Lean.Elab.Tactic.Omega

/-!
# Complete source census for an incoming DOWN bank

For an actual logged physical DOWN input, the collected bank is exactly the
original prelaunch positives together with the actual postlaunch positives
strictly before that record. This identifies the existing receiver bank; it
does not assert ambiguity, probability, overflow, or regret.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.ReferenceGeneratedPrelaunchDownCohort
open Bandits.Support.ReferenceFollowerDownDecoderReplay

namespace Bandits.Support.ReferenceCompleteDownOriginalPositiveCensus

variable {p : ConstructorDimensions.Parameters}

/-- The actual incoming DOWN batch contains the full original initialization
census and exactly the physical positives before this record. -/
theorem actual_incoming_down_collected_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r)
    (hlogged : (r.output.followers i).downInput = some logged) :
    AffineBatchDecoder.collected logged.downBatch =
      (ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
        rate rewards C_star C_h z i).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry ++
      ReferenceFollowerDownDecoderReplay.actualDownPositives i
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).take
          (t.val - ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h)) := by
  classical
  let x := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let f := ActualReferenceInitializationBlock.refFollower i
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let k := t.val - s

  have hlaunchBy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := by
    by_contra hnot
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hnot
    rw [hnone] at hrecord
    cases hrecord

  have hstartLe : s ≤ t.val := hlaunchBy.2
  have hstartStrict : s < p.T := by omega
  have hstop : ReferenceInitializationRun.elapsed p b.completed < p.T := hstartStrict
  have hcross : b.crossing.isSome = true := hlaunchBy.1

  obtain ⟨launchSource, _hsource, hlaunch, hinitial, hseed, _, _⟩ :=
    ReferenceGeneratedPrelaunchDownCohort.source_launch_down_cohort_provenance
      rate rewards C_star C_h z i hstop hcross
  let active := ReferenceGeneratedDownBatchCalendar.generatedSourceSeed rate rewards C_star C_h
    (ReferenceInitializationRun.elapsed p b.completed) hstop launchSource
  let initialFollower := ReferenceInitializationRun.ordinary x b f
  let initialMemory := ActiveFollowerLifecycle.initialMemory p
  have hinitialState : active.followers i = .ordinary initialFollower initialMemory := hinitial
  have hseedStart : ReferenceFollowerDecoderChronology.downBatchSeed active s := hseed
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s :=
    ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h active hlaunch
  have hfullSpan : s + (p.T - s) ≤ p.T := by omega
  have hfullRun : R = (ReferenceActivePhysicalHorizon.run active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
      hfullSpan hmode).records := by
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hlaunch
  have hfullCount := ReferenceActivePhysicalHorizon.run_record_count active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (p.T - s)
    hfullSpan hmode
  have hRlength : R.length = p.T - s := by
    rw [hfullRun]
    exact hfullCount
  have hk : k < R.length := by
    rw [hRlength]
    dsimp only [k]
    omega
  let kFin : Fin R.length := ⟨k, hk⟩
  have hprefixSpan : s + k ≤ p.T := by
    dsimp only [k]
    omega
  let prefixRun := ReferenceActivePhysicalHorizon.run active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan hmode
  have hprefixCount := ReferenceActivePhysicalHorizon.run_record_count active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan hmode

  have hactualOnLaunch := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z active hlaunch hstartLe
  have hrecordValue : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
      (by dsimp only [s, k]; omega) hmode := by
    apply Option.some.inj
    calc
      some r = ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z := hrecord.symm
      _ = some (ReferenceAssignmentPayloadChronology.actualRunRecordAt
          active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
          (by dsimp only [s, k]; omega) hmode) := by
            simpa only [s, k, hmode] using hactualOnLaunch

  have hkFull : k < p.T - s := by
    rw [← hRlength]
    exact hk
  have hRactualRunRecord : R[k] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
          active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
          (by dsimp only [s, k]; omega) hmode := by
    simpa only [hfullRun] using ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode
      (p.T - s) hfullSpan ⟨k, hkFull⟩
  have hRrecord : R[k] = r := hRactualRunRecord.trans hrecordValue.symm

  obtain ⟨inputState, inputMemory, actualChoice, hinput, _hinputDomain,
      hstartActual, hchoiceActual, _hchoiceDomain, _hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h z kFin i
  have hordinary : prefixRun.finalState.followers i = .ordinary inputState inputMemory := by
    rw [hRactualRunRecord] at hinput
    change prefixRun.finalState.followers i = .ordinary inputState inputMemory at hinput
    exact hinput

  obtain ⟨_, hcollected, _, _⟩ := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k
    hprefixSpan hmode hseedStart i initialFollower initialMemory hinitialState
    inputState inputMemory hordinary

  have hprelaunch := ReferenceGeneratedPrelaunchDownCohort.source_prelaunch_down_cohorts
    rate rewards C_star C_h z i
  have hprelaunchCollected :
      (ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
        rate rewards C_star C_h z i).map ReferenceGeneratedPrelaunchDownCohort.testEntry =
        AffineBatchDecoder.collected initialFollower.downBatch := hprelaunch.1

  have hloggedAtR : (R[k].output.followers i).downInput = some logged := by
    rw [hRrecord]
    exact hlogged
  have hchoiceConfig :
      ((R[k]).output.preparation.followers.followers i).configuration =
        .ordinary actualChoice inputMemory := by
    simpa only [ReferenceFollowerFixedReply.actualChoice] using hchoiceActual

  let record := R[k]
  let prepared := record.output.preparation.followers.followers i
  let own := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hpreparedConfig : prepared.configuration = .ordinary actualChoice inputMemory := by
    simpa only [record, prepared] using hchoiceConfig
  have hloggedObservation : (record.output.preparation.observeFollower i).downInput =
      some logged := by
    have h := hloggedAtR
    rw [← ReferenceDownCompletedAmbiguityMeasurability.record_preparationDiagnostics
      record i] at h
    exact h
  have hloggedFinish :
      (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
        prepared own).downInput = some logged := by
    change (ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView prepared own).downInput = some logged
      at hloggedObservation
    exact hloggedObservation
  have hfinishFrame :
      (ReferenceActivePhysicalStep.finishFollower record.output.preparation.coordinator.downView
        prepared own).downInput =
        (ReferenceActivePhysicalStep.recordFollower record.output.preparation.coordinator.downView
          prepared.follower prepared.row prepared.activation prepared.time prepared.active
          prepared.arm own actualChoice).downInput := by
    classical
    rw [ReferenceActivePhysicalStep.finishFollower, hpreparedConfig]
    cases hrecorded : ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm own actualChoice with
    | mk result downInput down =>
        cases result with
        | error failure => simp [hrecorded]
        | ok post =>
            cases hrelease : DeclaredFollowerLocalRound.releaseAndFinish rate
                prepared.follower prepared.row prepared.time own actualChoice inputMemory post with
            | error failure => simp [hrecorded, hrelease]
            | ok next => cases next; simp [hrecorded, hrelease]
  have hrecordedInput := hfinishFrame.symm.trans hloggedFinish
  have hlogging : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
      prepared.activation prepared.time (prepared.arm, own) actualChoice = .ok logged := by
    by_cases hstatus : actualChoice.status = .unoccupied
    · cases hlog : ActiveFollowerLogging.checkedLogging prepared.follower prepared.row
          prepared.activation prepared.time (prepared.arm, own) actualChoice with
      | error failure =>
          simp [ReferenceActivePhysicalStep.recordFollower, hstatus, hlog] at hrecordedInput
      | ok loggedState =>
          have heq : loggedState = logged := by
            simpa [ReferenceActivePhysicalStep.recordFollower, hstatus, hlog] using
              hrecordedInput
          exact congrArg Except.ok heq
    · simp [ReferenceActivePhysicalStep.recordFollower, hstatus] at hrecordedInput
  have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
    prepared.follower prepared.row prepared.activation prepared.time (prepared.arm, own)
    actualChoice logged hlogging
  rcases hloggingFrame with ⟨_, _, _, _, _, hloggedBatch, _⟩
  have hstartFrame := ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time
    inputState actualChoice inputMemory inputMemory hstartActual
  rcases hstartFrame with ⟨_, _, _, _, hchoiceBatch, _, _, _⟩
  have hloggedBeforeDecoder : logged.downBatch = inputState.downBatch :=
    hloggedBatch.trans hchoiceBatch

  have hprefixRecords : R.take k = prefixRun.records := by
    rw [hfullRun]
    apply List.ext_getElem
    · rw [List.length_take, hfullCount, hprefixCount,
        Nat.min_eq_left (Nat.le_of_lt hkFull)]
    · intro j hjLeft hjRight
      have hj : j < k := by
        rw [ReferenceActivePhysicalHorizon.run_record_count] at hjRight
        exact hjRight
      let jPrefix : Fin k := ⟨j, hj⟩
      let jFull : Fin (p.T - s) := ⟨j, by omega⟩
      have hfullAt := ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode
        (p.T - s) hfullSpan jFull
      have hprefixAt := ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s hmode k
        hprefixSpan jPrefix
      simpa only [List.getElem_take, jFull, jPrefix] using hfullAt.trans hprefixAt.symm

  calc
    AffineBatchDecoder.collected logged.downBatch =
        AffineBatchDecoder.collected inputState.downBatch :=
          congrArg AffineBatchDecoder.collected hloggedBeforeDecoder
    _ = AffineBatchDecoder.collected initialFollower.downBatch ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i prefixRun.records := hcollected
    _ = (ReferenceGeneratedPrelaunchDownCohort.sourcePrelaunchDownTests
          rate rewards C_star C_h z i).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry ++
        ReferenceFollowerDownDecoderReplay.actualDownPositives i (R.take k) := by
          rw [← hprelaunchCollected, ← hprefixRecords]

end Bandits.Support.ReferenceCompleteDownOriginalPositiveCensus
