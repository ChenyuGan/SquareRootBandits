/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseBoundary
public import Bandits.Support.ReferenceFirstLiveInitialTransferCost

import Mathlib.Tactic

/-!
# Actual later-installation handover stages and inherited decoder bank

This module isolates source-backed data at an actual later installation after
the first replacement collection.  The birth input, retained DOWN history,
current word, and handover prefix all belong to the same complete physical
suffix. The actual choices distinguish the retained old reply from the
accepted current word, and the full bank splices through the same handover.
Identification with the stopped analysis replay remains a separate obligation.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions BootstrapPrivateRoundStreams

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverReplay

variable {p : ConstructorDimensions.Parameters}

private abbrev Record {rate : ReferenceActivePhysicalStep.RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

private theorem eq_if_iff_implications {α : Type} (condition : Prop)
    [Decidable condition] (value yes no : α) :
    (value = if condition then yes else no) ↔
      (condition → value = yes) ∧ (¬ condition → value = no) := by
  by_cases h : condition <;> simp [h]

private theorem retainedDown_sigma_le_record_time_succ
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : Record (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (message : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown record i message) :
    message.val.sigma ≤ record.input.time.val + 1 := by
  rcases hretained with
    ⟨logged, cut, after, raw, scan, registers, lastService,
      hinput, hdown, houtcome⟩
  obtain ⟨_choice, _memory, loggedActual, _hchoice, _hunoccupied,
      _hlogging, hinputActual, hcutActual⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice
      record i cut hdown
  have hlogged : loggedActual = logged :=
    Option.some.inj (hinputActual.symm.trans hinput)
  rw [hlogged] at hcutActual
  have haccepted :
      (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome =
        .accepted logged after raw message scan registers lastService := by
    rw [← hcutActual]
    exact houtcome
  have hbound := ReferenceFollowerReplyChronology.referenceDownCut_accepted
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i).follower
    (record.output.preparation.followers.followers i).row
    (record.output.preparation.followers.followers i).time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    logged after raw message scan registers lastService haccepted
  have htime :
      (record.output.preparation.followers.followers i).time.val =
        record.input.time.val := by
    have halign := (ReferenceActivePhysicalStep.prepare record.input).follower_alignment i
    have htimeFin : (record.output.preparation.followers.followers i).time =
        record.input.time := by
      rw [record.output_eq]
      simpa [ReferenceActivePhysicalStep.step] using halign.2.2.1
    exact congrArg Fin.val htimeFin
  simp only [OrdinaryMessageCodec.acceptDown] at hbound
  rcases hbound with ⟨⟨_, hboundTime⟩, _⟩
  rw [htime] at hboundTime
  exact hboundTime

private theorem payload_down_sigma_at_birth
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : Record (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload)
    (i : Fin (p.m - 1)) :
    (payload.downRecord i).val.sigma = record.input.time.val + 1 := by
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hlater
  rw [← hprep] at hlater
  cases hcoord : record.output.preparation.coordinator with
  | first _ => simp only [hcoord, Bool.false_eq_true] at hlater
  | live _ _ _ _ => simp only [hcoord, Bool.false_eq_true] at hlater
  | invalidCollectionCutoff => simp only [hcoord, Bool.false_eq_true] at hlater
  | dagger => simp only [hcoord, Bool.false_eq_true] at hlater
  | collection _ _ _ _ outcome =>
      cases outcome <;>
        simp only [hcoord, Bool.false_eq_true] at hlater
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hcoord] at hbirth
      rcases hbirth with ⟨_, htime⟩
      rw [payload.downRecord_fields i]
      rw [htime]

private theorem old_accepted_start_lt_birth_word
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1))
    (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.followers i =
        .ordinary before beforeMemory)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] payload) :
    ReferencePrelaunchFollower.acceptedStart before <
      (payload.downRecord i).val.sigma := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hnewSigma := payload_down_sigma_at_birth R[b.val] payload hlater hbirth i
  cases hlast : before.lastDown with
  | none =>
      simp [ReferencePrelaunchFollower.acceptedStart, hlast, hnewSigma]
  | some old =>
      have hmass := ReferenceCompleteOrdinaryFollowerMass.complete_ordinary_follower_input_mass
        rewards C_star C_h z b i before beforeMemory hinput old hlast
      rcases hmass with
        ⟨_oldBirth, j, _oldPayload, _beta, _hbirthBefore, hjb,
          _holdBirth, _hbase, hretained, _hmessage, _hmass, _hdelta⟩
      have holdSigma : old.val.sigma ≤ R[j.val].input.time.val + 1 :=
        retainedDown_sigma_le_record_time_succ R[j.val] i old hretained
      have htj := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z j
      have htb := ReferenceAssignmentFollowerMassSteps.complete_record_time
        rate rewards C_star C_h z b
      rw [htj] at holdSigma
      simp only [ReferencePrelaunchFollower.acceptedStart, hlast]
      rw [hnewSigma]
      rw [htb]
      omega

private theorem connected_final_unique
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {initial final₁ final₂ : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (h₁ : ReferenceActivePhysicalHorizon.Connected initial records final₁)
    (h₂ : ReferenceActivePhysicalHorizon.Connected initial records final₂) :
    final₁ = final₂ := by
  induction records generalizing initial final₁ final₂ with
  | nil =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      exact h₁.trans h₂.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at h₁ h₂
      exact ih h₁.2 h₂.2

private theorem run_prefix_final_eq_input_at
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count j : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hj : j < count) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
      (by omega) hmode).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records[j]'(by
          rw [ReferenceActivePhysicalHorizon.run_record_count
            initial rows selected rewards start count hspan hmode]
          exact hj)).input.state := by
  let shortRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start j
    (by omega) hmode
  let wholeRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
    hspan hmode
  obtain ⟨suffix, hsplit⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start j (count - j) (by omega) hmode
  have hsplitSame : wholeRun.records = shortRun.records ++ suffix := by
    have hcountSplit : j + (count - j) = count := by omega
    simpa [wholeRun, shortRun, hcountSplit] using hsplit
  have hshortLength : shortRun.records.length = j := by
    simp [shortRun, ReferenceActivePhysicalHorizon.run_record_count]
  have hshortTake : shortRun.records = wholeRun.records.take j := by
    rw [hsplitSame]
    rw [List.take_append_of_le_length (by omega)]
    simp [hshortLength]
  have hwholeConnected := ReferenceActivePhysicalHorizon.run_connected
    initial rows selected rewards start count hspan hmode
  have hwholeLength := ReferenceActivePhysicalHorizon.run_record_count
    initial rows selected rewards start count hspan hmode
  have hwholeLength' : wholeRun.records.length = count := by
    simpa [wholeRun] using hwholeLength
  have hjWhole : j < wholeRun.records.length := by
    rw [hwholeLength']
    exact hj
  have hinputConnected :=
    ReferenceFollowerReplyChronology.connected_take_to_input hwholeConnected j hjWhole
  rw [← hshortTake] at hinputConnected
  have hprefixConnected := ReferenceActivePhysicalHorizon.run_connected
    initial rows selected rewards start j (by omega) hmode
  exact connected_final_unique hprefixConnected hinputConnected

private theorem completeSuffix_launch_route
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hne : 0 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ∃ (active : ReferenceActivePhysicalStep.State p rate)
      (_hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
      (_hseed : ReferenceFollowerDecoderChronology.downBatchSeed active
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)),
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some active := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hlaunch
      have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
        rate z rewards C_star C_h
      have hzero : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length = 0 := by
        simpa [hstart] using hlength
      rw [hzero] at hne
      omega
  | some active =>
      have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h).isSome = true := by
        rw [hlaunch]
        rfl
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp hsome
      obtain ⟨active', hlaunch', hseed⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
          rate z rewards C_star C_h hc
      have hactive : active = active' := Option.some.inj (hlaunch.symm.trans hlaunch')
      subst active'
      refine ⟨active,
        ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h active hlaunch,
        hseed, rfl⟩

private theorem completeSuffix_input_down_bank_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
    (hseed : ReferenceFollowerDecoderChronology.downBatchSeed active
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.followers i =
        .ordinary state memory) :
    ∃ (initialFollower : ReferencePrelaunchFollower.State p rate.eta)
      (initialMemory : ActiveFollowerLifecycle.LocalMemory p),
      active.followers i = .ordinary initialFollower initialMemory ∧
      ReferenceFollowerDecoderChronology.downBatchWellFormed initialFollower.downBatch ∧
      ReferenceFollowerDecoderChronology.downCollectedChronological initialFollower.downBatch ∧
      (∀ entry ∈ AffineBatchDecoder.collected initialFollower.downBatch,
        entry.time.val <
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ∧
      state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).take k.val) initialFollower.downBatch ∧
      ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch ∧
      (∀ entry ∈ state.downBatch.pending,
        entry.time.val <
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.time.val) ∧
      ReferenceFollowerDecoderChronology.downCollectedChronological state.downBatch ∧
      (∀ entry ∈ AffineBatchDecoder.collected state.downBatch,
        entry.time.val <
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.time.val) ∧
      (state.status ≠ .unoccupied → state.downBatch.pending = []) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - start
  have hstartLe := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate z rewards C_star C_h
  have hfullSpan : start + count ≤ p.T := by
    dsimp [count]
    omega
  have hcount : R.length = count := by
    dsimp [R, count, start]
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hk : k.val < count := by
    rw [← hcount]
    exact k.isLt
  have hprefixSpan : start + k.val ≤ p.T := by
    dsimp [count] at hk
    omega
  let whole := ReferenceActivePhysicalHorizon.run active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start count
    hfullSpan hmode
  let shortRun := ReferenceActivePhysicalHorizon.run active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val
    hprefixSpan hmode
  have hrecords : R = whole.records := by
    change ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
      (ReferenceActivePhysicalHorizon.run active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by omega) hmode).records
    exact ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hlaunch
  have hkWhole : k.val < whole.records.length := by
    rw [← hrecords]
    exact k.isLt
  have hrecordEq : R[k.val] = whole.records[k.val] :=
    getElem_congr_coll hrecords
  have hinputWhole : whole.records[k.val].input.state.followers i = .ordinary state memory := by
    rw [← hrecordEq]
    exact hinput
  have hfinalWhole : shortRun.finalState = whole.records[k.val].input.state := by
    exact run_prefix_final_eq_input_at rate active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start count k.val
      hfullSpan hmode hk
  have hordinary : shortRun.finalState.followers i = .ordinary state memory := by
    rw [hfinalWhole]
    exact hinputWhole
  obtain ⟨initialFollower, initialMemory, hinitial, hstatus, hwellSeed,
    hchronSeed, hstampSeed⟩ := hseed i
  have hreplay := ReferenceFollowerDownDecoderReplay.run_downBatch_replay
    active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    start k.val hprefixSpan hmode hseed i initialFollower initialMemory hinitial
    state memory hordinary
  have hsplit := ReferenceCollectionPhaseHistory.run_records_prefix active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val
    (count - k.val) (by omega) hmode
  rcases hsplit with ⟨suffix, hsplit⟩
  have hsplitSame : whole.records = shortRun.records ++ suffix := by
    have hcountSplit : k.val + (count - k.val) = count := by omega
    simpa [whole, shortRun, hcountSplit] using hsplit
  have hprefixLength : shortRun.records.length = k.val := by
    simp [shortRun, ReferenceActivePhysicalHorizon.run_record_count]
  have hprefixRecords : shortRun.records = whole.records.take k.val := by
    rw [hsplitSame]
    rw [List.take_append_of_le_length (by omega)]
    simp [hprefixLength]
  have hbank : state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
      (R.take k.val) initialFollower.downBatch := by
    calc
      state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          shortRun.records initialFollower.downBatch := hreplay.1
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (whole.records.take k.val) initialFollower.downBatch := by rw [hprefixRecords]
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (R.take k.val) initialFollower.downBatch := by rw [← hrecords]
  have hendpoint := ReferenceFollowerDecoderChronology.run_downBatch_spec
    active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    start k.val hprefixSpan hmode hseed i state memory hordinary
  have hpending := ReferenceFollowerDownDecoderReplay.run_downBatch_pending_before_next_input
    active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    start k.val hprefixSpan hmode hseed i state memory hordinary
  have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h z k
  refine ⟨initialFollower, initialMemory, hinitial, hwellSeed, hchronSeed,
    hstampSeed, hbank, hendpoint.1.1, ?_, hendpoint.1.2.1, ?_, hendpoint.2⟩
  · intro entry hentry
    exact lt_of_lt_of_le (hpending entry hentry) (by rw [htime])
  · intro entry hentry
    exact lt_of_lt_of_le (hendpoint.1.2.2 entry hentry) (by rw [htime])

/-- Every ordinary input in the actual complete suffix carries the DOWN bank
obtained by replaying the original launch seed through the same physical
prefix. The endpoint records retain completed, pending, and collected entries. -/
public theorem actual_complete_suffix_input_down_bank_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    ∀ k : Fin R.length, ∀ (i : Fin (p.m - 1))
      (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      R[k.val].input.state.followers i = .ordinary state memory →
      ∃ (active : ReferenceActivePhysicalStep.State p rate)
        (_hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
        (_hseed : ReferenceFollowerDecoderChronology.downBatchSeed active
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)),
        ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h = some active ∧
        ∃ (initialFollower : ReferencePrelaunchFollower.State p rate.eta)
          (initialMemory : ActiveFollowerLifecycle.LocalMemory p),
          active.followers i = .ordinary initialFollower initialMemory ∧
          ReferenceFollowerDecoderChronology.downBatchWellFormed initialFollower.downBatch ∧
          ReferenceFollowerDecoderChronology.downCollectedChronological initialFollower.downBatch ∧
          (∀ entry ∈ AffineBatchDecoder.collected initialFollower.downBatch,
            entry.time.val <
              ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ∧
          state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
            (R.take k.val) initialFollower.downBatch ∧
          ReferenceFollowerDecoderChronology.downBatchWellFormed state.downBatch ∧
          (∀ entry ∈ state.downBatch.pending,
            entry.time.val < R[k.val].input.time.val) ∧
          ReferenceFollowerDecoderChronology.downCollectedChronological state.downBatch ∧
          (∀ entry ∈ AffineBatchDecoder.collected state.downBatch,
            entry.time.val < R[k.val].input.time.val) ∧
          (state.status ≠ .unoccupied → state.downBatch.pending = []) ∧
          (∀ cut : ReferenceDownReception.ReferenceDownCutOutput p rate,
            (R[k.val].output.followers i).down = some cut →
            cut.rawComparison ≠ none →
            ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
              ∃ choiceMemory : ActiveFollowerLifecycle.LocalMemory p,
              ∃ logged : ReferencePrelaunchFollower.State p rate.eta,
                let prep := R[k.val].output.preparation.followers.followers i
                let observation := R[k.val].output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)
                prep.configuration = .ordinary choice choiceMemory ∧
                choice.status = .unoccupied ∧
                ActiveFollowerLogging.checkedLogging prep.follower prep.row prep.activation
                  prep.time (prep.arm, observation) choice = .ok logged ∧
                (R[k.val].output.followers i).downInput = some logged ∧
                logged.downBatch = state.downBatch ∧
                prep.follower = i ∧
                prep.row = R[k.val].input.row ∧
                prep.time = R[k.val].input.time ∧
                cut.raw =
                  (ActiveFollowerDownAcceptance.currentDecodeStep p i R[k.val].input.row
                    R[k.val].input.time observation rate logged).2) := by
  classical
  intro R k i state memory hinput
  have hnonempty : 0 < R.length :=
    Nat.lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  obtain ⟨active, hmode, hseed, hlaunch⟩ :=
    completeSuffix_launch_route rate rewards C_star C_h z (by simpa [R] using hnonempty)
  obtain ⟨initialFollower, initialMemory, hinitial, hwellSeed, hchronSeed,
    hstampSeed, hbank, hwell, hpendingBound, hchron, hcollectedBound,
    hoccupiedPending⟩ :=
    completeSuffix_input_down_bank_prefix rate rewards C_star C_h z active
      hmode hseed hlaunch k i state memory hinput
  refine ⟨active, hmode, hseed, hlaunch, initialFollower, initialMemory,
    hinitial, hwellSeed, hchronSeed, hstampSeed, hbank, hwell, hpendingBound,
    hchron, hcollectedBound, hoccupiedPending, ?_⟩
  intro cut hdown hcompared
  let record := R[k.val]
  let prep := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  obtain ⟨choice, choiceMemory, logged, hprepared, hchoiceStatus, hlogging,
    hdownInput, hcutEq⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hprepareFrame := ReferenceFollowerDecoderChronology.run_interruption_downBatch_frame
    record i state choice memory choiceMemory hinput hprepared hoccupiedPending
  have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
    prep.follower prep.row prep.activation prep.time (prep.arm, observation)
    choice logged hlogging
  rcases hloggingFrame with ⟨_, _, _, _, _, hloggedBank, _⟩
  have hloggedBankEq : logged.downBatch = state.downBatch :=
    hloggedBank.trans hprepareFrame.1
  have hcomparedCut :
      (ReferenceDownReception.referenceDownCut p record.output.preparation.coordinator.downView
        prep.follower prep.row prep.time observation rate logged).rawComparison ≠ none := by
    simpa [hcutEq] using hcompared
  have hraw := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
    record.output.preparation.coordinator.downView prep.follower prep.row prep.time
    observation rate logged hcomparedCut
  have halign := (ReferenceActivePhysicalStep.prepare record.input).follower_alignment i
  have hprepRow : prep.row = record.input.row := by
    dsimp [prep]
    rw [record.output_eq]
    simpa [ReferenceActivePhysicalStep.step] using halign.1
  have hprepFollower : prep.follower = i := by
    dsimp [prep]
    rw [record.output_eq]
    simpa [ReferenceActivePhysicalStep.step] using halign.2.1
  have hprepTime : prep.time = record.input.time := by
    dsimp [prep]
    rw [record.output_eq]
    simpa [ReferenceActivePhysicalStep.step] using halign.2.2.1
  refine ⟨choice, choiceMemory, logged, hprepared, hchoiceStatus, hlogging,
    hdownInput, hloggedBankEq, hprepFollower, hprepRow, hprepTime, ?_⟩
  simpa [record, prep, observation, hcutEq, hprepFollower, hprepRow, hprepTime] using hraw

/-- The actual later-installation branch fixes an unoccupied birth INPUT and
choice for every follower, keeps the entire old DOWN bank and local memory,
and starts the new current word strictly after that follower's retained
accepted start.  The handover/release split and confirmation classification
are for this same record and complete physical suffix. -/
public theorem actual_later_installation_handover_birth_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
          (base : Fin (p.m - 1) → ℕ)
          (birthSelected : ReferenceActivePhysicalStep.Selection R[b.val].input),
          R[b.val].output.next.coordinator = .live registers owned base ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] registers.payload ∧
          R[b.val].output.preparation.coordinator.selection = some birthSelected ∧
          birthSelected.view.payload = registers.payload ∧
          birthSelected.view.pendingAtChoice = Finset.univ ∧
          (b.val + 1 = R.length ∨
            ∃ k : Fin R.length, k.val = b.val + 1 ∧
              R[k.val].input.state.coordinator = .live registers owned base ∧
              let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z k.val
              ∀ j : Fin W.length,
                ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                  (selected : ReferenceActivePhysicalStep.Selection W[j.val].input)
                  (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                  (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next),
                  W[j.val].input.state.coordinator = .live r q base ∧
                  r.payload = registers.payload ∧
                  W[j.val].output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = registers.payload ∧
                  selected.view.pendingAtChoice = r.pendingAtChoice ∧
                  W[j.val].output.next.coordinator = .live next nextOwned base ∧
                  next.payload = registers.payload ∧
                  (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                      W[j.val] selected →
                    next.pendingAtChoice = selected.view.pendingAtChoice.erase
                      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (W[j.val].input.row.2 W[j.val].input.time).1)) ∧
                  (¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                      W[j.val] selected →
                    next.pendingAtChoice = selected.view.pendingAtChoice)) ∧
          (∀ i : Fin (p.m - 1),
            ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
              (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
              R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
              before.status = .unoccupied ∧
              (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
                .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply choice =
                ReferenceFollowerReplyChronology.reply before ∧
              choice.lastDown = before.lastDown ∧
              choice.downBatch = before.downBatch ∧
              choice.buffer = before.buffer ∧
              choice.initializationFailure = before.initializationFailure ∧
              choiceMemory = beforeMemory ∧
              ReferencePrelaunchFollower.acceptedStart choice =
                ReferencePrelaunchFollower.acceptedStart before ∧
              ReferencePrelaunchFollower.acceptedStart before <
                (registers.payload.downRecord i).val.sigma ∧
              (registers.payload.downRecord i).val.sigma =
                R[b.val].input.time.val + 1) ∧
          (let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b.val + 1)
            let V := R[b.val] :: W
            let H := V.takeWhile
              ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
            let Rel := V.dropWhile
              ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
            H ++ Rel = V ∧
              (Rel = [] ↔ ∀ r ∈ V,
                ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice r = true) ∧
              (∀ i (hi : i < Rel.length),
                ∃ j, ∃ hj : j < W.length, Rel[i]'hi = W[j]'hj ∧
                  ∃ selected : ReferenceActivePhysicalStep.Selection (W[j]'hj).input,
                    (W[j]'hj).output.preparation.coordinator.selection = some selected ∧
                    selected.view.pendingAtChoice = ∅ ∧
                    ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
                      (memory : ActiveFollowerLifecycle.LocalMemory p),
                      (ReferenceFollowerFixedReply.actualChoice (W[j]'hj) follower).configuration =
                        .ordinary choice memory → choice.status ≠ .unoccupied) ∧
              ∀ r ∈ V, ∀ selected : ReferenceActivePhysicalStep.Selection r.input,
                r.output.preparation.coordinator.selection = some selected →
                ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected →
              r ∈ H) ∧
          (let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b.val + 1)
            let V := R[b.val] :: W
            let H := V.takeWhile
              ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
            ∀ r ∈ H, ∀ (i : Fin (p.m - 1))
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                .ordinary choice memory →
              choice.status ≠ .released) ∧
          (let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
              rate rewards C_star C_h z (b.val + 1)
            ∀ j : Fin W.length,
              ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
                (selected : ReferenceActivePhysicalStep.Selection W[j.val].input)
                (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
                (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
                (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
                (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
                W[j.val].input.state.coordinator = .live r q base ∧
                r.payload = registers.payload ∧
                W[j.val].output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = registers.payload ∧
                selected.view.pendingAtChoice = r.pendingAtChoice ∧
                W[j.val].output.next.coordinator = .live next owned base ∧
                next.payload = registers.payload ∧
                (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                    W[j.val] selected →
                  next.pendingAtChoice = selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (W[j.val].input.row.2 W[j.val].input.time).1)) ∧
                (¬ ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                    W[j.val] selected →
                  next.pendingAtChoice = selected.view.pendingAtChoice) ∧
                (∀ i, (ReferenceFollowerFixedReply.actualChoice W[j.val] i).configuration =
                  .ordinary (states i) (memories i)) ∧
                (∀ i, i ∉ selected.view.pendingAtChoice →
                  (states i).status ≠ .unoccupied) ∧
                (ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                    W[j.val] selected →
                  selected.view.pendingAtChoice.erase
                    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                      (W[j.val].input.row.2 W[j.val].input.time).1) = ∅ →
                  ∀ i, (states i).status ≠ .unoccupied) ∧
                ∀ i, (states i).status = .unoccupied ∨
                  ∃ (nextFollower : ReferencePrelaunchFollower.State p rate.eta)
                    (nextMemory : ActiveFollowerLifecycle.LocalMemory p),
                    W[j.val].output.next.followers i =
                      .ordinary nextFollower nextMemory ∧
                    nextFollower.status ≠ .unoccupied ∧
                    nextFollower.lastDown = (states i).lastDown ∧
                    ((states i).status = .released →
                      nextFollower.status = .released) ∧
                    (selected.view.pendingAtChoice.Nonempty →
                      (states i).status = .pending →
                      nextFollower.status = .pending) ∧
                    ∀ h : j.val + 1 < W.length,
                      (ReferenceFollowerFixedReply.actualChoice W[j.val + 1] i).configuration =
                        .ordinary nextFollower nextMemory)
      else True := by
  classical
  intro R b
  by_cases hlater :
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hlater]
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hlater] at hhistory
    obtain ⟨registers, owned, base, birthSelected, hnext, hbirth, _hstart,
      hselection,
      hpayload, hpending, _hrbPending, _hbirthNoEvent, hfollower, htail,
      hnoRelease, hframes⟩ := hhistory
    have hstage :=
      ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_stage_partition
        rate rewards C_star C_h z b
    rw [ite_eq_left hlater] at hstage
    refine ⟨registers, owned, base, birthSelected, hnext, hbirth, hselection,
      hpayload, hpending, ?_, ?_, ?_⟩
    · classical
      simpa only [eq_if_iff_implications, and_assoc] using htail
    · intro i
      obtain ⟨before, beforeMemory, choice, choiceMemory, hinput, hbeforeUnoccupied,
        hchoice, hchoiceUnoccupied, hreply, hbank, hbuffer, hfailure, hmemory⟩ :=
        hfollower i
      have hstartEq := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
      have hlastDown : choice.lastDown = before.lastDown := by
        have h := congrArg Prod.fst hreply
        change choice.lastDown = before.lastDown at h
        exact h
      have hstrict := old_accepted_start_lt_birth_word rate rewards C_star C_h z b i
        before beforeMemory hinput registers.payload hlater hbirth
      have hwordTime := payload_down_sigma_at_birth R[b.val] registers.payload hlater hbirth i
      exact ⟨before, beforeMemory, choice, choiceMemory, hinput, hbeforeUnoccupied,
        hchoice, hchoiceUnoccupied, hreply, hlastDown, hbank, hbuffer, hfailure, hmemory,
        hstartEq, hstrict, hwordTime⟩
    · refine ⟨hstage, hnoRelease, ?_⟩
      classical
      simpa only [eq_if_iff_implications, and_assoc] using hframes
  · simp only [ite_eq_right hlater]

/-- At the same actual later-installation birth, every follower's complete
DOWN decoder bank is the fold over the original physical prefix from the
corrected initialization seed. The retained completed and pending entries
are included, and the current pending stamps are strictly before this input. -/
public theorem actual_later_installation_birth_bank_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        ∃ (active : ReferenceActivePhysicalStep.State p rate)
          (_hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))
          (_hseed : ReferenceFollowerDecoderChronology.downBatchSeed active
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)),
          ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate z rewards C_star C_h = some active ∧
          (∀ i : Fin (p.m - 1),
            ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
              (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
              (choice : ReferencePrelaunchFollower.State p rate.eta)
              (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
              (initialFollower : ReferencePrelaunchFollower.State p rate.eta)
              (initialMemory : ActiveFollowerLifecycle.LocalMemory p),
              R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
              before.status = .unoccupied ∧
              (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
                .ordinary choice choiceMemory ∧
              choice.status = .unoccupied ∧
              choice.downBatch = before.downBatch ∧
              choice.buffer = before.buffer ∧
              choice.initializationFailure = before.initializationFailure ∧
              choiceMemory = beforeMemory ∧
              active.followers i = .ordinary initialFollower initialMemory ∧
              ReferenceFollowerDecoderChronology.downBatchWellFormed
                initialFollower.downBatch ∧
              ReferenceFollowerDecoderChronology.downCollectedChronological
                initialFollower.downBatch ∧
              (∀ entry ∈ AffineBatchDecoder.collected initialFollower.downBatch,
                entry.time.val <
                  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ∧
              before.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
                (R.take b.val) initialFollower.downBatch ∧
              ReferenceFollowerDecoderChronology.downBatchWellFormed before.downBatch ∧
              (∀ entry ∈ before.downBatch.pending,
                entry.time.val < R[b.val].input.time.val) ∧
              ReferenceFollowerDecoderChronology.downCollectedChronological
                before.downBatch ∧
              (∀ entry ∈ AffineBatchDecoder.collected before.downBatch,
                entry.time.val < R[b.val].input.time.val))
      else True := by
  classical
  intro R b
  by_cases hlater :
      ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hlater]
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hlater] at hhistory
    obtain ⟨_registers, _owned, _base, _birthSelected, _hnext, _hbirth, _hstart,
      _hselection, _hpayload, _hpending, _hrbPending, _hbirthNoEvent,
      hfollower, _htail, _hnoRelease, _hframes⟩ := hhistory
    obtain ⟨active, hmode, hseed, hlaunch⟩ :=
      completeSuffix_launch_route rate rewards C_star C_h z (by omega)
    refine ⟨active, hmode, hseed, hlaunch, ?_⟩
    intro i
    obtain ⟨before, beforeMemory, choice, choiceMemory, hinput, hbeforeStatus,
      hchoice, hchoiceStatus, hreply, hbank, hbuffer, hfailure, hmemory⟩ := hfollower i
    obtain ⟨initialFollower, initialMemory, hinitial, hwellSeed, hchronSeed,
      hstampSeed, hbankReplay, hwell, hpendingBound, hchron, hcollectedBound,
      _hoccupiedPending⟩ :=
      completeSuffix_input_down_bank_prefix rate rewards C_star C_h z active
        hmode hseed hlaunch b i before beforeMemory hinput
    exact ⟨before, beforeMemory, choice, choiceMemory, initialFollower, initialMemory,
      hinput, hbeforeStatus, hchoice, hchoiceStatus, hbank, hbuffer, hfailure, hmemory,
      hinitial, hwellSeed, hchronSeed, hstampSeed, hbankReplay, hwell, hpendingBound,
      hchron, hcollectedBound⟩
  · simp only [ite_eq_right hlater]

section ChoiceStages

open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence

variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_clock
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected r.input.time.val r.input.state := by
  obtain ⟨hc, _, hr⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  have hl := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate z rewards C_star C_h hc
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate z rewards C_star C_h initial hl
  have hseed : ReferenceCoordinatorClockDomains.clockAt z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) initial := by
    have hf := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate z rewards C_star C_h hc).coordinatorFirst
    simp only [ReferenceCoordinatorClockDomains.clockAt, show initial.coordinator = .first from hf]
  have hrun := ReferenceRunClockPreservation.run_clockAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h; omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some rate z rewards C_star C_h initial hl) hseed
  have h := hrun.2.2.2 _ (by rw [← hrecords]; exact List.getElem_mem k.isLt)
  simpa only [h.2.2.1, h.2.2.2.1] using h.1

private theorem startRound_no_cutoff
    (t : Fin p.T) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (out : CoordinatorPhaseClock.StartRoundResult p)
    (h : CoordinatorPhaseClock.startRound p rate.eta.val t clock pending = .ok out)
    (hu : out.clock.u = none) :
    CoordinatorPhaseClock.detectCutoff clock t = .ok .noCutoff := by
  classical
  have hp : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
    by_contra hn
    simp only [CoordinatorPhaseClock.startRound, hn, ↓reduceIte] at h
    cases h
  have hv : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock := by
    by_contra hn
    simp only [CoordinatorPhaseClock.startRound, hp, hn, ↓reduceDIte, ↓reduceIte] at h
    cases h
  have ht : CoordinatorPhaseClock.startRoundTimeValid p t clock := by
    by_contra hn
    simp only [CoordinatorPhaseClock.startRound, hp, hv, hn, ↓reduceDIte, ↓reduceIte] at h
    cases h
  cases hd : CoordinatorPhaseClock.detectCutoff clock t with
  | error failure =>
      simp only [CoordinatorPhaseClock.startRound, hp, hv, ht, hd, ↓reduceDIte, ↓reduceIte] at h
      cases h
  | ok decision =>
      cases decision with
      | noCutoff => rfl
      | cutoff sigma hsigma =>
          obtain ⟨result, hr, hc, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
            p rate.eta.val t sigma clock pending hp hv ht hsigma hd
          have he := Except.ok.inj (h.symm.trans hr)
          rw [he, hc] at hu
          cases hu

/-- PREPARE on an actual continuing record preserves an occupied current
payload's entire local state and memory. Its cutoff test reads the same prior
proposal coordinate as the coordinator; no new launch or reset occurs. -/
private theorem complete_continuing_prepare_occupied
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hin : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.coordinator = .live r q base)
    (hc : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = true)
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.state.followers i = .ordinary before memory)
    (ho : before.status ≠ .unoccupied) (hd : before.lastDown = some (r.payload.downRecord i)) :
    (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] i).configuration = .ordinary before memory := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  have hclock := complete_clock rewards C_star C_h z k
  change ReferenceCoordinatorClockDomains.clockAt record.input.rows record.input.selected
    record.input.time.val record.input.state at hclock
  change record.input.state.coordinator = .live r q base at hin
  change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest record = true at hc
  simp only [ReferenceCoordinatorClockDomains.clockAt, hin] at hclock
  obtain ⟨hst, _hvalid, hsigma, hu, _hg, hstarted, _hgrid, hproposal⟩ := hclock
  have hp : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  have hdata := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
    rate rewards C_star C_h z k r q base hin
  have hdispatch : record.output.preparation.coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)) := hp ▸ hdata.1
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hc
  rw [hdispatch] at hc
  cases hchosen : CoordinatorRoundDispatch.dispatchLive (liveInput record.input r q base)
    <;> simp only [hchosen, Bool.false_eq_true] at hc
  rename_i dispatched hstart continuation arm
  have hbranch := hdata.2
  rw [hchosen] at hbranch
  have hnone := hbranch.2.1
  have hdetect := startRound_no_cutoff (rate := rate) record.input.time r.priorClock
    (liveRegistersAt r record.input.time).clockPending dispatched.startResult hstart hnone
  have hread := CoordinatorPhaseClock.savedPriorProposal_correct r.priorClock record.input.time
    r.time _ hproposal hst
  have hcauses : record.input.time.val + 1 ≠ r.priorClock.g ∧
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time = false := by
    change CoordinatorPhaseClock.savedPriorProposal r.priorClock record.input.time =
      .ok (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time) at hread
    generalize heq : r.priorClock = clock at hsigma hu hdetect hread ⊢
    rcases clock with ⟨sigma, u, g, token⟩
    change sigma = some r.payload.sigma at hsigma
    change u = none at hu
    subst sigma
    subst u
    by_cases hg : record.input.time.val + 1 = g
    · simp [CoordinatorPhaseClock.detectCutoff, FollowerCutoffScan.calendarRound, hg] at hdetect
    · refine ⟨hg, ?_⟩
      cases hb : FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time with
      | false => rfl
      | true =>
          simp [CoordinatorPhaseClock.detectCutoff, hread,
            FollowerCutoffScan.calendarRound, hg, hb] at hdetect
          cases hdetect
  obtain ⟨choice, hv, hlocal, hchoice, _⟩ :=
    ReferenceCompleteFollowerPreparation.complete_ordinary_input_prepare
      rewards C_star C_h z k i before memory hf
  obtain ⟨stamp, hstamp, htoken⟩ :=
    ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h z k i before memory hf ho
  change stamp.val + 1 = record.input.time.val at hstamp
  have he : stamp = r.time := Fin.ext (by omega)
  rw [he] at htoken
  change memory.lastProposalRead = some ⟨r.time,
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row r.time⟩ at htoken
  have hfield : (r.payload.downRecord i).val.sigma = r.payload.sigma.val + 1 := by
    rw [r.payload.downRecord_fields i]
  have hcoord : ActiveFollowerLifecycle.acceptedStartCoordinate (r.payload.downRecord i) = r.payload.sigma := by
    apply Fin.ext
    have := ActiveFollowerLifecycle.accepted_start_coordinate_one_based (r.payload.downRecord i)
    omega
  have hgridEq : r.priorClock.g = FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma :=
    by simpa only [CoordinatorPhaseClock.boundaryFromSigma, hsigma] using _hvalid.1
  have hsame : choice = before := by
    have hbound : record.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
      rw [← hgridEq]
      omega
    have hs := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta record.input.time
      before memory ho hv (r.payload.downRecord i) hd
      (by rw [hfield]; omega)
      (by simpa only [hcoord] using hbound) _ htoken hst
    rw [hcoord, ← hgridEq, hcauses.2] at hs
    simp only [hcauses.1.symm, decide_false, Bool.false_or, Bool.false_eq_true, ite_false] at hs
    change ActiveFollowerLifecycle.startRound rate.eta record.input.time before memory = .ok (choice, memory) at hlocal
    exact (Prod.mk.inj (Except.ok.inj (hlocal.symm.trans hs))).1
  simpa only [hsame] using hchoice

private theorem continuing_current_input_choice_occupied
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hin : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator = .live r q base)
    (hc : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] = true)
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.followers i = .ordinary before memory)
    (hd : before.lastDown = some (r.payload.downRecord i)) :
    ∃ choiceMemory,
      (ReferenceFollowerFixedReply.actualChoice
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val] i).configuration =
            .ordinary before choiceMemory ∧ before.status ≠ .unoccupied := by
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  obtain ⟨_crossing, _span, hrecord⟩ :=
    ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z k
  have hrow : record.input.row = z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
    change ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get k).input.row = _
    rw [hrecord]
    rfl
  have hcut := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h z k
  dsimp only at hcut
  rw [hin] at hcut
  have hstart : ActiveFollowerDownAcceptance.downStart p rate (r.payload.downRecord i) =
      r.payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one
      p rate (r.payload.downRecord i)
    have hfields := congrArg OrdinaryMessageCodec.DownFields.sigma
      (r.payload.downRecord_fields i)
    change (r.payload.downRecord i).val.sigma = r.payload.sigma.val + 1 at hfields
    omega
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h z k i before memory hf (r.payload.downRecord i) hd
  rw [hstart, hrow] at hphase
  have ho : before.status ≠ .unoccupied := by
    intro hu
    exact (Nat.not_le_of_lt hcut.2) (hphase.mp hu)
  exact ⟨memory, complete_continuing_prepare_occupied rewards C_star C_h z k
    r q base hin hc i before memory hf ho hd, ho⟩

/-- One actual selected receiver step either carries the selected current
word or preserves the whole old reply while remaining unoccupied. Each
branch is discharged by its actual complete-source forward producer. -/
private theorem selected_next_reply_cases
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (selected : Selection (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input)
    (hs : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] i).configuration = .ordinary choice memory) :
    ∃ next nextMemory,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].output.next.followers i = .ordinary next nextMemory ∧
      (next.lastDown = some (selected.view.payload.downRecord i) ∨
        (choice.status = .unoccupied ∧ next.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply next =
            ReferenceFollowerReplyChronology.reply choice)) := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k.val]
  let own := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
    record.input.time own rate choice
  let expected := ReferenceDownReception.expectedDownFlatWord
    record.output.preparation.coordinator.downView i record.input.row record.input.time
  let parsed := ReferenceDownReception.ordinaryParse p rate decoded.2
  by_cases hu : choice.status = .unoccupied
  · by_cases ha : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
        decoded.2 = expected ∧ ReferenceDownReception.ordinaryLocalAcceptanceTest
          p rate record.input.time choice parsed
    · obtain ⟨selected', hs', _hview, _hbranch, _hraw, _hparsed, _haccepted,
        _birth, _beta, _hbefore, _hbirth, _hbase, _hcredit, final, htail⟩ :=
        ReferenceCompleteAcceptedCurrentDownForward.complete_ordinary_unoccupied_accepted_current_down_forward
          rewards C_star C_h z k i choice memory hc hu ha
      have heq : selected' = selected := Option.some.inj (hs'.symm.trans hs)
      subst selected'
      rcases htail with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _hdomain, _, _, _, _, _, _, _houtput, hnext⟩
      exact ⟨_, _, hnext, Or.inl rfl⟩
    · obtain ⟨logged, _hlogging, _hbuffer, _hchoiceDomain, _hoperation,
        _hloggedDomain, _hloggedFrame, _hordered, _hbounded, htail⟩ :=
        ReferenceCompleteUnoccupiedNonacceptingForward.complete_ordinary_unoccupied_nonaccepting_forward
          rewards C_star C_h z k i choice memory hc hu ha
      rcases htail with
        ⟨_hconsume, _hfinish, hstatus, hlast, hS, hdelta, hbacklog,
          _hnextBuffer, _hfailure, _hdomain, _hendpoint, _hdecoded, _hzero,
          _hexpected, _hdiagnostic, _houtput, hnext⟩
      refine ⟨_, _, hnext, Or.inr ⟨hu, hstatus, ?_⟩⟩
      exact congrArg₂ Prod.mk hlast
        (congrArg₂ Prod.mk hS (congrArg₂ Prod.mk hdelta hbacklog))
  · obtain ⟨states, memories, hchoices, hfields, _hincoming, _houtgoing⟩ :=
      ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
        rewards C_star C_h z k selected hs
    have hchoiceEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hchoices i).symm.trans hc)
    have hcurrent : choice.lastDown = some (selected.view.payload.downRecord i) := by
      rw [← hchoiceEq.1]
      exact hfields i (by rw [hchoiceEq.1]; exact hu)
    obtain ⟨_M, _hdown, _htime, _hdomain, _b, _j, _P, _beta, hmass⟩ :=
      ReferenceCompleteOccupiedServiceForward.complete_ordinary_occupied_service_forward
        rewards C_star C_h z k i choice memory hc hu
    obtain ⟨_, _, _, _, _, _, _, _, _, hprepared⟩ := hmass
    obtain ⟨_, _, _, _, _serviced, next, nextMemory, htail⟩ := hprepared
    rcases htail with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlast,
        _, _, _, _, _, _, _, _, _, _, _, hnext⟩
    exact ⟨next, nextMemory, hnext, Or.inl (hlast.trans hcurrent)⟩

private theorem birth_continuing_index {α : Type} (records : List α)
    (test : α → Bool) (b : Fin records.length)
    (j : Fin (records[b.val] :: (records.drop (b.val + 1)).takeWhile test).length) :
    ∃ h : b.val + j.val < records.length,
      (records[b.val] :: (records.drop (b.val + 1)).takeWhile test).get j =
        records[b.val + j.val]'h := by
  have hj := j.isLt
  cases hn : j.val with
  | zero =>
      refine ⟨by omega, ?_⟩
      simp only [List.get_eq_getElem, hn, Nat.add_zero, List.getElem_cons_zero]
  | succ n =>
      have hnlt : n < ((records.drop (b.val + 1)).takeWhile test).length := by
        simp only [List.length_cons, hn] at hj
        omega
      have hlen := (List.takeWhile_prefix (l := records.drop (b.val + 1)) test).length_le
      simp only [List.length_drop] at hlen
      refine ⟨by omega, ?_⟩
      simp only [List.get_eq_getElem, hn, List.getElem_cons_succ]
      rw [(List.takeWhile_prefix test).getElem hnlt, List.getElem_drop]
      congr 1
      omega

private theorem later_unoccupied_choice_reply
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (beforeMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hinput : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[b.val].input.state.followers i = .ordinary before beforeMemory) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    ∀ j : Fin V.length, ∀ choice memory,
      (ReferenceFollowerFixedReply.actualChoice (V.get j) i).configuration =
        .ordinary choice memory →
      choice.status = .unoccupied → ReferenceFollowerReplyChronology.reply choice =
        ReferenceFollowerReplyChronology.reply before := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  let V := R[b.val] :: W
  have hhistory :=
    ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
      rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hhistory
  obtain ⟨rb, _qb, beta, birthSelected, _hnext, _hbirth, _hlater, hbirthSelection,
    hbirthPayload, _hbirthPending, _hrbPending, _hnoEvent, hfollowers, _htail,
    _hnoReleased, hframes⟩ := hhistory
  obtain ⟨beforeActual, _beforeMemory, birthChoice, _birthMemory, hbefore,
    _hu, hbirthChoice, _hbirthUnoccupied, hbirthReply, _⟩ := hfollowers i
  have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hbefore.symm.trans hinput)
  rw [heq.1] at hbirthReply
  have hindex (j : Fin V.length) : ∃ hj : b.val + j.val < R.length,
      V[j.val] = R[b.val + j.val]'hj :=
    birth_continuing_index R _ b j
  have hselected (j : Fin V.length) : ∃ selected : Selection (V.get j).input,
      (V.get j).output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = rb.payload := by
    cases hj : j.val with
    | zero =>
        have hzero : V.get j = R[b.val] := by
          simp only [List.get_eq_getElem, V, hj, List.getElem_cons_zero]
        rw [hzero]
        exact ⟨birthSelected, hbirthSelection, hbirthPayload⟩
    | succ n =>
        have hn : n < W.length := by
          have := j.isLt
          simp only [V, List.length_cons] at this
          omega
        have hsucc : V.get j = W[n] := by
          simp only [List.get_eq_getElem, V, hj, List.getElem_cons_succ]
        rw [hsucc]
        obtain ⟨_r, _q, selected, _next, _owned, _states, _memories,
          _hin, _hp, hs, hp, _⟩ := hframes ⟨n, hn⟩
        exact ⟨selected, hs, hp⟩
  change ∀ j : Fin V.length, ∀ choice memory,
    (ReferenceFollowerFixedReply.actualChoice (V.get j) i).configuration =
      .ordinary choice memory →
    choice.status = .unoccupied → ReferenceFollowerReplyChronology.reply choice =
      ReferenceFollowerReplyChronology.reply before
  intro j
  generalize hj : j.val = n
  induction n generalizing j with
  | zero =>
      intro choice memory hc _hu
      have hc' : (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
          .ordinary choice memory := by
        simpa only [List.get_eq_getElem, V, hj, List.getElem_cons_zero] using hc
      have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hc'.symm.trans hbirthChoice)
      rw [heq.1]
      exact hbirthReply
  | succ n ih =>
      intro choice memory hc hchoiceUnoccupied
      have hn : n < V.length := by
        have := j.isLt
        omega
      let prev : Fin V.length := ⟨n, hn⟩
      obtain ⟨hprevBound, hprev⟩ := hindex prev
      obtain ⟨hcurrentBound, hcurrent⟩ := hindex j
      let previous : Fin R.length := ⟨b.val + n, hprevBound⟩
      let current : Fin R.length := ⟨b.val + j.val, hcurrentBound⟩
      obtain ⟨_oldInput, oldMemory, oldChoice, _hinputOld, _hvalidOld,
        _hstartOld, hchoiceOld, _⟩ :=
        ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
          (rate := rate) rewards C_star C_h z previous i
      have hchoiceOld' : (ReferenceFollowerFixedReply.actualChoice V[prev.val] i).configuration =
          .ordinary oldChoice oldMemory := by rw [hprev]; exact hchoiceOld
      obtain ⟨selected, hs, hpPrev⟩ := hselected prev
      have hforward := selected_next_reply_cases (rate := rate) rewards C_star C_h z previous
      rw [← hprev] at hforward
      obtain ⟨next, nextMemory, hnext, hcases⟩ := hforward selected hs i oldChoice oldMemory hchoiceOld'
      have hlink : V[j.val].input.state = V[prev.val].output.next := by
        rw [hcurrent, hprev]
        have hsucc : b.val + j.val = (b.val + n) + 1 := by omega
        simp only [hsucc]
        exact ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
          rewards C_star C_h z (b.val + n) (by
            change (b.val + n) + 1 < R.length
            rw [← hsucc]
            exact hcurrentBound)
      have hnextInput : V[j.val].input.state.followers i = .ordinary next nextMemory := by
        rw [hlink]
        exact hnext
      rcases hcases with hcurrentDown | ⟨holdUnoccupied, _hnextUnoccupied, hreply⟩
      · have hnW : n < W.length := by
          have := j.isLt
          simp only [V, List.length_cons] at this
          omega
        obtain ⟨r, q, selectedNow, _out, _owned, _states, _memories,
          hin, hp, _hs, _hpay, _⟩ := hframes ⟨n, hnW⟩
        have hrecord : V[j.val] = W[n] := by simp only [V, hj, List.getElem_cons_succ]
        have hin' : V[j.val].input.state.coordinator = .live r q beta := by rw [hrecord]; exact hin
        have hcontinue : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest V[j.val] = true := by
          rw [hrecord]
          exact List.mem_takeWhile_imp (List.getElem_mem hnW)
        have hdown : next.lastDown = some (r.payload.downRecord i) := by
          rw [hp]
          rw [← hpPrev]
          exact hcurrentDown
        have hoccupied := continuing_current_input_choice_occupied (rate := rate)
          rewards C_star C_h z current
        rw [← hcurrent] at hoccupied
        obtain ⟨nextChoiceMemory, hnextChoice, hnextOccupied⟩ :=
          hoccupied r q beta hin' hcontinue i next nextMemory hnextInput hdown
        have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          (hc.symm.trans hnextChoice)
        exact (hnextOccupied (heq.1 ▸ hchoiceUnoccupied)).elim
      · obtain ⟨inputNow, memoryNow, hinputNow, hchoiceReply, _⟩ :=
          ReferenceFollowerReplyChronology.record_input_to_choice V[j.val] i choice memory hc
        have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
          (hinputNow.symm.trans hnextInput)
        have hreplyNow : ReferenceFollowerReplyChronology.reply choice =
            ReferenceFollowerReplyChronology.reply next := heq.1 ▸ hchoiceReply
        exact hreplyNow.trans (hreply.trans (ih prev rfl oldChoice oldMemory hchoiceOld' holdUnoccupied))

/-- The actual handover choices have three stages: awaiting with the complete
old birth reply, accepted-current with a missing confirmation, or current with
its confirmation already removed. Occupied choices remain pending while any
confirmation is missing. This is physical chronology, before analysis stops. -/
public theorem actual_later_installation_handover_choice_stages
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        ∃ payload : Payload rate,
          InstallationBirth R[b.val] payload ∧
          ∀ i : Fin (p.m - 1),
            ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
              (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
              R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
              before.status = .unoccupied ∧
              ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
              let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
                rate rewards C_star C_h z (b.val + 1)
              let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
              ∀ j : Fin H.length,
                ∃ (selected : Selection H[j.val].input)
                  (choice : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p),
                  H[j.val].output.preparation.coordinator.selection = some selected ∧
                  selected.view.payload = payload ∧
                  (ReferenceFollowerFixedReply.actualChoice H[j.val] i).configuration =
                    .ordinary choice memory ∧
                  ((i ∈ selected.view.pendingAtChoice ∧ choice.status = .unoccupied ∧
                      ReferenceFollowerReplyChronology.reply choice =
                        ReferenceFollowerReplyChronology.reply before ∧
                      ReferencePrelaunchFollower.acceptedStart choice =
                        ReferencePrelaunchFollower.acceptedStart before) ∨
                    (i ∈ selected.view.pendingAtChoice ∧ choice.status = .pending ∧
                      choice.lastDown = some (payload.downRecord i) ∧
                      ReferencePrelaunchFollower.acceptedStart choice =
                        (payload.downRecord i).val.sigma) ∨
                    (i ∉ selected.view.pendingAtChoice ∧ choice.status = .pending ∧
                      choice.lastDown = some (payload.downRecord i) ∧
                      ReferencePrelaunchFollower.acceptedStart choice =
                        (payload.downRecord i).val.sigma))
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    obtain ⟨rb, _qb, beta, birthSelected, _hnext, hbirth, _hlater, hbirthSelection,
      hbirthPayload, hbirthPending, _hrbPending, _hnoEvent, hfollowers, _htail,
      hnoReleased, hframes⟩ := hhistory
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    have hindex (j : Fin V.length) : ∃ hj : b.val + j.val < R.length,
        V[j.val] = R[b.val + j.val]'hj :=
      birth_continuing_index R _ b j
    have hselected (j : Fin V.length) :
        ∃ selected : Selection (V.get j).input,
          (V.get j).output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = rb.payload ∧
          ∀ i choice memory,
            (ReferenceFollowerFixedReply.actualChoice (V.get j) i).configuration =
              .ordinary choice memory →
            i ∉ selected.view.pendingAtChoice → choice.status ≠ .unoccupied := by
      cases hj : j.val with
      | zero =>
          have hbase : ∃ selected : Selection R[b.val].input,
            R[b.val].output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = rb.payload ∧
              ∀ i choice memory,
                (ReferenceFollowerFixedReply.actualChoice R[b.val] i).configuration =
                  .ordinary choice memory →
                i ∉ selected.view.pendingAtChoice → choice.status ≠ .unoccupied := by
            refine ⟨birthSelected, hbirthSelection, hbirthPayload, ?_⟩
            intro i _choice _memory _hc hi
            exact (hi (hbirthPending ▸ Finset.mem_univ i)).elim
          have hzero : V.get j = R[b.val] := by
            simp only [List.get_eq_getElem, V, hj, List.getElem_cons_zero]
          rw [hzero]
          exact hbase
      | succ n =>
          have hn : n < W.length := by
            have := j.isLt
            simp only [V, List.length_cons] at this
            omega
          obtain ⟨_r, _q, selected, _next, _owned, states, memories,
            _hin, _hp, hs, hp, _hpend, _hout, _hnextPay, _hupdate,
            hchoices, homitted, _⟩ := hframes ⟨n, hn⟩
          have htailFrame : ∃ selected : Selection W[n].input,
              W[n].output.preparation.coordinator.selection = some selected ∧
                selected.view.payload = rb.payload ∧
                ∀ i choice memory,
                  (ReferenceFollowerFixedReply.actualChoice W[n] i).configuration =
                    .ordinary choice memory →
                  i ∉ selected.view.pendingAtChoice → choice.status ≠ .unoccupied := by
            refine ⟨selected, hs, hp, ?_⟩
            intro i choice memory hc hi
            have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
              ((hchoices i).symm.trans hc)
            rw [← heq.1]
            exact homitted i hi
          have hsucc : V.get j = W[n] := by
            simp only [List.get_eq_getElem, V, hj, List.getElem_cons_succ]
          rw [hsucc]
          exact htailFrame
    refine ⟨rb.payload, hbirth, ?_⟩
    intro i
    obtain ⟨before, beforeMemory, birthChoice, birthMemory, hinput, hu,
      hbirthChoice, _hbirthUnoccupied, hbirthReply, _⟩ := hfollowers i
    have hstrict := old_accepted_start_lt_birth_word rate rewards C_star C_h z b i
      before beforeMemory hinput rb.payload hb hbirth
    refine ⟨before, beforeMemory, hinput, hu, hstrict, ?_⟩
    have hstage := later_unoccupied_choice_reply (rate := rate) rewards C_star C_h z
      b hb i before beforeMemory hinput
    intro j
    have hjV : j.val < V.length :=
      lt_of_lt_of_le j.isLt (List.takeWhile_prefix _).length_le
    let v : Fin V.length := ⟨j.val, hjV⟩
    have hH : H[j.val] = V[v.val] := (List.takeWhile_prefix _).getElem j.isLt
    obtain ⟨selected, hs, hp, homitted⟩ := hselected v
    obtain ⟨hk, hrecord⟩ := hindex v
    have hdata :=
      ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
        (rate := rate) rewards C_star C_h z ⟨b.val + v.val, hk⟩
    rw [← hrecord] at hdata
    obtain ⟨choiceStates, choiceMemories, hchoices, hfields, _⟩ := hdata selected hs
    let choice := choiceStates i
    let memory := choiceMemories i
    have hchoice := hchoices i
    have hmemH : V[v.val] ∈ H := by rw [← hH]; exact List.getElem_mem j.isLt
    have hno := hnoReleased V[v.val] hmemH i choice memory hchoice
    rw [hH]
    refine ⟨selected, choice, memory, hs, hp, hchoice, ?_⟩
    have homit : i ∉ selected.view.pendingAtChoice → choice.status ≠ .unoccupied :=
      homitted i choice memory hchoice
    by_cases huChoice : choice.status = .unoccupied
    · have hreply := hstage v choice memory hchoice huChoice
      exact Or.inl ⟨by_contra (fun hi => homit hi huChoice), huChoice, hreply,
          ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply⟩
    · have hpending : choice.status = .pending := by
        cases h : choice.status with
        | unoccupied => exact (huChoice h).elim
        | pending => rfl
        | released => exact (hno h).elim
      have hdown : choice.lastDown = some (rb.payload.downRecord i) := by
        rw [← hp]
        exact hfields i huChoice
      have hstart : ReferencePrelaunchFollower.acceptedStart choice =
          (rb.payload.downRecord i).val.sigma := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hdown]
      by_cases hi : i ∈ selected.view.pendingAtChoice
      · exact Or.inr (Or.inl ⟨hi, hpending, hdown, hstart⟩)
      · exact Or.inr (Or.inr ⟨hi, hpending, hdown, hstart⟩)
  · simp only [ite_eq_right hb]

/-- Splice the birth bank into the same actual handover prefix. The seed and
both endpoint banks come from the original corrected launch, so completed
history and an arbitrary partial pending batch are retained literally. -/
public theorem actual_later_installation_handover_bank_replay
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ b : Fin R.length,
      if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
        ∀ (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
          (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
          R[b.val].input.state.followers i = .ordinary before beforeMemory →
          let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b.val + 1)
          let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
          ∀ (j : Fin H.length) (state : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            H[j.val].input.state.followers i = .ordinary state memory →
            state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
              (H.take j.val) before.downBatch
      else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    intro i before beforeMemory hbefore
    let V := R[b.val] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let H := V.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    change ∀ (j : Fin H.length) (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      H[j.val].input.state.followers i = .ordinary state memory →
      state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
        (H.take j.val) before.downBatch
    intro j state memory hstate
    have hnonempty : 0 < R.length := Nat.lt_of_le_of_lt (Nat.zero_le b.val) b.isLt
    obtain ⟨active, hmode, hseed, hlaunch⟩ :=
      completeSuffix_launch_route rate rewards C_star C_h z hnonempty
    obtain ⟨initialFollower, initialMemory, hinitial, _hwell, _hchron,
      _hstamps, hbirthBank, _⟩ :=
      completeSuffix_input_down_bank_prefix rate rewards C_star C_h z active
        hmode hseed hlaunch b i before beforeMemory hbefore
    have hV : V.IsPrefix (R.drop b.val) := by
      rw [List.drop_eq_getElem_cons b.isLt]
      exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
    have hH : H.IsPrefix (R.drop b.val) := (List.takeWhile_prefix _).trans hV
    have hjV : j.val < V.length := lt_of_lt_of_le j.isLt (List.takeWhile_prefix _).length_le
    obtain ⟨hk, hrecord⟩ := birth_continuing_index R _ b ⟨j.val, hjV⟩
    have hHrecord : H[j.val] = R[b.val + j.val]'hk :=
      ((List.takeWhile_prefix _).getElem j.isLt).trans hrecord
    have hcurrentInput : R[b.val + j.val].input.state.followers i = .ordinary state memory := by
      rw [← hHrecord]
      exact hstate
    obtain ⟨initialFollower', initialMemory', hinitial', _hwell', _hchron',
      _hstamps', hcurrentBank, _⟩ :=
      completeSuffix_input_down_bank_prefix rate rewards C_star C_h z active
        hmode hseed hlaunch ⟨b.val + j.val, hk⟩ i state memory hcurrentInput
    have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hinitial'.symm.trans hinitial)
    rw [hsame.1] at hcurrentBank
    have htake : (R.drop b.val).take j.val = H.take j.val := by
      obtain ⟨tail, htail⟩ := hH
      rw [← htail, List.take_append_of_le_length (Nat.le_of_lt j.isLt)]
    have hsplit : R.take (b.val + j.val) = R.take b.val ++ H.take j.val := by
      rw [List.take_add, htake]
    calc
      state.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
          (R.take b.val ++ H.take j.val) initialFollower.downBatch := by
        rw [← hsplit]
        exact hcurrentBank
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i (H.take j.val)
          (ReferenceFollowerDownDecoderReplay.replayDownCalls i (R.take b.val)
            initialFollower.downBatch) := by
        simp only [ReferenceFollowerDownDecoderReplay.replayDownCalls,
          ReferenceFollowerDownDecoderReplay.actualDownCalls, List.filterMap_append,
          ReferenceFollowerDownDecoderReplay.foldDownCalls, List.foldl_append]
      _ = ReferenceFollowerDownDecoderReplay.replayDownCalls i (H.take j.val)
          before.downBatch := by rw [← hbirthBank]
  · simp only [ite_eq_right hb]

end ChoiceStages

end Bandits.Support.ReferencePostReplacementCollectionHandoverReplay

end
