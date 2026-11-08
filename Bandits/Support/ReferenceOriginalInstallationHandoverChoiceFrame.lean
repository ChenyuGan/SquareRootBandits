/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalFixedInstallationHandoverSupport

import Mathlib.Tactic

/-!
# Actual choice frames for an original fixed installation

This module connects the original fixed-installation raw H predicate to the
actual prepared CHOICE row. Initial rows use the accepted first-live source
window; later rows use the same actual empty-COLLECTION birth index.

Sources: ZIP4 `05_binary_transport.tex:244-289`,
`06_interruptions.tex:431-490`, and `appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstLiveHandoverBoundaryFactorization
open scoped Classical

namespace Bandits.Support.ReferenceOriginalInstallationHandoverChoiceFrame

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev Source := BootstrapPrivateRoundStreams.SourceInput p
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

local notation "lookup" =>
  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "rawPending" =>
  ReferenceOriginalFixedInstallationHandoverSupport.rawPending rate rewards C_star C_h
local notation "maskedPending" =>
  ReferenceOriginalFixedInstallationHandoverSupport.pending rate rewards C_star C_h
local notation "before" =>
  ReferenceOriginalFixedInstallationHandoverSupport.before rate rewards C_star C_h
local notation "after" =>
  ReferenceOriginalFixedInstallationHandoverSupport.after rate rewards C_star C_h
local notation "preRoundStatus" =>
  ReferenceOriginalFixedInstallationHandoverSupport.preRoundStatus rate rewards C_star C_h

private theorem initial_window_choice_frame
    (z : Source) (j : Fin (ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z).length)
    (record : Record (p := p) (rate := rate))
    (hrecord : record = (ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z)[j.val])
    (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection
      record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hi : i ∈ selected.view.pendingAtChoice) :
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      (∀ k, (record.output.preparation.followers.followers k).configuration =
        .ordinary (states k) (memories k)) ∧
      (∀ k, (states k).status ≠ .unoccupied →
        (states k).lastDown = some (selected.view.payload.downRecord k)) ∧
      (∀ k, (states k).status ≠ .released) := by
  let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
    rate rewards C_star C_h z
  have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hempty := ReferenceOriginalInitialTransferWindowGeometry.raw_window_empty_of_no_launch
      rate rewards C_star C_h z hnone
    have : ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
        rate rewards C_star C_h z = [] := hempty
    rw [this] at j
    exact Fin.elim0 j
  obtain ⟨active, hlaunch⟩ := Option.ne_none_iff_exists'.mp hlaunchNe
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by simp [hlaunch])
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hsourceLaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross
  have hcellLaunch := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate z rewards C_star C_h hcross
  let actualSeed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hcross
  have hinitialEq : initial = ReferenceFirstLaunchNumericalCell.launchState
      rate z rewards C_star C_h hcross :=
    Option.some.inj (hsourceLaunch.symm.trans hcellLaunch.1)
  have hdecoderSeed := ReferenceFirstLiveDownCompletionReadout.actual_corrected_decoder_seed
    rate z rewards C_star C_h hcross
  have hseedLastDown : ∀ k, (actualSeed.followers k).lastDown = none := by
    intro k
    obtain ⟨state, memory, hstate, hnone, _, _, _, _⟩ := hdecoderSeed k
    have hstateSeed : initial.followers k = .ordinary (actualSeed.followers k)
        (actualSeed.memory k) := by
      simpa only [initial, hinitialEq, actualSeed] using actualSeed.configuration k
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hstate.symm.trans hstateSeed)
    rw [← heq.1]
    exact hnone
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  have hs : s ≤ p.T := by
    simpa only [s] using ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp only [count]; omega
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    have hsElapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
      dsimp [s, ReferenceCompletePhysicalHistory.physicalStart,
        ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput]
    simpa only [initial, hinitialEq, s, hsElapsed] using hcanonical.2.1
  have hfirst : initial.coordinator = .first := by
    simpa only [initial] using hcanonical.1
  have hinitialFollowers : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    simpa only [initial] using hcanonical.2.2
  let sourceRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hmode
  let sourceWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow sourceRun.records
  have hrunRecords : sourceRun.records =
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h :=
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hsourceLaunch).symm
  have hwindow : W = sourceWindow := by
    calc
      W = (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).takeWhile
          (fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) := by
            simpa only [W, ReferenceOriginalInitialTransferWindowGeometry.rawCompleteSuffixRecords] using
              ReferenceOriginalInitialTransferWindowGeometry.raw_window_eq_complete_suffix_takeWhile
                rate rewards C_star C_h z
      _ = ReferenceFirstLiveConfirmationHistory.firstLiveWindow sourceRun.records := by
            rw [← hrunRecords]
            rfl
      _ = sourceWindow := rfl
  have hrecordMem : record ∈ sourceWindow := by
    rw [hrecord]
    rw [← hwindow]
    exact List.getElem_mem j.isLt
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hrecordMem
  let k : Fin sourceWindow.length := ⟨n, hn⟩
  have hrecordEq : record = sourceWindow[k.val] := by
    change record = sourceWindow[n]
    exact hget.symm
  clear hrecord
  subst record
  have hselected' : sourceWindow[k.val].output.preparation.coordinator.selection = some selected := by
    simpa only [k] using hselected
  have hprepareSelected :
      (ReferenceActivePhysicalStep.prepare sourceWindow[k.val].input).coordinator.selection = some selected := by
    simpa only [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected'
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode hfirst actualSeed.followers actualSeed.memory actualSeed.configuration
    actualSeed.S_zero actualSeed.delta_zero actualSeed.backlog_zero hseedLastDown
    actualSeed.unoccupied actualSeed.bufferValid actualSeed.chronologicalBuffer
    actualSeed.bufferStamps actualSeed.decoderValid
  have hchoices : ∀ l : Fin (p.m - 1),
      ∃ choice choiceMemory next nextMemory,
        (sourceWindow[k.val].output.preparation.followers.followers l).configuration =
          .ordinary choice choiceMemory ∧
        (sourceWindow[k.val].output.followers l).configuration = .ordinary next nextMemory ∧
        (sourceWindow[k.val].output.followers l).failure = none ∧
        ∀ selected' : ReferenceActivePhysicalStep.Selection sourceWindow[k.val].input,
          sourceWindow[k.val].output.preparation.coordinator.selection = some selected' →
          choice.status ≠ .unoccupied →
            choice.lastDown = some (selected'.view.payload.downRecord l) :=
    hsafe.2 k
  choose states memories nextStates nextMemories hprepared _hnext _hfailure hcarried using hchoices
  have hnoReleased := ReferenceFirstLiveConfirmationHistory.run_firstLive_no_released
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode hfirst hinitialFollowers
  have hfields : ∀ l, (states l).status ≠ .unoccupied →
      (states l).lastDown = some (selected.view.payload.downRecord l) := by
    intro l hoccupied
    exact hcarried l selected hselected hoccupied
  have hnotReleased : ∀ l, (states l).status ≠ .released := by
    intro l
    exact (hnoReleased k selected hprepareSelected l (states l) (memories l)
      (by simpa only [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] using
        hprepared l)).2 ⟨i, hi⟩
  refine ⟨states, memories, ?_, hfields, hnotReleased⟩
  intro l
  exact hprepared l

/-- Every literal raw H request resolves to the same actual record and
selection. All ordinary prepared follower choices, the selected payload's
occupied DOWN fields, and the no-released condition are retained. -/
public theorem rawPending_actual_choice_frame (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) (hp : rawPending ell t i z) :
    ∃ (record : Record (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input)
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
      (choice : ReferencePrelaunchFollower.State p rate.eta)
      (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
      lookup t z = some record ∧ record.input.time = t ∧
      record.output.preparation.coordinator.selection = some selected ∧
      i ∈ selected.view.pendingAtChoice ∧
      (∀ j, (record.output.preparation.followers.followers j).configuration =
        .ordinary (states j) (memories j)) ∧
      (∀ j, (states j).status ≠ .unoccupied →
        (states j).lastDown = some (selected.view.payload.downRecord j)) ∧
      (∀ j, (states j).status ≠ .released) ∧
      (ReferenceFollowerFixedReply.actualChoice record i).configuration =
        .ordinary choice choiceMemory ∧
      preRoundStatus t i z = some (FollowerDownMeasurability.followerStatusCode choice.status) := by
  classical
  obtain ⟨record0, choice, choiceMemory, hlookup0, hchoice0, hcode0⟩ :=
    ReferenceOriginalFixedInstallationHandoverSupport.rawPending_actual_status
      rate rewards C_star C_h ell t i z hp
  rcases hp with ⟨birth, hb, hfirst, htBirth, hstart, j, hj, ht, selected0, hsel0, hi⟩ |
    ⟨b, hb, htBirth, hlookupBirth, payload, ledger, saved, hstate, hempty,
      installed, hinstalled, j, ht, selected0, hsel0, hi⟩
  · let W := ReferenceOriginalInitialTransferWindowGeometry.rawInitialTransferWindow
      rate rewards C_star C_h z
    let record := W[j.val]
    have hlookup : lookup t z = some record := by
      rw [← ht]
      exact (ReferenceOriginalInitialTransferWindowGeometry.raw_window_record_calendar
        rate rewards C_star C_h z j).2
    have htimeRecord : record.input.time = t := ht
    have hframe := initial_window_choice_frame rate rewards C_star C_h z j record rfl i selected0 hsel0 hi
    obtain ⟨states, memories, hprepared, hfields, hnotReleased⟩ := hframe
    have hsel : record.output.preparation.coordinator.selection = some selected0 := hsel0
    have hsameRecord : record0 = record := Option.some.inj (hlookup0.symm.trans hlookup)
    subst record0
    exact ⟨record, selected0, states, memories, choice, choiceMemory,
      hlookup, htimeRecord, hsel, hi, hprepared, hfields, hnotReleased, hchoice0, hcode0⟩
  · let H := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actualHandoverRecords
      rate rewards C_star C_h z b
    let record := H[j.val]
    have hlookup : lookup t z = some record := by
      rw [← ht]
      exact ReferenceOriginalFixedInstallationHandoverSupport.actualHandover_actualRecord
        rate rewards C_star C_h z b j
    have hlater := ReferenceOriginalFixedInstallationHandoverSupport.laterBirthAt_is_laterChosen
      rate rewards C_star C_h z b payload ledger saved hstate hempty
    obtain ⟨bornPayload, hborn, hframes⟩ :=
      ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_later_handover_snapshot
        (rate := rate) rewards C_star C_h z b hlater
    obtain ⟨selectedFrame, states, memories, hselectedFrame, hpayload,
      hprepared, _hsnapshot, hfields0, hnotReleased, _hunoccupied⟩ := hframes j
    have hselectedEq := Option.some.inj (hselectedFrame.symm.trans hsel0)
    subst selectedFrame
    have hfields : ∀ k, (states k).status ≠ .unoccupied →
        (states k).lastDown = some (selected0.view.payload.downRecord k) := by
      intro k hk
      rw [hpayload]
      exact hfields0 k hk
    have hsameRecord : record0 = record := Option.some.inj (hlookup0.symm.trans hlookup)
    subst record0
    exact ⟨record, selected0, states, memories, choice, choiceMemory,
      hlookup, ht, hsel0, hi, hprepared, hfields, hnotReleased, hchoice0, hcode0⟩

/-- A raw H request has exactly one of the actual unoccupied or pending
choice statuses. The released status is excluded by the actual source frame. -/
public theorem rawPending_status_before_or_after (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) (hp : rawPending ell t i z) :
    preRoundStatus t i z = some 0 ∨ preRoundStatus t i z = some 1 := by
  obtain ⟨record, selected, states, memories, choice, choiceMemory,
    _hlookup, _htime, _hsel, _hi, hprepared, _hfields, hnotReleased,
    hchoice, hstatus⟩ := rawPending_actual_choice_frame rate rewards C_star C_h ell t i z hp
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (by simpa only [ReferenceFollowerFixedReply.actualChoice] using hprepared i))
  have hchoiceNotReleased : choice.status ≠ .released := by
    intro hreleased
    apply hnotReleased i
    simpa only [hsame.1] using hreleased
  cases hchoiceStatus : choice.status with
  | unoccupied => simp [FollowerDownMeasurability.followerStatusCode, hstatus, hchoiceStatus]
  | pending =>
      simp [FollowerDownMeasurability.followerStatusCode, hstatus, hchoiceStatus]
  | released => exact False.elim (hchoiceNotReleased hchoiceStatus)

/-- The masked actual pending set is exactly the disjoint BEFORE/AFTER
partition, with its indicator sum represented by ordinary real indicators. -/
public theorem pending_iff_before_or_after (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) :
    maskedPending ell t i z ↔ before ell t i z ∨ after ell t i z := by
  constructor
  · intro hp
    obtain ⟨hbad, hraw⟩ := hp
    rcases rawPending_status_before_or_after rate rewards C_star C_h ell t i z hraw with hstatus | hstatus
    · exact Or.inl ⟨⟨hbad, hraw⟩, hstatus⟩
    · exact Or.inr ⟨⟨hbad, hraw⟩, hstatus⟩
  · rintro (⟨⟨hbad, hraw⟩, _⟩ | ⟨⟨hbad, hraw⟩, _⟩)
    · exact ⟨hbad, hraw⟩
    · exact ⟨hbad, hraw⟩

public theorem before_after_disjoint (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) : ¬ (before ell t i z ∧ after ell t i z) := by
  intro h
  have hstatus : (0 : Fin 3) = 1 := Option.some.inj (h.1.2.symm.trans h.2.2)
  have hne : (0 : Fin 3) ≠ 1 := by decide
  exact hne hstatus

public theorem pending_stage_indicator_sum (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) :
    (if maskedPending ell t i z then (1 : ℝ) else 0) =
      (if before ell t i z then 1 else 0) + (if after ell t i z then 1 else 0) := by
  by_cases hp : maskedPending ell t i z
  · have hstage := (pending_iff_before_or_after rate rewards C_star C_h ell t i z).mp hp
    rcases hstage with hb | ha
    · have hnot : ¬ after ell t i z := by
        intro ha
        exact before_after_disjoint rate rewards C_star C_h ell t i z ⟨hb, ha⟩
      simp [hp, hb, hnot]
    · have hnot : ¬ before ell t i z := by
        intro hb
        exact before_after_disjoint rate rewards C_star C_h ell t i z ⟨hb, ha⟩
      simp [hp, ha, hnot]
  · have hb : ¬ before ell t i z := fun h => hp h.1
    have ha : ¬ after ell t i z := fun h => hp h.1
    simp [hp, hb, ha]

/-- On every original installation's BEFORE branch, positive physical follower
feedback is exactly the selected one-bit DOWN service event. -/
public theorem before_physical_service (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) (hz : before ell t i z) :
    ∃ (record : Record (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input),
      lookup t z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      (V_before rate rewards C_star C_h i t z ↔
        PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
        CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = 1 ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) := by
  obtain ⟨record, selected, states, memories, choice, choiceMemory,
    hr, htime, hs, hi, hc, hf, hn, hchoice, hcode⟩ :=
    rawPending_actual_choice_frame rate rewards C_star C_h ell t i z hz.1.2
  obtain ⟨_, _, htimeFields, hreward⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t z record hr
  have hstatusCode := Option.some.inj (hcode.symm.trans hz.2)
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (by simpa only [ReferenceFollowerFixedReply.actualChoice] using hc i))
  have hu : (states i).status = .unoccupied := by
    cases hstatus : (states i).status <;>
      simp [FollowerDownMeasurability.followerStatusCode, hsame.1, hstatus] at hstatusCode ⊢
  refine ⟨record, selected, hr, hs, ?_⟩
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hfeedback (hdown : PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 =
      PublicDiscreteDraws.downSlot)
      (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 t).1 = i) :
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val =
      if CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = 1 then
        ((rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val : ℝ) / (D p : ℝ)
      else 0 := by
    let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
    let input := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
      selected.view.payload record.input.row record.input.time
    have ha := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_handover_down_actions
      record.input selected (by rw [← hprep]; exact hs) states memories
      (by intro j; rw [← hprep]; exact hc j) hf hn i hi
      (by rw [htime]; exact hdown) (by rw [htime]; exact hdraw)
    have ha' : record.output.preparation.arms.actions =
        ActiveRoundActions.actions p.two_le_m snapshot input := by
      rw [hprep]
      exact ha
    have hinv : ActiveRoundActions.no_released_while_missing snapshot := by
      intro _ j
      exact hn j
    have hselected : input.selected = i := by
      dsimp [input, ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput]
      rw [htime]
      exact hdraw
    have hbit : input.down.bit = CoordinatorLocalArmChoice.currentDownHash
        selected.view.payload (record.input.row.2 t) i := by
      rw [ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput_down_bit]
      rw [htime, hdraw]
    calc
      _ = ActiveRoundActions.feedback p.two_le_m snapshot input
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow record)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
        calc
          _ = FiniteBanditModel.playerFeedback record.output.preparation.arms.actions
              (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ))
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
            record.output.preparation.feedback.feedback_scalar_eq_playerFeedback _
          _ = _ := by rw [ha']; rfl
      _ = _ := by
        have h := ActiveRoundActions.unoccupied_down_feedback p.two_le_m snapshot input
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow record)
          (by dsimp [input, ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput];
              rw [htime]; exact hdown)
          (by rw [hselected]; exact hi) hinv (by rw [hselected]; exact hu)
        rw [hselected] at h
        rw [h, hbit]
        dsimp [ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow,
          ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRowAt,
          RealRewardGridCount.realRewardGridValue, input,
          ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput,
          PublicDiscreteDraws.followerCount]
        rw [hreward, htime]
  have hpositive (a : Fin p.K) :
      0 < ((rewards t a).val : ℝ) / (D p : ℝ) ↔ 0 < (rewards t a).val := by
    have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast Iff.rfl
  constructor
  · rintro ⟨other, hother, hdown, hdraw, hpos⟩
    have heq := Option.some.inj (hother.symm.trans hr)
    subst other
    rw [htime] at hdown hdraw
    refine ⟨hdown, hdraw, ?_⟩
    rw [hfeedback hdown hdraw] at hpos
    split_ifs at hpos with hbit
    · exact ⟨hbit, (hpositive _).mp hpos⟩
    · exact False.elim (lt_irrefl 0 hpos)
  · rintro ⟨hdown, hdraw, hbit, hpos⟩
    refine ⟨record, hr, ?_, ?_, ?_⟩
    · rw [htime]
      exact hdown
    · rw [htime]
      exact hdraw
    · rw [hfeedback hdown hdraw, ite_eq_left hbit]
      exact (hpositive _).mpr hpos

/-- On every original installation's AFTER branch, positive physical
coordinator confirmation is exactly zero-bit DOWN service at its receiver. -/
public theorem after_physical_service (ell t : Fin p.T) (i : Fin (p.m - 1))
    (z : Source) (hz : after ell t i z) :
    ∃ (record : Record (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection record.input),
      lookup t z = some record ∧
      record.output.preparation.coordinator.selection = some selected ∧
      (V_after rate rewards C_star C_h i t z ↔
        PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
        CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (record.input.row.2 t) i = 0 ∧
        0 < (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val) := by
  obtain ⟨record, selected, states, memories, choice, choiceMemory,
    hr, htime, hs, hi, hc, hf, hn, hchoice, hcode⟩ :=
    rawPending_actual_choice_frame rate rewards C_star C_h ell t i z hz.1.2
  obtain ⟨_, _, htimeFields, hreward⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t z record hr
  have hstatusCode := Option.some.inj (hcode.symm.trans hz.2)
  have hsame := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (by simpa only [ReferenceFollowerFixedReply.actualChoice] using hc i))
  have hpending : (states i).status = .pending := by
    cases hstatus : (states i).status <;>
      simp [FollowerDownMeasurability.followerStatusCode, hsame.1, hstatus] at hstatusCode ⊢
  refine ⟨record, selected, hr, hs, ?_⟩
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hfeedback (hdown : PublicDiscreteDraws.slotDraw (record.input.row.2 t).1 =
      PublicDiscreteDraws.downSlot)
      (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 t).1 = i)
      (hzero : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
        (record.input.row.2 t) i = 0) :
      (record.output.preparation.feedback.observations
        (ActiveRoundActions.coordinator p.two_le_m)).val.val =
        ((rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (record.input.row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))).val : ℝ) / (D p : ℝ) := by
    let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
    let input := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput
      selected.view.payload record.input.row record.input.time
    have ha := ReferencePostReplacementCollectionHandoverDecoderCorrespondence.actual_handover_down_actions
      record.input selected (by rw [← hprep]; exact hs) states memories
      (by intro j; rw [← hprep]; exact hc j) hf hn i hi
      (by rw [htime]; exact hdown) (by rw [htime]; exact hdraw)
    have ha' : record.output.preparation.arms.actions =
        ActiveRoundActions.actions p.two_le_m snapshot input := by
      rw [hprep]
      exact ha
    have hinv : ActiveRoundActions.no_released_while_missing snapshot := by
      intro _ j
      exact hn j
    have hselected : input.selected = i := by
      dsimp [input, ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput]
      rw [htime]
      exact hdraw
    have hbit : input.down.bit = 0 := by
      rw [ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput_down_bit,
        htime, hdraw]
      exact hzero
    calc
      _ = ActiveRoundActions.feedback p.two_le_m snapshot input
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow record)
          (ActiveRoundActions.coordinator p.two_le_m) := by
        calc
          _ = FiniteBanditModel.playerFeedback record.output.preparation.arms.actions
              (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ))
              (ActiveRoundActions.coordinator p.two_le_m) :=
            record.output.preparation.feedback.feedback_scalar_eq_playerFeedback _
          _ = _ := by rw [ha']; rfl
      _ = _ := by
        rw [ActiveRoundActions.pending_down_coordinator_feedback p.two_le_m snapshot input
          (ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow record)
          (by dsimp [input, ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput];
              rw [htime]; exact hdown)
          (by rw [hselected]; exact hi) hinv
          (by rw [hselected]; exact hpending) hbit, hselected]
        dsimp [ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRow,
          ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverWholeRewardRowAt,
          RealRewardGridCount.realRewardGridValue, input,
          ReferencePostReplacementCollectionHandoverDecoderCorrespondence.handoverRoundInput,
          PublicDiscreteDraws.followerCount]
        rw [hreward, htime]
  have hpositive (a : Fin p.K) :
      0 < ((rewards t a).val : ℝ) / (D p : ℝ) ↔ 0 < (rewards t a).val := by
    have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
    rw [div_pos_iff_of_pos_right hD]
    exact_mod_cast Iff.rfl
  constructor
  · rintro ⟨other, otherSelection, hother, hotherSelection, hdown, hdraw, hzero, hpos⟩
    have heq := Option.some.inj (hother.symm.trans hr)
    subst other
    have hselEq := Option.some.inj (hotherSelection.symm.trans hs)
    subst otherSelection
    rw [htime] at hdown hdraw hzero
    rw [hfeedback hdown hdraw hzero] at hpos
    exact ⟨hdown, hdraw, hzero, (hpositive _).mp hpos⟩
  · rintro ⟨hdown, hdraw, hzero, hpos⟩
    refine ⟨record, selected, hr, hs, ?_, ?_, ?_, ?_⟩
    · rw [htime]
      exact hdown
    · rw [htime]
      exact hdraw
    · rw [htime]
      exact hzero
    · rw [hfeedback hdown hdraw hzero]
      exact (hpositive _).mpr hpos

end Bandits.Support.ReferenceOriginalInstallationHandoverChoiceFrame

end
