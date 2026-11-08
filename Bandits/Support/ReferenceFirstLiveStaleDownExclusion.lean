/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLivePendingErasureHistory

import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# First-live retained-assignment stale DOWN diagnostic exclusion

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108`,
`sources/zip4/manuscript/05_binary_transport.tex:74-88`, and
`sources/zip4/manuscript/06_interruptions.tex:246-295`.

For an actual selected first-live assignment and a follower already absent
from its pending set, this module bounds that exact assignment record by any
later-or-same ordinary choice of the same follower in the original physical
run. It then excludes acceptance of that stale exact record as an actual
DOWN diagnostic at the later choice, including when a later release or finish
fails. This is one retained-FIRST-assignment component of AppA:102. It proves
no candidate/origin alignment, assignment-lineage theorem, other false-
acceptance case, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceFollowerFixedReply
open ReferenceFollowerReplyChronology
open ReferenceFirstLiveConfirmationHistory
open ReferenceFirstLivePendingErasureHistory
open ReferencePrelaunchFollower

namespace Bandits.Support.ReferenceFirstLiveStaleDownExclusion

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_actual_output_before_choice
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (n t : Fin records.length) (hnt : n.val < t.val)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice records[t.val] i).configuration =
      .ordinary s memory) :
    ∃ next nextMemory,
      records[n.val].output.next.followers i = .ordinary next nextMemory ∧
      ReferencePrelaunchFollower.acceptedStart next ≤
        ReferencePrelaunchFollower.acceptedStart s := by
  obtain ⟨before, beforeMemory, hbefore, hreply, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice records[t.val] i s memory hchoice
  have hstart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input
    chain t.val t.isLt
  have htakeLength : (records.take t.val).length = t.val := by
    simp only [List.length_take, min_eq_left_of_lt t.isLt]
  have hnTake : n.val < (records.take t.val).length := by
    rw [htakeLength]
    exact hnt
  obtain ⟨next, nextMemory, hout, hbound⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i before
      beforeMemory hbefore n.val hnTake
  have hget := List.getElem_take (xs := records) (j := t.val) (i := n.val) (h := hnTake)
  rw [hget] at hout
  refine ⟨next, nextMemory, hout, ?_⟩
  calc
    ReferencePrelaunchFollower.acceptedStart next ≤
        ReferencePrelaunchFollower.acceptedStart before := hbound
    _ = ReferencePrelaunchFollower.acceptedStart s := hstart.symm

private theorem connected_actual_choice_backward
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (chain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (n t : Fin records.length) (hnt : n.val ≤ t.val)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice records[t.val] i).configuration =
      .ordinary s memory) :
    ∃ earlier earlierMemory,
      (ReferenceFollowerFixedReply.actualChoice records[n.val] i).configuration =
        .ordinary earlier earlierMemory ∧
      ReferencePrelaunchFollower.acceptedStart earlier ≤
        ReferencePrelaunchFollower.acceptedStart s := by
  by_cases hEq : n.val = t.val
  · have hfin : n = t := Fin.ext hEq
    subst n
    exact ⟨s, memory, hchoice, Nat.le_refl _⟩
  · have hlt : n.val < t.val := by omega
    obtain ⟨next, nextMemory, hout, hnextBound⟩ :=
      connected_actual_output_before_choice chain i n t hlt s memory hchoice
    obtain ⟨earlier, earlierMemory, hEarlierChoice, hChoiceBound, _, _⟩ :=
      ReferenceFollowerReplyChronology.record_choice_chronology records[n.val] i next
        nextMemory hout
    exact ⟨earlier, earlierMemory, hEarlierChoice, hChoiceBound.trans hnextBound⟩

private theorem finishFollower_ordinary_diagnostic_frame
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).downInput ∧
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
        (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  classical
  cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation state).result with
  | error reason =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord]
      exact ⟨trivial, trivial⟩
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time observation state memory post with
      | error reason =>
          simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]
          exact ⟨trivial, trivial⟩
      | ok result =>
          simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration, hrecord, hfinish]
          exact ⟨trivial, trivial⟩

private theorem acceptedDown_actual_unoccupied_choice
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (haccepted : ReferenceFirstLiveConfirmationHistory.AcceptedDown record i M) :
    ∃ state memory,
      (ReferenceFollowerFixedReply.actualChoice record i).configuration = .ordinary state memory ∧
      state.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart state < M.val.sigma := by
  rcases haccepted with
    ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hdown, houtcome⟩
  have hinputStep := hinput
  have hdownStep := hdown
  rw [record.output_eq] at hinputStep hdownStep
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let localPrepared := prepared.followers.followers i
  have hdiagInput :
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
        localPrepared observation).downInput = some logged := by
    change ((ReferenceActivePhysicalStep.prepare record.input).observeFollower i).downInput =
      some logged at hinputStep
    simpa only [ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, localPrepared, observation] using hinputStep
  have hdiagDown :
      (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
        localPrepared observation).down = some cut := by
    change ((ReferenceActivePhysicalStep.prepare record.input).observeFollower i).down =
      some cut at hdownStep
    simpa only [ReferenceActivePhysicalStep.PreparedRound.observeFollower,
      prepared, localPrepared, observation] using hdownStep
  cases hconfiguration : localPrepared.configuration with
  | dagger =>
      simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration] at hdiagInput
      cases hdiagInput
  | ordinary state memory =>
      have hchoice :
          (ReferenceFollowerFixedReply.actualChoice record i).configuration =
            .ordinary state memory := by
        change (record.output.preparation.followers.followers i).configuration = _
        rw [record.output_eq]
        change ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration = _
        exact hconfiguration
      have hdiagnosticFrame := finishFollower_ordinary_diagnostic_frame
        prepared.coordinator.downView localPrepared observation state memory hconfiguration
      have hrecordInput :
          (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
            localPrepared.follower localPrepared.row localPrepared.activation localPrepared.time
            localPrepared.active localPrepared.arm observation state).downInput = some logged :=
        hdiagnosticFrame.1.symm.trans hdiagInput
      have hrecordDown :
          (ReferenceActivePhysicalStep.recordFollower prepared.coordinator.downView
            localPrepared.follower localPrepared.row localPrepared.activation localPrepared.time
            localPrepared.active localPrepared.arm observation state).down = some cut :=
        hdiagnosticFrame.2.symm.trans hdiagDown
      by_cases hunoccupied : state.status = .unoccupied
      · cases hlogging : ActiveFollowerLogging.checkedLogging localPrepared.follower localPrepared.row
            localPrepared.activation localPrepared.time (localPrepared.arm, observation) state with
        | error reason =>
            simp only [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging] at hrecordInput
            cases hrecordInput
        | ok logged' =>
            have hlogged : logged' = logged := by
              simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging]
                using hrecordInput
            subst logged'
            have hcutEq :
                ReferenceDownReception.referenceDownCut p prepared.coordinator.downView localPrepared.follower
                  localPrepared.row localPrepared.time observation rate logged = cut := by
              apply Option.some.inj
              simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hlogging]
                using hrecordDown
            have houtcome' :
                (ReferenceDownReception.referenceDownCut p prepared.coordinator.downView localPrepared.follower
                  localPrepared.row localPrepared.time observation rate logged).outcome =
                  ActiveFollowerDownAcceptance.LocalDownResult.accepted
                    logged after raw M scan registers lastService := by
              simpa only [hcutEq] using houtcome
            have haccept := ReferenceFollowerReplyChronology.referenceDownCut_accepted
              prepared.coordinator.downView localPrepared.follower localPrepared.row localPrepared.time observation
              logged after raw M scan registers lastService houtcome'
            have hloggingFrame := ActiveFollowerLogging.checkedLogging_success_frame
              localPrepared.follower localPrepared.row localPrepared.activation localPrepared.time
              (localPrepared.arm, observation) state logged hlogging
            have hstart : ReferencePrelaunchFollower.acceptedStart logged =
                ReferencePrelaunchFollower.acceptedStart state := by
              simp only [ReferencePrelaunchFollower.acceptedStart, hloggingFrame.1]
            rw [hstart] at haccept
            exact ⟨state, memory, hchoice, hunoccupied, haccept.1.1⟩
      · simp only [ReferenceActivePhysicalStep.recordFollower, hunoccupied] at hrecordInput
        cases hrecordInput

/-- The exact record selected by an absent-pending first-live assignment is
no newer than any later-or-same actual ordinary choice of that follower in
the original physical run. The intervening accepted diagnostic and its
ordinary output are derived from the run. -/
theorem run_firstLive_missing_pending_stale_down_start_bound
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (a : Fin W.length) (v : ReferenceFirstLivePendingErasureHistory.Selection W[a.val].input),
      (ReferenceActivePhysicalStep.prepare W[a.val].input).coordinator.selection = some v →
      ∀ (i : Fin (p.m - 1)), i ∉ v.view.pendingAtChoice →
      ∀ (t : Fin R.records.length), a.val ≤ t.val →
      ∀ (s : ReferencePrelaunchFollower.State p rate.eta)
        (memory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceFollowerFixedReply.actualChoice R.records[t.val] i).configuration =
          .ordinary s memory →
        (v.view.payload.downRecord i).val.sigma ≤
          ReferencePrelaunchFollower.acceptedStart s := by
  intro R W a v hselected i hi t hat s memory hchoice
  have hwindowPrefix : W.IsPrefix R.records := List.takeWhile_prefix _
  let aR : Fin R.records.length :=
    ⟨a.val, Nat.lt_of_lt_of_le a.isLt hwindowPrefix.length_le⟩
  have hwindowGetA : W[a.val] = R.records[a.val] := hwindowPrefix.getElem a.isLt
  obtain ⟨stateA, memoryA, hchoiceA, _⟩ :=
    connected_actual_choice_backward R.connected i aR t hat s memory hchoice
  have hchoiceAWindow :
      (ReferenceFollowerFixedReply.actualChoice W[a.val] i).configuration =
        .ordinary stateA memoryA := by
    simpa only [hwindowGetA] using hchoiceA
  have hchoiceAPrepared :
      ((ReferenceActivePhysicalStep.prepare W[a.val].input).followers.followers i).configuration =
        .ordinary stateA memoryA := by
    have h := hchoiceAWindow
    change (W[a.val].output.preparation.followers.followers i).configuration = _ at h
    rw [W[a.val].output_eq] at h
    simpa only [ReferenceActivePhysicalStep.step] using h
  obtain ⟨b, hb, w, hselectedB, hdrawB, heventB, hpayloadB, rB, qB, baseB,
      hliveB, hpendingB, j, hj, haccepted⟩ :=
    ReferenceFirstLivePendingErasureHistory.run_firstLive_missing_pending_prior_down
      initial rows J rewards start count hspan hmode hfirst hseed a v hselected i
      stateA memoryA hchoiceAPrepared hi
  have hwindowGetJ : W[j.val] = R.records[j.val] := hwindowPrefix.getElem j.isLt
  have hacceptedR :
      ReferenceFirstLiveConfirmationHistory.AcceptedDown R.records[j.val] i
        (v.view.payload.downRecord i) := by
    change ReferenceFirstLiveConfirmationHistory.AcceptedDown W[j.val] i
      (v.view.payload.downRecord i) at haccepted
    rw [hwindowGetJ] at haccepted
    exact haccepted
  have hjt : j.val < t.val := by omega
  let jR : Fin R.records.length :=
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt hwindowPrefix.length_le⟩
  obtain ⟨next, nextMemory, houtputJ, hnextBound⟩ :=
    connected_actual_output_before_choice R.connected i jR t hjt s memory hchoice
  have hApplied : ReferenceFollowerReplyChronology.appliedDown R.records[jR.val] i
      (v.view.payload.downRecord i).val.sigma := by
    rcases hacceptedR with
      ⟨logged, cut, after, raw, scan, registers, lastService, hinput, hcut, houtcome⟩
    exact ⟨logged, cut, after, raw, v.view.payload.downRecord i, scan, registers,
      lastService, hinput, hcut, houtcome, rfl⟩
  obtain ⟨choiceJ, memoryJ, hchoiceJ, hstrictJ, hinstalledJ⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict R.records[jR.val] i
      (v.view.payload.downRecord i).val.sigma hApplied next nextMemory houtputJ
  calc
    (v.view.payload.downRecord i).val.sigma =
        ReferencePrelaunchFollower.acceptedStart next := hinstalledJ.symm
    _ ≤ ReferencePrelaunchFollower.acceptedStart s := hnextBound

/-- The actual accepted-DOWN diagnostic cannot accept the stale exact record
at any later-or-same actual record, even if the follower's subsequent
release, finish, or terminal path fails. The current unoccupied ordinary
choice, successful logging frame, and strict local acceptance test are
inverted from that retained diagnostic. -/
theorem run_firstLive_missing_pending_stale_down_diagnostic_excluded
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
    ∀ (a : Fin W.length) (v : ReferenceFirstLivePendingErasureHistory.Selection W[a.val].input),
      (ReferenceActivePhysicalStep.prepare W[a.val].input).coordinator.selection = some v →
      ∀ (i : Fin (p.m - 1)), i ∉ v.view.pendingAtChoice →
      ∀ (t : Fin R.records.length), a.val ≤ t.val →
        ¬ ReferenceFirstLiveConfirmationHistory.AcceptedDown R.records[t.val] i
          (v.view.payload.downRecord i) := by
  intro R W a v hselected i hi t hat haccepted
  obtain ⟨state, memory, hchoice, hunoccupied, hstrict⟩ :=
    acceptedDown_actual_unoccupied_choice R.records[t.val] i
      (v.view.payload.downRecord i) haccepted
  have hbound := run_firstLive_missing_pending_stale_down_start_bound
    initial rows J rewards start count hspan hmode hfirst hseed a v hselected i hi t hat
    state memory hchoice
  exact Nat.not_lt_of_ge hbound hstrict

end Bandits.Support.ReferenceFirstLiveStaleDownExclusion

end
