/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedAssignmentLiveErasureHistory

import Lean.Elab.Tactic.Omega

/-!
# The generated assignment's actual live segment

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`,
`sources/zip4/manuscript/05_binary_transport.tex:60-88,94-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,246-295,303-348`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The endpoint is an actual continuing LIVE dispatcher and an ordinary focal
CHOICE. The birth initializer is supplied by the admitted generated-history
module. Backward inversion of actual physical steps produces the live segment:
a collection tail cannot return LIVE, a failed tail has no stored payload, and
a new installation cannot restore a payload with an earlier birth timestamp.
The endpoint's post-choice tail is allowed to fail. This is an internal branch
result, not pending-erasure history or manuscript closure.
-/

@[expose] public section

noncomputable section

open scoped Classical
open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceGeneratedAssignmentLiveSegment

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record := RoundRecord (p := p) (rate := rate)

private theorem selectionAt_fields
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (hselected : selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload ∧ selected.started = started ∧
      selected.view.pendingAtChoice = started.pending := by
  unfold selectionAt at hselected
  split at hselected
  · cases hselected
    exact ⟨rfl, rfl, rfl⟩
  · cases hselected

/-- Invert the actual dispatch, including invalid collection clocks. -/
private theorem prepared_input_origin (x : RoundInput p rate) :
    match (prepare x).coordinator with
    | .first _ => x.state.coordinator = .first
    | .live r q base _ => x.state.coordinator = .live r q base
    | _ => True := by
  change match dispatch x with
    | .first _ => x.state.coordinator = .first
    | .live r q base _ => x.state.coordinator = .live r q base
    | _ => True
  cases hstate : x.state.coordinator with
  | first => rw [dispatch_first x hstate]
  | live r q base =>
      have hd : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        simp only [dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hd]
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock payload ledger proposal cutoff
        cases hr : CoordinatorRoundDispatch.dispatch
            (.collection (collectionInput x payload ledger clock cutoff)) with
        | collection outcome =>
            have hd : dispatch x = .collection payload ledger clock cutoff outcome := by
              simp only [dispatch, hstate, dite_eq_left hvalid, cutoff, clock]
              rw [hr]
              rfl
            rw [hd]
            trivial
      · have hd : dispatch x = .invalidCollectionCutoff := by
          simp only [dispatch, hstate, dite_eq_right hvalid]
        rw [hd]
        trivial
  | dagger => rw [dispatch_dagger x hstate]; trivial

private theorem record_prepared_eq (record : Record (p := p) (rate := rate)) :
    record.output.preparation = prepare record.input := by
  rw [record.output_eq]
  rfl

private theorem record_next_eq (record : Record (p := p) (rate := rate)) :
    record.output.next.coordinator =
      record.output.preparation.observeCoordinator.configuration := by
  rw [record.output_eq]
  rfl

private theorem collectionPhase_not_live
    (configuration : CoordinatorConfiguration p rate)
    (hphase : ReferenceCollectionPhaseHistory.CollectionPhase configuration)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) : configuration ≠ .live r q base := by
  rcases hphase with he | ⟨payload, ledger, proposal, he⟩
  · rw [he]
    intro h
    cases h
  · rw [he]
    intro h
    cases h

private theorem live_tail_payload
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (htail : (livePostChoice prepared r q base started).configuration =
      .live next nextOwned nextBase) : next.payload = r.payload := by
  have hframe := ReferenceAssignmentPayloadPersistence.livePostChoice_payload_frame
    prepared r q base started
  rw [htail] at hframe
  rcases hframe with hnone | hsome
  · cases hnone
  · exact Option.some.inj hsome

/-- A real LIVE successor is produced only by an installation or by the
continuing LIVE constructor. Selection and the entire payload are recovered
from that same executed step. No success of a later step is assumed here. -/
private theorem record_live_output_origin
    (record : Record (p := p) (rate := rate))
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : record.output.next.coordinator = .live next nextOwned nextBase) :
    ∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = next.payload ∧
      (InstallationBirth record next.payload ∨
        ∃ r q base, ∃ (outcome : CoordinatorRoundDispatch.LiveOutcome
          (liveInput record.input r q base)),
          record.input.state.coordinator = .live r q base ∧
          record.output.preparation.coordinator = .live r q base outcome ∧
          (∃ dispatched hstart continuation arm,
        outcome = .continuingChosen dispatched hstart continuation arm) ∧
          r.payload = next.payload) := by
  classical
  have hnotNone : record.output.preparation.coordinator.selection ≠ none := by
    intro hnone
    have h := ReferenceAssignmentPayloadChronology.actualRecord_next_storedPayload_none_of_no_selection record hnone
    rw [hnext] at h
    cases h
  obtain ⟨selected, hselected⟩ := Option.ne_none_iff_exists'.mp hnotNone
  have hobs := (record_next_eq record).symm.trans hnext
  have horigin := prepared_input_origin record.input
  rw [← record_prepared_eq record] at horigin
  cases hcut : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome with
      | chosen installed arm =>
          have hfields := selectionAt_fields record.input installed.registers.payload
            installed.startRoundResult installed.registers.time
            installed.registers.complementWeights arm selected
            (by simpa only [hcut, DispatchCut.selection] using hselected)
          rw [observeCoordinator_first_equation record.output.preparation _ hcut] at hobs
          have hnonempty : (DispatchCut.first (.chosen installed arm)).selection ≠ none := by
            simpa only [hcut] using hnotNone
          simp only [ite_eq_right hnonempty] at hobs
          have hframe := live_tail_payload record.output.preparation _ _ _ _
            next nextOwned nextBase hobs
          have hlocal := ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
            record selected hselected
          have hfirst : record.input.state.coordinator = .first := by
            simpa only [hcut] using horigin
          rcases hlocal with hstored | hbirth
          · rw [hfirst] at hstored
            cases hstored
          · refine ⟨selected, (by rw [← hcut]; exact hselected), hfields.1.trans hframe.symm, Or.inl ?_⟩
            simpa only [hfields.1.trans hframe.symm] using hbirth
      | choiceDomainFailure _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | recorderBoundaryFailure _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | choiceRejected _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
  | live r q base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          have hfields := selectionAt_fields record.input r.payload dispatched.startResult
            record.input.time (liveRegistersAt r record.input.time).complementWeights
            arm selected (by simpa only [hcut, DispatchCut.selection] using hselected)
          rw [observeCoordinator_live_equation record.output.preparation _ _ _ _ hcut] at hobs
          have hnonempty : (DispatchCut.live r q base
              (.continuingChosen dispatched hstart continuation arm)).selection ≠ none := by
            simpa only [hcut] using hnotNone
          simp only [ite_eq_right hnonempty] at hobs
          have hframe := live_tail_payload record.output.preparation _ _ _ _
            next nextOwned nextBase hobs
          have hin : record.input.state.coordinator = .live r q base := by
            simpa only [hcut] using horigin
          exact ⟨selected, (by rw [← hcut]; exact hselected), hfields.1.trans hframe.symm,
            Or.inr ⟨r, q, base, .continuingChosen dispatched hstart continuation arm,
              hin, rfl, ⟨dispatched, hstart, continuation, arm, rfl⟩, hframe.symm⟩⟩
      | cutoffChosen dispatched _ ledger _ _ _ _ _ _ _ =>
          rw [observeCoordinator_live_equation record.output.preparation _ _ _ _ hcut] at hobs
          have hnonempty : record.output.preparation.coordinator.selection ≠ none := hnotNone
          rw [hcut] at hnonempty
          simp only [ite_eq_right hnonempty] at hobs
          exact (collectionPhase_not_live _
            (ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
              record.output.preparation _ _ _ _) next nextOwned nextBase hobs).elim
      | clockFailure _ _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | initializerFailure _ _ _ _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | localFailure _ _ _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          rw [observeCoordinator_collection_equation record.output.preparation _ _ _ _ _ hcut] at hobs
          have hnonempty := hnotNone
          rw [hcut] at hnonempty
          simp only [ite_eq_right hnonempty] at hobs
          exact (collectionPhase_not_live _
            (ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
              record.output.preparation _ _ _ _) next nextOwned nextBase hobs).elim
      | laterChosen core consistent started hstart instruction hinstruction output hlocal
          clockData installed arm =>
          have hfields := selectionAt_fields record.input installed.registers.payload
            started instruction.time installed.registers.complementWeights arm selected
            (by simpa only [hcut, DispatchCut.selection] using hselected)
          rw [observeCoordinator_collection_equation record.output.preparation _ _ _ _ _ hcut] at hobs
          have hnonempty := hnotNone
          rw [hcut] at hnonempty
          simp only [ite_eq_right hnonempty] at hobs
          have hframe := live_tail_payload record.output.preparation _ _ _ _
            next nextOwned nextBase hobs
          have hbirth := ReferenceLaterInstallationProvenance.record_laterChosen_birth record
          rw [hcut] at hbirth
          refine ⟨selected, (by rw [← hcut]; exact hselected), hfields.1.trans hframe.symm, Or.inl ?_⟩
          simpa only [hframe] using hbirth
      | clockFailure _ _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | localFailure _ _ _ _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | coreFailure _ _ _ _ => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | laterReconstructionFailure _ _ _ _ _ _ _ _ =>
          simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | laterPrefixFailure _ _ _ _ _ _ _ _ _ =>
          simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | laterOrientationFailure _ _ _ _ _ _ _ _ =>
          simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
      | laterChoiceFailure _ _ _ _ _ _ _ _ _ _ _ =>
          simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
  | invalidCollectionCutoff => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected
  | dagger => simp only [hcut, DispatchCut.selection, reduceCtorEq] at hselected

private theorem record_live_predecessor
    (record : Record (p := p) (rate := rate))
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (nextOwned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (nextBase : Fin (p.m - 1) → ℕ)
    (hnext : record.output.next.coordinator = .live next nextOwned nextBase)
    (hdate : next.payload.sigma.val < record.input.time.val) :
    ∃ r q base, ∃ (outcome : CoordinatorRoundDispatch.LiveOutcome
      (liveInput record.input r q base)),
      record.input.state.coordinator = .live r q base ∧
      record.output.preparation.coordinator = .live r q base outcome ∧
      (∃ dispatched hstart continuation arm,
        outcome = .continuingChosen dispatched hstart continuation arm) ∧
      r.payload = next.payload ∧
      ∃ selected : Selection record.input,
        record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = next.payload := by
  obtain ⟨selected, hselected, hpayload, hbirth | hcontinue⟩ :=
    record_live_output_origin record next nextOwned nextBase hnext
  · have htime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
      record next.payload hbirth
    omega
  · rcases hcontinue with ⟨r, q, base, outcome, hin, hcut, hcont, hframe⟩
    exact ⟨r, q, base, outcome, hin, hcut, hcont, hframe,
      selected, hselected, hpayload⟩

/-- The pending initializer uses the real accepted clock call in both birth
constructors. In particular it does not reset any later follower reply. -/
private theorem birth_selection_pending
    (record : Record (p := p) (rate := rate)) (payload : Payload rate)
    (hbirth : InstallationBirth record payload)
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected) :
    selected.view.payload = payload ∧
      selected.view.pendingAtChoice = Finset.univ ∧ selected.started.pending = Finset.univ := by
  cases hcut : record.output.preparation.coordinator with
  | first outcome =>
      cases outcome <;> try simp only [InstallationBirth, hcut] at hbirth
      rename_i installed arm
      have hfields := selectionAt_fields record.input installed.registers.payload
        installed.startRoundResult installed.registers.time
        installed.registers.complementWeights arm selected
        (by simpa only [hcut, DispatchCut.selection] using hselected)
      have heq := Except.ok.inj (installed.startRound_eq.symm.trans
        (CoordinatorAssignmentRegisterInstall.first_start_round_success _))
      have hpending : installed.startRoundResult.pending = Finset.univ := by
        rw [heq]
        rfl
      refine ⟨hfields.1.trans hbirth.1.symm, hfields.2.2.trans hpending, ?_⟩
      rw [hfields.2.1, hpending]
  | live _ _ _ outcome => cases outcome <;> simp only [InstallationBirth, hcut] at hbirth
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> try simp only [InstallationBirth, hcut] at hbirth
      rename_i core consistent started hstart instruction hinstruction output hlocal
        clockData installed arm
      have hfields := selectionAt_fields record.input installed.registers.payload
        started instruction.time installed.registers.complementWeights arm selected
        (by simpa only [hcut, DispatchCut.selection] using hselected)
      obtain ⟨_, _, _, _, _, _, hpending, _⟩ :=
        CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val record.input.time
          clock ledger.pending started instruction core.clock_parameter_valid
          core.clock_registers_valid core.clock_start_time_valid hstart hinstruction
      refine ⟨hfields.1.trans hbirth.1.symm, hfields.2.2.trans hpending, ?_⟩
      rw [hfields.2.1, hpending]
  | invalidCollectionCutoff => simp only [InstallationBirth, hcut] at hbirth
  | dagger => simp only [InstallationBirth, hcut] at hbirth

private theorem generated_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (k : Fin (p.T - s)) :
    (generatedSourceRecordAt rate rewards C_star C_h s hs x k).input.time.val = s + k.val := rfl

private theorem generated_run_length
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) :
    (generatedSourceRun rate rewards C_star C_h s hs x).records.length = p.T - s := by
  exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _

private theorem generated_record_get
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs) (k : Fin (p.T - s)) :
    (generatedSourceRun rate rewards C_star C_h s hs x).records[k.val]'(by
      rw [generated_run_length]; exact k.isLt) =
      generatedSourceRecordAt rate rewards C_star C_h s hs x k := by
  have hget := generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x k
  rw [List.getElem?_eq_getElem (by rw [generated_run_length]; exact k.isLt)] at hget
  exact Option.some.inj hget

/-- Consecutive indices are linked by the canonical run, not a supplied trace. -/
private theorem generated_adjacent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (k j : Fin (p.T - s)) (hkj : j.val = k.val + 1) :
    (generatedSourceRecordAt rate rewards C_star C_h s hs x k).output.next =
      (generatedSourceRecordAt rate rewards C_star C_h s hs x j).input.state := by
  let total := generatedSourceRun rate rewards C_star C_h s hs x
  have hcount : total.records.length = p.T - s := generated_run_length rate rewards C_star C_h s hs x
  have hk : k.val < total.records.length := by rw [hcount]; exact k.isLt
  have hj : j.val < total.records.length := by rw [hcount]; exact j.isLt
  have hchain := ReferenceFollowerReplyChronology.connected_drop_from_output total.connected k.val hk
  rw [← hkj, List.drop_eq_getElem_cons hj] at hchain
  have hstate := hchain.1
  rw [generated_record_get rate rewards C_star C_h s hs x k,
    generated_record_get rate rewards C_star C_h s hs x j] at hstate
  exact hstate.symm

private theorem generated_connected_segment
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (b n : Fin (p.T - s)) (hbn : b.val < n.val) :
    Connected (generatedSourceRecordAt rate rewards C_star C_h s hs x b).output.next
      (((generatedSourceRun rate rewards C_star C_h s hs x).records.take n.val).drop (b.val + 1))
      (generatedSourceRecordAt rate rewards C_star C_h s hs x n).input.state := by
  let total := generatedSourceRun rate rewards C_star C_h s hs x
  have hcount : total.records.length = p.T - s := generated_run_length rate rewards C_star C_h s hs x
  have hn : n.val < total.records.length := by rw [hcount]; exact n.isLt
  have hb : b.val < (total.records.take n.val).length := by
    rw [List.length_take, hcount]
    omega
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input total.connected n.val hn
  have hsegment := ReferenceFollowerReplyChronology.connected_drop_from_output hprefix b.val hb
  have hbget : (total.records.take n.val)[b.val] =
      generatedSourceRecordAt rate rewards C_star C_h s hs x b := by
    rw [List.getElem_take, generated_record_get rate rewards C_star C_h s hs x b]
  rw [hbget, generated_record_get rate rewards C_star C_h s hs x n] at hsegment
  exact hsegment

private theorem generated_ordinary_choices
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (ReferenceFollowerFixedReply.actualChoice
      (generatedSourceRecordAt rate rewards C_star C_h s hs x n) i).configuration =
        .ordinary state memory)
    (k : Fin (p.T - s)) (hkn : k.val ≤ n.val) :
    ∃ earlier earlierMemory,
      (ReferenceFollowerFixedReply.actualChoice
        (generatedSourceRecordAt rate rewards C_star C_h s hs x k) i).configuration =
          .ordinary earlier earlierMemory := by
  by_cases heq : k = n
  · subst k
    exact ⟨state, memory, hchoice⟩
  have hlt : k.val < n.val := by
    have hne : k.val ≠ n.val := fun h => heq (Fin.ext h)
    omega
  let total := generatedSourceRun rate rewards C_star C_h s hs x
  have hcount : total.records.length = p.T - s := generated_run_length rate rewards C_star C_h s hs x
  have hn : n.val < total.records.length := by rw [hcount]; exact n.isLt
  have hk : k.val < (total.records.take n.val).length := by
    rw [List.length_take, hcount]
    omega
  obtain ⟨before, beforeMemory, hbefore, _, _⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice
      (generatedSourceRecordAt rate rewards C_star C_h s hs x n) i state memory hchoice
  have hprefix := ReferenceFollowerReplyChronology.connected_take_to_input total.connected n.val hn
  rw [generated_record_get rate rewards C_star C_h s hs x n] at hprefix
  obtain ⟨after, afterMemory, hafter, _⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hprefix i before beforeMemory hbefore k.val hk
  rw [List.getElem_take, generated_record_get rate rewards C_star C_h s hs x k] at hafter
  obtain ⟨earlier, earlierMemory, hc, _, _, _⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology
      (generatedSourceRecordAt rate rewards C_star C_h s hs x k) i after afterMemory hafter
  exact ⟨earlier, earlierMemory, hc⟩

private theorem continuing_selection
    (record : Record (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput record.input r q base))
    (hcut : record.output.preparation.coordinator = .live r q base outcome)
    (hcontinue : ∃ dispatched hstart continuation arm,
      outcome = .continuingChosen dispatched hstart continuation arm) :
    (∃ selected : Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = r.payload) ∧
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false ∧
      ∀ fresh : Payload rate, ¬ InstallationBirth record fresh := by
  rcases hcontinue with ⟨dispatched, hstart, continuation, arm, rfl⟩
  have hnonempty : record.output.preparation.coordinator.selection ≠ none := by
    simp only [hcut, DispatchCut.selection, selectionAt, dite_true]
    exact Option.some_ne_none _
  obtain ⟨selected, hselected⟩ := Option.ne_none_iff_exists'.mp hnonempty
  have hfields := selectionAt_fields record.input r.payload dispatched.startResult
    record.input.time (liveRegistersAt r record.input.time).complementWeights arm selected
    (by simpa only [hcut, DispatchCut.selection] using hselected)
  have hactual : (prepare record.input).coordinator =
      .live r q base (.continuingChosen dispatched hstart continuation arm) := by
    rw [← record_prepared_eq record]
    exact hcut
  refine ⟨⟨selected, hselected, hfields.1⟩, ?_, ?_⟩
  · simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hactual]
  · intro fresh
    simp only [InstallationBirth, hcut, not_false_eq_true]

/-- The actual generated segment for one retained assignment. Every physical
connection, successful predecessor, phase, selection, ordinary focal CHOICE,
and pending initializer is produced from the original execution. Only the
endpoint's actual branch, selection, and ordinary focal CHOICE select this
internal case. The detecting endpoint itself need not have a successful tail.
-/
theorem generated_live_actual_payload_segment
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)
    (n : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    let R := generatedSourceRecordAt rate rewards C_star C_h s hs x
    match (R n).output.preparation.coordinator with
    | .live _ _ _ (.continuingChosen _ _ _ _) =>
        ∀ selected : Selection (R n).input,
          (R n).output.preparation.coordinator.selection = some selected →
        ∀ (state : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice (R n) i).configuration = .ordinary state memory →
        ∃ b : Fin (p.T - s), b.val < n.val ∧
          InstallationBirth (R b) selected.view.payload ∧
          selected.view.payload.sigma.val = s + b.val ∧
          (selected.view.payload.downRecord i).val.sigma = s + b.val + 1 ∧
          (∃ birthState birthMemory,
            (ReferenceFollowerFixedReply.actualChoice (R b) i).configuration =
              .ordinary birthState birthMemory ∧
            birthState.status = .unoccupied ∧
            ∃ before beforeMemory,
              (R b).input.state.followers i = .ordinary before beforeMemory ∧
              before.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply birthState =
                ReferenceFollowerReplyChronology.reply before ∧
              birthState.downBatch = before.downBatch ∧
              birthState.buffer = before.buffer ∧
              birthState.initializationFailure = before.initializationFailure ∧
              birthMemory = beforeMemory) ∧
          (∃ birthSelected : Selection (R b).input,
            (R b).output.preparation.coordinator.selection = some birthSelected ∧
            birthSelected.view.payload = selected.view.payload ∧
            birthSelected.view.pendingAtChoice = Finset.univ ∧
            birthSelected.started.pending = Finset.univ) ∧
          (∃ r q base,
            (R b).output.next.coordinator = .live r q base ∧
            r.payload = selected.view.payload) ∧
          Connected (R b).output.next
            (((generatedSourceRun rate rewards C_star C_h s hs x).records.take n.val).drop (b.val + 1))
            (R n).input.state ∧
          (∀ k : Fin (p.T - s), b.val < k.val → k.val ≤ n.val →
            ∃ r q base, ∃ (outcome : CoordinatorRoundDispatch.LiveOutcome
              (liveInput (R k).input r q base)),
              (R k).input.state.coordinator = .live r q base ∧
              (R k).output.preparation.coordinator = .live r q base outcome ∧
              (∃ dispatched hstart continuation arm,
                outcome = .continuingChosen dispatched hstart continuation arm) ∧
              r.payload = selected.view.payload ∧
              (∃ currentSelected : Selection (R k).input,
                (R k).output.preparation.coordinator.selection = some currentSelected ∧
                currentSelected.view.payload = selected.view.payload) ∧
              ReferenceCollectionPhaseHistory.cutoffChosen (R k).input = false ∧
              ∀ fresh : Payload rate, ¬ InstallationBirth (R k) fresh) ∧
          (∀ k : Fin (p.T - s), b.val ≤ k.val → k.val < n.val →
            ∃ r q base,
              (R k).output.next.coordinator = .live r q base ∧
              r.payload = selected.view.payload) ∧
          (∀ k : Fin (p.T - s), b.val ≤ k.val → k.val ≤ n.val →
            (R k).input.time.val = s + k.val ∧ s + k.val < p.T ∧
            ∃ earlier earlierMemory,
              (ReferenceFollowerFixedReply.actualChoice (R k) i).configuration =
                .ordinary earlier earlierMemory)
    | _ => True := by
  classical
  dsimp only
  let R := generatedSourceRecordAt rate rewards C_star C_h s hs x
  cases hcoord : (R n).output.preparation.coordinator with
  | first _ => trivial
  | live endpoint endpointOwned endpointBase outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          intro selected hselected state memory hchoice
          have hinit :=
            ReferenceGeneratedAssignmentLiveErasureHistory.generated_live_actual_payload_birth_initializer
              rate rewards C_star C_h s hs x n i
          dsimp only at hinit
          rw [hcoord] at hinit
          obtain ⟨b, hbn, hbirth, hdate, hinitializer⟩ :=
            hinit selected hselected state memory hchoice
          have hfields := selectionAt_fields (R n).input endpoint.payload dispatched.startResult
            (R n).input.time (liveRegistersAt endpoint (R n).input.time).complementWeights
            arm selected (by simpa only [hcoord, DispatchCut.selection] using hselected)
          have hendpoint : (R n).input.state.coordinator =
              .live endpoint endpointOwned endpointBase := by
            have h := prepared_input_origin (R n).input
            rw [← record_prepared_eq (R n), hcoord] at h
            exact h
          have hincoming : ∀ k : Fin (p.T - s), b.val < k.val → k.val ≤ n.val →
              ∃ r q base, (R k).input.state.coordinator = .live r q base ∧
                r.payload = selected.view.payload := by
            intro k hbk hkn
            refine Nat.decreasingInduction' (n := n.val) (m := k.val)
              (P := fun j => ∀ hj : j < p.T - s, b.val < j →
                ∃ r q base, (R ⟨j, hj⟩).input.state.coordinator = .live r q base ∧
                  r.payload = selected.view.payload) ?_ hkn ?_ k.isLt hbk
            · intro j hjn _ ih hj hbj
              let nextIndex : Fin (p.T - s) := ⟨j + 1, by omega⟩
              obtain ⟨next, nextOwned, nextBase, hnextInput, hnextPayload⟩ :=
                ih nextIndex.isLt (by omega)
              have hconnection := generated_adjacent rate rewards C_star C_h s hs x
                ⟨j, hj⟩ nextIndex rfl
              have hnext : (R ⟨j, hj⟩).output.next.coordinator =
                  .live next nextOwned nextBase := by
                rw [hconnection]
                exact hnextInput
              have hearlier : next.payload.sigma.val < (R ⟨j, hj⟩).input.time.val := by
                rw [hnextPayload, hdate, generated_record_time]
                change s + b.val < s + j
                omega
              obtain ⟨r, q, base, outcome, hin, _, _, hframe, _⟩ :=
                record_live_predecessor (R ⟨j, hj⟩) next nextOwned nextBase hnext hearlier
              exact ⟨r, q, base, hin, hframe.trans hnextPayload⟩
            · intro _ _
              exact ⟨endpoint, endpointOwned, endpointBase, hendpoint, hfields.1.symm⟩
          have hsuccess : ∀ k : Fin (p.T - s), b.val ≤ k.val → k.val < n.val →
              ∃ r q base, (R k).output.next.coordinator = .live r q base ∧
                r.payload = selected.view.payload := by
            intro k hbk hkn
            let j : Fin (p.T - s) := ⟨k.val + 1, by omega⟩
            obtain ⟨r, q, base, hin, hpayload⟩ := hincoming j (by dsimp only [j]; omega)
              (by dsimp only [j]; omega)
            refine ⟨r, q, base, ?_, hpayload⟩
            rw [generated_adjacent rate rewards C_star C_h s hs x k j rfl]
            exact hin
          obtain ⟨birthNext, birthOwned, birthBase, hbirthNext, hbirthPayload⟩ :=
            hsuccess b (Nat.le_refl _) hbn
          obtain ⟨birthSelected, hbirthSelected, _, _⟩ :=
            record_live_output_origin (R b) birthNext birthOwned birthBase hbirthNext
          have hbirthPending := birth_selection_pending (R b) selected.view.payload
            hbirth birthSelected hbirthSelected
          refine ⟨b, hbn, hbirth, hdate, ?_, hinitializer,
            ⟨birthSelected, hbirthSelected, hbirthPending⟩,
            ⟨birthNext, birthOwned, birthBase, hbirthNext, hbirthPayload⟩,
            generated_connected_segment rate rewards C_star C_h s hs x b n hbn,
            ?_, hsuccess, ?_⟩
          · change selected.view.payload.sigma.val + 1 = s + b.val + 1
            rw [hdate]
          · intro k hbk hkn
            have hphase : ∃ r q base, ∃ (outcome : CoordinatorRoundDispatch.LiveOutcome
                (liveInput (R k).input r q base)),
                (R k).input.state.coordinator = .live r q base ∧
                (R k).output.preparation.coordinator = .live r q base outcome ∧
                (∃ dispatched hstart continuation arm,
                  outcome = .continuingChosen dispatched hstart continuation arm) ∧
                r.payload = selected.view.payload := by
              by_cases heq : k = n
              · subst k
                exact ⟨endpoint, endpointOwned, endpointBase,
                  .continuingChosen dispatched hstart continuation arm,
                  hendpoint, hcoord, ⟨dispatched, hstart, continuation, arm, rfl⟩, hfields.1.symm⟩
              · have hlt : k.val < n.val := by
                  have hne : k.val ≠ n.val := fun h => heq (Fin.ext h)
                  omega
                obtain ⟨next, nextOwned, nextBase, hnext, hpayload⟩ :=
                  hsuccess k (Nat.le_of_lt hbk) hlt
                have hearlier : next.payload.sigma.val < (R k).input.time.val := by
                  rw [hpayload, hdate, generated_record_time]
                  omega
                obtain ⟨r, q, base, outcome, hin, hcut, hcont, hframe, _⟩ :=
                  record_live_predecessor (R k) next nextOwned nextBase hnext hearlier
                exact ⟨r, q, base, outcome, hin, hcut, hcont, hframe.trans hpayload⟩
            rcases hphase with ⟨r, q, base, outcome, hin, hcut, hcont, hpayload⟩
            obtain ⟨hselection, hcutoff, hnoBirth⟩ :=
              continuing_selection (R k) r q base outcome hcut hcont
            refine ⟨r, q, base, outcome, hin, hcut, hcont, hpayload, ?_, hcutoff, hnoBirth⟩
            rcases hselection with ⟨currentSelected, hc, hp⟩
            exact ⟨currentSelected, hc, hp.trans hpayload⟩
          · intro k _ hkn
            refine ⟨generated_record_time rate rewards C_star C_h s hs x k, ?_, ?_⟩
            · omega
            · exact generated_ordinary_choices rate rewards C_star C_h s hs x n i
                state memory hchoice k hkn
      | cutoffChosen _ _ _ _ _ _ _ _ _ _ => trivial
      | clockFailure _ _ => trivial
      | initializerFailure _ _ _ _ => trivial
      | localFailure _ _ _ => trivial
  | collection _ _ _ _ _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

end Bandits.Support.ReferenceGeneratedAssignmentLiveSegment

end
