/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSuffixFollowerPreservation

import Lean.Elab.Tactic.Omega

/-!
# Matching DOWN senders on the original complete physical suffix

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,270-288,327-348`,
`sources/zip4/manuscript/05_binary_transport.tex:60-124`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The chronology below keeps the original whole source and rewards. A successful
current selection supplies the branch on which a wrong locally accepted DOWN
word is excluded from every earlier matching sender. The absent-selection
branch is retained explicitly. These are internal structural results, without
physical queue, stopping, probability, or manuscript closure assertions.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceAssignmentPayloadPersistence
open ReferenceGeneratedDownBatchCalendar
open ReferenceGeneratedInheritedDownWrongCompletionWitness

namespace Bandits.Support.ReferenceCompleteMatchingDownSenderChronology

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem selectionAt_payload
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (v : Selection x) (hv : selectionAt x payload started time weights choice = some v) :
    v.view.payload = payload := by
  by_cases ht : time = x.time
  · simp only [selectionAt, dite_eq_left ht] at hv
    exact (congrArg (fun a : Selection x => a.view.payload) (Option.some.inj hv)).symm
  · simp only [selectionAt, dite_eq_right ht] at hv
    cases hv

private theorem selectionAt_pending
    (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (choice : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (v : Selection x) (hv : selectionAt x payload started time weights choice = some v) :
    v.view.pendingAtChoice = started.pending := by
  by_cases ht : time = x.time
  · simp only [selectionAt, dite_eq_left ht] at hv
    exact (congrArg (fun a : Selection x => a.view.pendingAtChoice)
      (Option.some.inj hv)).symm
  · simp only [selectionAt, dite_eq_right ht] at hv
    cases hv

private theorem live_tail_configuration
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (livePostChoice prepared r q base started).configuration = .dagger ∨
      (storedPayload (livePostChoice prepared r q base started).configuration =
        some r.payload ∧
        (livePostChoice prepared r q base started).configuration ≠ .first) := by
  classical
  unfold livePostChoice
  cases CoordinatorRecorderComplementBridge.run (liveRecordingInput prepared r started) with
  | none => exact Or.inl rfl
  | some recording =>
    cases hs : CoordinatorLiveServiceFinish.servicePass r q recording with
    | error reason => simp only [hs]; exact Or.inl rfl
    | ok serviced =>
      cases CoordinatorLocalArmChoice.confirmationUpdate r.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none => simp only [hs]; exact Or.inl rfl
      | some pending =>
        cases hf : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock pending x.row with
        | error reason => simp only [hs, hf]; exact Or.inl rfl
        | ok finished => simp [hs, hf, storedPayload]

private theorem collection_finish_configuration
    {x : RoundInput p rate} (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : UpCut p rate) :
    (collectionFinish (x := x) payload started recording cut).configuration = .dagger ∨
      (storedPayload (collectionFinish (x := x) payload started recording cut).configuration =
        some payload ∧
        (collectionFinish (x := x) payload started recording cut).configuration ≠ .first) := by
  unfold collectionFinish
  cases cut.result with
  | invalid => exact Or.inl rfl
  | success pair | rejected pair =>
    rcases pair with ⟨ledger, bank⟩
    cases hl : CoordinatorCollectionLedger.finishRound ledger with
    | invalid => simp only [hl]; exact Or.inl rfl
    | rejected reason => simp only [hl]; exact Or.inl rfl
    | success finished =>
      cases hc : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
          started.clock finished.pending x.row with
      | error reason => simp only [hl, hc]; exact Or.inl rfl
      | ok clock => simp [hl, hc, storedPayload]

private theorem collection_tail_configuration
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (collectionPostChoice prepared payload ledger started weights).configuration = .dagger ∨
      (storedPayload (collectionPostChoice prepared payload ledger started weights).configuration =
        some payload ∧
        (collectionPostChoice prepared payload ledger started weights).configuration ≠ .first) := by
  classical
  unfold collectionPostChoice
  cases CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput prepared payload started weights) with
  | none => exact Or.inl rfl
  | some recording =>
    cases hl : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
    | invalid => simp only [hl]; exact Or.inl rfl
    | rejected reason => simp only [hl]; exact Or.inl rfl
    | success startedLedger =>
      simpa only [hl] using collection_finish_configuration (x := x) payload started
        recording (receiveUp prepared startedLedger)

/-- A missing actual selection goes directly to dagger, including alignment
and checked-dispatch failures. It never returns to the first phase. -/
private theorem actual_no_selection_next_dagger
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hv : r.output.preparation.coordinator.selection = none) :
    r.output.next.coordinator = .dagger := by
  have hp : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
  have hn : (prepare r.input).coordinator.selection = none := by simpa [hp] using hv
  rw [r.output_eq]
  change (prepare r.input).observeCoordinator.configuration = .dagger
  unfold PreparedRound.observeCoordinator
  rw [dite_eq_left hn]
  cases (prepare r.input).coordinator <;> rfl

/-- The payload selected before observations is retained whole on a successful
tail. Every failed tail is dagger. No success of the current tail is assumed. -/
private theorem actual_selected_next_retained_or_dagger
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v) :
    r.output.next.coordinator = .dagger ∨
      storedPayload r.output.next.coordinator = some v.view.payload := by
  classical
  have hp : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
  have hn : (prepare r.input).coordinator.selection ≠ none := by rw [← hp, hv]; simp
  have hs : (prepare r.input).coordinator.selection = some v := by simpa [hp] using hv
  rw [r.output_eq]
  change (prepare r.input).observeCoordinator.configuration = .dagger ∨
    storedPayload (prepare r.input).observeCoordinator.configuration = some v.view.payload
  unfold PreparedRound.observeCoordinator
  rw [dite_eq_right hn]
  cases hc : (prepare r.input).coordinator with
  | first outcome =>
    cases outcome <;> try { simp [hc, DispatchCut.selection] at hs }
    rename_i installed choice
    have hpay := selectionAt_payload r.input _ _ _ _ choice v
      (by simpa [hc, DispatchCut.selection] using hs)
    rw [hpay]
    exact (live_tail_configuration _ _ _ _ _).imp_right And.left
  | live registers owned base outcome =>
    cases outcome <;> try { simp [hc, DispatchCut.selection] at hs }
    · rename_i dispatched hstart ledger hi he hd hclock hpending hno choice
      have hpay := selectionAt_payload r.input registers.payload
        dispatched.startResult r.input.time (liveRegistersAt registers r.input.time).complementWeights
        choice v (by simpa [hc, DispatchCut.selection] using hs)
      rw [hpay]
      exact (collection_tail_configuration _ _ _ _ _).imp_right And.left
    · rename_i dispatched hstart continuation choice
      have hpay := selectionAt_payload r.input registers.payload
        dispatched.startResult r.input.time (liveRegistersAt registers r.input.time).complementWeights
        choice v (by simpa [hc, DispatchCut.selection] using hs)
      rw [hpay]
      exact (live_tail_configuration _ _ _ _ _).imp_right And.left
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> try { simp [hc, DispatchCut.selection] at hs }
    · rename_i core snapshot boundary scores
      have hpay : v.view.payload = payload := by
        have hm := congrArg (Option.map fun a : Selection r.input => a.view.payload) hs
        simpa [hc, DispatchCut.selection] using hm.symm
      rw [hpay]
      exact (collection_tail_configuration _ _ _ _ _).imp_right And.left
    · rename_i core consistent started hstart instruction hi output hlocal data installed choice
      have hpay := selectionAt_payload r.input _ _ _ _ choice v
        (by simpa [hc, DispatchCut.selection] using hs)
      rw [hpay]
      exact (live_tail_configuration _ _ _ _ _).imp_right And.left
  | invalidCollectionCutoff => simp [hc, DispatchCut.selection] at hs
  | dagger => simp [hc, DispatchCut.selection] at hs

/-- No actual physical step returns the coordinator to its initial phase. -/
private theorem actual_next_ne_first
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    r.output.next.coordinator ≠ .first := by
  cases hs : r.output.preparation.coordinator.selection with
  | none => rw [actual_no_selection_next_dagger r hs]; intro h; cases h
  | some v =>
    rcases actual_selected_next_retained_or_dagger r v hs with hd | hp
    · rw [hd]; intro h; cases h
    · intro hf
      rw [hf] at hp
      cases hp

private theorem dispatch_origin (x : RoundInput p rate) :
    match (prepare x).coordinator with
    | .first _ => x.state.coordinator = .first
    | .live registers owned base _ => x.state.coordinator = .live registers owned base
    | .collection payload ledger _ _ _ =>
        ∃ proposal, x.state.coordinator = .collection payload ledger proposal
    | .invalidCollectionCutoff => True
    | .dagger => x.state.coordinator = .dagger := by
  change match dispatch x with
    | .first _ => _
    | .live registers owned base _ => _
    | .collection payload ledger _ _ _ => _
    | .invalidCollectionCutoff => _
    | .dagger => _
  cases hc : x.state.coordinator with
  | first => rw [dispatch_first x hc]
  | live registers owned base =>
    have he : dispatch x = .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base)) := by
      simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
      rfl
    rw [he]
  | dagger => rw [dispatch_dagger x hc]
  | collection payload ledger proposal =>
    by_cases hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      have he : dispatch x = .collection payload ledger
          (collectionClock payload ledger proposal cutoff) cutoff
          (CoordinatorRoundDispatch.dispatchCollection
            (collectionInput x payload ledger (collectionClock payload ledger proposal cutoff)
              cutoff)) := by
        simp only [dispatch, hc, hv, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [he]
      exact ⟨proposal, rfl⟩
    · rw [(dispatch_collection_invalid_cutoff x payload ledger proposal hc hv).1]
      trivial

/-- A selected later branch supplies its incoming stored assignment, empty
pending set, physical cursor, and fresh timestamp from the actual constructor.
The physical ledger start is one greater than the zero-based payload sigma. -/
private theorem actual_later_selection_provenance
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen r.input = true) :
    v.view.payload.sigma.val = r.input.time.val ∧
      ∃ payload ledger proposal,
        r.input.state.coordinator = .collection payload ledger proposal ∧
        ledger.sigma = payload.sigma.val + 1 ∧ ledger.pending = ∅ ∧
        ledger.cursor = r.input.time.val + 1 := by
  have hp : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
  have ho := dispatch_origin r.input
  have ht := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance r.input
  have hactual : dispatch r.input = r.output.preparation.coordinator := by
    rw [hp]; rfl
  rw [hactual] at ht
  rw [← hp] at ho
  obtain ⟨old, oldLedger, proposal, hstate, hempty⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty r.input hlater
  rw [ReferenceCollectionPhaseHistory.laterChosen, ← hp] at hlater
  cases hc : r.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
    cases outcome <;> try { simp only [hc, Bool.false_eq_true] at hlater }
    rename_i core consistent started hstart instruction hi output hlocal data installed choice
    rw [hc] at ho ht
    obtain ⟨actualProposal, hcoord⟩ := ho
    have hpay := selectionAt_payload r.input _ _ _ _ choice v
      (by simpa [hc, DispatchCut.selection] using hv)
    have hledger : oldLedger = ledger := by
      rw [hcoord] at hstate
      cases hstate
      rfl
    refine ⟨(congrArg (fun a : Payload rate => a.sigma.val) hpay).trans ht.2.2.1,
      payload, ledger, actualProposal, hcoord, ?_, hledger ▸ hempty, ?_⟩
    · exact core.ledger_sigma_eq
    · exact core.ledger_cursor_eq
  | first outcome => simp only [hc, Bool.false_eq_true] at hlater
  | live registers owned base outcome => simp only [hc, Bool.false_eq_true] at hlater
  | invalidCollectionCutoff => simp only [hc, Bool.false_eq_true] at hlater
  | dagger => simp only [hc, Bool.false_eq_true] at hlater

private theorem selected_retains_without_later
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (v : Selection r.input)
    (hv : r.output.preparation.coordinator.selection = some v)
    (hfirst : r.input.state.coordinator ≠ .first)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen r.input = false) :
    storedPayload r.input.state.coordinator = some v.view.payload := by
  rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
      r v hv with hstored | hbirth
  · exact hstored
  · have ho := dispatch_origin r.input
    have hp : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
    rw [← hp] at ho
    rw [ReferenceCollectionPhaseHistory.laterChosen, ← hp] at hlater
    cases hc : r.output.preparation.coordinator with
    | first outcome =>
      rw [hc] at ho
      exact False.elim (hfirst ho)
    | live registers owned base outcome => simp [InstallationBirth, hc] at hbirth
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp [InstallationBirth, hc] at hbirth
      simp [hc] at hlater
    | invalidCollectionCutoff => simp [InstallationBirth, hc] at hbirth
    | dagger => simp [InstallationBirth, hc] at hbirth

private theorem reference_cut_fields
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (time : Fin p.T) (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta) :
    let cut := ReferenceDownReception.referenceDownCut p view i row time observation rate logged
    cut.expectedWord = ReferenceDownReception.expectedDownFlatWord view i row time ∧
      cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
      (cut.rawComparison = some false → cut.raw ≠ cut.expectedWord) := by
  classical
  dsimp only
  unfold ReferenceDownReception.referenceDownCut
  split
  · split
    · split
      · split
        · split
          · dsimp only
            split
            · exact ⟨rfl, rfl, by intro h; cases h⟩
            next hmatch => exact ⟨rfl, rfl, fun _ => hmatch⟩
          · exact ⟨rfl, rfl, by intro h; cases h⟩
        · exact ⟨rfl, rfl, by intro h; cases h⟩
      · exact ⟨rfl, rfl, by intro h; cases h⟩
    · exact ⟨rfl, rfl, by intro h; cases h⟩
  · exact ⟨rfl, rfl, by intro h; cases h⟩

private theorem actual_cut_fields
    (r : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (r.output.followers i).down = some cut) :
    cut.expectedWord = ReferenceDownReception.expectedDownFlatWord
        r.output.preparation.coordinator.downView i r.input.row r.input.time ∧
      cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate cut.raw ∧
      (cut.rawComparison = some false → cut.raw ≠ cut.expectedWord) := by
  obtain ⟨_choice, _memory, logged, _hc, _hu, _hl, hlogged, _hsource⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hcut
  have he := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    r i logged cut hlogged hcut
  rw [he]
  exact reference_cut_fields _ _ _ _ _ _

private theorem actual_wrong_down_selected
    (r : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (r.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut) :
    ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
  obtain ⟨_choice, _memory, logged, _hc, _hu, _hl, hlogged, _hsource⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hcut
  have he := ReferenceDownCompletedAmbiguityMeasurability.record_downCut_eq_actual
    r i logged cut hlogged hcut
  have hfalse := hwrong.1
  rw [he] at hfalse
  by_contra hnot
  simp [ReferenceDownReception.referenceDownCut, hnot] at hfalse

private theorem pending_wrong_word_ne
    (r : RoundRecord (p := p) (rate := rate)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : (r.output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (v : Selection r.input) (hv : r.output.preparation.coordinator.selection = some v)
    (hi : i ∈ v.view.pendingAtChoice) :
    cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i) := by
  have hfields := actual_cut_fields r i cut hcut
  have hdown := actual_wrong_down_selected r i cut hcut hwrong
  have hview : r.output.preparation.coordinator.downView = some v.view := by
    simp only [DispatchCut.downView, hv, Option.map_some]
  have hw := v.expected_down_word i ⟨hdown.1, hdown.2, hi⟩
  have he : cut.expectedWord =
      some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i) := by
    rw [hfields.1, hview]
    exact hw
  rw [← he]
  exact hfields.2.2 hwrong.1

section Generated

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (hs : s < p.T)
    (x : LaunchSource rate rewards C_star C_h s hs)

local notation "R" => generatedSourceRecordAt rate rewards C_star C_h s hs x
local notation "seed" => generatedSourceSeed rate rewards C_star C_h s hs x
local notation "rows" => Prod.snd (Prod.fst (Subtype.val x))
local notation "J" => ActualInitializationPhysicalStep.selectedRowIndex p x.val
local notation "mode" =>
  And.left (And.right (generatedSourceSeed_spec rate rewards C_star C_h s hs x))

private theorem generated_seed_followers :
    (seed).coordinator = .first ∧
      ∀ i : Fin (p.m - 1), ∃ first firstMemory,
        (seed).followers i = .ordinary first firstMemory ∧ first.lastDown = none := by
  have hspec := generatedSourceSeed_spec rate rewards C_star C_h s hs x
  obtain ⟨active, hactive, _hunique⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have hactiveEq : seed = active := Option.some.inj (hspec.1.symm.trans hactive.1)
  obtain ⟨fields, hlaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate x.val rewards C_star C_h x.property.1
  have hfieldsEq : seed = fields := Option.some.inj (hspec.1.symm.trans hlaunch)
  refine ⟨by rw [hactiveEq]; exact hactive.2.1, ?_⟩
  intro i
  obtain ⟨hc, hlast, _, _, _, _, _, _⟩ := hfields i
  refine ⟨ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate)
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput x.val rewards C_star C_h rate))
      (ActualReferenceInitializationBlock.refFollower i),
    ActiveFollowerLifecycle.initialMemory p, ?_, hlast⟩
  rw [hfieldsEq]
  exact hc

private theorem generated_complete_records :
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate x.val rewards C_star C_h =
      (generatedSourceRun rate rewards C_star C_h s hs x).records := by
  have he := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate x.val rewards C_star C_h seed
    (generatedSourceSeed_spec rate rewards C_star C_h s hs x).1
  have ht : ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h = s :=
    x.property.2
  change _ = (run seed rows J rewards s (p.T - s) (by omega) mode).records
  simpa only [ht] using he

private theorem generated_prefix_get
    (count : ℕ) (hspan : s + count ≤ p.T)
    (j : Fin (p.T - s)) (hj : j.val < count) :
    (run seed rows J rewards s count hspan mode).records[j.val]'
      (by rw [run_record_count]; exact hj) = R j := by
  have he := ReferenceDownCompletedAmbiguityMeasurability.run_records_eq_ofFn
    s count hspan (generatedSourceRunInput rate rewards C_star C_h s hs x)
  change (run seed rows J rewards s count hspan mode).records = _ at he
  rw [List.getElem_of_eq he]
  simp only [List.getElem_ofFn]
  rfl

private theorem generated_ordinary (j : Fin (p.T - s)) (i : Fin (p.m - 1)) :
    ∃ choice memory next nextMemory,
      (ReferenceFollowerFixedReply.actualChoice (R j) i).configuration =
        .ordinary choice memory ∧
      (R j).output.next.followers i = .ordinary next nextMemory := by
  have hlen : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h).length = p.T - s := by
    rw [generated_complete_records rate rewards C_star C_h s hs x]
    exact run_record_count seed rows J rewards s (p.T - s) (by omega) mode
  let index : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h).length := ⟨j.val, by rw [hlen]; exact j.isLt⟩
  have hrec : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h)[index.val] = R j := by
    rw [List.getElem_of_eq (generated_complete_records rate rewards C_star C_h s hs x)]
    exact generated_prefix_get rate rewards C_star C_h s hs x (p.T - s) (by omega) j j.isLt
  obtain ⟨_input, memory, choice, next, nextMemory,
      _hi, _hdom, _hstart, hc, _hchoiceDom, _hop, _hnextDom, _hout, _hfail, hn⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_preservation
      (rate := rate) rewards C_star C_h x.val index i
  rw [hrec] at hc hn
  exact ⟨choice, memory, next, nextMemory, hc, hn⟩

private theorem generated_choice_mono
    (i : Fin (p.m - 1)) (a b : Fin (p.T - s)) (hab : a.val ≤ b.val)
    (left right : ReferencePrelaunchFollower.State p rate.eta)
    (leftMemory rightMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hl : (ReferenceFollowerFixedReply.actualChoice (R a) i).configuration =
      .ordinary left leftMemory)
    (hr : (ReferenceFollowerFixedReply.actualChoice (R b) i).configuration =
      .ordinary right rightMemory) :
    ReferencePrelaunchFollower.acceptedStart left ≤ ReferencePrelaunchFollower.acceptedStart right := by
  have hlen := run_record_count seed rows J rewards s (p.T - s) (by omega) mode
  have hleft : (ReferenceFollowerFixedReply.actualChoice
      ((run seed rows J rewards s (p.T - s) (by omega) mode).records[a.val]'
        (by rw [hlen]; exact a.isLt)) i).configuration = .ordinary left leftMemory := by
    rw [generated_prefix_get rate rewards C_star C_h s hs x (p.T - s) (by omega) a a.isLt]
    exact hl
  have hright : (ReferenceFollowerFixedReply.actualChoice
      ((run seed rows J rewards s (p.T - s) (by omega) mode).records[b.val]'
        (by rw [hlen]; exact b.isLt)) i).configuration = .ordinary right rightMemory := by
    rw [generated_prefix_get rate rewards C_star C_h s hs x (p.T - s) (by omega) b b.isLt]
    exact hr
  exact (ReferenceFollowerReplyChronology.run_acceptedStart_mono seed rows J rewards s
    (p.T - s) (by omega) mode i ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ hab
    left right leftMemory rightMemory hleft hright).1

private theorem generated_record_eq_actual (j : Fin (p.T - s)) :
    R j = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      seed rows J rewards s j.val (by omega) mode := rfl

private theorem generated_input_time (j : Fin (p.T - s)) :
    (R j).input.time.val = s + j.val := rfl

private theorem generated_successor (j l : Fin (p.T - s)) (hl : l.val = j.val + 1) :
    (R l).input.state = (R j).output.next := by
  have hstep := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
    seed rows J rewards s j.val (by omega) mode
  rw [← generated_record_eq_actual rate rewards C_star C_h s hs x j] at hstep
  change (ReferenceActivePhysicalHorizon.run seed rows J rewards s l.val
    (by omega) mode).finalState = _
  simpa only [hl] using hstep

private theorem generated_input_ne_first (j : Fin (p.T - s)) (hj : 0 < j.val) :
    (R j).input.state.coordinator ≠ .first := by
  let b : Fin (p.T - s) := ⟨j.val - 1, by omega⟩
  have hlink := generated_successor rate rewards C_star C_h s hs x b j (by dsimp [b]; omega)
  rw [hlink]
  exact actual_next_ne_first (R b)

private theorem generated_dagger_absorbing (a b : Fin (p.T - s)) (hab : a.val ≤ b.val)
    (ha : (R a).input.state.coordinator = .dagger) :
    (R b).input.state.coordinator = .dagger := by
  have hall : ∀ j, a.val ≤ j → ∀ hj : j < p.T - s,
      (R ⟨j, hj⟩).input.state.coordinator = .dagger := by
    intro j haj
    induction j, haj using Nat.le_induction with
    | base => intro hj; exact ha
    | succ j haj ih =>
      intro hj
      let prior : Fin (p.T - s) := ⟨j, by omega⟩
      have hd : (R prior).input.state.coordinator = .dagger := ih prior.isLt
      have hn : (R prior).output.next.coordinator = .dagger := by
        rw [(R prior).output_eq]
        exact (step_coordinator_dagger (R prior).input hd).1
      rw [generated_successor rate rewards C_star C_h s hs x prior ⟨j + 1, hj⟩ rfl]
      exact hn
  exact hall b.val hab b.isLt

private theorem generated_selected_input_ne_dagger (n : Fin (p.T - s))
    (now : Selection (R n).input)
    (hnow : (R n).output.preparation.coordinator.selection = some now) :
    (R n).input.state.coordinator ≠ .dagger := by
  intro hd
  have hp : (R n).output.preparation.coordinator = .dagger := by
    rw [(R n).output_eq]
    exact dispatch_dagger (R n).input hd
  simp [hp, DispatchCut.selection] at hnow

private theorem generated_predecessor_next_ne_dagger (n : Fin (p.T - s))
    (now : Selection (R n).input)
    (hnow : (R n).output.preparation.coordinator.selection = some now)
    (j : Fin (p.T - s)) (hjn : j.val < n.val) :
    (R j).output.next.coordinator ≠ .dagger := by
  intro hd
  let after : Fin (p.T - s) := ⟨j.val + 1, by omega⟩
  have ha : (R after).input.state.coordinator = .dagger := by
    rw [generated_successor rate rewards C_star C_h s hs x j after rfl]
    exact hd
  exact generated_selected_input_ne_dagger rate rewards C_star C_h s hs x n now hnow
    (generated_dagger_absorbing rate rewards C_star C_h s hs x after n (by dsimp [after]; omega) ha)

private theorem generated_predecessor_selected (n : Fin (p.T - s))
    (now : Selection (R n).input)
    (hnow : (R n).output.preparation.coordinator.selection = some now)
    (j : Fin (p.T - s)) (hjn : j.val ≤ n.val) :
    ∃ v : Selection (R j).input, (R j).output.preparation.coordinator.selection = some v := by
  by_cases he : j = n
  · subst j; exact ⟨now, hnow⟩
  · have hlt : j.val < n.val := by
      have hne : j.val ≠ n.val := fun hv => he (Fin.ext hv)
      omega
    cases hv : (R j).output.preparation.coordinator.selection with
    | none =>
      exact False.elim
        (generated_predecessor_next_ne_dagger rate rewards C_star C_h s hs x n now hnow j hlt
          (actual_no_selection_next_dagger (R j) hv))
    | some v => exact ⟨v, rfl⟩

private theorem generated_retained_until (n : Fin (p.T - s))
    (now : Selection (R n).input)
    (hnow : (R n).output.preparation.coordinator.selection = some now)
    (k : Fin (p.T - s)) (old : Selection (R k).input)
    (hold : (R k).output.preparation.coordinator.selection = some old)
    (b : Fin (p.T - s)) (hkb : k.val < b.val) (hbn : b.val ≤ n.val)
    (hno : ∀ j : Fin (p.T - s), k.val < j.val → j.val < b.val →
      ReferenceCollectionPhaseHistory.laterChosen (R j).input = false) :
    storedPayload (R b).input.state.coordinator = some old.view.payload := by
  have hall : ∀ j, k.val + 1 ≤ j → ∀ hj : j < p.T - s, j ≤ b.val →
      storedPayload (R ⟨j, hj⟩).input.state.coordinator = some old.view.payload := by
    intro j hkj
    induction j, hkj using Nat.le_induction with
    | base =>
      intro hj _hle
      rw [generated_successor rate rewards C_star C_h s hs x k ⟨k.val + 1, hj⟩ rfl]
      exact (actual_selected_next_retained_or_dagger (R k) old hold).resolve_left
        (generated_predecessor_next_ne_dagger rate rewards C_star C_h s hs x n now hnow
          k (by omega))
    | succ j hkj ih =>
      intro hj hle
      let prior : Fin (p.T - s) := ⟨j, by omega⟩
      have hprior : k.val < prior.val ∧ prior.val < b.val := by dsimp [prior]; omega
      have hincoming := ih prior.isLt (by omega)
      obtain ⟨prev, hprev⟩ := generated_predecessor_selected
        rate rewards C_star C_h s hs x n now hnow prior (by omega)
      have hselected := selected_retains_without_later (R prior) prev hprev
        (generated_input_ne_first rate rewards C_star C_h s hs x prior (by omega))
        (hno prior hprior.1 hprior.2)
      have he : prev.view.payload = old.view.payload :=
        Option.some.inj (hselected.symm.trans hincoming)
      have hnext := (actual_selected_next_retained_or_dagger (R prior) prev hprev).resolve_left
        (generated_predecessor_next_ne_dagger rate rewards C_star C_h s hs x n now hnow
          prior (by omega))
      rw [generated_successor rate rewards C_star C_h s hs x prior ⟨j + 1, hj⟩ rfl, ← he]
      exact hnext
  exact hall b.val (by omega) b.isLt le_rfl

/-- The first later installation, if present, still has the complete old
payload at its input. All intermediate successful selections are produced from
the current selection and the absorbing failure branch. -/
private theorem first_intervening_installation
    (n k : Fin (p.T - s)) (hkn : k.val < n.val)
    (old : Selection (R k).input) (now : Selection (R n).input)
    (hold : (R k).output.preparation.coordinator.selection = some old)
    (hnow : (R n).output.preparation.coordinator.selection = some now) :
    old.view.payload = now.view.payload ∨
      ∃ (a : Fin (p.T - s)) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool)),
        k.val < a.val ∧ a.val ≤ n.val ∧
        ReferenceCollectionPhaseHistory.laterChosen (R a).input = true ∧
        (R a).input.state.coordinator = .collection old.view.payload ledger proposal ∧
        ledger.sigma = old.view.payload.sigma.val + 1 := by
  classical
  by_cases hex : ∃ a : Fin (p.T - s), k.val < a.val ∧ a.val ≤ n.val ∧
      ReferenceCollectionPhaseHistory.laterChosen (R a).input = true
  · have hexNat : ∃ a : ℕ, ∃ ha : a < p.T - s, k.val < a ∧ a ≤ n.val ∧
        ReferenceCollectionPhaseHistory.laterChosen (R ⟨a, ha⟩).input = true := by
      obtain ⟨a, hka, han, hlater⟩ := hex
      exact ⟨a.val, a.isLt, hka, han, hlater⟩
    obtain ⟨ha, hka, han, hlater⟩ := Nat.find_spec hexNat
    let a : Fin (p.T - s) := ⟨Nat.find hexNat, ha⟩
    have hminimal : ∀ b : Fin (p.T - s), k.val < b.val → b.val < a.val →
        ReferenceCollectionPhaseHistory.laterChosen (R b).input = false := by
      intro b hkb hba
      cases hb : ReferenceCollectionPhaseHistory.laterChosen (R b).input with
      | false => rfl
      | true =>
        exact False.elim (Nat.find_min hexNat hba
          ⟨b.isLt, hkb, by dsimp [a] at hba; omega, hb⟩)
    have hincoming := generated_retained_until rate rewards C_star C_h s hs x n now hnow
      k old hold a hka han hminimal
    obtain ⟨fresh, hfresh⟩ := generated_predecessor_selected
      rate rewards C_star C_h s hs x n now hnow a han
    obtain ⟨_htime, payload, ledger, proposal, hstate, hsigma, _hempty, _hcursor⟩ :=
      actual_later_selection_provenance (R a) fresh hfresh hlater
    have he : payload = old.view.payload := by
      rw [hstate] at hincoming
      exact Option.some.inj hincoming
    subst payload
    exact Or.inr ⟨a, ledger, proposal, hka, han, hlater, hstate, hsigma⟩
  · have hno : ∀ b : Fin (p.T - s), k.val < b.val → b.val ≤ n.val →
        ReferenceCollectionPhaseHistory.laterChosen (R b).input = false := by
      intro b hkb hbn
      cases hb : ReferenceCollectionPhaseHistory.laterChosen (R b).input with
      | false => rfl
      | true => exact False.elim (hex ⟨b, hkb, hbn, hb⟩)
    have hincoming := generated_retained_until rate rewards C_star C_h s hs x n now hnow
      k old hold n hkn le_rfl (fun b hkb hbn => hno b hkb (by omega))
    have hselected := selected_retains_without_later (R n) now hnow
      (generated_input_ne_first rate rewards C_star C_h s hs x n (by omega))
      (hno n hkn le_rfl)
    exact Or.inl (Option.some.inj (hincoming.symm.trans hselected))

private theorem generated_prior_accepted_bound
    (i : Fin (p.m - 1)) (a n : Fin (p.T - s)) (han : a.val < n.val)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (ha : ReferenceFirstLiveConfirmationHistory.AcceptedDown (R a) i M)
    (current : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : (ReferenceFollowerFixedReply.actualChoice (R n) i).configuration =
      .ordinary current memory) :
    M.val.sigma ≤ ReferencePrelaunchFollower.acceptedStart current := by
  obtain ⟨_old, _oldMemory, next, nextMemory, _hchoice, hnext⟩ :=
    generated_ordinary rate rewards C_star C_h s hs x a i
  have happlied : ReferenceFollowerReplyChronology.appliedDown (R a) i M.val.sigma := by
    obtain ⟨logged, cut, after, raw, scan, registers, service, hi, hd, ho⟩ := ha
    exact ⟨logged, cut, after, raw, M, scan, registers, service, hi, hd, ho, rfl⟩
  obtain ⟨_oldChoice, _oldMem, _hc, _hstrict, hstart⟩ :=
    ReferenceFollowerReplyChronology.record_appliedDown_strict (R a) i M.val.sigma
      happlied next nextMemory hnext
  let b : Fin (p.T - s) := ⟨a.val + 1, by omega⟩
  obtain ⟨after, afterMemory, _afterNext, _afterNextMemory, hafter, _hn⟩ :=
    generated_ordinary rate rewards C_star C_h s hs x b i
  obtain ⟨before, beforeMemory, hbefore, hreply, _hstatus⟩ :=
    ReferenceFollowerReplyChronology.record_input_to_choice (R b) i after afterMemory hafter
  have hi : (R b).input.state.followers i = .ordinary next nextMemory := by
    rw [generated_successor rate rewards C_star C_h s hs x a b rfl]
    exact hnext
  have he : before = next :=
    (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hbefore.symm.trans hi)).1
  have hafterStart : ReferencePrelaunchFollower.acceptedStart after =
      ReferencePrelaunchFollower.acceptedStart next := by
    rw [ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hreply, he]
  have hm := generated_choice_mono rate rewards C_star C_h s hs x i b n
    (by dsimp [b]; omega) after current afterMemory memory hafter hc
  omega

/-- A successor installation forces a genuine earlier accepted UP, and hence
an applied DOWN for the old start. The current ordinary strict-start test then
excludes that old whole record. -/
private theorem earlier_sender_payload_eq
    (i : Fin (p.m - 1)) (n k : Fin (p.T - s)) (hkn : k.val < n.val)
    (old : Selection (R k).input) (now : Selection (R n).input)
    (hold : (R k).output.preparation.coordinator.selection = some old)
    (hnow : (R n).output.preparation.coordinator.selection = some now)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((R n).output.followers i).down = some cut)
    (hparse : cut.ordinaryParse = some (old.view.payload.downRecord i))
    (haccept : cut.ordinaryAcceptance) : old.view.payload = now.view.payload := by
  rcases first_intervening_installation rate rewards C_star C_h s hs x n k hkn
      old now hold hnow with he | ⟨a, ledger, proposal, _hka, han, hlater, hstate, hsigma⟩
  · exact he
  · obtain ⟨current, currentMemory, hcurrent, _hu, hstrict⟩ :=
      ReferenceFirstLiveRawDownExclusion.retained_raw_down_parse_acceptance_actual_choice
        (R n) i cut (old.view.payload.downRecord i) hcut hparse haccept
    have hseed := generated_seed_followers rate rewards C_star C_h s hs x
    have hinput : (R a).input = ReferenceCollectionPhaseHistory.nextInput
        seed rows J rewards s a.val (by omega) mode := rfl
    have hhistory := ReferenceAcceptedUpFollowerHistory.run_laterStart_prior_down
      seed rows J rewards s a.val (by omega) mode hseed.1 hseed.2
      (by rw [← hinput]; exact hlater)
    obtain ⟨_before, _cutoff, _during, payload, oldLedger, oldProposal,
      _hrecords, _hcutoff, hcoordinator, _hempty, _hwindow, heach⟩ := hhistory
    have hledger : oldLedger = ledger := by
      have heq : CoordinatorConfiguration.collection payload oldLedger oldProposal =
          .collection old.view.payload ledger proposal := by
        rw [← hcoordinator, ← hinput]
        exact hstate
      exact (CoordinatorConfiguration.collection.inj heq).2.1
    obtain ⟨u, record, message, _hlower, hua, hget, _hup, hmessage,
      _downIndex, _prior, sender, upState, upMemory, _hdu, _hretained, _happlied,
      _hpriorSigma, hsender, hupChoice, _hunoccupied, _hoffer, hstart, _hstarted,
      _hS, _hdelta, _hbacklog, _hlast, _hsame, _hpositive⟩ := heach i
    let up : Fin (p.T - s) := ⟨u, by omega⟩
    have hrecord : record = R up := by
      have hlen := run_record_count seed rows J rewards s a.val (by omega) mode
      have hget' := List.getElem?_eq_getElem (l := (run seed rows J rewards s a.val
        (by omega) mode).records) (i := u) (by rw [hlen]; exact hua)
      rw [hget] at hget'
      exact (Option.some.inj hget').trans
        (generated_prefix_get rate rewards C_star C_h s hs x a.val (by omega) up hua)
    have hup : (ReferenceFollowerFixedReply.actualChoice (R up) i).configuration =
        .ordinary upState upMemory := by
      rw [← hrecord, ← hsender]
      exact hupChoice
    have hm := generated_choice_mono rate rewards C_star C_h s hs x i up n
      (by dsimp [up]; omega) upState current upMemory currentMemory hup hcurrent
    have hrecordSigma : (old.view.payload.downRecord i).val.sigma = ledger.sigma := by
      rw [old.view.payload.downRecord_fields i, hsigma]
    rw [hledger] at hmessage
    rw [hrecordSigma] at hstrict
    omega

private theorem generated_selected_wrong_word
    (n : Fin (p.T - s)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((R n).output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (v : Selection (R n).input)
    (hv : (R n).output.preparation.coordinator.selection = some v) :
    cut.raw ≠ some (CoordinatorLocalArmChoice.storedDownFlatWord v.view.payload i) := by
  classical
  by_cases hi : i ∈ v.view.pendingAtChoice
  · exact pending_wrong_word_ne (R n) i cut hcut hwrong v hv hi
  · intro hraw
    have hparse : cut.ordinaryParse = some (v.view.payload.downRecord i) := by
      rw [(actual_cut_fields (R n) i cut hcut).2.1, hraw]
      unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
      change OrdinaryMessageCodec.parseDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (some ((OrdinaryMessageCodec.wordEquivFlat
          (ReferencePrelaunchFollower.codecParams p rate.eta)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (ReferencePrelaunchFollower.codecParams p rate.eta))
            (v.view.payload.downWord i)))) = _
      rw [Equiv.symm_apply_apply]
      exact v.view.payload.parseDown_downWord i
    obtain ⟨current, memory, hcurrent, _hunoccupied, hstrict⟩ :=
      ReferenceFirstLiveRawDownExclusion.retained_raw_down_parse_acceptance_actual_choice
        (R n) i cut (v.view.payload.downRecord i) hcut hparse hwrong.2.2
    cases hcoord : (R n).output.preparation.coordinator with
    | first outcome =>
      cases outcome <;> try { simp [hcoord, DispatchCut.selection] at hv }
      rename_i installed choice
      have hp := selectionAt_pending (R n).input _ _ _ _ choice v
        (by simpa [hcoord, DispatchCut.selection] using hv)
      have hstart : installed.startRoundResult =
          CoordinatorAssignmentRegisterInstall.firstStartRoundResult _ :=
        Except.ok.inj (installed.startRound_eq.symm.trans
          (CoordinatorAssignmentRegisterInstall.first_start_round_success _))
      apply hi
      rw [hp, hstart]
      exact Finset.mem_univ i
    | live registers owned base outcome =>
      cases outcome <;> try { simp [hcoord, DispatchCut.selection] at hv }
      · rename_i dispatched hstart ledger he hiDomain hd hclock hpending hno choice
        have hp := selectionAt_pending (R n).input registers.payload
          dispatched.startResult (R n).input.time
          (liveRegistersAt registers (R n).input.time).complementWeights choice v
          (by simpa [hcoord, DispatchCut.selection] using hv)
        apply hi
        rw [hp, hpending]
        exact Finset.mem_univ i
      · rename_i dispatched hstart continuation choice
        have hprior := ReferenceGeneratedLiveConfirmationAcceptedDown.generated_live_missing_pending_prior_accepted_down
          rate rewards C_star C_h s hs x n i
        dsimp only at hprior
        rw [hcoord] at hprior
        obtain ⟨a, han, ha, _confirmation⟩ := hprior v (by simpa only [hcoord] using hv) current memory hcurrent hi
        have hm := generated_prior_accepted_bound rate rewards C_star C_h s hs x
          i a n han (v.view.payload.downRecord i) ha current memory hcurrent
        omega
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> try { simp [hcoord, DispatchCut.selection] at hv }
      · rename_i core snapshot boundary scores
        have hp : v.view.payload = payload := by
          have he := congrArg (Option.map fun a : Selection (R n).input => a.view.payload) hv
          simpa [hcoord, DispatchCut.selection] using he.symm
        have hne := ReferenceGeneratedRetainedCollectionStaleWordCut.generated_retained_collection_wrong_word
          rate rewards C_star C_h s hs x i n cut hcut hwrong
        rw [hcoord] at hne
        exact hne (by simpa only [hp] using hraw)
      · rename_i core consistent started hstart instruction hinstruction output hlocal data installed choice
        have hp := selectionAt_pending (R n).input _ _ _ _ choice v
          (by simpa [hcoord, DispatchCut.selection] using hv)
        have hu := (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
          (R n).input.time clock ledger.pending started instruction
          core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid
          hstart hinstruction).2.2.2.2.2.2.1
        apply hi
        rw [hp]
        rw [hu]
        exact Finset.mem_univ i
    | invalidCollectionCutoff => simp [hcoord, DispatchCut.selection] at hv
    | dagger => simp [hcoord, DispatchCut.selection] at hv

/-- Every earlier actual retained DOWN diagnostic is excluded, including
absent expected words. This statement uses the generated source only as the
literal original complete-source run. -/
private theorem generated_selected_not_sent
    (n : Fin (p.T - s)) (i : Fin (p.m - 1))
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (hcut : ((R n).output.followers i).down = some cut)
    (hwrong : ReferenceDownReception.wrongUniqueAccepted cut)
    (now : Selection (R n).input)
    (hnow : (R n).output.preparation.coordinator.selection = some now) :
    ∀ a : Fin (p.T - s), a.val ≤ n.val →
      ∀ oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate,
        ((R a).output.followers i).down = some oldCut → oldCut.expectedWord ≠ cut.raw := by
  intro a han oldCut holdCut hsent
  cases hraw : cut.raw with
  | none => exact hwrong.2.1 hraw
  | some word =>
    have hexpected : oldCut.expectedWord = some word := hsent.trans hraw
    obtain ⟨old, hold, _hbranch, hword, hparse, _hencode⟩ :=
      ReferenceGeneratedInheritedDownCandidateOrigin.actual_expectedDownWord_origin
        (R a) i oldCut word holdCut hexpected
    have hpayload : old.view.payload = now.view.payload := by
      by_cases heq : a = n
      · subst a
        exact congrArg (fun v : Selection (R n).input => v.view.payload)
          (Option.some.inj (hold.symm.trans hnow))
      · have hlt : a.val < n.val := by
          have hne : a.val ≠ n.val := fun he => heq (Fin.ext he)
          omega
        have hparseCurrent : cut.ordinaryParse = some (old.view.payload.downRecord i) := by
          rw [(actual_cut_fields (R n) i cut hcut).2.1, hraw]
          exact hparse
        exact earlier_sender_payload_eq rate rewards C_star C_h s hs x i n a hlt
          old now hold hnow cut hcut hparseCurrent hwrong.2.2
    apply generated_selected_wrong_word rate rewards C_star C_h s hs x n i cut hcut hwrong now hnow
    rw [hraw, hword, hpayload]
    rfl

end Generated

/-- On an actual selected branch of the original complete physical suffix,
a locally admissible wrong DOWN candidate was never the expected whole word
of an earlier retained diagnostic for this follower. No queue or stopping
condition, historical agreement, or survival premise is supplied. -/
theorem complete_selected_wrong_down_not_sent_before
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ k : Fin R.length,
      let r := R[k.val]
      ∀ (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
        (r.output.followers i).down = some cut →
        ReferenceDownReception.wrongUniqueAccepted cut →
        ∀ v : ReferenceActivePhysicalStep.Selection r.input,
          r.output.preparation.coordinator.selection = some v →
          ∀ a : Fin R.length, a.val ≤ k.val →
            ∀ oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate,
              ((R[a.val]).output.followers i).down = some oldCut →
              oldCut.expectedWord ≠ cut.raw := by
  classical
  dsimp only
  intro k i cut hcut hwrong v hv
  let L := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hlen : L.length = p.T - s :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hs : s < p.T := by
    have hk := k.isLt
    change k.val < L.length at hk
    omega
  have hlaunch : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h).isSome = true := by
    cases he : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none =>
      have hk := k.isLt
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, he] at hk
    | some active => rfl
  have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp hlaunch
  let x : LaunchSource rate rewards C_star C_h s hs := ⟨z, hcross, rfl⟩
  let n : Fin (p.T - s) := ⟨k.val, by have hk := k.isLt; change k.val < L.length at hk; omega⟩
  have hrecords := generated_complete_records rate rewards C_star C_h s hs x
  have hrecord (a : Fin L.length) : L[a.val] =
      generatedSourceRecordAt rate rewards C_star C_h s hs x
        ⟨a.val, by have ha := a.isLt; omega⟩ := by
    rw [List.getElem_of_eq hrecords]
    exact generated_prefix_get rate rewards C_star C_h s hs x (p.T - s) (by omega)
      ⟨a.val, by have ha := a.isLt; omega⟩ (by have ha := a.isLt; omega)
  have hcurrent : L[k.val] = generatedSourceRecordAt rate rewards C_star C_h s hs x n :=
    hrecord k
  have hlocal : ∀ (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
      ((L[k.val]).output.followers i).down = some cut →
      ReferenceDownReception.wrongUniqueAccepted cut →
      ∀ v : Selection (L[k.val]).input,
        (L[k.val]).output.preparation.coordinator.selection = some v →
        ∀ a : Fin L.length, a.val ≤ k.val →
          ∀ oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate,
            ((L[a.val]).output.followers i).down = some oldCut →
            oldCut.expectedWord ≠ cut.raw := by
    rw [hcurrent]
    intro currentCut hdown hbad selected hselected a ha oldCut hold
    let b : Fin (p.T - s) := ⟨a.val, by have hb := a.isLt; omega⟩
    apply generated_selected_not_sent rate rewards C_star C_h s hs x n i currentCut
      hdown hbad selected hselected b ha oldCut
    rw [← hrecord a]
    exact hold
  exact hlocal cut hcut hwrong v hv

/-- The original complete suffix either has its actual selection and the
historical exclusion above, or has no selection, no expected DOWN word, and
an actual dagger successor. The second branch is left open. -/
theorem complete_wrong_down_not_sent_or_no_selection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∀ k : Fin R.length,
      let r := R[k.val]
      ∀ (i : Fin (p.m - 1)) (cut : ReferenceDownReception.ReferenceDownCutOutput p rate),
        (r.output.followers i).down = some cut →
        ReferenceDownReception.wrongUniqueAccepted cut →
        (∃ v : ReferenceActivePhysicalStep.Selection r.input,
          r.output.preparation.coordinator.selection = some v ∧
          ∀ a : Fin R.length, a.val ≤ k.val →
            ∀ oldCut : ReferenceDownReception.ReferenceDownCutOutput p rate,
              ((R[a.val]).output.followers i).down = some oldCut →
              oldCut.expectedWord ≠ cut.raw) ∨
        (r.output.preparation.coordinator.selection = none ∧ cut.expectedWord = none ∧
          r.output.next.coordinator = ReferenceActivePhysicalStep.CoordinatorConfiguration.dagger) := by
  dsimp only
  intro k i cut hcut hwrong
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]
  cases hv : r.output.preparation.coordinator.selection with
  | none =>
    refine Or.inr ⟨rfl, ?_, actual_no_selection_next_dagger r hv⟩
    rw [(actual_cut_fields r i cut hcut).1]
    simp only [DispatchCut.downView, hv, Option.map_none,
      ReferenceDownReception.expectedDownFlatWord]
  | some v =>
    exact Or.inl ⟨v, rfl,
      complete_selected_wrong_down_not_sent_before rate rewards C_star C_h z k i cut
        hcut hwrong v hv⟩

end Bandits.Support.ReferenceCompleteMatchingDownSenderChronology

end
