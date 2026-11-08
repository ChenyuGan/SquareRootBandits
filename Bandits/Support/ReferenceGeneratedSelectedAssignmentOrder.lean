/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedRetainedCollectionStaleWordCut
public import Bandits.Support.ReferenceGeneratedDownCompletionTestInterval

/-!
# Selected assignments and the first intervening installation

Internal facts on the original generated reference execution. Sources:
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`,
`sources/zip4/manuscript/05_binary_transport.tex:60-78,95-103`,
`sources/zip4/manuscript/06_interruptions.tex:41-61,246-295,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:129-140,157`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

A cutoff retains the whole assignment. Only a chosen first or later installation
can replace it. Checked failures enter dagger; they cannot precede a later
selected round. Nothing here asserts stale-word exclusion or manuscript closure.
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

namespace Bandits.Support.ReferenceGeneratedSelectedAssignmentOrder

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
theorem actual_no_selection_next_dagger
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
theorem actual_selected_next_retained_or_dagger
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
theorem actual_next_ne_first
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
theorem actual_later_selection_provenance
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

private theorem generated_seed_first : (seed).coordinator = .first := by
  obtain ⟨active, hactive, _hunique⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate x.val rewards C_star C_h x.property.1
  have he : seed = active := Option.some.inj
    ((generatedSourceSeed_spec rate rewards C_star C_h s hs x).1.symm.trans hactive.1)
  rw [he]
  exact hactive.2.1

private theorem generated_selected_sigma_le_time (j : Fin (p.T - s))
    (v : Selection (R j).input)
    (hv : (R j).output.preparation.coordinator.selection = some v) :
    v.view.payload.sigma.val ≤ s + j.val := by
  have hm : R j ∈ (generatedSourceRun rate rewards C_star C_h s hs x).records :=
    List.mem_of_getElem?
      (generatedSourceRecordAt_getElem? rate rewards C_star C_h s hs x j)
  obtain ⟨birth, _hmem, _hbirth, _htime, hbound⟩ :=
    ReferenceSelectedPayloadChronology.actualRun_selectedPayload_has_birth
      seed rows J rewards s (p.T - s) (by omega) mode
      (generated_seed_first rate rewards C_star C_h s hs x) (R j) v hm hv
  exact hbound

private theorem generated_selected_sigma_mono (k n : Fin (p.T - s))
    (hkn : k.val ≤ n.val) (old : Selection (R k).input) (now : Selection (R n).input)
    (hold : (R k).output.preparation.coordinator.selection = some old)
    (hnow : (R n).output.preparation.coordinator.selection = some now) :
    old.view.payload.sigma.val ≤ now.view.payload.sigma.val := by
  have hbound := generated_selected_sigma_le_time rate rewards C_star C_h s hs x k old hold
  have hall : ∀ j, k.val ≤ j → ∀ hj : j < p.T - s, j ≤ n.val →
      ∀ v : Selection (R ⟨j, hj⟩).input,
        (R ⟨j, hj⟩).output.preparation.coordinator.selection = some v →
        old.view.payload.sigma.val ≤ v.view.payload.sigma.val := by
    intro j hkj
    induction j, hkj using Nat.le_induction with
    | base =>
      intro hj _hle v hv
      have he : v = old := Option.some.inj (hv.symm.trans hold)
      rw [he]
    | succ j hkj ih =>
      intro hj hle v hv
      let prior : Fin (p.T - s) := ⟨j, by omega⟩
      have hprior : prior.val < n.val := by dsimp [prior]; omega
      obtain ⟨prev, hprev⟩ := generated_predecessor_selected
        rate rewards C_star C_h s hs x n now hnow prior (by omega)
      have hlower := ih prior.isLt (by omega) prev hprev
      have hnext := (actual_selected_next_retained_or_dagger (R prior) prev hprev).resolve_left
        (generated_predecessor_next_ne_dagger rate rewards C_star C_h s hs x n now hnow
          prior hprior)
      have hincoming : storedPayload (R ⟨j + 1, hj⟩).input.state.coordinator =
          some prev.view.payload := by
        rw [generated_successor rate rewards C_star C_h s hs x prior ⟨j + 1, hj⟩ rfl]
        exact hnext
      rcases ReferenceSelectedPayloadChronology.actualSelectedPayload_local_stored_or_birth
          (R ⟨j + 1, hj⟩) v hv with hstored | hbirth
      · have he : prev.view.payload = v.view.payload :=
          Option.some.inj (hincoming.symm.trans hstored)
        rw [← he]
        exact hlower
      · have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
          (R ⟨j + 1, hj⟩) v.view.payload hbirth
        change v.view.payload.sigma.val = s + (j + 1) at ht
        rw [ht]
        exact hbound.trans (Nat.add_le_add_left (by omega) s)
  exact hall n.val hkn n.isLt le_rfl now hnow

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

/-- Two genuine selected assignments in the same generated execution are
identical, or their starts strictly increase. In the latter case this gives
the first later installation after the old selected round, with the exact old
incoming payload and empty pending set. No success after the current arm-choice
step, phase trace, or monotonicity premise is supplied by the caller.

The focal follower parameter is retained for the subsequent stale-word consumer;
assignment chronology itself holds simultaneously for every follower. -/
theorem generated_selected_assignment_first_intervening_installation
    (_i : Fin (p.m - 1)) (n : Fin (p.T - s)) (k : Fin (p.T - s))
    (hkn : k.val < n.val) (old : Selection (R k).input) (now : Selection (R n).input)
    (hold : (R k).output.preparation.coordinator.selection = some old)
    (hnow : (R n).output.preparation.coordinator.selection = some now) :
    old.view.payload = now.view.payload ∨
      (old.view.payload.sigma.val < now.view.payload.sigma.val ∧
        ∃ (a : Fin (p.T - s)) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool)),
          k.val < a.val ∧ a.val ≤ n.val ∧
          ReferenceCollectionPhaseHistory.laterChosen (R a).input = true ∧
          (R a).input.state.coordinator = .collection old.view.payload ledger proposal ∧
          ledger.sigma = old.view.payload.sigma.val + 1 ∧ ledger.pending = ∅ ∧
          s + a.val ≤ now.view.payload.sigma.val ∧
          (∀ b : Fin (p.T - s), k.val < b.val → b.val < a.val →
            ReferenceCollectionPhaseHistory.laterChosen (R b).input = false)) := by
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
        exact False.elim (Nat.find_min hexNat hba ⟨b.isLt, hkb, by dsimp [a] at hba; omega, hb⟩)
    have hincoming := generated_retained_until rate rewards C_star C_h s hs x n now hnow
      k old hold a hka han hminimal
    obtain ⟨fresh, hfresh⟩ := generated_predecessor_selected
      rate rewards C_star C_h s hs x n now hnow a han
    obtain ⟨htime, payload, ledger, proposal, hstate, hsigma, hempty, _hcursor⟩ :=
      actual_later_selection_provenance (R a) fresh hfresh hlater
    have he : payload = old.view.payload := by
      rw [hstate] at hincoming
      exact Option.some.inj hincoming
    subst payload
    have hbound := generated_selected_sigma_le_time rate rewards C_star C_h s hs x k old hold
    have hlower : s + a.val ≤ now.view.payload.sigma.val := by
      have hm := generated_selected_sigma_mono rate rewards C_star C_h s hs x a n han
        fresh now hfresh hnow
      rw [generated_input_time rate rewards C_star C_h s hs x a] at htime
      rw [← htime]
      exact hm
    have hstrict : old.view.payload.sigma.val < now.view.payload.sigma.val :=
      lt_of_le_of_lt hbound
        (lt_of_lt_of_le (Nat.add_lt_add_left (show k.val < a.val from hka) s) hlower)
    refine Or.inr ⟨hstrict, a, ledger, proposal, hka, han, hlater, hstate, hsigma,
      hempty, hlower, hminimal⟩
  · have hno : ∀ b : Fin (p.T - s), k.val < b.val → b.val ≤ n.val →
        ReferenceCollectionPhaseHistory.laterChosen (R b).input = false := by
      intro b hkb hbn
      cases hb : ReferenceCollectionPhaseHistory.laterChosen (R b).input with
      | false => rfl
      | true => exact False.elim (hex ⟨b, hkb, hbn, hb⟩)
    have hincoming := generated_retained_until rate rewards C_star C_h s hs x n now hnow
      k old hold n hkn le_rfl (fun b hkb hbn => hno b hkb (by omega))
    have hselected := selected_retains_without_later (R n) now hnow
      (generated_input_ne_first rate rewards C_star C_h s hs x n (by omega)) (hno n hkn le_rfl)
    exact Or.inl (Option.some.inj (hincoming.symm.trans hselected))

end Generated

end Bandits.Support.ReferenceGeneratedSelectedAssignmentOrder

end
