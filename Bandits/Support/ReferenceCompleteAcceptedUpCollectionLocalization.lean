/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteFollowerTerminalUpNumericalReplay
public import Bandits.Support.ReferenceCollectionUpReplayHistory
public import Bandits.Support.ReferenceCompleteCoordinatorPhaseExhaustion

import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# Localization of an actual accepted UP to its cutoff collection

The records, dispatch, initializer and calendar labels below belong to the
original complete suffix. Source evidence: ZIP4 04:157-168;
06:40-100,192-233,246-299,329-348; Appendix A:28-64.
This is an internal execution localization, without a queue-truth or regret claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCompleteAcceptedUpCollectionLocalization

open Bandits.Support
open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open ReferenceAssignmentPayloadPersistence

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_adjacent
    (records : List (RoundRecord (p := p) (rate := rate))) (initial terminal : ReferenceActivePhysicalStep.State p rate)
    (h : Connected initial records terminal) (n : ℕ) (hn : n + 1 < records.length) :
    records[n + 1].input.state = (records[n]'(by omega)).output.next := by
  induction records generalizing initial n with
  | nil => simp at hn
  | cons r rest ih =>
      rcases h with ⟨_, hrest⟩
      cases n with
      | zero =>
          cases rest with
          | nil => simp at hn
          | cons next tail => exact hrest.1
      | succ n =>
          exact ih r.output.next hrest n (by simpa using hn)

private theorem complete_clock
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected
      r.input.time.val r.input.state ∧
    ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected
      (r.input.time.val + 1) r.output.next := by
  classical
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate source rewards C_star C_h hl).2.1
      have hk := k.isLt
      have hlen := congrArg List.length hnil
      simp only [List.length_nil] at hlen
      omega
  | some active =>
      have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).mp (by rw [hl]; rfl)
      obtain ⟨first, hfirstLaunch, hfirst, _⟩ :=
        ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
          rate source rewards C_star C_h hc
      have heq : first = active := Option.some.inj (hfirstLaunch.symm.trans hl)
      subst first
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hl
      have hseed : ReferenceCoordinatorClockDomains.clockAt source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          active := by
        simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hclock := ReferenceRunClockPreservation.run_clockAt active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h; omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h active hl) hseed
      have hmem := List.getElem_mem k.isLt
      let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]
      change r ∈ _ at hmem
      have hmemRun : r ∈ _ := Eq.mp
        (congrArg (fun records => r ∈ records) hrecords) hmem
      obtain ⟨hin, hout, hrows, hselected, _⟩ := hclock.2.2.2 _ hmemRun
      dsimp only
      rw [hrows, hselected]
      exact ⟨hin, hout⟩

private theorem live_tail_not_collection
    {x : RoundInput p rate} (prepared : PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool)) :
    (livePostChoice prepared r q base started).configuration ≠ .collection P l saved := by
  unfold livePostChoice
  split
  · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
  · split
    · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
    · split
      · simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]
      · split <;> simp only [coordinatorFailure, ne_eq, reduceCtorEq, not_false_eq_true]

private theorem choice_of_collection_output (r : RoundRecord (p := p) (rate := rate))
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hout : r.output.next.coordinator = .collection P l saved) :
    ∃ c : Choice rate, choice r.input = some c := by
  classical
  let x := r.input
  have h : (prepare x).observeCoordinator.configuration = .collection P l saved := by
    rw [r.output_eq] at hout
    exact hout
  have hsel : (prepare x).coordinator.selection ≠ none := by
    intro hn
    simp only [PreparedRound.observeCoordinator, dite_eq_left hn,
      coordinatorFailure] at h
    cases hh : (prepare x).coordinator <;> simp only [hh, reduceCtorEq] at h
  unfold choice
  rw [ite_eq_right hsel]
  cases hd : (prepare x).coordinator with
  | first outcome =>
      cases outcome <;>
        simp only [PreparedRound.observeCoordinator, hd, dite_eq_right hsel,
          coordinatorFailure, reduceCtorEq] at h
      exact (live_tail_not_collection _ _ _ _ _ P l saved h).elim
  | live a q base outcome =>
      cases outcome <;>
        simp only [PreparedRound.observeCoordinator, hd, dite_eq_right hsel,
          coordinatorFailure, reduceCtorEq] at h
      · exact ⟨_, rfl⟩
      · exact (live_tail_not_collection _ _ _ _ _ P l saved h).elim
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;>
        simp only [PreparedRound.observeCoordinator, hd, dite_eq_right hsel,
          coordinatorFailure, reduceCtorEq] at h
      · exact ⟨_, rfl⟩
      · exact (live_tail_not_collection _ _ _ _ _ P l saved h).elim
  | invalidCollectionCutoff =>
      simp only [PreparedRound.observeCoordinator, hd, dite_eq_right hsel,
        coordinatorFailure, reduceCtorEq] at h
  | dagger =>
      simp only [PreparedRound.observeCoordinator, hd, DispatchCut.selection,
        ↓reduceDIte, reduceCtorEq] at h

private theorem choice_next_collection
    (r : RoundRecord (p := p) (rate := rate)) (c : Choice rate) (hc : choice r.input = some c)
    (hnot : r.output.next.coordinator ≠ .dagger) :
    ∃ P l saved, r.output.next.coordinator = .collection P l saved := by
  have htail := choice_tail r.input c hc
  have hout : r.output.next.coordinator =
      (collectionPostChoice (prepare r.input) c.payload c.preLedger c.started c.weights).configuration := by
    rw [r.output_eq]
    exact congrArg CoordinatorObservation.configuration htail
  rw [hout] at hnot ⊢
  unfold collectionPostChoice at hnot ⊢
  cases hr : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare r.input) c.payload c.started c.weights) with
  | none =>
      simp only [hr, coordinatorFailure] at hnot
      exact (hnot rfl).elim
  | some recording =>
      simp only [hr] at hnot
      cases hs : CoordinatorCollectionLedger.startRound c.preLedger (r.input.time.val + 1)
          (collectionEnabled c.preLedger r.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp only [hs, coordinatorFailure] at hnot; exact (hnot rfl).elim
      | rejected bad => simp only [hs, coordinatorFailure] at hnot; exact (hnot rfl).elim
      | success started =>
          simp only [hs] at hnot ⊢
          unfold collectionFinish at hnot ⊢
          cases hu : (receiveUp (prepare r.input) started).result with
          | invalid => simp only [hu, coordinatorFailure] at hnot; exact (hnot rfl).elim
          | success pair | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              simp only [hu] at hnot ⊢
              cases hf : CoordinatorCollectionLedger.finishRound decoded with
              | invalid => simp only [hf, coordinatorFailure] at hnot; exact (hnot rfl).elim
              | rejected bad => simp only [hf, coordinatorFailure] at hnot; exact (hnot rfl).elim
              | success finished =>
                  simp only [hf] at hnot ⊢
                  cases hk : CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time
                      c.started.clock finished.pending r.input.row with
                  | error reason =>
                      simp only [hk, coordinatorFailure] at hnot
                      exact (hnot rfl).elim
                  | ok clock => exact ⟨c.payload, finished, clock.clock.lastProposal, rfl⟩

private theorem live_choice_initializer
    (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (c : Choice rate)
    (hstate : x.state.coordinator = .live r q base)
    (hc : choice x = some c) :
    c.payload = r.payload ∧
      c.initializer = some (cutoffInitializer (liveRegistersAt r x.time)
        (liveOwnedAt r q x.time) base x.time) ∧
      ReferenceCollectionPhaseHistory.cutoffChosen x = true ∧
      (prepare x).coordinator = .live r q base
        (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
  have hprep : (prepare x).coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
    simp only [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  unfold choice at hc
  split at hc
  · contradiction
  next =>
    rw [hprep] at hc
    cases hd : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) <;>
      simp only [hd, choiceOfCut, reduceCtorEq] at hc
    next =>
      cases Option.some.inj hc
      refine ⟨rfl, rfl, ?_, by simpa only [hd] using hprep⟩
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hprep, hd]

private theorem accepted_extracted_selectors
    (r : RoundRecord (p := p) (rate := rate)) (c : Choice rate)
    (hc : choice r.input = some c)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp r.input i U)
    (done : CompletedRound rate) (hdone : extractRound r = some done) :
    done.context = c ∧ done.accepted = true ∧
      done.input.parsed = some U ∧ done.input.selectedFollower = i := by
  classical
  obtain ⟨tail, recording, started, decoded, bank, htail, hrec, hstart,
    hreceive, hparse, hsender⟩ := hacc
  have hcontext : done.context = c := Option.some.inj
    ((actual_collection_round_checked r done hdone).1.symm.trans hc)
  have htailFields : tail.payload = c.payload ∧ tail.ledger = c.preLedger ∧
      tail.started = c.started ∧ HEq tail.weights c.weights := by
    unfold choice at hc
    unfold ReferenceCollectionPhaseHistory.executedTail at htail
    split at hc
    · contradiction
    next hn =>
      simp only [ite_eq_right hn] at htail
      cases hcut : (prepare r.input).coordinator with
      | first outcome => cases outcome <;> simp [hcut, choiceOfCut] at hc
      | live a q base outcome =>
          cases outcome <;> simp only [hcut, choiceOfCut, reduceCtorEq] at hc
          next =>
            cases Option.some.inj hc
            simp only [hcut] at htail
            cases Option.some.inj htail
            exact ⟨rfl, rfl, rfl, HEq.rfl⟩
      | collection P l clock cutoff outcome =>
          cases outcome <;> simp only [hcut, choiceOfCut, reduceCtorEq] at hc
          next =>
            cases Option.some.inj hc
            simp only [hcut] at htail
            cases Option.some.inj htail
            exact ⟨rfl, rfl, rfl, HEq.rfl⟩
      | invalidCollectionCutoff => simp only [hcut, choiceOfCut, reduceCtorEq] at hc
      | dagger => simp only [hcut, choiceOfCut, reduceCtorEq] at hc
  obtain ⟨hp, hl, hs, hw⟩ := htailFields
  have hrec' : CoordinatorRecorderComplementBridge.run
      (collectionRecordingInput (prepare r.input) c.payload c.started c.weights) =
        some recording := by
    cases tail
    dsimp only at hp hl hs hw
    cases hp
    cases hs
    cases hw
    exact hrec
  have hstart' : CoordinatorCollectionLedger.startRound c.preLedger
      (r.input.time.val + 1) (collectionEnabled c.preLedger r.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
        .success started := by simpa only [hl] using hstart
  obtain ⟨recording', started', decoded', bank', hrecord', hactualRec, hactualStart,
    hinput, hactualReceive, _⟩ := actual_collection_round_inputs r done hdone
  rw [hcontext] at hactualRec hactualStart hinput
  have hr : recording' = recording := Option.some.inj (hactualRec.symm.trans hrec')
  subst recording'
  have ht : started' = started := by
    rw [hstart'] at hactualStart
    exact (CoordinatorCollectionLedger.Checked.success.inj hactualStart).symm
  subst started'
  have haccepted : done.accepted = true := by
    cases ha : done.accepted
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hactualReceive
      rw [hreceive] at hactualReceive
      contradiction
    · rfl
  refine ⟨hcontext, haccepted, ?_, ?_⟩
  · rw [hinput]
    exact hparse
  · rw [hinput]
    exact hsender.symm

private theorem takeWhile_prefix {α : Type} (xs : List α) (test : α → Bool)
    (n : ℕ) (hn : n ≤ xs.length)
    (hall : ∀ j, (hj : j < n) → test (xs[j]'(by omega)) = true) :
    n ≤ (xs.takeWhile test).length ∧
      (xs.takeWhile test).take n = xs.take n := by
  have ht : (xs.take n).takeWhile test = xs.take n := by
    apply List.takeWhile_eq_self_iff.mpr
    intro a ha
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp ha
    have hjn : j < n := by simpa only [List.length_take, Nat.min_eq_left hn] using hj
    have hget : (xs.take n)[j] = xs[j]'(by omega) := by simp only [List.getElem_take]
    rw [← heq, hget]
    exact hall j hjn
  have heq : (xs.takeWhile test).take n = xs.take n := by
    rw [List.take_takeWhile, ht]
  have hlen := congrArg List.length heq
  simp only [List.length_take, Nat.min_eq_left hn] at hlen
  exact ⟨by omega, heq⟩

private theorem complete_live_before_cutoff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .live r q base) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.time.val <
      FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) := by
  have h := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  dsimp only at h
  rw [hstate] at h
  exact h.2

private theorem complete_collection_cutoff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved) :
    l.cutoff = FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) := by
  have h := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  dsimp only at h
  rw [hstate] at h
  exact h.2.2.2

private theorem complete_retained_entry_live
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (P : Payload rate)
    (hstored : storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (htime : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.time.val + 1 =
      FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)))) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]
    ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ),
      r.input.state.coordinator = .live registers owned base ∧ registers.payload = P := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  change storedPayload r.input.state.coordinator = some P at hstored
  dsimp only
  cases hstate : r.input.state.coordinator with
  | first => simp only [hstate, storedPayload, reduceCtorEq] at hstored
  | dagger => simp only [hstate, storedPayload, reduceCtorEq] at hstored
  | live registers owned base =>
      exact ⟨registers, owned, base, rfl, by
        simpa only [hstate, storedPayload, Option.some.injEq] using hstored⟩
  | collection payload l saved =>
      have hp : payload = P := by
        simpa only [hstate, storedPayload, Option.some.injEq] using hstored
      have hclock := (complete_clock rewards C_star C_h source k).1
      change ReferenceCoordinatorClockDomains.clockAt r.input.rows r.input.selected
        r.input.time.val r.input.state at hclock
      simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
      have hcut := complete_collection_cutoff rewards C_star C_h source k payload l saved hstate
      rw [hp, ← htime] at hcut
      have hle : r.input.time.val + 1 ≤ r.input.time.val := hcut ▸ hclock.2.2.2.2.1
      exact (Nat.not_succ_le_self _ hle).elim

private theorem complete_retained_collection_after_cutoff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) (P : Payload rate)
    (hstored : storedPayload (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = some P)
    (htime : FollowerCutoffScan.firstCutoff p rate.eta.val P.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input.time.val) :
    ∃ l saved, (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input.state.coordinator = .collection P l saved := by
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]
  change storedPayload r.input.state.coordinator = some P at hstored
  change ∃ l saved, r.input.state.coordinator = .collection P l saved
  cases hstate : r.input.state.coordinator with
  | first => simp only [hstate, storedPayload, reduceCtorEq] at hstored
  | dagger => simp only [hstate, storedPayload, reduceCtorEq] at hstored
  | live registers owned base =>
      have hp : registers.payload = P := by
        simpa only [hstate, storedPayload, Option.some.injEq] using hstored
      have hlt := complete_live_before_cutoff rewards C_star C_h source k
        registers owned base hstate
      rw [hp] at hlt
      exact (not_lt_of_ge htime hlt).elim
  | collection payload l saved =>
      have hp : payload = P := by
        simpa only [hstate, storedPayload, Option.some.injEq] using hstored
      exact ⟨l, saved, by rw [hp]⟩

private theorem complete_adjacent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (n : ℕ) (hn : n + 1 < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    R[n + 1].input.state = (R[n]'(Nat.lt_trans (Nat.lt_succ_self n) hn)).output.next := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hnil := (ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate source rewards C_star C_h hl).2.1
      have hlen := congrArg List.length hnil
      simp only [List.length_nil] at hlen
      omega
  | some initial =>
      exact connected_adjacent _ initial _
        (ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate source rewards C_star C_h initial hl) n hn

private theorem collection_continuing
    (r : RoundRecord (p := p) (rate := rate))
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection P l saved)
    (Pout : Payload rate) (lout : Ledger rate) (savedout : Option (Fin p.T × Bool))
    (hout : r.output.next.coordinator = .collection Pout lout savedout) :
    continuing r = true := by
  obtain ⟨c, hc⟩ := choice_of_collection_output r Pout lout savedout hout
  obtain ⟨done, hdone⟩ := actual_collection_round_complete r c Pout lout savedout hc hout
  have hccontext := (actual_collection_round_checked r done hdone).1
  have hnone := (choice_collection_pre r.input P l saved done.context hstate hccontext).2
  simp only [continuing, hdone, hnone, Option.isNone_none]

private theorem segment_prefix
    (R : List (RoundRecord (p := p) (rate := rate))) (o k : ℕ)
    (hok : o ≤ k) (hk : k < R.length) (ho : o < R.length)
    (c0 : Choice rate) (I : Initializer p)
    (hc0 : choice R[o].input = some c0) (hI : c0.initializer = some I)
    (hentry : (extractRound R[o]).isSome = true)
    (hall : ∀ a : Fin R.length, o < a.val → a.val ≤ k → continuing R[a.val] = true) :
    ∃ seg : Segment rate,
      k - o < seg.records.length ∧ segmentAt R o = some seg ∧
      seg.entry = R[o] ∧ seg.context = c0 ∧
      (∀ hn : k - o < seg.records.length, seg.records[k - o]'hn = R[k]) ∧
      seg.records.take (k - o + 1) = (R.drop o).take (k - o + 1) := by
  classical
  let n := k - o
  let rest := R.drop (o + 1)
  let seg : Segment rate := ⟨R[o], c0, R[o] :: rest.takeWhile continuing,
    rest.dropWhile continuing⟩
  have hdrop : R.drop o = R[o] :: rest := List.drop_eq_getElem_cons ho
  have hsegment : segmentAt R o = some seg := by
    simp only [segmentAt, hdrop, ReferenceCollectionSegmentExtraction.segment, hc0, Option.map_some,
      hentry, ↓reduceIte, Option.bind_some]
    change (if o = 0 ∨ c0.initializer.isSome = true then some seg else none) = some seg
    exact ite_eq_left (Or.inr (by simp only [hI, Option.isSome_some]))
  have hnRest : n ≤ rest.length := by
    dsimp only [rest, n]
    simp only [List.length_drop]
    omega
  have hprefix := takeWhile_prefix rest continuing n hnRest (by
    intro j hj
    have hbound : o + 1 + j < R.length := by dsimp only [n] at hj; omega
    have hget : rest[j]'(by omega) = R[o + 1 + j] := by
      simp only [rest, List.getElem_drop]
    rw [hget]
    exact hall ⟨o + 1 + j, hbound⟩ (by change o < o + 1 + j; omega)
      (by change o + 1 + j ≤ k; dsimp only [n] at hj; omega))
  have hn : n < seg.records.length := by
    change n < (R[o] :: rest.takeWhile continuing).length
    simp only [List.length_cons]
    omega
  have hprefixEq : seg.records.take (n + 1) = (R.drop o).take (n + 1) := by
    change (R[o] :: rest.takeWhile continuing).take (n + 1) = _
    rw [hdrop]
    simp only [List.take_succ_cons, hprefix.2]
  have hrecord : seg.records[n] = R[k] := by
    have hget := congrArg (fun xs : List (RoundRecord (p := p) (rate := rate)) => xs[n]?) hprefixEq
    have hdropBound : n < (R.drop o).length := by
      simp only [List.length_drop]
      dsimp only [n]
      omega
    simp only [List.getElem?_take, show n < n + 1 by omega, ↓reduceIte,
      List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hdropBound] at hget
    have heq : o + n = k := by dsimp only [n]; omega
    simpa only [List.getElem_drop, heq] using Option.some.inj hget
  exact ⟨seg, hn, hsegment, rfl, rfl, fun _ => hrecord, hprefixEq⟩

private theorem prefix_calendar
    (R : List (RoundRecord (p := p) (rate := rate))) (s o count : ℕ)
    (hbound : o + count ≤ R.length)
    (htimes : ∀ a : Fin R.length, R[a.val].input.time.val = s + a.val) :
    ((R.drop o).take count).map (fun r => r.input.time.val + 1) =
      List.range' (s + o + 1) count := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_drop, List.length_range']
    omega
  · intro j hj hj'
    have hjn : j < count := by simpa only [List.length_range'] using hj'
    have hindex : o + j < R.length := by omega
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range']
    have ht := htimes ⟨o + j, hindex⟩
    dsimp only at ht
    omega

private theorem offset_geometry (s b k stamp u : ℕ)
    (hstamp : stamp = s + b) (hcut : stamp + 1 < u)
    (hupper : u ≤ s + k + 1) :
    b < u - (s + 1) ∧ u - (s + 1) ≤ k ∧ s + (u - (s + 1)) + 1 = u := by
  omega

private theorem time_after_offset (s o u a : ℕ)
    (hstart : s + o + 1 = u) (hoa : o < a) : u ≤ s + a := by
  omega

private theorem accepted_cutoff_geometry
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U)
    (c : Choice rate) (hc : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val].input = some c) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma bits
    let o := u - (s + 1)
    o ≤ k.val ∧ o < R.length ∧ s + o + 1 = u ∧
      ∃ b : Fin R.length, b.val < o ∧
        ∀ a : Fin R.length, b.val < a.val → a.val ≤ k.val →
          storedPayload R[a.val].input.state.coordinator = some c.payload := by
  classical
  intro R s bits u o
  obtain ⟨c', b, j, F, mu, hc', hbj, hjk, hbirth, hretained, hinput,
    hdown, hUsigma, hS, hdelta, hq, hledgerSigma, hcutoff, hbase, hbetween, hselected⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_selected_payload_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  have heq : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  clear hbj hjk hretained hinput hdown hUsigma hS hdelta hq hledgerSigma hcutoff
    hbase hselected j F mu
  obtain ⟨c', b', j', hc', hbj', hjk', hbirth', hretained', hbase',
    hpositive, hule, htimes, hcells⟩ :=
    ReferenceCompleteFollowerRetainedDownRecovery.complete_accepted_up_live_calendar_interval
      (rate := rate) rewards C_star C_h source k i U hacc
  have heq : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  clear hbj' hjk' hbirth' hretained' hbase' hpositive htimes hcells b' j'
  have hbtime := ReferenceAssignmentPayloadChronology.installationBirth_time_eq
    R[b.val] c.payload hbirth
  have hbclock := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source b
  have hkclock := ReferenceAssignmentFollowerMassSteps.complete_record_time
    rate rewards C_star C_h source k
  have hbounds := FollowerCutoffScan.firstCutoff_bounds p rate.eta.val
    rate.eta.property rate.sourceCap c.payload.sigma bits
  change u ≤ R[k.val].input.time.val + 1 at hule
  change R[b.val].input.time.val = s + b.val at hbclock
  change R[k.val].input.time.val = s + k.val at hkclock
  change c.payload.sigma.val = R[b.val].input.time.val at hbtime
  have hupper : u ≤ s + k.val + 1 := by
    rw [← hkclock]
    exact hule
  have hgeom := offset_geometry s b.val k.val c.payload.sigma.val u
    (hbtime.trans hbclock) hbounds.1 hupper
  have hbo : b.val < o := hgeom.1
  have hok : o ≤ k.val := hgeom.2.1
  have hstart : s + o + 1 = u := hgeom.2.2
  have ho : o < R.length := lt_of_le_of_lt hok k.isLt
  exact ⟨hok, ho, hstart, b, hbo, hbetween⟩

/-- An actual accepted UP belongs to the collection initialized at its own
first cutoff. The choice is universally quantified in the conclusion so a
consumer can retain its already selected terminal-reply witness. -/
theorem complete_accepted_up_collection_localization
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (i : Fin (p.m - 1)) (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hacc : ReferenceCollectionPhaseHistory.AcceptedUp
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input i U) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))
    ∀ c : Choice rate, choice (R[k.val]'k.isLt).input = some c →
    let sigma := c.payload.sigma.val + 1
    let u := FollowerCutoffScan.firstCutoff p rate.eta.val c.payload.sigma bits
    let o := u - (s + 1)
    let n := k.val - o
    ∃ (seg : Segment rate) (done : CompletedRound rate)
      (c0 : Choice rate) (I : Initializer p),
      o ≤ k.val ∧ o < R.length ∧ n < seg.records.length ∧
      segmentAt R o = some seg ∧
      (∀ ho : o < R.length, seg.entry = R[o]'ho) ∧ seg.context = c0 ∧
      choice seg.entry.input = some c0 ∧ c0.payload = c.payload ∧
      c0.initializer = some I ∧ I.checkedStart rate = .success seg.context.preLedger ∧
      I.sigma = sigma ∧ I.cutoff = u ∧ seg.entry.input.time.val + 1 = u ∧
      (∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ),
        seg.entry.input.state.coordinator = .live registers owned base ∧
        I = cutoffInitializer (liveRegistersAt registers seg.entry.input.time)
          (liveOwnedAt registers owned seg.entry.input.time) base seg.entry.input.time ∧
        (prepare seg.entry.input).coordinator = .live registers owned base
          (CoordinatorRoundDispatch.dispatchLive (liveInput seg.entry.input registers owned base)) ∧
        ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true) ∧
      (∀ hn : n < seg.records.length, seg.records[n]'hn = (R[k.val]'k.isLt)) ∧ extractRound (R[k.val]'k.isLt) = some done ∧
      done.context = c ∧ done.accepted = true ∧ done.input.parsed = some U ∧
      done.input.selectedFollower = i ∧
      seg.records.take (n + 1) = (R.drop o).take (n + 1) ∧
      (seg.records.take (n + 1)).map (fun r => r.input.time.val + 1) =
        List.range' u (n + 1) ∧
      seg.records ++ seg.remaining = R.drop o ∧ seg.exit = exitOf seg.remaining := by
  classical
  intro R s bits c hc sigma u o n
  obtain ⟨hok, ho, hstart, b, hbo, hbetween⟩ :=
    accepted_cutoff_geometry rewards C_star C_h source k i U hacc c hc
  let startIndex : Fin R.length := ⟨o, ho⟩
  have hotime : R[o].input.time.val + 1 = u := by
    have ht := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h source startIndex
    change R[o].input.time.val = s + o at ht
    rw [ht]
    exact hstart
  have hstored0 := hbetween startIndex hbo hok
  have hentryLive := complete_retained_entry_live rewards C_star C_h source startIndex
    c.payload hstored0 hotime
  have hcollectionInput (a : Fin R.length) (hoa : o < a.val) (hak : a.val ≤ k.val) :
      ∃ l saved, R[a.val].input.state.coordinator = .collection c.payload l saved := by
    have hstored := hbetween a (hbo.trans hoa) hak
    have htime := ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h source a
    change R[a.val].input.time.val = s + a.val at htime
    have hge := time_after_offset s o u a.val hstart hoa
    have hafter : u ≤ R[a.val].input.time.val := by rw [htime]; exact hge
    exact complete_retained_collection_after_cutoff rewards C_star C_h source a
      c.payload hstored hafter
  have hnext (a : Fin R.length) (hoa : o ≤ a.val) (hak : a.val ≤ k.val) :
      ∃ P l saved, R[a.val].output.next.coordinator = .collection P l saved := by
    by_cases heq : a.val = k.val
    · have ha : a = k := Fin.ext heq
      subst a
      have hphase := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
        rate rewards C_star C_h source).1 k
      exact choice_next_collection R[k.val] c hc hphase.2.2.2.2
    · have haklt : a.val < k.val := lt_of_le_of_ne hak heq
      have hnextBound : a.val + 1 < R.length :=
        lt_of_le_of_lt (Nat.succ_le_of_lt haklt) k.isLt
      let nextIndex : Fin R.length := ⟨a.val + 1, hnextBound⟩
      obtain ⟨l, saved, hstate⟩ := hcollectionInput nextIndex
        (lt_of_le_of_lt hoa (Nat.lt_succ_self a.val)) (Nat.succ_le_of_lt haklt)
      have hadj := complete_adjacent rewards C_star C_h source a.val hnextBound
      exact ⟨c.payload, l, saved, by rw [← hadj]; exact hstate⟩
  obtain ⟨registers, owned, base, hstate0, hpayload0⟩ := hentryLive
  obtain ⟨Pout, lout, savedout, hout0⟩ := hnext startIndex le_rfl hok
  obtain ⟨c0, hc0⟩ := choice_of_collection_output R[o] Pout lout savedout hout0
  obtain ⟨hpayload, hinit, hcutoffTag, hprepare⟩ :=
    live_choice_initializer R[o].input registers owned base c0 hstate0 hc0
  let I := cutoffInitializer (liveRegistersAt registers R[o].input.time)
    (liveOwnedAt registers owned R[o].input.time) base R[o].input.time
  have hI : c0.initializer = some I := hinit
  obtain ⟨entryDone, hentryDone⟩ := actual_collection_round_complete
    R[o] c0 Pout lout savedout hc0 hout0
  have hcontinuing (a : Fin R.length) (hoa : o < a.val) (hak : a.val ≤ k.val) :
      continuing R[a.val] = true := by
    obtain ⟨l, saved, hstate⟩ := hcollectionInput a hoa hak
    obtain ⟨Pout, lout, savedout, hout⟩ := hnext a hoa.le hak
    exact collection_continuing R[a.val] c.payload l saved hstate Pout lout savedout hout
  obtain ⟨seg, hn, hsegment, hentry, hsegContext, hrecord, hprefixEq⟩ :=
    segment_prefix R o k.val hok k.isLt ho c0 I hc0 hI
      (by rw [hentryDone]; rfl) hcontinuing
  obtain ⟨Pk, lk, savedk, houtk⟩ := hnext k hok le_rfl
  obtain ⟨done, hdone⟩ := actual_collection_round_complete R[k.val] c Pk lk savedk hc houtk
  obtain ⟨hcontext, haccepted, hparsed, hselected⟩ :=
    accepted_extracted_selectors R[k.val] c hc i U hacc done hdone
  have hcountBound : o + (n + 1) ≤ R.length := by
    have heq : o + n = k.val := Nat.add_sub_of_le hok
    calc
      o + (n + 1) = k.val + 1 := by rw [← Nat.add_assoc, heq]
      _ ≤ R.length := k.isLt
  have hlabels := prefix_calendar R s o (n + 1) hcountBound
    (fun a => ReferenceAssignmentFollowerMassSteps.complete_record_time
      rate rewards C_star C_h source a)
  rw [hstart] at hlabels
  refine ⟨seg, done, c0, I, hok, ho, hn, hsegment, (fun _ => hentry), hsegContext,
    (by rw [hentry]; exact hc0),
    hpayload.trans hpayload0, hI, ?_,
    ?_, ?_, (by rw [hentry]; exact hotime), ?_, hrecord, hdone, hcontext, haccepted, hparsed,
    hselected, hprefixEq, ?_, segmentAt_partition R o seg hsegment, rfl⟩
  · rw [hsegContext]
    exact choice_initializer R[o].input c0 I hc0 hI
  · change registers.payload.sigma.val + 1 = c.payload.sigma.val + 1
    rw [hpayload0]
  · exact hotime
  · rw [hentry]
    exact ⟨registers, owned, base, hstate0, rfl, hprepare, hcutoffTag⟩
  · rw [hprefixEq]
    exact hlabels

end Bandits.Support.ReferenceCompleteAcceptedUpCollectionLocalization

end
