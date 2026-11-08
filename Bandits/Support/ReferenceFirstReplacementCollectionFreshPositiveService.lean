/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionFreshFollowerGeometry
public import Bandits.Support.ReferenceFirstReplacementCollectionCommonStopObservation
public import Bandits.Support.ReferenceCompleteCoordinatorDiagnosticSupport

/-!
# Fresh controls in the first replacement collection

Sources: `sources/zip4/manuscript/05_binary_transport.tex:70-125,180-240`,
`sources/zip4/manuscript/06_interruptions.tex:110-190,246-349,425-431,459-487`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

These are internal deterministic source-control identities. The strict-past
flag does not inspect the current round, including a first detecting round.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCollectionFreshPositiveService

open ConstructorDimensions ReferenceActivePhysicalStep PublicDiscreteDraws

variable {p : ConstructorDimensions.Parameters}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- Changing the selected row's current whole control preserves the literal
strict prefix, including all private arrays and all other rows. -/
theorem sourcePrefix_replaceSourceControl
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (h : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z
    · subst q
      simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      congr 1
      funext v
      by_cases hv : v.val < t.val
      · have hne : v ≠ t := by intro heq; subst v; omega
        simp [hv, Function.update_of_ne hne]
      · simp [hv]
    · simp [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ActualInitializationPhysicalStep.selectedRowIndex,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex] at hq ⊢
      simp [Function.update_of_ne hq]
  · rfl

/-- The same strict-past stop flag is retained under every current control.
There is no condition on the current row's failure diagnostic. -/
theorem L_replaceSourceControl
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (s u : ℕ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (h : ContinuousLearningRows.TimeControl p) :
    ReferenceFirstReplacementCollectionCommonStopObservation.L
        rate rewards C_star C_h control0 s u i t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h) =
      ReferenceFirstReplacementCollectionCommonStopObservation.L
        rate rewards C_star C_h control0 s u i t.val z := by
  rw [ReferenceFirstReplacementCollectionCommonStopObservation.L_factor
    rate rewards C_star C_h control0 s u t.val i,
    sourcePrefix_replaceSourceControl,
    ← ReferenceFirstReplacementCollectionCommonStopObservation.L_factor]

/-- A complete-suffix member is the actual record at its own physical time. -/
theorem actualRecord_of_mem
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h r.input.time z = some r := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have htime := congrArg (fun times : List ℕ => times[k]?) htimes
  rw [List.getElem?_map, List.getElem?_eq_getElem hk] at htime
  have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  have hk' : k < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by omega
  simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hk',
    Nat.one_mul, Option.map_some] at htime
  have ht : r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k := by
    rw [heq] at htime
    exact Option.some.inj htime
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left (by omega), show r.input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k by omega,
    List.getElem?_eq_getElem hk, heq]

private theorem complete_record_selection
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) :
    r.input.state.coordinator ≠ .dagger ∧
      (∃ v : Selection r.input, r.output.preparation.coordinator.selection = some v) ∧
      r.output.next.coordinator ≠ .dagger := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
  have h := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 ⟨k, hk⟩
  dsimp only at h
  rw [heq] at h
  refine ⟨h.1, ?_, h.2.2.2.2⟩
  cases hs : r.output.preparation.coordinator.selection with
  | none => exact (h.2.1 hs).elim
  | some v => exact ⟨v, rfl⟩

private theorem continuing_selection_fields
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (P : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool))
    (cutTime : Fin p.T)
    (hc : r.input.state.coordinator = .collection P ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false)
    (hcut : ledger.cutoff = cutTime.val + 1)
    (v : Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some v) :
    v.view.payload = P ∧ v.view.pendingAtChoice = ledger.pending ∧
      v.view.cutoff = some (CoordinatorCollectionUpRoundStep.localCutoff cutTime) := by
  classical
  have hfields := ReferenceFirstReplacementCollectionOldDownSenderReadiness.collection_selection_pending
    r P ledger saved hc hn v hs
  refine ⟨hfields.1, hfields.2, ?_⟩
  have hp : r.output.preparation.coordinator = dispatch r.input := by
    rw [r.output_eq]
    rfl
  rw [hp] at hs
  have hv : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    have := cutTime.isLt
    omega
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have htime : cutoff = cutTime := Fin.ext (by dsimp [cutoff]; omega)
  let clock := collectionClock P ledger saved cutoff
  let x := collectionInput r.input P ledger clock cutoff
  have hd : dispatch r.input =
      .collection P ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection x) := by
    simp only [dispatch, hc, dite_eq_left hv, CoordinatorRoundDispatch.dispatch]
    rfl
  rw [hd] at hs
  cases ho : CoordinatorRoundDispatch.dispatchCollection x with
  | continuing core prepared boundary scores =>
    rw [ho] at hs
    have he := Option.some.inj hs
    have hview := congrArg (fun s : Selection r.input => s.view.cutoff) he.symm
    change v.view.cutoff =
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p prepared.clockStarted.clock.u at hview
    rw [hview, prepared.clockStarted_frame.1]
    change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clock.u = _
    have hu : clock.u = some cutoff := prepared.inputsValid.clock_cutoff_eq
    rw [hu, htime]
    rfl
  | laterChosen core consistent started startEq instruction instructionEq output
      localEq clockData installed chosen =>
    have htrue : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
      simp only [ReferenceCollectionPhaseHistory.laterChosen, prepare, hd, ho]
    exact Bool.noConfusion (hn.symm.trans htrue)
  | _ => simp [ho, DispatchCut.selection] at hs

/-- Every actual row in the cutoff-inclusive physical collection has its
original whole payload and current cutoff at CHOICE. The view is constructed,
with its actual pending set; no survival or matching-view input is assumed. -/
theorem complete_first_replacement_collection_choice_views
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let _s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let _J := ActualInitializationPhysicalStep.selectedRowIndex p z
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let P := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            ∀ a : Fin K.length,
              let r := K.get a
              ∃ v0 : Selection r.input,
                r.output.preparation.coordinator.selection = some v0 ∧
                v0.view.payload = P ∧
                v0.view.cutoff = some
                  (CoordinatorCollectionUpRoundStep.localCutoff cut.input.time)
          | _ => True
      | _ => True := by
  classical
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  have hR := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h
  have hP := ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
    rate z rewards C_star C_h
  dsimp only at hB hR hP ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hB hR hP ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hB hR hP ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [collectionInput] at hB hR hP ⊢
      rcases hR with ⟨_, _, hR⟩
      rcases hP with ⟨_, _, hP⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hB hR hP ⊢
        rcases hB with ⟨_, hB⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hB hR hP ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hB hR hP ⊢
          let P := installed.registers.payload
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, vcut, hvcut, hpaycut,
            _, hcutcut, _⟩
          rcases hR with ⟨hendpoints, _, _⟩
          rcases hP with ⟨_, hZ, _⟩
          intro ⟨a, ha⟩
          cases a with
          | zero =>
            refine ⟨vcut, ?_, hpaycut, hcutcut⟩
            change cut.output.preparation.coordinator.selection = some vcut
            rw [hcut]
            exact hvcut
          | succ a =>
            have haW : a < W.length := Nat.lt_of_succ_lt_succ ha
            let j : Fin W.length := ⟨a, haW⟩
            let r := W.get j
            have hlookup : R[c + 1 + a]? = some r :=
              ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get R c a haW
            have hmem : r ∈ R := List.mem_of_getElem? hlookup
            obtain ⟨hnonD, ⟨v0, hv0⟩, _⟩ :=
              complete_record_selection rate z rewards C_star C_h r hmem
            have hinput : r.input.state = E a := by
              have h := (hZ.2.2 ⟨a + 1, ha⟩).1
              change r.input.state = Z (a + 1) at h
              exact h.trans (hZ.2.1 a (Nat.le_of_lt haW))
            rcases hendpoints a (Nat.le_of_lt haW) with hd | ⟨l, saved, hstate, _, hcutoff, _⟩
            · exact (hnonD (congrArg (fun s => s.coordinator) hinput |>.trans hd)).elim
            · have hstate' : r.input.state.coordinator = .collection P l saved :=
                (congrArg (fun s => s.coordinator) hinput).trans hstate
              have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                have hmemW : r ∈ W := List.get_mem W j
                have hp := List.all_eq_true.mp (List.all_takeWhile
                  (l := R.drop (c + 1))
                  (p := fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)) r hmemW
                cases ht : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                  simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true]
              have hfields := continuing_selection_fields r P l saved cut.input.time
                hstate' hn hcutoff v0 hv0
              exact ⟨v0, hv0, hfields.1, hfields.2.2⟩

private theorem startRound_frame
    {rate : RateInput p} (l started : Ledger rate) (time : Fin p.T)
    (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (hs : CoordinatorCollectionLedger.startRound l (time.val + 1) enabled raw =
      .success started) :
    started.pending = l.pending ∧ started.cutoff = l.cutoff := by
  unfold CoordinatorCollectionLedger.startRound at hs
  split at hs <;> try contradiction
  dsimp only at hs
  split at hs <;> try contradiction
  split at hs <;> try contradiction
  cases hs
  exact ⟨rfl, rfl⟩

private theorem complete_continuing_site
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hstate : r.input.state.coordinator = .collection P l saved)
    (hpending : l.pending.Nonempty) :
    ∃ u : Fin p.T, u.val + 1 = l.cutoff ∧ ∃ v : Selection r.input,
      (prepare r.input).coordinator.selection = some v ∧
      v.view.payload = P ∧ v.view.pendingAtChoice = l.pending ∧
      v.view.cutoff = some (CoordinatorCollectionUpRoundStep.localCutoff u) ∧
      ∃ started : Ledger rate,
        started.pending = l.pending ∧ started.cutoff = l.cutoff ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some started ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) = true ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input =
          decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started))) := by
  classical
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
  subst r
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h)[k]'hk |>.input
  obtain ⟨u, hu, core, scores, clockStarted, hclockStart, hframe,
      choiceInputs, snapshot, boundary, hdispatch, _, hclockStarted, _,
      c, hchoice, hc, _⟩ :=
    ReferenceCompleteContinuingCollectionChoiceDomains.complete_nonempty_continuing_collection_choice_domains
      rate rewards C_star C_h z ⟨k, hk⟩ P l saved hstate hpending
  let clock := collectionClock P l saved u
  have hstate' : x.state.coordinator = .collection P l saved := hstate
  have hrange : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by have := u.isLt; omega
  have hu' : (⟨l.cutoff - 1, by omega⟩ : Fin p.T) = u := by
    apply Fin.ext
    change l.cutoff - 1 = u.val
    omega
  have hprepare : (prepare x).coordinator =
      .collection P l clock u (.continuing core snapshot boundary scores) := by
    simp only [prepare, dispatch, hstate', dite_eq_left hrange, CoordinatorRoundDispatch.dispatch]
    rw [hu']
    exact congrArg (DispatchCut.collection P l clock u) hdispatch
  obtain ⟨o, started, decoded, bank, finished, clockFinished, hrest⟩ :=
    ReferenceCompleteContinuingCollectionReception.actual_continuing_collection_reception_finish
      rate rewards C_star C_h z ⟨k, hk⟩ P l saved hstate c hchoice
  rcases hrest with ⟨_, hpre, _, _, hrecord, _, hstart, _, _, _, _, _, _, hcheck,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hclockRest⟩
  rcases hclockRest with ⟨_, _, cutoff, _, _, _, _, _, _, _, _, hobserve, _⟩
  have hfields := startRound_frame l started x.time
    (collectionEnabled l x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) hstart
  have hsel : (prepare x).coordinator.selection ≠ none := by
    rw [hprepare]
    simp [DispatchCut.selection]
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hsel
  have hn : ReferenceCollectionPhaseHistory.laterChosen x = false := by
    simp only [ReferenceCollectionPhaseHistory.laterChosen, hprepare]
  have hvout : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k]'hk).output.preparation.coordinator.selection = some v := by
    rw [ReferenceActivePhysicalHorizon.RoundRecord.output_eq]
    exact hv
  have hview := continuing_selection_fields
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k]'hk)
    P l saved u hstate hn hu.symm v hvout
  refine ⟨u, hu, v, hv, hview.1, hview.2.1, hview.2.2,
    started, hfields.1, hfields.2, ?_, hcheck, ?_⟩
  · rw [hc] at hrecord
    change ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some started
    unfold ReferenceCoordinatorUpPhysicalCall.siteLedger?
    dsimp only
    rw [dite_eq_right hsel, hprepare]
    dsimp only
    unfold ReferenceCoordinatorUpPhysicalCall.tailLedger?
    rw [hrecord]
    dsimp only
    rw [hstart]
  · unfold ReferenceActiveAffinePositiveTest.upPositive
    rw [hobserve]
    rw [ReferenceActiveAffinePositiveTest.receiveUp_positive]
    change (CoordinatorUpReception.receptionInputCheck
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started) && _) = _
    have hcheck' : CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started) = true := hcheck
    rw [hcheck', Bool.true_and]
    rfl

private theorem live_input_of_prepare
    {rate : RateInput p} (x : RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x registers owned base))
    (hprepare : (prepare x).coordinator = .live registers owned base outcome) :
    x.state.coordinator = .live registers owned base := by
  cases hc : x.state.coordinator with
  | first =>
    simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch] at hprepare
    contradiction
  | dagger =>
    simp only [prepare, dispatch, hc] at hprepare
    contradiction
  | collection P ledger saved =>
    simp only [prepare, dispatch, hc] at hprepare
    split at hprepare <;>
      (try simp only [CoordinatorRoundDispatch.dispatch] at hprepare) <;> contradiction
  | live registers' owned' base' =>
    have hp : (prepare x).coordinator = .live registers' owned' base'
        (CoordinatorRoundDispatch.dispatchLive (liveInput x registers' owned' base')) := by
      simp only [prepare, dispatch, hc, CoordinatorRoundDispatch.dispatch]
      rfl
    have he := hp.symm.trans hprepare
    cases he
    rfl

private theorem initializing_not_continuing
    (current : CoordinatorRoundDispatch.LiveInput p)
    (initialized : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p current.eta.val current.registers.time
      current.registers.priorClock current.registers.clockPending = .ok initialized)
    (hcommand : initialized.ledgerCommand = some (.initializeAt current.registers.time))
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output current.registers
      current.ownedRegisters current.followerBaseScore)
    (hs : CoordinatorPhaseClock.startRound p current.eta.val current.registers.time
      current.registers.priorClock current.registers.clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation current.registers current.row)
    (selection : CoordinatorRoundDispatch.ArmSelection current.registers.payload
      dispatched.startResult current.registers.time current.registers.complementWeights current.row)
    (ho : CoordinatorRoundDispatch.dispatchLive current =
      .continuingChosen dispatched hs continuation selection) : False := by
  classical
  have hnotnone : ∀ output : CoordinatorStartRoundCutoffDispatch.Output current.registers
      current.ownedRegisters current.followerBaseScore,
      CoordinatorStartRoundCutoffDispatch.dispatch current.registers current.ownedRegisters
        current.followerBaseScore = .ok output →
      output.collectionInitialization ≠ .success none := by
    intro output houtput
    unfold CoordinatorStartRoundCutoffDispatch.dispatch at houtput
    rw [hstart] at houtput
    dsimp only at houtput
    rw [hcommand] at houtput
    have hout := Except.ok.inj houtput
    rw [← hout]
    dsimp only
    unfold CoordinatorStartRoundCutoffDispatch.checkedOptionIfValid
    intro hnone
    split at hnone
    · split at hnone
      · injection hnone with he
        cases he
      · contradiction
    · contradiction
    · contradiction
  unfold CoordinatorRoundDispatch.dispatchLive at ho
  dsimp only at ho
  split at ho
  · contradiction
  · rename_i actual hactual
    split at ho
    · contradiction
    · contradiction
    · rename_i hinit
      exact hnotnone actual hactual hinit
    · split at ho <;> try contradiction
      split at ho <;> try contradiction
      split at ho <;> try contradiction
      split at ho
      · rename_i hselected
        exact CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          current.registers.payload actual.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p actual.startResult.clock.u)
          current.registers.time current.registers.complementWeights current.row
          (by assumption) hselected
      · contradiction

private theorem complete_cutoff_site
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : r.input.state.coordinator = .live registers owned base)
    (initialized : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
      registers.priorClock registers.clockPending = .ok initialized)
    (hcommand : initialized.ledgerCommand = some (.initializeAt r.input.time)) :
    ∃ v : Selection r.input,
      (prepare r.input).coordinator.selection = some v ∧
      v.view.payload = registers.payload ∧ v.view.pendingAtChoice = Finset.univ ∧
      v.view.cutoff = some (CoordinatorCollectionUpRoundStep.localCutoff r.input.time) ∧
      ∃ started : Ledger rate,
        started.pending = Finset.univ ∧ started.cutoff = r.input.time.val + 1 ∧
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some started ∧
        CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) = true ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input =
          decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
            (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started))) := by
  classical
  obtain ⟨_, ⟨v0, hv0⟩, _⟩ := complete_record_selection rate z rewards C_star C_h r hr
  have hsel : (prepare r.input).coordinator.selection ≠ none := by
    have hv := hv0
    rw [r.output_eq] at hv
    change (prepare r.input).coordinator.selection = some v0 at hv
    rw [hv]
    exact Option.some_ne_none _
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
  have hpost := complete_live_cutoff_post_choice rate rewards C_star C_h z
    ⟨k, hk⟩ registers owned base (heq ▸ hstate)
  dsimp only at hpost
  rw [heq] at hpost
  let x := r.input
  rcases hpost with ⟨hprepare, hpost⟩
  cases houtcome : CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base) with
  | clockFailure failure he =>
    rw [houtcome] at hprepare
    rw [hprepare] at hsel
    exact (hsel rfl).elim
  | initializerFailure dispatched hs checked he =>
    rw [houtcome] at hprepare
    rw [hprepare] at hsel
    exact (hsel rfl).elim
  | localFailure dispatched hs reason =>
    rw [houtcome] at hprepare
    rw [hprepare] at hsel
    exact (hsel rfl).elim
  | continuingChosen dispatched hs continuation selection =>
    exact (initializing_not_continuing (liveInput x registers owned base) initialized
      hstart hcommand dispatched hs continuation selection houtcome).elim
  | cutoffChosen dispatched hs ledger hi hledger hdomain hclock hpending hnone selection =>
    rw [houtcome] at hprepare hpost
    rcases hpost with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      physical, hselected, hpay, hpend, hcut, _, _, _, _, _, recording, hrecord,
      started, hrest⟩
    rcases hrest with ⟨hledgerStart, hcandidate, _, _, _, _, _, _, _, _, _, _, _, _,
      decoded, bank, hreceive, _⟩
    have hcheck : CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started) = true := by
      by_contra hn
      have hf : CoordinatorUpReception.receptionInputCheck
          (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started) = false :=
        Bool.eq_false_iff.mpr hn
      have hinvalid := (ReferenceUpReception.receiveUpFilteredAtRow_input_invalid rate x.row
        (upInputs (prepare x) started) x.time
        ((prepare x).followers.followers (upSenderIndex x))
        ((prepare x).follower_alignment _).1 ((prepare x).follower_alignment _).2.1
        ((prepare x).follower_alignment _).2.2.1 rfl hf).1
      change (receiveUp (prepare x) started).result = .invalid at hinvalid
      rw [hinvalid] at hreceive
      contradiction
    have hstarted : started.pending = Finset.univ ∧ started.cutoff = x.time.val + 1 := by
      rw [hcandidate, hledger]
      exact ⟨rfl, rfl⟩
    have hcut' : physical.view.cutoff =
        some (CoordinatorCollectionUpRoundStep.localCutoff x.time) := by
      rw [hcut, hclock]
      rfl
    have hselection : (prepare x).coordinator.selection ≠ none := hsel
    have hobserve : (prepare x).observeCoordinator.up =
        (receiveUp (prepare x) started).diagnostic := by
      rw [observeCoordinator_live_equation (prepare x) registers owned base _ hprepare]
      have hn := hselection
      rw [hprepare] at hn
      rw [ite_eq_right hn]
      dsimp only
      unfold collectionPostChoice
      rw [hrecord]
      dsimp only
      rw [hledgerStart]
      exact ReferenceActiveAffinePositiveTest.collectionFinish_up x registers.payload
        dispatched.startResult recording (receiveUp (prepare x) started)
    refine ⟨physical, hselected, hpay, hpend.trans hpending, hcut',
      started, hstarted.1, hstarted.2, ?_, hcheck, ?_⟩
    · unfold ReferenceCoordinatorUpPhysicalCall.siteLedger?
      dsimp only
      rw [dite_eq_right hselection, hprepare]
      dsimp only
      unfold ReferenceCoordinatorUpPhysicalCall.tailLedger?
      rw [hrecord]
      dsimp only
      rw [hledgerStart]
    · unfold ReferenceActiveAffinePositiveTest.upPositive
      rw [hobserve, ReferenceActiveAffinePositiveTest.receiveUp_positive]
      change (CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started) && _) = _
      rw [hcheck, Bool.true_and]
      rfl

private theorem down_event
    {rate : RateInput p} (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (P : Payload rate) (i : Fin (p.m - 1)) (v : Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some v)
    (hpayload : v.view.payload = P) (hpending : i ∈ v.view.pendingAtChoice)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : ((prepare r.input).followers.followers i).configuration =
      .ordinary choice memory)
    (hstatus : choice.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid choice)
    (hfollowers : slotDraw (r.input.row.2 r.input.time).1 = downSlot →
      ∀ j : Fin (p.m - 1), (prepare r.input).arms.actions (followerPlayer p.two_le_m j) =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (followerPlayer p.two_le_m j)) :
    (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive r.input = true) ↔
    (slotDraw (r.input.row.2 r.input.time).1 = downSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
      AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (0, i))
        (CoordinatorLocalArmChoice.storedDownFlatWord P i) = 1 ∧
      0 < r.input.rewards r.input.time
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (followerPlayer p.two_le_m i))) := by
  have atDown (hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time) :
      (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        ReferenceActiveAffinePositiveTest.downPositive r.input = true) ↔
      (slotDraw (r.input.row.2 r.input.time).1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (0, i))
          (CoordinatorLocalArmChoice.storedDownFlatWord P i) = 1 ∧
        0 < r.input.rewards r.input.time
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
            (followerPlayer p.two_le_m i))) := by
    have hsender := ReferenceFirstReplacementCollectionOldDownSenderReadiness.selected_sender
      r P i v hselected hpayload hdown hpending
    have hcoord := hsender.2.2.2.1
    rw [r.output_eq] at hcoord
    exact ReferenceFirstCutoffDownControlGeometry.old_down_event_iff_prepared_unoccupied
      r.input i choice memory (CoordinatorLocalArmChoice.storedDownFlatWord P i)
      ((ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hdown.2)
      hconfiguration hstatus hdomain hcoord (hfollowers hdown.1)
  constructor
  · rintro ⟨hdraw, hpositive⟩
    have hindex := (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw r.input).trans hdraw
    have hgate := ReferenceFirstCutoffDownControlGeometry.down_gate_eq_decide_downSelected_of_prepared_unoccupied
      r.input i choice memory hindex hconfiguration hstatus hdomain
    have hp := hpositive
    rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback] at hp
    have hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
      rw [hgate] at hp
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hp).1
    exact (atDown hdown).mp ⟨hdraw, hpositive⟩
  · intro h
    exact (atDown ⟨h.1, h.2.1⟩).mpr h

private theorem coordinator_observation_positive_iff
    {rate : RateInput p} (x : RoundInput p rate) (arm : Fin p.K)
    (ha : (prepare x).arms.actions (ActiveRoundActions.coordinator p.two_le_m) = arm) :
    (0 < CoordinatorUpReception.roundedObservationValue p (prepare x).coordinatorObservation) ↔
      FiniteBanditModel.collisionFreeFor (prepare x).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) ∧ 0 < x.rewards x.time arm := by
  classical
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos : (0 < CoordinatorUpReception.roundedObservationValue p
      (prepare x).coordinatorObservation) ↔
      0 < ((prepare x).feedback.feedback (ActiveRoundActions.coordinator p.two_le_m)).val := by
    rw [CoordinatorUpReception.roundedObservationValue,
      PreparedRound.coordinatorObservation, div_pos_iff_of_pos_right hD]
    exact Nat.cast_pos
  rw [hpos, (prepare x).feedback_rule]
  by_cases hfree : FiniteBanditModel.collisionFreeFor (prepare x).arms.actions
      (ActiveRoundActions.coordinator p.two_le_m)
  · rw [ite_eq_left hfree, ha]
    simp only [hfree, true_and]
    rfl
  · rw [ite_eq_right hfree]
    simp only [Fin.val_zero, Nat.lt_irrefl, hfree, false_and]

private theorem up_event
    {rate : RateInput p} (x : RoundInput p rate) (i : Fin (p.m - 1))
    (v : Selection x) (hselected : (prepare x).coordinator.selection = some v)
    (hpending : i ∈ v.view.pendingAtChoice)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (started : Ledger rate) (hpend : started.pending = v.view.pendingAtChoice)
    (hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started) = true)
    (hpositive : ReferenceActiveAffinePositiveTest.upPositive x =
      decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput x started))))
    (hsender : slotDraw (x.row.2 x.time).1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i →
      ((prepare x).followers.followers i).arm = ActiveRoundActions.sendArm
        (ActiveFollowerArmChoice.offeredUpBit rate.eta (x.row.2 x.time) i U)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (followerPlayer p.two_le_m i))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m)))
    (hothers : slotDraw (x.row.2 x.time).1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i →
      ∀ j : Fin (p.m - 1), j ≠ i → ((prepare x).followers.followers j).arm =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (followerPlayer p.two_le_m j)) :
    (selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i ∧
      ReferenceActiveAffinePositiveTest.upPositive x = true) ↔
    (slotDraw (x.row.2 x.time).1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i ∧
      AffineChannelLaw.affineHash ((x.row.2 x.time).2 (1, i))
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
      0 < x.rewards x.time
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m))) := by
  classical
  let prepared := prepare x
  let input := ReferenceCoordinatorUpPhysicalCall.actualUpInput x started
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1
  let hash := AffineChannelLaw.affineHash ((x.row.2 x.time).2 (1, i))
    (ActiveFollowerArmChoice.offeredUpWord rate.eta U)
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid v.view.payload
      v.view.cutoff x.time v.view.complementWeights := by
    by_contra hn
    have hc := v.choice_eq
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
        _ _ _ _ _ _ hn] at hc
    contradiction
  have hcoord (hup : slotDraw (x.row.2 x.time).1 = upSlot) :
      prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
        tuple.val (ActiveRoundActions.coordinator p.two_le_m) := by
    have hnfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
        x.time ∧ v.view.pendingAtChoice = ∅) := by
      rintro ⟨_, he⟩
      rw [he] at hpending
      exact Finset.notMem_empty _ hpending
    have hnd : slotDraw (x.row.2 x.time).1 ≠ dataSlot := by rw [hup]; decide
    have hnDown : ¬ (slotDraw (x.row.2 x.time).1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 ∈ v.view.pendingAtChoice) := by
      rintro ⟨he, _⟩
      have : upSlot ≠ downSlot := by decide
      exact this (hup.symm.trans he)
    have hc := v.choice_eq
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      CoordinatorLocalArmChoice.coordinatorArmChoiceCore_other _ _ _ _ _ _
        hvalid hnfast hnd hnDown] at hc
    have harm : prepared.coordinator.arm = v.arm := by
      change (prepare x).coordinator.arm = v.arm
      unfold DispatchCut.arm
      rw [hselected]
    exact prepared.action_coordinator.trans (harm.trans (Option.some.inj hc).symm)
  constructor
  · rintro ⟨hdraw, hp⟩
    have he : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input) := by
      rw [hpositive] at hp
      exact of_decide_eq_true hp
    obtain ⟨hup, hobs⟩ := ReferenceUpPhysicalHashRule.receiver_eligible_observation
      prepared started he
    have hfree := (coordinator_observation_positive_iff x _ (hcoord hup)).mp hobs
    have hbit : hash = 0 ∨ hash = 1 := by
      have hv : hash.val = 0 ∨ hash.val = 1 := by have := ZMod.val_lt hash; omega
      rcases hv with hv | hv
      · left
        simpa only [hv, Nat.cast_zero] using (ZMod.natCast_zmod_val hash).symm
      · right
        simpa only [hv, Nat.cast_one] using (ZMod.natCast_zmod_val hash).symm
    have hone : hash = 1 := by
      rcases hbit with hz | ho
      · have hne := hfree.1 (followerPlayer p.two_le_m i)
          (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i)
        rw [prepared.arms.actions_follower i] at hne
        change ((prepare x).followers.followers i).arm ≠
          prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) at hne
        rw [hsender ⟨hup, hdraw⟩, hcoord hup] at hne
        change ActiveRoundActions.sendArm hash _ _ ≠ _ at hne
        rw [hz, ActiveRoundActions.sendArm_zero] at hne
        exact (hne rfl).elim
      · exact ho
    exact ⟨hup, hdraw, hone, hfree.2⟩
  · rintro ⟨hup, hdraw, hhash, hreward⟩
    have hfree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) := by
      intro player hne
      rcases ActiveRoundActions.player_cases p.two_le_m player with ho | ⟨j, hj⟩
      · exact (hne ho).elim
      · rw [hj, prepared.arms.actions_follower j, hcoord hup]
        change ((prepare x).followers.followers j).arm ≠
          tuple.val (ActiveRoundActions.coordinator p.two_le_m)
        by_cases hji : j = i
        · subst j
          rw [hsender ⟨hup, hdraw⟩, ActiveFollowerArmChoice.offeredUpBit,
            hhash, ActiveRoundActions.sendArm_one]
          exact fun he => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
            (tuple.property he)
        · rw [hothers ⟨hup, hdraw⟩ j hji]
          exact fun he => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
            (tuple.property he)
    have hobs := (coordinator_observation_positive_iff x _ (hcoord hup)).mpr ⟨hfree, hreward⟩
    have hdomain := (CoordinatorUpReception.receptionInputCheck_eq_true_iff input).mp hcheck
    have hgate : CoordinatorUpReception.receptionGate input := by
      refine ⟨hdomain.2.2.2.2.1.trans hdomain.2.2.2.2.2.2.1.le, hup, ?_⟩
      change selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 ∈ started.pending
      rw [hdraw, hpend]
      exact hpending
    have he : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput input) :=
      ⟨(CoordinatorUpReception.roundInput_selected_iff_gate input).mpr hgate, rfl, hobs⟩
    exact ⟨hdraw, hpositive.trans (decide_eq_true he)⟩

private theorem live_outcome_of_prepare
    {rate : RateInput p} (x : RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x registers owned base))
    (hstate : x.state.coordinator = .live registers owned base)
    (hprepare : (prepare x).coordinator = .live registers owned base outcome) :
    CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base) = outcome := by
  have hp : (prepare x).coordinator = .live registers owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x registers owned base)) := by
    simp only [prepare, dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have he := hp.symm.trans hprepare
  injection he

private theorem complete_record_rewards
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hr : r ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) : r.input.rewards = rewards := by
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hr
  obtain ⟨_, _, hrecord⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z ⟨k, hk⟩
  rw [← heq]
  change ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get
    ⟨k, hk⟩).input.rewards = rewards
  rw [hrecord]
  rfl

private theorem selection_transport_view
    {rate : RateInput p} {x y : RoundInput p rate} (he : x = y) (v : Selection x) :
    (he ▸ v).view = v.view := by
  cases he
  rfl

private theorem selection_transport_selected
    {rate : RateInput p} {x y : RoundInput p rate} (he : x = y) (v : Selection x)
    (hv : (prepare x).coordinator.selection = some v) :
    (prepare y).coordinator.selection = some (he ▸ v) := by
  cases he
  exact hv

private theorem down_readout_eq
    {rate : RateInput p} (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (h : ContinuousLearningRows.TimeControl p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (ht : r.input.time = t) (hc : r.input.row.2 r.input.time = h)
    (hrewards : r.input.rewards = rewards)
    (hevent : (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        ReferenceActiveAffinePositiveTest.downPositive r.input = true) ↔
      (slotDraw (r.input.row.2 r.input.time).1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (0, i)) word = 1 ∧
        0 < r.input.rewards r.input.time
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
            (followerPlayer p.two_le_m i)))) :
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t z =
      (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet rewards t i word).indicator
        (fun _ => (1 : ℝ)) h := by
  subst t
  subst h
  subst rewards
  unfold ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
  rw [hr]
  rw [Set.indicator_apply]
  dsimp only
  apply ite_congr
  · exact propext hevent
  · intro _; rfl
  · intro _; rfl

private theorem up_readout_eq
    {rate : RateInput p} (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (h : ContinuousLearningRows.TimeControl p)
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (ht : r.input.time = t) (hc : r.input.row.2 r.input.time = h)
    (hrewards : r.input.rewards = rewards)
    (hevent : (selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input = true) ↔
      (slotDraw (r.input.row.2 r.input.time).1 = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1 = i ∧
        AffineChannelLaw.affineHash ((r.input.row.2 r.input.time).2 (1, i))
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
        0 < r.input.rewards r.input.time
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1).val
          (ActiveRoundActions.coordinator p.two_le_m)))) :
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t z =
      (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet
        (rate := rate) rewards t i U).indicator (fun _ => (1 : ℝ)) h := by
  subst t
  subst h
  subst rewards
  unfold ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
  rw [hr]
  rw [Set.indicator_apply]
  dsimp only
  apply ite_congr
  · exact propext hevent
  · intro _; rfl
  · intro _; rfl

/-- Literal whole-control OLD and FORMED positive tests in every physical row
of the first replacement collection, including its cutoff and detecting row.
This deterministic identity is intended for the later actual stopped-service
assembly after its predictable stage, support and count construction. -/
theorem complete_first_replacement_collection_fresh_positive_tests
    (rate : RateInput p) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let _J := ActualInitializationPhysicalStep.selectedRowIndex p z
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let P := installed.registers.payload
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let M := fun i => P.downRecord i
            ∀ a : Fin K.length,
              let r := K.get a
              let t := r.input.time
              ∃ v0 : Selection r.input,
                r.output.preparation.coordinator.selection = some v0 ∧
                v0.view.payload = P ∧
                v0.view.cutoff = some
                  (CoordinatorCollectionUpRoundStep.localCutoff cut.input.time) ∧
                ∀ i : Fin (p.m - 1), i ∈ v0.view.pendingAtChoice →
                  ReferenceFirstReplacementCollectionCommonStopObservation.L
                    rate rewards C_star C_h control0 s u i t.val z = false →
                  (ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt r i (M i) →
                    ∀ h : ContinuousLearningRows.TimeControl p,
                    let zh := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h
                    let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
                    let wD := CoordinatorLocalArmChoice.storedDownFlatWord P i
                    ∃ rh : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                      ∃ vh : Selection xh,
                        ReferenceSourcePrefixHistoryFiltration.actualRecord
                          rate rewards C_star C_h t zh = some rh ∧ rh.input = xh ∧
                        (prepare xh).coordinator.selection = some vh ∧
                        vh.view.payload = P ∧ vh.view.pendingAtChoice = v0.view.pendingAtChoice ∧
                        vh.view.cutoff = v0.view.cutoff ∧
                        ReferenceFirstReplacementCollectionCommonStopObservation.L
                          rate rewards C_star C_h control0 s u i t.val zh = false ∧
                        ReferenceFirstReplacementCollectionOldDownCallDates.actualOldAt rh i (M i) ∧
                        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
                            (rate := rate) rewards C_star C_h i t zh =
                          (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet
                            rewards t i wD).indicator (fun _ => (1 : ℝ)) h) ∧
                  (ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt r i (M i) →
                    ∃ choice : ReferencePrelaunchFollower.State p rate.eta,
                      ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                      ∃ U : OrdinaryMessageCodec.UpRecord
                          (ReferencePrelaunchFollower.codecParams p rate.eta),
                        (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                          .ordinary choice memory ∧ choice.status = .unoccupied ∧
                        choice.lastDown = some (M i) ∧
                        U.val = ActiveFollowerQueueOperation.upOfferFields choice ∧
                        U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                        ∀ h : ContinuousLearningRows.TimeControl p,
                        let zh := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h
                        let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
                        ∃ rh : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                          ∃ vh : Selection xh,
                            ReferenceSourcePrefixHistoryFiltration.actualRecord
                              rate rewards C_star C_h t zh = some rh ∧ rh.input = xh ∧
                            (prepare xh).coordinator.selection = some vh ∧
                            vh.view.payload = P ∧
                            vh.view.pendingAtChoice = v0.view.pendingAtChoice ∧
                            vh.view.cutoff = v0.view.cutoff ∧
                            ReferenceFirstReplacementCollectionCommonStopObservation.L
                              rate rewards C_star C_h control0 s u i t.val zh = false ∧
                            ReferenceFirstReplacementCollectionStoppedPureUpQuota.replyFormedAt
                              rh i (M i) ∧
                            ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
                                (rate := rate) rewards C_star C_h i t zh =
                              (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet
                                (rate := rate) rewards t i U).indicator (fun _ => (1 : ℝ)) h)
          | _ => True
      | _ => True := by
  classical
  have hA := ReferenceFirstReplacementCollectionFreshFollowerGeometry.complete_first_replacement_collection_follower_control_geometry
    rate z rewards C_star C_h
  have hV := complete_first_replacement_collection_choice_views rate z rewards C_star C_h
  have hB := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  have hR := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h
  have hP := ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
    rate z rewards C_star C_h
  dsimp only at hA hV hB hR hP ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hA hV hB hR hP ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hA hV hB hR hP ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [collectionInput] at hA hV hB hR hP ⊢
      rcases hR with ⟨_, _, hR⟩
      rcases hP with ⟨_, _, hP⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hA hV hB hR hP ⊢
        rcases hB with ⟨_, hB⟩
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hA hV hB hR hP ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hA hV hB hR hP ⊢
          let P := installed.registers.payload
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          have hpayregs : registers.payload = P := hB.1
          have hcutmem : cut ∈ R := List.mem_of_getElem? hc
          have hcutprep : (prepare cut.input).coordinator = .live registers owned base
              (.cutoffChosen dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut) := by
            have h := hcut
            rw [cut.output_eq] at h
            exact h
          have hcutstate := live_input_of_prepare cut.input registers owned base _ hcutprep
          have hcommand : dispatched.startResult.ledgerCommand = some (.initializeAt cut.input.time) := by
            obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hcutmem
            have hp := complete_live_cutoff_post_choice rate rewards C_star C_h z
              ⟨k, hk⟩ registers owned base (heq ▸ hcutstate)
            dsimp only at hp
            rw [heq] at hp
            rw [live_outcome_of_prepare cut.input registers owned base _ hcutstate hcutprep] at hp
            exact hp.2.1
          rcases hR with ⟨hendpoints, _, _⟩
          rcases hP with ⟨_, hZ, _⟩
          intro a
          let r := K.get a
          let t := r.input.time
          obtain ⟨v0, hv0, hvpay, hvcut⟩ := hV a
          refine ⟨v0, hv0, hvpay, hvcut, ?_⟩
          intro i himem hL
          have hrmem : r ∈ R := by
            rcases a with ⟨a, ha⟩
            cases a with
            | zero => exact hcutmem
            | succ a =>
              exact List.mem_of_getElem?
                (ReferenceFirstReplacementCollectionFollowerPrefix.collectionWindow_get
                  R c a (Nat.lt_of_succ_lt_succ ha))
          have hractual := actualRecord_of_mem rate z rewards C_star C_h r hrmem
          have hrrewards := complete_record_rewards rate z rewards C_star C_h r hrmem
          obtain ⟨choice, memory, U, hactual, hstatus, hdomain, _, _, hU, hgeometry⟩ := hA a i
          have fresh (h : ContinuousLearningRows.TimeControl p) :
              let zh := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h
              let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
              ∃ rh : ReferenceCompletePhysicalHistory.RoundRecord p rate,
                ReferenceSourcePrefixHistoryFiltration.actualRecord
                  rate rewards C_star C_h t zh = some rh ∧ rh.input = xh ∧
                ∃ vh : Selection xh,
                  (prepare xh).coordinator.selection = some vh ∧
                  vh.view.payload = P ∧ vh.view.pendingAtChoice = v0.view.pendingAtChoice ∧
                  vh.view.cutoff = v0.view.cutoff ∧
                  ∃ started : Ledger rate, started.pending = vh.view.pendingAtChoice ∧
                    CoordinatorUpReception.receptionInputCheck
                      (ReferenceCoordinatorUpPhysicalCall.actualUpInput xh started) = true ∧
                    ReferenceActiveAffinePositiveTest.upPositive xh =
                      decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
                        (ReferenceCoordinatorUpPhysicalCall.actualUpInput xh started))) := by
            dsimp only
            let zh := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h
            let xh := ReferenceLaterOptionalControlResampling.withControl r.input h
            obtain ⟨rh, hrh, hinput⟩ :=
              ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUp_actualRecord_replace
                rewards C_star C_h control0 t z r hractual h
            have hrhmem : rh ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate zh rewards C_star C_h := by
              unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hrh
              split at hrh
              · exact List.mem_of_getElem? hrh
              · contradiction
            have site : ∃ vh : Selection rh.input,
                (prepare rh.input).coordinator.selection = some vh ∧
                vh.view.payload = P ∧ vh.view.pendingAtChoice = v0.view.pendingAtChoice ∧
                vh.view.cutoff = v0.view.cutoff ∧
                ∃ started : Ledger rate, started.pending = vh.view.pendingAtChoice ∧
                  CoordinatorUpReception.receptionInputCheck
                    (ReferenceCoordinatorUpPhysicalCall.actualUpInput rh.input started) = true ∧
                  ReferenceActiveAffinePositiveTest.upPositive rh.input =
                    decide (AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput
                      (ReferenceCoordinatorUpPhysicalCall.actualUpInput rh.input started))) := by
              rcases a with ⟨a, ha⟩
              cases a with
              | zero =>
                have hstateh : rh.input.state.coordinator = .live registers owned base := by
                  rw [hinput]
                  exact hcutstate
                have hsh : CoordinatorPhaseClock.startRound p rate.eta.val rh.input.time
                    registers.priorClock registers.clockPending = .ok dispatched.startResult := by
                  rw [hinput]
                  exact hs
                have hch : dispatched.startResult.ledgerCommand = some (.initializeAt rh.input.time) := by
                  rw [hinput]
                  exact hcommand
                obtain ⟨vh, hvh, hpay, hpend, hcutoff, started, hsp, _, hsite, hcheck, hpos⟩ :=
                  complete_cutoff_site rate zh rewards C_star C_h rh hrhmem
                    registers owned base hstateh dispatched.startResult hsh hch
                rcases hB with ⟨_, _, _, _, _, _, _, _, _, _, _, vc, hvc, _, hvcp, _, _⟩
                have hvc' : cut.output.preparation.coordinator.selection = some vc := by
                  rw [hcut]
                  exact hvc
                have he : v0 = vc := Option.some.inj (hv0.symm.trans hvc')
                have hpc : v0.view.pendingAtChoice = Finset.univ := he ▸ hvcp
                refine ⟨vh, hvh, hpay.trans hpayregs, hpend.trans hpc.symm, ?_,
                  started, hsp.trans hpend.symm, hcheck, hpos⟩
                rw [hcutoff, hvcut]
                rw [hinput]
                rfl
              | succ a =>
                have haW : a < W.length := Nat.lt_of_succ_lt_succ ha
                have hinputState : r.input.state = E a := by
                  have hlink := (hZ.2.2 ⟨a + 1, ha⟩).1
                  change r.input.state = Z (a + 1) at hlink
                  exact hlink.trans (hZ.2.1 a (Nat.le_of_lt haW))
                have hnonD := (complete_record_selection rate z rewards C_star C_h r hrmem).1
                rcases hendpoints a (Nat.le_of_lt haW) with hd | ⟨l, saved, hstate, _, hcutoff, _⟩
                · exact (hnonD ((congrArg (fun s => s.coordinator) hinputState).trans hd)).elim
                · have hstate' : r.input.state.coordinator = .collection P l saved :=
                    (congrArg (fun s => s.coordinator) hinputState).trans hstate
                  have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
                    have hp := List.all_eq_true.mp (List.all_takeWhile
                      (l := R.drop (c + 1))
                      (p := fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input))
                      r (List.get_mem W ⟨a, haW⟩)
                    cases ht : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                      simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true]
                  have hfields := continuing_selection_fields r P l saved cut.input.time
                    hstate' hn hcutoff v0 hv0
                  have hstateh : rh.input.state.coordinator = .collection P l saved := by
                    rw [hinput]
                    exact hstate'
                  obtain ⟨uh, huh, vh, hvh, hpay, hpend, hcutvh, started, hsp, _, hsite, hcheck, hpos⟩ :=
                    complete_continuing_site rate zh rewards C_star C_h rh hrhmem
                      P l saved hstateh ⟨i, hfields.2.1 ▸ himem⟩
                  have he : uh = cut.input.time := Fin.ext (by omega)
                  refine ⟨vh, hvh, hpay, hpend.trans hfields.2.1.symm, ?_,
                    started, hsp.trans hpend.symm, hcheck, hpos⟩
                  rw [hcutvh, he, hvcut]
            obtain ⟨vh, hvh, hpay, hpend, hcutvh, started, hsp, hcheck, hpos⟩ := site
            refine ⟨rh, hrh, hinput, hinput ▸ vh,
              selection_transport_selected hinput vh hvh, ?_⟩
            rw [selection_transport_view]
            exact ⟨hpay, hpend, hcutvh, started, hsp,
              by simpa only [hinput] using hcheck, by simpa only [hinput] using hpos⟩
          constructor
          · intro hold h
            obtain ⟨rh, hrh, hinput, vh, hvh, hpay, hpend, hcutvh, started, _, _, _⟩ := fresh h
            rcases hold with ⟨old, oldMemory, hold, _, hlast⟩
            have he := hold.symm.trans hactual
            injection he with heq hmem
            subst old
            have hactualh : (ReferenceFollowerFixedReply.actualChoice rh i).configuration =
                .ordinary choice memory := by
              change (rh.output.preparation.followers.followers i).configuration = _
              rw [rh.output_eq]
              change ((prepare rh.input).followers.followers i).configuration = _
              rw [hinput]
              exact (hgeometry h).1
            have hcfg := (hgeometry h).1
            have hselout : rh.output.preparation.coordinator.selection =
                some (hinput.symm ▸ vh) := by
              rw [rh.output_eq]
              exact selection_transport_selected hinput.symm vh hvh
            have hevent := down_event rh P i (hinput.symm ▸ vh) hselout
              (by rw [selection_transport_view]; exact hpay)
              (by rw [selection_transport_view]; exact hpend.symm ▸ himem)
              choice memory (by rw [hinput]; exact hcfg) hstatus hdomain (by
                intro hd j
                obtain ⟨_, _, _, _, _, _, _, _, _, hj⟩ := hA a j
                have hh := (hj h).2.2.2
                have hcurrent : rh.input.row.2 rh.input.time = h :=
                  (congrArg (fun x : RoundInput p rate => x.row.2 x.time) hinput).trans
                    (ReferenceLaterOptionalControlResampling.withControl_currentControl r.input h)
                have hd' : slotDraw h.1 = downSlot :=
                  (congrArg (fun c => slotDraw c.1) hcurrent).symm.trans hd
                have hsnot : slotDraw h.1 ≠ dataSlot := by rw [hd']; decide
                have hnup : ¬ (slotDraw h.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = j) := by
                  rintro ⟨he, _⟩
                  rw [hd'] at he
                  contradiction
                have ha := (prepare (ReferenceLaterOptionalControlResampling.withControl r.input h)).arms.actions_follower j
                  |>.trans (hh ⟨hsnot, hnup⟩)
                exact (congrArg (fun x : RoundInput p rate =>
                  (prepare x).arms.actions (followerPlayer p.two_le_m j)) hinput).trans
                    (ha.trans (congrArg (fun c : ContinuousLearningRows.TimeControl p =>
                      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
                        (followerPlayer p.two_le_m j)) hcurrent.symm)))
            refine ⟨rh, vh, hrh, hinput, hvh, hpay, hpend, hcutvh, ?_,
              ⟨choice, memory, hactualh, hstatus, hlast⟩, ?_⟩
            · rw [L_replaceSourceControl]
              exact hL
            · exact down_readout_eq rewards C_star C_h _ t i h rh
                (CoordinatorLocalArmChoice.storedDownFlatWord P i) hrh
                ((congrArg RoundInput.time hinput).trans
                  (ReferenceLaterOptionalControlResampling.withControl_time r.input h))
                ((congrArg (fun x : RoundInput p rate => x.row.2 x.time) hinput).trans
                  (ReferenceLaterOptionalControlResampling.withControl_currentControl r.input h))
                ((congrArg RoundInput.rewards hinput).trans hrrewards) hevent
          · intro hformed
            rcases hformed with ⟨formed, formedMemory, hformed, _, hlast⟩
            have he := hformed.symm.trans hactual
            injection he with heq hmem
            subst formed
            have hsigma : U.val.sigma = (P.downRecord i).val.sigma := by
              rw [hU, ActiveFollowerQueueOperation.upOfferFields,
                ReferencePrelaunchFollower.acceptedStart, hlast]
              rfl
            refine ⟨choice, memory, U, hactual, hstatus, hlast, hU, hsigma,
              hsigma ▸ (P.downRecord i).property.1, ?_⟩
            intro h
            obtain ⟨rh, hrh, hinput, vh, hvh, hpay, hpend, hcutvh, started, hsp, hcheck, hpos⟩ := fresh h
            have hactualh : (ReferenceFollowerFixedReply.actualChoice rh i).configuration =
                .ordinary choice memory := by
              change (rh.output.preparation.followers.followers i).configuration = _
              rw [rh.output_eq]
              change ((prepare rh.input).followers.followers i).configuration = _
              rw [hinput]
              exact (hgeometry h).1
            have hevent := up_event (ReferenceLaterOptionalControlResampling.withControl r.input h)
              i vh hvh (hpend.symm ▸ himem) U started hsp hcheck hpos
              (by
                intro hu
                have hcur := ReferenceLaterOptionalControlResampling.withControl_currentControl r.input h
                have hu' := And.intro
                  ((congrArg (fun c => slotDraw c.1) hcur).symm.trans hu.1)
                  ((congrArg (fun c => selectedFollowerDraw p.two_le_m p.m_lt_K c.1) hcur).symm.trans hu.2)
                exact (((hgeometry h).2.1 hu').2).trans
                  (congrArg (fun c : ContinuousLearningRows.TimeControl p => ActiveRoundActions.sendArm
                    (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
                    ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val (followerPlayer p.two_le_m i))
                    ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
                      (ActiveRoundActions.coordinator p.two_le_m))) hcur.symm)) (by
                intro hu j hji
                have hcur := ReferenceLaterOptionalControlResampling.withControl_currentControl r.input h
                have hu' := And.intro
                  ((congrArg (fun c => slotDraw c.1) hcur).symm.trans hu.1)
                  ((congrArg (fun c => selectedFollowerDraw p.two_le_m p.m_lt_K c.1) hcur).symm.trans hu.2)
                obtain ⟨_, _, _, _, _, _, _, _, _, hj⟩ := hA a j
                have hnData : slotDraw h.1 ≠ dataSlot := by rw [hu'.1]; decide
                have hnUp : ¬ (slotDraw h.1 = upSlot ∧ selectedFollowerDraw p.two_le_m p.m_lt_K h.1 = j) := by
                  rintro ⟨_, he⟩
                  exact hji (he.symm.trans hu'.2)
                exact ((hj h).2.2.2 ⟨hnData, hnUp⟩).trans
                  (congrArg (fun c : ContinuousLearningRows.TimeControl p =>
                    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
                      (followerPlayer p.two_le_m j)) hcur.symm))
            refine ⟨rh, vh, hrh, hinput, hvh, hpay, hpend, hcutvh, ?_,
              ⟨choice, memory, hactualh, hstatus, hlast⟩, ?_⟩
            · rw [L_replaceSourceControl]
              exact hL
            · apply up_readout_eq rewards C_star C_h _ t i h rh U hrh
                ((congrArg RoundInput.time hinput).trans
                  (ReferenceLaterOptionalControlResampling.withControl_time r.input h))
                ((congrArg (fun x : RoundInput p rate => x.row.2 x.time) hinput).trans
                  (ReferenceLaterOptionalControlResampling.withControl_currentControl r.input h))
                ((congrArg RoundInput.rewards hinput).trans hrrewards)
              exact hinput.symm ▸ hevent

end Bandits.Support.ReferenceFirstReplacementCollectionFreshPositiveService
