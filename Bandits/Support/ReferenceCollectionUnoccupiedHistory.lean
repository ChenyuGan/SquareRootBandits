/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionPhaseHistory
public import Bandits.Support.ReferenceFollowerReplyChronology
public import Bandits.Support.ReferenceAssignmentPayloadChronology
public import Bandits.Support.ReferenceActiveDataOwnership

import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# Collection-window unoccupied-follower history

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-88,100-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,246-295,324,340-344`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:54-64,100-108`.

The results below follow one actual follower and coordinator through the
retained collection prefix of the original physical run. They preserve the
whole follower reply while retaining the buffers, batches, and proposal memory
computed by the actual constructors. The local seed is explicit: this module
does not produce it from an accepted UP. The boundary result stops before the
replacement round's tail, where the new payload may be accepted.
They do not assert service identities, queue truth, or source-facing
manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.ReferenceFollowerFixedReply

namespace Bandits.Support.ReferenceCollectionUnoccupiedHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem connected_endpoint_unique
    {initial left right : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hl : ReferenceActivePhysicalHorizon.Connected initial records left)
    (hr : ReferenceActivePhysicalHorizon.Connected initial records right) :
    left = right := by
  induction records generalizing initial left right with
  | nil =>
      change left = initial at hl
      change right = initial at hr
      exact hl.trans hr.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hl hr
      exact ih hl.2 hr.2

private def runRecordAt (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start index
    (by omega) active
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards start
    active prefixRun ⟨start + index, by omega, by omega⟩
  ⟨input, ReferenceActivePhysicalStep.step input, rfl⟩

private theorem run_successor_equations (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start index : ℕ) (hspan : start + (index + 1) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      hspan active).finalState = (runRecordAt initial rows selected rewards start index hspan active).output.next ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (index + 1)
      hspan active).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) active).records ++
        [runRecordAt initial rows selected rewards start index hspan active] := by
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  have heq := ReferenceActivePhysicalHorizon.foldRound_equations initial rows selected rewards start
    active (ReferenceActivePhysicalHorizon.run initial rows selected rewards start index (by omega) active)
    ⟨start + index, by omega, by omega⟩
  simpa [runRecordAt, ReferenceActivePhysicalHorizon.roundInputAt] using heq

private theorem run_prefix_records (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active).records := by
  revert hspan hn
  induction total with
  | zero =>
      intro hspan hn
      have hn0 : n = 0 := by omega
      subst n
      rw [List.take_zero, ReferenceActivePhysicalHorizon.run_zero_records]
  | succ total ih =>
      intro hspan hn
      by_cases heq : n = total + 1
      · subst n
        apply List.take_of_length_le
        rw [ReferenceActivePhysicalHorizon.run_record_count]
      · have hn' : n ≤ total := by omega
        rw [(run_successor_equations initial rows selected rewards start total hspan active).2,
          List.take_append_of_le_length (by
            rw [ReferenceActivePhysicalHorizon.run_record_count]
            exact hn')]
        exact ih (by omega) hn'

private theorem run_prefix_endpoints (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).input.state ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1) (by omega) active).finalState =
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records[n]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        exact hn)).output.next := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active
  let nextPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1) (by omega) active
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards start total hspan active
  have hnFull : n < full.records.length := by
    dsimp [full]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hn
  have htake := ReferenceFollowerReplyChronology.connected_take_to_input hconnected n hnFull
  have hprefix := run_prefix_records initial rows selected rewards start total hspan active n (by omega)
  have hinput := connected_endpoint_unique prefixRun.connected (by
    rw [← hprefix]
    exact htake)
  have hchainPrefix := ReferenceFollowerReplyChronology.connected_take_to_input
    hconnected n hnFull
  have htakeSucc : full.records.take (n + 1) = full.records.take n ++ [full.records[n]] := by
    rw [List.take_add_one]
    simp [hnFull]
  have hchainNext : ReferenceActivePhysicalHorizon.Connected initial
      (full.records.take (n + 1)) (full.records[n].output.next) := by
    rw [htakeSucc]
    exact ReferenceActivePhysicalHorizon.Connected.append_one
      (full.records.take n) full.records[n] hchainPrefix rfl
  have hrecordsNext := run_prefix_records initial rows selected rewards start total hspan active
    (n + 1) (by omega)
  have hnext := connected_endpoint_unique nextPrefix.connected (by
    rw [← hrecordsNext]
    exact hchainNext)
  exact ⟨hinput, hnext⟩

private theorem takeWhile_length_le (α : Type) (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

private theorem getElem_takeWhile_eq (α : Type) (pred : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < (xs.takeWhile pred).length) :
    (xs.takeWhile pred)[k] = xs[k]'(by
      exact Nat.lt_of_lt_of_le hk (takeWhile_length_le α pred xs)) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases hp : pred head with
      | false => simp [List.takeWhile, hp] at hk
      | true =>
          cases k with
          | zero => simp [List.takeWhile, hp]
          | succ k =>
              have htail : k < (tail.takeWhile pred).length := by
                simpa [List.takeWhile, hp] using hk
              simpa only [List.takeWhile, hp, List.getElem_cons_succ] using ih k htail

private theorem takeWhile_boundary_not (α : Type) (pred : α → Bool)
    (xs : List α) (k : ℕ) (hlen : (xs.takeWhile pred).length = k)
    (hk : k < xs.length) : pred (xs.get ⟨k, hk⟩) = false := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases hp : pred head with
      | false =>
          cases k with
          | zero => simpa using hp
          | succ k => simp [List.takeWhile, hp] at hlen
      | true =>
          cases k with
          | zero => simp [List.takeWhile, hp] at hlen
          | succ k =>
              have hlen' : (tail.takeWhile pred).length = k := by
                simpa [List.takeWhile, hp] using hlen
              have hk' : k < tail.length := by
                simpa using hk
              simpa using ih k hlen' hk'

private theorem actualChoice_unoccupied_reply
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (hin : record.input.state.followers i = .dagger ∨
      ∃ state memory, record.input.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) :
    (ReferenceFollowerFixedReply.actualChoice record i).configuration = .dagger ∨
      ∃ state memory,
        (ReferenceFollowerFixedReply.actualChoice record i).configuration = .ordinary state memory ∧
        state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed := by
  have hprep : ReferenceFollowerFixedReply.actualChoice record i =
      DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := by
    exact record.output.preparation.followers.followers_eq i
  rcases hin with hdagger | ⟨before, memory, hbefore, hstatus, hreply⟩
  · rw [hprep, hdagger]
    simp [DeclaredFollowerLocalRound.prepare]
  · rw [hprep, hbefore]
    cases hchoice : DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (.ordinary before memory) with
    | mk follower row activation time active arm configuration =>
      cases hconfig : configuration with
      | dagger => exact Or.inl (by simp)
      | ordinary choice choiceMemory =>
          have hordinary : (DeclaredFollowerLocalRound.prepare rate i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (.ordinary before memory)).configuration = .ordinary choice choiceMemory := by
            simpa [hconfig] using congrArg DeclaredFollowerLocalRound.PreparedRound.configuration hchoice
          obtain ⟨actualBefore, beforeMemory, hinput, hstart, hframe, hunoccupied⟩ :=
            ReferenceFollowerReplyChronology.prepare_ordinary_inversion i record.input.row
              (record.input.state.activations i) record.input.time (record.input.active i)
              (.ordinary before memory) choice choiceMemory hordinary
          have hactual : actualBefore = before := by
            exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hinput).1.symm
          subst actualBefore
          have hu : choice.status = .unoccupied := hunoccupied hstatus
          exact Or.inr ⟨choice, choiceMemory, by rfl,
            hu, hframe.trans hreply⟩

private theorem actualSelection_view
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hcoord : x.state.coordinator = .dagger ∨
      ∃ ledger saved, x.state.coordinator = .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.downView = none ∨
      ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
        (ReferenceActivePhysicalStep.prepare x).coordinator.downView = some view ∧
        view.payload = payload := by
  rcases hcoord with hdagger | ⟨ledger, saved, hcollection⟩
  · left
    change (ReferenceActivePhysicalStep.dispatch x).downView = none
    rw [ReferenceActivePhysicalStep.dispatch_dagger x hdagger]
    simp [ReferenceActivePhysicalStep.DispatchCut.downView,
      ReferenceActivePhysicalStep.DispatchCut.selection]
  · by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
      let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
      cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection input) with
      | collection outcome =>
        have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .collection payload ledger clock cutoff outcome := by
          change ReferenceActivePhysicalStep.dispatch x =
            .collection payload ledger clock cutoff outcome
          unfold ReferenceActivePhysicalStep.dispatch
          rw [hcollection]
          simp only [dite_eq_left hvalid]
          dsimp [cutoff, clock, input]
          rw [hdispatch]
          rfl
        cases outcome with
        | continuing core snapshot boundary scores =>
            let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
              payload := payload
              pendingAtChoice := snapshot.clockStarted.pending
              cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                snapshot.clockStarted.clock.u
              complementWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq }
            right
            refine ⟨view, ?_, rfl⟩
            rw [ReferenceActivePhysicalStep.DispatchCut.downView, hcut]
            rfl
        | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
            have hfalse := hn
            unfold ReferenceCollectionPhaseHistory.laterChosen at hfalse
            rw [hcut] at hfalse
            simp at hfalse
        | _ =>
            left
            rw [ReferenceActivePhysicalStep.DispatchCut.downView, hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
    · left
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hvalid, hcollection, ReferenceActivePhysicalStep.DispatchCut.downView,
        ReferenceActivePhysicalStep.DispatchCut.selection]

private theorem step_collection_same_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : x.state.coordinator = .collection payload ledger saved)
    (hn : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ movingLedger movingSaved,
        (ReferenceActivePhysicalStep.step x).next.coordinator =
          .collection payload movingLedger movingSaved := by
  by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection input) with
    | collection outcome =>
      have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
          .collection payload ledger clock cutoff outcome := by
        change ReferenceActivePhysicalStep.dispatch x =
          .collection payload ledger clock cutoff outcome
        unfold ReferenceActivePhysicalStep.dispatch
        rw [hcoord]
        simp only [dite_eq_left hvalid]
        dsimp [cutoff, clock, input]
        rw [hdispatch]
        rfl
      have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
        (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcut
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hselection :
              (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                (.continuing core snapshot boundary scores)).selection ≠ none := by
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hpost : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
                (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                  snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) := by
            simpa [hselection] using hobs
          have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
            (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights input
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
          have hpayloadFrame := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
            (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
            (CoordinatorCollectionInteractive.PreObservationInputs.weights input
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
          rcases hphase with hdagger | ⟨nextPayload, nextLedger, nextSaved, hnext⟩
          · left
            rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
            rw [congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost]
            exact hdagger
          · have hpayload : nextPayload = payload := by
              rw [hnext] at hpayloadFrame
              simp [ReferenceAssignmentPayloadPersistence.storedPayload] at hpayloadFrame
              exact hpayloadFrame
            right
            refine ⟨nextLedger, nextSaved, ?_⟩
            rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
            rw [congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost,
              hnext, hpayload]
      | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
          have hfalse := hn
          unfold ReferenceCollectionPhaseHistory.laterChosen at hfalse
          rw [hcut] at hfalse
          simp at hfalse
      | _ =>
          have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
            rw [hcut]
            simp [ReferenceActivePhysicalStep.DispatchCut.selection]
          have hselectionOut := hselection
          rw [hcut] at hselectionOut
          left
          rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
          have hfailure : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
              ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
                .dispatchRejected none none := by
            simpa [hselectionOut] using hobs
          rw [hfailure]
          rfl
  · have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
        .invalidCollectionCutoff := by
      simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hvalid, hcoord]
    left
    rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
    simp [ReferenceActivePhysicalStep.PreparedRound.observeCoordinator, hcut,
      ReferenceActivePhysicalStep.coordinatorFailure]

private theorem recordFollower_logging_of_downInput
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice logged : ReferencePrelaunchFollower.State p rate.eta)
    (hunoccupied : choice.status = .unoccupied)
    (hdownInput : (ReferenceActivePhysicalStep.recordFollower view i row activation t active
      arm observation choice).downInput = some logged) :
    ActiveFollowerLogging.checkedLogging i row activation t (arm, observation) choice = .ok logged := by
  cases hcheck : ActiveFollowerLogging.checkedLogging i row activation t
      (arm, observation) choice with
  | error reason => simp [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hcheck] at hdownInput
  | ok actual =>
      have hactual : actual = logged := by
        simpa [ReferenceActivePhysicalStep.recordFollower, hunoccupied, hcheck] using hdownInput
      cases hactual
      rfl


/-- Diagnostics survive both recording failure and later release/finish
failure. This equation makes no ordinary-success assumption. -/
private theorem finishFollower_diagnostics
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hc : prepared.configuration = .ordinary choice memory) :
    let recorded := ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm observation choice
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput = recorded.downInput ∧
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).down = recorded.down := by
  dsimp only
  unfold ReferenceActivePhysicalStep.finishFollower
  rw [hc]
  dsimp only
  cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
  | error failure => exact ⟨rfl, rfl⟩
  | ok post =>
    simp only
    cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation choice memory post with
    | error failure => exact ⟨rfl, rfl⟩
    | ok pair => cases pair; exact ⟨rfl, rfl⟩

/-- A missing sender view cannot yield an accepted filtered DOWN. -/
private theorem referenceDown_none_not_accepted
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (h : (ReferenceDownReception.referenceDownCut (eta := rate.eta) p none i row t observation rate before).outcome =
      .accepted before after raw M scan registers lastService) : False := by
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · rename_i hmatches
              have hraw : (ActiveFollowerDownAcceptance.currentDecodeStep
                  p i row t observation rate before).2 = none := hmatches
              simp only [hraw, ReferenceDownReception.ordinaryParse,
                OrdinaryMessageCodec.parseDown] at h
              cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- The actual logged input and retained cut already contradict a new
acceptance: the continuing payload has exactly the seed's accepted start.
Neither successful recovery nor a successful tail is an input. -/
private theorem recordFollower_no_acceptance
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (hview : view = none ∨ ∃ selected, view = some selected ∧ selected.payload = payload)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hu : choice.status = .unoccupied)
    (hr : ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply seed)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
    (after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ)
    (hlogged : (ReferenceActivePhysicalStep.recordFollower view i row activation t active
      arm observation choice).downInput = some logged)
    (hcut : (ReferenceActivePhysicalStep.recordFollower view i row activation t active
      arm observation choice).down = some cut)
    (haccepted : cut.outcome = .accepted logged after raw M scan registers lastService) : False := by
  have hlogging := recordFollower_logging_of_downInput view i row activation t active
    arm observation choice logged hu hlogged
  have hdiagnostics := ReferenceActivePhysicalStep.recordFollower_logged view i row activation
    t active arm observation choice logged hu hlogging
  have hcutEq : cut = ReferenceDownReception.referenceDownCut p view i row t observation rate logged :=
    (Option.some.inj (hcut.symm.trans hdiagnostics.2))
  rw [hcutEq] at haccepted
  rcases hview with hnone | ⟨selected, hselected, hpayload⟩
  · rw [hnone] at haccepted
    exact referenceDown_none_not_accepted i row t observation logged after raw M scan registers
      lastService haccepted
  · rw [hselected] at haccepted
    have hfields := ReferenceActiveDataOwnership.referenceDown_accepted_fields
      selected i row t observation logged logged after raw M scan registers lastService haccepted
    have hsig : M.val.sigma = payload.sigma.val + 1 := by
      calc
        M.val.sigma = (selected.payload.downRecord
            (show ActiveRoundActions.Follower p.m from i)).val.sigma :=
          congrArg (fun record => record.val.sigma) hfields.1
        _ = (payload.downRecord (show ActiveRoundActions.Follower p.m from i)).val.sigma :=
          congrArg (fun value : ReferenceActivePhysicalStep.Payload rate =>
            (value.downRecord (show ActiveRoundActions.Follower p.m from i)).val.sigma) hpayload
        _ = payload.sigma.val + 1 := congrArg OrdinaryMessageCodec.DownFields.sigma
          (payload.downRecord_fields (show ActiveRoundActions.Follower p.m from i))
    have hstrict := ReferenceFollowerReplyChronology.referenceDownCut_accepted
      (some selected) i row t observation logged after raw M scan registers lastService haccepted
    have hlog := ActiveFollowerLogging.checkedLogging_success_frame i row activation t
      (arm, observation) choice logged hlogging
    have hstart : ReferencePrelaunchFollower.acceptedStart logged =
        ReferencePrelaunchFollower.acceptedStart choice := by
      unfold ReferencePrelaunchFollower.acceptedStart
      rw [hlog.1]
    have hreplyStart := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq hr
    have hlt := hstrict.1.1
    rw [hstart, hreplyStart, hseedStart, hsig] at hlt
    exact Nat.lt_irrefl _ hlt

/-- One physical step before replacement preserves the same collection payload
and the unoccupied follower's whole reply, allowing either player to fail into
dagger. Retained accepted DOWN diagnostics are excluded even on failed tails.
The two disjunctions are the expanded induction inputs. -/
theorem step_collection_unoccupied
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false)
    (hcoordinator : x.state.coordinator = .dagger ∨
      ∃ ledger saved, x.state.coordinator = .collection payload ledger saved)
    (hfollower : x.state.followers i = .dagger ∨
      ∃ state memory, x.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) :
    ((ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ ledger saved, (ReferenceActivePhysicalStep.step x).next.coordinator =
        .collection payload ledger saved) ∧
    ((ReferenceActivePhysicalStep.step x).next.followers i = .dagger ∨
      ∃ state memory, (ReferenceActivePhysicalStep.step x).next.followers i =
          .ordinary state memory ∧ state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) ∧
    (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) i sigma) := by
  have hview := actualSelection_view x payload hcoordinator hnotLater
  have hcoordNext : (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ ledger saved, (ReferenceActivePhysicalStep.step x).next.coordinator =
        .collection payload ledger saved := by
    rcases hcoordinator with hdagger | ⟨ledger, saved, hcollection⟩
    · exact Or.inl (ReferenceActivePhysicalStep.step_coordinator_dagger x hdagger).1
    · exact step_collection_same_payload x payload ledger saved hcollection hnotLater
  let prepared := ReferenceActivePhysicalStep.prepare x
  let followerPrepared := prepared.followers.followers i
  let observation := prepared.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  -- Keep this observer spelling throughout; its own dependent indices are
  -- the actual PREPARE projections, never reconstructed follower indices.
  have hobservation :
      (ReferenceAssignmentPayloadChronology.actualStepRecord x).output.followers i =
        ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
          followerPrepared observation := rfl
  have hchoice := actualChoice_unoccupied_reply
    (ReferenceAssignmentPayloadChronology.actualStepRecord x) i seed hfollower
  have hpreparedChoice : followerPrepared.configuration = .dagger ∨
      ∃ choice memory, followerPrepared.configuration = .ordinary choice memory ∧
        choice.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply seed :=
    hchoice
  have hnoApplied : ∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown
      (ReferenceAssignmentPayloadChronology.actualStepRecord x) i sigma := by
    intro sigma happ
    rcases happ with ⟨logged, cut, after, raw, M, scan, registers, lastService,
      hlogged, hcut, haccepted, _⟩
    rw [hobservation] at hlogged hcut
    rcases hpreparedChoice with hdagger | ⟨choice, memory, hc, hu, hr⟩
    · rw [(ReferenceActivePhysicalStep.finishFollower_dagger _ _ _ hdagger).2] at hcut
      cases hcut
    · have hdiagnostics := finishFollower_diagnostics prepared.coordinator.downView
        followerPrepared observation choice memory hc
      rw [hdiagnostics.1] at hlogged
      rw [hdiagnostics.2] at hcut
      exact recordFollower_no_acceptance payload seed hseedStart
        prepared.coordinator.downView hview followerPrepared.follower followerPrepared.row
        followerPrepared.activation followerPrepared.time followerPrepared.active
        followerPrepared.arm observation choice hu hr logged cut after raw M scan registers
        lastService hlogged hcut haccepted
  have hstepFollower :
      (ReferenceActivePhysicalStep.step x).next.followers i = .dagger ∨
        ∃ state memory, (ReferenceActivePhysicalStep.step x).next.followers i =
          .ordinary state memory ∧ state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed := by
    cases hout : (ReferenceActivePhysicalStep.step x).next.followers i with
    | dagger => exact Or.inl rfl
    | ordinary next nextMemory =>
      right
      have htail : (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
          followerPrepared observation).configuration = .ordinary next nextMemory := hout
      obtain ⟨choice, memory, post, hc, hrecord, hfinish, hlogged, hcut⟩ :=
        ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
          prepared.coordinator.downView followerPrepared observation next nextMemory htail
      have huhr : choice.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply choice = ReferenceFollowerReplyChronology.reply seed := by
        rcases hpreparedChoice with hd | ⟨actual, actualMemory, ha, hu, hr⟩
        · rw [hd] at hc
          cases hc
        · have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hc.symm.trans ha)
          exact heq.1 ▸ ⟨hu, hr⟩
      rcases ReferenceFollowerReplyChronology.recordFollower_ordinary_inversion
          prepared.coordinator.downView followerPrepared.follower followerPrepared.row
          followerPrepared.activation followerPrepared.time followerPrepared.active
          followerPrepared.arm observation choice post hrecord with hkeep | haccept
      · have hpost := hkeep.2 huhr.1
        have hframe := ReferenceFollowerReplyChronology.releaseAndFinish_frame
          followerPrepared.follower followerPrepared.row followerPrepared.time observation
          choice post next memory nextMemory hfinish
        exact ⟨next, nextMemory, rfl, (hframe.2 huhr.1).trans hpost.2,
          hframe.1.trans (hpost.1.trans huhr.2)⟩
      · rcases haccept with ⟨logged, cut, raw, M, scan, registers, lastService,
          hlog, hdown, _, haccepted, _, _⟩
        apply False.elim
        apply hnoApplied M.val.sigma
        refine ⟨logged, cut, post, raw, M, scan, registers, lastService, ?_, ?_, haccepted, rfl⟩
        · rw [hobservation, hlogged]
          exact hlog
        · rw [hobservation, hcut]
          exact hdown
  exact ⟨hcoordNext, hstepFollower, hnoApplied⟩

/-- Induction over the actual original run, from the supplied local seed
through every boundary of the failure-retaining collection window. Moving
ledgers, buffers, batches, and proposal memory come from the physical steps. -/
theorem run_collection_unoccupied_prefix
    (p : Parameters) (rate : RateInput p) (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ total)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active).finalState.coordinator =
      .collection payload ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active).finalState.followers i =
      .ordinary seed seedMemory)
    (hunoccupied : seed.status = .unoccupied)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active
    let W := (R.records.drop b).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
    let C := fun (k : ℕ) (hk : k ≤ W.length) =>
      ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + k) (by
        have hcount : R.records.length = total := by
          dsimp [R]
          exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start total hspan active
        have hdrop : (R.records.drop b).length = total - b := by
          rw [List.length_drop, hcount]
        have htake := takeWhile_length_le _
          (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.records.drop b)
        have hwindow : W.length ≤ total - b := by
          calc
            W.length ≤ (R.records.drop b).length := by
              dsimp [W]
              exact htake
            _ = total - b := hdrop
        omega) active
    ∀ k (hk : k ≤ W.length),
      ((C k hk).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          (C k hk).finalState.coordinator = .collection payload movingLedger movingSaved) ∧
      ((C k hk).finalState.followers i = .dagger ∨
        ∃ state memory,
          (C k hk).finalState.followers i = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) := by
  let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active
  let W := (R.records.drop b).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  have hcount : R.records.length = total := by
    dsimp [R]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start total hspan active
  have hdrop : (R.records.drop b).length = total - b := by
    rw [List.length_drop, hcount]
  have hlength : W.length ≤ total - b := by
    have htake := takeWhile_length_le _ (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.records.drop b)
    calc
      W.length ≤ (R.records.drop b).length := by
        dsimp [W]
        exact htake
      _ = total - b := hdrop
  let C := fun (k : ℕ) (hk : k ≤ W.length) =>
    ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + k) (by omega) active
  have hseedState :
      (C 0 (by omega)).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved, (C 0 (by omega)).finalState.coordinator =
          .collection payload movingLedger movingSaved := by
    exact Or.inr ⟨ledger, saved, hcoord⟩
  have hseedFollower :
      (C 0 (by omega)).finalState.followers i = .dagger ∨
        ∃ state memory, (C 0 (by omega)).finalState.followers i = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed := by
    exact Or.inr ⟨seed, seedMemory, hseed, hunoccupied, rfl⟩
  have hind : ∀ k (hk : k ≤ W.length),
      ((C k hk).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved, (C k hk).finalState.coordinator = .collection payload movingLedger movingSaved) ∧
      ((C k hk).finalState.followers i = .dagger ∨
        ∃ state memory, (C k hk).finalState.followers i = .ordinary state memory ∧
          state.status = .unoccupied ∧ ReferenceFollowerReplyChronology.reply state =
            ReferenceFollowerReplyChronology.reply seed) := by
    intro k
    induction k with
    | zero =>
        intro hk
        exact ⟨hseedState, hseedFollower⟩
    | succ k ih =>
        intro hk
        have hkle : k ≤ W.length := by omega
        have hprev := ih hkle
        have hwindow : k < W.length := by omega
        have hdropIdx : k < (R.records.drop b).length := by
          have htake := takeWhile_length_le _
            (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
              !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.records.drop b)
          dsimp [W] at hwindow
          omega
        have hindex : b + k < total := by omega
        have hindexRecords : b + k < R.records.length := by
          rw [hcount]
          exact hindex
        have htag : ReferenceCollectionPhaseHistory.laterChosen
            ((R.records.drop b)[k]'hdropIdx).input = false := by
          have hmemW : W[k]'hwindow ∈ W := List.getElem_mem hwindow
          have hgetTake : W[k]'hwindow = (R.records.drop b)[k]'hdropIdx := by
            simpa [W] using getElem_takeWhile_eq _
              (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
                !ReferenceCollectionPhaseHistory.laterChosen r.input)
              (R.records.drop b) k (by simpa [W] using hwindow)
          have hmem : (R.records.drop b)[k]'hdropIdx ∈ W := by
            rw [← hgetTake]
            exact hmemW
          have hpred := List.mem_takeWhile_imp hmem
          simpa using hpred
        let record := R.records[b + k]
        have hstateEq := (run_prefix_endpoints initial rows J rewards start total hspan active
          (b + k) hindex).1
        have htagRecord : ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
          have hget : (R.records.drop b)[k]'hdropIdx = R.records[b + k] := by
            rw [List.getElem_drop]
          change ReferenceCollectionPhaseHistory.laterChosen (R.records[b + k]).input = false
          rw [← hget]
          exact htag
        have hrecCoord : record.input.state.coordinator = .dagger ∨
            ∃ movingLedger movingSaved,
              record.input.state.coordinator = .collection payload movingLedger movingSaved := by
          rw [← hstateEq]
          exact hprev.1
        have hrecFollower : record.input.state.followers i = .dagger ∨
            ∃ state memory, record.input.state.followers i = .ordinary state memory ∧
              state.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed := by
          rw [← hstateEq]
          exact hprev.2
        have hstep := step_collection_unoccupied payload i seed hseedStart record.input
          htagRecord hrecCoord hrecFollower
        have houtput : (C (k + 1) hk).finalState = record.output.next := by
          simpa [C, record, Nat.add_assoc] using
            (run_prefix_endpoints initial rows J rewards start total hspan active
              (b + k) hindex).2
        rw [houtput]
        have hstep' := hstep
        rw [← record.output_eq] at hstep'
        exact ⟨hstep'.1, hstep'.2.1⟩
  exact hind

/-- Every retained record excludes accepted/applied DOWN for this follower;
no ordinary-output premise is needed, so later failures remain covered. -/
theorem run_collection_no_appliedDown
    (p : Parameters) (rate : RateInput p) (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ total)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active).finalState.coordinator =
      .collection payload ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active).finalState.followers i =
      .ordinary seed seedMemory)
    (hunoccupied : seed.status = .unoccupied)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active
    let W := (R.records.drop b).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
    ∀ k, k < W.length → ∀ (hrecord : b + k < R.records.length), ∀ sigma,
      ¬ ReferenceFollowerReplyChronology.appliedDown (R.records.get ⟨b + k, hrecord⟩) i sigma := by
  intro R W k hk hindexRecords sigma
  have hprefix := run_collection_unoccupied_prefix p rate initial rows J rewards start total hspan active
    b hb payload ledger saved hcoord i seed seedMemory hseed hunoccupied hseedStart
  dsimp only at hprefix
  have hcount : R.records.length = total := by
    dsimp [R]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start total hspan active
  have hindex : b + k < total := by
    rw [hcount] at hindexRecords
    exact hindexRecords
  let record := R.records.get ⟨b + k, hindexRecords⟩
  have hstate := hprefix k (Nat.le_of_lt hk)
  have hinput := (run_prefix_endpoints initial rows J rewards start total hspan active (b + k) hindex).1
  have hdropIdx : k < (R.records.drop b).length := by
    have htake := takeWhile_length_le _
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.records.drop b)
    dsimp [W] at hk
    omega
  have hdropEq : (R.records.drop b)[k]'hdropIdx = record := by
    simp only [List.getElem_drop]
    simp [record, List.get_eq_getElem]
  have hgetRecord : R.records[b + k] = record := by
    simp [record, List.get_eq_getElem]
  have hmemW : W[k]'hk ∈ W := List.getElem_mem hk
  have hgetTake : W[k]'hk = (R.records.drop b)[k]'hdropIdx := by
    simpa [W] using getElem_takeWhile_eq _
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input)
      (R.records.drop b) k (by simpa [W] using hk)
  have hmem : (R.records.drop b)[k]'hdropIdx ∈ W := by
    rw [← hgetTake]
    exact hmemW
  have htag := List.mem_takeWhile_imp hmem
  have htagRecord : ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
    rw [← hdropEq]
    simpa using htag
  have hcoordRec : record.input.state.coordinator = .dagger ∨
      ∃ movingLedger movingSaved,
        record.input.state.coordinator = .collection payload movingLedger movingSaved := by
    rw [← hgetRecord, ← hinput]
    exact hstate.1
  have hfollowRec : record.input.state.followers i = .dagger ∨
      ∃ state memory, record.input.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed := by
    rw [← hgetRecord, ← hinput]
    exact hstate.2
  have hstep := step_collection_unoccupied payload i seed hseedStart
    record.input htagRecord hcoordRec hfollowRec
  have hactual : ReferenceAssignmentPayloadChronology.actualStepRecord record.input = record := by
    cases record with
    | mk input output output_eq =>
      cases output_eq
      rfl
  have hno := hstep.2.2 sigma
  rw [hactual] at hno
  exact hno

/-- Every existing boundary record has a dagger or unoccupied prepared
choice with the seed reply. At the window endpoint the remaining record is
proved to be the first later-chosen round. No claim concerns its new-word tail,
and no endpoint record is asserted when the original run is exhausted. -/
theorem run_collection_boundary_choice_unoccupied
    (p : Parameters) (rate : RateInput p) (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (b : ℕ) (hb : b ≤ total)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active).finalState.coordinator =
      .collection payload ledger saved)
    (i : Fin (p.m - 1)) (seed : ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : (ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active).finalState.followers i =
      .ordinary seed seedMemory)
    (hunoccupied : seed.status = .unoccupied)
    (hseedStart : ReferencePrelaunchFollower.acceptedStart seed = payload.sigma.val + 1) :
    let R := ReferenceActivePhysicalHorizon.run initial rows J rewards start total hspan active
    let W := (R.records.drop b).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
    ∀ k, k ≤ W.length → ∀ (hrecord : b + k < R.records.length),
      (k = W.length →
        ReferenceCollectionPhaseHistory.laterChosen (R.records.get ⟨b + k, hrecord⟩).input = true) ∧
      ((ReferenceFollowerFixedReply.actualChoice (R.records.get ⟨b + k, hrecord⟩) i).configuration = .dagger ∨
        ∃ state memory,
          (ReferenceFollowerFixedReply.actualChoice (R.records.get ⟨b + k, hrecord⟩) i).configuration = .ordinary state memory ∧
          state.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed) := by
  intro R W k hk hindexRecords
  have hprefix := run_collection_unoccupied_prefix p rate initial rows J rewards start total hspan active
    b hb payload ledger saved hcoord i seed seedMemory hseed hunoccupied hseedStart
  dsimp only at hprefix
  have hcount : R.records.length = total := by
    dsimp [R]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start total hspan active
  have hindex : b + k < total := by
    rw [hcount] at hindexRecords
    exact hindexRecords
  let record := R.records.get ⟨b + k, hindexRecords⟩
  have hstate := hprefix k hk
  have hgetRecord : R.records[b + k] = record := by
    simp [record, List.get_eq_getElem]
  have hinput := (run_prefix_endpoints initial rows J rewards start total hspan active (b + k) hindex).1
  have hchoiceIn : record.input.state.followers i = .dagger ∨
      ∃ state memory, record.input.state.followers i = .ordinary state memory ∧
        state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply seed := by
    rw [← hgetRecord, ← hinput]
    exact hstate.2
  have hchoice := actualChoice_unoccupied_reply record i seed hchoiceIn
  have htag : k = W.length → ReferenceCollectionPhaseHistory.laterChosen record.input = true := by
    intro hkEnd
    have hkdrop : k < (R.records.drop b).length := by
      have hdropLen : (R.records.drop b).length = total - b := by
        rw [List.length_drop, hcount]
      omega
    have hlen : W.length = k := hkEnd.symm
    have hnot := takeWhile_boundary_not _ (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.laterChosen r.input) (R.records.drop b) k hlen hkdrop
    have hdropEq : (R.records.drop b)[k]'hkdrop = record := by
      simp only [List.getElem_drop]
      simp [record, List.get_eq_getElem]
    have hnotRecord : (!ReferenceCollectionPhaseHistory.laterChosen record.input) = false := by
      rw [← hdropEq]
      exact hnot
    simpa using hnotRecord
  exact ⟨htag, hchoice⟩

end Bandits.Support.ReferenceCollectionUnoccupiedHistory

end
