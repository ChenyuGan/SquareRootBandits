/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveGuardedConditionalService
public import Bandits.Support.ReferenceSourceReleaseWaitingStrictPast
public import Bandits.Support.ReferencePhysicalReleaseQuota

/-!
# Actual first-live source release support

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,180-240,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module constructs the last confirmation from a literal actual gate query,
identifies the complete finite gate list with its first-live release suffix,
and transports physical quotas and whole-payload source readouts to that list.
Coordinator safety is consumed explicitly; follower failures remain governed by
the original execution. No stopping law, inspected conditional expectation,
failure or cost bound, or source-facing waiting or regret closure is asserted.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveSourceReleaseSupport

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActivePhysicalStepMeasurability
open ReferenceRetainedReleasePhaseObservation
open ReferenceAssignmentPayloadPersistence
open scoped Classical

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The original physical record type, without a replacement run. -/
abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
/-- The existing dependent arm-selection type on a physical input. -/
abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)

private theorem local_gate_not_cutoff (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (b : ℕ) (hg : localReleaseGate rate b x.time (encodeState x.state) = true) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  cases hphase : x.state.coordinator with
  | first => simp [localReleaseGate, encodeState, encodeCoordinator, hphase] at hg
  | collection payload ledger proposal =>
      simp [localReleaseGate, encodeState, encodeCoordinator, hphase] at hg
  | dagger => simp [localReleaseGate, encodeState, encodeCoordinator, hphase] at hg
  | live r q base =>
      have hg' := hg
      simp only [localReleaseGate, encodeState, encodeCoordinator, hphase,
        Bool.and_eq_true, decide_eq_true_eq] at hg'
      have hprefix := hg'.1
      have hcutoff : r.priorClock.u = none := by
        simpa only [encodeLive] using hprefix.2
      have hresult := hg'.2
      split at hresult
      · contradiction
      · rename_i started hcall'
        have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
            (decodeLiveRegisters r.payload (encodeLive r q base)) started := by
          simpa only [decide_eq_true_eq] using hresult
        have hclock : started.clock = r.priorClock := by
          have h := (localReleaseGate_startFrame_iff rate x.time r.payload
            (encodeLive r q base) started).mp hframe
          simpa only [encodeLive] using h.1
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        simp only [ReferenceActivePhysicalStep.prepare,
          ReferenceActivePhysicalStep.dispatch, CoordinatorRoundDispatch.dispatch, hphase]
        cases hout : CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x r q base) with
        | cutoffChosen dispatched hstart ledger hinitial hledger hdomains hclockCut
            hpending hnoAssignment selected =>
            have hlocal : CoordinatorPhaseClock.startRound p rate.eta.val x.time
                r.priorClock r.clockPending = .ok started := by
              have heq := localReleaseStartResult_eq_decoded rate x.time r.payload
                (encodeLive r q base)
              rw [hcall'] at heq
              simpa only [encodeLive, decodeLiveRegisters,
                ReferenceActivePhysicalStep.liveInput,
                liveRegistersAt,
                CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq] using heq.symm
            have hsame : started = dispatched.startResult := by
              have hd := hstart
              have hstarted : Except.ok started = Except.ok dispatched.startResult :=
                hlocal.symm.trans (by simpa only [ReferenceActivePhysicalStep.liveInput,
                  liveRegistersAt,
                  CoordinatorLiveChoiceRecorderStep.Registers.clockPending_eq] using hd)
              exact Except.ok.inj hstarted
            have hcut := hclockCut
            rw [← hsame] at hcut
            have hnone : started.clock.u = none := by
              rw [hclock, hcutoff]
            have hsome : started.clock.u = some x.time := by
              have hproj := congrArg CoordinatorPhaseClock.ClockRegisters.u hcut
              simpa only [ReferenceActivePhysicalStep.liveInput, liveRegistersAt] using hproj
            rw [hnone] at hsome
            cases hsome
        | _ => rfl

private theorem live_successor_not_cutoff (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
    (base : Fin (p.m - 1) → ℕ)
    (hout : (ReferenceActivePhysicalStep.step x).next.coordinator = .live next owned base) :
    ReferenceCollectionPhaseHistory.cutoffChosen x = false := by
  cases htag : ReferenceCollectionPhaseHistory.cutoffChosen x with
  | false => rfl
  | true =>
      unfold ReferenceCollectionPhaseHistory.cutoffChosen at htag
      cases hpre : (ReferenceActivePhysicalStep.prepare x).coordinator with
      | live r q oldBase outcome =>
          cases outcome with
          | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected =>
              have hcollection := by
                simpa only [ReferenceActivePhysicalStep.liveInput,
                  ReferenceActivePhysicalStep.liveRegistersAt] using
                  (ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
                    (ReferenceActivePhysicalStep.prepare x) r.payload
                    (ReferenceActivePhysicalStep.sharedLedger ledger) dispatched.startResult
                    (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights)
              have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
                (ReferenceActivePhysicalStep.prepare x) r q oldBase
                (.cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected)
                hpre
              have htarget : (ReferenceActivePhysicalStep.prepare x).observeCoordinator.configuration =
                  .live next owned base := (ReferenceActivePhysicalStep.step_next_fields x).1.symm.trans hout
              rw [hobs] at htarget
              by_cases hn : (ReferenceActivePhysicalStep.DispatchCut.live r q oldBase
                  (.cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected)).selection = none
              · simp only [hn, ReferenceActivePhysicalStep.coordinatorFailure] at htarget
                cases htarget
              · simp only [hn] at htarget
                rcases hcollection with hdagger | ⟨payload, oldLedger, proposal, hcol⟩
                · have hbad : CoordinatorConfiguration.dagger = .live next owned base := by
                    exact hdagger.symm.trans htarget
                  cases hbad
                · have hbad : CoordinatorConfiguration.collection payload oldLedger proposal =
                      .live next owned base := by
                    exact hcol.symm.trans htarget
                  cases hbad
          | _ => simp [hpre] at htag
      | _ => simp [hpre] at htag

private theorem takeWhile_length_gt_of_prefix_true {α : Type*}
    (predicate : α → Bool) (xs : List α) (n : ℕ) (hn : n < xs.length)
    (htrue : ∀ j (_hjn : j ≤ n) (hjl : j < xs.length),
      predicate (xs[j]'hjl) = true) :
    n < (xs.takeWhile predicate).length := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => simp at hn
      | cons head tail =>
          have hh := htrue 0 le_rfl (by simp)
          simp only [List.getElem_cons_zero] at hh
          simp [hh]
  | succ n ih =>
      cases xs with
      | nil => simp at hn
      | cons head tail =>
          have hh := htrue 0 (by omega) (by simp)
          simp only [List.getElem_cons_zero] at hh
          have hn' : n < tail.length := by simpa using hn
          have htail : ∀ j (hjn : j ≤ n) (hjl : j < tail.length),
              predicate (tail[j]'hjl) = true := by
            intro j hj hjl
            have hshift := htrue (j + 1) (by omega) (by simp; omega)
            simpa using hshift
          have hrec := ih tail hn' htail
          simp [hh] at hrec ⊢
          omega

private theorem takeWhile_length_le {α : Type} (predicate : α → Bool)
    (xs : List α) : (xs.takeWhile predicate).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : predicate head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

private theorem getElem_takeWhile_eq {α : Type} (predicate : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < (xs.takeWhile predicate).length) :
    (xs.takeWhile predicate)[k] =
      xs[k]'(Nat.lt_of_lt_of_le hk (takeWhile_length_le predicate xs)) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases hp : predicate head with
      | false => simp [List.takeWhile, hp] at hk
      | true =>
          cases k with
          | zero => simp [List.takeWhile, hp]
          | succ k =>
              have htail : k < (tail.takeWhile predicate).length := by
                simpa [List.takeWhile, hp] using hk
              simpa only [List.takeWhile, hp, List.getElem_cons_succ] using ih k htail

private theorem firstLive_record_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)[j.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start j.val
        (by
          have hle : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
              (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length ≤ count := by
            calc
              _ ≤ (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records.length :=
                takeWhile_length_le _ _
              _ = count := ReferenceActivePhysicalHorizon.run_record_count
                initial rows J rewards start count hspan active
          have hj := j.isLt
          omega) active := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let predicate : Record (p := p) (rate := rate) → Bool :=
    fun r => !ReferenceCollectionPhaseHistory.cutoffChosen r.input
  have hle : W.length ≤ E.records.length := by
    dsimp only [W, ReferenceFirstLiveConfirmationHistory.firstLiveWindow, E]
    exact takeWhile_length_le predicate _
  have hjcount : j.val < count := by
    have hj := j.isLt
    change j.val < W.length at hj
    have hle' : W.length ≤ count := by
      calc
        W.length ≤ E.records.length := hle
        _ = count := ReferenceActivePhysicalHorizon.run_record_count
          initial rows J rewards start count hspan active
    omega
  have htakeBound : j.val < (E.records.takeWhile predicate).length := by
    change j.val < W.length
    exact j.isLt
  have htake : W[j.val]'j.isLt =
      E.records[j.val]'(Nat.lt_of_lt_of_le htakeBound (takeWhile_length_le predicate E.records)) := by
    dsimp only [W, ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    exact getElem_takeWhile_eq predicate E.records j.val htakeBound
  have hrun := ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards start
    active count hspan ⟨j.val, hjcount⟩
  dsimp only [E] at hrun
  rw [htake]
  exact hrun

/-- A true gate at physical index `k` is reached before the actual first
chosen cutoff. The proof follows the real predecessor registers backward to
the `.first` launch, using the same whole run and its timestamped payload. -/
private theorem actual_gate_index_firstLiveWindow
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) (k : Fin count)
    (hgate : localReleaseGate rate start
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k.val
        (by have hk := k.isLt; omega) active).input.time
      (encodeState (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k.val
        (by have hk := k.isLt; omega) active).input.state) = true) :
    k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length := by
  let preRun (n : ℕ) (_hn : n ≤ k.val) := ReferenceActivePhysicalHorizon.run
    initial rows J rewards start n (by have hbound := _hn; have hk := k.isLt; omega) active
  let record (n : ℕ) (_hn : n ≤ k.val) := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial rows J rewards start n (by have hbound := _hn; have hk := k.isLt; omega) active
  obtain ⟨gateRegs, gateOwned, gateBase, hgateLive, hgateBirth, _, _, _⟩ :=
    ReferenceLocalReleaseGateChronology.gate_live start
      (record k.val le_rfl).input.time (record k.val le_rfl).input.state hgate
  have hgatePrefix : (preRun k.val le_rfl).finalState.coordinator =
      .live gateRegs gateOwned gateBase := by
    have hinput : (record k.val le_rfl).input.state = (preRun k.val le_rfl).finalState := rfl
    rw [← hinput]
    exact hgateLive
  have hkpos : 0 < k.val := by
    by_contra hnot
    have hkzero : k.val = 0 := by omega
    have hgateLiveZero : (record 0 (by omega)).input.state.coordinator =
        .live gateRegs gateOwned gateBase := by
      simpa only [hkzero] using hgateLive
    have hinitialState : (record 0 (by omega)).input.state = initial := rfl
    have hfirstCoord := congrArg (fun state : ReferenceActivePhysicalHorizon.State p rate =>
      state.coordinator) hinitialState
    rw [hfirst] at hfirstCoord
    rw [hfirstCoord] at hgateLiveZero
    cases hgateLiveZero
  have hback : ∀ d n, n + d = k.val → 0 < n → (hnk : n ≤ k.val) →
      ∃ regs owned base, (preRun n hnk).finalState.coordinator = .live regs owned base ∧
        regs.payload.sigma.val = start := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro n hsum hn hnk
        cases d with
        | zero =>
            have hnk : n = k.val := by omega
            subst n
            exact ⟨gateRegs, gateOwned, gateBase, hgatePrefix, hgateBirth⟩
        | succ d =>
            have hnextSum : (n + 1) + d = k.val := by omega
            obtain ⟨next, nextOwned, nextBase, hnext, hnextBirth⟩ :=
              ih d (by omega) (n + 1) hnextSum (by omega) (by omega)
            have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
              initial rows J rewards start n (by have hk := k.isLt; omega) active
            have houtput : (record n hnk).output.next.coordinator =
                .live next nextOwned nextBase := by
              have hcoord := congrArg
                (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator)
                hsuccessor
              exact hcoord.symm.trans hnext
            have hstepOutput : (ReferenceActivePhysicalStep.step (record n hnk).input).next.coordinator =
                .live next nextOwned nextBase := by
              simpa only [record, ReferenceAssignmentPayloadChronology.actualRunRecordAt] using houtput
            obtain ⟨prev, prevOwned, prevBase, hprev, hprevBirth, _⟩ :=
              ReferenceLocalReleaseGateChronology.step_old_live_predecessor
                (record n hnk).input start next nextOwned nextBase hstepOutput hnextBirth (by
                  have htime : (record n hnk).input.time.val = start + n := by
                    simp [record, ReferenceAssignmentPayloadChronology.actualRunRecordAt,
                      ReferenceActivePhysicalHorizon.roundInputAt]
                  omega)
            have hinput : (record n hnk).input.state = (preRun n hnk).finalState := rfl
            refine ⟨prev, prevOwned, prevBase, ?_, hprevBirth⟩
            rw [← hinput]
            exact hprev
  have hcutoff : ∀ j (hj : j ≤ k.val),
      ReferenceCollectionPhaseHistory.cutoffChosen (record j (by omega)).input = false := by
    intro j hj
    by_cases hjzero : j = 0
    · subst j
      have hstate : (record 0 (by omega)).input.state = initial := rfl
      have hcoord := congrArg
        (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator) hstate
      rw [hfirst] at hcoord
      have hdispatch := ReferenceActivePhysicalStep.dispatch_first (record 0 (by omega)).input hcoord
      have hprepared : (ReferenceActivePhysicalStep.prepare (record 0 (by omega)).input).coordinator =
          .first (CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput (record 0 (by omega)).input) :
              CoordinatorRoundDispatch.FirstOutcome
                (ReferenceActivePhysicalStep.firstInput (record 0 (by omega)).input)) := by
        simpa only [ReferenceActivePhysicalStep.prepare] using hdispatch
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      rw [hprepared]
    · by_cases hjk : j = k.val
      · subst j
        exact local_gate_not_cutoff (record k.val le_rfl).input start hgate
      · have hjlt : j < k.val := by omega
        obtain ⟨next, nextOwned, nextBase, hnext, _⟩ :=
          hback (k.val - (j + 1)) (j + 1) (by omega) (by omega) (by omega)
        have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
          initial rows J rewards start j (by have hk := k.isLt; omega) active
        have houtput : (record j (by omega)).output.next.coordinator = .live next nextOwned nextBase := by
          have hcoord := congrArg
            (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator)
            hsuccessor
          exact hcoord.symm.trans hnext
        have hstepOutput : (ReferenceActivePhysicalStep.step (record j (by omega)).input).next.coordinator =
            .live next nextOwned nextBase := by
          simpa only [record, ReferenceAssignmentPayloadChronology.actualRunRecordAt] using houtput
        exact live_successor_not_cutoff (record j (by omega)).input next nextOwned nextBase hstepOutput
  let records := (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records
  have hlength : k.val < records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact k.isLt
  apply takeWhile_length_gt_of_prefix_true
    (fun r : Record => !ReferenceCollectionPhaseHistory.cutoffChosen r.input) records k.val hlength
  intro j hj hjlen
  have hjcount : j < count := by
    rw [ReferenceActivePhysicalHorizon.run_record_count] at hjlen
    exact hjlen
  let fj : Fin count := ⟨j, hjcount⟩
  have hrecord := ReferenceLocalReleaseGateChronology.run_record_at
    initial rows J rewards start active count hspan fj
  have hrecord' : records[j]'hjlen = record j (by omega) := by
    simpa only [records, fj, record, ReferenceLocalReleaseGateChronology.run_record_at] using hrecord
  rw [hrecord']
  have hcut := hcutoff j hj
  simp [hcut]

/-- A true gate query on the corrected source run belongs to its actual
first-live window. The launch, original rows and selected source index are
computed from the same source input. -/
theorem actual_first_live_gate_in_window
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    (hspan : s + count ≤ p.T) →
    (hcross : I.crossing.isSome = true) →
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
      hcross s count rfl hspan
    (k : Fin count) →
    let r := R.records[k.val]'(by
      simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)
    localReleaseGate rate s r.input.time (encodeState r.input.state) = true →
    k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length := by
  intro I s hspan hcross R k r hgate
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate source rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [initial, s, I] using hcanonical.2.1
  have hfirst : initial.coordinator = .first := by
    simpa only [initial, I] using hcanonical.1
  have hbound : k.val < R.records.length := by
    change k.val <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records.length
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact k.isLt
  have hrecord : R.records[k.val]'hbound =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive := by
    dsimp only [R, rows, J, initial, ReferenceLocalReleaseGateChronology.sourceRun]
    exact ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards s hactive
      count hspan k
  have hgate' : localReleaseGate rate s
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive).input.time
      (encodeState (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive).input.state) = true := by
    simpa only [r, hrecord] using hgate
  have hmem := actual_gate_index_firstLiveWindow initial rows J rewards s count hspan
    hactive hfirst k hgate'
  simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun, initial, rows, J] using hmem

/-- At an actual true gate, missing-set provenance identifies the selected
whole payload from the first installation and shows that this very selection
has empty pre-choice pending set. -/
theorem actual_first_live_gate_selected_empty
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    (hspan : s + count ≤ p.T) →
    (hcross : I.crossing.isSome = true) →
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
      hcross s count rfl hspan
    (k : Fin count) →
    let r := R.records[k.val]'(by
      simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)
    (hgate : localReleaseGate rate s r.input.time (encodeState r.input.state) = true) →
    ∃ selected : Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      ∃ M : ReferenceActivePhysicalStep.Payload rate,
        selected.view.payload = M ∧ selected.view.pendingAtChoice = ∅ ∧ M.sigma.val = s := by
  intro I s hspan hcross R k r hgate
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate source rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [initial, s, I] using hcanonical.2.1
  have hfirst : initial.coordinator = .first := by
    simpa only [initial, I] using hcanonical.1
  have hbound : k.val < R.records.length := by
    change k.val <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records.length
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact k.isLt
  have hrecord : R.records[k.val]'hbound =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive := by
    change (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records[k.val]'hbound = _
    exact ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards s hactive
      count hspan k
  have hgate' : localReleaseGate rate s
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive).input.time
      (encodeState (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive).input.state) = true := by
    simpa only [r, hrecord] using hgate
  have hindex := actual_first_live_gate_in_window source rewards C_star C_h count hspan hcross k hgate
  let L := ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records
  have hget : L[k.val]'(by simpa only [L] using hindex) = r := by
    let predicate : Record (p := p) (rate := rate) → Bool :=
      fun x => !ReferenceCollectionPhaseHistory.cutoffChosen x.input
    have htakeBound : k.val < (R.records.takeWhile predicate).length := by
      simpa only [predicate, L, ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using hindex
    change (R.records.takeWhile predicate)[k.val]'htakeBound = R.records[k.val]'hbound
    exact getElem_takeWhile_eq predicate R.records k.val htakeBound
  have hprovenance := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    initial rows J rewards s count hspan hactive hfirst
  rcases hprovenance with hzero | ⟨hW, firstSelected, firstInstalled, firstArm,
      hrow0first, hdispatch, hinstalled, hinitialPending, hstartPending,
      hselected0, hpayload0, hpending0, hstarted0, hrows⟩
  · have hlength : L.length = 0 := by
      simpa only [L, R, ReferenceLocalReleaseGateChronology.sourceRun] using hzero
    rw [hlength] at hindex
    omega
  · have hrowBound : k.val < L.length := by simpa only [L] using hindex
    obtain ⟨record, hrecordL, selected, hselected, hpayload, hphase,
      next, nextOwned, nextBase, hout, hnextPayload, hupdate, hcoverage⟩ :=
      hrows ⟨k.val, hrowBound⟩
    have hrecordR : record = r := hrecordL.trans hget
    cases hrecordR
    obtain ⟨gateRegs, gateOwned, gateBase, hgateLive, hgateBirth, hgatePending,
      hgateClock, hgateClockU⟩ :=
      ReferenceLocalReleaseGateChronology.gate_live s r.input.time r.input.state hgate
    have hlive : r.input.state.coordinator = .live gateRegs gateOwned gateBase := by
      exact hgateLive
    have hphase' : selected.view.payload = gateRegs.payload ∧
        selected.view.pendingAtChoice = gateRegs.pendingAtChoice ∧
        selected.started.pending = gateRegs.pendingAtChoice := by
      simpa only [hlive] using hphase
    refine ⟨selected, ?_⟩
    constructor
    · exact hselected
    · refine ⟨firstInstalled.registers.payload, ?_⟩
      refine ⟨hpayload, ?_, ?_⟩
      · rw [hphase'.2.1, hgatePending]
      · calc
          firstInstalled.registers.payload.sigma.val = selected.view.payload.sigma.val := by
            rw [← hpayload]
          _ = gateRegs.payload.sigma.val := by rw [hphase'.1]
          _ = s := hgateBirth

private theorem filter_eq_take_drop {α : Type*} (xs : List α) (gate : α → Bool)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ xs.length)
    (hgate : ∀ j (hj : j < xs.length), gate xs[j] = true ↔ a ≤ j ∧ j < b) :
    xs.filter gate = (xs.take b).drop a := by
  induction xs generalizing a b with
  | nil => simp_all
  | cons x xs ih =>
      cases b with
      | zero =>
          have ha : a = 0 := by omega
          subst a
          apply List.filter_eq_nil_iff.mpr
          intro r hr htrue
          obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hr
          have h := (hgate j hj).mp (by simpa only [heq] using htrue)
          omega
      | succ b =>
          have hb' : b ≤ xs.length := by simp only [List.length_cons] at hb; omega
          cases a with
          | zero =>
              have hx : gate x = true := (hgate 0 (by simp)).mpr (by omega)
              have ht : ∀ j (hj : j < xs.length), gate xs[j] = true ↔ 0 ≤ j ∧ j < b := by
                intro j hj
                have hh := hgate (j + 1) (by simp only [List.length_cons]; omega)
                simpa only [List.getElem_cons_succ, Nat.zero_le, true_and,
                  Nat.add_lt_add_iff_right] using hh
              simpa only [List.filter_cons, hx, List.take_succ_cons, List.drop_zero,
                Bool.true_eq, ↓reduceIte] using congrArg (List.cons x) (ih 0 b (by omega) hb' ht)
          | succ a =>
              have hx : gate x = false := by
                cases he : gate x with
                | false => rfl
                | true => have hh := (hgate 0 (by simp)).mp he; omega
              have ht : ∀ j (hj : j < xs.length), gate xs[j] = true ↔ a ≤ j ∧ j < b := by
                intro j hj
                have hh := hgate (j + 1) (by simp only [List.length_cons]; omega)
                simpa only [List.getElem_cons_succ, Nat.add_le_add_iff_right,
                  Nat.add_lt_add_iff_right] using hh
              simpa only [List.filter_cons, hx, List.take_succ_cons, List.drop_succ_cons,
                Bool.false_eq_true, ↓reduceIte] using ih a b (by omega) hb' ht

private theorem gate_of_live_frame (x : RoundInput p rate) (b : ℕ)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base) (hb : r.payload.sigma.val = b)
    (he : r.pendingAtChoice = ∅) (hs : r.priorClock.sigma = some r.payload.sigma)
    (hu : r.priorClock.u = none) (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
      r.clockPending = .ok started)
    (hf : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (liveRegistersAt r x.time) started) :
    localReleaseGate rate b x.time (encodeState x.state) = true := by
  have hstart' : localReleaseStartResult rate x.time (encodeLive r q base) = .ok started := hstart
  have hf' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (decodeLiveRegisters r.payload (encodeLive r q base)) started := by
    simpa only [CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame,
      decodeLiveRegisters, encodeLive, liveRegistersAt,
      CoordinatorLiveChoiceRecorderStep.Registers.clockPending] using hf
  simp only [localReleaseGate, encodeState, encodeCoordinator, hc]
  change (decide (r.payload.sigma.val = b) && decide (r.pendingAtChoice = ∅) &&
    decide (r.priorClock.sigma = some r.payload.sigma) && decide (r.priorClock.u = none) &&
    (match localReleaseStartResult rate x.time (encodeLive r q base) with
      | .error _ => false
      | .ok result => decide (CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
          (decodeLiveRegisters r.payload (encodeLive r q base)) result))) = true
  rw [hstart']
  simp only [hb, he, hs, hu, hf', decide_true, Bool.and_self]

variable (rate)

/-- The actual queried gate determines a real last confirmation. The least
empty pre-choice set is selected from the actual first-live records, and its
ordinary next registers are the physical successor. Q's release lemma is
applied only after its four branch inputs have been constructed here. -/
theorem actual_first_live_gate_last_confirmation
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    (hcross : I.crossing.isSome = true) →
    (hspan : s + count ≤ p.T) →
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
      hcross s count rfl hspan
    (k : Fin count) →
    let r := R.records[k.val]'(by
      simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)
    (hgate : localReleaseGate rate s r.input.time (encodeState r.input.state) = true) →
    k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length ∧
    ∃ c : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length,
      c.val < k.val ∧
      ∃ selected : Selection
          ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].input),
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].output.preparation.coordinator.selection =
          some selected ∧
        ∃ M : ReferenceActivePhysicalStep.Payload rate,
          M.sigma.val = s ∧
          ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
          selected.view.payload = M ∧
          selected.view.pendingAtChoice =
            {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].input.row.2
                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].input.time).1)} ∧
          ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
            ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val]) selected ∧
          ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
              ∃ base : Fin (p.m - 1) → ℕ,
                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].output.next.coordinator =
                  .live next owned base ∧
                next.payload = M ∧ next.pendingAtChoice = ∅ ∧
                let support := R.records.filter (fun record =>
                  localReleaseGate rate s record.input.time (encodeState record.input.state))
                support = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).drop
                    (c.val + 1) ∧
                (∀ a b (hab : a ≤ b) (hb : b < support.length),
                  ReferencePhysicalReleaseQuota.pendingSet M (support[b]'hb) ⊆
                    ReferencePhysicalReleaseQuota.pendingSet M (support[a]'(lt_of_le_of_lt hab hb))) ∧
                (∀ i n (_hn : n ≤ support.length),
                  ReferencePhysicalReleaseQuota.releaseCount M (support.take n) i ≤ 1 ∧
                  ReferencePhysicalReleaseQuota.upCount M (support.take n) i ≤ 1 ∧
                  ReferencePhysicalReleaseQuota.dataCount M (support.take n) i ≤ 1) ∧
                (∀ i n (hn : n < support.length),
                  i ∈ ReferencePhysicalReleaseQuota.pendingSet M (support[n]'hn) →
                  ReferencePhysicalReleaseQuota.releaseCount M (support.take n) i = 0 ∧
                  ReferencePhysicalReleaseQuota.upCount M (support.take n) i = 0 ∧
                  ReferencePhysicalReleaseQuota.dataCount M (support.take n) i = 0) ∧
                (∀ n : Fin support.length,
                  (support[n.val]'n.isLt).input.time.val + 1 = s + c.val + 2 + n.val) ∧
                (∀ record ∈ support,
                  ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator = some M ∧
                  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                    record.input.time source = some record ∧
                  ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s
                    record.input.time source = some (true,
                      some (ReferencePhysicalReleaseQuota.pendingSet M record)) ∧
                  ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h s
                    record.input.time source = ReferencePhysicalReleaseQuota.pendingSet M record ∧
                  ∀ i,
                    ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i
                      record.input.time source = ReferencePhysicalReleaseQuota.upFlag M record i ∧
                    ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i
                      record.input.time source = ReferencePhysicalReleaseQuota.dataFlag M record i ∧
                    ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i
                      record.input.time source = ReferencePhysicalReleaseQuota.releaseFlag M record i) := by
  intro I s hcross hspan R k r hgate
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate source rewards C_star C_h hcross
  let rows := source.1.2
  let J := ActualInitializationPhysicalStep.selectedRowIndex p source
  have hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate source rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [initial, s, I] using hcanonical.2.1
  have hfirst : initial.coordinator = .first := by
    simpa only [initial, I] using hcanonical.1
  have hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    simpa only [initial, I] using hcanonical.2.2
  have hbound : k.val < R.records.length := by
    change k.val <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records.length
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact k.isLt
  have hrecord : R.records[k.val]'hbound =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive := by
    change (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records[k.val]'hbound = _
    exact ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards s hactive
      count hspan k
  have hgate' : localReleaseGate rate s
      (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive).input.time
      (encodeState (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
        (by have hk := k.isLt; omega) hactive).input.state) = true := by
    simpa only [r, hrecord] using hgate
  have hindex := actual_gate_index_firstLiveWindow initial rows J rewards s count hspan
    hactive hfirst k hgate'
  let L := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
    (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records
  have hrecordAtK := firstLive_record_eq_actualRunRecordAt initial rows J rewards s
    count hspan hactive ⟨k.val, hindex⟩
  have hgetK : L[k.val]'hindex = r := by
    calc
      L[k.val]'hindex =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s k.val
            (by have hk := k.isLt; omega) hactive := by
        simpa only [L] using hrecordAtK
      _ = R.records[k.val]'hbound := hrecord.symm
      _ = r := rfl
  have hprovenance := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    initial rows J rewards s count hspan hactive hfirst
  rcases hprovenance with hzero | ⟨hW, firstSelected, firstInstalled, firstArm,
      hrow0first, hdispatch, hinstalled, hinitialPending, hstartPending,
      hselected0, hpayload0, hpending0, hstarted0, hrows⟩
  · have hlength : L.length = 0 := by exact hzero
    rw [hlength] at hindex
    omega
  · have hindex' : k.val < L.length := by simpa only [L] using hindex
    obtain ⟨recordK, hrecordK, selectedK, hselectedK, hpayloadK, hphaseK,
      nextK, nextOwnedK, nextBaseK, houtK, hnextPayloadK, hupdateK, hcoverageK⟩ :=
      hrows ⟨k.val, hindex'⟩
    cases hrecordK
    obtain ⟨gateRegs, gateOwned, gateBase, hgateLive, hgateBirth, hgatePending,
      hgateClock, hgateClockU⟩ :=
      ReferenceLocalReleaseGateChronology.gate_live s r.input.time r.input.state hgate
    have hcoordK : (L[k.val]'hindex').input.state.coordinator =
        .live gateRegs gateOwned gateBase := by
      rw [hgetK]
      exact hgateLive
    have hphaseK' :
        selectedK.view.payload = gateRegs.payload ∧
        selectedK.view.pendingAtChoice = gateRegs.pendingAtChoice ∧
        selectedK.started.pending = gateRegs.pendingAtChoice := by
      have hh := hphaseK
      change match (L[k.val]'hindex').input.state.coordinator with
        | .first => selectedK.view.pendingAtChoice = Finset.univ ∧
            selectedK.started.pending = Finset.univ
        | .live incoming owned baseScores =>
            selectedK.view.payload = incoming.payload ∧
              selectedK.view.pendingAtChoice = incoming.pendingAtChoice ∧
              selectedK.started.pending = incoming.pendingAtChoice
        | _ => False at hh
      rw [hcoordK] at hh
      exact hh
    have hselectedPendingK : selectedK.view.pendingAtChoice = ∅ := by
      rw [hphaseK'.2.1, hgatePending]
    let P : ℕ → Prop := fun n =>
      ∃ hn : n < L.length,
        ∃ selected : Selection (L[n]'hn).input,
          (L[n]'hn).output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅
    have hPk : P k.val := ⟨hindex', selectedK, hselectedK, hselectedPendingK⟩
    have hselectedAtZero :
        (L[0]'(by have := hW; omega)).output.preparation.coordinator.selection =
          some firstSelected := by
      exact hselected0
    have hnotPzero : ¬ P 0 := by
      rintro ⟨h0, selected0, hselection0, hempty0⟩
      have heq : selected0 = firstSelected :=
        Option.some.inj (hselection0.symm.trans hselectedAtZero)
      rw [heq] at hempty0
      have hz : (Finset.univ : Finset (Fin (p.m - 1))) = ∅ :=
        hpending0.symm.trans hempty0
      have hmem : (⟨0, by have hm := p.two_le_m; omega⟩ : Fin (p.m - 1)) ∈
          (Finset.univ : Finset (Fin (p.m - 1))) := Finset.mem_univ _
      rw [hz] at hmem
      exact Finset.notMem_empty _ hmem
    let existsEmpty : ∃ n, P n := ⟨k.val, hPk⟩
    let h := Nat.find existsEmpty
    have hP : P h := Nat.find_spec existsEmpty
    have hle : h ≤ k.val := Nat.find_min' existsEmpty hPk
    have hpos : 0 < h := by
      by_contra hnot
      have hz : h = 0 := by omega
      have hPzero : P 0 := by
        have hzFind : Nat.find existsEmpty = 0 := by
          change Nat.find existsEmpty = 0 at hz
          exact hz
        change P (Nat.find existsEmpty) at hP
        rw [hzFind] at hP
        exact hP
      exact hnotPzero hPzero
    rcases hP with ⟨hboundL, selectedH, hselectedH, hemptyH⟩
    have hcval : h - 1 < L.length := by omega
    let c : Fin L.length := ⟨h - 1, hcval⟩
    have hcplus : c.val + 1 = h := by
      dsimp only [c]
      omega
    have hclt : c.val < k.val := by omega
    have hnotPc : ¬ P c.val := by
      apply Nat.find_min existsEmpty
      dsimp only [c]
      omega
    obtain ⟨recordC, hrecordC, selectedC, hselectedC, hpayloadC, hphaseC,
      next, nextOwned, nextBase, houtC, hnextPayloadC, hupdateC, hcoverageC⟩ :=
      hrows c
    cases hrecordC
    have hnonemptyC : selectedC.view.pendingAtChoice ≠ ∅ := by
      intro hempty
      exact hnotPc ⟨c.isLt, selectedC, hselectedC, hempty⟩
    have hrecordAtC := firstLive_record_eq_actualRunRecordAt initial rows J rewards s
      count hspan hactive c
    have hrecordAtH := firstLive_record_eq_actualRunRecordAt initial rows J rewards s
      count hspan hactive ⟨h, hboundL⟩
    have hsuccState :
        (L[c.val]'c.isLt).output.next = (L[h]'hboundL).input.state := by
      rw [hrecordAtC, hrecordAtH]
      change (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s
          c.val (by have hc := c.isLt; omega) hactive).output.next =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards s h (by omega) hactive).finalState
      have hcountEq :
          (⟨c.val + 1, by omega⟩ : {n : ℕ // s + n ≤ p.T}) =
            ⟨h, by omega⟩ := Subtype.ext hcplus
      have hrunEq := congrArg
        (fun n : {n : ℕ // s + n ≤ p.T} =>
          (ReferenceActivePhysicalHorizon.run initial rows J rewards s n.val n.property hactive).finalState)
        hcountEq
      have hsuccessor :=
        ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
          initial rows J rewards s c.val (by omega) hactive
      calc
        _ = (ReferenceActivePhysicalHorizon.run initial rows J rewards s (c.val + 1)
            (by omega) hactive).finalState := hsuccessor.symm
        _ = (ReferenceActivePhysicalHorizon.run initial rows J rewards s h (by omega)
            hactive).finalState := hrunEq
    have hcoordEq :
        CoordinatorConfiguration.live next nextOwned nextBase =
          (L[h]'hboundL).input.state.coordinator := by
      have hstateCoord := congrArg
        (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator) hsuccState
      calc
        .live next nextOwned nextBase = (L[c.val]'c.isLt).output.next.coordinator := houtC.symm
        _ = (L[h]'hboundL).input.state.coordinator := hstateCoord
    obtain ⟨recordH, hrecordH, selectedHActual, hselectedHActual, hpayloadH,
      hphaseH, nextH, nextOwnedH, nextBaseH, houtH, hnextPayloadH, hupdateH,
      hcoverageH⟩ := hrows ⟨h, hboundL⟩
    cases hrecordH
    have hselectedHeq : selectedH = selectedHActual :=
      Option.some.inj (hselectedH.symm.trans hselectedHActual)
    rw [hselectedHeq] at hemptyH
    have hphaseH' :
        selectedHActual.view.payload = next.payload ∧
        selectedHActual.view.pendingAtChoice = next.pendingAtChoice ∧
        selectedHActual.started.pending = next.pendingAtChoice := by
      have hh := hphaseH
      rw [← hcoordEq] at hh
      simpa only [] using hh
    have hnextPending : next.pendingAtChoice = ∅ :=
      hphaseH'.2.1.symm.trans hemptyH
    have hevent : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
        (L[c.val]'c.isLt) selectedC := by
      by_cases he : ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
          (L[c.val]'c.isLt) selectedC
      · exact he
      · have hupdateC' := hupdateC
        change next.pendingAtChoice =
          if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
              (L[c.val]'c.isLt) selectedC then
            selectedC.view.pendingAtChoice.erase
              (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (((L[c.val]'c.isLt).input.row.2 (L[c.val]'c.isLt).input.time).1))
          else selectedC.view.pendingAtChoice at hupdateC'
        have hupdateFalse : next.pendingAtChoice = selectedC.view.pendingAtChoice := by
          simpa only [he, ite_false] using hupdateC'
        exact False.elim (hnonemptyC (hupdateFalse.symm.trans hnextPending))
    let draw := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (((L[c.val]'c.isLt).input.row.2 (L[c.val]'c.isLt).input.time).1)
    have herase : selectedC.view.pendingAtChoice.erase draw = ∅ := by
      have hupdateC' := hupdateC
      change next.pendingAtChoice =
        if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
            (L[c.val]'c.isLt) selectedC then
          selectedC.view.pendingAtChoice.erase draw
        else selectedC.view.pendingAtChoice at hupdateC'
      have hupdateTrue : next.pendingAtChoice = selectedC.view.pendingAtChoice.erase draw := by
        simpa only [hevent, ite_true] using hupdateC'
      exact hupdateTrue.symm.trans hnextPending
    have heraseCases := (Finset.erase_eq_empty_iff selectedC.view.pendingAtChoice draw).mp herase
    have hsingle :
        selectedC.view.pendingAtChoice = {draw} := by
      rcases heraseCases with hempty | hsingleton
      · exact False.elim (hnonemptyC hempty)
      · exact hsingleton
    let cQuota : Fin (ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count hspan hactive).length :=
      ⟨c.val, by simpa only [ReferencePhysicalReleaseQuota.runWindow, L] using c.isLt⟩
    have hselectedQuota :
        (ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count hspan hactive)[cQuota.val].output.preparation.coordinator.selection =
          some selectedC := by
      simpa only [ReferencePhysicalReleaseQuota.runWindow, L] using hselectedC
    have houtQuota :
        (ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count hspan hactive)[cQuota.val].output.next.coordinator =
          .live next nextOwned nextBase := by
      simpa only [ReferencePhysicalReleaseQuota.runWindow, L] using houtC
    have hsingleQuota :
        selectedC.view.pendingAtChoice =
          {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (((ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count hspan hactive)[cQuota.val].input.row.2
              (ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count hspan hactive)[cQuota.val].input.time).1)} := by
      simpa only [ReferencePhysicalReleaseQuota.runWindow, L] using hsingle
    let quotaRecord :=
      (ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count hspan hactive)[cQuota.val]
    have heventQuota :
        ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent quotaRecord selectedC := by
      simpa only [quotaRecord, cQuota, ReferencePhysicalReleaseQuota.runWindow, L] using hevent
    have hselectedQuotaRecord :
        quotaRecord.output.preparation.coordinator.selection = some selectedC := by
      simpa only [quotaRecord] using hselectedQuota
    have hselectedQuotaPrepared :
        (ReferenceActivePhysicalStep.prepare
          quotaRecord.input).coordinator.selection =
            some selectedC := by
      have hpreparation := congrArg
        (fun output : ReferenceActivePhysicalStep.RoundOutput quotaRecord.input =>
          output.preparation.coordinator.selection) quotaRecord.output_eq
      have h := hselectedQuotaRecord
      rw [hpreparation] at h
      simpa only [ReferenceActivePhysicalStep.step] using h
    have heventQuotaPrepared :
        CoordinatorLocalArmChoice.downConfirmationEvent selectedC.view.payload
          selectedC.view.pendingAtChoice selectedC.view.cutoff quotaRecord.input.time
          (quotaRecord.input.row.2 quotaRecord.input.time)
          (ReferenceActivePhysicalStep.prepare quotaRecord.input).coordinatorObservation := by
      have heventOutput := heventQuota
      unfold ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent at heventOutput
      have hObservation := congrArg
        (fun output : ReferenceActivePhysicalStep.RoundOutput quotaRecord.input =>
          output.preparation.coordinatorObservation) quotaRecord.output_eq
      rw [hObservation] at heventOutput
      simpa only [ReferenceActivePhysicalStep.step] using heventOutput
    have hquota := ReferencePhysicalReleaseQuota.run_firstLive_release_seed
      initial rows J rewards s count hspan hactive hfirst hseed cQuota selectedC hselectedQuotaPrepared
      hsingleQuota heventQuotaPrepared next nextOwned nextBase houtQuota
    have hbirth : firstInstalled.registers.payload.sigma.val = s := by
      calc
        _ = selectedK.view.payload.sigma.val := by rw [← hpayloadK]
        _ = gateRegs.payload.sigma.val := by rw [hphaseK'.1]
        _ = s := hgateBirth
    have hsafe := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
      initial rows J rewards s count hspan hactive hfirst
    have hLcount : L.length ≤ count := by
      calc
        _ ≤ (ReferenceActivePhysicalHorizon.run initial rows J rewards s count hspan hactive).records.length :=
          (List.takeWhile_prefix _).length_le
        _ = count := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    have hconnect (j : Fin L.length) (hj : j.val + 1 < L.length) :
        (L[j.val]'j.isLt).output.next = (L[j.val + 1]'hj).input.state := by
      rw [firstLive_record_eq_actualRunRecordAt initial rows J rewards s count hspan hactive j,
        firstLive_record_eq_actualRunRecordAt initial rows J rewards s count hspan hactive
          ⟨j.val + 1, hj⟩]
      exact (ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards s j.val (by have hh := j.isLt; omega) hactive).symm
    have hemptyAfter : ∀ j (hj : j < L.length), h ≤ j →
        ∀ sel : Selection (L[j]'hj).input,
          (L[j]'hj).output.preparation.coordinator.selection = some sel →
          sel.view.pendingAtChoice = ∅ := by
      intro j
      induction j using Nat.strong_induction_on with
      | h j ih =>
          intro hj hhj sel hsel
          by_cases heq : j = h
          · subst j
            have heq : sel = selectedHActual := Option.some.inj (hsel.symm.trans hselectedHActual)
            simpa only [heq] using hemptyH
          · have hjpos : 0 < j := by omega
            have hjprev : j - 1 < L.length := by omega
            obtain ⟨recordN, hrN, selN, hsN, hpN, hfN, nxN, owN, bsN,
              hoN, hnpN, huN, hcN⟩ := hrows ⟨j - 1, hjprev⟩
            cases hrN
            have heN := ih (j - 1) (by omega) hjprev (by omega) selN hsN
            have hnextEmpty : nxN.pendingAtChoice = ∅ := by
              rw [huN, heN]
              split <;> simp
            have hcoord : (L[j]'hj).input.state.coordinator = .live nxN owN bsN := by
              have hh := congrArg (fun st : State p rate => st.coordinator)
                (hconnect ⟨j - 1, hjprev⟩ (by change j - 1 + 1 < L.length; omega))
              have hh' : (L[j - 1]'hjprev).output.next.coordinator =
                  (L[j]'hj).input.state.coordinator := by
                simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hh
              exact hh'.symm.trans hoN
            obtain ⟨recordS, hrS, selS, hsS, hpS, hfS, nxS, owS, bsS,
              hoS, hnpS, huS, hcS⟩ := hrows ⟨j, hj⟩
            cases hrS
            have heq : sel = selS := Option.some.inj (hsel.symm.trans hsS)
            subst sel
            rw [hcoord] at hfS
            exact hfS.2.1.trans hnextEmpty
    have hgateIff : ∀ j (hj : j < R.records.length),
        localReleaseGate rate s (R.records[j]'hj).input.time
          (encodeState (R.records[j]'hj).input.state) = true ↔ h ≤ j ∧ j < L.length := by
      intro j hj
      have hjcount : j < count := by simpa only [R,
        ReferenceLocalReleaseGateChronology.sourceRun, ReferenceActivePhysicalHorizon.run_record_count] using hj
      have hrj : R.records[j]'hj = ReferenceAssignmentPayloadChronology.actualRunRecordAt
          initial rows J rewards s j (by omega) hactive :=
        ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards s hactive
          count hspan ⟨j, hjcount⟩
      constructor
      · intro hg
        have hjL := actual_gate_index_firstLiveWindow initial rows J rewards s count
          hspan hactive hfirst ⟨j, hjcount⟩ (by simpa only [hrj] using hg)
        have hLj : L[j]'hjL = R.records[j]'hj := by
          rw [firstLive_record_eq_actualRunRecordAt initial rows J rewards s count hspan hactive ⟨j, hjL⟩]
          exact hrj.symm
        obtain ⟨rr, hrr, ss, hss, hps, hfs, nn, oo, bb, hon, hpn, hun, hcn⟩ := hrows ⟨j, hjL⟩
        cases hrr
        obtain ⟨rg, og, bg, hcg, hbg, heg, hsg, hug⟩ :=
          ReferenceLocalReleaseGateChronology.gate_live s _ _ hg
        have hcgL : (L[j]'hjL).input.state.coordinator = .live rg og bg := by rw [hLj]; exact hcg
        rw [hcgL] at hfs
        have hPj : P j := ⟨hjL, ss, hss, hfs.2.1.trans heg⟩
        exact ⟨Nat.find_min' existsEmpty hPj, hjL⟩
      · rintro ⟨hhj, hjL⟩
        have hLj : L[j]'hjL = R.records[j]'hj := by
          rw [firstLive_record_eq_actualRunRecordAt initial rows J rewards s count hspan hactive ⟨j, hjL⟩]
          exact hrj.symm
        obtain ⟨rr, hrr, ss, hss, hps, hfs, nn, oo, bb, hon, hpn, hun, hcn⟩ := hrows ⟨j, hjL⟩
        cases hrr
        have heS : ss.view.pendingAtChoice = ∅ := hemptyAfter j hjL hhj ss hss
        have hsafeJ := hsafe.1 ⟨j, hjL⟩
        obtain ⟨recording, hrecording, nxSafe, owSafe, bsSafe, houtSafe⟩ := hsafeJ.2
        have hpSafe : nxSafe.payload = nn.payload := by
          have hh := congrArg ReferenceAssignmentPayloadPersistence.storedPayload
            (houtSafe.symm.trans hon)
          exact Option.some.inj hh
        have hnBirth : nxSafe.payload.sigma.val = s := by rw [hpSafe, hpn, hps]; exact hbirth
        have htj : (L[j]'hjL).input.time.val = s + j := by
          exact ReferencePhysicalReleaseQuota.runWindow_time initial rows J rewards s count hspan hactive ⟨j, hjL⟩
        obtain ⟨rg, og, bg, hcg, hbg, started, hstart, hframe, hsig, hsub, hsigmaNext, huNext⟩ :=
          ReferenceLocalReleaseGateChronology.step_old_live_predecessor (L[j]'hjL).input s
            nxSafe owSafe bsSafe (by simpa only [← (L[j]'hjL).output_eq] using houtSafe)
            hnBirth (by omega)
        rw [hcg] at hfs
        have hpending : rg.pendingAtChoice = ∅ := hfs.2.1.symm.trans heS
        have hclockSeed : ReferenceCoordinatorClockDomains.clockAt rows J s initial := by
          simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
        have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards s
          count hspan hactive hclockSeed
        have hmem : (L[j]'hjL) ∈ R.records := by
          rw [hLj]
          exact List.getElem_mem hj
        have hclock := (hclockRun.2.2.2 (L[j]'hjL) hmem).1
        rw [ReferenceCoordinatorClockDomains.clockAt, hcg] at hclock
        have hactualGate := gate_of_live_frame (L[j]'hjL).input s rg og bg hcg hbg
          hpending hsig hclock.2.2.2.1 started hstart hframe
        simpa only [hLj] using hactualGate
    have hfilter : R.records.filter (fun record => localReleaseGate rate s record.input.time
        (encodeState record.input.state)) = L.drop (c.val + 1) := by
      have hRlength : R.records.length = count := ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
      have hfilter' := filter_eq_take_drop R.records
        (fun record => localReleaseGate rate s record.input.time (encodeState record.input.state))
        h L.length (by omega) (by omega) hgateIff
      have hprefix : L = R.records.take L.length := List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
      rw [← hprefix, ← hcplus] at hfilter'
      exact hfilter'
    have hstoredK : ReferenceAssignmentPayloadPersistence.storedPayload
        r.input.state.coordinator = some firstInstalled.registers.payload := by
      rw [hgateLive]
      exact congrArg some (hphaseK'.1.symm.trans hpayloadK)
    refine ⟨hindex, c, hclt, selectedC, hselectedC, firstInstalled.registers.payload, ?_, hstoredK, hpayloadC,
      hsingle, hevent, next, nextOwned, nextBase, houtC, ?_, hquota.2, hfilter, ?_, ?_, ?_, ?_, ?_⟩
    · calc
        firstInstalled.registers.payload.sigma.val = selectedK.view.payload.sigma.val := by
          rw [← hpayloadK]
        _ = gateRegs.payload.sigma.val := by rw [hphaseK'.1]
        _ = s := hgateBirth
    · exact hquota.1.trans hpayloadC
    · intro a b hab hb
      have hb' : b < ((ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count
          hspan hactive).drop (cQuota.val + 1)).length := by
        simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow] using hb
      have hh := ReferencePhysicalReleaseQuota.run_firstLive_release_pending_nested
        initial rows J rewards s count hspan hactive hfirst hseed cQuota selectedC
        hselectedQuotaPrepared hsingleQuota heventQuotaPrepared next nextOwned nextBase
        houtQuota a b hab hb'
      simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow, hpayloadC] using hh
    · intro i n hn
      have hn' : n ≤ ((ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count
          hspan hactive).drop (cQuota.val + 1)).length := by
        simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow] using hn
      have hh := ReferencePhysicalReleaseQuota.run_firstLive_release_prefix_quota
        initial rows J rewards s count hspan hactive hfirst hseed cQuota selectedC
        hselectedQuotaPrepared hsingleQuota heventQuotaPrepared next nextOwned nextBase
        houtQuota i n hn'
      simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow, hpayloadC] using hh
    · intro i n hn hpending
      have hn' : n < ((ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count
          hspan hactive).drop (cQuota.val + 1)).length := by
        simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow] using hn
      have hpending' : i ∈ ReferencePhysicalReleaseQuota.pendingSet selectedC.view.payload
          ((ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count
            hspan hactive).drop (cQuota.val + 1))[n] := by
        simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow, hpayloadC] using hpending
      have hh := ReferencePhysicalReleaseQuota.run_firstLive_release_precount_zero
        initial rows J rewards s count hspan hactive hfirst hseed cQuota selectedC
        hselectedQuotaPrepared hsingleQuota heventQuotaPrepared next nextOwned nextBase
        houtQuota i n hn' hpending'
      simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow, hpayloadC] using hh
    · intro n
      have hn' : n.val < ((ReferencePhysicalReleaseQuota.runWindow initial rows J rewards s count
          hspan hactive).drop (cQuota.val + 1)).length := by
        simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow] using n.isLt
      have hh := ReferencePhysicalReleaseQuota.run_firstLive_release_calendar initial rows J rewards
        s count hspan hactive cQuota ⟨n.val, hn'⟩
      have ht : (R.records.filter (fun record => localReleaseGate rate s record.input.time
          (encodeState record.input.state)))[n.val].input.time.val = s + c.val + 1 + n.val := by
        simpa only [hfilter, L, ReferencePhysicalReleaseQuota.runWindow] using hh
      omega
    · intro record hrecordSupport
      obtain ⟨hrecordR, hrecordGate⟩ := List.mem_filter.mp hrecordSupport
      have hmemK : r ∈ R.records := List.getElem_mem hbound
      obtain ⟨common, birth, hcommonK, hcommonRecord, hcommonBirth,
        hbirthMem, hbirthEvent, hbirthTime, hbeforeK, hbeforeRecord⟩ :=
        ReferenceLocalReleaseGateChronology.run_gate_records_payload_eq initial rows J rewards
          s hactive count hspan hfirst r record hmemK hrecordR s hgate hrecordGate
      have hcommon : common = firstInstalled.registers.payload :=
        Option.some.inj (hcommonK.symm.trans hstoredK)
      have hstored : ReferenceAssignmentPayloadPersistence.storedPayload
          record.input.state.coordinator = some firstInstalled.registers.payload := by
        exact hcommonRecord.trans (congrArg some hcommon)
      let sourcePoint : ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s :=
        ⟨source, hcross, rfl⟩
      let fiber : ReferenceSourceReleaseWaitingReadouts.SourceFiber rate rewards C_star C_h s J :=
        ⟨sourcePoint, rfl⟩
      have hst : s ≤ record.input.time.val := by omega
      have hlookup : ReferenceLocalReleaseCalendarCounts.calendarRecord rate source rewards
          C_star C_h hcross s (p.T - s) rfl (by omega) record.input.time.val = some record := by
        obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hrecordR
        have hjcount : j < count := by
          simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
            ReferenceActivePhysicalHorizon.run_record_count] using hj
        have hrj : R.records[j]'hj = ReferenceAssignmentPayloadChronology.actualRunRecordAt
            initial rows J rewards s j (by omega) hactive :=
          ReferenceLocalReleaseGateChronology.run_record_at initial rows J rewards s hactive
            count hspan ⟨j, hjcount⟩
        have htj : record.input.time.val = s + j := by rw [← heq, hrj]; rfl
        have hoff : record.input.time.val - s = j := by omega
        have hh := ReferenceSourceReleaseWaitingReadouts.source_calendar_record_eq_actual_run_record
          rate rewards C_star C_h s J record.input.time hst fiber record.input.time.val hst le_rfl
        have hh' : ReferenceLocalReleaseCalendarCounts.calendarRecord rate source rewards
            C_star C_h hcross s (p.T - s) rfl (by omega) record.input.time.val =
            some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards s j
              (by omega) hactive) := by
          simpa only [fiber, sourcePoint, hoff] using hh
        exact hh'.trans (congrArg some (hrj.symm.trans heq))
      have hcalendarGate : ReferenceLocalReleaseCalendarCounts.calendarGate rate source rewards
          C_star C_h hcross s (p.T - s) rfl (by omega) s record.input.time.val = some true := by
        simp only [ReferenceLocalReleaseCalendarCounts.calendarGate, hlookup,
          Option.map_some, hrecordGate]
      obtain ⟨readRecord, readPayload, hreadLookup, hreadStored, hreadBirth,
        hentry, hpending, hflags⟩ := ReferenceLocalReleaseWaitingPaths.sourceReadouts_at_trueGate
          rate rewards C_star C_h s (by omega) s sourcePoint record.input.time.val hcalendarGate
      have hreadRecord : readRecord = record := Option.some.inj (hreadLookup.symm.trans hlookup)
      cases hreadRecord
      have hreadPayload : readPayload = firstInstalled.registers.payload :=
        Option.some.inj (hreadStored.symm.trans hstored)
      cases hreadPayload
      have hactual : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          record.input.time source = some record := by
        rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_source_calendar
          rate rewards C_star C_h record.input.time s hst sourcePoint]
        exact hlookup
      have hsourceEntry : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s
          record.input.time source = some (true,
            some (ReferencePhysicalReleaseQuota.pendingSet firstInstalled.registers.payload record)) := by
        rw [ReferenceSourcePrefixHistoryFiltration.entry_source_calendar
          rate rewards C_star C_h s record.input.time s hst sourcePoint]
        exact hentry
      refine ⟨hstored, hactual, hsourceEntry, ?_, ?_⟩
      · simp only [ReferenceSourcePrefixHistoryFiltration.pending, hsourceEntry,
          Option.bind_some, Option.getD_some]
      · intro i
        simp only [ReferenceSourcePrefixHistoryFiltration.actualUp,
          ReferenceSourcePrefixHistoryFiltration.actualData,
          ReferenceSourcePrefixHistoryFiltration.actualRelease, hactual, hstored,
          Option.bind_some]
        exact ⟨rfl, rfl, rfl⟩

/-- The full finite-support identity and quotas use the same actual last
confirmation witnesses as the constructor above. Empty follower pending sets
remain in the true-gate list. -/
theorem actual_first_live_gate_support_eq_release_suffix
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    let s := ReferenceInitializationRun.elapsed p I.completed
    (hcross : I.crossing.isSome = true) →
    (hspan : s + count ≤ p.T) →
    let R := ReferenceLocalReleaseGateChronology.sourceRun rate source rewards C_star C_h
      hcross s count rfl hspan
    (k : Fin count) →
    let r := R.records[k.val]'(by
      simpa only [R, ReferenceLocalReleaseGateChronology.sourceRun,
        ReferenceActivePhysicalHorizon.run_record_count] using k.isLt)
    (hgate : localReleaseGate rate s r.input.time (encodeState r.input.state) = true) →
    k.val < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length ∧
    ∃ c : Fin (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).length,
      c.val < k.val ∧
      ∃ selected : Selection
          ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].input),
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].output.preparation.coordinator.selection =
          some selected ∧
        ∃ M : ReferenceActivePhysicalStep.Payload rate,
          M.sigma.val = s ∧
          ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
          selected.view.payload = M ∧
          selected.view.pendingAtChoice =
            {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].input.row.2
                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].input.time).1)} ∧
          ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
            ((ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val]) selected ∧
          ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
            ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
              ∃ base : Fin (p.m - 1) → ℕ,
                (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records)[c.val].output.next.coordinator =
                  .live next owned base ∧
                next.payload = M ∧ next.pendingAtChoice = ∅ ∧
                let support := R.records.filter (fun record =>
                  localReleaseGate rate s record.input.time (encodeState record.input.state))
                support = (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R.records).drop
                    (c.val + 1) ∧
                (∀ a b (hab : a ≤ b) (hb : b < support.length),
                  ReferencePhysicalReleaseQuota.pendingSet M (support[b]'hb) ⊆
                    ReferencePhysicalReleaseQuota.pendingSet M (support[a]'(lt_of_le_of_lt hab hb))) ∧
                (∀ i n (_hn : n ≤ support.length),
                  ReferencePhysicalReleaseQuota.releaseCount M (support.take n) i ≤ 1 ∧
                  ReferencePhysicalReleaseQuota.upCount M (support.take n) i ≤ 1 ∧
                  ReferencePhysicalReleaseQuota.dataCount M (support.take n) i ≤ 1) ∧
                (∀ i n (hn : n < support.length),
                  i ∈ ReferencePhysicalReleaseQuota.pendingSet M (support[n]'hn) →
                  ReferencePhysicalReleaseQuota.releaseCount M (support.take n) i = 0 ∧
                  ReferencePhysicalReleaseQuota.upCount M (support.take n) i = 0 ∧
                  ReferencePhysicalReleaseQuota.dataCount M (support.take n) i = 0) ∧
                (∀ n : Fin support.length,
                  (support[n.val]'n.isLt).input.time.val + 1 = s + c.val + 2 + n.val) ∧
                (∀ record ∈ support,
                  ReferenceAssignmentPayloadPersistence.storedPayload record.input.state.coordinator = some M ∧
                  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
                    record.input.time source = some record ∧
                  ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s
                    record.input.time source = some (true,
                      some (ReferencePhysicalReleaseQuota.pendingSet M record)) ∧
                  ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h s
                    record.input.time source = ReferencePhysicalReleaseQuota.pendingSet M record ∧
                  ∀ i,
                    ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i
                      record.input.time source = ReferencePhysicalReleaseQuota.upFlag M record i ∧
                    ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i
                      record.input.time source = ReferencePhysicalReleaseQuota.dataFlag M record i ∧
                    ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i
                      record.input.time source = ReferencePhysicalReleaseQuota.releaseFlag M record i) :=
  actual_first_live_gate_last_confirmation rate source rewards C_star C_h count

end Bandits.Support.ReferenceFirstLiveSourceReleaseSupport
