/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionUpOfferCut
public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

import Mathlib.Data.Nat.Find
import Mathlib.Data.List.TakeDrop
import Lean.Elab.Tactic.Omega

/-!
# First replacement collection: fixed-UP positive window cuts

Sources: `sources/zip4/manuscript/06_interruptions.tex:110-177,246-299,477-481`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:141-157`, and
`sources/zip4/manuscript/05_binary_transport.tex:27-55,354-431`.

The first completion can contain older or placeholder equations. Only the
second window after the actual current reply's birth is pure. A saved decoder
decision is distinguished from physical receiver commitment and acceptance.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstReplacementCollectionPureUpWindowCut

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Positives of the literal saved-call trace on exactly these physical records. -/
def physicalPositives
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) :
    List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :=
  AffineBatchDecoder.positives p
    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
    (records.map (fun r => r.input.time))

private theorem record_positive_length_le_one
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1)) :
    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i).length ≤ 1 := by
  classical
  cases hd : r.output.coordinator.up with
  | none => simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd]
  | some d =>
      by_cases hs : ReferenceCoordinatorUpDecoderReplay.retainedUpFollower d = i
      · simp only [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          ite_eq_left hs, AffineBatchDecoder.positiveAt]
        split <;> simp
      · simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd, hs]

/-- Every physical record contributes zero or one positive entry. Thus an
attainable quota has a least prefix attaining it exactly, without liveness. -/
theorem retained_positive_prefix_cut
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (need : ℕ) (hneed : 0 < need) :
    (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i).length < need ∨
      ∃ m : ℕ, 0 < m ∧ m ≤ records.length ∧
        (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
          (records.take m) i).length = need ∧
        ∀ n : ℕ, n < m →
          (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
            (records.take n) i).length < need := by
  classical
  by_cases hsmall :
      (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries records i).length < need
  · exact Or.inl hsmall
  · right
    let count := fun n => (ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries
      (records.take n) i).length
    have hex : ∃ n, need ≤ count n := by
      refine ⟨records.length, ?_⟩
      simpa only [count, List.take_length] using Nat.le_of_not_gt hsmall
    let m := Nat.find hex
    have hreach : need ≤ count m := Nat.find_spec hex
    have hbound : m ≤ records.length :=
      Nat.find_min' hex (by simpa only [count, List.take_length] using Nat.le_of_not_gt hsmall)
    have hprevious : ∀ n, n < m → count n < need := by
      intro n hn
      exact Nat.lt_of_not_ge (Nat.find_min hex hn)
    have hpos : 0 < m := by
      by_contra hn
      have hm : m = 0 := by omega
      simp [hm, count, ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries] at hreach
      omega
    obtain ⟨n, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    rw [hm] at hreach hbound hprevious hpos
    simp only [Nat.succ_eq_add_one] at hreach hbound hprevious hpos
    have hn : n < records.length := by omega
    have hstep : count (n + 1) ≤ count n + 1 := by
      dsimp only [count]
      rw [List.take_succ_eq_append_getElem hn]
      simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
        List.flatMap_append, List.flatMap_singleton, List.length_append]
      exact Nat.add_le_add_left (record_positive_length_le_one records[n] i) _
    refine ⟨n + 1, hpos, hbound, ?_, hprevious⟩
    have := hprevious n (by omega)
    dsimp only [count] at hreach hstep this
    omega

/-- Chronology identifies the administrative trace positives with the
physical retained equations, on the whole interval and on every prefix. -/
theorem physical_positive_prefix_cut
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1)) (need : ℕ) (hneed : 0 < need)
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val)) :
    (physicalPositives records i).length < need ∨
      ∃ m : ℕ, 0 < m ∧ m ≤ records.length ∧
        (physicalPositives (records.take m) i).length = need ∧
        ∀ n : ℕ, n < m → (physicalPositives (records.take n) i).length < need := by
  have heq := ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
    records i hchronological
  have hprefix : ∀ n, physicalPositives (records.take n) i =
      ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (records.take n) i := by
    intro n
    exact ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
      (records.take n) i hchronological.take
  rcases retained_positive_prefix_cut records i need hneed with hsmall | ⟨m, hm, hb, he, hl⟩
  · left
    simpa only [physicalPositives, heq] using hsmall
  · exact Or.inr ⟨m, hm, hb, (congrArg List.length (hprefix m)).trans he,
      fun n hn => by rw [hprefix n]; exact hl n hn⟩

/-- Raw solver failure for a batch with a known solution means a distinct
second solution. Parsing and local acceptance are separate operations. -/
theorem pure_batch_raw_cases
    (window : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hword : ∀ e ∈ window, AffineBatchDecoder.equation e.sample word) :
    (AffineBatchDecoder.batchOutput window = none ∧
      ∃ other, other ≠ word ∧
        ∀ e ∈ window, AffineBatchDecoder.equation e.sample other) ∨
    (AffineBatchDecoder.batchOutput window = some word ∧
      ∀ other, (∀ e ∈ window, AffineBatchDecoder.equation e.sample other) →
        other = word) := by
  classical
  cases hraw : AffineBatchDecoder.batchOutput window with
  | none =>
      left
      refine ⟨rfl, ?_⟩
      have hnone : ¬ ∃! u, AffineBatchDecoder.satisfies
          (AffineBatchDecoder.samples window) u :=
        (AffineBatchDecoder.solve_eq_none_iff _).mp hraw
      by_contra hother
      apply hnone
      refine ⟨word, (AffineBatchDecoder.satisfies_samples_iff window word).mpr hword, ?_⟩
      intro u hu
      by_contra hne
      exact hother ⟨u, hne, (AffineBatchDecoder.satisfies_samples_iff window u).mp hu⟩
  | some decoded =>
      obtain ⟨_, hunique⟩ := (AffineBatchDecoder.batchOutput_eq_some_iff window decoded).mp hraw
      have heq := hunique word hword
      subst decoded
      exact Or.inr ⟨rfl, hunique⟩

private theorem connected_endpoint
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final) :
    ReferenceCollectionSegmentExtraction.endpointState initial records = final := by
  induction records generalizing initial with
  | nil => exact hchain.symm
  | cons r rest ih =>
      exact ih hchain.2

private theorem run_prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count n : ℕ) (hn : n ≤ count) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
        hspan hmode).records.take n := by
  obtain ⟨suffix, hs⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (count - n) (by omega) hmode
  have hsum : n + (count - n) = count := by omega
  have hs' : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
      hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) hmode).records ++ suffix := by simpa only [hsum] using hs
  rw [hs']
  have hlength := ReferenceActivePhysicalHorizon.run_record_count
    initial rows selected rewards start n (by omega) hmode
  simp only [List.take_append, hlength, Nat.sub_self, List.take_zero, List.append_nil]
  exact (List.take_of_length_le (by omega)).symm

/-- The source suffix has a strictly increasing physical calendar even on
failed, no-launch, and terminal runs. -/
theorem complete_records_chronological
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).Pairwise
        (fun earlier later => earlier.input.time.val < later.input.time.val) := by
  apply List.pairwise_map.mp
  rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values]
  exact List.pairwise_lt_range' (step := 1) (by decide : 0 < 1)

/-- Restrict the original launched run to the actual input and successors
of a source record interval. The initial empty history is the original launch
bank; no assertion empties a channel at replacement birth. -/
theorem source_interval_runs
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (c : ℕ)
    (cut : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hcut : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[c]? = some cut)
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (hrecords : records <+:
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).drop c) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
      cut.input.state (records.take j)
    ∃ (initial : ReferenceActivePhysicalStep.State p rate)
      (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start),
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some initial ∧
      initial.coordinator = .first ∧
      initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      ReferenceUpDecoderBankInvariant.upBankInvariant initial ∧
      (∀ i, AffineBatchDecoder.collected (initial.upDecoderBank i) = []) ∧
      R = (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) (by
          have := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
          omega) active).records ∧
      ∀ j : ℕ, j ≤ records.length →
        ∃ span : start + (c + j) ≤ p.T,
          (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (c + j) span active).records.drop c = records.take j ∧
          (ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
            (c + j) span active).finalState = Z j := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  change records <+: R.drop c at hrecords
  obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hcut
  change c < R.length at hci
  obtain ⟨crossing, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h source ⟨c, hci⟩
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h crossing
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h crossing
  have hseed := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate source rewards C_star C_h crossing
  rcases hseed with ⟨_, active, _, hfirst, hbank, _⟩
  have hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant initial := by
    change ReferenceUpDecoderBankInvariant.coordinatorBankInvariant
      initial.coordinator initial.upDecoderBank
    rw [hfirst, hbank]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  have hfull := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h initial hlaunch
  change R = (ReferenceActivePhysicalHorizon.run initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
    (p.T - start) _ _).records at hfull
  have hchain := ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
    rate source rewards C_star C_h initial hlaunch
  have hbefore := ReferenceFollowerReplyChronology.connected_take_to_input hchain c hci
  rw [hce] at hbefore
  have hstart : start ≤ p.T :=
    ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
  have hlength : R.length = p.T - start :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate source rewards C_star C_h
  have hrecordsLength := hrecords.length_le
  have hrecordsTake : ∀ j, j ≤ records.length → (R.drop c).take j = records.take j := by
    intro j hj
    obtain ⟨suffix, hsuffix⟩ := hrecords
    rw [← hsuffix]
    exact List.take_append_of_le_length hj
  refine ⟨initial, active, hlaunch, hfirst, hbank, hinvariant, ?_, hfull, ?_⟩
  · intro i
    rw [hbank]
    rfl
  · intro j hj
    have span : start + (c + j) ≤ p.T := by
      simp only [List.length_drop] at hrecordsLength
      omega
    let run := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
      (c + j) span active
    have hrun : run.records = R.take (c + j) := by
      rw [hfull]
      exact run_prefix_records initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) (c + j) (by omega) (by omega) active
    have hdrop : run.records.drop c = records.take j := by
      rw [hrun, List.drop_take, Nat.add_sub_cancel_left]
      exact hrecordsTake j hj
    have hendpoint := connected_endpoint run.connected
    have heq : R.take (c + j) = R.take c ++ records.take j := by
      rw [← hrecordsTake j hj, List.take_add]
    have hstate : run.finalState = ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (records.take j) := by
      rw [← hendpoint, hrun, heq]
      unfold ReferenceCollectionSegmentExtraction.endpointState
      rw [List.foldl_append]
      have hpre := connected_endpoint hbefore
      change (R.take c).foldl _ initial = cut.input.state at hpre
      rw [hpre]
    exact ⟨span, hdrop, hstate⟩

private theorem tailLedger_eq_reception
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (tail : ReferenceCollectionPhaseHistory.Tail x) :
    ReferenceCoordinatorUpPhysicalCall.tailLedger?
      (ReferenceActivePhysicalStep.prepare x) tail.payload tail.ledger
        tail.started tail.weights = tail.reception.map Prod.fst := by
  unfold ReferenceCoordinatorUpPhysicalCall.tailLedger?
    ReferenceCollectionPhaseHistory.Tail.reception
  cases CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) tail.payload tail.started tail.weights) with
  | none => rfl
  | some recording =>
      dsimp only
      cases CoordinatorCollectionLedger.startRound tail.ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled tail.ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) <;> rfl

private theorem siteLedger_eq_reception
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) =
      (ReferenceCollectionPhaseHistory.executedTail x).bind
        (fun tail => tail.reception.map Prod.fst) := by
  classical
  unfold ReferenceCoordinatorUpPhysicalCall.siteLedger?
    ReferenceCollectionPhaseHistory.executedTail
  dsimp only
  split
  · rfl
  · cases hc : (ReferenceActivePhysicalStep.prepare x).coordinator with
    | first outcome => cases outcome <;> rfl
    | live registers owned base outcome =>
        cases outcome <;> dsimp only <;> try rfl
        rename_i dispatched hstart ledger hinit hledger hvalid hclock hpending hnone selected
        exact tailLedger_eq_reception x
          ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
            dispatched.startResult,
            (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights⟩
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> dsimp only <;> try rfl
        rename_i core snapshot boundary scores
        exact tailLedger_eq_reception x
          ⟨payload, ledger, snapshot.clockStarted,
            CoordinatorCollectionInteractive.PreObservationInputs.weights
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩
    | invalidCollectionCutoff => rfl
    | dagger => rfl

/-- A saved diagnostic's raw and expected fields come from its literal
receiver invocation, including when replay or a subsequent finish fails. -/
theorem retained_diagnostic_raw_expected
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : r.output.coordinator.up = some d) :
    d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) ∧
      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 := by
  obtain ⟨ledger, hsite, _, _, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input r d hd
  rw [siteLedger_eq_reception] at hsite
  cases ht : ReferenceCollectionPhaseHistory.executedTail r.input with
  | none => simp only [ht, Option.bind_none, reduceCtorEq] at hsite
  | some tail =>
      simp only [ht, Option.bind_some] at hsite
      cases hr : tail.reception with
      | none => simp only [hr, Option.map_none, reduceCtorEq] at hsite
      | some pair =>
          rcases pair with ⟨started, received⟩
          obtain ⟨_, _, _, _, hup⟩ :=
            ReferenceFirstReplacementCollectionUpReceiverProvenance.executed_reception_provenance
              r tail started received ht hr
          have hdiagnostic :=
            ReferenceFirstReplacementCollectionUpReceiverProvenance.executed_reception_diagnostic
              r tail started received ht hr
          have hsaved : received.diagnostic = some d := hup.symm.trans hd
          rw [hsaved] at hdiagnostic
          dsimp only at hdiagnostic
          refine ⟨hdiagnostic.2.1, ?_⟩
          rw [hdiagnostic.1]
          exact hdiagnostic.2.2.1

private theorem run_saved_pure_window
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a z : ℕ) (haz : a ≤ z) (span : start + z ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start z
      span active).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (word : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (hcount :
      (physicalPositives
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start z
          span active).records.drop a) i).length =
        AffineBatchDecoder.quota p -
          ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
            (by omega) active).finalState.upDecoderBank i).pending.length +
          AffineBatchDecoder.quota p)
    (hequations : ∀ e ∈ physicalPositives
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start z
          span active).records.drop a) i,
      AffineBatchDecoder.equation e.sample word)
    (hexpected : ∀ r ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start z
          span active).records.drop a,
      ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
        r.output.coordinator.up = some d → d.input.selectedFollower = i →
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
        d.expected = some word) :
    let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start z span active
    let pre := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a (by omega) active
    let interval := full.records.drop a
    let channel := pre.finalState.upDecoderBank i
    let positive := physicalPositives interval i
    let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
    ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (index : Fin interval.length)
      (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      first = channel.pending ++ positive.take (AffineBatchDecoder.quota p - channel.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
      (∀ e ∈ window, AffineBatchDecoder.equation e.sample word) ∧
      last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
      r ∈ interval ∧ r.input.time = last.time ∧
      r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      d.input.time = r.input.time ∧ last.sample = d.input.affineSample ∧
      d.input.upDecoderBank = r.input.state.upDecoderBank ∧
      r.input.state.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
        pre.finalState.upDecoderBank
          (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (interval.take index.val)) ∧
      (d.input.upDecoderBank i).pending ++ [last] = window ∧
      d.decoderAfter = ⟨[], channel.completed ++ [first, window]⟩ ∧
      d.raw = AffineBatchDecoder.batchOutput window ∧ d.expected = some word ∧
      full.finalState.upDecoderBank i = ⟨[], channel.completed ++ [first, window]⟩ ∧
      ((d.raw = none ∧ ∃ other, other ≠ word ∧
          ∀ e ∈ window, AffineBatchDecoder.equation e.sample other) ∨
        (d.raw = some word ∧ ∀ other,
          (∀ e ∈ window, AffineBatchDecoder.equation e.sample other) → other = word)) := by
  have hcut := ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
    initial rows selected rewards start a z haz span active hinvariant hordinary i hseed hcount
  dsimp only at hcut ⊢
  obtain ⟨first, last, index, r, d, hfirst, hfirstLen, hwindowLen, hchron,
    hlast, hdecision, hround, hr, htime, hd, hi, hdt, hentry, hsample,
    hphysical, hconnected, hreplay, hbank, hbefore, hpending, hclear, hcompleted,
    hafter, hraw, hbatch, htransition, hrun, hfinal⟩ := hcut
  let interval := (ReferenceActivePhysicalHorizon.run initial rows selected rewards start z
    span active).records.drop a
  let positive := physicalPositives interval i
  let channel := (ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
    (by omega) active).finalState.upDecoderBank i
  let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
  have hpure : ∀ e ∈ window, AffineBatchDecoder.equation e.sample word := by
    intro e he
    exact hequations e (List.mem_of_mem_drop he)
  have hlastPositive : last ∈ positive := List.mem_of_mem_drop hlast
  change last ∈ AffineBatchDecoder.positives p
    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i)
    (interval.map (fun r => r.input.time)) at hlastPositive
  have hlastEligible := (AffineBatchDecoder.mem_positives_iff p
    (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i)
    _ last).mp hlastPositive
  have hintervalChronological : interval.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    have hc := ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
      initial rows selected rewards start a z haz span active hinvariant hordinary
    have hc' : (interval.map (fun r => r.input.time)).Pairwise
        (fun earlier later => earlier.val < later.val) := hc
    exact (List.pairwise_map (R := fun earlier later : Fin p.T => earlier.val < later.val)
      (f := fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate => r.input.time)).mp hc'
  have htrace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
    interval i hintervalChronological r hr
  have heligible : AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
    have he := hlastEligible.2.1
    rw [← htime, htrace] at he
    simpa only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hd, hi,
      ite_eq_left, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using he
  have hexpect := hexpected r hr d hd hi heligible
  have hfields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
  obtain ⟨_, _, _, _, _, _, _, hsample', _⟩ := hfields
  have hlastSample : last.sample = d.input.affineSample := hsample.trans hsample'.symm
  have hdecoder : d.decoderAfter = ⟨[], channel.completed ++ [first, window]⟩ := by
    rw [hafter]
    exact congrArg Prod.fst htransition
  have hfinalState : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start z
      span active).finalState.upDecoderBank i = ⟨[], channel.completed ++ [first, window]⟩ :=
    hfinal.symm.trans hrun
  refine ⟨first, last, ⟨index.val, by simpa only [
      ReferenceCoordinatorUpIntervalWindow.intervalRounds,
      ReferenceCoordinatorUpIntervalWindow.intervalRecords, List.length_map] using index.isLt⟩,
    r, d, hfirst, hfirstLen, hwindowLen, hchron, hpure, hlast, hdecision, hr,
    htime, hd, hi, hdt, hlastSample, hbank, hreplay, ?_, hdecoder, hbatch, hexpect,
    hfinalState, ?_⟩
  · rw [← hbefore, hentry]
    exact hpending
  · rw [hbatch]
    exact pure_batch_raw_cases window word hpure

private theorem live_failure_isSome
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration =
        .dagger →
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).failure.isSome =
        true := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · simp [ReferenceActivePhysicalStep.coordinatorFailure]
  · dsimp only
    split
    · simp [ReferenceActivePhysicalStep.coordinatorFailure]
    · split
      · simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · split
        · simp [ReferenceActivePhysicalStep.coordinatorFailure]
        · simp

private theorem collectionFinish_failure_isSome
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration =
        .dagger →
      (ReferenceActivePhysicalStep.collectionFinish (x := x)
        payload started recording cut).failure.isSome = true := by
  cases hr : cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.collectionFinish, hr,
      ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      simp only [ReferenceActivePhysicalStep.collectionFinish, hr]
      split
      · simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · simp [ReferenceActivePhysicalStep.coordinatorFailure]
      · split
        · simp [ReferenceActivePhysicalStep.coordinatorFailure]
        · simp

private theorem collection_failure_isSome
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration =
        .dagger →
      (ReferenceActivePhysicalStep.collectionPostChoice
        prepared payload ledger started weights).failure.isSome = true := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  split
  · simp [ReferenceActivePhysicalStep.coordinatorFailure]
  · dsimp only
    split
    · simp [ReferenceActivePhysicalStep.coordinatorFailure]
    · simp [ReferenceActivePhysicalStep.coordinatorFailure]
    · exact collectionFinish_failure_isSome x _ _ _ _

private theorem prepared_dagger_requires_input_dagger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hdagger : (ReferenceActivePhysicalStep.prepare x).coordinator = .dagger) :
    x.state.coordinator = .dagger := by
  change ReferenceActivePhysicalStep.dispatch x = .dagger at hdagger
  unfold ReferenceActivePhysicalStep.dispatch at hdagger
  cases hs : x.state.coordinator with
  | first =>
      simp only [hs, CoordinatorRoundDispatch.dispatch] at hdagger
      cases CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) <;>
        contradiction
  | live registers owned base =>
      simp only [hs, CoordinatorRoundDispatch.dispatch] at hdagger
      cases CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x registers owned base) <;> contradiction
  | collection payload ledger proposal =>
      simp only [hs] at hdagger
      split at hdagger
      · rename_i hcutoff
        simp only [CoordinatorRoundDispatch.dispatch] at hdagger
        cases CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger proposal
              ⟨ledger.cutoff - 1, by omega⟩) ⟨ledger.cutoff - 1, by omega⟩) <;> contradiction
      · contradiction
  | dagger => rfl

/-- The first physical transition into coordinator dagger has an actual
retained failure constructor; an administrative no-call is never sufficient. -/
theorem first_dagger_record_failure
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (hbefore : r.input.state.coordinator ≠ .dagger)
    (hafter : r.output.next.coordinator = .dagger) :
    ∃ reason : ReferenceActivePhysicalStep.CoordinatorFailure,
      r.output.coordinator.failure = some reason := by
  have hprepared : (ReferenceActivePhysicalStep.prepare r.input).coordinator ≠ .dagger :=
    fun h => hbefore (prepared_dagger_requires_input_dagger r.input h)
  have hsome : r.output.coordinator.failure.isSome = true := by
    rw [r.output_eq] at hafter ⊢
    change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.configuration = .dagger at hafter
    change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.failure.isSome = true
    unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at hafter ⊢
    by_cases hsel : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = none
    · rw [dite_eq_left hsel] at hafter ⊢
      cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator <;>
        simp only [ReferenceActivePhysicalStep.coordinatorFailure, Option.isSome_some]
      exact (hprepared hc).elim
    · rw [dite_eq_right hsel] at hafter ⊢
      cases hc : (ReferenceActivePhysicalStep.prepare r.input).coordinator with
      | first outcome =>
          cases outcome <;> simp only [hc] at hafter ⊢ <;> try rfl
          exact live_failure_isSome r.input _ _ _ _ _ hafter
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc] at hafter ⊢ <;> try rfl
          · exact collection_failure_isSome r.input _ _ _ _ _ hafter
          · exact live_failure_isSome r.input _ _ _ _ _ hafter
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc] at hafter ⊢ <;> try rfl
          · exact collection_failure_isSome r.input _ _ _ _ _ hafter
          · exact live_failure_isSome r.input _ _ _ _ _ hafter
      | invalidCollectionCutoff => rfl
      | dagger => exact (hprepared hc).elim
  cases hf : r.output.coordinator.failure with
  | none => simp only [hf, Option.isSome_none, Bool.false_eq_true] at hsome
  | some reason => exact ⟨reason, rfl⟩

private theorem linked_prefix_connected
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ q : Fin records.length,
      (records.get q).input.state = Z q.val ∧
        (records.get q).output.next = Z (q.val + 1))
    (n : ℕ) (hn : n ≤ records.length) :
    ReferenceActivePhysicalHorizon.Connected (Z 0) (records.take n) (Z n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlt : n < records.length := by omega
      have hl := hlinks ⟨n, hlt⟩
      rw [← hl.2, List.take_succ_eq_append_getElem hlt]
      exact ReferenceActivePhysicalHorizon.Connected.append_one _ _ (ih (by omega)) hl.1

private theorem first_dagger_index
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (Z : ℕ → ReferenceActivePhysicalStep.State p rate)
    (hlinks : ∀ q : Fin records.length,
      (records.get q).input.state = Z q.val ∧
        (records.get q).output.next = Z (q.val + 1))
    (hinitial : (Z 0).coordinator ≠ .dagger)
    (hfailure : ¬ ∀ q : Fin records.length, (records.get q).output.next.coordinator ≠ .dagger) :
    ∃ q : Fin records.length,
      (Z q.val).coordinator ≠ .dagger ∧ (records.get q).output.next.coordinator = .dagger ∧
      (∀ j : Fin records.length, j.val < q.val →
        (records.get j).output.next.coordinator ≠ .dagger) ∧
      ∃ reason : ReferenceActivePhysicalStep.CoordinatorFailure,
        (records.get q).output.coordinator.failure = some reason := by
  classical
  have hex : ∃ n, ∃ hn : n < records.length,
      (records.get ⟨n, hn⟩).output.next.coordinator = .dagger := by
    push Not at hfailure
    obtain ⟨q, hq⟩ := hfailure
    exact ⟨q.val, q.isLt, hq⟩
  let n := Nat.find hex
  obtain ⟨hn, hnext⟩ := Nat.find_spec hex
  let q : Fin records.length := ⟨n, hn⟩
  have hprevious : ∀ j : Fin records.length, j.val < q.val →
      (records.get j).output.next.coordinator ≠ .dagger := by
    intro j hj he
    exact Nat.find_min hex hj ⟨j.isLt, he⟩
  have hbefore : (Z n).coordinator ≠ .dagger := by
    cases hnzero : n with
    | zero => exact hinitial
    | succ k =>
        have hk : k < records.length := by omega
        have hprev := hprevious ⟨k, hk⟩ (by change k < n; omega)
        have hl := (hlinks ⟨k, hk⟩).2
        exact fun he => hprev (by rw [hl]; exact he)
  refine ⟨q, hbefore, hnext, hprevious, ?_⟩
  apply first_dagger_record_failure (records.get q) _ hnext
  rw [(hlinks q).1]
  exact hbefore

private theorem connected_bank_replay
    {initial final : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate)}
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hinvariant : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : final.coordinator ≠ .dagger) :
    final.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay initial.upDecoderBank
      (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics records) := by
  induction records generalizing initial with
  | nil =>
      subst final
      rfl
  | cons r rest ih =>
      rcases hchain with ⟨hinput, htail⟩
      have hrInv : ReferenceUpDecoderBankInvariant.upBankInvariant r.input.state :=
        hinput.symm ▸ hinvariant
      have hnextInv : ReferenceUpDecoderBankInvariant.upBankInvariant r.output.next := by
        rw [r.output_eq]
        exact ReferenceUpDecoderBankInvariant.step_upBankInvariant hrInv
      have hnext : r.output.next.coordinator ≠ .dagger := by
        intro hd
        exact hordinary (ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hd).1
      have hr := ReferenceCoordinatorUpDecoderReplay.ordinaryRecord_upDecoderBank_replay r hrInv hnext
      have ht := ih htail hnextInv
      rw [ht, hr, hinput]
      cases hd : r.output.coordinator.up <;>
        simp [ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics,
          ReferenceCoordinatorUpDecoderReplay.replay,
          ReferenceCoordinatorUpDecoderReplay.replayOption, hd, List.foldl_cons]

private theorem referenceDownCut_none_not_accepted
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (before after : ReferencePrelaunchFollower.State p rate.eta)
    (raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (scan : FollowerCutoffScan.ScanResult p.T) (registers : ℕ × ℕ) (lastService : ℕ) :
    (ReferenceDownReception.referenceDownCut (eta := rate.eta) p none i row t observation rate before).outcome ≠
      .accepted before after raw message scan registers lastService := by
  intro h
  unfold ReferenceDownReception.referenceDownCut at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · dsimp only at h
            split at h
            · rename_i hmatch
              simp only [ReferenceDownReception.expectedDownFlatWord] at hmatch
              simp only [hmatch, ReferenceDownReception.ordinaryParse,
                OrdinaryMessageCodec.parseDown] at h
              cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

private theorem retainedDown_not_on_dagger
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (i : Fin (p.m - 1))
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hout : r.output.next.followers i = .ordinary next memory)
    (hretained : ReferenceAcceptedUpFollowerHistory.RetainedDown r i message) :
    r.input.state.coordinator ≠ .dagger := by
  intro hdagger
  rcases r with ⟨input, output, output_eq⟩
  cases output_eq
  let prepared := ReferenceActivePhysicalStep.prepare input
  let sender := prepared.followers.followers i
  let observation := prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hcoord : prepared.coordinator = .dagger :=
    ReferenceActivePhysicalStep.dispatch_dagger input hdagger
  have hview : prepared.coordinator.downView = none := by rw [hcoord]; rfl
  have hout' : (ReferenceActivePhysicalStep.finishFollower
      prepared.coordinator.downView sender observation).configuration = .ordinary next memory := hout
  obtain ⟨choice, choiceMemory, post, _, _, _, hdownInput, hdown⟩ :=
    ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion
      prepared.coordinator.downView sender observation next memory hout'
  rcases hretained with ⟨logged, cut, after, raw, scan, registers, lastService,
    hrecordInput, hrecordDown, houtcome⟩
  have hactualInput : (ReferenceActivePhysicalStep.finishFollower
      prepared.coordinator.downView sender observation).downInput = some logged := hrecordInput
  have hactual : (ReferenceActivePhysicalStep.finishFollower
      prepared.coordinator.downView sender observation).down = some cut := hrecordDown
  have hrecord := hdown.symm.trans hactual
  have hinput := hdownInput.symm.trans hactualInput
  rw [hview] at hrecord hinput
  unfold ReferenceActivePhysicalStep.recordFollower at hrecord hinput
  split at hrecord
  · rename_i hu
    simp only [dite_eq_left hu] at hinput
    split at hrecord
    · cases hrecord
    · rename_i recorded hlogging
      simp only [hlogging] at hinput
      have hlogged : recorded = logged := Option.some.inj hinput
      subst recorded
      have heq := Option.some.inj hrecord
      subst cut
      exact referenceDownCut_none_not_accepted (rate := rate) _ _ _ _ _ _ _ _ _ _ _ houtcome
  · cases hrecord

private theorem physical_positive_prefix_succ
    (records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (q : Fin records.length) :
    physicalPositives (records.take (q.val + 1)) i =
      physicalPositives (records.take q.val) i ++
        ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (records.get q) i := by
  simp only [physicalPositives,
    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
      _ i hchronological.take]
  rw [List.take_succ_eq_append_getElem q.isLt]
  simp only [ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries,
    List.flatMap_append, List.flatMap_singleton, List.get_eq_getElem]

/-- Actual replacement-history cut, retaining the current-word origin, absent
case, physical obstruction, and surviving two-completion geometry. -/
theorem complete_first_replacement_collection_pure_up_window_cut
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L := X.length
        C.length = L ∧ X = birth :: tail ∧
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            (∀ q : Fin K.length, (K.get q).input.time.val + 1 = u + q.val) ∧
            (Z 0 = cut.input.state ∧
              (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
              (∀ q : Fin K.length, (K.get q).input.state = Z q.val ∧
                (K.get q).output.next = Z (q.val + 1))) ∧
            (∀ i : Fin (p.m - 1),
              (∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p),
                ((b = 0 ∧
                  (cut.output.preparation.followers.followers i).configuration =
                    .ordinary anchor memory ∧
                  ∃! x : Fin X.length,
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get x) i (M i)) ∨
                 (∃ q : Fin K.length, b = q.val + 1 ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                  (∀ j : Fin K.length, j.val < q.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get j) i (M i)) ∧
                  (K.get q).output.next.followers i = .ordinary anchor memory ∧
                  (Z (q.val + 1)).followers i = .ordinary anchor memory ∧
                  ∀ state mem, (cut.output.preparation.followers.followers i).configuration =
                    .ordinary state mem → state.lastDown ≠ some (M i))) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid anchor ∧
                anchor.lastDown = some (M i) ∧
                (∃ last lastMemory, (E W.length).followers i = .ordinary last lastMemory ∧
                  last.status = .unoccupied ∧ last.lastDown = some (M i) ∧
                  ReferenceFollowerReplyChronology.reply last =
                    ReferenceFollowerReplyChronology.reply anchor) ∧
                ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                (∀ j : Fin K.length, b ≤ j.val → ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown = some (M i) ∧
                  ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor ∧
                  (ReferenceActivePhysicalStep.upSenderIndex (K.get j).input = i →
                    PublicDiscreteDraws.slotDraw ((K.get j).input.row.2
                      (K.get j).input.time).1 = PublicDiscreteDraws.upSlot →
                    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (K.get j).input.row
                      ((K.get j).input.state.activations i) (K.get j).input.time state = .offer U ∧
                    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare
                      (K.get j).input) = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                  (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    (K.get j).output.coordinator.up = some d → d.input.selectedFollower = i →
                    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
                    d.input.time = (K.get j).input.time ∧ d.input.selectedFollower = i ∧
                    d.input.slot = PublicDiscreteDraws.slotDraw
                      ((K.get j).input.row.2 (K.get j).input.time).1 ∧
                    d.input.affineSample = ((K.get j).input.row.2 (K.get j).input.time).2 (1, i) ∧
                    AffineChannelLaw.affineHash d.input.affineSample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)) ∧
                (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.drop b) i,
                  ∃ r ∈ K.drop b, ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
                    entry.time = r.input.time ∧
                    d.input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ∧
                    entry.sample = d.input.affineSample ∧
                    d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
                    AffineChannelLaw.affineHash entry.sample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1) ∧
                let H := K.drop b
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                (∀ e ∈ physicalPositives H i,
                  AffineBatchDecoder.equation e.sample
                    (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                ((∃ (q : Fin K.length) (reason : ReferenceActivePhysicalStep.CoordinatorFailure),
                    b ≤ q.val + 1 ∧ (Z q.val).coordinator ≠ .dagger ∧
                    (K.get q).output.next.coordinator = .dagger ∧
                    (K.get q).output.coordinator.failure = some reason ∧
                    (∀ j : Fin K.length, j.val < q.val →
                      (K.get j).output.next.coordinator ≠ .dagger) ∧
                    (Z q.val).upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
                      (Z 0).upDecoderBank
                      (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (K.take q.val)) ∧
                    AffineBatchDecoder.run p
                      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (K.take q.val) i)
                      ((K.take q.val).map (fun r => r.input.time)) ((Z 0).upDecoderBank i) =
                        (Z q.val).upDecoderBank i ∧
                    (b ≤ q.val → AffineBatchDecoder.run p
                      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (H.take (q.val - b)) i)
                      ((H.take (q.val - b)).map (fun r => r.input.time)) channel = (Z q.val).upDecoderBank i ∧
                      (physicalPositives (H.take (q.val + 1 - b)) i).length =
                        (physicalPositives (H.take (q.val - b)) i).length +
                          (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length) ∧
                    (physicalPositives (K.take (q.val + 1)) i).length =
                      (physicalPositives (K.take q.val) i).length +
                        (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length ∧
                    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length ≤ 1 ∧
                    (match ReferenceCollectionPhaseHistory.executedTail (K.get q).input with
                    | none => ReferenceCollectionPhaseHistory.executedTail (K.get q).input = none
                    | some t =>
                      match t.reception with
                      | none =>
                        CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare (K.get q).input)
                            t.payload t.started t.weights) = none ∨
                        ∃ recording : CoordinatorRecordingOperation.Output p,
                          CoordinatorRecorderComplementBridge.run
                            (ReferenceActivePhysicalStep.collectionRecordingInput
                              (ReferenceActivePhysicalStep.prepare (K.get q).input)
                              t.payload t.started t.weights) = some recording ∧
                          (CoordinatorCollectionLedger.startRound t.ledger ((K.get q).input.time.val + 1)
                            (ReferenceActivePhysicalStep.collectionEnabled t.ledger (K.get q).input.time)
                            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .invalid ∨
                           ∃ rejected, CoordinatorCollectionLedger.startRound t.ledger
                            ((K.get q).input.time.val + 1)
                            (ReferenceActivePhysicalStep.collectionEnabled t.ledger (K.get q).input.time)
                            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .rejected rejected)
                      | some (started, received) =>
                        let rin := ReferenceUpReception.receptionInputAtRow rate (K.get q).input.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare (K.get q).input) started) (K.get q).input.time
                        match received.diagnostic with
                        | none => CoordinatorUpReception.receptionInputCheck rin = false ∧
                            received.result = .invalid ∧ (K.get q).output.coordinator.up = none
                        | some d => d.input = rin ∧
                            d.expected = ReferenceActivePhysicalStep.upExpected
                              (ReferenceActivePhysicalStep.prepare (K.get q).input) ∧
                            d.raw = (CoordinatorUpReception.decoderTransition rin).2 ∧
                            d.parsed = ReferenceUpReception.rawParsedOutput rate rin ∧
                            (K.get q).output.coordinator.up = some d) ∧
                    (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                      (K.get q).output.coordinator.up = some d →
                      d.input.upDecoderBank = (Z q.val).upDecoderBank ∧
                      d.expected = ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare (K.get q).input) ∧
                      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
                      ∃ ledger,
                        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := (K.get q).input) = some ledger ∧
                        CoordinatorUpReception.receptionInputCheck
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput (K.get q).input ledger) = true ∧
                        d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput (K.get q).input ledger ∧
                        d.decoderAfter = (CoordinatorUpReception.decoderTransition
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput (K.get q).input ledger)).1 ∧
                        (((ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare (K.get q).input) ledger).result = .invalid ∧
                            (K.get q).output.next.upDecoderBank = (K.get q).input.state.upDecoderBank) ∨
                          ∃ out,
                            ((ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare (K.get q).input) ledger).result = .success out ∨
                             (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare (K.get q).input) ledger).result = .rejected out) ∧
                            out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
                            (K.get q).output.next.upDecoderBank = out.2))) ∨
                  ((∀ q : Fin K.length, (K.get q).output.next.coordinator ≠ .dagger) ∧
                    (((physicalPositives H i).length < need ∧
                        ((∀ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input ≠ some i) ∨
                         ∃ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i ∧
                           ∃ message, ReferenceCollectionPhaseHistory.AcceptedUp r.input i message ∧
                             ∃ ledger saved, (E W.length).coordinator = .collection payload ledger saved ∧
                               i ∉ ledger.pending ∧ ((E W.length).upDecoderBank i).pending = [])) ∨
                      ∃ m : ℕ, 0 < m ∧ m ≤ H.length ∧
                        (physicalPositives (H.take m) i).length = need ∧
                        (∀ n : ℕ, n < m → (physicalPositives (H.take n) i).length < need) ∧
                        let positive := physicalPositives (H.take m) i
                        let window := positive.drop (Q - channel.pending.length)
                        ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                          (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                          (index : Fin (H.take m).length)
                          (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
                          (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                          first = channel.pending ++ positive.take (Q - channel.pending.length) ∧
                          first.length = Q ∧ window.length = Q ∧
                          window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                          (∀ e ∈ window, AffineBatchDecoder.equation e.sample
                            (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                          last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
                          r ∈ H.take m ∧ r.input.time = last.time ∧
                          r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                          d.input.time = r.input.time ∧ last.sample = d.input.affineSample ∧
                          d.input.upDecoderBank = r.input.state.upDecoderBank ∧
                          r.input.state.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
                            (Z b).upDecoderBank
                            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics ((H.take m).take index.val)) ∧
                          (d.input.upDecoderBank i).pending ++ [last] = window ∧
                          d.decoderAfter = ⟨[], channel.completed ++ [first, window]⟩ ∧
                          d.raw = AffineBatchDecoder.batchOutput window ∧
                          d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                          (Z (b + m)).upDecoderBank i = ⟨[], channel.completed ++ [first, window]⟩ ∧
                          ((d.raw = none ∧ ∃ other,
                              other ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta U ∧
                              ∀ e ∈ window, AffineBatchDecoder.equation e.sample other) ∨
                            (d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                              ∀ other, (∀ e ∈ window, AffineBatchDecoder.equation e.sample other) →
                                other = ActiveFollowerArmChoice.offeredUpWord rate.eta U)))))) ∨
              ((∀ j : Fin K.length, ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                    ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧
                      old.val.sigma < (M i).val.sigma)) ∧
               (∃ last memory, (E W.length).followers i = .ordinary last memory ∧
                  last.status = .unoccupied ∧ last.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart last < (M i).val.sigma ∧
                  ((last.lastDown = none ∧ last.S = 0 ∧ last.delta = 0 ∧ last.backlog = 0) ∨
                    ∃ old, last.lastDown = some old ∧ 0 < old.val.sigma ∧
                      old.val.sigma < (M i).val.sigma)) ∧
               (∀ q : Fin K.length,
                 ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i)) ∧
               (∀ q : Fin K.length, ∀ old,
                 ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i old →
                 old.val.sigma < (M i).val.sigma) ∧
               R[c + 1 + W.length]? = none)) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState
                  rate source rewards C_star C_h = some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved,
                  (E W.length).coordinator = .collection payload ledger saved ∧
                  next.input.state.coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K,
                    ∃ U, ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hO := ReferenceFirstReplacementCollectionUpOfferCut.complete_first_replacement_collection_up_offer_cut
    rate source rewards C_star C_h
  have hR := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate source rewards C_star C_h
  dsimp only at hO hR ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hO hR ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hO hR ⊢
      cases outcome <;> try trivial
      rename_i core consistent started hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hO hR ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      let X := (R.drop v).take (1 + tail.length)
      rcases hO with ⟨hCL, hX, hO⟩
      rcases hR with ⟨_, _, hR⟩
      refine ⟨hCL, hX, ?_⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [tail, c, hc] at hO hR ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hO hR ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hO hR ⊢
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hO with ⟨hcalendar, hZ, hfollowers, hnext⟩
          rcases hR with ⟨hgeometry, hreceptions, _⟩
          refine ⟨hcalendar, hZ, ?_, hnext⟩
          have hKprefix : K <+: R.drop c := by
            obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          have hchronR := complete_records_chronological rate source rewards C_star C_h
          have hchronK : K.Pairwise
              (fun earlier later => earlier.input.time.val < later.input.time.val) :=
            List.Pairwise.sublist hKprefix.sublist hchronR.drop
          obtain ⟨initial, active, hlaunch, hfirst, hbank, hInvInitial, hseed, hfull, hRuns⟩ :=
            source_interval_runs rate source rewards C_star C_h c cut hc K hKprefix
          have hInv : ∀ j, j ≤ K.length → ReferenceUpDecoderBankInvariant.upBankInvariant (Z j) := by
            intro j hj
            obtain ⟨span, _, hend⟩ := hRuns j hj
            change (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + j) span active).finalState = Z j at hend
            rw [← hend]
            exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + j) span active hInvInitial
          have hlinks : ∀ q : Fin K.length,
              (K.get q).input.state = Z q.val ∧ (K.get q).output.next = Z (q.val + 1) := hZ.2.2
          have hOrdinaryZero : (Z 0).coordinator ≠ .dagger := by
            change cut.input.state.coordinator ≠ .dagger
            intro hd
            have hp := ReferenceActivePhysicalStep.dispatch_dagger cut.input hd
            change (ReferenceActivePhysicalStep.prepare cut.input).coordinator = .dagger at hp
            have hactual := hcut
            rw [cut.output_eq] at hactual
            change (ReferenceActivePhysicalStep.prepare cut.input).coordinator = _ at hactual
            rw [hp] at hactual
            cases hactual
          intro i
          rcases hfollowers i with hcurrent | habsent
          · rcases hcurrent with ⟨b, anchor, memory, horigin, hbK, hstatus, hdomain,
                hcurrent, hend, U, hfields, hsigma, hpositive, hchoices, hentries⟩
            refine Or.inl ⟨b, anchor, memory, horigin, hbK, hstatus, hdomain,
              hcurrent, hend, U, hfields, hsigma, hpositive, hchoices, hentries, ?_⟩
            let H := K.drop b
            let channel := (Z b).upDecoderBank i
            let Q := AffineBatchDecoder.quota p
            let need := Q - channel.pending.length + Q
            have hchronH : H.Pairwise
                (fun earlier later => earlier.input.time.val < later.input.time.val) := hchronK.drop
            have hpure : ∀ e ∈ physicalPositives H i,
                AffineBatchDecoder.equation e.sample
                  (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
              intro e he
              rw [physicalPositives,
                ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained H i hchronH] at he
              obtain ⟨_, _, _, _, _, _, _, _, _, _, heq⟩ := hentries e he
              exact (AffineBatchDecoder.equation_iff_affineHash _ _).mpr heq
            refine ⟨hpure, ?_⟩
            by_cases hsurvive : ∀ q : Fin K.length, (K.get q).output.next.coordinator ≠ .dagger
            · right
              refine ⟨hsurvive, ?_⟩
              have hOrdinary : ∀ j, j ≤ K.length → (Z j).coordinator ≠ .dagger := by
                intro j hj
                cases j with
                | zero => exact hOrdinaryZero
                | succ k =>
                    have hk : k < K.length := by omega
                    have hl := (hlinks ⟨k, hk⟩).2
                    exact fun he => hsurvive ⟨k, hk⟩ (by rw [hl]; exact he)
              have hneed : 0 < need := by
                have := AffineBatchDecoder.quota_pos p
                dsimp only [need, Q]
                omega
              rcases physical_positive_prefix_cut H i need hneed hchronH with
                hshort | ⟨m, hm, hmH, hcount, hleast⟩
              · left
                refine ⟨hshort, ?_⟩
                by_cases ha : ∃ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i
                · obtain ⟨r, hr, ha⟩ := ha
                  obtain ⟨message, haccepted⟩ := ReferenceCollectionPhaseHistory.acceptedLabel_witness ha
                  have hZe : Z K.length = E W.length := by
                    simp only [Z, E, K, List.length_cons, List.take_length,
                      ReferenceCollectionSegmentExtraction.endpointState, List.foldl_cons,
                      List.take_succ_cons]
                  rcases hgeometry W.length le_rfl with hdagger | ⟨finalLedger, saved, hcoord, _, _, hpending⟩
                  · exact (hOrdinary K.length le_rfl (by rw [hZe]; exact hdagger)).elim
                  · change (E W.length).coordinator = .collection payload finalLedger saved at hcoord
                    have hrK : r ∈ K := List.mem_of_mem_drop hr
                    have hlabel : i ∈ ReferenceCollectionPhaseHistory.acceptedLabels K :=
                      List.mem_filterMap.mpr ⟨r, hrK, ha⟩
                    have hnotPending : i ∉ finalLedger.pending := by
                      rw [hpending]
                      exact fun hi => (Finset.mem_sdiff.mp hi).2 (by
                        simpa [K, W, c, tail] using hlabel)
                    have hfinalInv := hInv K.length le_rfl
                    rw [hZe] at hfinalInv
                    simp only [ReferenceUpDecoderBankInvariant.upBankInvariant,
                      ReferenceUpDecoderBankInvariant.coordinatorBankInvariant, hcoord] at hfinalInv
                    exact Or.inr ⟨r, hr, ha, message, haccepted, finalLedger, saved,
                      hcoord, hnotPending, hfinalInv.2 i hnotPending⟩
                · exact Or.inl (fun r hr he => ha ⟨r, hr, he⟩)
              · right
                refine ⟨m, hm, hmH, hcount, hleast, ?_⟩
                have hbm : b + m ≤ K.length := by
                  change m ≤ (K.drop b).length at hmH
                  simp only [List.length_drop] at hmH
                  omega
                obtain ⟨span, hdrop, hendRun⟩ := hRuns (b + m) hbm
                obtain ⟨spanPre, _, hpre⟩ := hRuns b hbK
                change (ReferenceActivePhysicalHorizon.run initial source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                  (c + b) spanPre active).finalState = Z b at hpre
                let full := ReferenceActivePhysicalHorizon.run initial source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                  (c + (b + m)) span active
                have hinterval : full.records.drop (c + b) = H.take m := by
                  rw [← List.drop_drop, hdrop, List.drop_take]
                  simp only [Nat.add_sub_cancel_left]
                  rfl
                change full.finalState = Z (b + m) at hendRun
                have hfinalOrdinary : full.finalState.coordinator ≠ .dagger := by
                  rw [hendRun]
                  exact hOrdinary (b + m) hbm
                have hcountRun : (physicalPositives (full.records.drop (c + b)) i).length =
                    AffineBatchDecoder.quota p -
                      ((ReferenceActivePhysicalHorizon.run initial source.1.2
                        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                        (c + b) spanPre active).finalState.upDecoderBank i).pending.length +
                      AffineBatchDecoder.quota p := by
                  rw [hinterval, hpre]
                  exact hcount
                have hprefixPure : ∀ e ∈ physicalPositives (H.take m) i,
                    AffineBatchDecoder.equation e.sample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
                  intro e he
                  rw [physicalPositives,
                    ReferenceCoordinatorUpIntervalWindow.actual_trace_positives_eq_retained
                      (H.take m) i hchronH.take] at he
                  obtain ⟨r, hr, he⟩ := List.mem_flatMap.mp he
                  have hwhole : e ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries H i :=
                    List.mem_flatMap.mpr ⟨r, List.mem_of_mem_take hr, he⟩
                  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq⟩ := hentries e hwhole
                  exact (AffineBatchDecoder.equation_iff_affineHash _ _).mpr heq
                have hexpected : ∀ r ∈ full.records.drop (c + b),
                    ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                      r.output.coordinator.up = some d → d.input.selectedFollower = i →
                      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
                      d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
                  intro r hr d hd hselected heligible
                  rw [hinterval] at hr
                  have hrH : r ∈ K.drop b := List.mem_of_mem_take hr
                  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hrH
                  have hq : b + j < K.length := by
                    simp only [List.length_drop] at hj
                    omega
                  have hget' : K.get ⟨b + j, hq⟩ = r := by
                    simpa only [List.get_eq_getElem, List.getElem_drop] using hget
                  obtain ⟨state, mem, _, _, _, _, hoffer, _⟩ :=
                    hchoices ⟨b + j, hq⟩ (Nat.le_add_right b j)
                  rw [hget'] at hoffer
                  obtain ⟨_, _, _, _, _, _, hsender, _, hslot, _⟩ :=
                    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r d hd
                  have hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i :=
                    hsender.symm.trans hselected
                  have hgate := (CoordinatorUpReception.roundInput_selected_iff_gate d.input).mp heligible.1
                  have hslot' : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                      PublicDiscreteDraws.upSlot := hslot.symm.trans hgate.2.1
                  exact (retained_diagnostic_raw_expected r d hd).1.trans (hoffer hindex hslot').2
                have hsaved := run_saved_pure_window initial source.1.2
                  (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                  (c + b) (c + (b + m)) (by omega) span active hInvInitial hfinalOrdinary i
                  (hseed i) (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hcountRun
                  (by rw [hinterval]; exact hprefixPure) hexpected
                dsimp only [full] at hinterval hendRun
                dsimp only at hsaved ⊢
                obtain ⟨first, last, index, r, d, hsaved⟩ := hsaved
                refine ⟨first, last, ⟨index.val, ?_⟩, r, d, ?_⟩
                · change index.val < (H.take m).length
                  rw [← hinterval]
                  exact index.isLt
                · simp only [hinterval, hpre, hendRun] at hsaved
                  convert hsaved using 1
                  rfl
            · left
              obtain ⟨q, hbefore, hafter, hprevious, reason, hreason⟩ :=
                first_dagger_index K Z hlinks hOrdinaryZero hsurvive
              have hbirthBound : b ≤ q.val + 1 := by
                rcases horigin with ⟨hbzero, _⟩ | ⟨birthIndex, hbindex, hretained, _, houtput, _⟩
                · omega
                · by_contra hnot
                  have hbetween : q.val + 1 ≤ birthIndex.val := by omega
                  have hchain := linked_prefix_connected K Z hlinks K.length le_rfl
                  simp only [List.take_length] at hchain
                  have htail := ReferenceCollectionSegmentExtraction.connected_drop
                    K (Z 0) (Z K.length) (q.val + 1) hchain
                  change ReferenceActivePhysicalHorizon.Connected
                    (Z (q.val + 1)) (K.drop (q.val + 1)) (Z K.length) at htail
                  have hdagger : (Z (q.val + 1)).coordinator = .dagger := by
                    rw [← (hlinks q).2]
                    exact hafter
                  have hmem : K.get birthIndex ∈ K.drop (q.val + 1) := by
                    apply List.mem_iff_getElem.mpr
                    refine ⟨birthIndex.val - (q.val + 1), ?_, ?_⟩
                    · simp only [List.length_drop]
                      have hbirthLt : birthIndex.val < K.length := birthIndex.isLt
                      have hqLt : q.val < K.length := q.isLt
                      omega
                    · simp only [List.getElem_drop, List.get_eq_getElem]
                      congr 1
                      omega
                  exact (retainedDown_not_on_dagger (K.get birthIndex) i (M i)
                    anchor memory houtput hretained)
                    ((ReferenceActivePhysicalHorizon.Connected.coordinator_dagger htail hdagger).2
                      (K.get birthIndex) hmem)
              have hprefix := linked_prefix_connected K Z hlinks q.val (Nat.le_of_lt q.isLt)
              have hreplay := connected_bank_replay hprefix (hInv 0 (Nat.zero_le _)) hbefore
              have hfold := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_run_eq_replay
                (K.take q.val) i hchronK.take (Z 0).upDecoderBank
                ((hInv 0 (Nat.zero_le _)).1 i)
              have hsuffixReplay : b ≤ q.val → AffineBatchDecoder.run p
                  (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (H.take (q.val - b)) i)
                  ((H.take (q.val - b)).map (fun r => r.input.time)) channel = (Z q.val).upDecoderBank i ∧
                  (physicalPositives (H.take (q.val + 1 - b)) i).length =
                    (physicalPositives (H.take (q.val - b)) i).length +
                      (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length := by
                intro hbq
                have hsuffix := ReferenceCollectionSegmentExtraction.connected_drop
                  (K.take q.val) (Z 0) (Z q.val) b hprefix
                have hleft : ReferenceCollectionSegmentExtraction.endpointState
                    (Z 0) ((K.take q.val).take b) = Z b := by
                  rw [List.take_take, Nat.min_eq_left hbq]
                  rfl
                have hright : (K.take q.val).drop b = H.take (q.val - b) := by
                  rw [List.drop_take]
                rw [hleft, hright] at hsuffix
                have hr := connected_bank_replay hsuffix (hInv b hbK) hbefore
                have hf := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_run_eq_replay
                  (H.take (q.val - b)) i hchronH.take (Z b).upDecoderBank ((hInv b hbK).1 i)
                refine ⟨hf.trans (congrArg (fun bank => bank i) hr).symm, ?_⟩
                have hindex : q.val - b < H.length := by
                  change q.val - b < (K.drop b).length
                  simp only [List.length_drop]
                  have hqLt : q.val < K.length := q.isLt
                  omega
                let index : Fin H.length := ⟨q.val - b, hindex⟩
                have hget : H.get index = K.get q := by
                  simp only [H, index, List.get_eq_getElem, List.getElem_drop]
                  congr 1
                  omega
                have hcount := congrArg List.length (physical_positive_prefix_succ H i hchronH index)
                rw [hget, List.length_append] at hcount
                have heq : q.val - b + 1 = q.val + 1 - b := by omega
                simpa only [index, heq] using hcount
              refine ⟨q, reason, hbirthBound, hbefore, hafter, hreason, hprevious, hreplay,
                hfold.trans (congrArg (fun bank => bank i) hreplay).symm, hsuffixReplay,
                ?_, record_positive_length_le_one (K.get q) i, ?_, ?_⟩
              · exact congrArg List.length (physical_positive_prefix_succ K i hchronK q) |>.trans
                  List.length_append
              · have hstage := hreceptions q
                cases ht : ReferenceCollectionPhaseHistory.executedTail (K.get q).input with
                | none => rfl
                | some t =>
                  dsimp only [K, W, c, tail] at ht
                  simp only [ht] at hstage
                  cases hr : t.reception with
                  | none => simpa only [hr] using hstage
                  | some pair =>
                    rcases pair with ⟨started, received⟩
                    simp only [hr] at hstage
                    have hdiagnostic := hstage.2.2.2.2.2.2
                    cases hd : received.diagnostic <;>
                      simpa only [hr, hd] using hdiagnostic
              · intro d hd
                obtain ⟨_, _, _, hdbank, _⟩ :=
                  ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields (K.get q) d hd
                have hraw := retained_diagnostic_raw_expected (K.get q) d hd
                refine ⟨hdbank.trans (congrArg ReferenceActivePhysicalStep.State.upDecoderBank (hlinks q).1),
                  hraw.1, hraw.2, ?_⟩
                apply ReferenceCoordinatorUpPhysicalCall.record_up_commit_cases (K.get q) d hd
                rw [(hlinks q).1]
                exact hInv q.val (Nat.le_of_lt q.isLt)
          · exact Or.inr habsent

end Bandits.Support.ReferenceFirstReplacementCollectionPureUpWindowCut
