/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCutoffUpReplyInterval
public import Bandits.Support.ReferenceCoordinatorUpWindowCompletedCut

import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.TakeWhile
import Lean.Elab.Tactic.Omega

/-!
# Actual fixed UP word on a second completed decoder window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:36-53,70-88,105-124`,
`sources/zip4/manuscript/06_interruptions.tex:41-70,164-177,277-284,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

The export joins the actual cutoff word and actual second completed decoder
window. It retains the decoder's raw result, including failure, and returns a
separate dagger alternative for the focal follower. On the surviving ordinary
branch it produces every affine equation from actual positive physical
observations and the matching expected word at the located decoder call. A
unique-solution implication then identifies that call's actual raw output and
expected word. The local parser, reception test, and `AcceptedUp` witness are
not concluded here. No unique-solution event or follower-survival condition
is an input.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFixedUpCompletedWindowTruth

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

private theorem foldRounds_records_prefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin : ℕ) (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p origin))
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    acc.records =
      (entries.foldl
        (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards origin hmode)
        acc).records.take acc.records.length := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      let first := ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards
        origin hmode acc entry
      have hfirst : first.records = acc.records ++
          [⟨ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards origin
              hmode acc entry,
            ReferenceActivePhysicalStep.step
              (ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards origin
                hmode acc entry), rfl⟩] := rfl
      have hlen : first.records.length = acc.records.length + 1 := by
        simp [hfirst]
      have htail := ih first
      calc
        acc.records = first.records.take acc.records.length := by
          rw [hfirst, List.take_append_of_le_length (by omega)]
          simp
        _ = (entries.foldl
              (ReferenceActivePhysicalHorizon.foldRound initial rows selected rewards origin hmode)
              first).records.take acc.records.length := by
          rw [htail, List.take_take, Nat.min_eq_left (by omega)]

private theorem foldCalendar_records_prefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (origin intervalStart count : ℕ) (horigin : origin ≤ intervalStart)
    (hspan : intervalStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (acc : ReferenceActivePhysicalHorizon.Run initial) :
    acc.records =
      (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards origin
        intervalStart count horigin hspan hmode acc).records.take acc.records.length := by
  exact foldRounds_records_prefix initial rows selected rewards origin hmode
    (ReferenceActivePhysicalHorizon.calendarEntries origin intervalStart count horigin hspan)
    acc

private theorem run_prefix_records
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active).records := by
  let shortRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active
  have happend := ReferenceActivePhysicalHorizon.run_append initial rows selected rewards
    start n (total - n) (by omega) active
  have hfold :
      ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active =
        ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
          (start + n) (total - n) (by omega) (by omega) active shortRun := by
    simpa [shortRun, Nat.add_sub_of_le hn] using happend
  have hrecords := foldCalendar_records_prefix initial rows selected rewards start
    (start + n) (total - n) (by omega) (by omega) active shortRun
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start n (by omega) active
  calc
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active).records.take n =
        (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards start
          (start + n) (total - n) (by omega) (by omega) active shortRun).records.take n := by
      rw [hfold]
    _ = shortRun.records := by
      let extended := ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards
        start (start + n) (total - n) (by omega) (by omega) active shortRun
      have htake := congrArg (fun length => extended.records.take length) hlength.symm
      change extended.records.take n = shortRun.records
      exact htake.trans hrecords.symm

private theorem takeWhile_length_le {α : Type} (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length :=
  (List.takeWhile_prefix pred).length_le

private theorem fixed_window_count_bound
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k n : ℕ) (hk : k + 1 < count) (hn : n ≤
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records.drop
          (k + 2)).takeWhile
        fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input).length) :
    k + 2 + n ≤ count := by
  let E := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active
  let rest := E.records.drop (k + 2)
  let W := rest.takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  change n ≤ W.length at hn
  have htake : W.length ≤ rest.length := by
    dsimp [W, rest]
    exact takeWhile_length_le _ _
  have hcount : E.records.length = count := by
    dsimp [E]
    exact ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start
      count span active
  have hdrop : rest.length = count - (k + 2) := by
    simp [rest, List.length_drop, hcount]
  omega

theorem fixed_window_span
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k n : ℕ) (hk : k + 1 < count) (hn : n ≤
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records.drop
          (k + 2)).takeWhile
        fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input).length) :
    start + (k + 2 + n) ≤ p.T := by
  have hbound := fixed_window_count_bound initial rows selected rewards start count span active k n hk hn
  omega

private theorem getElem_takeWhile_eq {α : Type} (pred : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < (xs.takeWhile pred).length) :
    (xs.takeWhile pred)[k] = xs[k]'(by
      exact Nat.lt_of_lt_of_le hk (takeWhile_length_le pred xs)) := by
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

private theorem livePostChoice_up_none {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r owned base started).up = none := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

private theorem receiveUp_expected_provenance {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.receiveUp prepared ledger).diagnostic = some diagnostic) :
    diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared := by
  unfold ReferenceActivePhysicalStep.receiveUp at hd
  dsimp only at hd
  split at hd
  · cases Option.some.inj hd
    rfl
  · cases hd

private theorem collectionPostChoice_up_expected_provenance
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started
      weights).up = some diagnostic) :
    diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice at hd
  split at hd
  · cases hd
  · dsimp only at hd
    split at hd
    · cases hd
    · cases hd
    · rw [ReferenceActiveAffinePositiveTest.collectionFinish_up] at hd
      exact receiveUp_expected_provenance prepared _ diagnostic hd

private theorem observeCoordinator_up_expected_provenance
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : prepared.observeCoordinator.up = some diagnostic) :
    diagnostic.expected = ReferenceActivePhysicalStep.upExpected prepared := by
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator at hd
  split at hd
  · split at hd <;> cases hd
  · split at hd
    all_goals first
    | exact collectionPostChoice_up_expected_provenance prepared _ _ _ _ diagnostic hd
    | cases hd
    | (have hn : (none : Option (ReferenceActivePhysicalStep.UpDiagnostic p rate)) =
          some diagnostic := (livePostChoice_up_none prepared _ _ _ _).symm.trans hd
       cases hn)

private theorem record_up_expected_provenance
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hd : record.output.coordinator.up = some diagnostic) :
    diagnostic.expected = ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) := by
  rw [record.output_eq] at hd
  exact observeCoordinator_up_expected_provenance _ diagnostic hd

private theorem interval_eq_original_window_prefix
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k n : ℕ) (hk : k + 1 < count)
    (hn : n ≤
      (((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records.drop
          (k + 2)).takeWhile
        fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input).length) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 2 + n)
      (fixed_window_span initial rows selected rewards start count span active k n hk hn) active).records.drop
        (k + 2) =
      ((((ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records.drop
        (k + 2)).takeWhile fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input).take n) := by
  let E := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active
  let W := (E.records.drop (k + 2)).takeWhile
    fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input
  change n ≤ W.length at hn
  have hcount := fixed_window_count_bound initial rows selected rewards start count span active k n hk hn
  have hprefix := run_prefix_records initial rows selected rewards start count span active
    (k + 2 + n) hcount
  have hshortLength := ReferenceActivePhysicalHorizon.run_record_count initial rows selected
    rewards start (k + 2 + n) (fixed_window_span initial rows selected rewards start count span active k n hk hn) active
  have htakeLength : (W.take n).length = n := by
    simp [List.length_take, Nat.min_eq_left hn]
  have hdropLength : (E.records.drop (k + 2)).length ≥ n := by
    have hWPrefix : W <+: E.records.drop (k + 2) := List.takeWhile_prefix _
    exact le_trans hn hWPrefix.length_le
  have hWtake : W.take n = (E.records.drop (k + 2)).take n := by
    have hprefix : W.take n <+: (E.records.drop (k + 2)).take n :=
      (List.takeWhile_prefix _).take n
    rw [List.prefix_iff_eq_take.mp hprefix]
    simp [List.length_take, Nat.min_eq_left hn, List.take_take]
  have hintervalPrefix :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 2 + n)
        (fixed_window_span initial rows selected rewards start count span active k n hk hn) active).records.drop
          (k + 2) <+: E.records.drop (k + 2) := by
    rw [← hprefix]
    exact (List.take_prefix (k + 2 + n) E.records).drop (k + 2)
  have hintervalLength :
      ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 2 + n)
        (fixed_window_span initial rows selected rewards start count span active k n hk hn) active).records.drop
          (k + 2)).length = n := by
    rw [List.length_drop, hshortLength]
    omega
  have hintervalEq :
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 2 + n)
        (fixed_window_span initial rows selected rewards start count span active k n hk hn) active).records.drop
          (k + 2) = (E.records.drop (k + 2)).take n := by
    rw [List.prefix_iff_eq_take.mp hintervalPrefix, hintervalLength]
  calc
    _ = (E.records.drop (k + 2)).take n := hintervalEq
    _ = W.take n := hWtake.symm

/-- The actual second UP-completed batch has the one cutoff-fixed sent word.
The affine equations are conclusions on the computed ordinary focal branch;
the decoder's raw output is retained in the output on both branches. The
ordinary branch also supplies the matching expected word, and a local
unique-solution implication identifies the raw result when uniqueness is
actually available. Sources: `05_binary_transport.tex:36-53,70-88,105-124`,
`06_interruptions.tex:41-70,164-177,277-284,327-348`, and
`appendix_a_local_protocol.tex:92-109,151-157`. -/
theorem run_cutoff_up_second_window_truth
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k + 1 < count)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (hp : ReferenceAssignmentPayloadPersistence.storedPayload
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).input.state.coordinator =
        some payload)
    (hc : ReferenceCollectionPhaseHistory.cutoffChosen
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).input = true)
    (hd : ReferenceAcceptedUpFollowerHistory.RetainedDown
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; omega))
      i (payload.downRecord i))
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hf : ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).output.next.followers i =
        .ordinary next nextMemory)
    (ho : ((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records[k + 1]'(by
        rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hk)).output.next.coordinator ≠ .dagger)
    (n : ℕ)
    (hn : n ≤ (((ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records.drop
      (k + 2)).takeWhile fun r =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input).length)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (hcoord : (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2 + n)
      (fixed_window_span initial rows J rewards start count span active k n hk hn) active).finalState.coordinator ≠
        .dagger)
    (hpositiveCount :
      let preRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 2)
        (by omega) active
      let completedRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start
        (k + 2 + n) (fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let interval := completedRun.records.drop (k + 2)
      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
      let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start
        (k + 2) (k + 2 + n)
        (fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let channel := preRun.finalState.upDecoderBank i
      (AffineBatchDecoder.positives p trace rounds).length =
        AffineBatchDecoder.quota p - channel.pending.length + AffineBatchDecoder.quota p) :
    ∃ (M : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta)),
      ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
        (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
        (index : Fin (ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start
          (k + 2) (k + 2 + n)
          (fixed_window_span initial rows J rewards start count span active k n hk hn) active).length)
        (record : Record p rate)
        (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
      let b := k + 2
      let preRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active
      let completedRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
        (fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let interval := completedRun.records.drop b
      let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
      let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start b
        (b + n) (fixed_window_span initial rows J rewards start count span active k n hk hn) active
      let positive := AffineBatchDecoder.positives p trace rounds
      let channel := preRun.finalState.upDecoderBank i
      let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
      M.val = ActiveFollowerQueueOperation.upOfferFields next ∧
      0 < M.val.sigma ∧
      first = channel.pending ++ positive.take (AffineBatchDecoder.quota p - channel.pending.length) ∧
      first.length = AffineBatchDecoder.quota p ∧
      window.length = AffineBatchDecoder.quota p ∧
      window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
      last ∈ window ∧
      AffineBatchDecoder.decisionTime window = some last.time ∧
      rounds.get index = last.time ∧
      record ∈ interval ∧
      record.input.time = last.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
      ((ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
        (fixed_window_span initial rows J rewards start count span active k n hk hn) active).finalState.followers i =
          .dagger ∨
      ∃ (finalFollower : ReferencePrelaunchFollower.State p rate.eta)
        (finalMemory : ActiveFollowerLifecycle.LocalMemory p),
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + n)
          (fixed_window_span initial rows J rewards start count span active k n hk hn) active).finalState.followers i =
            .ordinary finalFollower finalMemory ∧
        (∀ entry, entry ∈ window →
          AffineBatchDecoder.equation entry.sample
            (ActiveFollowerArmChoice.offeredUpWord rate.eta M)) ∧
        ((∃! v, AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) v) →
          diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
            diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M))) := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  let b := k + 2
  let W := (E.records.drop b).takeWhile fun r =>
    !ReferenceCollectionPhaseHistory.laterChosen r.input
  change n ≤ W.length at hn
  change n ≤ W.length at hn
  let endpoint := b + n
  have hendSpan : start + endpoint ≤ p.T := by
    dsimp [endpoint, b]
    exact fixed_window_span initial rows J rewards start count span active k n hk hn
  let preRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start b (by omega) active
  let completedRun := ReferenceActivePhysicalHorizon.run initial rows J rewards start endpoint hendSpan active
  let interval := completedRun.records.drop b
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
  let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds initial rows J rewards start b endpoint
    hendSpan active
  let positive := AffineBatchDecoder.positives p trace rounds
  let channel := preRun.finalState.upDecoderBank i
  let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
  have hcountBound := fixed_window_count_bound initial rows J rewards start count span active
    k n hk hn
  have hrunPrefix := run_prefix_records initial rows J rewards start count span active endpoint hcountBound
  have horiginalLength := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
    start count span active
  have hcompletedLength := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards
    start endpoint hendSpan active
  obtain ⟨M, hMval, hMsigma, hquery⟩ :=
    ReferenceCutoffUpReplyInterval.collection_interval_fixed_up_query
      initial rows J rewards start count span active k hk payload i hp hc hd next nextMemory hf ho
  have hcut := ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
    initial rows J rewards start b endpoint (by omega) hendSpan active hinitial hcoord i hseed
    hpositiveCount
  obtain ⟨first, last, index, record, diagnostic, hcutFacts⟩ := hcut
  rcases hcutFacts with ⟨hfirst, hfirstLen, hwindowLen, hwindowPairwise, hlast,
    hdecision, hindexRound, hrecordMem, hrecordTime, hdiagnostic, hselected,
    _, _, hsample, hledgerFacts, hconnectedCut, hbankReplay, hdiagnosticBank,
    hbefore, hbeforePending, htransitionPending, htransitionCompleted,
    hdecoderAfter, hrawTransition, hrawBatch, htransitionPair, hrunReplay,
    hfinalBank⟩
  have hprefixInterval := interval_eq_original_window_prefix initial rows J rewards start count
    span active k n hk hn
  have hintervalLength : interval.length = n := by
    dsimp only [interval]
    rw [List.length_drop, hcompletedLength]
    dsimp [endpoint, b]
    omega
  have hintervalChronological : interval.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    have hroundsChronological :=
      ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
        initial rows J rewards start b endpoint (by omega) hendSpan active hinitial hcoord
    have hroundValues : (rounds.map Fin.val).Pairwise LT.lt :=
      List.pairwise_map.mpr hroundsChronological
    have htimeValues : (interval.map (fun current => current.input.time.val)).Pairwise LT.lt := by
      simpa [rounds, ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, interval, completedRun,
        endpoint, b, List.map_map, Function.comp_def] using hroundValues
    exact List.pairwise_map.mp htimeValues
  have hintervalCut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut
    initial rows J rewards start b endpoint (by omega) hendSpan active hinitial hcoord
  rcases hintervalCut with ⟨_, _, hconnected, _, _, _, _⟩
  have hentryDetails (finalFollower : ReferencePrelaunchFollower.State p rate.eta)
      (finalMemory : ActiveFollowerLifecycle.LocalMemory p)
      (hfinalFollower : completedRun.finalState.followers i =
        .ordinary finalFollower finalMemory) : ∀ entry, entry ∈ window →
      ∃ source, source ∈ interval ∧ source.input.time = entry.time ∧
        AffineBatchDecoder.equation entry.sample
          (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare source.input) =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
    intro entry hentryWindow
    have hentryPositive : entry ∈ positive := List.mem_of_mem_drop hentryWindow
    obtain ⟨htime, hentryEligible, hentrySample⟩ :=
      (AffineBatchDecoder.mem_positives_iff p trace rounds entry).mp hentryPositive
    obtain ⟨source, hsourceMem, hsourceTime⟩ := List.mem_map.mp htime
    obtain ⟨j, hj, hsourceGet⟩ := List.mem_iff_getElem.mp hsourceMem
    have hjn : j < n := by rw [← hintervalLength]; exact hj
    have htakeWindowLength : (W.take n).length = n := by
      simp [List.length_take, Nat.min_eq_left hn]
    have hjTake : j < (W.take n).length := by
      rw [htakeWindowLength]
      exact hjn
    have hjBound : j ≤ W.length := by omega
    have hwindowSource : (W.take n)[j]'hjTake = source := by
      have hgetPrefix : interval[j]'hj = (W.take n)[j]'hjTake :=
        List.getElem_of_eq hprefixInterval hj
      exact hgetPrefix.symm.trans hsourceGet
    have htraceSource : trace source.input.time =
        ReferenceCoordinatorUpIntervalWindow.recordFocalInput source i :=
      ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
        interval i hintervalChronological source hsourceMem
    have hsourceEligible : AffineBatchDecoder.eligible
        (ReferenceCoordinatorUpIntervalWindow.recordFocalInput source i) := by
      rw [← htraceSource, hsourceTime]
      exact hentryEligible
    obtain ⟨sourceDiagnostic, hsourceDiagnostic, hsourceSelected⟩ :
        ∃ d, source.output.coordinator.up = some d ∧ d.input.selectedFollower = i := by
      cases hcall : source.output.coordinator.up with
      | none =>
          simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall,
            ReferenceCoordinatorUpIntervalWindow.administrativeNoCallInput,
            AffineBatchDecoder.eligible] at hsourceEligible
      | some d =>
          by_cases hselectedSource : d.input.selectedFollower = i
          · exact ⟨d, rfl, hselectedSource⟩
          · have hfalse : ¬ AffineBatchDecoder.eligible
                (ReferenceCoordinatorUpIntervalWindow.recordFocalInput source i) := by
              simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall,
                ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
                hselectedSource, AffineBatchDecoder.eligible]
            exact False.elim (hfalse hsourceEligible)
    have hsourceTraceInput : trace source.input.time =
        CoordinatorUpReception.roundInput sourceDiagnostic.input := by
      rw [htraceSource]
      simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput,
        hsourceDiagnostic, hsourceSelected,
        ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput]
    have hsourceRoundEligible : AffineBatchDecoder.eligible
        (CoordinatorUpReception.roundInput sourceDiagnostic.input) := by
      rw [← hsourceTraceInput]
      rw [hsourceTime]
      exact hentryEligible
    obtain ⟨sourceLedger, _, _, _, _, _, hselectedIndex, hsourceSample, hslot,
      _, hselectedFlag, hroundSample, _, _⟩ :=
      ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
        source sourceDiagnostic hsourceDiagnostic
    have hselector : sourceLedger.cutoff ≤ source.input.time.val + 1 ∧
        sourceDiagnostic.input.slot = PublicDiscreteDraws.upSlot ∧
        sourceDiagnostic.input.selectedFollower ∈ sourceLedger.pending := by
      have hselectedTrue := hsourceRoundEligible.1
      rw [hselectedFlag] at hselectedTrue
      exact of_decide_eq_true hselectedTrue
    have hslotDraw : PublicDiscreteDraws.slotDraw
        (source.input.row.2 source.input.time).1 = PublicDiscreteDraws.upSlot :=
      hslot.symm.trans hselector.2.1
    have hsenderDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (source.input.row.2 source.input.time).1 = i := by
      rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
      exact hselectedIndex.symm.trans hsourceSelected
    obtain ⟨queryState, queryMemory, hsourceOutput⟩ :=
      ReferenceFollowerReplyChronology.connected_output_chronology
        hconnected i finalFollower finalMemory hfinalFollower j hj
    have hsourceOutput' : source.output.next.followers i = .ordinary queryState queryMemory := by
      rw [← hsourceGet]
      simpa [ReferenceCoordinatorUpIntervalWindow.intervalRecords, interval, completedRun,
        endpoint, b] using hsourceOutput.1
    obtain ⟨choice, choiceMemory, hchoice, _, _, _⟩ :=
      ReferenceFollowerReplyChronology.record_choice_chronology
        source i queryState queryMemory hsourceOutput'
    have hjEndpoint : b + j < endpoint := by dsimp [endpoint]; omega
    have hjCompleted : b + j < completedRun.records.length := by
      rw [hcompletedLength]
      exact hjEndpoint
    have hrecordIndex : b + j < E.records.length := by
      rw [horiginalLength]
      dsimp [endpoint] at hjEndpoint
      omega
    have hsourceOriginal : source = E.records.get ⟨b + j, hrecordIndex⟩ := by
      have hdropGet : interval[j]'hj = completedRun.records[b + j]'hjCompleted := by
        exact List.getElem_drop
      have htakeGet : completedRun.records[b + j]'hjCompleted = E.records[b + j]'hrecordIndex := by
        have hjPrefix : b + j < (E.records.take endpoint).length := by
          simp only [List.length_take, horiginalLength]
          dsimp [endpoint] at hjEndpoint
          omega
        have htakePrefix : (E.records.take endpoint)[b + j]'hjPrefix =
            completedRun.records[b + j]'hjCompleted :=
          List.getElem_of_eq hrunPrefix hjPrefix
        calc
          completedRun.records[b + j]'hjCompleted = (E.records.take endpoint)[b + j]'hjPrefix :=
            htakePrefix.symm
          _ = E.records[b + j]'hrecordIndex := by simp only [List.getElem_take]
      calc
        source = interval[j]'hj := hsourceGet.symm
        _ = completedRun.records[b + j]'hjCompleted := hdropGet
        _ = E.records[b + j]'hrecordIndex := htakeGet
        _ = E.records.get ⟨b + j, hrecordIndex⟩ := by rfl
    have hchoiceOriginal :
        (ReferenceFollowerFixedReply.actualChoice (E.records.get ⟨b + j, by
          have hidx : b + j < count := by omega
          rw [horiginalLength]
          exact hidx⟩) i).configuration = .ordinary choice choiceMemory := by
      rw [← hsourceOriginal]
      exact hchoice
    have hqueryAt := hquery j hjBound (by omega) hrecordIndex
      choice choiceMemory hchoiceOriginal (by
        rw [← hsourceOriginal]
        exact hslotDraw) (by
        rw [← hsourceOriginal]
        exact hsenderDraw)
    have hpositive : ReferenceActiveAffinePositiveTest.upPositive source.input = true := by
      rw [ReferenceActiveAffinePositiveTest.record_upPositive]
      simpa [ReferenceActiveAffinePositiveTest.upDiagnosticPositive,
        hsourceDiagnostic] using hsourceRoundEligible
    have hpositiveOriginal : ReferenceActiveAffinePositiveTest.upPositive
        ((E.records.get ⟨b + j, hrecordIndex⟩).input) = true := by
      rw [← hsourceOriginal]
      exact hpositive
    have hindex : CoordinatorUpMeasurability.selectedFollowerIndex
        ((source.input.rows source.input.selected).2 source.input.time) = i :=
      hselectedIndex.symm.trans hsourceSelected
    have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
        ((source.input.rows source.input.selected).2 source.input.time) = i := by
      apply Fin.ext
      rw [CoordinatorUpMeasurability.selectedChannelFollower_val,
        ← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
      simpa [ContinuousLearningRows.d] using congrArg Fin.val hindex
    have hlastSample : sourceDiagnostic.input.affineSample =
        ((source.input.rows source.input.selected).2 source.input.time).2 (1, i) := by
      rw [hsourceSample, hchannel]
    have hsampleEq : entry.sample =
        ((source.input.rows source.input.selected).2 source.input.time).2
          (1, i) := by
      rw [hentrySample, ← hsourceTime, htraceSource]
      simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput,
        hsourceDiagnostic, hsourceSelected,
        ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput]
      simp only [if_true]
      rw [hroundSample, hsourceSample, hchannel]
    have hhash : AffineChannelLaw.affineHash entry.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta M) = 1 := by
      have hqueryHash := hqueryAt.2.2.2.2 hpositiveOriginal
      rw [← hsourceOriginal] at hqueryHash
      rw [hsampleEq]
      exact hqueryHash
    have hqueryExpected := hqueryAt.2.2.2.1
    rw [← hsourceOriginal] at hqueryExpected
    exact ⟨source, hsourceMem, hsourceTime,
      (AffineBatchDecoder.equation_iff_affineHash _ _).2 hhash, hqueryExpected⟩
  have hentryEquations (finalFollower : ReferencePrelaunchFollower.State p rate.eta)
      (finalMemory : ActiveFollowerLifecycle.LocalMemory p)
      (hfinalFollower : completedRun.finalState.followers i =
        .ordinary finalFollower finalMemory) : ∀ entry, entry ∈ window →
      AffineBatchDecoder.equation entry.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
    intro entry hentry
    exact (hentryDetails finalFollower finalMemory hfinalFollower entry hentry).choose_spec.2.2.1
  have hfinalFollowerCases :
      (completedRun.finalState.followers i = .dagger) ∨
      ∃ finalFollower finalMemory,
        completedRun.finalState.followers i = .ordinary finalFollower finalMemory := by
    cases hfollower : completedRun.finalState.followers i with
    | dagger => exact Or.inl rfl
    | ordinary state memory => exact Or.inr ⟨state, memory, rfl⟩
  rcases hfinalFollowerCases with hdagger | ⟨finalFollower, finalMemory, hfinalFollower⟩
  · refine ⟨M, first, last, index, record, diagnostic, ?_⟩
    dsimp only [E, b, preRun, completedRun, interval, trace, rounds, positive, channel, window]
    refine ⟨hMval, ?_⟩
    refine ⟨hMsigma, ?_⟩
    refine ⟨hfirst, ?_⟩
    refine ⟨hfirstLen, ?_⟩
    refine ⟨hwindowLen, ?_⟩
    refine ⟨hwindowPairwise, ?_⟩
    refine ⟨hlast, ?_⟩
    refine ⟨hdecision, ?_⟩
    refine ⟨hindexRound, ?_⟩
    refine ⟨hrecordMem, ?_⟩
    refine ⟨hrecordTime, ?_⟩
    refine ⟨hdiagnostic, ?_⟩
    refine ⟨hselected, ?_⟩
    refine ⟨hrawBatch, ?_⟩
    exact Or.inl hdagger
  · have huniqueRaw : (∃! v, AffineBatchDecoder.satisfies
        (AffineBatchDecoder.samples window) v) →
      diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) ∧
        diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
      intro hunique
      have hword := hentryEquations finalFollower finalMemory hfinalFollower
      have hsolves : AffineBatchDecoder.satisfies
          (AffineBatchDecoder.samples window)
          (ActiveFollowerArmChoice.offeredUpWord rate.eta M) :=
        (AffineBatchDecoder.satisfies_samples_iff window _).2 hword
      obtain ⟨v, hv, hvUnique⟩ := hunique
      have hwordEq : v = ActiveFollowerArmChoice.offeredUpWord rate.eta M :=
        (hvUnique _ hsolves).symm
      have huniqueWord : ∀ candidate,
          AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window) candidate →
            candidate = ActiveFollowerArmChoice.offeredUpWord rate.eta M := by
        intro candidate hcandidate
        exact (hvUnique candidate hcandidate).trans hwordEq
      have huniqueEquations : ∀ candidate,
          (∀ entry, entry ∈ window →
            AffineBatchDecoder.equation entry.sample candidate) →
          candidate = ActiveFollowerArmChoice.offeredUpWord rate.eta M := by
        intro candidate hequations
        have hcandidate : AffineBatchDecoder.satisfies
            (AffineBatchDecoder.samples window) candidate :=
          (AffineBatchDecoder.satisfies_samples_iff window candidate).2 hequations
        exact huniqueWord candidate hcandidate
      have hraw := (AffineBatchDecoder.batchOutput_eq_some_iff window
        (ActiveFollowerArmChoice.offeredUpWord rate.eta M)).2
          ⟨hword, huniqueEquations⟩
      obtain ⟨source, hsourceMemLast, hsourceTimeLast, _, hsourceExpected⟩ :=
        hentryDetails finalFollower finalMemory hfinalFollower last hlast
      obtain ⟨jSource, hjSource, hgetSource⟩ := List.mem_iff_getElem.mp hsourceMemLast
      obtain ⟨jRecord, hjRecord, hgetRecord⟩ := List.mem_iff_getElem.mp hrecordMem
      have htimeEqual : source.input.time.val = record.input.time.val := by
        rw [hsourceTimeLast, hrecordTime]
      have hindexEqual : jSource = jRecord := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have hpair := hintervalChronological.rel_getElem_of_lt hjSource hjRecord hlt
          rw [hgetSource, hgetRecord] at hpair
          omega
        · have hpair := hintervalChronological.rel_getElem_of_lt hjRecord hjSource hgt
          rw [hgetSource, hgetRecord] at hpair
          omega
      have hsourceRecord : source = record := by
        subst jRecord
        exact hgetSource.symm.trans hgetRecord
      have hrecordExpected :
          ReferenceActivePhysicalStep.upExpected
            (ReferenceActivePhysicalStep.prepare record.input) =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) := by
        rw [← hsourceRecord]
        exact hsourceExpected
      have hexpectedFromInput :=
        record_up_expected_provenance record diagnostic hdiagnostic
      have hexpected : diagnostic.expected =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta M) :=
        hexpectedFromInput.trans hrecordExpected
      exact ⟨hrawBatch.trans hraw, hexpected⟩
    refine ⟨M, first, last, index, record, diagnostic, ?_⟩
    dsimp only [E, b, preRun, completedRun, interval, trace, rounds, positive, channel, window]
    refine ⟨hMval, ?_⟩
    refine ⟨hMsigma, ?_⟩
    refine ⟨hfirst, ?_⟩
    refine ⟨hfirstLen, ?_⟩
    refine ⟨hwindowLen, ?_⟩
    refine ⟨hwindowPairwise, ?_⟩
    refine ⟨hlast, ?_⟩
    refine ⟨hdecision, ?_⟩
    refine ⟨hindexRound, ?_⟩
    refine ⟨hrecordMem, ?_⟩
    refine ⟨hrecordTime, ?_⟩
    refine ⟨hdiagnostic, ?_⟩
    refine ⟨hselected, ?_⟩
    refine ⟨hrawBatch, ?_⟩
    refine Or.inr ?_
    refine ⟨finalFollower, finalMemory, hfinalFollower, ?_⟩
    exact ⟨hentryEquations finalFollower finalMemory hfinalFollower, huniqueRaw⟩

end ReferenceFixedUpCompletedWindowTruth

end Bandits.Support
