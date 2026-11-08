/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedAssignedArrivalPrefix
public import Bandits.Support.ReferenceFirstCollectionCorrectedNumericalOverflowSum

import Mathlib.Tactic

/-!
# Observation-attributed assigned queues on the first corrected slice

The assigned queue below is the calendar queue reconstructed from the actual
observation-attributed word. It remains an analytical queue before DOWN is
decoded; this definition does not claim that an unoccupied follower stores it.
The word includes every LIVE date and, when the first cutoff is actually
present, its actual collection update.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:40-100,192-233,246-299,355-426`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart birthIndex liveTail cutoffDelta endDate
    prefixInputs overflowEvent)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Input" => RecordedQueueRun.RoundInput p.K

/-- The literal assigned-arm overflow event on the first corrected LIVE
slice. A word is present only when every attributed observation slot is
present. Its queue starts from the actual installation queue. At the actual
first cutoff, the physical collection record is appended to that complete
LIVE word before the backlog is tested. -/
def assignedAttributedOverflowEvent (u t : Fin p.T) : Set X :=
  {z | z ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ (birth : Record) (P : ReferenceActivePhysicalStep.Payload rate),
      (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z]? =
        some birth ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P ∧
      P.sigma = t ∧
      ((∃ (i : Fin (p.m - 1)) (v : ℕ) (word : List (Bool × ℕ)),
          1 ≤ v ∧ v ≤ 1 + (liveTail rate rewards C_star C_h z).length ∧
          (((sourceRecords rate rewards C_star C_h z).drop
            (birthIndex rate rewards C_star C_h z)).take v).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
            some word ∧
          ((QueueReplay.replay (4 * rate.n)
            (0, P.queues (P.assignment.assigned i)) word).2 : ℝ) /
            (rate.n : ℝ) > 1 / (32 * rate.eta.val)) ∨
        (∃ (i : Fin (p.m - 1)) (liveWord : List (Bool × ℕ))
            (seg : ReferenceCollectionSegmentExtraction.Segment rate)
            (cut : Record),
          cutoffDelta rate rewards C_star C_h z = 1 ∧
          (sourceRecords rate rewards C_star C_h z)[birthIndex rate rewards C_star C_h z + 1 +
            (liveTail rate rewards C_star C_h z).length]? = some cut ∧
          ReferenceCollectionSegmentExtraction.segmentAt
            (sourceRecords rate rewards C_star C_h z)
            (birthIndex rate rewards C_star C_h z + 1 +
              (liveTail rate rewards C_star C_h z).length) = some seg ∧
          seg.entry = cut ∧ seg.context.payload = P ∧
          (((sourceRecords rate rewards C_star C_h z).drop
            (birthIndex rate rewards C_star C_h z)).take
              (1 + (liveTail rate rewards C_star C_h z).length)).mapM
                (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P i) =
              some liveWord ∧
          ((QueueReplay.replay (4 * rate.n)
            (0, P.queues (P.assignment.assigned i))
            (liveWord ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
              seg.context.preLedger (P.assignment.assigned i) cut])).2 : ℝ) /
            (rate.n : ℝ) > 1 / (32 * rate.eta.val)))}

private theorem replay_add_score (capacity score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (score, backlog) records =
      (score + (QueueReplay.replay capacity (0, backlog) records).1,
        (QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (0, backlog) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [CollectionKnownQueueContinuation.queueReplay_transition_add_score]
      rw [ih (score + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2]
      rw [ih (QueueReplay.transition capacity (0, backlog) record).1
        (QueueReplay.transition capacity (0, backlog) record).2]
      simp only [Nat.add_assoc]

private theorem raw_replay_eq (q : RecordedQueueRun.Parameters)
    (seed : ℕ × ℕ) (cells : List Input) (a : Fin p.K) :
    QueueReplay.replay (4 * q.n) seed
        (cells.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival q c a)) =
      QueueReplay.replay (4 * q.n) seed
        (cells.map fun c => UnstoppedRecordedQueueComparison.unstoppedRecord q c a) := by
  induction cells generalizing seed with
  | nil => rfl
  | cons c cells ih =>
      simp only [List.map_cons, QueueReplay.replay, List.foldl_cons]
      change QueueReplay.replay _ _ _ = QueueReplay.replay _ _ _
      rw [ih]
      congr 1
      cases he : c.enabled <;>
        simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he,
          Bool.false_eq_true, ite_false, ite_true, QueueReplay.transition]

private theorem initialized_replay (A B : List Input) (a : Fin p.K) :
    QueueReplay.replay (4 * rate.n)
        (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a)
        (B.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c a)) =
      UnstoppedRecordedQueueComparison.unstoppedReplay Q
        (A ++ B) (A ++ B).length a := by
  simp only [UnstoppedRecordedQueueComparison.unstoppedReplay,
    List.take_length, List.map_append, QueueReplay.replay_append]
  exact raw_replay_eq Q _ B a

/-- Appending physical-attributed arrivals to the actual installation queue
has the same backlog as the corresponding complete original calendar prefix.
The comparison preserves disabled dates and enabled zero-arrival service. -/
private theorem initialized_queue_replay (A B : List Input) (a : Fin p.K) :
    (QueueReplay.replay (4 * rate.n)
      (0, (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)
      (B.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c a))).2 =
    (UnstoppedRecordedQueueComparison.unstoppedReplay Q
      (A ++ B) (A ++ B).length a).2 := by
  have hshift := replay_add_score (4 * rate.n)
    (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).1
    (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2
    (B.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c a))
  have hfull := initialized_replay (rate := rate) A B a
  calc
    _ = (QueueReplay.replay (4 * rate.n)
        (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a)
        (B.map fun c => (c.enabled, RecordedQueueRun.quantizedArrival Q c a))).2 :=
          (congrArg Prod.snd hshift).symm
    _ = (UnstoppedRecordedQueueComparison.unstoppedReplay Q
        (A ++ B) (A ++ B).length a).2 := congrArg Prod.snd hfull

private theorem continuing_windows_eq (z : X) :
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z
        (birthIndex rate rewards C_star C_h z + 1) =
      liveTail rate rewards C_star C_h z := by
  simp only [ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords]
  have htest :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
          (p := p) (rate := rate) =
        ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen := by
    funext r
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
      ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
    cases r.output.preparation.coordinator with
    | live rv qv base chosen => cases chosen <;> rfl
    | first _ | collection _ _ _ _ _ | invalidCollectionCutoff | dagger => rfl
  rw [htest]

private theorem event_of_present_prefix_crossing
    (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (n0 : ℕ) (hn0 : t.val + 1 ≤ n0)
    (hne : n0 ≤ endDate rate rewards C_star C_h t z)
    (inputs : List Input)
    (hinputs : prefixInputs rate rewards C_star C_h n0 z = some inputs)
    (hlen : inputs.length = n0 - sourceStart rate rewards C_star C_h z)
    (hfull : UnstoppedRecordedQueueComparison.replay_crosses_overflow
      Q inputs inputs.length) :
    ∃ a : Fin p.K, z ∈ overflowEvent rate rewards C_star C_h u t a := by
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let h := UnstoppedRecordedQueueComparison.firstOverflowPrefix Q inputs
  have htime : s + b = t.val :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz
  have hlenpos : 0 < inputs.length := by rw [hlen]; omega
  have hex : ∃ n, 1 ≤ n ∧ n ≤ inputs.length ∧
      UnstoppedRecordedQueueComparison.replay_crosses_overflow Q inputs n :=
    ⟨inputs.length, by omega, le_rfl, hfull⟩
  have hfirstle : h ≤ inputs.length := by
    dsimp [h, UnstoppedRecordedQueueComparison.firstOverflowPrefix]
    rw [dite_eq_left hex]
    exact Nat.find_min' hex ⟨by omega, le_rfl, hfull⟩
  have hfirstpos : 0 < h :=
    UnstoppedRecordedQueueComparison.first_overflow_prefix_pos Q inputs
  obtain ⟨a₀, hcross₀⟩ :=
    UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first Q inputs hfirstle
  have hlen' : inputs.length = n0 - s := by simpa [s] using hlen
  have hmle : s + h ≤ n0 := by omega
  by_cases hearly : h ≤ b
  · let m := t.val + 1
    have hmstart : t.val + 1 ≤ m := le_rfl
    have hmend : m ≤ n0 := by change t.val + 1 ≤ n0; exact hn0
    obtain ⟨inputsM, hM, hMlen, hMread⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne)
    obtain ⟨suffix, hjoin, _hsuffix⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_append
        rate rewards C_star C_h u t z hz m n0 hmstart hmend hne inputsM inputs
        hM hinputs
    have htake : inputsM = inputs.take inputsM.length := by
      rw [hjoin]
      simp
    have hMlen' : inputsM.length = m - s := by simpa [s] using hMlen
    have hlenM : inputsM.length = b + 1 := by
      rw [hMlen']
      dsimp [m]
      omega
    have htake' : inputsM = inputs.take (b + 1) := by rw [htake, hlenM]
    have hrun := (UnstoppedRecordedQueueComparison.prefix_state_comparison
      Q inputs (b + 1) (by rw [hlen']; omega)).1 a₀
    have hmin : min (b + 1) h = h := Nat.min_eq_right (by omega)
    rw [← htake', hmin] at hrun
    let on := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q inputsM)
    have hon : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h m z = some on := by
      simpa only [on] using hMread
    have hcrossM : ((on.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      have hq : (on.1 a₀).2 =
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs h a₀).2 := by
        change ((RecordedQueueRun.run Q inputsM).registers a₀).2 = _
        exact congrArg Prod.snd hrun
      have hcut : 32 * (on.1 a₀).2 >
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D := by
        rw [hq]
        exact hcross₀
      have hnorm := (RecordedQueueRun.overflowCutoff_iff Q (on.1 a₀).2).mpr hcut
      change _ > 1 / (32 * rate.eta.val) at hnorm
      exact hnorm
    have hflag :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefix_threshold_overflow
        rate rewards C_star C_h m z a₀ on hon hcrossM
    obtain ⟨oe, hoe, heq, _hflag, _hrecords⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_overflow_endpoint
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne) on hon hflag
    have hcrossE : ((oe.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      rw [heq]
      exact hcrossM
    refine ⟨a₀, ?_⟩
    exact (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent_iff_endpoint
      rate rewards C_star C_h u t a₀ z).mpr ⟨hz, oe, hoe, hcrossE⟩
  · let m := s + h
    have hmstart : t.val + 1 ≤ m := by dsimp [m]; rw [← htime]; omega
    have hmend : m ≤ n0 := hmle
    obtain ⟨inputsM, hM, hMlen, hMread⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne)
    obtain ⟨suffix, hjoin, _hsuffix⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_append
        rate rewards C_star C_h u t z hz m n0 hmstart hmend hne inputsM inputs
        hM hinputs
    have htake : inputsM = inputs.take inputsM.length := by
      rw [hjoin]
      simp
    have hMlen' : inputsM.length = m - s := by simpa [s] using hMlen
    have hlenM : inputsM.length = h := by
      rw [hMlen']
      dsimp [m]
      omega
    have htake' : inputsM = inputs.take h := by rw [htake, hlenM]
    have hrun := (UnstoppedRecordedQueueComparison.prefix_state_comparison
      Q inputs h (by rw [hlen']; omega)).1 a₀
    rw [← htake', min_self h] at hrun
    let on := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q inputsM)
    have hon : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h m z = some on := by
      simpa only [on] using hMread
    have hcrossM : ((on.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      have hq : (on.1 a₀).2 =
          (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs h a₀).2 := by
        change ((RecordedQueueRun.run Q inputsM).registers a₀).2 = _
        exact congrArg Prod.snd hrun
      have hcut : 32 * (on.1 a₀).2 >
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D := by
        rw [hq]
        exact hcross₀
      have hnorm := (RecordedQueueRun.overflowCutoff_iff Q (on.1 a₀).2).mpr hcut
      change _ > 1 / (32 * rate.eta.val) at hnorm
      exact hnorm
    have hflag :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefix_threshold_overflow
        rate rewards C_star C_h m z a₀ on hon hcrossM
    obtain ⟨oe, hoe, heq, _hflag, _hrecords⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_overflow_endpoint
        rate rewards C_star C_h u t z hz m hmstart (hmend.trans hne) on hon hflag
    have hcrossE : ((oe.1 a₀).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * rate.eta.val) := by
      rw [heq]
      exact hcrossM
    refine ⟨a₀, ?_⟩
    exact (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent_iff_endpoint
      rate rewards C_star C_h u t a₀ z).mpr ⟨hz, oe, hoe, hcrossE⟩

private theorem numerical_union_of_prefix_queue
    (u t : Fin p.T) (z : X) (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (n : ℕ) (hn : t.val + 1 ≤ n)
    (hend : n ≤ endDate rate rewards C_star C_h t z)
    (inputs : List Input)
    (hinputs : prefixInputs rate rewards C_star C_h n z = some inputs)
    (hlen : inputs.length = n - sourceStart rate rewards C_star C_h z)
    (a : Fin p.K) (backlog : ℕ)
    (hqueue : backlog =
      (UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs inputs.length a).2)
    (hcross : (backlog : ℝ) / (rate.n : ℝ) > 1 / (32 * rate.eta.val)) :
    ∃ a₀ : Fin p.K, z ∈ overflowEvent rate rewards C_star C_h u t a₀ := by
  have hnorm :
      ((UnstoppedRecordedQueueComparison.unstoppedReplay Q inputs inputs.length a).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
          1 / (32 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta) := by
    change _ > 1 / (32 * rate.eta.val)
    rw [← hqueue]
    exact hcross
  have hfull := (UnstoppedRecordedQueueComparison.replay_crosses_overflow_iff_normalized
    Q inputs inputs.length).2 ⟨a, hnorm⟩
  exact event_of_present_prefix_crossing rate rewards C_star C_h u t z hz n hn hend
    inputs hinputs hlen hfull

private theorem firstCell_birth_time_eq (u t : Fin p.T) (z : X)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    sourceStart rate rewards C_star C_h z + birthIndex rate rewards C_star C_h z = t.val :=
  ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hz

private theorem overflowEvent_mem_allArmOverflowEvent (u t : Fin p.T)
    (a : Fin p.K) :
    overflowEvent rate rewards C_star C_h u t a ⊆
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
        rate rewards C_star C_h := by
  intro z hz
  refine Set.mem_iUnion.mpr ⟨a, ?_⟩
  refine Set.mem_iUnion.mpr ⟨u, ?_⟩
  exact Set.mem_iUnion.mpr ⟨t, hz⟩

private theorem take_append_suffix {α : Type*} (A B : List α) (b v : ℕ)
    (hA : A.length = b + 1) (hv : 1 ≤ v) :
    (A ++ B).take (b + v) = A ++ B.take (v - 1) := by
  rw [List.take_append]
  have hAle : A.length ≤ b + v := by rw [hA]; omega
  rw [List.take_of_length_le hAle]
  have hsub : b + v - A.length = v - 1 := by omega
  rw [hsub]

/-- Every overflow of the assigned-arm observation-attributed calendar queue
on the first corrected LIVE slice, including the actual first cutoff update,
is covered by the existing original-source numerical union. -/
theorem assignedAttributedOverflowEvent_subset_allArmOverflowEvent
    (u t : Fin p.T) :
    assignedAttributedOverflowEvent rate rewards C_star C_h u t ⊆
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
        rate rewards C_star C_h := by
  classical
  intro z hzEvent
  change z ∈ correctedCell rate rewards C_star C_h u t ∧ _ at hzEvent
  obtain ⟨hz, birth, P, hbirthEvent, hbornEvent, _hsigmaEvent, hcase⟩ := hzEvent
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  have htime : s + b = t.val :=
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
      rate rewards C_star C_h u t z hz
  obtain ⟨L, c, birth0, P0, base, hL, hc, hprefixBirth, hlenL,
    hbirthRoot, _hactual, _hbirthTime, _hbirthRows, _hbirthSelected,
    _hbirthRewards, _hrecordRows, _hlaterChosen, hcEnabled, hbornRoot, _hsigmaRoot,
    _hcRate, _hcReward, hqueues, _hbase, hterminal, hbirthWord, hafter⟩ :=
      ReferenceFirstCorrectedAssignedArrivalPrefix.firstCell_total_assigned_arrival_prefix
        rate rewards C_star C_h u t z hz
  have hbirthEvent' : R[b]? = some birth := by
    simpa only [R, b] using hbirthEvent
  have hbirthRoot' : R[b]? = some birth0 := by
    simpa only [R, b,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hbirthRoot
  have hbirthEq : birth = birth0 := Option.some.inj (hbirthEvent'.symm.trans hbirthRoot')
  subst birth
  have hpayloadEq : P = P0 :=
    ReferenceAssignmentPayloadChronology.installationBirth_payload_unique
      birth0 P P0 hbornEvent hbornRoot
  subst P
  rcases hcase with hLive | hCut
  · by_cases hterminal' : t.val + 1 = p.T
    · have hRlen : b + 1 = R.length := by
        simpa only [R, b, sourceRecords,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using
          hterminal hterminal'
      have hdropNil : R.drop (b + 1) = [] :=
        List.drop_eq_nil_iff.mpr (by omega)
      have hWnil : liveTail rate rewards C_star C_h z = [] := by
        change (R.drop (b + 1)).takeWhile _ = []
        rw [hdropNil]
        rfl
      rcases hLive with ⟨i, v, word, hvpos, hvle, hword, hcross⟩
      have hvle' : v ≤ 1 := by simpa [hWnil] using hvle
      have hv : v = 1 := by omega
      have hdropLen : (R.drop b).length = 1 := by
        simp only [List.length_drop]
        omega
      have hhead : (R.drop b)[0]? = some birth0 := by
        simpa only [List.getElem?_drop, Nat.add_zero] using hbirthRoot'
      have hdropBirth : R.drop b = [birth0] := by
        cases hdrop : R.drop b with
        | nil => simp [hdrop] at hdropLen
        | cons x xs =>
            have hx : x = birth0 := by
              have hh : some x = some birth0 := by simpa [hdrop] using hhead
              exact Option.some.inj hh
            cases xs with
            | nil => subst x; simp
            | cons y ys => simp [hdrop] at hdropLen
      have hrootWord := hbirthWord hterminal' i
      have hwordValue : word =
          [(true, RecordedQueueRun.quantizedArrival Q c
            (P0.assignment.assigned i))] := by
        apply Option.some.inj
        calc
          some word = ((R.drop b).take v).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i) :=
                hword.symm
          _ = [birth0].mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i) := by
                simp [hv, hdropBirth]
          _ = some [(true, RecordedQueueRun.quantizedArrival Q c
              (P0.assignment.assigned i))] := hrootWord
      let a := P0.assignment.assigned i
      have hqueue :
          (QueueReplay.replay (4 * rate.n) (0, P0.queues a) word).2 =
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q
              (L ++ [c]) (L ++ [c]).length a).2 := by
        rw [hwordValue, hqueues a]
        simpa [hcEnabled] using initialized_queue_replay (rate := rate) L [c] a
      have hlen : (L ++ [c]).length = (t.val + 1) - s := by
        simp only [List.length_append, List.length_singleton, hlenL]
        omega
      have hend :=
        (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
          rate rewards C_star C_h u t z hz).1
      obtain ⟨det, hdet⟩ := numerical_union_of_prefix_queue rate rewards C_star C_h
        u t z hz (t.val + 1) le_rfl hend (L ++ [c]) hprefixBirth hlen a
        (QueueReplay.replay (4 * rate.n) (0, P0.queues a) word).2 hqueue hcross
      exact overflowEvent_mem_allArmOverflowEvent rate rewards C_star C_h u t det hdet
    · have hsucc : t.val + 1 < p.T := by omega
      obtain ⟨rout, qout, beta, hbirthNext, hk, hstate, hlater, hB, hallv,
        hEbound, hprefixEnd, hdrop, _hrowsW, rE, qE, _hpayloadE, _hstatesE,
        hboundary⟩ := hafter hsucc
      let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b + 1)
      let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
        rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
      let e := b + 1 + W.length
      have hW_eq : W = liveTail rate rewards C_star C_h z := by
        change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (birthIndex rate rewards C_star C_h z + 1) =
            liveTail rate rewards C_star C_h z
        exact continuing_windows_eq rate rewards C_star C_h z
      have hBlen : B.length = W.length := hB
      have htimeEnd : s + e = t.val + 1 + W.length := by
        dsimp [e]
        rw [← htime]
        omega
      have hEndBound : s + e ≤ endDate rate rewards C_star C_h t z := by
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate
        rw [← htime, ← hW_eq]
        dsimp [e]
        omega
      rcases hLive with ⟨i, v, word, hvpos, hvle, hword, hcross⟩
      have hvroot : v ≤ 1 + W.length := by rw [hW_eq]; exact hvle
      have hall := hallv i v hvpos hvroot
      have hprefixRecords :
          (R.drop b).take v = (birth0 :: W).take v := by
        have hvTake : v ≤ 1 + W.length := hvroot
        calc
          (R.drop b).take v = ((R.drop b).take (1 + W.length)).take v := by
            rw [List.take_take]
            simp [Nat.min_eq_left hvTake]
          _ = (birth0 :: W).take v := congrArg (List.take v) hdrop
      have hwordValue : word =
          (([c] ++ B.take (v - 1)).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival Q cell
              (P0.assignment.assigned i))) := by
        have hwordRoot : ((R.drop b).take v).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i) =
            some (([c] ++ B.take (v - 1)).map fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival Q cell
                (P0.assignment.assigned i))) := by
          rw [hprefixRecords]
          exact hall
        exact Option.some.inj (hword.symm.trans hwordRoot)
      let a := P0.assignment.assigned i
      have hqueueLive :
          (QueueReplay.replay (4 * rate.n) (0, P0.queues a) word).2 =
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q
              ((L ++ [c]) ++ B.take (v - 1))
              ((L ++ [c]) ++ B.take (v - 1)).length a).2 := by
        rw [hwordValue, hqueues a]
        simpa [hcEnabled, List.append_assoc] using
          initialized_queue_replay (rate := rate) L ([c] ++ B.take (v - 1)) a
      let m := t.val + v
      have hmstart : t.val + 1 ≤ m := by dsimp [m]; omega
      have hmend : m ≤ s + e := by
        dsimp [m]
        rw [htimeEnd]
        omega
      obtain ⟨inputsM, hM, hMlen, hMread⟩ :=
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
          rate rewards C_star C_h u t z hz m hmstart (hmend.trans hEndBound)
      obtain ⟨suffix, hjoin, _hsuffix⟩ :=
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_append
          rate rewards C_star C_h u t z hz m (s + e) hmstart hmend hEndBound
          inputsM ((L ++ [c]) ++ B) hM hprefixEnd
      have htake : inputsM = (((L ++ [c]) ++ B).take inputsM.length) := by
        rw [hjoin]
        simp
      have hMlen' : inputsM.length = b + v := by
        have hMlen0 : inputsM.length = m - s := by simpa [s] using hMlen
        rw [hMlen0]
        dsimp [m]
        rw [← htime]
        dsimp [b]
        omega
      have hA : (L ++ [c]).length = b + 1 := by
        calc
          (L ++ [c]).length = L.length + 1 := by simp
          _ = b + 1 := by
            change L.length + 1 = birthIndex rate rewards C_star C_h z + 1
            exact congrArg (fun n => n + 1) hlenL
      have hshape : inputsM = ((L ++ [c]) ++ B.take (v - 1)) := by
        calc
          inputsM = (((L ++ [c]) ++ B).take inputsM.length) := htake
          _ = (((L ++ [c]) ++ B).take (b + v)) := by rw [hMlen']
          _ = ((L ++ [c]) ++ B.take (v - 1)) := by
            exact take_append_suffix (L ++ [c]) B b v hA hvpos
      have hqueue :
          (QueueReplay.replay (4 * rate.n) (0, P0.queues a) word).2 =
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q
              inputsM inputsM.length a).2 := by
        rw [hqueueLive, hshape]
      have hend : m ≤ endDate rate rewards C_star C_h t z := by
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate
        dsimp [m]
        rw [← htime]
        omega
      have hlen : inputsM.length = m - s := hMlen
      obtain ⟨det, hdet⟩ := numerical_union_of_prefix_queue rate rewards C_star C_h
        u t z hz m hmstart hend inputsM hM hlen a
        (QueueReplay.replay (4 * rate.n) (0, P0.queues a) word).2 hqueue hcross
      exact overflowEvent_mem_allArmOverflowEvent rate rewards C_star C_h u t det hdet
  · rcases hCut with ⟨i, liveWord, segEvent, cutEvent, hdeltaEvent,
      hcutRecordEvent, hsegmentEvent, hentryEvent, hpayloadEvent,
      hliveMapEvent, hcross⟩
    have hcutAtEvent : R[b + 1 + (liveTail rate rewards C_star C_h z).length]? =
        some cutEvent := by
      simpa only [R, b, sourceRecords,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using
        hcutRecordEvent
    have hcutIndex : b + 1 < R.length := by
      have hidx := (List.getElem?_eq_some_iff.mp hcutAtEvent).1
      omega
    have hrecordsLength :=
      ReferenceCompletePhysicalHistory.completeSuffixRecords_length
        rate z rewards C_star C_h
    change R.length = p.T - s at hrecordsLength
    have hsucc : t.val + 1 < p.T := by
      rw [hrecordsLength] at hcutIndex
      omega
    obtain ⟨rout, qout, beta, hbirthNext, hk, hstate, hlater, hB, hallv,
      hEbound, hprefixEnd, hdrop, _hrowsW, rE, qE, _hpayloadE, _hstatesE,
      hboundary⟩ := hafter hsucc
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)
    let B := ReferenceCompleteLaterLiveComplementPrefixReplay.prefixCells
      rewards C_star C_h z ⟨b + 1, hk⟩ rout qout beta hstate hlater
    let e := b + 1 + W.length
    have hW_eq : W = liveTail rate rewards C_star C_h z := by
      change ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (birthIndex rate rewards C_star C_h z + 1) =
          liveTail rate rewards C_star C_h z
      exact continuing_windows_eq rate rewards C_star C_h z
    have hBlen : B.length = W.length := hB
    have htimeEnd : s + e = t.val + 1 + W.length := by
      dsimp [e]
      rw [← htime]
      omega
    have hEndBound : s + e ≤ endDate rate rewards C_star C_h t z := by
      unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate
      rw [← htime, ← hW_eq]
      dsimp [e]
      omega
    have heventIndex : b + 1 + (liveTail rate rewards C_star C_h z).length = e := by
      dsimp [e]
      rw [← hW_eq]
    rcases hboundary with hEnd | ⟨he, segCut, I, l0, ccut, hsegment,
      hentry, hpayload, hpre, _hinitializer, _hI, _hchecked, _hassignment,
      _hsigmaI, _hcutoffI, _hfirstCutoff, _hfreeze, _hbaseCut, _hchosen,
      _hnonempty, _hpartition, hprefixCut, htimeCut, _hrowsCut, _hselectedCut,
      _hrewardsCut, _hcell0, _hcollection, _hcollectionEnabled, _hrateCut,
      _hrewardCut, hdisabled, hphysical, happended⟩
    · have hcutAtEvent' : R[b + 1 + (liveTail rate rewards C_star C_h z).length]? =
          some cutEvent := hcutAtEvent
      have hcutAtEnd : R[e]? = some cutEvent := by simpa only [heventIndex] using hcutAtEvent'
      have hEnd' : e = R.length := by
        simpa only [R, sourceRecords,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hEnd
      have hcutNone : R[e]? = none := by
        rw [hEnd']
        exact List.getElem?_eq_none (Nat.le_refl _)
      rw [hcutNone] at hcutAtEnd
      cases hcutAtEnd
    · have hcutAtEvent' : R[b + 1 + (liveTail rate rewards C_star C_h z).length]? =
          some cutEvent := hcutAtEvent
      have hcutAtEnd : R[e]? = some cutEvent := by simpa only [heventIndex] using hcutAtEvent'
      have hcutGet : R[e]? = some (R[e]'he) := List.getElem?_eq_getElem he
      have hcutEq : cutEvent = R[e]'he := Option.some.inj (hcutAtEnd.symm.trans hcutGet)
      have hentryEq : segEvent.entry = R[e]'he := hentryEvent.trans hcutEq
      subst cutEvent
      have hsegmentAtEvent : ReferenceCollectionSegmentExtraction.segmentAt R e =
          some segEvent := by
        have hsegmentAtEvent' :
            ReferenceCollectionSegmentExtraction.segmentAt R
              (b + 1 + (liveTail rate rewards C_star C_h z).length) = some segEvent := by
          simpa only [R, b, sourceRecords,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using
            hsegmentEvent
        simpa only [heventIndex] using hsegmentAtEvent'
      have hsegEq : segEvent = segCut :=
        Option.some.inj (hsegmentAtEvent.symm.trans hsegment)
      subst segEvent
      have hWdrop :
          (R.drop b).take (1 + (liveTail rate rewards C_star C_h z).length) =
            birth0 :: W := by
        simpa only [R, b, sourceRecords,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
          ← hW_eq] using hdrop
      have hmapEq :
          (birth0 :: W).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i) =
            ((R.drop b).take
              (1 + (liveTail rate rewards C_star C_h z).length)).mapM
              (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i) :=
        congrArg (fun xs => xs.mapM
          (ReferenceFirstCorrectedAssignedArrivalPrefix.attributedArrival? P0 i)) hWdrop.symm
      have happ := happended i
      rw [hmapEq, hliveMapEvent] at happ
      simp only [Option.map_some] at happ
      have hwordCutBase :
          liveWord ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
            l0 (P0.assignment.assigned i) (R[e]'he)] =
          ((([c] ++ B) ++ [ccut]).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival Q cell
              (P0.assignment.assigned i))) := Option.some.inj happ
      have hwordCut :
          liveWord ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
            segCut.context.preLedger (P0.assignment.assigned i) (R[e]'he)] =
          ((([c] ++ B) ++ [ccut]).map fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival Q cell
              (P0.assignment.assigned i))) := by
        rw [hpre]
        exact hwordCutBase
      let a := P0.assignment.assigned i
      have hqueue :
          (QueueReplay.replay (4 * rate.n) (0, P0.queues a)
            (liveWord ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
              segCut.context.preLedger a (R[e]'he)])).2 =
            (UnstoppedRecordedQueueComparison.unstoppedReplay Q
              (((L ++ [c]) ++ B) ++ [ccut])
              (((L ++ [c]) ++ B) ++ [ccut]).length a).2 := by
        rw [hwordCut, hqueues a]
        simpa [List.append_assoc] using
          initialized_queue_replay (rate := rate) L ((([c] ++ B) ++ [ccut])) a
      let mcut := s + e + 1
      have hdate : mcut = t.val + 1 +
          (liveTail rate rewards C_star C_h z).length + 1 := by
        dsimp [mcut, e]
        rw [← htime, ← hW_eq]
        omega
      have hn : t.val + 1 ≤ mcut := by rw [hdate]; omega
      have hend : mcut ≤ endDate rate rewards C_star C_h t z := by
        unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate
        rw [hdeltaEvent, hdate]
      have hprefixCut' : prefixInputs rate rewards C_star C_h mcut z =
          some (((L ++ [c]) ++ B) ++ [ccut]) := by
        simpa [mcut, s, e, W, B,
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart] using hprefixCut
      have hlen : (((L ++ [c]) ++ B) ++ [ccut]).length =
          mcut - s := by
        simp only [List.length_append, List.length_singleton,
          List.length_append, hlenL]
        rw [hBlen]
        dsimp [mcut, e]
        omega
      have hcross' :
          ((QueueReplay.replay (4 * rate.n) (0, P0.queues a)
            (liveWord ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
              segCut.context.preLedger a (R[e]'he)])).2 : ℝ) /
            (rate.n : ℝ) > 1 / (32 * rate.eta.val) := by
        simpa [a, hentryEq] using hcross
      obtain ⟨det, hdet⟩ := numerical_union_of_prefix_queue rate rewards C_star C_h
        u t z hz mcut hn hend (((L ++ [c]) ++ B) ++ [ccut]) hprefixCut' hlen a
        (QueueReplay.replay (4 * rate.n) (0, P0.queues a)
          (liveWord ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
            segCut.context.preLedger a (R[e]'he)])).2 hqueue hcross'
      exact overflowEvent_mem_allArmOverflowEvent rate rewards C_star C_h u t det hdet

/-- The source-specific assigned-arm cover is bounded on the unchanged
original source law by the already accepted numerical all-arm estimate. -/
theorem assignedAttributedOverflowEvent_measure_le (control0 : TimeControl p)
    (u t : Fin p.T) :
    (sourceInputLaw p).real
        (assignedAttributedOverflowEvent rate rewards C_star C_h u t) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  calc
    (sourceInputLaw p).real
        (assignedAttributedOverflowEvent rate rewards C_star C_h u t) ≤
      (sourceInputLaw p).real
        (ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h) :=
        MeasureTheory.measureReal_mono (μ := sourceInputLaw p)
          (assignedAttributedOverflowEvent_subset_allArmOverflowEvent
            rate rewards C_star C_h u t)
          (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) :=
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
        rate rewards C_star C_h control0

/-- Every first-corrected assigned-arm overflow, over all calendar cells, is
contained in the same original-source numerical all-arm event. -/
theorem assignedAttributedOverflowUnion_subset_allArmOverflowEvent :
    (⋃ u : Fin p.T, ⋃ t : Fin p.T,
      assignedAttributedOverflowEvent rate rewards C_star C_h u t) ⊆
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
        rate rewards C_star C_h := by
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨u, t, hzt⟩ := hz
  exact assignedAttributedOverflowEvent_subset_allArmOverflowEvent
    rate rewards C_star C_h u t hzt

/-- The union over every first-corrected cutoff/date cell obeys the original
source numerical all-arm bound, without summing the individual cell bounds. -/
theorem assignedAttributedOverflowUnion_measure_le (control0 : TimeControl p) :
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          assignedAttributedOverflowEvent rate rewards C_star C_h u t) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  calc
    (sourceInputLaw p).real
        (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          assignedAttributedOverflowEvent rate rewards C_star C_h u t) ≤
      (sourceInputLaw p).real
        (ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent
          rate rewards C_star C_h) :=
        MeasureTheory.measureReal_mono (μ := sourceInputLaw p)
          (assignedAttributedOverflowUnion_subset_allArmOverflowEvent
            rate rewards C_star C_h)
          (by finiteness)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) :=
      ReferenceFirstCollectionCorrectedNumericalOverflowSum.allArmOverflowEvent_measure_le
        rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCollectionCorrectedAssignedOverflowCover
end
