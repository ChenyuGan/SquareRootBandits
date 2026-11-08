/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseSupport

import Mathlib.Tactic

/-!
# Literal stopped support after the raw replacement collection

The queue test below continues the original launch-zero numerical calendar
through the actual post-collection live continuation. The release support and
stored payload remain the original source objects.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation

variable {p : ConstructorDimensions.Parameters}

private theorem complete_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hcal : k.val < (ReferenceActivePhysicalHorizon.calendar
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).length := by
    rw [← htimes, List.length_map]
    exact k.isLt
  have heq : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).map (fun r => r.input.time.val))[k.val]'(by
        rw [List.length_map]; exact k.isLt) =
      (ReferenceActivePhysicalHorizon.calendar
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))[k.val]'hcal := by
    simp only [htimes]
  simpa only [List.getElem_map, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', Nat.one_mul] using heq

private theorem complete_record_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time) z =
      some (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] := by
  have ht := complete_record_time rate rewards C_star C_h z k
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  have hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]).input.time.val := by omega
  rw [ite_eq_left hs, ht, Nat.add_sub_cancel_left, List.getElem?_eq_getElem k.isLt]

/-- Join the inclusive raw-collection calendar to the same actual installation
and its live complement. The proof covers both a last-record birth and a
continuing live suffix. -/
theorem actual_postRawK_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hne : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [])
    (hpresent :
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
      let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
      let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
      c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z).length < R.length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let b := c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z).length
    ∃ E_K E_V : List (RecordedQueueRun.RoundInput p.K),
      E_K.length = b ∧ E_V.length ≤ R.length ∧ E_V.take b = E_K ∧
      E_V.length = b + 1 + (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b + 1)).length ∧
      (∀ h, h ≤ E_V.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + h) z = some (E_V.take h)) ∧
      (R.take E_V.length).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        E_V.map some ∧
      ∃ birthCell C, E_V = E_K ++ [birthCell] ++ C ∧
        C.length = (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b + 1)).length := by
  classical
  dsimp only at hpresent ⊢
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
  let b := c + K.length
  have hv : v = ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
      rate rewards C_star C_h z := rfl
  have hb : b < R.length := by simpa only [b, K, c, R] using hpresent
  let endpoint : Fin R.length := ⟨b, hb⟩
  have htime := complete_record_time rate rewards C_star C_h z endpoint
  let endpointRecord := R[endpoint.val]
  have hocc : ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
      rate rewards C_star C_h endpointRecord.input.time z := by
    have hchar := ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_iff_endpoint
      rate rewards C_star C_h z endpointRecord.input.time
    apply hchar.mpr
    refine ⟨hne, hb, ?_⟩
    change endpointRecord.input.time.val = s + b
    exact htime
  obtain ⟨payload, onset, actual, _hphase, _hactual, hchosen⟩ :=
    (ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_iff_actualLaterChosen
      rate rewards C_star C_h endpointRecord.input.time z).1 hocc
  have hactualRecord := complete_record_actual rate rewards C_star C_h z endpoint
  have hsame : actual = endpointRecord := by
    exact Option.some.inj (_hactual.symm.trans hactualRecord)
  rw [hsame] at hchosen
  obtain ⟨E_K, hKlen, _hKbound, hKprefix, _hKindices, _hKfirst, _hKlast⟩ :=
    ReferenceFirstReplacementCollectionInclusiveStoppedCharge.complete_inclusive_stopped_calendar
      rate rewards C_star C_h control0 z hne
  have hKlen' : E_K.length = b := by
    simpa only [b, K, c, R, w, v,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords] using hKlen
  obtain ⟨P0, rb, qb, beta, birthCell, native, hP0len, _hPslots, hPprefix,
    _hinitialize, _hpost, _hbirth, _hstrict, _hbase, _hcell, _hnative,
    _hnativePayload, _henabled, hBirthPrefix, hBirthSlots, _hseed, _hdown,
    hcontinuation⟩ :=
    ReferenceCompleteInstallationOutsideCalendarReplay.actual_later_installation_complement_calendar_replay
      rate rewards C_star C_h z endpoint hchosen
  have hP0len' : P0.length = b := by simpa only [b, K, c, R, w, v] using hP0len
  have hBirthPrefix' :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + (b + 1)) z = some (P0 ++ [birthCell]) := by
    simpa only [b, K, c, R, w, v, s] using hBirthPrefix
  have hBirthSlots' :
      (R.take (b + 1)).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        (P0 ++ [birthCell]).map some := by
    simpa only [b, K, c, R, w, v] using hBirthSlots
  have hprefixBirth :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + b) z = some E_K := by
    have hbK : b ≤ E_K.length := by rw [hKlen']
    have h := hKprefix b hbK
    simpa only [hKlen', List.take_of_length_le (Nat.le_of_eq hKlen')] using h
  have hPprefixBirth :
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + b) z = some P0 := by
    have h := hPprefix b (by simp [endpoint])
    simpa only [hP0len', List.take_of_length_le (Nat.le_of_eq hP0len')] using h
  have hP0eq : P0 = E_K := Option.some.inj (hPprefixBirth.symm.trans hprefixBirth)
  rcases hcontinuation with hterminal | ⟨k, C, hk, _hstate, htail⟩
  · have hk' : b + 1 = R.length := by simpa only [b, K, c, R, w, v] using hterminal
    let E_V := P0 ++ [birthCell]
    have hlen : E_V.length = b + 1 := by simp [E_V, hP0len']
    have hprefix : ∀ h, h ≤ E_V.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + h) z = some (E_V.take h) := by
      intro h hh
      by_cases hle : h ≤ b
      · have hp := hKprefix h (by omega)
        have hinner : h ≤ P0.length := by omega
        have htake : E_V.take h = E_K.take h := by
          change (P0 ++ [birthCell]).take h = E_K.take h
          rw [List.take_append_of_le_length hinner]
          exact congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs.take h) hP0eq
        rw [htake]
        exact hp
      · have heq : h = b + 1 := by omega
        subst h
        have htake : E_V.take (b + 1) = E_V := by
          apply List.take_of_length_le
          simp [E_V, hP0len']
        rw [htake]
        exact hBirthPrefix'
    have hslots : (R.take E_V.length).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = E_V.map some := by
      simpa only [E_V, hlen, hk'] using hBirthSlots'
    refine ⟨E_K, E_V, hKlen', ?_, ?_, ?_, hprefix, hslots, ?_⟩
    · omega
    · have hinner : b ≤ P0.length := by rw [hP0len']
      have hfull : P0.length ≤ b := by rw [hP0len']
      change (P0 ++ [birthCell]).take b = E_K
      rw [List.take_append_of_le_length hinner, List.take_of_length_le hfull]
      exact hP0eq
    · have hW : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z (b + 1) = [] := by
        unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        change (R.drop (b + 1)).takeWhile _ = []
        rw [hk', List.drop_length, List.takeWhile_nil]
      rw [hlen, hW, List.length_nil, Nat.add_zero]
    · refine ⟨birthCell, [], ?_, ?_⟩
      · change P0 ++ [birthCell] = E_K ++ [birthCell] ++ []
        rw [List.append_nil, hP0eq]
      · unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        change 0 = ((R.drop (b + 1)).takeWhile _).length
        rw [hk', List.drop_length, List.takeWhile_nil, List.length_nil]
  · have hk' : k.val = b + 1 := by simpa only [b, K, c, R, w, v] using hk
    dsimp only at htail
    rcases htail with ⟨hClen, _hCmap, _htimes, heR, _heT, hHlen,
      hHprefix, hHslots, _hdisabled, _hcounts, _rE, _qE, _hlast, _hincoming,
      _hvalues, _halter⟩
    let E_V := P0 ++ [birthCell] ++ C
    have hWlen : C.length =
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z k.val).length := by
      exact hClen
    have hHlen' : E_V.length = k.val +
        (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
          rate rewards C_star C_h z k.val).length := by
      simpa only [E_V, hWlen] using hHlen
    have hElen : E_V.length ≤ R.length := by simpa only [hHlen'] using heR
    have hprefix : ∀ h, h ≤ E_V.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + h) z = some (E_V.take h) := by
      intro h hh
      by_cases hle : h ≤ b
      · have hp := hKprefix h (by omega)
        have houter : h ≤ (P0 ++ [birthCell]).length := by simp [hP0len']; omega
        have hinner : h ≤ P0.length := by omega
        have htake : E_V.take h = E_K.take h := by
          dsimp only [E_V]
          rw [List.take_append_of_le_length houter]
          rw [List.take_append_of_le_length hinner]
          exact congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs.take h) hP0eq
        rw [htake]
        exact hp
      · have hp := hHprefix h (by omega) (by simpa only [hHlen'] using hh)
        simpa only [E_V] using hp
    have hslots : (R.take E_V.length).map
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = E_V.map some := by
      simpa only [E_V, hHlen'] using hHslots
    have htakeJoin : E_V.take b = E_K := by
      have htake : E_V.take b = P0 := by
        have houter : b ≤ (P0 ++ [birthCell]).length := by simp [hP0len']
        have hinner : b ≤ P0.length := by rw [hP0len']
        have hfull : P0.length ≤ b := by rw [hP0len']
        dsimp only [E_V]
        change ((P0 ++ [birthCell]) ++ C).take b = P0
        rw [List.take_append_of_le_length houter]
        rw [List.take_append_of_le_length hinner]
        rw [List.take_of_length_le hfull]
      rw [htake, hP0eq]
    refine ⟨E_K, E_V, hKlen', hElen, htakeJoin, ?_, hprefix, hslots, birthCell, C, ?_, ?_⟩
    · rw [hHlen', hk']
    · change P0 ++ [birthCell] ++ C = E_K ++ [birthCell] ++ C
      rw [hP0eq]
    · rw [← hk']
      exact hClen

private theorem release_member_index
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : r ∈ ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val] ::
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)).dropWhile
          ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    s ≤ r.input.time.val ∧ r.input.time.val - s < b.val + 1 +
      (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b.val + 1)).length := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  have hW : W = (R.drop (b.val + 1)).take W.length :=
    List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
  have hV : R[b.val] :: W = (R.drop b.val).take (1 + W.length) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    simpa only [Nat.add_comm 1, List.take_succ_cons] using congrArg (List.cons R[b.val]) hW
  have hm : r ∈ (R.drop b.val).take (1 + W.length) := by
    rw [← hV]
    exact List.dropWhile_sublist _ |>.subset hr
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hm
  have hj' : j < 1 + W.length ∧ j < (R.drop b.val).length := by
    simpa only [List.length_take, Nat.lt_min] using hj
  have hidx : b.val + j < R.length := by
    have := b.isLt
    simp only [List.length_drop] at hj'
    omega
  have heq : R[b.val + j] = r := by
    simpa only [List.getElem_take, List.getElem_drop] using hget
  have ht := complete_record_time rate rewards C_star C_h z ⟨b.val + j, hidx⟩
  change R[b.val + j].input.time.val =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + (b.val + j) at ht
  rw [heq] at ht
  dsimp only
  change _ ∧ _ < b.val + 1 + W.length
  omega

/-- The post-rawK date mask uses the original decoder event and the current
retained test of the launch-zero queue machine. -/
def postRawKStoppedDate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
      rate rewards C_star C_h t z ∧
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ∧
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t

/-- Incoming pending membership is read from the same fixed-timestamp payload
as the actual raw release history. -/
def postRawKStoppedPendingDate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport
      rate rewards C_star C_h t i z ∧
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ∧
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t

/-- Literal form of the kept source date, before identifying its prefix with
the inherited calendar word. -/
def postRawKLiteralDate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
      rate rewards C_star C_h t z ∧
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ∧
    ∃ N : List (RecordedQueueRun.RoundInput p.K),
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
        rate rewards C_star C_h t z = some N ∧
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N

private theorem run_overflow_false_iff_literalQueueSafe
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (N : List (RecordedQueueRun.RoundInput p.K)) :
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false ↔
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  have hfirst := UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
    q N N.length (by rfl)
  simp only [List.take_length] at hfirst
  have hrun : (RecordedQueueRun.run q N).overflow = false ↔
      N.length < UnstoppedRecordedQueueComparison.firstOverflowPrefix q N := by
    constructor
    · intro hfalse
      by_contra hnot
      have hcross := hfirst.mpr (Nat.le_of_not_gt hnot)
      rw [hfalse] at hcross
      cases hcross
    · intro hsafe
      cases hflag : (RecordedQueueRun.run q N).overflow with
      | false => rfl
      | true =>
          have hcross : (RecordedQueueRun.run q N).overflow = true := hflag
          have hle := hfirst.mp hcross
          omega
  have hsafe := ReferenceFirstReplacementCollectionInclusiveStoppedCharge.literalQueueSafe_take_iff_before_first
    rate N N.length (by rfl)
  simpa only [List.take_length] using hrun.trans hsafe.symm

/-- The public finite-prefix overflow identity gives the needed local bridge
between the queue readout and literal safety on every past prefix and arm. -/
theorem retainedQueue_iff_literalQueueSafe
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (N : List (RecordedQueueRun.RoundInput p.K))
    (hN : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h t z = some N) :
    z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N := by
  have hpast := ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs_eq_pastCells?
    rate rewards C_star C_h t z
  have hpastN : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z = some N := by rw [← hpast, hN]
  have hread : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t z = some
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) N)) := by
    simp only [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hpastN,
      Option.map_some]
  have hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H
      rate rewards C_star C_h t ↔
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) N).overflow = false := by
    rw [ReferenceFirstCollectionCurrentRetainedGate.H]
    change (∃ v, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
      rate rewards C_star C_h t z = some v ∧ v.2.1 = false) ↔ _
    rw [hread]
    simp [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  rw [hH]
  exact run_overflow_false_iff_literalQueueSafe rate N

/-- The original strict-past literal decoder test is exactly the admitted
decoder endpoint's kept-date test, so it belongs to the pre-round field. -/
theorem safe_iff_decoderDateKeptAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) :
    ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ↔
    ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
      rate rewards C_star C_h z t := by
  rw [ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe,
    ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_iff_no_earlier]
  constructor
  · intro hs u hu hfail
    exact hs u hu ((ReferenceFirstCollectionLiteralStoppedCharge.literalFailure_iff_decoderFailureAt
      rate rewards C_star C_h z u).mpr hfail)
  · intro hs u hu hfail
    exact (hs u hu) ((ReferenceFirstCollectionLiteralStoppedCharge.literalFailure_iff_decoderFailureAt
      rate rewards C_star C_h z u).mp hfail)

/-- Exact literal meaning of the post-rawK stopped date: on the same source
gate, retaining the date under H is equivalent to the original literal queue
word being safe. -/
theorem postRawKStoppedDate_iff_literalDate
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKStoppedDate rate rewards C_star C_h t z ↔
      postRawKLiteralDate rate rewards C_star C_h t z := by
  constructor
  · rintro ⟨hgate, hsafe, hH⟩
    have hprefix :=
      ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs_eq_pastCells?
        rate rewards C_star C_h t z
    have hsome : ∃ N : List (RecordedQueueRun.RoundInput p.K),
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
          rate rewards C_star C_h t z = some N := by
      have hread := hH
      rw [ReferenceFirstCollectionCurrentRetainedGate.H] at hread
      rcases hread with ⟨v, hv, _⟩
      change (ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z).map _ = some v at hv
      cases hpast : ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z with
      | none => simp [hpast] at hv
      | some N => exact ⟨N, by rw [hprefix, hpast]⟩
    obtain ⟨N, hN⟩ := hsome
    exact ⟨hgate, hsafe, N, hN,
      (retainedQueue_iff_literalQueueSafe rate rewards C_star C_h t z N hN).mp hH⟩
  · rintro ⟨hgate, hsafe, N, hN, hqueue⟩
    refine ⟨hgate, hsafe,
      (retainedQueue_iff_literalQueueSafe rate rewards C_star C_h t z N hN).mpr hqueue⟩

/-- For any actual source date whose joined launch prefix is present, the
literal queue witness is exactly the inherited original-calendar prefix. -/
theorem postRawKLiteralDate_joined_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (E : List (RecordedQueueRun.RoundInput p.K))
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hstart : s ≤ t.val) (hindex : t.val - s ≤ E.length)
    (hprefix : ∀ h, h ≤ E.length →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (s + h) z = some (E.take h))
    (hkept : postRawKLiteralDate rate rewards C_star C_h t z) :
    ∃ N, ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
        rate rewards C_star C_h t z = some N ∧
      N = E.take (t.val - s) ∧
      ReferenceFirstCollectionLiteralStoppedCharge.literalQueueSafe rate N := by
  obtain ⟨_hgate, _hsafe, N, hN, hqueue⟩ := hkept
  have hjoined : ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
      rate rewards C_star C_h t z = some (E.take (t.val - s)) := by
    unfold ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
    simpa only [Nat.add_sub_of_le hstart] using hprefix (t.val - s) hindex
  refine ⟨N, hN, Option.some.inj (hN.symm.trans hjoined), hqueue⟩

/-- Every actual raw release member has its strict-past numerical word in
one and the same inherited calendar. Presence and index bounds are derived
from support, including the absent and horizon alternatives. -/
theorem postRawKReleaseSupport_inherited_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ []) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
    let b := c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z).length
    ∃ E_K E_V : List (RecordedQueueRun.RoundInput p.K),
      E_K.length = b ∧ E_V.take b = E_K ∧ E_V.length ≤ R.length ∧
      (∀ h, h ≤ E_V.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (s + h) z = some (E_V.take h)) ∧
      (R.take E_V.length).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) =
        E_V.map some ∧
      ∀ t : Fin p.T,
        ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
          rate rewards C_star C_h t z →
        s ≤ t.val ∧ t.val - s < E_V.length ∧
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
          rate rewards C_star C_h t z = some (E_V.take (t.val - s)) := by
  intro R s w v c b
  have hK : ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
      rate rewards C_star C_h z ≠ [] := by
    intro h
    apply hrel
    simp only [ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords, h, ↓reduceIte]
  have hb : b < R.length := by
    by_contra hn
    apply hrel
    unfold ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
    rw [ite_eq_right hK]
    change (if hb : b < R.length then _ else []) = []
    rw [dite_eq_right hn]
  obtain ⟨E_K, E_V, hKlen, hbound, htake, hlen, hpref, hslots, _hsplit⟩ :=
    actual_postRawK_calendar rate rewards C_star C_h control0 z hK hb
  refine ⟨E_K, E_V, hKlen, htake, hbound, hpref, hslots, ?_⟩
  intro t ht
  obtain ⟨r, hr, htime⟩ :=
    (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
      rate rewards C_star C_h z t).mpr ht
  have hr' : r ∈ (R[b] :: ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)).dropWhile
        ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice := by
    unfold ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords at hr
    rw [ite_eq_right hK] at hr
    change r ∈ (if hb : b < R.length then _ else []) at hr
    rw [dite_eq_left hb] at hr
    exact hr
  have hi := release_member_index rate rewards C_star C_h z ⟨b, hb⟩ r hr'
  rw [htime] at hi
  change s ≤ t.val ∧ t.val - s < b + 1 +
    (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b + 1)).length at hi
  have hlen' : E_V.length = b + 1 +
      (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (b + 1)).length := hlen
  refine ⟨hi.1, by rw [hlen']; exact hi.2, ?_⟩
  unfold ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
  have h := hpref (t.val - s) (by rw [hlen']; omega)
  change ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
    rate rewards C_star C_h (s + (t.val - s)) z = _ at h
  rw [Nat.add_sub_of_le hi.1] at h
  exact h

/-- On the actual nonempty branch the first exclusions are the literal
strict-past decoder endpoint and the first crossing of the inherited word.
The cutoff is formed before any empty-phase endpoint is replaced by a sentinel. -/
theorem postRawKStoppedDate_cutoff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ []) :
    ∃ (E : List (RecordedQueueRun.RoundInput p.K)) (cutoff : ℕ),
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).take E.length).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = E.map some ∧
      (∀ t : Fin p.T,
        ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
          rate rewards C_star C_h t z →
        ReferenceFirstReplacementCollectionInclusiveStoppedCharge.originalPrefixInputs
          rate rewards C_star C_h t z = some (E.take (t.val -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))) ∧
      cutoff = min (ReferenceFirstCollectionLiteralStoppedCharge.literalDecoderEndpoint
          rate rewards C_star C_h z)
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
          UnstoppedRecordedQueueComparison.firstOverflowPrefix
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) E + 1) ∧
      1 ≤ cutoff ∧ cutoff ≤ p.T + 1 ∧
      ∀ t : Fin p.T,
        ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
          rate rewards C_star C_h t z →
        (postRawKStoppedDate rate rewards C_star C_h t z ↔ t.val + 1 < cutoff) := by
  obtain ⟨E_K, E_V, _hKlen, _htake, _hbound, _hprefix, hslots, hdates⟩ :=
    postRawKReleaseSupport_inherited_prefix rate rewards C_star C_h control0 z hrel
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let first := UnstoppedRecordedQueueComparison.firstOverflowPrefix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) E_V
  let decoder := ReferenceFirstCollectionLiteralStoppedCharge.literalDecoderEndpoint
    rate rewards C_star C_h z
  have hdecoder : 2 ≤ decoder ∧ decoder ≤ p.T + 1 := by
    dsimp only [decoder]
    rw [ReferenceFirstCollectionLiteralStoppedCharge.literalDecoderEndpoint_eq]
    exact ReferenceFirstCollectionInclusiveDecoderStop.firstExcludedDate_bounds
      rate rewards C_star C_h z
  refine ⟨E_V, min decoder (s + first + 1), hslots,
    (fun t ht => (hdates t ht).2.2), rfl, by omega, by omega, ?_⟩
  intro t ht
  obtain ⟨hs, hi, hN⟩ := hdates t ht
  have hqueue : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔
      t.val - s < first := by
    rw [retainedQueue_iff_literalQueueSafe rate rewards C_star C_h t z _ hN]
    exact ReferenceFirstReplacementCollectionInclusiveStoppedCharge.literalQueueSafe_take_iff_before_first
      rate E_V (t.val - s) (Nat.le_of_lt hi)
  have hsafe : ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
      rate rewards C_star C_h z t.val ↔ t.val + 1 < decoder := by
    rw [safe_iff_decoderDateKeptAt,
      ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt,
      ← ReferenceFirstCollectionLiteralStoppedCharge.literalDecoderEndpoint_eq]
  change s ≤ t.val at hs
  simp only [postRawKStoppedDate, ht, true_and, hsafe, hqueue, Nat.lt_min]
  omega

private theorem raw_release_gate_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ []) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (a : ℕ) (M : ReferenceActivePhysicalStep.Payload rate),
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecords rate z rewards C_star C_h
        hc s (p.T - s) rfl (by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
          dsimp only [s]; omega) a =
        ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords rate rewards C_star C_h z ∧
      M.sigma.val = a ∧
      ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
        rate rewards C_star C_h M.sigma z ∧
      ∀ r ∈ ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords rate rewards C_star C_h z,
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h a r.input.time z =
          ReferencePhysicalReleaseQuota.pendingSet M r := by
  intro s
  have h := ReferencePostReplacementCollectionReleaseSupport.raw_release_source_readouts
    rate rewards C_star C_h z
  dsimp only at h
  split at h
  · exact (hrel h).elim
  · rename_i hK
    split at h
    · rename_i hb
      obtain ⟨⟨hc, hgate⟩, M, _hbirth, hstamp, hread⟩ := h
      refine ⟨hc, M.sigma.val, M, ?_, rfl, ?_, ?_⟩
      · rw [hstamp]
        exact hgate
      · exact (ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_iff_endpoint
          rate rewards C_star C_h z M.sigma).mpr ⟨hK, hb, hstamp⟩
      · intro r hr
        exact ⟨(hread r hr).1, (hread r hr).2.2.2.2⟩
    · exact (hrel h).elim

/-- Adaptation of the stopped raw release support uses the original
source-prefix field at the next pre-round. -/
theorem postRawKStoppedDate_measurable_preRound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKStoppedDate rate rewards C_star C_h t z} := by
  have hgate := ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport_measurable
    rate rewards C_star C_h control0 t
  have hsafe : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
          rate rewards C_star C_h z t.val} := by
    have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
          ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
            rate rewards C_star C_h z t.val} =
        {z | ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
          rate rewards C_star C_h z t} := by
      ext z
      exact safe_iff_decoderDateKeptAt rate rewards C_star C_h z t
    rw [hEq]
    exact ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_measurable_preRound
      rate rewards C_star C_h control0 t
  have hqueue := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
      postRawKStoppedDate rate rewards C_star C_h t z} =
      {z | ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
        rate rewards C_star C_h t z} ∩
      {z | ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z t.val} ∩
      {z | z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t} := by
    ext z
    change (ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
        rate rewards C_star C_h t z ∧
      ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z t.val ∧
      z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t) ↔ _
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact (hgate.inter hsafe).inter hqueue

/-- Pending support stays on the same fixed-u pending history and is empty
outside the exact stopped release support. -/
theorem postRawKStoppedPending_measurable_preRound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKStoppedPendingDate rate rewards C_star C_h t i z} := by
  have hpending := ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport_measurable
    rate rewards C_star C_h control0 t i
  have hsafe : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
          rate rewards C_star C_h z t.val} := by
    have hEq : {z : BootstrapPrivateRoundStreams.SourceInput p |
          ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
            rate rewards C_star C_h z t.val} =
        {z | ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt
          rate rewards C_star C_h z t} := by
      ext z
      exact safe_iff_decoderDateKeptAt rate rewards C_star C_h z t
    rw [hEq]
    exact ReferenceFirstCollectionInclusiveDecoderStop.decoderDateKeptAt_measurable_preRound
      rate rewards C_star C_h control0 t
  have hqueue := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H
    rate rewards C_star C_h control0 t
  have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
      postRawKStoppedPendingDate rate rewards C_star C_h t i z} =
      {z | ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport
        rate rewards C_star C_h t i z} ∩
      {z | ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z t.val} ∩
      {z | z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t} := by
    ext z
    change (ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport
        rate rewards C_star C_h t i z ∧
      ReferenceFirstReplacementCollectionLiteralDecoderSafeSupport.Safe
        rate rewards C_star C_h z t.val ∧
      z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t) ↔ _
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact (hpending.inter hsafe).inter hqueue

/-- The stopped phase carries the original incoming pending set on kept dates
and the empty set off support. -/
def postRawKStoppedPendingSet
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset (Fin (p.m - 1)) :=
  if postRawKStoppedDate rate rewards C_star C_h t z then
    Finset.univ.filter (fun i => postRawKStoppedPendingDate rate rewards C_star C_h t i z)
  else ∅

/-- The finite one-based support of the literal stopped post-rawK release
date. This is formed directly from the original source-round predicate. -/
def postRawKStoppedSupport
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : Finset ℕ :=
  ((Finset.univ : Finset (Fin p.T)).filter
    (fun t => postRawKStoppedDate rate rewards C_star C_h t z)).image
      (fun t => t.val + 1)

theorem postRawKStoppedSupport_mem_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (v : ℕ) :
    v ∈ postRawKStoppedSupport rate rewards C_star C_h z ↔
      ∃ t : Fin p.T, postRawKStoppedDate rate rewards C_star C_h t z ∧
        t.val + 1 = v := by
  simp [postRawKStoppedSupport]

theorem postRawKStoppedSupport_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (v : ℕ)
    (hv : v ∈ postRawKStoppedSupport rate rewards C_star C_h z) :
    1 ≤ v ∧ v ≤ p.T := by
  obtain ⟨t, _hkeep, rfl⟩ := (postRawKStoppedSupport_mem_iff
    rate rewards C_star C_h z v).mp hv
  have ht := t.isLt
  omega

theorem postRawKStoppedSupport_empty_of_rawReleaseRecords_empty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hempty : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z = []) :
    postRawKStoppedSupport rate rewards C_star C_h z = ∅ := by
  ext v
  constructor
  · intro hv
    obtain ⟨t, hkeep, _⟩ := (postRawKStoppedSupport_mem_iff
      rate rewards C_star C_h z v).mp hv
    have hraw := hkeep.1
    obtain ⟨r, hr, _⟩ := (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
      rate rewards C_star C_h z t).mpr hraw
    rw [hempty] at hr
    simp at hr
  · intro hv
    simp at hv

/-- The raw absent and horizon branches retain the actual empty release list;
no later birth or endpoint is introduced. -/
theorem rawReleaseRecords_empty_of_absent_postRawK
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (habsent :
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z = [] ∨
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
      let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
      let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
      c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z).length ≥ R.length) :
    ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z = [] := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
  let K := ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK rate rewards C_star C_h z
  rcases habsent with hK | hbound
  · simp [ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords, hK]
  · change c + K.length ≥ R.length at hbound
    have hnot : ¬ c + K.length < R.length := by omega
    simp [ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords,
      R, w, v, c, K, hnot]

/-- Every kept release date is tied to the same unique earlier occurrence
selected by the actual post-rawK scan. -/
theorem postRawKStoppedDate_unique_occurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : postRawKStoppedDate rate rewards C_star C_h t z) :
    ∃! u : Fin p.T,
      u.val < t.val ∧
        ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
          rate rewards C_star C_h u z ∧
        (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          u.val t z).map Prod.fst = some true := by
  obtain ⟨u, hut, hu, hentry⟩ := hkeep.1
  refine ⟨u, ⟨hut, hu, hentry⟩, ?_⟩
  intro v hv
  exact (ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
    rate rewards C_star C_h u v z hu hv.2.1).symm

/-- The stopped pending predicate refers to that same unique assignment
timestamp, while preserving its actual fixed-u pending readout. -/
theorem postRawKStoppedPendingDate_same_occurrence
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : postRawKStoppedDate rate rewards C_star C_h t z)
    (hpending : postRawKStoppedPendingDate rate rewards C_star C_h t i z) :
    ∃ u : Fin p.T,
      u.val < t.val ∧
        ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence
          rate rewards C_star C_h u z ∧
        (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          u.val t z).map Prod.fst = some true ∧
        i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
          u.val t z := by
  obtain ⟨u, hut, hu, hentry⟩ := hkeep.1
  obtain ⟨v, hvt, hv, hpending⟩ := hpending.1
  have huv := ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
    rate rewards C_star C_h u v z hu hv
  subst v
  exact ⟨u, hut, hu, hentry, hpending⟩

theorem postRawKStoppedSupport_empty_of_absent_postRawK
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (habsent :
      ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z = [] ∨
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
      let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
      let c := v + 1 + (ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v).length
      c + (ReferenceFirstReplacementCollectionGlobalDecoderCharge.rawK
        rate rewards C_star C_h z).length ≥ R.length) :
    postRawKStoppedSupport rate rewards C_star C_h z = ∅ :=
  postRawKStoppedSupport_empty_of_rawReleaseRecords_empty rate rewards C_star C_h z
    (rawReleaseRecords_empty_of_absent_postRawK rate rewards C_star C_h z habsent)

theorem postRawKStoppedPendingSet_mem_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z ↔
      postRawKStoppedDate rate rewards C_star C_h t z ∧
        postRawKStoppedPendingDate rate rewards C_star C_h t i z := by
  by_cases hkeep : postRawKStoppedDate rate rewards C_star C_h t z
  · simp only [postRawKStoppedPendingSet, hkeep, ↓reduceIte,
      Finset.mem_filter, Finset.mem_univ, true_and]
  · simp [postRawKStoppedPendingSet, hkeep]

theorem postRawKStoppedPendingSet_eq_empty_of_not_kept
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hnot : ¬ postRawKStoppedDate rate rewards C_star C_h t z) :
    postRawKStoppedPendingSet rate rewards C_star C_h t z = ∅ := by
  simp [postRawKStoppedPendingSet, hnot]

theorem postRawKStoppedPendingSet_mem_measurable_preRound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z} := by
  have hkeep := postRawKStoppedDate_measurable_preRound rate rewards C_star C_h control0 t
  have hpending := postRawKStoppedPending_measurable_preRound
    rate rewards C_star C_h control0 t i
  have hset : {z : BootstrapPrivateRoundStreams.SourceInput p |
      i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z} =
      {z | postRawKStoppedDate rate rewards C_star C_h t z} ∩
      {z | postRawKStoppedPendingDate rate rewards C_star C_h t i z} := by
    ext z
    exact postRawKStoppedPendingSet_mem_iff rate rewards C_star C_h t z i
  rw [hset]
  exact hkeep.inter hpending

/-- Ordered actual release records kept by the literal strict-past mask. -/
def postRawKStoppedRecords
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords rate rewards C_star C_h z).filter
    (fun r => decide (postRawKStoppedDate rate rewards C_star C_h r.input.time z))

private theorem stopped_support_eq_clipped
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) (cutoff : ℕ)
    (hcut : ∀ t : Fin p.T,
      ReferencePostReplacementCollectionReleaseSupport.postRawKReleaseSupport
        rate rewards C_star C_h t z →
      (postRawKStoppedDate rate rewards C_star C_h t z ↔ t.val + 1 < cutoff)) :
    postRawKStoppedSupport rate rewards C_star C_h z =
      (((ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
        rate rewards C_star C_h z).map (fun r => r.input.time.val + 1)).toFinset).filter (· < cutoff) := by
  ext v
  rw [postRawKStoppedSupport_mem_iff, Finset.mem_filter]
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨r, hr, htime⟩ :=
      (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
        rate rewards C_star C_h z t).mpr ht.1
    exact ⟨⟨r, hr, by rw [htime]⟩, (hcut t ht.1).mp ht⟩
  · rintro ⟨⟨r, hr, rfl⟩, hv⟩
    have ht := (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
      rate rewards C_star C_h z r.input.time).mp ⟨r, hr, rfl⟩
    exact ⟨r.input.time, (hcut _ ht).mpr hv, rfl⟩

/-- The literal stopped support is an actual bounded interval. The raw gate
is clipped at the true exclusion before its empty sentinel is applied. -/
theorem postRawKStoppedSupport_exists_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ∃ left right : ℕ,
      postRawKStoppedSupport rate rewards C_star C_h z = Finset.Ico left right ∧
      1 ≤ left ∧ left ≤ right ∧ right ≤ p.T + 1 := by
  by_cases hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z = []
  · refine ⟨p.T + 1, p.T + 1, ?_, by omega, le_rfl, le_rfl⟩
    rw [postRawKStoppedSupport_empty_of_rawReleaseRecords_empty rate rewards C_star C_h z hrel,
      Finset.Ico_self]
  · obtain ⟨_E, cutoff, _hslots, _hdates, _hcutoff, hlo, hhi, hcut⟩ :=
      postRawKStoppedDate_cutoff rate rewards C_star C_h control0 z hrel
    obtain ⟨hc, a, M, hgate, _hstamp, _hocc, _hread⟩ := raw_release_gate_data rate rewards C_star C_h z hrel
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hspan : s + (p.T - s) ≤ p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      dsimp only [s]; omega
    have hinterval := ReferenceLocalReleasePendingHistory.source_local_gate_interval_restrict
      rate z rewards C_star C_h hc s (p.T - s) rfl hspan a cutoff ⟨hlo, hhi⟩
    dsimp only at hinterval
    refine ⟨_, _, ?_, hinterval.2⟩
    rw [stopped_support_eq_clipped rate rewards C_star C_h z cutoff hcut, ← hinterval.1]
    change (((ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z).map _).toFinset).filter _ =
      (((ReferenceLocalReleasePendingHistory.sourceLocalGateRecords rate z rewards C_star C_h
        hc s (p.T - s) rfl hspan a).map _).toFinset).filter _
    rw [hgate]

/-- The first literal supported one-based date, or the common empty sentinel. -/
def postRawKReleaseSigma
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (postRawKStoppedSupport rate rewards C_star C_h z).Nonempty then
    (postRawKStoppedSupport rate rewards C_star C_h z).min' h else p.T + 1

/-- One past the last literal supported date, or the same empty sentinel. -/
def postRawKReleaseTheta
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℕ :=
  if h : (postRawKStoppedSupport rate rewards C_star C_h z).Nonempty then
    (postRawKStoppedSupport rate rewards C_star C_h z).max' h + 1 else p.T + 1

/-- Exact empty-phase endpoints; failure in the inherited past may empty the
phase even while the original physical release records continue. -/
theorem postRawKRelease_endpoints_empty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (he : postRawKStoppedSupport rate rewards C_star C_h z = ∅) :
    postRawKReleaseSigma rate rewards C_star C_h z = p.T + 1 ∧
      postRawKReleaseTheta rate rewards C_star C_h z = p.T + 1 := by
  simp only [postRawKReleaseSigma, postRawKReleaseTheta, he, Finset.not_nonempty_empty,
    dite_false, and_self]

/-- Contiguity and bounds of both actual literal endpoints. -/
theorem postRawKRelease_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKStoppedSupport rate rewards C_star C_h z =
        Finset.Ico (postRawKReleaseSigma rate rewards C_star C_h z)
          (postRawKReleaseTheta rate rewards C_star C_h z) ∧
      1 ≤ postRawKReleaseSigma rate rewards C_star C_h z ∧
      postRawKReleaseSigma rate rewards C_star C_h z ≤ postRawKReleaseTheta rate rewards C_star C_h z ∧
      postRawKReleaseTheta rate rewards C_star C_h z ≤ p.T + 1 := by
  let S := postRawKStoppedSupport rate rewards C_star C_h z
  by_cases h : S.Nonempty
  · obtain ⟨left, right, hI, hlo, _horder, hhi⟩ :=
      postRawKStoppedSupport_exists_interval rate rewards C_star C_h control0 z
    change S = Finset.Ico left right at hI
    have hne := h
    obtain ⟨x, hx⟩ := hne
    have hx' := hx
    rw [hI, Finset.mem_Ico] at hx'
    have hmin : S.min' h = left := by
      apply (Finset.min'_eq_iff S h left).mpr
      constructor
      · rw [hI, Finset.mem_Ico]; omega
      · intro y hy
        rw [hI, Finset.mem_Ico] at hy
        exact hy.1
    have hmax : S.max' h = right - 1 := by
      apply (Finset.max'_eq_iff S h (right - 1)).mpr
      constructor
      · rw [hI, Finset.mem_Ico]; omega
      · intro y hy
        rw [hI, Finset.mem_Ico] at hy
        omega
    have hσ : postRawKReleaseSigma rate rewards C_star C_h z = left := by
      exact (dite_eq_left h).trans hmin
    have hθ : postRawKReleaseTheta rate rewards C_star C_h z = right := by
      change (if h : S.Nonempty then S.max' h + 1 else p.T + 1) = right
      rw [dite_eq_left h, hmax]
      omega
    rw [hσ, hθ]
    exact ⟨hI, hlo, by omega, hhi⟩
  · have he : postRawKStoppedSupport rate rewards C_star C_h z = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨hσ, hθ⟩ := postRawKRelease_endpoints_empty rate rewards C_star C_h z he
    rw [hσ, hθ, he, Finset.Ico_self]
    exact ⟨rfl, by omega, le_rfl, le_rfl⟩

/-- The same whole payload and ordered source gates, restricted at the true
cutoff. In particular an empty stopped phase cannot restore earlier raw gates
by substituting the endpoint sentinel. -/
theorem postRawKStoppedRecords_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ []) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (hc : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (a cutoff : ℕ) (M : ReferenceActivePhysicalStep.Payload rate),
      1 ≤ cutoff ∧ cutoff ≤ p.T + 1 ∧ M.sigma.val = a ∧
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore rate z rewards C_star C_h
        hc s (p.T - s) rfl (by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
          dsimp only [s]; omega) a cutoff = postRawKStoppedRecords rate rewards C_star C_h z ∧
      ∀ r ∈ postRawKStoppedRecords rate rewards C_star C_h z,
        ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some M ∧
        postRawKStoppedPendingSet rate rewards C_star C_h r.input.time z =
          ReferencePhysicalReleaseQuota.pendingSet M r := by
  intro s
  obtain ⟨_E, cutoff, _hslots, _hdates, _hcutoff, hlo, hhi, hcut⟩ :=
    postRawKStoppedDate_cutoff rate rewards C_star C_h control0 z hrel
  obtain ⟨hc, a, M, hgate, hstamp, hocc, hread⟩ := raw_release_gate_data rate rewards C_star C_h z hrel
  refine ⟨hc, a, cutoff, M, hlo, hhi, hstamp, ?_, ?_⟩
  · unfold ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore postRawKStoppedRecords
    rw [hgate]
    apply List.filter_congr
    intro r hr
    have hg := (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_support_iff
      rate rewards C_star C_h z r.input.time).mp ⟨r, hr, rfl⟩
    exact decide_eq_decide.mpr (hcut _ hg).symm
  · intro r hr
    obtain ⟨hr, hk⟩ := List.mem_filter.mp hr
    have hk' : postRawKStoppedDate rate rewards C_star C_h r.input.time z := of_decide_eq_true hk
    refine ⟨(hread r hr).1, ?_⟩
    ext i
    rw [postRawKStoppedPendingSet_mem_iff]
    have hp : ReferencePostReplacementCollectionReleaseSupport.postRawKPendingSupport
        rate rewards C_star C_h r.input.time i z ↔
        i ∈ ReferencePhysicalReleaseQuota.pendingSet M r := by
      constructor
      · rintro ⟨u, _hut, hu, hi⟩
        have he := ReferencePostReplacementCollectionReleaseSupport.postRawKOccurrence_unique
          rate rewards C_star C_h u M.sigma z hu hocc
        rw [he, hstamp, (hread r hr).2] at hi
        exact hi
      · intro hi
        exact (ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords_pending_iff
          rate rewards C_star C_h z r.input.time i).mp ⟨r, hr, rfl, M, (hread r hr).1, hi⟩
    simp only [hk', true_and, postRawKStoppedPendingDate, hk'.2.1, hk'.2.2,
      and_true, hp]

/-- Deterministic quota one for the actual clipped gate stream, together with
backward pending persistence and strict-prior zero release/UP/DATA counts.
No service probability or stochastic waiting assertion is an input. -/
theorem postRawKStoppedRecords_quota
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (M : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    let L := postRawKStoppedRecords rate rewards C_star C_h z
    ReferencePhysicalReleaseQuota.releaseCount M L i ≤ 1 ∧
    ReferencePhysicalReleaseQuota.upCount M L i ≤ 1 ∧
    ReferencePhysicalReleaseQuota.dataCount M L i ≤ 1 ∧
    (∀ a c : Fin L.length, a.val < c.val →
      i ∈ ReferencePhysicalReleaseQuota.pendingSet M (L.get c) →
      i ∈ ReferencePhysicalReleaseQuota.pendingSet M (L.get a)) ∧
    (∀ current : Fin L.length, i ∈ ReferencePhysicalReleaseQuota.pendingSet M (L.get current) →
      ReferencePhysicalReleaseQuota.releaseCount M (L.take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.upCount M (L.take current.val) i = 0 ∧
      ReferencePhysicalReleaseQuota.dataCount M (L.take current.val) i = 0) := by
  dsimp only
  by_cases hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z = []
  · simp [postRawKStoppedRecords, hrel, ReferencePhysicalReleaseQuota.releaseCount,
      ReferencePhysicalReleaseQuota.upCount, ReferencePhysicalReleaseQuota.dataCount]
  · obtain ⟨hc, a, cutoff, _payload, _hlo, _hhi, _hstamp, hrecords, _hread⟩ :=
      postRawKStoppedRecords_source rate rewards C_star C_h control0 z hrel
    rw [← hrecords]
    exact ⟨ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_releaseCount_le_one
        rate z rewards C_star C_h hc _ _ rfl _ a cutoff M i,
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_upCount_le_one
        rate z rewards C_star C_h hc _ _ rfl _ a cutoff M i,
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_dataCount_le_one
        rate z rewards C_star C_h hc _ _ rfl _ a cutoff M i,
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_pairwise_pending
        rate z rewards C_star C_h hc _ _ rfl _ a cutoff M i,
      ReferenceLocalReleasePendingHistory.sourceLocalGateRecordsBefore_strict_prior_counts_zero
        rate z rewards C_star C_h hc _ _ rfl _ a cutoff M i⟩

/-- The actual incoming task sets shrink on the same ordered kept phase.
A true supported gate with an empty task set remains a phase date. -/
theorem postRawKStoppedPendingSet_antitone_on_records
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a c : Fin (postRawKStoppedRecords rate rewards C_star C_h z).length)
    (hac : a.val < c.val) :
    postRawKStoppedPendingSet rate rewards C_star C_h
        ((postRawKStoppedRecords rate rewards C_star C_h z).get c).input.time z ⊆
      postRawKStoppedPendingSet rate rewards C_star C_h
        ((postRawKStoppedRecords rate rewards C_star C_h z).get a).input.time z := by
  have hrel : ReferencePostReplacementCollectionReleaseSupport.rawReleaseRecords
      rate rewards C_star C_h z ≠ [] := by
    intro he
    have hc := c.isLt
    simp only [postRawKStoppedRecords, he, List.filter_nil, List.length_nil] at hc
    omega
  obtain ⟨_hc, _birth, _cutoff, M, _hlo, _hhi, _hstamp, _hrecords, hread⟩ :=
    postRawKStoppedRecords_source rate rewards C_star C_h control0 z hrel
  rw [(hread _ (List.get_mem _ c)).2, (hread _ (List.get_mem _ a)).2]
  intro i hi
  exact (postRawKStoppedRecords_quota rate rewards C_star C_h control0 z M i).2.2.2.1
    a c hac hi

/-- Exact empty characterization for both literal phase endpoints. -/
theorem postRawKRelease_empty_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKStoppedSupport rate rewards C_star C_h z = ∅ ↔
      postRawKReleaseSigma rate rewards C_star C_h z = p.T + 1 ∧
      postRawKReleaseTheta rate rewards C_star C_h z = p.T + 1 := by
  constructor
  · exact postRawKRelease_endpoints_empty rate rewards C_star C_h z
  · rintro ⟨hσ, _hθ⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hb := postRawKStoppedSupport_bounds rate rewards C_star C_h z v hv
    have hI := (postRawKRelease_interval rate rewards C_star C_h control0 z).1
    rw [hI, Finset.mem_Ico, hσ] at hv
    omega

section Endpoints

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

theorem postRawKStoppedSupport_adapted (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z : BootstrapPrivateRoundStreams.SourceInput p |
        t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} := by
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
      t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} =
      {z | postRawKStoppedDate rate rewards C_star C_h t z} := by
    ext z
    change (t.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z) ↔
      postRawKStoppedDate rate rewards C_star C_h t z
    rw [postRawKStoppedSupport_mem_iff]
    constructor
    · rintro ⟨u, hu, he⟩
      have hut : u = t := Fin.ext (by omega)
      exact hut ▸ hu
    · intro ht
      exact ⟨t, ht, rfl⟩
  rw [heq]
  exact postRawKStoppedDate_measurable_preRound rate rewards C_star C_h control0 t

/-- For a nonterminal date, the actual start has occurred exactly when
some supported one-based round no later than that date exists. -/
theorem postRawKRelease_sigma_le_iff (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (v : ℕ) (hv : v ≤ p.T) :
    postRawKReleaseSigma rate rewards C_star C_h z ≤ v ↔
      ∃ u : Fin p.T, u.val + 1 ≤ v ∧
        u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z := by
  obtain ⟨hinterval, hlow, horder, hhigh⟩ := postRawKRelease_interval rate rewards C_star C_h control0 z
  constructor
  · intro hstart
    have hne : (postRawKStoppedSupport rate rewards C_star C_h z).Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have he := (postRawKRelease_endpoints_empty rate rewards C_star C_h z hempty).1
      omega
    obtain ⟨w, hw⟩ := hne
    rw [hinterval, Finset.mem_Ico] at hw
    let u : Fin p.T := ⟨postRawKReleaseSigma rate rewards C_star C_h z - 1, by omega⟩
    have hu : u.val + 1 = postRawKReleaseSigma rate rewards C_star C_h z := by dsimp [u]; omega
    refine ⟨u, by omega, ?_⟩
    rw [hinterval, Finset.mem_Ico, hu]
    omega
  · rintro ⟨u, hu, hmem⟩
    rw [hinterval, Finset.mem_Ico] at hmem
    omega

/-- The actual first excluded endpoint has occurred exactly when an earlier
supported round exists and the current one-based date is unsupported. -/
theorem postRawKRelease_theta_le_iff (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (v : ℕ) (hv : v ≤ p.T) :
    postRawKReleaseTheta rate rewards C_star C_h z ≤ v ↔
      (∃ u : Fin p.T, u.val + 1 < v ∧
        u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z) ∧
      v ∉ postRawKStoppedSupport rate rewards C_star C_h z := by
  obtain ⟨hinterval, hlow, horder, hhigh⟩ := postRawKRelease_interval rate rewards C_star C_h control0 z
  constructor
  · intro hend
    have hne : (postRawKStoppedSupport rate rewards C_star C_h z).Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      have he := (postRawKRelease_endpoints_empty rate rewards C_star C_h z hempty).2
      omega
    obtain ⟨w, hw⟩ := hne
    rw [hinterval, Finset.mem_Ico] at hw
    let u : Fin p.T := ⟨postRawKReleaseSigma rate rewards C_star C_h z - 1, by omega⟩
    have hu : u.val + 1 = postRawKReleaseSigma rate rewards C_star C_h z := by dsimp [u]; omega
    constructor
    · refine ⟨u, by omega, ?_⟩
      rw [hinterval, Finset.mem_Ico, hu]
      omega
    · rw [hinterval, Finset.mem_Ico]
      omega
  · rintro ⟨⟨u, hu, hmem⟩, hnot⟩
    rw [hinterval, Finset.mem_Ico] at hmem hnot
    omega

private theorem stopped_supported_before_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (v : ℕ) (strict : Bool) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 v]
      {z : BootstrapPrivateRoundStreams.SourceInput p | ∃ u : Fin p.T,
        (if strict then u.val + 1 < v else u.val + 1 ≤ v) ∧
        u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} := by
  let : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 v
  have heq : {z : BootstrapPrivateRoundStreams.SourceInput p | ∃ u : Fin p.T,
        (if strict then u.val + 1 < v else u.val + 1 ≤ v) ∧
        u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} =
      ⋃ u : Fin p.T, if (if strict then u.val + 1 < v else u.val + 1 ≤ v) then
        {z : BootstrapPrivateRoundStreams.SourceInput p |
          u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} else ∅ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, hm⟩
      refine ⟨u, ?_⟩
      rw [ite_eq_left hu]
      exact hm
    · rintro ⟨u, hu⟩
      by_cases h : if strict then u.val + 1 < v else u.val + 1 ≤ v
      · rw [ite_eq_left h] at hu
        exact ⟨u, h, hu⟩
      · rw [ite_eq_right h] at hu
        exact hu.elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : if strict then u.val + 1 < v else u.val + 1 ≤ v
  · rw [ite_eq_left hu]
    have hle : u.val + 1 ≤ v := by
      cases strict with
      | false => exact hu
      | true => exact Nat.le_of_lt hu
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono hle _
      (postRawKStoppedSupport_adapted rate rewards C_star C_h control0 u)
  · rw [ite_eq_right hu]
    exact MeasurableSet.empty

/-- The endpoint module's actual start is a stopping time for the original
source-prefix filtration, including empty and terminal release phases. -/
theorem postRawKRelease_sigma_stopping (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (postRawKReleaseSigma rate rewards C_star C_h) := by
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKReleaseSigma rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hlow := (postRawKRelease_interval rate rewards C_star C_h control0 z).2.1
      omega
    rw [heq]
    exact @MeasurableSet.empty (BootstrapPrivateRoundStreams.SourceInput p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 0)
  by_cases hv : v ≤ p.T
  · have heq : {z : BootstrapPrivateRoundStreams.SourceInput p | postRawKReleaseSigma rate rewards C_star C_h z ≤ v} =
        {z : BootstrapPrivateRoundStreams.SourceInput p | ∃ u : Fin p.T, u.val + 1 ≤ v ∧
          u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} := by
      ext z
      exact postRawKRelease_sigma_le_iff rate rewards C_star C_h control0 z v hv
    rw [heq]
    exact stopped_supported_before_measurable rate rewards C_star C_h control0 v false
  · have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKReleaseSigma rate rewards C_star C_h z ≤ v} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      obtain ⟨_, _, horder, hhigh⟩ := postRawKRelease_interval rate rewards C_star C_h control0 z
      omega
    rw [heq]
    exact MeasurableSet.univ

/-- The endpoint module's actual end is a stopping time. Unsupported dates
after all followers released remain governed by the actual gate interval. -/
theorem postRawKRelease_theta_stopping (control0 : ContinuousLearningRows.TimeControl p) :
    PhaseServiceWaiting.IsPreRoundStoppingTime
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0)
      (postRawKReleaseTheta rate rewards C_star C_h) := by
  intro v
  by_cases hv0 : v = 0
  · subst v
    have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKReleaseTheta rate rewards C_star C_h z ≤ 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      obtain ⟨_, hlow, horder, _⟩ := postRawKRelease_interval rate rewards C_star C_h control0 z
      omega
    rw [heq]
    exact @MeasurableSet.empty (BootstrapPrivateRoundStreams.SourceInput p)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 0)
  by_cases hv : v ≤ p.T
  · let current : Fin p.T := ⟨v - 1, by omega⟩
    have hcurrent : current.val + 1 = v := by dsimp [current]; omega
    have heq : {z : BootstrapPrivateRoundStreams.SourceInput p | postRawKReleaseTheta rate rewards C_star C_h z ≤ v} =
        {z : BootstrapPrivateRoundStreams.SourceInput p | ∃ u : Fin p.T, u.val + 1 < v ∧
          u.val + 1 ∈ postRawKStoppedSupport rate rewards C_star C_h z} ∩
        {z : BootstrapPrivateRoundStreams.SourceInput p | v ∈ postRawKStoppedSupport rate rewards C_star C_h z}ᶜ := by
      ext z
      exact postRawKRelease_theta_le_iff rate rewards C_star C_h control0 z v hv
    rw [heq]
    have hm := postRawKStoppedSupport_adapted rate rewards C_star C_h control0 current
    rw [hcurrent] at hm
    exact (stopped_supported_before_measurable rate rewards C_star C_h control0 v true).inter hm.compl
  · have heq : {z : BootstrapPrivateRoundStreams.SourceInput p |
        postRawKReleaseTheta rate rewards C_star C_h z ≤ v} = Set.univ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      have hhigh := (postRawKRelease_interval rate rewards C_star C_h control0 z).2.2.2
      omega
    rw [heq]
    exact MeasurableSet.univ


end Endpoints

end Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation

end
