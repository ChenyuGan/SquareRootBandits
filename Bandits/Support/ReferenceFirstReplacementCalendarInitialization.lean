/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionNextStartNumericalSeed
public import Bandits.Support.ReferenceFirstCollectionOldPrefixCalendarReadout
public import Bandits.Support.ReferenceCorrectedSuccessorOutsideNumericalStep

import Lean.Elab.Tactic.Omega

/-!
# First replacement calendar initialization

This module joins the actual first-call source prefix to the native numerical
seed and its actual later installation. The source prefix retains every
original suffix slot, including disabled rounds and zero-arrival rounds.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCompletePhysicalHistory (completeSuffixRecords physicalStart)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
open ReferenceCollectionPhaseHistory (laterChosen)

namespace Bandits.Support.ReferenceFirstReplacementCalendarInitialization

variable {p : Parameters}

/-- The original armwise calendar word used by the numerical replay. -/
def rawCalendar (rate : ReferenceActivePhysicalStep.RateInput p)
    (a : Fin p.K) (P : List (RecordedQueueRun.RoundInput p.K)) :
    List (Bool × ℕ) :=
  P.map fun c => (c.enabled,
    RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)

/-- Native queue replay at one arm of a strict prefix of the same calendar. -/
def calendarReplay (rate : ReferenceActivePhysicalStep.RateInput p)
    (a : Fin p.K) (P : List (RecordedQueueRun.RoundInput p.K)) (h : ℕ) :
    ℕ × ℕ :=
  QueueReplay.replay (4 * rate.n) (0, 0) (rawCalendar rate a (P.take h))

private theorem map_some_mapM {α : Type*} (xs : List α) :
    (xs.map some).mapM id = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

private theorem sourceCell_congr
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (lc rc : ReferenceCollectionSegmentExtraction.Choice rate)
    (rewards : GridRewardTable p)
    (lv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput left.output.preparation
        lc.payload lc.started lc.weights))
    (rv : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput right.output.preparation
        rc.payload rc.started rc.weights))
    (he : left = right) (hc : lc = rc) :
    ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate left lc rewards lv =
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate right rc rewards rv := by
  cases he
  cases hc
  rfl

private theorem firstCell_covered_calendar_word
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (s : ℕ)
    (R : List (ReferenceCompletePhysicalHistory.RoundRecord p rate))
    (P0 : List (RecordedQueueRun.RoundInput p.K))
    (hbound : P0.length ≤ R.length)
    (hR : ∀ k : Fin P0.length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        R[k.val]? = some r ∧ r.input.time.val = s + k.val ∧
          cell0 rate r = some P0[k.val])
    (h : ℕ) (hh : h ≤ P0.length) :
    (R.take h).map (cell0 rate) = (P0.take h).map some := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_map]
    rw [Nat.min_eq_left (by omega : h ≤ R.length), Nat.min_eq_left hh]
  · intro k hkL hkR
    have hk : k < h := by
      simpa only [List.length_map, List.length_take,
        Nat.min_eq_left (by omega : h ≤ R.length)] using hkL
    have hkP0 : k < P0.length := lt_of_lt_of_le hk hh
    obtain ⟨r, hr, _, hcell⟩ := hR ⟨k, hkP0⟩
    have hr' : R[k]'(by omega) = r :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hr)
    simp only [List.getElem_map, List.getElem_take]
    rw [hr']
    exact hcell

private theorem initializedStream_ledgerAt_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (left right : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (hwindow : left.window = right.window)
    (i : ℕ) (hiLeft : i < left.ell) (hiRight : i < right.ell) :
    left.ledgers ⟨i, hiLeft⟩ = right.ledgers ⟨i, hiRight⟩ := by
  obtain ⟨leftRecord, hleftRecord, _, hleftNext, _, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput.output_properties
      left ⟨i, hiLeft⟩
  obtain ⟨rightRecord, hrightRecord, _, hrightNext, _, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput.output_properties
      right ⟨i, hiRight⟩
  have hrightOnLeft : left.window[i]? = some rightRecord := by
    rw [hwindow]
    exact hrightRecord
  have hrecord : leftRecord = rightRecord :=
    Option.some.inj (hleftRecord.symm.trans hrightOnLeft)
  have hconfiguration :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          left.payload (left.ledgers ⟨i, hiLeft⟩) left.saved =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.collection
          right.payload (right.ledgers ⟨i, hiRight⟩) right.saved := by
    calc
      _ = leftRecord.output.next.coordinator := hleftNext.symm
      _ = rightRecord.output.next.coordinator :=
        congrArg (fun r => r.output.next.coordinator) hrecord
      _ = _ := hrightNext
  exact
    (ReferenceActivePhysicalStep.CoordinatorConfiguration.collection.inj
      hconfiguration).2.1

private theorem initializedStream_firstEmpty_length_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (left right : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (hwindow : left.stream.window = right.stream.window)
    (hleftEmpty : left.ledger.pending = ∅) :
    left.stream.ell = right.stream.ell := by
  have hleftLastEmpty : (left.stream.ledgers left.last).pending = ∅ := by
    rw [← left.ledgerIsLast]
    exact hleftEmpty
  cases hrightOutcome : right.outcome with
  | exhausted hpending hwindowExhausted _ _ _ =>
      have hleftLe : left.stream.ell ≤ right.stream.ell := by
        calc
          left.stream.ell ≤ left.stream.window.length := left.stream.withinWindow
          _ = right.stream.window.length := congrArg List.length hwindow
          _ = right.stream.ell := hwindowExhausted.symm
      by_contra hne
      have hlt : left.stream.ell < right.stream.ell := by omega
      let iRight : Fin right.stream.ell :=
        ⟨left.last.val, by have h := left.last.isLt; omega⟩
      have hbefore : iRight.val + 1 < right.stream.ell := by
        change left.last.val + 1 < right.stream.ell
        omega
      have hnonempty := right.allEarlierNonempty iRight hbefore
      have hledger := initializedStream_ledgerAt_eq rate source rewards C_star C_h
        count hcross hspan hshort left.stream right.stream hwindow
        left.last.val left.last.isLt iRight.isLt
      have hleftIndex :
          left.stream.ledgers left.last =
            left.stream.ledgers ⟨left.last.val, left.last.isLt⟩ := by
        congr 1
      have hrightEmpty : (right.stream.ledgers iRight).pending = ∅ := by
        rw [← hledger, ← hleftIndex]
        exact hleftLastEmpty
      exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hrightEmpty)
  | empty data =>
      have hrightLastEmpty : (right.stream.ledgers right.last).pending = ∅ := by
        rw [← right.ledgerIsLast]
        exact data.pendingEmpty
      by_cases hltLR : left.stream.ell < right.stream.ell
      · let iRight : Fin right.stream.ell :=
          ⟨left.last.val, by have h := left.last.isLt; omega⟩
        have hbefore : iRight.val + 1 < right.stream.ell := by
          change left.last.val + 1 < right.stream.ell
          omega
        have hnonempty := right.allEarlierNonempty iRight hbefore
        have hledger := initializedStream_ledgerAt_eq rate source rewards C_star C_h
          count hcross hspan hshort left.stream right.stream hwindow
          left.last.val left.last.isLt iRight.isLt
        have hleftIndex :
            left.stream.ledgers left.last =
              left.stream.ledgers ⟨left.last.val, left.last.isLt⟩ := by
          congr 1
        have hrightEmpty : (right.stream.ledgers iRight).pending = ∅ := by
          rw [← hledger, ← hleftIndex]
          exact hleftLastEmpty
        exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hrightEmpty)
      · by_cases hltRL : right.stream.ell < left.stream.ell
        · let iLeft : Fin left.stream.ell :=
            ⟨right.last.val, by have h := right.last.isLt; omega⟩
          have hbefore : iLeft.val + 1 < left.stream.ell := by
            change right.last.val + 1 < left.stream.ell
            omega
          have hnonempty := left.allEarlierNonempty iLeft hbefore
          have hledger := initializedStream_ledgerAt_eq rate source rewards C_star C_h
            count hcross hspan hshort left.stream right.stream hwindow
            right.last.val iLeft.isLt right.last.isLt
          have hrightIndex :
              right.stream.ledgers right.last =
                right.stream.ledgers ⟨right.last.val, right.last.isLt⟩ := by
            congr 1
          have hleftEmptyAt : (left.stream.ledgers iLeft).pending = ∅ := by
            rw [hledger, ← hrightIndex]
            exact hrightLastEmpty
          exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hleftEmptyAt)
        · omega

private theorem initializedStream_record_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (left right : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (hwindow : left.stream.window = right.stream.window)
    (hell : left.stream.ell = right.stream.ell) :
    left.record = right.record := by
  have hlast : left.last.val = right.last.val := by
    have hl := left.lastIsLast
    have hr := right.lastIsLast
    omega
  apply Option.some.inj
  calc
    some left.record = left.stream.window[left.last.val]? := left.recordAt.symm
    _ = right.stream.window[right.last.val]? := by rw [hwindow, hlast]
    _ = some right.record := right.recordAt

private theorem collectionReadout_zero_of_positiveStart
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K)
    (hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record =
      some cell) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
  classical
  have hdomain := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s record).mp
    (by rw [hreadout]; rfl)
  obtain ⟨hf, hbranch⟩ := hdomain
  cases hcoord : record.output.preparation.coordinator with
  | first outcome => simp [hcoord] at hbranch
  | invalidCollectionCutoff => simp [hcoord] at hbranch
  | dagger => simp [hcoord] at hbranch
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot hvalid hscores =>
          simpa [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            hf, hcoord] using hreadout
      | _ => simp [hcoord] at hbranch
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinitialized hcandidate hdomain'
          hclock hpending hnoAssignment selection =>
          have hs : s < registers.payload.sigma.val := by simpa [hcoord] using hbranch
          have hzero : 0 < registers.payload.sigma.val := by omega
          simpa [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            hf, hcoord, hs, hzero] using hreadout
      | _ => simp [hcoord] at hbranch

private theorem initializedStream_suffix_words_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (start : ℕ)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count)
    (left right : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort)
    (leftCells rightCells : List (RecordedQueueRun.RoundInput p.K))
    (hwindow : left.stream.window = right.stream.window)
    (hell : left.stream.ell = right.stream.ell)
    (hleftLength : leftCells.length = left.stream.ell)
    (hrightLength : rightCells.length = right.stream.ell)
    (hzero : leftCells[0]? = rightCells[0]?)
    (hleft : ∀ i : Fin left.stream.ell, 0 < i.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (left.stream.window[i.val]'(lt_of_lt_of_le i.isLt left.stream.withinWindow)) =
          some (leftCells[i.val]'(by rw [hleftLength]; exact i.isLt)))
    (hright : ∀ i : Fin right.stream.ell, 0 < i.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout start
        (right.stream.window[i.val]'(lt_of_lt_of_le i.isLt right.stream.withinWindow)) =
          some (rightCells[i.val]'(by rw [hrightLength]; exact i.isLt))) :
    leftCells = rightCells := by
  apply List.ext_getElem
  · simp only [hleftLength, hrightLength, hell]
  · intro k hkl hkr
    have hkLeft : k < left.stream.ell := by simpa [hleftLength] using hkl
    have hkRight : k < right.stream.ell := by simpa [hrightLength] using hkr
    by_cases hk0 : k = 0
    · subst k
      have hopt :
          some (leftCells[0]'(by simpa [hleftLength] using hkLeft)) =
            some (rightCells[0]'(by simpa [hrightLength] using hkRight)) := by
        calc
          some (leftCells[0]'(by simpa [hleftLength] using hkLeft)) = leftCells[0]? :=
            (List.getElem?_eq_getElem (by simpa [hleftLength] using hkLeft)).symm
          _ = rightCells[0]? := hzero
          _ = some (rightCells[0]'(by simpa [hrightLength] using hkRight)) :=
            List.getElem?_eq_getElem (by simpa [hrightLength] using hkRight)
      exact Option.some.inj hopt
    · let iLeft : Fin left.stream.ell := ⟨k, hkLeft⟩
      let iRight : Fin right.stream.ell := ⟨k, hkRight⟩
      have hrec :
          left.stream.window[k]'(lt_of_lt_of_le hkLeft left.stream.withinWindow) =
            right.stream.window[k]'(lt_of_lt_of_le hkRight right.stream.withinWindow) := by
        apply Option.some.inj
        calc
          some (left.stream.window[k]'(lt_of_lt_of_le hkLeft left.stream.withinWindow)) =
              left.stream.window[k]? :=
            (List.getElem?_eq_getElem (lt_of_lt_of_le hkLeft left.stream.withinWindow)).symm
          _ = right.stream.window[k]? := congrArg (fun xs => xs[k]?) hwindow
          _ = some (right.stream.window[k]'(lt_of_lt_of_le hkRight right.stream.withinWindow)) :=
            List.getElem?_eq_getElem (lt_of_lt_of_le hkRight right.stream.withinWindow)
      have hposLeft : 0 < iLeft.val := by simp [iLeft]; omega
      have hposRight : 0 < iRight.val := by simp [iRight]; omega
      have hreadLeft := hleft iLeft hposLeft
      have hreadRight := collectionReadout_zero_of_positiveStart rate start
        (right.stream.window[k]'(lt_of_lt_of_le hkRight right.stream.withinWindow))
        (rightCells[k]'(by simpa [hrightLength] using hkRight))
        (hright iRight hposRight)
      rw [hrec] at hreadLeft
      exact Option.some.inj (hreadLeft.symm.trans hreadRight)
/-- The first-cell event determines one complete, literal calendar prefix.
Every shorter boundary, including zero and the invocation date, reads the
corresponding `take` of this same word through the source-facing prefix API. -/
theorem firstCell_initial_calendar_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = t.val - physicalStart rate z rewards C_star C_h ∧
    ((completeSuffixRecords rate z rewards C_star C_h).take P0.length).map
        (cell0 rate) = P0.map some ∧
      (∀ h, h ≤ P0.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
            (physicalStart rate z rewards C_star C_h + h) z = some (P0.take h)) := by
  obtain ⟨hc, _hspan, _hshort, _f, _head, _valid, _D, L,
    _hsu, _hut, _hu, _htotal, _hpending, _hrecord, _hchoice, _hDlen,
    _hDzero, _hDread, _hLD, _hPast, hlen, hcoverage, _hprefix, _hsplit,
    _hstart⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_prefix_at_boundary
      rate rewards C_star C_h u t z hz
  have hRlen :
      (completeSuffixRecords rate z rewards C_star C_h).length =
        p.T - physicalStart rate z rewards C_star C_h :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
  have hbound : L.length ≤
      (completeSuffixRecords rate z rewards C_star C_h).length := by
    rw [hRlen, hlen]
    omega
  refine ⟨L, hlen, ?_, ?_⟩
  · simpa only [List.take_length] using
      firstCell_covered_calendar_word rate
        (physicalStart rate z rewards C_star C_h)
        (completeSuffixRecords rate z rewards C_star C_h) L hbound hcoverage
        L.length le_rfl
  · intro h hh
    have hlaunch :
        ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h
            (physicalStart rate z rewards C_star C_h + h) z := by
      exact ⟨hc, by omega⟩
    have hmap := firstCell_covered_calendar_word rate
      (physicalStart rate z rewards C_star C_h)
      (completeSuffixRecords rate z rewards C_star C_h) L hbound hcoverage h hh
    have hsub :
        (physicalStart rate z rewards C_star C_h + h) -
          physicalStart rate z rewards C_star C_h = h := by omega
    unfold ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
    rw [ite_eq_left hlaunch, hsub]
    rw [hmap]
    exact map_some_mapM (L.take h)

/-- The original first-call prefix is the very same list as the initialized
stream's native source cells followed by its actual collection suffix. The
accepted numerical endpoint is retained as a conclusion, and the identification
is proved for each of its actual stream witnesses. -/
theorem firstCell_initial_calendar_matches_native_stream
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = t.val - physicalStart rate z rewards C_star C_h ∧
      ((completeSuffixRecords rate z rewards C_star C_h).take P0.length).map
        (cell0 rate) = P0.map some ∧
      (∀ h, h ≤ P0.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h
            (physicalStart rate z rewards C_star C_h + h) z = some (P0.take h)) ∧
      (∃ hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
        ∃ hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
          z rewards C_star C_h + (p.T - physicalStart rate z rewards C_star C_h) ≤ p.T,
        ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hc (p.T - physicalStart rate z rewards C_star C_h) hspan).records).length <
              (p.T - physicalStart rate z rewards C_star C_h),
          ∀ (d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
              (p := p) (rate := rate) z rewards C_star C_h
              (p.T - physicalStart rate z rewards C_star C_h) hc hspan hshort)
            (head : ReferenceCollectionSegmentExtraction.Choice rate)
            (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
              (ReferenceActivePhysicalStep.collectionRecordingInput
                d.stream.cutoff.cut.output.preparation head.payload head.started head.weights))
            (D : List (RecordedQueueRun.RoundInput p.K)),
            ReferenceCollectionSegmentExtraction.choice d.stream.cutoff.cut.input = some head →
            ∀ hDlen : D.length = d.stream.ell,
            (D[0]'(by rw [hDlen]; exact lt_of_lt_of_le Nat.zero_lt_one d.stream.positiveLength) =
              ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
                rate d.stream.cutoff.cut head rewards valid) →
            (∀ i : Fin d.stream.ell, 0 < i.val →
              (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
                (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                  z rewards C_star C_h)
                (d.stream.window[i.val]'(lt_of_lt_of_le i.isLt d.stream.withinWindow)) =
                  some (D[i.val]'(by rw [hDlen]; exact i.isLt)))) →
            P0 = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
              hc (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D)) := by
  classical
  obtain ⟨P0, hP0len, hP0map, hP0prefix⟩ :=
    firstCell_initial_calendar_prefix rate rewards C_star C_h u t z hz
  obtain ⟨hc, hspan, hshort, f, oldHead, oldValid, oldD, L,
      _hsu, _hut, _hu, _htotal, hpending, _hrecord, oldChoice, oldDlen,
      oldDzero, oldDread, hLD, _hPast, hlen, oldCoverage, _hPrefix,
      _hsplit, _hstart⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_prefix_at_boundary
      rate rewards C_star C_h u t z hz
  have hRlen :
      (completeSuffixRecords rate z rewards C_star C_h).length =
        p.T - physicalStart rate z rewards C_star C_h :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
  have hbound : L.length ≤
      (completeSuffixRecords rate z rewards C_star C_h).length := by
    rw [hRlen, hlen]
    omega
  have hLmap :
      ((completeSuffixRecords rate z rewards C_star C_h).take L.length).map (cell0 rate) =
        L.map some := by
    simpa only [List.take_length] using
      firstCell_covered_calendar_word rate
        (physicalStart rate z rewards C_star C_h)
        (completeSuffixRecords rate z rewards C_star C_h) L hbound oldCoverage
        L.length le_rfl
  have hmapEq : P0.map some = L.map some := by
    calc
      P0.map some =
          ((completeSuffixRecords rate z rewards C_star C_h).take P0.length).map (cell0 rate) :=
        hP0map.symm
      _ = ((completeSuffixRecords rate z rewards C_star C_h).take L.length).map (cell0 rate) := by
        rw [hP0len, hlen]
      _ = L.map some := hLmap
  have hPL : P0 = L := by
    have hinj : Function.Injective (fun c : RecordedQueueRun.RoundInput p.K => some c) := by
      intro a b h
      exact Option.some.inj h
    exact hinj.list_map hmapEq
  refine ⟨P0, hP0len, hP0map, hP0prefix, ⟨hc, hspan, hshort, ?_⟩⟩
  intro d head valid D hchoice hDlen hseedZero hread
  have hwindow : f.stream.window = d.stream.window := by
    calc
      f.stream.window = ReferenceFirstCollectionReadyStream.actualWindow
          (rate := rate) z rewards C_star C_h hc
            (p.T - physicalStart rate z rewards C_star C_h) hspan :=
        f.stream.windowIsActual
      _ = d.stream.window := d.stream.windowIsActual.symm
  have hell := initializedStream_firstEmpty_length_eq
    rate z rewards C_star C_h
      (p.T - physicalStart rate z rewards C_star C_h) hc hspan hshort
      f d hwindow hpending
  have hleft : ∀ i : Fin f.stream.ell, 0 < i.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (f.stream.window[i.val]'(lt_of_lt_of_le i.isLt f.stream.withinWindow)) =
          some (oldD[i.val]'(by rw [oldDlen]; exact i.isLt)) := by
    intro i hi
    calc
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (f.stream.window[i.val]'(lt_of_lt_of_le i.isLt f.stream.withinWindow)) =
        oldD[i.val]? := oldDread i
      _ = some (oldD[i.val]'(by rw [oldDlen]; exact i.isLt)) :=
        List.getElem?_eq_getElem (by rw [oldDlen]; exact i.isLt)
  have hzeroright : D[0]? = some
      (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate d.stream.cutoff.cut head rewards valid) := by
    have hD0 : 0 < D.length := by
      rw [hDlen]
      exact lt_of_lt_of_le Nat.zero_lt_one d.stream.positiveLength
    rw [List.getElem?_eq_getElem hD0]
    exact congrArg some hseedZero
  have hcut : f.stream.cutoff.cut = d.stream.cutoff.cut := by
    apply Option.some.inj
    have hleftCut : f.stream.window[0]? = some f.stream.cutoff.cut := by
      have hpos : 0 < f.stream.window.length := f.stream.windowNonempty
      rw [List.getElem?_eq_getElem hpos]
      exact congrArg some f.stream.cutoffIsHead
    have hrightCut : d.stream.window[0]? = some d.stream.cutoff.cut := by
      have hpos : 0 < d.stream.window.length := d.stream.windowNonempty
      rw [List.getElem?_eq_getElem hpos]
      exact congrArg some d.stream.cutoffIsHead
    calc
      some f.stream.cutoff.cut = f.stream.window[0]? := hleftCut.symm
      _ = d.stream.window[0]? := congrArg (fun xs => xs[0]?) hwindow
      _ = some d.stream.cutoff.cut := hrightCut
  have hhead : oldHead = head := by
    apply Option.some.inj
    calc
      some oldHead = ReferenceCollectionSegmentExtraction.choice f.stream.cutoff.cut.input := oldChoice.symm
      _ = ReferenceCollectionSegmentExtraction.choice d.stream.cutoff.cut.input := by rw [hcut]
      _ = some head := hchoice
  have hcell :
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate f.stream.cutoff.cut oldHead rewards oldValid =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate d.stream.cutoff.cut head rewards valid := by
    exact sourceCell_congr rate f.stream.cutoff.cut d.stream.cutoff.cut
      oldHead head rewards oldValid valid hcut hhead
  have hzero : oldD[0]? = D[0]? := by
    calc
      oldD[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate f.stream.cutoff.cut oldHead rewards oldValid) := oldDzero
      _ = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate d.stream.cutoff.cut head rewards valid) := congrArg some hcell
      _ = D[0]? := hzeroright.symm
  have hreadright : ∀ i : Fin d.stream.ell, 0 < i.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h)
        (d.stream.window[i.val]'(lt_of_lt_of_le i.isLt d.stream.withinWindow)) =
          some (D[i.val]'(by rw [hDlen]; exact i.isLt)) := hread
  have hDword := initializedStream_suffix_words_eq
    rate (ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h)
      z rewards C_star C_h (p.T - physicalStart rate z rewards C_star C_h)
      hc hspan hshort f d oldD D hwindow hell oldDlen
      hDlen hzero hleft hreadright
  have hword : P0 =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h hc
        (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D := by
    calc
      P0 = L := hPL
      _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h hc
            (p.T - physicalStart rate z rewards C_star C_h) hspan ++ oldD := by simpa using hLD
      _ = ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h hc
            (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D := by rw [hDword]
  exact hword
/-- Extract the native numerical stream itself, with its complete suffix word
identified as the same original calendar prefix. -/
theorem firstCell_initial_calendar_native_output
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = t.val - physicalStart rate z rewards C_star C_h ∧
      ((completeSuffixRecords rate z rewards C_star C_h).take P0.length).map
        (cell0 rate) = P0.map some ∧
      (∀ h, h ≤ P0.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h)) ∧
      ∃ hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
      ∃ hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
          z rewards C_star C_h + (p.T - physicalStart rate z rewards C_star C_h) ≤ p.T,
      ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
            z rewards C_star C_h hc (p.T - physicalStart rate z rewards C_star C_h) hspan).records).length <
              (p.T - physicalStart rate z rewards C_star C_h),
      ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
          (p := p) (rate := rate) z rewards C_star C_h
          (p.T - physicalStart rate z rewards C_star C_h) hc hspan hshort,
      ∃ head : ReferenceCollectionSegmentExtraction.Choice rate,
      ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
      ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput
          d.stream.cutoff.cut.output.preparation head.payload head.started head.weights),
      ∃ D : List (RecordedQueueRun.RoundInput p.K),
        ReferenceCollectionSegmentExtraction.choice d.stream.cutoff.cut.input = some head ∧
        head.payload = d.stream.payload ∧
        head.initializer = some initializer ∧
        initializer.checkedStart rate = .success head.preLedger ∧
        ∃ hDlen : D.length = d.stream.ell,
          D[0]'(by rw [hDlen]; exact lt_of_lt_of_le Nat.zero_lt_one d.stream.positiveLength) =
            ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
              rate d.stream.cutoff.cut head rewards valid ∧
          (∀ i : Fin d.stream.ell, 0 < i.val →
            ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
              (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
                z rewards C_star C_h)
              (d.stream.window[i.val]'(lt_of_lt_of_le i.isLt d.stream.withinWindow)) =
                some (D[i.val]'(by rw [hDlen]; exact i.isLt))) ∧
          (∀ h, h ≤ d.stream.ell → ∀ a : Fin p.K,
            (d.stream.window.take h).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger a) =
              ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a (D.take h)) ∧
          P0 = (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
            hc (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D) ∧
          (∀ a : Fin p.K, rawCalendar rate a P0 =
            ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
              (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
                hc (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D)) := by
  classical
  obtain ⟨P0, hP0len, hP0map, hP0prefix, ⟨hc, hspan, hshort, hsameWord⟩⟩ :=
    firstCell_initial_calendar_matches_native_stream rate rewards C_star C_h u t z hz
  have hseed :=
    ReferenceFirstCollectionNextStartNumericalSeed.actual_initialized_first_collection_classified_next_start_numerical_seed
      rate z rewards C_star C_h hc
      (p.T - physicalStart rate z rewards C_star C_h) hspan hshort
  obtain ⟨d, head, initializer, valid, D, hchoice, hpay, hinit, hchecked,
      hDlen, hzero, hcells, hqueuePrefix, _hledgerPrefix, _hfinal⟩ := hseed
  have hread : ∀ i : Fin d.stream.ell, 0 < i.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h)
        (d.stream.window[i.val]'(lt_of_lt_of_le i.isLt d.stream.withinWindow)) =
          some (D[i.val]'(by rw [hDlen]; exact i.isLt)) := by
    intro i hi
    obtain ⟨call, validCall, hchoiceCall, hcallPayload, hcontext, hcell, hrows,
      hselected, hrewards, htime, henabled, hreward, hrate, hraw, hread⟩ := hcells i
    exact hread hi
  have hword := hsameWord d head valid D hchoice hDlen hzero hread
  have hraw : ∀ a : Fin p.K, rawCalendar rate a P0 =
      ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
          hc (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D) := by
    intro a
    rw [hword]
    rfl
  exact ⟨P0, hP0len, hP0map, hP0prefix, hc, hspan, hshort,
    d, head, initializer, valid, D, hchoice, hpay, hinit, hchecked,
    hDlen, hzero, hread, hqueuePrefix, hword, hraw⟩

/-- Literal equations at the queried record's actual later installation.
This predicate is used only as an output: its constructor equality identifies
all numerical fields with the same physical dispatch and successful start. -/
def initializes_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (P0 : List (RecordedQueueRun.RoundInput p.K))
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T),
    r.input.state.coordinator = .collection payload ledger saved ∧
    ledger.pending = ∅ ∧ cutoff.val + 1 = ledger.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock cutoff
    ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (hstart : CoordinatorPhaseClock.startRound p rate.eta.val r.input.time
        input.clock ledger.pending = .ok started)
      (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
      (hassignment : started.assignmentStart = some instruction),
      instruction.time = r.input.time ∧
      let operation := CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
      ∃ (consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operation)
        (output : LaterAssignmentStartOperation.SuccessfulStart input.payload operation instruction input.row)
        (hlocal : output.localConsistency = consistent)
        (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
        (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
        (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload started
          instruction.time installed.registers.complementWeights input.row),
        installed = CoordinatorAssignmentRegisterInstall.installLater output clockData ∧
        LaterAssignmentStartOperation.laterAssignmentStart input.payload operation instruction
          input.row consistent = .success output hlocal ∧
        CoordinatorRoundDispatch.dispatchCollection input =
          .laterChosen core consistent started hstart instruction hassignment output hlocal
            clockData installed selected ∧
        r.output.preparation.coordinator =
          .collection payload ledger clock cutoff
            (.laterChosen core consistent started hstart instruction hassignment output hlocal
              clockData installed selected) ∧
        installed.registers.payload = output.payload ∧
        installed.registers.payload.sigma = r.input.time ∧
        installed.assignmentVector = output.assignmentVector ∧
        installed.reconstruction = output.reconstruction ∧
        (∀ a : Fin p.K,
          AssignmentScoreReconstruction.sourceScore output.reconstruction a =
            (calendarReplay rate a P0 P0.length).1 ∧
          AssignmentScoreReconstruction.initialQueue output.reconstruction a =
            (calendarReplay rate a P0 P0.length).2 ∧
          output.payload.queues a = (calendarReplay rate a P0 P0.length).2 ∧
          installed.registers.payload.queues a = (calendarReplay rate a P0 P0.length).2 ∧
          output.reconstruction.registers.current a =
            ⟨(calendarReplay rate a P0 P0.length).2,
              (calendarReplay rate a P0 P0.length).1 -
                (calendarReplay rate a P0 (P0.length - 1)).1⟩) ∧
        (∀ i : Fin (p.m - 1),
          installed.registers.payload.assignment.assigned i = output.payload.assignment.assigned i ∧
          installed.retainedBaseScore i =
            (calendarReplay rate (installed.registers.payload.assignment.assigned i) P0 P0.length).1 ∧
          (installed.registers.payload.downRecord i).val.q =
            (calendarReplay rate (installed.registers.payload.assignment.assigned i) P0 P0.length).2) ∧
        (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
          installed.registers.complementScores j = (calendarReplay rate j.val P0 P0.length).1 ∧
          installed.ownedRegisters.queue j = (calendarReplay rate j.val P0 P0.length).2 ∧
          installed.ownedRegisters.previousService j =
            (calendarReplay rate j.val P0 P0.length).1 -
              (calendarReplay rate j.val P0 (P0.length - 1)).1) ∧
        (instruction.kind = .corrected →
          AssignmentScoreReconstruction.previousScore output.reconstruction =
            some (fun a => (output.reconstruction.registers.cutoff a).score -
              (output.reconstruction.registers.cutoff a).lastService)) ∧
        (instruction.kind = .renewal →
          AssignmentScoreReconstruction.previousScore output.reconstruction = none ∧
          AssignmentScoreReconstruction.previousWeight output.reconstruction = none)

private theorem take_before_last_append {α : Type*} (A D : List α)
    (hD : 0 < D.length) :
    (A ++ D).take ((A ++ D).length - 1) = A ++ D.take (D.length - 1) := by
  rw [List.length_append, List.take_append]
  have hA : A.length ≤ A.length + D.length - 1 := by omega
  rw [List.take_of_length_le hA]
  congr 2
  omega

private theorem record_eq_step
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    r = { input := r.input, output := ReferenceActivePhysicalStep.step r.input, output_eq := rfl } := by
  obtain ⟨input, output, houtput⟩ := r
  cases houtput
  rfl

/-- Numerical initialization at the actual successful first replacement,
corrected or renewal. The strict original prefix excludes the birth round;
no success, coverage or numerical seed is assumed at the root. -/
theorem firstCell_actual_replacement_calendar_initialization
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ P0 : List (RecordedQueueRun.RoundInput p.K),
      P0.length = t.val - physicalStart rate z rewards C_star C_h ∧
      ((completeSuffixRecords rate z rewards C_star C_h).take P0.length).map
        (cell0 rate) = P0.map some ∧
      (∀ h, h ≤ P0.length →
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h (physicalStart rate z rewards C_star C_h + h) z =
            some (P0.take h)) ∧
      ∀ b : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
        physicalStart rate z rewards C_star C_h + b.val = t.val →
        laterChosen (completeSuffixRecords rate z rewards C_star C_h)[b.val].input = true →
        initializes_calendar rate P0 (completeSuffixRecords rate z rewards C_star C_h)[b.val] := by
  classical
  obtain ⟨P0, hP0len, hP0map, hP0prefix, ⟨hc, hspan, hshort, hsameWord⟩⟩ :=
    firstCell_initial_calendar_matches_native_stream rate rewards C_star C_h u t z hz
  obtain ⟨d, head, initializer, valid, D, hchoice, _hpay, _hinit, _hchecked,
      hDlen, hzero, hcells, _hqueuePrefix, _hledgerPrefix, _hfinal, hnextSeed⟩ :=
    ReferenceFirstCollectionNextStartNumericalSeed.actual_initialized_first_collection_classified_next_start_numerical_seed
      rate z rewards C_star C_h hc
      (p.T - physicalStart rate z rewards C_star C_h) hspan hshort
  have hread : ∀ i : Fin d.stream.ell, 0 < i.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceFirstCollectionReadyStream.startTime (rate := rate) z rewards C_star C_h)
        (d.stream.window[i.val]'(lt_of_lt_of_le i.isLt d.stream.withinWindow)) =
          some (D[i.val]'(by rw [hDlen]; exact i.isLt)) := by
    intro i hi
    obtain ⟨call, validCall, _hchoiceCall, _hcallPayload, _hcontext, _hcell, _hrows,
      _hselected, _hrewards, _htime, _henabled, _hreward, _hrate, _hraw, hread⟩ := hcells i
    exact hread hi
  have hword := hsameWord d head valid D hchoice hDlen hzero hread
  obtain ⟨_hc, _hspan, _hshort, f, _oldHead, _oldValid, _oldD, _oldL,
    _hsu, _hut, _hu, htotal, hpending, _hrecord, _oldChoice, _oldDlen,
    _oldDzero, _oldDread, _hLD, _hPast, _hlen, _hcoverage, _hprefix, _hsplit,
    _hstart⟩ :=
    ReferenceFirstCollectionOldPrefixCalendarReadout.firstCell_prefix_at_boundary
      rate rewards C_star C_h u t z hz
  have hwindow : f.stream.window = d.stream.window :=
    f.stream.windowIsActual.trans d.stream.windowIsActual.symm
  have hell := initializedStream_firstEmpty_length_eq rate z rewards C_star C_h
    (p.T - physicalStart rate z rewards C_star C_h) hc hspan hshort f d hwindow hpending
  have hindex : f.last.val < d.stream.ell := by rw [← hell]; exact f.last.isLt
  have hlast : (⟨f.last.val, hindex⟩ : Fin d.stream.ell) = d.last := by
    apply Fin.ext
    have hf := f.lastIsLast
    have hd := d.lastIsLast
    dsimp only
    omega
  have hled := initializedStream_ledgerAt_eq rate z rewards C_star C_h
    (p.T - physicalStart rate z rewards C_star C_h) hc hspan hshort
      f.stream d.stream hwindow f.last.val f.last.isLt hindex
  have hdempty : d.ledger.pending = ∅ := by
    rw [d.ledgerIsLast, ← hlast, ← hled, ← f.ledgerIsLast]
    exact hpending
  let R := completeSuffixRecords rate z rewards C_star C_h
  let E := ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
    hc (p.T - physicalStart rate z rewards C_star C_h) hspan
  have hepoch : R = E.records :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
      rate rewards C_star C_h z hc
  have hrecord : d.stream.window[d.last.val]'(lt_of_lt_of_le d.last.isLt d.stream.withinWindow) =
      d.record :=
    Option.some.inj ((List.getElem?_eq_getElem
      (lt_of_lt_of_le d.last.isLt d.stream.withinWindow)).symm.trans d.recordAt)
  have hdate := (d.stream.alignment
    ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).2
  dsimp only at hdate
  rw [hrecord] at hdate
  change d.record.input.time.val + 1 =
    physicalStart rate z rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length + 1 + d.last.val at hdate
  rw [← hepoch] at hdate
  change physicalStart rate z rewards C_star C_h +
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length + f.stream.ell = t.val at htotal
  have hdateT : d.record.input.time.val + 1 = t.val := by
    have hd := d.lastIsLast
    omega
  have hboundary :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length + d.stream.ell =
        t.val - physicalStart rate z rewards C_star C_h := by
    rw [← hepoch]
    omega
  have hfull : ∀ a, QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
          hc (p.T - physicalStart rate z rewards C_star C_h) hspan ++ D)) =
        calendarReplay rate a P0 P0.length := by
    intro a
    simp only [calendarReplay, List.take_length, hword]
    rfl
  have hprev : ∀ a, QueueReplay.replay (4 * rate.n) (0, 0)
      (ReferenceFirstCollectionAllArmNumericalStream.arrivals rate a
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
          hc (p.T - physicalStart rate z rewards C_star C_h) hspan ++
            D.take (d.stream.ell - 1))) =
        calendarReplay rate a P0 (P0.length - 1) := by
    intro a
    unfold calendarReplay
    rw [hword, take_before_last_append _ D (by rw [hDlen]; have h := d.stream.positiveLength; omega), hDlen]
    rfl
  refine ⟨P0, hP0len, hP0map, hP0prefix, ?_⟩
  intro b hbt hchosen
  cases houtcome : d.outcome with
  | exhausted hnonempty _ _ _ _ =>
      exact False.elim ((Finset.nonempty_iff_ne_empty.mp hnonempty) hdempty)
  | empty e =>
      simp only [houtcome] at hnextSeed
      cases hnext : e.nextBoundary with
      | terminal hterminal _ =>
          omega
      | next _ _ x _ _ _ _ _ _ _ sameRecord dispatch =>
          simp only [hnext] at hnextSeed
          obtain ⟨_htime, _k, _hcanonical, _hknum, consistent, reconstructed, _hrec, hnum, hcases⟩ := hnextSeed
          have hslot : E.records[
              (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length + d.stream.ell]? =
                some R[b.val] := by
            rw [hboundary, ← hepoch]
            have hb : t.val - physicalStart rate z rewards C_star C_h = b.val := by omega
            rw [hb]
            exact List.getElem?_eq_getElem b.isLt
          have hx : x = R[b.val].input := sameRecord R[b.val] hslot
          have hchosenX : laterChosen x = true := by
            rw [hx]
            exact hchosen
          rcases hcases with hfailure | hsuccess
          · obtain ⟨arm, reason, _hcorrected, hlater, hdispatch⟩ := hfailure
            unfold laterChosen at hchosenX
            rw [dispatch.preparedCoordinator, hdispatch] at hchosenX
            cases hchosenX
          · obtain ⟨output, hlocal, clockData, installed, selection,
              hinstall, hreconstruction, hlater, hdispatch, hpayload, hsigma,
              hvector, hinstalledRec, hqueues, hretained, hcomplement⟩ := hsuccess
            have hnumOutput : ∀ a,
                AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                    (calendarReplay rate a P0 P0.length).1 ∧
                AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                    (calendarReplay rate a P0 P0.length).2 ∧
                output.reconstruction.registers.current a =
                  ⟨(calendarReplay rate a P0 P0.length).2,
                    (calendarReplay rate a P0 P0.length).1 -
                      (calendarReplay rate a P0 (P0.length - 1)).1⟩ := by
              intro a
              rw [hreconstruction]
              simpa only [hfull, hprev] using hnum a
            have hresult : initializes_calendar rate P0
                { input := x, output := ReferenceActivePhysicalStep.step x, output_eq := rfl } := by
              refine ⟨d.stream.payload, d.ledger, d.stream.saved, dispatch.cutoffTime,
                dispatch.actualState, hdempty, dispatch.cutoffTimeEq, dispatch.core,
                dispatch.started, dispatch.startCheck, dispatch.instruction,
                dispatch.assignmentStart, dispatch.instructionTime, consistent, output,
                hlocal, clockData, installed, selection, hinstall, hlater, hdispatch, ?_,
                hpayload, hsigma, hvector, hinstalledRec.trans hreconstruction.symm, ?_, ?_, ?_, ?_, ?_⟩
              · change (ReferenceActivePhysicalStep.prepare x).coordinator = _
                rw [dispatch.preparedCoordinator, hdispatch]
              · intro a
                exact ⟨(hnumOutput a).1, (hnumOutput a).2.1,
                  (output.payload_queues a).trans (hnumOutput a).2.1,
                  (hqueues a).trans (congrArg Prod.snd (hfull a)), (hnumOutput a).2.2⟩
              · intro i
                simpa only [hfull] using hretained i
              · intro j
                simpa only [hfull, hprev] using hcomplement j
              · intro hcorrected
                exact (AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
                  _ _ output.reconstruction output.reconstruction_eq hcorrected).1
              · intro hrenewal
                exact AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
                  _ _ output.reconstruction output.reconstruction_eq hrenewal
            have hr : (R[b.val]) =
                { input := x, output := ReferenceActivePhysicalStep.step x, output_eq := rfl } := by
              let canonical : ReferenceActivePhysicalStep.RoundInput p rate →
                  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
                fun y => { input := y, output := ReferenceActivePhysicalStep.step y, output_eq := rfl }
              exact (record_eq_step rate R[b.val]).trans (congrArg canonical hx.symm)
            change initializes_calendar rate P0 R[b.val]
            rw [hr]
            exact hresult

end Bandits.Support.ReferenceFirstReplacementCalendarInitialization

end
