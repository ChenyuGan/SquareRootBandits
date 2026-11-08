/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentExponentialQueueStep
public import Bandits.Support.ReferenceFirstLiveCalendarExponentialBound

/-!
# Old first-collection calendar-prefix readout

The fixed-boundary readout keeps the original live prefix and the actual
first-collection cells in one queue run. The cutoff cell belongs to the old
collection list; the invocation's current cell is read only after that list.

Sources: `04_slow_fast_learner.tex:140-188,245-284`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:35-100,355-426`
under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionOldPrefixCalendarReadout

open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceFirstCollectionCurrentRetainedGate (cell0 pastCells?)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate

private theorem mapM_some {α : Type*} (xs : List α) :
    (xs.map some).mapM id = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

/-- Each dated source slot in a covered first-call suffix contributes its
actual cell to every shorter strict prefix. No absent slot is filtered. -/
private theorem strictPrefix_eq_take
    (t v : Fin p.T) (z : S) (s : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = s)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hlen : L.length = t.val - s)
    (hcoverage : ∀ k : Fin L.length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]? = some r ∧
        r.input.time.val = s + k.val ∧ cell0 rate r = some L[k.val])
    (hsv : s ≤ v.val) (hvt : v.val ≤ t.val) :
    pastCells? rate rewards C_star C_h v z = some (L.take (v.val - s)) := by
  have htake : v.val - s ≤ L.length := by rw [hlen]; omega
  have hslots : ReferenceFirstCollectionCurrentRetainedGate.pastSlots
      rate rewards C_star C_h v z = (L.take (v.val - s)).map some := by
    apply List.ext_getElem
    · simp only [ReferenceFirstCollectionCurrentRetainedGate.pastSlots,
        hstart, List.length_map, List.length_range, List.length_take]
      rw [Nat.min_eq_left htake]
    · intro k hk hkTake
      have hkNum : k < v.val - s := by
        simpa only [ReferenceFirstCollectionCurrentRetainedGate.pastSlots,
          hstart, List.length_map, List.length_range] using hk
      have hkL : k < L.length := by rw [hlen]; omega
      obtain ⟨r, hrecord, _, hcell⟩ := hcoverage ⟨k, hkL⟩
      simp only [ReferenceFirstCollectionCurrentRetainedGate.pastSlots,
        List.getElem_map, List.getElem_range]
      have hrecord' : (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k]? = some r := by simpa using hrecord
      have hcell' : cell0 rate r = some L[k] := by simpa using hcell
      rw [hrecord', Option.bind_some]
      simpa only [List.getElem_take] using hcell'
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h v.val z := by
    change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing.isSome = true ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ v.val
    exact ⟨hcross, by rw [hstart]; exact hsv⟩
  unfold ReferenceFirstCollectionCurrentRetainedGate.pastCells?
  rw [ite_eq_left hlaunch, hslots]
  exact mapM_some (L.take (v.val - s))

/-- Taking a calendar prefix past the end of the live segment retains exactly
the same live list and the corresponding prefix of the actual old list. -/
private theorem split_old_prefix {V D : List (RecordedQueueRun.RoundInput p.K)}
    {s w u v : ℕ} (hVlen : V.length = w) (hu : u = s + w)
    (huv : u ≤ v) :
    (V ++ D).take (v - s) = V ++ D.take (v - u) := by
  have htake : (V ++ D).take (v - s) = V ++ D.take (v - s - w) := by
    rw [List.take_append]
    rw [List.take_of_length_le (by rw [hVlen]; omega), hVlen]
  have hindex : v - s - w = v - u := by omega
  rw [htake, hindex]

/-- The actual initialized stream, cutoff head, old ledger, whole live list,
and complete-suffix coverage are chosen once from the local first-call
selector. Every strict-prefix query through the invocation uses the same
list, and every post-cutoff prefix is the same live list followed by `D.take`.
The per-slot coverage retains the original dated record and `cell0` value. -/
theorem firstCell_prefix_at_boundary (u t : Fin p.T) (z : S)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
    ∃ hs : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T,
    ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        hs).records).length <
          p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
    ∃ f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) z rewards C_star C_h
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        hc hs hshort,
    ∃ head : ReferenceCollectionSegmentExtraction.Choice rate,
    ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
        head.payload head.started head.weights),
    ∃ D L : List (RecordedQueueRun.RoundInput p.K),
      let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h
      let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
      let count := p.T - s
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
      let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc count hs
      s ≤ u.val ∧ u.val < t.val ∧ u.val = s + w ∧
      s + w + f.stream.ell = t.val ∧ f.ledger.pending = ∅ ∧
      R[t.val - s - 1]? = some f.record ∧
      ReferenceCollectionSegmentExtraction.choice f.stream.cutoff.cut.input = some head ∧
      D.length = f.stream.ell ∧
      D[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate f.stream.cutoff.cut head rewards valid) ∧
      (∀ k : Fin f.stream.ell,
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (f.stream.window[k.val]'(lt_of_lt_of_le k.isLt f.stream.withinWindow)) =
            D[k.val]?) ∧
      L = V ++ D ∧ pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - s ∧
      (∀ k : Fin L.length,
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          R[k.val]? = some r ∧ r.input.time.val = s + k.val ∧
            cell0 rate r = some L[k.val]) ∧
      (∀ v : Fin p.T, s ≤ v.val → v.val ≤ t.val →
        pastCells? rate rewards C_star C_h v z = some (L.take (v.val - s))) ∧
      (∀ v : Fin p.T, u.val ≤ v.val → v.val ≤ t.val →
        L.take (v.val - s) = V ++ D.take (v.val - u.val)) ∧
      ∃ vStart : Fin p.T, vStart.val = s ∧
        pastCells? rate rewards C_star C_h vStart z = some [] ∧
        (∀ a : Fin p.K,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
            rate rewards C_star C_h a vStart.val z = 0) := by
  dsimp only
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, htotal,
      hpending, hrecord, hchoice, hDlen, hDzero, hDread, hLD, hPast,
      hlen, hcoverage⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage
      rate rewards C_star C_h u t z hz
  have hVlen :
      (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs).length =
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)).length := by
    have h := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc _ hs
    have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
    have hW : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z rewards C_star C_h hc _ hs =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) := by
      unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rw [← hepoch]
    exact h.trans (congrArg List.length hW)
  have hprefix (v : Fin p.T) (hsv :
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ v.val)
      (hvt : v.val ≤ t.val) :
      pastCells? rate rewards C_star C_h v z = some
        (L.take (v.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h)) := by
    exact strictPrefix_eq_take rate rewards C_star C_h t v z _ hc rfl L hlen
      hcoverage hsv hvt
  have hsplit (v : Fin p.T) (huv : u.val ≤ v.val) (hvt : v.val ≤ t.val) :
      L.take (v.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h) =
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
          rate z rewards C_star C_h hc _ hs) ++ D.take (v.val - u.val) := by
    have hlenV :
        (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
          rate z rewards C_star C_h hc _ hs).length =
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)).length := hVlen
    have hmain := split_old_prefix
      (V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc _ hs) (D := D)
      hlenV hu (by omega : u.val ≤ v.val)
    simpa only [hLD] using hmain
  refine ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, htotal,
    hpending, hrecord, hchoice, hDlen, hDzero, hDread, hLD, hPast, hlen,
    hcoverage, ?_, ?_, ?_⟩
  · intro v hsv hvt
    exact hprefix v (by simpa only [ReferenceCompletePhysicalHistory.physicalStart] using hsv) hvt
  · intro v huv hvt
    exact hsplit v huv hvt
  · have hslt : ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h < p.T := by omega
    let vStart : Fin p.T := ⟨
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
      hslt⟩
    have hstartPast : pastCells? rate rewards C_star C_h vStart z = some [] := by
      have h := hprefix vStart (by exact le_rfl) (by
        have h := hsu.trans (le_of_lt hut)
        simpa only [vStart] using h)
      simpa only [vStart, Nat.sub_self, List.take_zero] using h
    refine ⟨vStart, rfl, hstartPast, ?_⟩
    intro a
    simp [ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt,
      vStart, RecordedQueueRun.run, RecordedQueueRun.execute,
      RecordedQueueRun.initialState, StoppedQueueBound.normalizedBacklog]

/-- At the cutoff boundary the strict old prefix is exactly the completed
first-live queue. At the next boundary the actual cutoff source cell is
appended once, with the original stream and head witness. -/
theorem firstCell_cutoff_incoming_eq_firstWindow (u t : Fin p.T)
    (a : Fin p.K) (z : S)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (hs : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          hs).records).length <
            p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) z rewards C_star C_h
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        hc hs hshort)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D L : List (RecordedQueueRun.RoundInput p.K)),
      let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs
      D.length = f.stream.ell ∧
      D[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate f.stream.cutoff.cut head rewards valid) ∧
      L = V ++ D ∧ pastCells? rate rewards C_star C_h t z = some L ∧
      pastCells? rate rewards C_star C_h u z = some V ∧
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h a u.val z =
        StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q V) a ∧
      ∃ vNext : Fin p.T, vNext.val = u.val + 1 ∧
        pastCells? rate rewards C_star C_h vNext z =
          some (V ++ [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate f.stream.cutoff.cut head rewards valid]) := by
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, htotal,
      _, _, hchoice, hDlen, hDzero, _, hLD, hPast, hlen, hcoverage, hprefix,
      hsplit, _⟩ := firstCell_prefix_at_boundary rate rewards C_star C_h u t z hz
  dsimp only
  let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc (p.T -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h = (ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h) := rfl
  have hVlen : V.length =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)).length := by
    have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
      rate rewards C_star C_h z hc
    have hW : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z rewards C_star C_h hc _ hs =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) := by
      unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rw [← hepoch]
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc _ hs |>.trans (congrArg List.length hW)
  have huPrefix := hprefix u hsu (le_of_lt hut)
  have hAtU : L.take (u.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) = V := by
    have h := hsplit u le_rfl (le_of_lt hut)
    simpa only [Nat.sub_self, List.take_zero, List.append_nil] using h
  have hPastU : pastCells? rate rewards C_star C_h u z = some V := by
    rw [huPrefix, hAtU]
  have hwhole :
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z = V := by
    let s : Fin (p.T + 1) := ⟨
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
      Nat.lt_succ_of_le (ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h)⟩
    let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s.val :=
      ⟨z, hc, rfl⟩
    have hxCross := ReferenceFirstLiveOverflowReadout.launch_crossing
      rate rewards C_star C_h s.val x
    have hxSpan := ReferenceFirstLiveOverflowReadout.launch_span
      rate rewards C_star C_h s.val _ hs x
    have hfiber := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h s x
    simpa only [ReferenceFirstLiveOverflowReadout.firstLiveCells,
      ReferenceFirstLiveOverflowReadout.launch_crossing,
      ReferenceFirstLiveOverflowReadout.launch_span, s, x] using hfiber.2
  have hbacklog :
      ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
        rate rewards C_star C_h a u.val z =
        StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q V) a := by
    unfold ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
    rw [hwhole]
    have hindex : u.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h = V.length := by
      rw [hVlen]
      omega
    rw [hindex, List.take_length]
    rfl
  have hnextLe : u.val + 1 ≤ t.val := Nat.succ_le_of_lt hut
  have hnextLt : u.val + 1 < p.T := lt_of_le_of_lt hnextLe t.isLt
  let vNext : Fin p.T := ⟨u.val + 1, hnextLt⟩
  have hnextStart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ vNext.val := by
    simpa only [vNext] using Nat.le_trans hsu (Nat.le_succ u.val)
  have hnextPrefix := hprefix vNext hnextStart (by simpa only [vNext] using hnextLe)
  have hnextSplit := hsplit vNext (by simp only [vNext]; omega)
    (by simpa only [vNext] using hnextLe)
  have hDcons : D.take 1 = [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate f.stream.cutoff.cut head rewards valid] := by
    have hDpos : 0 < D.length := (List.getElem?_eq_some_iff.mp hDzero).1
    cases D with
    | nil => simp at hDpos
    | cons d ds =>
        have hd : d = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate f.stream.cutoff.cut head rewards valid := by
          simpa using hDzero
        simp [hd]
  refine ⟨hc, hs, hshort, f, head, valid, D, L, hDlen, hDzero,
    hLD, hPast, ?_, hbacklog, ⟨vNext, rfl, ?_⟩⟩
  · simpa only [ReferenceFirstCollectionCurrentRetainedGate.pastCells?,
      ReferenceFirstCollectionCurrentRetainedGate.pastSlots] using hPastU
  · rw [hnextPrefix, hnextSplit]
    have hindex : vNext.val - u.val = 1 := by simp [vNext]
    rw [hindex, hDcons]

/-- At the invocation boundary, `bMinus` is the real incoming register read
from the same old-prefix run `V ++ D`. The cutoff head is included in `D`; the
invocation's current update is excluded. -/
theorem firstCell_before_eq_oldPrefix (u t : Fin p.T) (a : Fin p.K)
    (z : S) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
      (hs : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed +
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
          hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          hs).records).length <
            p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        (rate := rate) z rewards C_star C_h
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        hc hs hshort)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D L : List (RecordedQueueRun.RoundInput p.K)),
      let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc (p.T -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs
      D.length = f.stream.ell ∧
      D[0]? = some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate f.stream.cutoff.cut head rewards valid) ∧
      pastCells? rate rewards C_star C_h t z = some L ∧
      L = V ++ D ∧
      ReferenceFirstCollectionCurrentQueueReadout.before?
        rate rewards C_star C_h t z = some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L)) ∧
      ReferenceFirstCollectionCurrentQueueReadout.bMinus
        rate rewards C_star C_h u t a z =
        StoppedQueueBound.normalizedBacklog q (RecordedQueueRun.run q (V ++ D)) a := by
  obtain ⟨hc, hs, hshort, f, head, valid, D, L, hsu, hut, hu, htotal,
      _, _, _, hDlen, hDzero, _, hLD, hPast, _, _, _, _, _⟩ :=
    firstCell_prefix_at_boundary rate rewards C_star C_h u t z hz
  obtain ⟨Lread, c, hLread, _, _, hbefore, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionCurrentQueueReadout.firstCell_actual_queue_readouts
      rate rewards C_star C_h u t a z hz
  have hsame : Lread = L := Option.some.inj (hLread.symm.trans hPast)
  subst Lread
  have hbMinus :
      ReferenceFirstCollectionCurrentQueueReadout.bMinus
        rate rewards C_star C_h u t a z =
        ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog
          rate (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run q L))) a := by
    simp [ReferenceFirstCollectionCurrentQueueReadout.bMinus,
      Set.indicator_of_mem hz, hbefore]
  refine ⟨hc, hs, hshort, f, head, valid, D, L, hDlen, hDzero,
    hPast, hLD, hbefore, ?_⟩
  rw [hbMinus, hLD]
  simp [ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog,
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
    StoppedQueueBound.normalizedBacklog,
    ReferenceFirstLaunchNumericalCell.queueParameters]

end Bandits.Support.ReferenceFirstCollectionOldPrefixCalendarReadout

end
