/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentRawMoments

import Mathlib.Tactic

/-!
# The strict-past retained test at the original first collection call

These are optional observations of the original physical suffix. Every dated
slot is retained, and a missing numerical readout makes the prefix absent.
The numerical run starts at the original launch with zero registers.

Sources: `04_slow_fast_learner.tex:140-188,245-274`,
`05_binary_transport.tex:352-431`, `06_interruptions.tex:355-426`, and
`appendix_a_local_protocol.tex:28-79` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate

open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open RecordedQueueRun (RoundInput run)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The two disjoint actual branch readouts, without a missing-cell default. -/
def cell0 (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r)

/-- One optional slot for every original suffix date strictly before `t`. -/
def pastSlots (t : Fin p.T) (z : SourceInput p) :
    List (Option (RecordedQueueRun.RoundInput p.K)) :=
  (List.range (t.val - ReferenceCompletePhysicalHistory.physicalStart
    rate z rewards C_star C_h)).map (fun k =>
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k]?).bind (cell0 rate))

/-- A launch and a present cell at every required date are both necessary. -/
def pastCells? (t : Fin p.T) (z : SourceInput p) :
    Option (List (RecordedQueueRun.RoundInput p.K)) :=
  if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z then
    (pastSlots rate rewards C_star C_h t z).mapM id
  else none

/-- Existing queue registers, overflow flag, and accepted histories only. -/
def prefixReadout? (t : Fin p.T) (z : SourceInput p) :
    Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) :=
  (pastCells? rate rewards C_star C_h t z).map (fun L =>
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) L))

/-- Only earlier updates determine this pre-choice overflow test. -/
def H (t : Fin p.T) : Set (SourceInput p) :=
  {z | ∃ v, prefixReadout? rate rewards C_star C_h t z = some v ∧ v.2.1 = false}

/-- The retained test localized to the original first invocation. -/
def G (u t : Fin p.T) : Set (SourceInput p) :=
  ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ∩
    H rate rewards C_star C_h t

/-- The exact accepted record, when both actual observations are present. -/
def acceptedCurrent? (t : Fin p.T) (a : Fin p.K) (z : SourceInput p) :
    Option (Bool × ℕ) :=
  (pastCells? rate rewards C_star C_h t z).bind (fun L =>
    (ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h t z).map (fun c =>
        RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) L) c a))

/-- No-launch, future-launch, and terminal-launch inputs remain absent. -/
theorem pastCells_eq_none (t : Fin p.T) (z : SourceInput p)
    (hz : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z) :
    pastCells? rate rewards C_star C_h t z = none := by
  simp only [pastCells?, ite_eq_right hz]

/-- At a genuine launch the empty strict prefix reads the actual initial state. -/
theorem prefixReadout_at_launch (t : Fin p.T) (z : SourceInput p)
    (hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z)
    (ht : t.val = ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h) :
    prefixReadout? rate rewards C_star C_h t z =
      some (stateReadout (RecordedQueueRun.initialState p.K)) := by
  unfold prefixReadout?
  rw [pastCells?, ite_eq_left hz]
  simp [pastSlots, ← ht, run, RecordedQueueRun.execute]

private theorem H_iff_overflow (t : Fin p.T) (z : SourceInput p)
    (L : List (RoundInput p.K))
    (hL : pastCells? rate rewards C_star C_h t z = some L) :
    z ∈ H rate rewards C_star C_h t ↔
      (run (queueParameters rate) L).overflow = false := by
  simp only [H, Set.mem_ofPred_eq, prefixReadout?, hL, Option.map_some]
  constructor
  · rintro ⟨v, hv, hf⟩
    cases Option.some.inj hv
    exact hf
  · intro hf
    exact ⟨_, rfl, hf⟩

private theorem overflow_false_iff_allPrefixes (q : RecordedQueueRun.Parameters)
    (L : List (RoundInput p.K)) :
    (run q L).overflow = false ↔
      ∀ h ≤ L.length, ∀ j : Fin p.K,
        32 * (UnstoppedRecordedQueueComparison.unstoppedReplay q L h j).2 ≤ q.D := by
  open UnstoppedRecordedQueueComparison in
  have hflag := prefix_overflow_iff_first_overflow_prefix_le q L L.length (by rfl)
  simp only [List.take_length] at hflag
  constructor
  · intro hfalse h hlen j
    have hbefore : L.length <
        UnstoppedRecordedQueueComparison.firstOverflowPrefix q L := by
      by_contra hnot
      have ht := hflag.mpr (Nat.le_of_not_gt hnot)
      rw [hfalse] at ht
      cases ht
    by_cases hz : h = 0
    · subst h
      simp [UnstoppedRecordedQueueComparison.unstoppedReplay, QueueReplay.replay]
    · have hno := UnstoppedRecordedQueueComparison.not_replay_crosses_overflow_before_first
        q L h (by omega) hlen (by omega)
      exact Nat.le_of_not_gt (fun hcross => hno ⟨j, hcross⟩)
  · intro hall
    cases hf : (run q L).overflow with
    | false => rfl
    | true =>
        have hk := hflag.mp hf
        obtain ⟨j, hj⟩ := UnstoppedRecordedQueueComparison.replay_crosses_overflow_at_first q L hk
        have hb := hall _ hk j
        omega

private theorem readout_zero_of_some (s : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RoundInput p.K)
    (hread : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some cell) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
  open ReferenceLaterCollectionArrivalReadout in
  have hp : (laterCollectionReadout s record).isSome = true := by rw [hread]; rfl
  obtain ⟨hf, hb⟩ := (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain s record).mp hp
  cases hcoord : record.output.preparation.coordinator with
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord] using hread
      | _ => simp only [hcoord] at hb
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected =>
          have hg : s < registers.payload.sigma.val := by simpa only [hcoord] using hb
          have hg0 : 0 < registers.payload.sigma.val := by omega
          simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
            dite_eq_left hf, hcoord, hg, hg0, ite_true] using hread
      | _ => simp only [hcoord] at hb
  | first outcome => cases outcome <;> simp only [hcoord] at hb
  | invalidCollectionCutoff => simp only [hcoord] at hb
  | dagger => simp only [hcoord] at hb

private theorem cutoff_readout_zero (z : SourceInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (hs : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) z rewards C_star C_h +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hc (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hs).records).length <
          p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (out : ReferenceFirstCollectionReadyStream.ActualInitializedStreamOutput
      (rate := rate) z rewards C_star C_h
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) hc hs hshort)
    (head : ReferenceCollectionSegmentExtraction.Choice rate)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput out.cutoff.cut.output.preparation
        head.payload head.started head.weights))
    (hhead : ReferenceCollectionSegmentExtraction.choice out.cutoff.cut.input = some head) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 out.cutoff.cut =
      some (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate out.cutoff.cut head rewards valid) := by
  obtain ⟨_, _, d, _, _, _, D, _, _, _, _, hDlen, _, hcells⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
      rate rewards C_star C_h z hc hshort
  let zero : Fin d.stream.ell := ⟨0, by have h := d.stream.positiveLength; omega⟩
  obtain ⟨call, validCall, hcall, _, _, hcell, _, _, _, _, _, _, _, _, hread, _⟩ :=
    hcells zero
  have hd := (d.stream.alignment
    ⟨0, lt_of_lt_of_le zero.isLt d.stream.withinWindow⟩).1
  have ho := (out.alignment ⟨0, out.windowNonempty⟩).1
  simp only [Nat.add_zero] at hd ho
  rw [out.cutoffIsHead] at ho
  have he : d.stream.window[0]'(by have h := d.stream.windowNonempty; omega) =
      out.cutoff.cut := Option.some.inj (hd.symm.trans ho)
  dsimp only [zero] at hcall hcell hread
  rw [he] at hcall hcell hread
  have hchoice : call = head := Option.some.inj (hcall.symm.trans hhead)
  subst call
  rw [hcell] at hread
  exact hread

private theorem mapM_some_slots {α : Type*} (L : List α) :
    (L.map some).mapM id = some L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.mapM_cons, ih]

private theorem takeWhile_lookup {α : Type*} (test : α → Bool)
    (R : List α) (k : ℕ) (hk : k < (R.takeWhile test).length) :
    R[k]? = some ((R.takeWhile test)[k]) := by
  induction R generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases ht : test head with
      | false => simp [List.takeWhile, ht] at hk
      | true =>
          cases k with
          | zero => simp [List.takeWhile, ht]
          | succ k =>
              have hk' : k < (tail.takeWhile test).length := by
                simpa [List.takeWhile, ht] using hk
              simpa only [List.takeWhile, ht, List.getElem_cons_succ,
                List.getElem?_cons_succ] using ih k hk'

/-- One original initialized stream covers every strict-past date, including
the cutoff head and the final FINISH before either kind of first invocation.
The same `f` supplies the empty incoming ledger and the source-cell list. -/
theorem firstCell_prefix_coverage (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    let count := p.T - s
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    ∃ hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true,
    ∃ hs : s + count ≤ p.T,
    ∃ hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        z rewards C_star C_h hc count hs).records).length < count,
    ∃ f : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (rate := rate) z rewards C_star C_h count hc hs hshort,
    ∃ (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput f.stream.cutoff.cut.output.preparation
          head.payload head.started head.weights))
      (D L : List (RoundInput p.K)),
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
      L = ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate z rewards C_star C_h hc count hs ++ D ∧
      pastCells? rate rewards C_star C_h t z = some L ∧ L.length = t.val - s ∧
      (∀ k : Fin L.length,
        ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
          R[k.val]? = some r ∧ r.input.time.val = s + k.val ∧
            cell0 rate r = some L[k.val]) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  obtain ⟨n, r, theta, hr, ht, har, hcall, hrows, hselected, hrewards,
    hearlier, htime, hc, hs, hrecords, hk, f, e, hf, hu, hn,
    hlast, hnext, hcoord, hcut, hcursor, hpending, hknown, hservice, hinc, hdispatch⟩ :=
    ReferenceFirstCollectionCallStoredBounds.firstCell_stored_bounds
      rate rewards C_star C_h u t z hz
  change s + n = t.val at htime
  change u.val = s + w at hu
  change n = w + f.stream.ell at hn
  obtain ⟨head, initializer, valid, D, hhead, hpay, hinit, hchecked, hDlen, hzero, hcells⟩ :=
    ReferenceFirstCollectionAllArmNumericalStream.stream_source_prefix
      rate z rewards C_star C_h hc count hs _ f.stream
  have hheadRead := cutoff_readout_zero rate rewards C_star C_h z hc hs _ f.stream head valid hhead
  have hDread (k : Fin f.stream.ell) :
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
        (f.stream.window[k.val]'(lt_of_lt_of_le k.isLt f.stream.withinWindow)) =
          some (D[k.val]'(by omega)) := by
    by_cases hzeroIndex : k.val = 0
    · simpa only [hzeroIndex, f.stream.cutoffIsHead, hzero] using hheadRead
    · obtain ⟨call, validCall, _, _, _, _, _, _, _, _, _, _, _, hread⟩ := hcells k
      exact readout_zero_of_some rate s _ _ (hread (by omega))
  let V := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc count hs
  let L := V ++ D
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z hc
  have hW : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z rewards C_star C_h hc count hs =
        ReferenceFirstLiveConfirmationHistory.firstLiveWindow R := by
    unfold ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rw [← hepoch]
  have hVlen : V.length = w := by
    exact (ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc count hs).trans (congrArg List.length hW)
  have hLlen : L.length = t.val - s := by
    simp only [L, List.length_append, hVlen, hDlen]
    change s + n = t.val at htime
    change n = w + f.stream.ell at hn
    omega
  obtain ⟨_, hstart, hlive⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
      rate rewards C_star C_h z hc
  have hcoverage (k : Fin L.length) :
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        R[k.val]? = some r ∧ r.input.time.val = s + k.val ∧
          cell0 rate r = some L[k.val] := by
    by_cases hkv : k.val < w
    · let j : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate z rewards C_star C_h hc count hs).length := ⟨k.val, by rw [hW]; exact hkv⟩
      obtain ⟨hbound, hdate, _, _, _, _, hread, hnone, _⟩ := hlive j
      let record := (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z rewards C_star C_h hc count hs)[j.val]
      have hlookup : R[k.val]? = some record := by
        have hprefix : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R)[k.val]? =
            some record := by
          have hi := congrArg (fun xs => xs[k.val]?) hW
          exact hi.symm.trans (List.getElem?_eq_getElem j.isLt)
        have hp := (List.getElem?_eq_some_iff.mp hprefix).2
        have hl := takeWhile_lookup
          (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.cutoffChosen r.input) R k.val hkv
        exact hl.trans (congrArg some hp)
      refine ⟨record, hlookup, hdate, ?_⟩
      change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).or _ = _
      rw [hread]
      simp only [Option.some_or]
      congr 1
      change V[k.val]'(by omega) = (V ++ D)[k.val]'k.isLt
      exact (List.getElem_append_left (by omega)).symm
    · let j : Fin f.stream.ell := ⟨k.val - w, by
        have h := k.isLt
        simp only [L, List.length_append, hVlen, hDlen] at h
        omega⟩
      let record := f.stream.window[j.val]'(lt_of_lt_of_le j.isLt f.stream.withinWindow)
      have hj : w + j.val = k.val := by dsimp only [j]; omega
      have ha := (f.stream.alignment
        ⟨j.val, lt_of_lt_of_le j.isLt f.stream.withinWindow⟩).1
      rw [← hrecords] at ha
      change R[w + j.val]? = some record at ha
      rw [hj] at ha
      have hread := hDread j
      have hnone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
        cases h : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
        | none => rfl
        | some c =>
            exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 record
              ⟨by rw [h]; rfl, by rw [hread]; rfl⟩)
      refine ⟨record, ha, ?_, ?_⟩
      · have hd := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
          rate z rewards C_star C_h k.val record ha
        exact hd
      · change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).or _ = _
        rw [hnone, Option.none_or, hread]
        congr 1
        change D[k.val - w]'(by have h := j.isLt; dsimp only [j] at h; omega) = (V ++ D)[k.val]'k.isLt
        simpa only [hVlen] using (List.getElem_append_right (as := V) (bs := D)
          (i := k.val) (by omega)).symm
  have hslots : pastSlots rate rewards C_star C_h t z = L.map some := by
    apply List.ext_getElem
    · simp only [pastSlots, List.length_map, List.length_range]
      exact hLlen.symm
    · intro k hk hk'
      have hkl : k < L.length := by simpa only [List.length_map] using hk'
      obtain ⟨record, hrecord, _, hread⟩ := hcoverage ⟨k, hkl⟩
      simp only [pastSlots, List.getElem_map, List.getElem_range]
      change (R[k]?.bind (cell0 rate)) = some L[k]
      rw [hrecord, Option.bind_some, hread]
  have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z := ⟨hc, by change s ≤ t.val; omega⟩
  refine ⟨hc, hs, _, f, head, valid, D, L, ?_, ?_, hu, ?_, hpending, ?_, hhead,
    hDlen, ?_, ?_, rfl, ?_, hLlen, hcoverage⟩
  · change s ≤ u.val
    change u.val = s + w at hu
    omega
  · change u.val = s + w at hu
    change s + n = t.val at htime
    change n = w + f.stream.ell at hn
    have hpos := f.stream.positiveLength
    omega
  · change s + w + f.stream.ell = t.val
    omega
  · have hi : t.val - s = n := by change s + n = t.val at htime; omega
    rw [hi]
    exact hlast
  · have hp := f.stream.positiveLength
    rw [List.getElem?_eq_getElem (by omega), hzero]
  · intro k
    rw [List.getElem?_eq_getElem (by omega)]
    exact hDread k
  · rw [pastCells?, ite_eq_left hlaunch, hslots]
    exact mapM_some_slots L

private theorem firstCell_past_exists (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ L, pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h := by
  obtain ⟨_, _, _, _, _, _, _, L, _, _, _, _, _, _, _, _, _, _, _, hL, hlen, _⟩ :=
    firstCell_prefix_coverage rate rewards C_star C_h u t z hz
  exact ⟨L, hL, hlen⟩

/-- The pre-choice flag checks every original earlier update, even when an
unstopped queue later drains. The first current crossing is therefore retained. -/
theorem firstCell_allPrefixes (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ L, pastCells? rate rewards C_star C_h t z = some L ∧
      L.length = t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h ∧
      (z ∈ H rate rewards C_star C_h t ↔
        ∀ h ≤ L.length, ∀ j : Fin p.K,
          32 * (UnstoppedRecordedQueueComparison.unstoppedReplay
            (queueParameters rate) L h j).2 ≤ (queueParameters rate).D) := by
  obtain ⟨L, hL, hlen⟩ := firstCell_past_exists rate rewards C_star C_h u t z hz
  exact ⟨L, hL, hlen, (H_iff_overflow rate rewards C_star C_h t z L hL).trans
    (overflow_false_iff_allPrefixes (queueParameters rate) L)⟩

/-- On either original first invocation, the actual enabled current cell and
the covered original prefix yield exactly the retained accepted record. -/
theorem firstCell_acceptedRecord (u t : Fin p.T) (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (L : List (RoundInput p.K)) (c : RoundInput p.K),
      pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧ c.enabled = true ∧
      acceptedCurrent? rate rewards C_star C_h t a z =
        some (RecordedQueueRun.acceptedRecord (queueParameters rate)
          (run (queueParameters rate) L) c a) ∧
      RecordedQueueRun.acceptedRecord (queueParameters rate)
        (run (queueParameters rate) L) c a =
          (if z ∈ H rate rewards C_star C_h t then
            (true, RecordedQueueRun.quantizedArrival (queueParameters rate) c a)
          else (false, 0)) ∧
      (RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord
        (queueParameters rate) (run (queueParameters rate) L) c a) : ℝ) /
          ((queueParameters rate).n : ℝ) =
        (H rate rewards C_star C_h t).indicator
          (ReferenceFirstCollectionCurrentRawMoments.currentRaw rate rewards C_star C_h t a) z := by
  obtain ⟨L, hL, _⟩ := firstCell_past_exists rate rewards C_star C_h u t z hz
  obtain ⟨_, r, _, _, c, _, _, _, _, _, _, _, _, _, hcell, hread, _⟩ :=
    ReferenceFirstCollectionCurrentRecordedCell.firstCell_selected
      rate rewards C_star C_h u t z hz
  have henabled := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r c hread).1
  have hgate := H_iff_overflow rate rewards C_star C_h t z L hL
  have haccept : RecordedQueueRun.acceptedRecord (queueParameters rate)
      (run (queueParameters rate) L) c a =
        if z ∈ H rate rewards C_star C_h t then
          (true, RecordedQueueRun.quantizedArrival (queueParameters rate) c a)
        else (false, 0) := by
    by_cases hzH : z ∈ H rate rewards C_star C_h t
    · simp only [ite_eq_left hzH, RecordedQueueRun.acceptedRecord,
        hgate.mp hzH, Bool.false_eq_true, ite_false, henabled, ite_true]
    · have hf : (run (queueParameters rate) L).overflow = true := by
        cases hf : (run (queueParameters rate) L).overflow with
        | false => exact False.elim (hzH (hgate.mpr hf))
        | true => rfl
      simp only [ite_eq_right hzH, RecordedQueueRun.acceptedRecord, hf, ite_true]
  refine ⟨L, c, hL, hcell, henabled, ?_, haccept, ?_⟩
  · simp only [acceptedCurrent?, hL, Option.bind_some, hcell, Option.map_some]
  · rw [haccept]
    by_cases hzH : z ∈ H rate rewards C_star C_h t
    · simp only [ite_eq_left hzH, Set.indicator_of_mem hzH,
        ReferenceFirstCollectionCurrentRawMoments.currentRaw, hcell,
        RecordedQueueRun.acceptedArrival, ite_true,
        RecordedRoundMoments.normalizedQuantizedArrival]
    · simp only [ite_eq_right hzH, Set.indicator_of_notMem hzH,
        RecordedQueueRun.acceptedArrival, Bool.false_eq_true, ite_false,
        Nat.cast_zero, zero_div]

private instance sumMeasurableSingleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) where
  measurableSet_singleton x := by
    cases x with
    | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
    | inr b => simpa only [Set.image_singleton] using (MeasurableSet.singleton b).inr_image

private instance optionMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton x := by
    have h := (comap_measurable (Equiv.optionEquivSumPUnit α))
      (MeasurableSet.singleton (Equiv.optionEquivSumPUnit α x))
    convert h using 1
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, (Equiv.optionEquivSumPUnit α).injective.eq_iff]

private instance listMeasurableSingleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    MeasurableSingletonClass (List α) where
  measurableSet_singleton L := by
    have hinj : Function.Injective
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates (α := α)) := by
      intro A B h
      have hlen : A.length = B.length := congrArg Prod.fst h
      apply List.ext_getElem hlen
      intro k hk hk'
      have he := congrFun (congrArg Prod.snd h) k
      simpa only [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Sum.inr.injEq] using he
    have hh := ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (MeasurableSet.singleton
        (ReferenceActiveHorizonMeasurability.listObservationCoordinates L))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_option_map {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (f : X → Option A) (hf : Measurable f) (g : A → B) (hg : Measurable g) :
    Measurable (fun x => (f x).map g) :=
  ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun q : A × X => g q.1) (hg.comp measurable_fst) f hf

private theorem cell0_coordinates
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    (cell0 rate r).map ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
      (ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r).map
        (Sum.elim id id) := by
  have hp := ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 r
  rw [cell0, Option.map_or]
  have hl := congrArg Prod.fst hp
  have hr := congrArg Prod.snd hp
  change ReferenceCompleteNumericalBranchObservation.leftProjection _ =
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hl
  change ReferenceCompleteNumericalBranchObservation.rightProjection _ =
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates at hr
  rw [← hl, ← hr]
  cases h : ReferenceCompleteNumericalBranchObservation.branchReadout rate 0 r with
  | none => rfl
  | some value => cases value <;> rfl

private theorem slotCoordinates_eq_datePrefix (t : Fin p.T) (z : SourceInput p) :
    (pastSlots rate rewards C_star C_h t z).map
        (Option.map ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates) =
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate t.val
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z)).map
        (fun e => e.2.2.map (Sum.elim id id)) := by
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)]
  simp only [ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
    ReferenceCompleteNumericalBranchObservation.branchCalendar, List.map_take, List.map_map,
    Function.comp_def]
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let n := t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have hn : n ≤ R.length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    exact Nat.sub_le_sub_right (Nat.le_of_lt t.isLt) _
  apply List.ext_getElem
  · simp only [pastSlots, List.length_map, List.length_range, List.length_take]
    exact (Nat.min_eq_left hn).symm
  · intro k hk hk'
    have hkR : k < R.length := by
      have hkn : k < n := by
        have h := hk'
        simp only [List.length_map, List.length_take] at h
        exact lt_of_lt_of_le h (Nat.min_le_left _ _)
      omega
    simp only [pastSlots, List.getElem_map, List.getElem_range, List.getElem_take]
    change (R[k]?.bind (cell0 rate)).map _ = _
    rw [List.getElem?_eq_getElem hkR, Option.bind_some]
    exact cell0_coordinates rate _

private theorem measurableSet_actualLaunchBy
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      {z | ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h t.val z} := by
  have he : {z | ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z} =
      ⋃ s : Fin (t.val + 1),
        ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val := by
    ext z
    constructor
    · rintro ⟨hc, hs⟩
      exact Set.mem_iUnion.mpr ⟨⟨ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h, by omega⟩, hc, rfl⟩
    · intro hz
      obtain ⟨s, hc, hs⟩ := Set.mem_iUnion.mp hz
      exact ⟨hc, hs ▸ Nat.le_of_lt_succ s.isLt⟩
  rw [he]
  exact MeasurableSet.iUnion (fun s =>
    ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_measurable
      rate rewards C_star C_h control0 t s.val (Nat.le_of_lt_succ s.isLt))

private theorem measurable_of_countable_fibers {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Countable A] [MeasurableSpace B] (g : X → A) (hg : Measurable g)
    (f : X → B) (hf : ∀ x y, g x = g y → f x = f y) : Measurable f := by
  intro U _
  have he : f ⁻¹' U = ⋃ v ∈ g '' (f ⁻¹' U), g ⁻¹' {v} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨g x, Set.mem_iUnion.mpr
        ⟨⟨x, hx, rfl⟩, rfl⟩⟩
    · intro hx
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
      obtain ⟨⟨y, hy, hgy⟩, hxv⟩ := Set.mem_iUnion.mp hv
      have heq := hf x y (hxv.trans hgy.symm)
      change f x ∈ U
      rw [heq]
      exact hy
  rw [he]
  exact MeasurableSet.iUnion (fun v => MeasurableSet.iUnion (fun _ =>
    (MeasurableSet.singleton v).preimage hg))

private theorem step_eq_of_arrivalCoordinates
    (state : RecordedQueueRun.RunState p.K) (c d : RoundInput p.K)
    (h : ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate c =
      ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate d) :
    RecordedQueueRun.step (queueParameters rate) state c =
      RecordedQueueRun.step (queueParameters rate) state d := by
  have he : c.enabled = d.enabled := congrArg Prod.fst h
  have ha (j : Fin p.K) : RecordedQueueRun.quantizedArrival (queueParameters rate) c j =
      RecordedQueueRun.quantizedArrival (queueParameters rate) d j :=
    congrFun (congrArg Prod.snd h) j
  simp only [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, he, ha]
  rfl

private theorem execute_eq_of_arrivalCoordinates
    (L M : List (RoundInput p.K))
    (h : L.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate) =
      M.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))
    (state : RecordedQueueRun.RunState p.K) :
    RecordedQueueRun.execute (queueParameters rate) L state =
      RecordedQueueRun.execute (queueParameters rate) M state := by
  induction L generalizing M state with
  | nil =>
      cases M with
      | nil => rfl
      | cons c M => simp at h
  | cons c L ih =>
      cases M with
      | nil => simp at h
      | cons d M =>
          simp only [List.map_cons, List.cons.injEq] at h
          simp only [RecordedQueueRun.execute]
          rw [step_eq_of_arrivalCoordinates rate state c d h.1]
          exact ih M h.2 _

private theorem mapM_map_coordinates {A B : Type*}
    (slots : List (Option A)) (f : A → B) :
    (slots.mapM id).map (List.map f) =
      (slots.map (Option.map f)).mapM id := by
  induction slots with
  | nil => rfl
  | cons c slots ih =>
      cases c with
      | none => simp [List.mapM_cons]
      | some c =>
          cases ht : slots.mapM id with
          | none => simp [List.mapM_cons, ← ih, ht]
          | some L => simp [List.mapM_cons, ← ih, ht]

private theorem optional_run_congr (L M : List (Option (RoundInput p.K)))
    (h : L.map (Option.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate)) =
      M.map (Option.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))) :
    (L.mapM id).map (fun cells => stateReadout (run (queueParameters rate) cells)) =
      (M.mapM id).map (fun cells => stateReadout (run (queueParameters rate) cells)) := by
  have he := congrArg (fun slots => slots.mapM id) h
  rw [← mapM_map_coordinates, ← mapM_map_coordinates] at he
  cases hL : L.mapM id with
  | none =>
      cases hM : M.mapM id with
      | none => rfl
      | some cells => simp only [hL, hM, Option.map_none, Option.map_some, reduceCtorEq] at he
  | some cells =>
      cases hM : M.mapM id with
      | none => simp only [hL, hM, Option.map_none, Option.map_some, reduceCtorEq] at he
      | some other =>
          simp only [hL, hM, Option.map_some, Option.some.injEq] at he
          have hrun := execute_eq_of_arrivalCoordinates rate cells other he
            (RecordedQueueRun.initialState p.K)
          exact congrArg (fun state => some (stateReadout state)) hrun

/-- Whole-carrier measurability in the strict pre-choice source field. Missing
launches and missing dated cells are included. Only the observation is coded;
the operational run and its real-vector input spaces are unchanged. -/
theorem prefixReadout_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (prefixReadout? rate rewards C_star C_h t) := by
  let : MeasurableSpace (SourceInput p) :=
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  have hentry : Measurable
      (fun e : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        e.2.2.map (Sum.elim id id)) :=
    measurable_option_map (fun e : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate => e.2.2)
      (measurable_snd.comp measurable_snd) _ (measurable_id.sumElim measurable_id)
  have hcoords : Measurable (fun z : SourceInput p =>
      (pastSlots rate rewards C_star C_h t z).map
        (Option.map ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates)) := by
    have h := ReferenceActiveHorizonMeasurability.measurable_list_map _
      (ReferenceCompleteObservationPrefixInformation.datePrefix_measurable
        rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt)) _ hentry
    convert h using 1
    funext z
    exact slotCoordinates_eq_datePrefix rate rewards C_star C_h t z
  have hmap : Measurable (fun c : Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
        c.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) :=
    measurable_option_map id measurable_id _
      (ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate)
  have harrivals : Measurable (fun z : SourceInput p =>
      (pastSlots rate rewards C_star C_h t z).map (Option.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate))) := by
    have h := ReferenceActiveHorizonMeasurability.measurable_list_map _ hcoords _ hmap
    simpa only [List.map_map, Option.map_map, Function.comp_def,
      ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates] using h
  let g := fun z : SourceInput p =>
    if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h t.val z then
      some ((pastSlots rate rewards C_star C_h t z).map (Option.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate)))
    else none
  have hg : Measurable g :=
    Measurable.ite (measurableSet_actualLaunchBy rate rewards C_star C_h control0 t)
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ harrivals)
      measurable_const
  apply measurable_of_countable_fibers g hg
  intro z y he
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · by_cases hy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h t.val y
    · simp only [g, ite_eq_left hz, ite_eq_left hy, Option.some.injEq] at he
      simp only [prefixReadout?, pastCells?, ite_eq_left hz, ite_eq_left hy]
      exact optional_run_congr rate _ _ he
    · simp only [g, ite_eq_left hz, ite_eq_right hy, reduceCtorEq] at he
  · by_cases hy : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h t.val y
    · simp only [g, ite_eq_right hz, ite_eq_left hy, reduceCtorEq] at he
    · simp only [prefixReadout?, pastCells?, ite_eq_right hz, ite_eq_right hy]

/-- The no-earlier-overflow set is predictable on the original source. -/
theorem measurableSet_H
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (H rate rewards C_star C_h t) := by
  let SR := (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))
  have htest : Measurable (fun v : Option SR => v.map (fun v => v.2.1)) :=
    measurable_option_map id measurable_id _ (measurable_fst.comp measurable_snd)
  have hm := htest.comp (prefixReadout_measurable rate rewards C_star C_h control0 t)
  have he : H rate rewards C_star C_h t =
      (fun z => (prefixReadout? rate rewards C_star C_h t z).map (fun v => v.2.1)) ⁻¹'
        {some false} := by
    ext z
    simp only [H, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    exact Option.map_eq_some_iff.symm
  rw [he]
  exact (MeasurableSet.singleton (some false)).preimage hm

/-- The original first-cell event intersected with the predictable retained test. -/
theorem measurableSet_G
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (G rate rewards C_star C_h u t) :=
  (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t).inter
      (measurableSet_H rate rewards C_star C_h control0 t)

end Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate
