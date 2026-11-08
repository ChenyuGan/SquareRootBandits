/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionRetainedMoment
public import Bandits.Support.ReferenceFirstCollectionCorrectedNumericalOverflowSum
public import Bandits.Support.ReferenceFirstCorrectedNativeUpComputedPrefixObservation

import Mathlib.Tactic

/-!
# Original-source numerical overflow through the first collection

This module extends the initialized numerical queue observation through the
actual first selected collection segment.  It preserves the old birth/live/
first-cutoff endpoint and uses the original source prefix and queue run.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:40-100,192-233,246-299,355-426`, and
`appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
  (correctedCell sourceRecords sourceStart birthIndex liveTail endDate prefixReadout)
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Readout" => ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K

local instance sourceInputMeasurableSpace : MeasurableSpace X := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionReadoutMeasurableSpace : MeasurableSpace (Option Readout) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace Readout

local instance optionReadoutMeasurableSingleton :
    MeasurableSingletonClass (Option Readout) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSingletonClass Readout

/-- Finite-calendar endpoint evaluation. The queue segment is selected only
by the actual first cutoff, and its length is read from the same source tags. -/
def collectionEndpointCodeEval (t : Fin p.T)
    (data : ℕ × (ℕ × ((Fin p.T → Bool) × ((Fin p.T → Bool) × (Fin p.T → ℕ))))) : ℕ := by
  let old := data.1
  let live := data.2.1
  let cutoff := data.2.2.1
  let completed := data.2.2.2.1
  let later := data.2.2.2.2
  let d := t.val + 1 + live
  exact if hd : d < p.T then
    let date : Fin p.T := ⟨d, hd⟩
    if cutoff date then
      max old (d + if completed date then 1 + later date else 0)
    else old
  else old

/-- The exclusive date through the actual selected cutoff's completed first
collection segment, retaining the original endpoint when no segment is present. -/
def collectionEndpoint (t : Fin p.T) (x : X) : ℕ :=
  collectionEndpointCodeEval t
    (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
        rate rewards C_star C_h t x,
      (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
          rate rewards C_star C_h t x,
        (fun q => ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
            rate rewards C_star C_h q x,
          (fun q => ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCompletedCollection
              rate rewards C_star C_h q x,
            fun q => ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
              rate rewards C_star C_h q x))))

theorem measurable_collectionEndpoint (t : Fin p.T) :
    Measurable (collectionEndpoint rate rewards C_star C_h t) := by
  apply (show Measurable (collectionEndpointCodeEval t) from Measurable.of_discrete).comp
  exact (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_endpointCode
      rate rewards C_star C_h t).prodMk
    ((ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_continuingLength
      rate rewards C_star C_h t).prodMk
      ((Measurable.of_eval fun q =>
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_horizonCutoff
          rate rewards C_star C_h q).prodMk
        ((Measurable.of_eval fun q =>
          ReferenceFirstCorrectedNativeUpComputedPrefixObservation.measurable_horizonCompletedCollection
            rate rewards C_star C_h q).prodMk
          (Measurable.of_eval fun q =>
            ReferenceFirstCorrectedNativeUpComputedPrefixObservation.measurable_collectionContinuingLength
              rate rewards C_star C_h q))))

theorem collectionEndpoint_ge_old (t : Fin p.T) (x : X) :
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
        rate rewards C_star C_h t x ≤ collectionEndpoint rate rewards C_star C_h t x := by
  simp only [collectionEndpoint, collectionEndpointCodeEval]
  split_ifs <;> first | exact Nat.le_max_left _ _ | rfl

private theorem collectionContinuingLength_le (q : Fin p.T) (x : X) :
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
      rate rewards C_star C_h q x ≤ p.T - (q.val + 1) := by
  unfold ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
  calc
    _ ≤ (List.ofFn fun i : Fin (p.T - (q.val + 1)) =>
        ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCollectionContinuing
          rate rewards C_star C_h ⟨q.val + 1 + i.val, by omega⟩ x).length :=
      (List.takeWhile_prefix _).length_le
    _ = p.T - (q.val + 1) := by simp

private theorem actualRecord_eq_sourceIndex (q : Fin p.T) (i : ℕ) (x : X)
    (hi : sourceStart rate rewards C_star C_h x + i = q.val) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q x =
      (sourceRecords rate rewards C_star C_h x)[i]? := by
  have hs : sourceStart rate rewards C_star C_h x ≤ q.val := by omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  change (if sourceStart rate rewards C_star C_h x ≤ q.val then
      (sourceRecords rate rewards C_star C_h x)[q.val -
        sourceStart rate rewards C_star C_h x]? else none) = _
  rw [ite_eq_left hs]
  have hindex : q.val - sourceStart rate rewards C_star C_h x = i := by omega
  rw [hindex]

private theorem horizonCutoff_eq_record (q : Fin p.T) (x : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q x = some r) :
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h q x = ReferenceCollectionPhaseHistory.cutoffChosen r.input := by
  unfold ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?
  simp only [hr, Option.map_some, Option.bind_some]
  unfold ReferenceFirstCollectionRenewalNextRecordingPriorView.dispatchTag
    ReferenceCollectionPhaseHistory.cutoffChosen
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.chosenCutoffTag
  have hp : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
      ReferenceActivePhysicalStep.dispatch r.input := rfl
  rw [hp]
  cases ReferenceActivePhysicalStep.dispatch r.input with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem horizonCompletedCollection_eq_record (q : Fin p.T) (x : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q x = some r) :
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCompletedCollection
      rate rewards C_star C_h q x =
        (ReferenceCollectionSegmentExtraction.extractRound r).isSome := by
  simp [ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCompletedCollection,
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?, hr,
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.extractRound_isSome_eq_outputCollectionTag
      rate r]

private theorem horizonCollectionContinuing_eq_record (q : Fin p.T) (x : X) (r : Record)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q x = some r) :
    ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCollectionContinuing
      rate rewards C_star C_h q x =
        ReferenceCollectionSegmentExtraction.continuing r := by
  simp only [ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCollectionContinuing,
    ReferenceFirstCollectionCorrectedNextPhysicalReadout.actualInput?, hr,
    Option.map_some, Option.elim_some]
  rw [ReferenceFirstCorrectedNativeUpComputedPrefixObservation.continuing_eq_collectionTags]

private theorem collectionFlags_actual (q : Fin p.T) (i : ℕ) (x : X)
    (hi : sourceStart rate rewards C_star C_h x + i = q.val) :
    (List.ofFn fun h : Fin (p.T - (q.val + 1)) =>
      ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCollectionContinuing
        rate rewards C_star C_h ⟨q.val + 1 + h.val, by omega⟩ x) =
      ((sourceRecords rate rewards C_star C_h x).drop (i + 1)).map
        ReferenceCollectionSegmentExtraction.continuing := by
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x rewards C_star C_h
  change (sourceRecords rate rewards C_star C_h x).length =
    p.T - sourceStart rate rewards C_star C_h x at hlen
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_drop]
    omega
  · intro h hh hh'
    have hhT : h < p.T - (q.val + 1) := by
      simpa only [List.length_ofFn] using hh
    let date : Fin p.T := ⟨q.val + 1 + h, by omega⟩
    have hlookup : i + 1 + h < (sourceRecords rate rewards C_star C_h x).length := by
      simp only [List.length_map, List.length_drop] at hh'
      omega
    have hr := actualRecord_eq_sourceIndex rate rewards C_star C_h date
      (i + 1 + h) x (by dsimp only [date]; omega)
    rw [List.getElem?_eq_getElem hlookup] at hr
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_drop]
    exact horizonCollectionContinuing_eq_record rate rewards C_star C_h date x _ hr

private theorem cutoff_choice (input : ReferenceActivePhysicalStep.RoundInput p rate)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen input = true) :
    ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
      ReferenceCollectionSegmentExtraction.choice input = some c ∧
        c.initializer.isSome = true := by
  unfold ReferenceCollectionPhaseHistory.cutoffChosen at hcut
  cases hd : (ReferenceActivePhysicalStep.prepare input).coordinator with
  | live registers owned base outcome =>
      cases outcome <;> simp only [hd, Bool.false_eq_true] at hcut
      next dispatched hstart ledger hinit heq hdomain hclock hpending hno selected =>
        have hselection : (ReferenceActivePhysicalStep.prepare input).coordinator.selection ≠ none := by
          simp [hd, ReferenceActivePhysicalStep.DispatchCut.selection,
            ReferenceActivePhysicalStep.selectionAt]
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [ite_eq_right hselection, hd]
        exact ⟨_, rfl, rfl⟩
  | first outcome => simp only [hd, Bool.false_eq_true] at hcut
  | collection payload ledger clock cutoff outcome => simp only [hd, Bool.false_eq_true] at hcut
  | invalidCollectionCutoff => simp only [hd, Bool.false_eq_true] at hcut
  | dagger => simp only [hd, Bool.false_eq_true] at hcut

private theorem segmentAt_cutoff_length (R : List Record) (i : ℕ) (entry : Record)
    (hr : R[i]? = some entry)
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true) :
    ∃ seg : ReferenceCollectionSegmentExtraction.Segment rate,
      ReferenceCollectionSegmentExtraction.segmentAt R i = some seg ∧
        seg.records.length = if (ReferenceCollectionSegmentExtraction.extractRound entry).isSome then
          1 + ((R.drop (i + 1)).takeWhile ReferenceCollectionSegmentExtraction.continuing).length
          else 0 := by
  classical
  obtain ⟨c, hc, hinit⟩ := cutoff_choice rate entry.input hcut
  have hi := (List.getElem?_eq_some_iff.mp hr).1
  have he := (List.getElem?_eq_some_iff.mp hr).2
  have hdrop : R.drop i = entry :: R.drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hi, he]
  unfold ReferenceCollectionSegmentExtraction.segmentAt
  rw [hdrop]
  simp only [ReferenceCollectionSegmentExtraction.segment, hc, Option.map_some]
  split
  · refine ⟨⟨entry, c, entry :: (R.drop (i + 1)).takeWhile
        ReferenceCollectionSegmentExtraction.continuing,
        (R.drop (i + 1)).dropWhile ReferenceCollectionSegmentExtraction.continuing⟩,
      ?_, ?_⟩
    · simp only [Option.bind_some, hinit, or_true, ↓reduceIte]
    · simp only [List.length_cons, Nat.add_comm]
  · refine ⟨⟨entry, c, [], entry :: R.drop (i + 1)⟩, ?_, rfl⟩
    simp only [Option.bind_some, hinit, or_true, ↓reduceIte]

/-- When the finite-calendar cutoff flag is set, it is the exact record at the
birth/live boundary, and the endpoint extension uses that record's own
`segmentAt` output. -/
theorem collectionEndpoint_eq_actualSegment_of_cutoff (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (hd : t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t x < p.T)
    (hcut : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h
        ⟨t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
          rate rewards C_star C_h t x, hd⟩ x = true) :
    ∃ entry seg,
      (sourceRecords rate rewards C_star C_h x)[birthIndex rate rewards C_star C_h x + 1 +
        (liveTail rate rewards C_star C_h x).length]? = some entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true ∧
      ReferenceCollectionSegmentExtraction.segmentAt
        (sourceRecords rate rewards C_star C_h x)
        (birthIndex rate rewards C_star C_h x + 1 + (liveTail rate rewards C_star C_h x).length) =
          some seg ∧
      collectionEndpoint rate rewards C_star C_h t x =
        max (endDate rate rewards C_star C_h t x)
          (sourceStart rate rewards C_star C_h x +
            (birthIndex rate rewards C_star C_h x + 1 +
              (liveTail rate rewards C_star C_h x).length) + seg.records.length) := by
  let R := sourceRecords rate rewards C_star C_h x
  let s := sourceStart rate rewards C_star C_h x
  let b := birthIndex rate rewards C_star C_h x
  let e := b + 1 + (liveTail rate rewards C_star C_h x).length
  let d := t.val + 1 +
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t x
  let q : Fin p.T := ⟨d, hd⟩
  have hbirth := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t x hx
  have hlive := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength_actual
    rate rewards C_star C_h u t x hx
  have hde : s + e = d := by
    dsimp only [s, e, d]
    rw [← hlive]
    omega
  have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate x rewards C_star C_h
  change R.length = p.T - s at hRlen
  have he : e < R.length := by dsimp only [e]; rw [hRlen]; omega
  let entry : Record := R[e]
  have hentry : R[e]? = some entry := List.getElem?_eq_getElem he
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h q x = some entry := by
    rw [actualRecord_eq_sourceIndex rate rewards C_star C_h q e x (by
      dsimp only [q]
      exact hde)]
    exact hentry
  have hcutRecord := horizonCutoff_eq_record rate rewards C_star C_h q x entry hrecord
  have hcut' : ReferenceCollectionPhaseHistory.cutoffChosen entry.input = true := by
    rw [← hcutRecord]
    exact hcut
  obtain ⟨seg, hseg, hsegLen⟩ := segmentAt_cutoff_length rate R e entry hentry hcut'
  have hcomplete := horizonCompletedCollection_eq_record rate rewards C_star C_h q x entry hrecord
  have hflags := collectionFlags_actual rate rewards C_star C_h q e x (by
    dsimp only [q]
    exact hde)
  have htake : ∀ xs : List Record,
      (List.takeWhile id (xs.map ReferenceCollectionSegmentExtraction.continuing)).length =
        (List.takeWhile ReferenceCollectionSegmentExtraction.continuing xs).length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih =>
        by_cases h : ReferenceCollectionSegmentExtraction.continuing a = true
        · simp [List.takeWhile, h, ih]
        · simp [List.takeWhile, h]
  have hcontinueLen :
      ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
        rate rewards C_star C_h q x =
        ((R.drop (e + 1)).takeWhile ReferenceCollectionSegmentExtraction.continuing).length := by
    unfold ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
    rw [hflags]
    exact htake _
  have hsegmentCode :
      (if ReferenceFirstCorrectedNativeUpComputedPrefixObservation.horizonCompletedCollection
          rate rewards C_star C_h q x then
        1 + ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
          rate rewards C_star C_h q x else 0) = seg.records.length := by
    rw [hcomplete, hcontinueLen, hsegLen]
  have hcode :=
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
      rate rewards C_star C_h u t x hx
  have hvalue : collectionEndpoint rate rewards C_star C_h t x =
      max (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
          rate rewards C_star C_h t x) (d + seg.records.length) := by
    simp [collectionEndpoint, collectionEndpointCodeEval, d, q, hd, hcut, hsegmentCode]
  refine ⟨entry, seg, hentry, hcut', hseg, ?_⟩
  rw [hvalue, hcode, ← hde]

theorem collectionEndpoint_eq_old_of_no_cutoff (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t)
    (hd : t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t x < p.T)
    (hcut : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h
        ⟨t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
          rate rewards C_star C_h t x, hd⟩ x = false) :
    collectionEndpoint rate rewards C_star C_h t x = endDate rate rewards C_star C_h t x := by
  rw [← ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
    rate rewards C_star C_h u t x hx]
  dsimp [collectionEndpoint, collectionEndpointCodeEval]
  simp [hd, hcut]

theorem collectionEndpoint_eq_old_at_horizon (t : Fin p.T) (x : X)
    (hd : ¬ t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t x < p.T) :
    collectionEndpoint rate rewards C_star C_h t x =
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
        rate rewards C_star C_h t x := by
  dsimp [collectionEndpoint, collectionEndpointCodeEval]
  simp [hd]

theorem collectionEndpoint_bounds (u t : Fin p.T) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    t.val + 1 ≤ collectionEndpoint rate rewards C_star C_h t x ∧
      collectionEndpoint rate rewards C_star C_h t x ≤ p.T := by
  have hold := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
    rate rewards C_star C_h u t x hx
  have hcode :=
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
      rate rewards C_star C_h u t x hx
  have hOldLo : t.val + 1 ≤
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
        rate rewards C_star C_h t x := by rw [hcode]; exact hold.1
  have hOldHi :
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
        rate rewards C_star C_h t x ≤ p.T := by rw [hcode]; exact hold.2
  let d := t.val + 1 +
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t x
  dsimp [collectionEndpoint, collectionEndpointCodeEval]
  split_ifs with hd hc hcomplete
  · constructor
    · exact hOldLo.trans (Nat.le_max_left _ _)
    · apply max_le hOldHi
      have hlen := collectionContinuingLength_le rate rewards C_star C_h
        ⟨t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
          rate rewards C_star C_h t x, hd⟩ x
      have hlen' : ReferenceFirstCorrectedNativeUpComputedPrefixObservation.collectionContinuingLength
          rate rewards C_star C_h
            ⟨t.val + 1 + ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
              rate rewards C_star C_h t x, hd⟩ x ≤
          p.T - (t.val + 1 +
            ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
              rate rewards C_star C_h t x + 1) := by
        simpa only [Fin.val_mk] using hlen
      omega
  · constructor
    · exact hOldLo.trans (Nat.le_max_left _ _)
    · exact max_le hOldHi (by omega)
  · exact ⟨hOldLo, hOldHi⟩
  · exact ⟨hOldLo, hOldHi⟩

/-- The literal arm threshold event through the extended first-segment
endpoint, using the unchanged initialized source prefix. -/
def collectionOverflowEvent (u t : Fin p.T) (a : Fin p.K) : Set X :=
  {x | x ∈ correctedCell rate rewards C_star C_h u t ∧
    ∃ n, t.val + 1 ≤ n ∧ n ≤ collectionEndpoint rate rewards C_star C_h t x ∧
      ∃ o : Readout, prefixReadout rate rewards C_star C_h n x = some o ∧
        ((o.1 a).2 : ℝ) / ((Q).n : ℝ) > 1 / (32 * rate.eta.val)}

theorem measurableSet_collectionOverflowEvent (u t : Fin p.T) (a : Fin p.K) :
    MeasurableSet (collectionOverflowEvent rate rewards C_star C_h u t a) := by
  have hcell := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurableSet_correctedCell
    rate rewards C_star C_h u t
  have he := measurable_collectionEndpoint rate rewards C_star C_h t
  have hr (n : ℕ) := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
    rate rewards C_star C_h n
  have hrepresentation : collectionOverflowEvent rate rewards C_star C_h u t a =
      correctedCell rate rewards C_star C_h u t ∩
        ⋃ n : ℕ, ⋃ o : Readout,
          if t.val + 1 ≤ n ∧ 1 / (32 * rate.eta.val) < ((o.1 a).2 : ℝ) / ((Q).n : ℝ)
          then {x | n ≤ collectionEndpoint rate rewards C_star C_h t x} ∩
            {x | prefixReadout rate rewards C_star C_h n x = some o} else ∅ := by
    ext x
    simp only [collectionOverflowEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hc, n, hn, he, o, ho, hcap⟩
      refine ⟨hc, n, o, ?_⟩
      rw [ite_eq_left ⟨hn, hcap⟩]
      exact ⟨he, ho⟩
    · rintro ⟨hc, n, o, h⟩
      split_ifs at h with htest
      · exact ⟨hc, n, htest.1, h.1, o, h.2, htest.2⟩
      · exact (Set.notMem_empty x h).elim
  rw [hrepresentation]
  refine hcell.inter (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun o => ?_)
  split_ifs
  · exact (measurableSet_le measurable_const he).inter
      ((hr n) (measurableSet_singleton (some o)))
  · exact MeasurableSet.empty

/-- The extended event retains every crossing in the inherited old window. -/
theorem oldOverflowEvent_subset_collectionOverflowEvent (u t : Fin p.T)
    (a : Fin p.K) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.overflowEvent
        rate rewards C_star C_h u t a ⊆
      collectionOverflowEvent rate rewards C_star C_h u t a := by
  rintro x ⟨hx, n, hn, hne, o, ho, hcross⟩
  have hend := collectionEndpoint_ge_old rate rewards C_star C_h t x
  rw [ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
    rate rewards C_star C_h u t x hx] at hend
  exact ⟨hx, n, hn, hne.trans hend, o, ho, hcross⟩

/-- Clamp an observation to the unchanged birth boundary and the exclusive
endpoint of the same actual first collection segment. -/
def collectionClampedIndex (t : Fin p.T) (n : ℕ) (x : X) : ℕ :=
  min (max (t.val + 1) n) (collectionEndpoint rate rewards C_star C_h t x)

theorem collectionClampedIndex_bounds (u t : Fin p.T) (n : ℕ) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    t.val + 1 ≤ collectionClampedIndex rate rewards C_star C_h t n x ∧
      collectionClampedIndex rate rewards C_star C_h t n x ≤
        collectionEndpoint rate rewards C_star C_h t x := by
  have he := collectionEndpoint_bounds rate rewards C_star C_h u t x hx
  exact ⟨le_min (le_max_left _ _) he.1, min_le_right _ _⟩

theorem measurable_collectionClampedIndex (t : Fin p.T) (n : ℕ) :
    Measurable (collectionClampedIndex rate rewards C_star C_h t n) := by
  exact (measurable_of_countable (fun e : ℕ => min (max (t.val + 1) n) e)).comp
    (measurable_collectionEndpoint rate rewards C_star C_h t)

/-- Scalar energy of an actual optional readout; an absent readout remains
absent in `prefixReadout` and contributes zero without creating a queue state. -/
def collectionReadoutEnergy (a : Fin p.K) (o : Readout) : ℝ :=
  Real.exp (beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ))

/-- The stopped energy reads the original initialized prefix at the extended
actual endpoint. Outside the corrected cell it is zero; missing prefix cells
remain `none` in the underlying source observation. -/
def collectionStoppedEnergy (u t : Fin p.T) (a : Fin p.K)
    (n : ℕ) (x : X) : ℝ :=
  if _hx : x ∈ correctedCell rate rewards C_star C_h u t then
    (prefixReadout rate rewards C_star C_h
      (collectionClampedIndex rate rewards C_star C_h t n x) x).elim 0
        (collectionReadoutEnergy rate a)
  else 0

/-- The actual adjacent extended stopped-energy difference. -/
def collectionEnergyIncrement (u t : Fin p.T) (a : Fin p.K)
    (q : Fin p.T) (x : X) : ℝ :=
  collectionStoppedEnergy rate rewards C_star C_h u t a (q.val + 1) x -
    collectionStoppedEnergy rate rewards C_star C_h u t a q.val x

theorem measurable_collectionStoppedEnergy (u t : Fin p.T) (a : Fin p.K)
    (n : ℕ) : Measurable (collectionStoppedEnergy rate rewards C_star C_h u t a n) := by
  have hjoint : Measurable (fun z : ℕ × X => prefixReadout rate rewards C_star C_h z.1 z.2) :=
    measurable_from_prod_countable_right
      (fun k => ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurable_prefixReadout
        rate rewards C_star C_h k)
  have hindex := measurable_collectionClampedIndex rate rewards C_star C_h t n
  have hobs := hjoint.comp (hindex.prodMk measurable_id)
  have hscalar : Measurable (fun o : Option Readout =>
      o.elim 0 (collectionReadoutEnergy rate a)) := measurable_of_countable _
  exact Measurable.ite
    (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.measurableSet_correctedCell
      rate rewards C_star C_h u t) (hscalar.comp hobs) measurable_const

theorem measurable_collectionEnergyIncrement (u t : Fin p.T) (a : Fin p.K)
    (q : Fin p.T) : Measurable (collectionEnergyIncrement rate rewards C_star C_h u t a q) :=
  (measurable_collectionStoppedEnergy rate rewards C_star C_h u t a (q.val + 1)).sub
    (measurable_collectionStoppedEnergy rate rewards C_star C_h u t a q.val)

theorem collectionStoppedEnergy_eq_old (u t : Fin p.T) (a : Fin p.K)
    (n : ℕ) (z : X) (hn : n ≤ endDate rate rewards C_star C_h t z) :
    collectionStoppedEnergy rate rewards C_star C_h u t a n z =
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
        rate rewards C_star C_h u t a n z := by
  by_cases hx : z ∈ correctedCell rate rewards C_star C_h u t
  · have hb := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
      rate rewards C_star C_h u t z hx
    have hold := collectionEndpoint_ge_old rate rewards C_star C_h t z
    rw [ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
      rate rewards C_star C_h u t z hx] at hold
    have hmax : max (t.val + 1) n ≤ endDate rate rewards C_star C_h t z := max_le hb.1 hn
    obtain ⟨L, _hL, _hlen, hread⟩ :=
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
        rate rewards C_star C_h u t z hx (max (t.val + 1) n) (le_max_left _ _) hmax
    have hclamp : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.clampedIndex
        rate rewards C_star C_h t n z = max (t.val + 1) n := min_eq_left hmax
    have hget : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.clampedReadout
        rate rewards C_star C_h u t n ⟨z, hx⟩ =
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (RecordedQueueRun.run Q L) := by
      unfold ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.clampedReadout
      apply Option.get_of_eq_some
      simpa only [hclamp] using hread
    simp only [collectionStoppedEnergy, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy,
      dite_eq_left hx, collectionClampedIndex, min_eq_left (hmax.trans hold), hread, Option.elim_some, hget]
    rfl
  · simp only [collectionStoppedEnergy, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy,
      dite_eq_right hx]

/-- The extended observation preserves the inherited energy just after birth. -/
theorem collectionStoppedEnergy_birth_eq_old (u t : Fin p.T) (a : Fin p.K) (x : X)
    (hx : x ∈ correctedCell rate rewards C_star C_h u t) :
    collectionStoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x =
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
        rate rewards C_star C_h u t a (t.val + 1) x := by
  exact collectionStoppedEnergy_eq_old rate rewards C_star C_h u t a (t.val + 1) x
    (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
      rate rewards C_star C_h u t x hx).1

theorem collectionStoppedEnergy_bounds (u t : Fin p.T) (a : Fin p.K)
    (n : ℕ) (x : X) :
    0 ≤ collectionStoppedEnergy rate rewards C_star C_h u t a n x ∧
      collectionStoppedEnergy rate rewards C_star C_h u t a n x ≤
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyCeiling rate := by
  by_cases hx : x ∈ correctedCell rate rewards C_star C_h u t
  · cases hread : prefixReadout rate rewards C_star C_h
        (collectionClampedIndex rate rewards C_star C_h t n x) x with
    | none =>
        simp only [collectionStoppedEnergy, dite_eq_left hx, hread, Option.elim_none]
        exact ⟨le_rfl, (Real.exp_pos _).le⟩
    | some o =>
        have hbound := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.prefixReadout_backlog_bounds
          rate rewards C_star C_h _ x o hread a
        simp only [collectionStoppedEnergy, dite_eq_left hx, hread, Option.elim_some]
        refine ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr ?_⟩
        change beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ) ≤ beta * (2 * (1 / (32 * rate.eta.val)))
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hbound.2
          (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  · simp only [collectionStoppedEnergy, dite_eq_right hx]
    exact ⟨le_rfl, (Real.exp_pos _).le⟩

theorem collectionEnergyIncrement_abs_le (u t : Fin p.T) (a : Fin p.K)
    (q : Fin p.T) (x : X) :
    |collectionEnergyIncrement rate rewards C_star C_h u t a q x| ≤
      2 * ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyCeiling rate := by
  have hnext := collectionStoppedEnergy_bounds rate rewards C_star C_h u t a (q.val + 1) x
  have hprior := collectionStoppedEnergy_bounds rate rewards C_star C_h u t a q.val x
  calc
    _ ≤ |collectionStoppedEnergy rate rewards C_star C_h u t a (q.val + 1) x| +
        |collectionStoppedEnergy rate rewards C_star C_h u t a q.val x| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg hnext.1, abs_of_nonneg hprior.1]
      linarith [hnext.2, hprior.2]

theorem integrable_collectionStoppedEnergy (u t : Fin p.T) (a : Fin p.K)
    (n : ℕ) : Integrable (collectionStoppedEnergy rate rewards C_star C_h u t a n)
      (sourceInputLaw p) := by
  have hconst : Integrable
      (fun _ : X => ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyCeiling rate)
      (sourceInputLaw p) := integrable_const _
  refine hconst.mono'
    (measurable_collectionStoppedEnergy rate rewards C_star C_h u t a n).aestronglyMeasurable ?_
  filter_upwards [] with x
  have hb := collectionStoppedEnergy_bounds rate rewards C_star C_h u t a n x
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem integrable_collectionEnergyIncrement (u t : Fin p.T) (a : Fin p.K)
    (q : Fin p.T) : Integrable (collectionEnergyIncrement rate rewards C_star C_h u t a q)
      (sourceInputLaw p) :=
  (integrable_collectionStoppedEnergy rate rewards C_star C_h u t a (q.val + 1)).sub
    (integrable_collectionStoppedEnergy rate rewards C_star C_h u t a q.val)

/-- Finite horizon telescope for the extended actual-prefix energy, including
the terminal birth case without constructing a successor date. -/
theorem collectionStoppedEnergy_telescope (u t : Fin p.T) (a : Fin p.K) (x : X) :
    collectionStoppedEnergy rate rewards C_star C_h u t a p.T x =
      collectionStoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x +
        ∑ q : Fin p.T, collectionEnergyIncrement rate rewards C_star C_h u t a q x := by
  have hsum : (∑ q : Fin p.T, collectionEnergyIncrement rate rewards C_star C_h u t a q x) =
      collectionStoppedEnergy rate rewards C_star C_h u t a p.T x -
        collectionStoppedEnergy rate rewards C_star C_h u t a 0 x := by
    unfold collectionEnergyIncrement
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      collectionStoppedEnergy rate rewards C_star C_h u t a (k + 1) x -
        collectionStoppedEnergy rate rewards C_star C_h u t a k x) p.T]
    exact Finset.sum_range_sub (fun k => collectionStoppedEnergy rate rewards C_star C_h u t a k x) p.T
  rw [hsum]
  have hzero : collectionStoppedEnergy rate rewards C_star C_h u t a 0 x =
      collectionStoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x := by
    simp only [collectionStoppedEnergy, collectionClampedIndex, max_zero, max_self]
  rw [hzero]
  ring

theorem integral_collectionStoppedEnergy_telescope (u t : Fin p.T) (a : Fin p.K) :
    (∫ x, collectionStoppedEnergy rate rewards C_star C_h u t a p.T x ∂sourceInputLaw p) =
      (∫ x, collectionStoppedEnergy rate rewards C_star C_h u t a (t.val + 1) x
        ∂sourceInputLaw p) +
        ∑ q : Fin p.T,
          ∫ x, collectionEnergyIncrement rate rewards C_star C_h u t a q x ∂sourceInputLaw p := by
  simp_rw [collectionStoppedEnergy_telescope rate rewards C_star C_h u t a]
  rw [integral_add (integrable_collectionStoppedEnergy rate rewards C_star C_h u t a (t.val + 1))
    (integrable_finsetSum Finset.univ fun q _ =>
      integrable_collectionEnergyIncrement rate rewards C_star C_h u t a q),
    integral_finsetSum Finset.univ fun q _ =>
      integrable_collectionEnergyIncrement rate rewards C_star C_h u t a q]

private theorem exp_reflectedIncrement_le (b e d : ℝ) :
    Real.exp (b * max (e + d) 0) - Real.exp (b * e) ≤
      1 + Real.exp (b * e) * (Real.exp (b * d) - 1) := by
  have h := CanonicalQueueProcess.exp_mul_max_le e d b
  linarith only [h]

private theorem liveTail_eq_continuingPrefix (z : X) :
    liveTail rate rewards C_star C_h z =
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z (birthIndex rate rewards C_star C_h z + 1) := by
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
  congr 1
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem initialized_segment_cutoff (R : List Record) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (I : ReferenceCollectionSegmentExtraction.Initializer p)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
    (hinit : seg.context.initializer = some I) :
    R[e]? = some seg.entry ∧
      ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true := by
  have hs := (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hseg).1
  have hd : R.drop e ≠ [] := by
    intro h
    simp only [h, ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hs
  have he : e < R.length := by
    by_contra hn
    exact hd (List.drop_eq_nil_iff.mpr (by omega))
  rw [List.drop_eq_getElem_cons he] at hs
  unfold ReferenceCollectionSegmentExtraction.segment at hs
  cases hc : ReferenceCollectionSegmentExtraction.choice (R[e]).input with
  | none => simp only [hc, Option.map_none, reduceCtorEq] at hs
  | some c =>
      simp only [hc, Option.map_some] at hs
      have hentry : seg.entry = R[e] := by split at hs <;> cases Option.some.inj hs <;> rfl
      have hcontext : seg.context = c := by split at hs <;> cases Option.some.inj hs <;> rfl
      refine ⟨by rw [hentry]; exact List.getElem?_eq_getElem he, ?_⟩
      rw [hentry]
      rw [hcontext] at hinit
      unfold ReferenceCollectionSegmentExtraction.choice at hc
      split at hc
      · contradiction
      · unfold ReferenceCollectionPhaseHistory.cutoffChosen
        cases hdispatch : (ReferenceActivePhysicalStep.prepare (R[e]).input).coordinator with
        | live registers owned base outcome =>
            cases outcome <;>
              simp only [hdispatch, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
            all_goals first | contradiction | rfl
        | first outcome =>
            cases outcome <;>
              simp only [hdispatch, ReferenceCollectionSegmentExtraction.choiceOfCut,
                reduceCtorEq] at hc
        | collection payload ledger clock cutoff outcome =>
            cases outcome <;>
              simp only [hdispatch, ReferenceCollectionSegmentExtraction.choiceOfCut] at hc
            all_goals first | contradiction | (cases Option.some.inj hc; contradiction)
        | invalidCollectionCutoff =>
            simp only [hdispatch, ReferenceCollectionSegmentExtraction.choiceOfCut,
              reduceCtorEq] at hc
        | dagger =>
            simp only [hdispatch, ReferenceCollectionSegmentExtraction.choiceOfCut,
              reduceCtorEq] at hc

private theorem segment_continuing_slot (R : List Record) (e : ℕ)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt R e = some seg)
    (j : ℕ) (hj0 : 0 < j) (hj : j < seg.records.length) :
    ReferenceCollectionSegmentExtraction.continuing seg.records[j] = true := by
  have hs := (ReferenceCollectionSegmentExtraction.segmentAt_branch R e seg hseg).1
  cases hd : R.drop e with
  | nil => simp only [hd, ReferenceCollectionSegmentExtraction.segment, reduceCtorEq] at hs
  | cons entry rest =>
      rw [hd] at hs
      unfold ReferenceCollectionSegmentExtraction.segment at hs
      cases hc : ReferenceCollectionSegmentExtraction.choice entry.input with
      | none => simp only [hc, Option.map_none, reduceCtorEq] at hs
      | some c =>
          simp only [hc, Option.map_some] at hs
          split at hs
          · cases Option.some.inj hs
            have hj' : j - 1 < (rest.takeWhile ReferenceCollectionSegmentExtraction.continuing).length := by
              simp only [List.length_cons] at hj
              omega
            have hv : (entry :: rest.takeWhile ReferenceCollectionSegmentExtraction.continuing)[j] =
                (rest.takeWhile ReferenceCollectionSegmentExtraction.continuing)[j - 1] := by
              cases j with
              | zero => omega
              | succ k => rfl
            rw [hv]
            exact List.mem_takeWhile_imp (List.getElem_mem hj')
          · cases Option.some.inj hs
            simp only [List.length_nil] at hj
            omega

private theorem continuing_collection_data (r : Record)
    (done : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hdone : ReferenceCollectionSegmentExtraction.extractRound r = some done)
    (hcont : ReferenceCollectionSegmentExtraction.continuing r = true) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool)),
      r.input.state.coordinator = .collection payload ledger saved ∧
      done.context.payload = payload ∧ ledger.pending.Nonempty := by
  have htags := ReferenceFirstCorrectedNativeUpComputedPrefixObservation.continuing_eq_collectionTags rate r
  rw [hcont] at htags
  have hin := (Bool.and_eq_true_iff.mp htags.symm).1
  rw [ReferenceFirstCorrectedNativeUpComputedPrefixObservation.inputCollectionTag_eq_configuration] at hin
  have hchoice := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked r done hdone).1
  cases hstate : r.input.state.coordinator with
  | first => simp [hstate, ReferenceFirstCorrectedNativeUpComputedPrefixObservation.configurationCollectionTag] at hin
  | live registers owned base =>
      simp [hstate, ReferenceFirstCorrectedNativeUpComputedPrefixObservation.configurationCollectionTag] at hin
  | dagger => simp [hstate, ReferenceFirstCorrectedNativeUpComputedPrefixObservation.configurationCollectionTag] at hin
  | collection payload ledger saved =>
      refine ⟨payload, ledger, saved, rfl, ?_⟩
      unfold ReferenceCollectionSegmentExtraction.choice at hchoice
      split at hchoice
      · contradiction
      · change ReferenceCollectionSegmentExtraction.choiceOfCut
          (ReferenceActivePhysicalStep.dispatch r.input) = some done.context at hchoice
        simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hchoice
        split at hchoice
        next hcut =>
          let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
          change ReferenceCollectionSegmentExtraction.choiceOfCut
            (.collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock cutoff))) =
            some done.context at hchoice
          cases hout : CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock cutoff) <;>
            simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hout] at hchoice
          all_goals try contradiction
          next core snapshot hcontinue selected =>
            have hctx := Option.some.inj hchoice
            exact ⟨(congrArg (fun c : ReferenceCollectionSegmentExtraction.Choice rate => c.payload)
              hctx).symm, snapshot.inputsValid.pending_nonempty⟩
        next => contradiction

private theorem collectionEndpoint_initialized_segment (u t : Fin p.T) (z : X)
    (hx : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : ReferenceCollectionSegmentExtraction.Segment rate)
    (I : ReferenceCollectionSegmentExtraction.Initializer p)
    (hseg : ReferenceCollectionSegmentExtraction.segmentAt
      (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) =
        some seg)
    (hinit : seg.context.initializer = some I) :
    endDate rate rewards C_star C_h t z = sourceStart rate rewards C_star C_h z +
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) + 1 ∧
    collectionEndpoint rate rewards C_star C_h t z =
      max (endDate rate rewards C_star C_h t z)
        (sourceStart rate rewards C_star C_h z +
          (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) +
            seg.records.length) := by
  obtain ⟨hentry, hcut⟩ := initialized_segment_cutoff rate _ _ seg I hseg hinit
  have hbt := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_birth_time
    rate rewards C_star C_h u t z hx
  have hlive := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength_actual
    rate rewards C_star C_h u t z hx
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
    rate z rewards C_star C_h
  change (sourceRecords rate rewards C_star C_h z).length =
    p.T - sourceStart rate rewards C_star C_h z at hlen
  have he := (List.getElem?_eq_some_iff.mp hentry).1
  have hd : t.val + 1 +
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
        rate rewards C_star C_h t z < p.T := by rw [hlive]; omega
  let date : Fin p.T := ⟨t.val + 1 +
    ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
      rate rewards C_star C_h t z, hd⟩
  have hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h date z = some seg.entry := by
    rw [actualRecord_eq_sourceIndex rate rewards C_star C_h date
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length)
      z (by dsimp only [date]; rw [hlive]; omega)]
    exact hentry
  have hflag : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h date z = true :=
    (horizonCutoff_eq_record rate rewards C_star C_h date z seg.entry hrecord).trans hcut
  obtain ⟨entry', seg', _hentry', _hcut', hseg', hend⟩ :=
    collectionEndpoint_eq_actualSegment_of_cutoff rate rewards C_star C_h u t z hx hd hflag
  have hsame : seg' = seg := Option.some.inj (hseg'.symm.trans hseg)
  subst seg'
  have hcode : ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
      rate rewards C_star C_h t z = t.val + 1 +
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
          rate rewards C_star C_h t z + 1 := by
    unfold ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
    dsimp only
    rw [dite_eq_left hd]
    change _ + (if ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.horizonCutoff
      rate rewards C_star C_h date z then 1 else 0) = _
    rw [hflag, ite_eq_left rfl]
  refine ⟨?_, hend⟩
  calc
    _ = ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode
        rate rewards C_star C_h t z :=
      (ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
        rate rewards C_star C_h u t z hx).symm
    _ = t.val + 1 + (liveTail rate rewards C_star C_h z).length + 1 := by rw [hcode, hlive]
    _ = _ := by omega

/-- Every causal continuing-collection update belongs to the same actual
completed segment used by the endpoint. This does not classify index zero. -/
theorem collectionCausal_endpoint_coverage (u t q : Fin p.T)
    (htq : t.val < q.val) (z : X)
    (hg : ReferenceFirstCorrectedCollectionCausalReadout.firstCollectionCausalGate
      rate rewards C_star C_h u t q z) :
    endDate rate rewards C_star C_h t z ≤ q.val ∧
      q.val + 1 ≤ collectionEndpoint rate rewards C_star C_h t z := by
  obtain ⟨L0, c0, B, D, birth, payload, seg, I, _hL0, _hc0, _hbase,
      _hLlen, hbt, _hb, _hborn, _hB, _hword, _hBcells, hseg, _hpay,
      hinit, _hIsigma, _hIcut, _hpartition, hD, _hjpos, hj, hq,
      _hDcells, _hprefix, _hcell, _hprior, _hnext, _hstep⟩ :=
    ReferenceFirstCorrectedCollectionRetainedMoment.collectionCell_dated_word
      rate rewards C_star C_h u t q htq z hg
  rw [← liveTail_eq_continuingPrefix rate rewards C_star C_h z] at hseg hj hq
  change ReferenceCollectionSegmentExtraction.segmentAt
    (sourceRecords rate rewards C_star C_h z)
    (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) =
      some seg at hseg
  obtain ⟨hold, hend⟩ := collectionEndpoint_initialized_segment
    rate rewards C_star C_h u t z hg.1 seg I hseg hinit
  change D.length = seg.records.length at hD
  rw [← liveTail_eq_continuingPrefix rate rewards C_star C_h z] at _hjpos
  rw [hold, hend]
  constructor
  · omega
  · apply le_trans _ (Nat.le_max_right _ _)
    omega

/-- Every newly included date is an actual continuing cell of this same
first collection. The first cutoff remains entirely in the old window. -/
theorem collectionCausal_of_new_date (u t q : Fin p.T) (z : X)
    (hx : z ∈ correctedCell rate rewards C_star C_h u t)
    (hold : endDate rate rewards C_star C_h t z ≤ q.val)
    (hnew : q.val < collectionEndpoint rate rewards C_star C_h t z) :
    ReferenceFirstCorrectedCollectionCausalReadout.firstCollectionCausalGate
      rate rewards C_star C_h u t q z := by
  have hb := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
    rate rewards C_star C_h u t z hx
  have htq : t.val + 1 < p.T := by omega
  obtain ⟨L0, c0, birth, _hL0, _hc0, _hbase, _hLlen, hbt, _hb, _ht,
      _hrows, _hJ, _hrewards, _he0, _hlive0, _hcell0, _hout, hnum⟩ :=
    ReferenceFirstCorrectedCollectionCalendarNumericalJoin.firstCell_collection_calendar_numerical_values
      rate rewards C_star C_h u t z hx
  obtain ⟨birth', rout, qout, base, _hb', _hbt, _hdate0, _hrows0, _hJ0,
      _hrewards0, _hborn0, hsigma, _hlater0, hnext, _htail0⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hx
  have hbirthEq : birth' = birth := Option.some.inj (_hb'.symm.trans _hb)
  subst birth'
  obtain ⟨_hsigmaNum, hnum⟩ := hnum rout qout base hnext
  obtain ⟨hk, hstate, hlater, hnum⟩ := hnum htq
  obtain ⟨_hB, _helen, _hT, _hAlen, hde, _hA, _hbirthW, _hBcells,
      rE, qE, _hpE, _hinE, hcase⟩ := hnum
  have hlive := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength_actual
    rate rewards C_star C_h u t z hx
  rw [liveTail_eq_continuingPrefix rate rewards C_star C_h z] at hlive
  rcases hcase with hterminal | ⟨he, seg, I, l0, hseg, _hentry,
      _hpay, _hpre, hinit, _hI, _hchecked, _harm, _hIsigma, _hIcut,
      _htrue, _hfreeze, _hbase0, _hchosen, _hnonempty, hpartition,
      D, hD, hDcells, _hraw, _hG, _hq, _hqT, _hRtake, _hfull, _hrest⟩
  · have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    have hd : ¬ t.val + 1 +
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.continuingLength
          rate rewards C_star C_h t z < p.T := by rw [hlive]; omega
    have hend := collectionEndpoint_eq_old_at_horizon rate rewards C_star C_h t z hd
    rw [ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.endpointCode_actual
      rate rewards C_star C_h u t z hx] at hend
    omega
  · rw [← liveTail_eq_continuingPrefix rate rewards C_star C_h z] at hseg hpartition
    obtain ⟨holdEq, hendEq⟩ := collectionEndpoint_initialized_segment
      rate rewards C_star C_h u t z hx seg I hseg hinit
    let e := birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length
    let s := sourceStart rate rewards C_star C_h z
    let j := q.val - s - e
    change seg.records ++ seg.remaining = (sourceRecords rate rewards C_star C_h z).drop e at hpartition
    have hj0 : 0 < j := by dsimp only [j, s, e]; omega
    have hj : j < seg.records.length := by
      rw [hendEq] at hnew
      dsimp only [j, s, e]
      omega
    have hdate : s + e + j = q.val := by dsimp only [s, e, j]; omega
    let record := seg.records[j]
    have hlookup : (sourceRecords rate rewards C_star C_h z)[e + j]? = some record := by
      have hh : ((sourceRecords rate rewards C_star C_h z).drop e)[j]? = some record := by
        rw [← hpartition, List.getElem?_append_left hj]
        exact List.getElem?_eq_getElem hj
      simpa only [List.getElem?_drop] using hh
    have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h q z = some record := by
      rw [actualRecord_eq_sourceIndex rate rewards C_star C_h q (e + j) z (by omega)]
      exact hlookup
    obtain ⟨done, hdone, _hunoccupied, _hread, hpay, _hframe⟩ := (hDcells ⟨j, hj⟩).2
    have hcont := segment_continuing_slot rate _ _ seg hseg j hj0 hj
    obtain ⟨payload, ledger, saved, hcoord, hpayload, hpending⟩ :=
      continuing_collection_data rate record done hdone hcont
    refine ⟨hx, (ReferenceFirstCorrectedCollectionCausalReadout.incomingCollectionTag_spec
      rate rewards C_star C_h t q z).mpr ⟨record, payload, ledger, saved, hr, hcoord, ?_, hpending⟩⟩
    rw [← hpayload, hpay, hsigma]

theorem collectionStoppedEnergy_eq_readout (u t : Fin p.T) (a : Fin p.K)
    (n : ℕ) (z : X) (hx : z ∈ correctedCell rate rewards C_star C_h u t)
    (hn : t.val + 1 ≤ n) (hne : n ≤ collectionEndpoint rate rewards C_star C_h t z) :
    collectionStoppedEnergy rate rewards C_star C_h u t a n z =
      (prefixReadout rate rewards C_star C_h n z).elim 0 (collectionReadoutEnergy rate a) := by
  simp only [collectionStoppedEnergy, dite_eq_left hx, collectionClampedIndex,
    max_eq_right hn, min_eq_left hne]

theorem collectionEnergyIncrement_eq_zero (u t : Fin p.T) (a : Fin p.K)
    (q : Fin p.T) (z : X)
    (hq : q.val < t.val + 1 ∨ collectionEndpoint rate rewards C_star C_h t z ≤ q.val) :
    collectionEnergyIncrement rate rewards C_star C_h u t a q z = 0 := by
  have hi : collectionClampedIndex rate rewards C_star C_h t (q.val + 1) z =
      collectionClampedIndex rate rewards C_star C_h t q.val z := by
    rcases hq with hq | hq
    · simp only [collectionClampedIndex, max_eq_left (by omega : q.val + 1 ≤ t.val + 1),
        max_eq_left (by omega : q.val ≤ t.val + 1)]
    · simp only [collectionClampedIndex,
        min_eq_right (hq.trans (le_max_right _ _)),
        min_eq_right ((hq.trans (Nat.le_succ _)).trans (le_max_right _ _))]
  simp only [collectionEnergyIncrement, collectionStoppedEnergy, hi, sub_self]

private theorem collectionCausal_prefix_step (u t q : Fin p.T)
    (htq : t.val < q.val) (z : X)
    (hg : ReferenceFirstCorrectedCollectionCausalReadout.firstCollectionCausalGate
      rate rewards C_star C_h u t q z) :
    ∃ L c, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h q.val z = some L ∧
      ReferenceFirstCorrectedCollectionRetainedMoment.collectionCell rate rewards C_star C_h u t q z = some c ∧
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (q.val + 1) z = some (L ++ [c]) := by
  obtain ⟨L0, c0, B, D, birth, payload, seg, I, _hL0, _hc0, _hbase,
      _hLlen, _hbt, _hb, _hborn, _hB, _hword, _hBcells, _hseg, _hpay,
      _hinit, _hIsigma, _hIcut, _hpartition, _hD, _hjpos, _hj, _hq,
      _hDcells, _hprefix, hcell, hprior, hnext, _hstep⟩ :=
    ReferenceFirstCorrectedCollectionRetainedMoment.collectionCell_dated_word
      rate rewards C_star C_h u t q htq z hg
  obtain ⟨record, P, ledger, saved, c, _hr, _hcoord, _hsigma, _hpending, hc, _hrest⟩ :=
    ReferenceFirstCorrectedCollectionRetainedMoment.collectionCell_data rate rewards C_star C_h u t q z hg
  rw [List.take_add_one, ← hcell, hc, Option.toList_some] at hnext
  exact ⟨_, c, hprior, hc, by simpa only [List.append_assoc] using hnext⟩

private theorem collectionCausal_increment_off_retained (u t q : Fin p.T)
    (htq : t.val < q.val) (a : Fin p.K) (z : X)
    (hg : ReferenceFirstCorrectedCollectionCausalReadout.firstCollectionCausalGate
      rate rewards C_star C_h u t q z)
    (hnot : z ∉ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
      rate rewards C_star C_h u t q) :
    collectionEnergyIncrement rate rewards C_star C_h u t a q z = 0 := by
  obtain ⟨L, c, hL, hc, hnext⟩ := collectionCausal_prefix_step rate rewards C_star C_h u t q htq z hg
  have hend := (collectionCausal_endpoint_coverage rate rewards C_star C_h u t q htq z hg).2
  have hrun : RecordedQueueRun.run Q (L ++ [c]) = RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c := by
    simp only [RecordedQueueRun.run, CanonicalQueueProcess.execute_append, RecordedQueueRun.execute]
  have hfreeze : ((RecordedQueueRun.run Q (L ++ [c])).registers a).2 =
      ((RecordedQueueRun.run Q L).registers a).2 := by
    rw [hrun]
    by_cases hf : (RecordedQueueRun.run Q L).overflow = false
    · have he : c.enabled = false := by
        apply Bool.eq_false_iff.mpr
        intro he
        apply hnot
        exact ⟨⟨hg, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.run Q L), by simp only [prefixReadout, hL, Option.map_some], hf⟩,
          c.rate, by simp only [ReferenceFirstCorrectedCollectionRetainedMoment.collectionParameters,
            hc, Option.map_some, he]⟩
      exact congrArg Prod.snd (RecordedQueueRun.step_disabled_preserves Q _ c he a).1
    · exact congrArg Prod.snd (RecordedQueueRun.step_after_overflow_preserves Q _ c
        (Bool.eq_true_of_not_eq_false hf) a).1
  unfold collectionEnergyIncrement
  rw [collectionStoppedEnergy_eq_readout rate rewards C_star C_h u t a (q.val + 1) z hg.1 (by omega) hend,
    collectionStoppedEnergy_eq_readout rate rewards C_star C_h u t a q.val z hg.1 (by omega) (by omega)]
  simp only [prefixReadout, hL, hnext, Option.map_some, Option.elim_some,
    collectionReadoutEnergy, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
    hfreeze, sub_self]

/-- The retained-gate recurrence is the actual adjacent increment of the
extended scalar energy at every retained continuing-collection date. -/
theorem collectionRetained_energy_increment_le (u t q : Fin p.T)
    (a : Fin p.K) (z : X)
    (hx : z ∈ correctedCell rate rewards C_star C_h u t)
    (htq : t.val < q.val)
    (hg : z ∈ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
      rate rewards C_star C_h u t q) :
    collectionEnergyIncrement rate rewards C_star C_h u t a q z ≤
      1 + collectionStoppedEnergy rate rewards C_star C_h u t a q.val z *
        (Real.exp (beta * ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
          rate rewards C_star C_h u t q a z) - 1) := by
  have hend := (collectionCausal_endpoint_coverage rate rewards C_star C_h u t q htq z hg.1.1).2
  obtain ⟨L, c, hL, _hc, _henabled, _hclear, _hnext, hread, _hinc, hrec, _hoverflow⟩ :=
    ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetained_queue_step
      rate rewards C_star C_h u t q a z hg
  have hread0 : prefixReadout rate rewards C_star C_h q.val z = some
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (RecordedQueueRun.run Q L)) := by
    simp only [prefixReadout, hL, Option.map_some]
  have hrun : RecordedQueueRun.run Q (L ++ [c]) = RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c := by
    simp only [RecordedQueueRun.run, CanonicalQueueProcess.execute_append, RecordedQueueRun.execute]
  have hread1 : prefixReadout rate rewards C_star C_h (q.val + 1) z = some
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (RecordedQueueRun.run Q (L ++ [c]))) := by
    simpa only [hrun] using hread
  have hstep : Real.exp (beta * StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (L ++ [c])) a) -
      Real.exp (beta * StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) a) ≤
      1 + Real.exp (beta * StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) a) *
        (Real.exp (beta * ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
          rate rewards C_star C_h u t q a z) - 1) := by
    rw [hrec]
    exact exp_reflectedIncrement_le _ _ _
  unfold collectionEnergyIncrement
  rw [collectionStoppedEnergy_eq_readout rate rewards C_star C_h u t a (q.val + 1) z hx (by omega) hend,
    collectionStoppedEnergy_eq_readout rate rewards C_star C_h u t a q.val z hx (by omega) (by omega),
    hread1, hread0]
  simpa only [Option.elim_some, collectionReadoutEnergy, StoppedQueueBound.normalizedBacklog,
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, mul_div_assoc] using hstep

/-- The active multiplier is localized by the incoming causal retained gate,
not by the full-history endpoint. -/
def collectionMultiplier (u t q : Fin p.T) (a : Fin p.K) : X → ℝ :=
  (ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
    rate rewards C_star C_h u t q).indicator
      (collectionStoppedEnergy rate rewards C_star C_h u t a q.val)

theorem collectionMultiplier_eq_current (u t q : Fin p.T)
    (htq : t.val < q.val) (a : Fin p.K) :
    collectionMultiplier rate rewards C_star C_h u t q a =
      (ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
        rate rewards C_star C_h u t q).indicator
        (ReferenceFirstCollectionCorrectedOriginalSourceOverflow.currentEnergy
          rate rewards C_star C_h q a) := by
  funext z
  by_cases hg : z ∈ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
      rate rewards C_star C_h u t q
  · have hend := (collectionCausal_endpoint_coverage rate rewards C_star C_h u t q htq z hg.1.1).2
    have hidx : collectionClampedIndex rate rewards C_star C_h t q.val z = q.val := by
      unfold collectionClampedIndex
      rw [max_eq_right (by omega), min_eq_left (by omega)]
    simp only [collectionMultiplier, Set.indicator_of_mem hg, collectionStoppedEnergy,
      dite_eq_left hg.1.1.1, hidx,
      ReferenceFirstCollectionCorrectedOriginalSourceOverflow.currentEnergy,
      ← ReferenceFirstCollectionCorrectedFutureRetainedMoment.prefixReadout_eq_current]
    rfl
  · simp only [collectionMultiplier, Set.indicator_of_notMem hg]

theorem collectionMultiplier_predictable (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (q.val + 1)] (collectionMultiplier rate rewards C_star C_h u t q a) := by
  rw [collectionMultiplier_eq_current rate rewards C_star C_h u t q htq a]
  exact (ReferenceFirstCollectionCorrectedOriginalSourceOverflow.currentEnergy_predictable
    rate rewards C_star C_h control0 q a).indicator
    (ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate_measurable
      rate rewards C_star C_h control0 u t q htq)

theorem collectionMultiplier_bounds (u t q : Fin p.T) (a : Fin p.K) (z : X) :
    0 ≤ collectionMultiplier rate rewards C_star C_h u t q a z ∧
      collectionMultiplier rate rewards C_star C_h u t q a z ≤
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyCeiling rate := by
  by_cases hg : z ∈ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
      rate rewards C_star C_h u t q
  · simpa only [collectionMultiplier, Set.indicator_of_mem hg] using
      collectionStoppedEnergy_bounds rate rewards C_star C_h u t a q.val z
  · simp only [collectionMultiplier, Set.indicator_of_notMem hg]
    exact ⟨le_rfl, (Real.exp_pos _).le⟩

theorem integrable_collectionMultiplier (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Integrable (collectionMultiplier rate rewards C_star C_h u t q a) mu :=
  (integrable_collectionStoppedEnergy rate rewards C_star C_h u t a q.val).indicator
    (((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)) _
      (ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate_measurable
        rate rewards C_star C_h control0 u t q htq))

theorem integrable_collectionMultiplier_exp (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    Integrable (fun z => collectionMultiplier rate rewards C_star C_h u t q a z *
      Real.exp (beta * ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
        rate rewards C_star C_h u t q a z)) mu := by
  refine (ReferenceFirstCorrectedCollectionRetainedMoment.collectionExpIncrement_integrable
    rate rewards C_star C_h control0 u t q htq a).bdd_mul
    (c := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyCeiling rate)
    ((collectionMultiplier_predictable rate rewards C_star C_h control0 u t q htq a).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1))
      le_rfl).aestronglyMeasurable ?_
  filter_upwards [] with z
  have hb := collectionMultiplier_bounds rate rewards C_star C_h u t q a z
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem integral_collectionMultiplier_exp_le (control0 : TimeControl p)
    (u t q : Fin p.T) (htq : t.val < q.val) (a : Fin p.K) :
    (∫ z, collectionMultiplier rate rewards C_star C_h u t q a z *
      Real.exp (beta * ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
        rate rewards C_star C_h u t q a z) ∂mu) ≤
      ∫ z, collectionMultiplier rate rewards C_star C_h u t q a z ∂mu := by
  let Fq := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1)
  let W := collectionMultiplier rate rewards C_star C_h u t q a
  let Z : X → ℝ := fun z => Real.exp (beta *
    ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
      rate rewards C_star C_h u t q a z)
  have hle := (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
    (q.val + 1)
  have hW : Measurable[Fq] W :=
    collectionMultiplier_predictable rate rewards C_star C_h control0 u t q htq a
  have hWi : Integrable W mu :=
    integrable_collectionMultiplier rate rewards C_star C_h control0 u t q htq a
  have hZi : Integrable Z mu :=
    ReferenceFirstCorrectedCollectionRetainedMoment.collectionExpIncrement_integrable
      rate rewards C_star C_h control0 u t q htq a
  have hWZi : Integrable (W * Z) mu :=
    integrable_collectionMultiplier_exp rate rewards C_star C_h control0 u t q htq a
  have hp := condExp_mul_of_stronglyMeasurable_left hW.stronglyMeasurable hWZi hZi
  have hZ := ReferenceFirstCorrectedCollectionRetainedMoment.condExp_exp_collectionRetainedIncrement_le_one
    rate rewards C_star C_h control0 u t q htq a
  have hb : mu[W * Z | Fq] ≤ᵐ[mu] W := by
    filter_upwards [hp, hZ] with z hz hbound
    rw [hz]
    simpa only [Pi.mul_apply, mul_one] using mul_le_mul_of_nonneg_left hbound
      (collectionMultiplier_bounds rate rewards C_star C_h u t q a z).1
  calc
    _ = ∫ z, mu[W * Z | Fq] z ∂mu := (integral_condExp hle).symm
    _ ≤ _ := integral_mono_ae integrable_condExp hWi hb

/-- Pointwise comparison adds only the continuing-collection causal gate to
the old telescope. It retains the first outgoing crossing in both windows. -/
theorem collectionEnergyIncrement_le_old_add (u t q : Fin p.T)
    (htq : t.val < q.val) (a : Fin p.K) (z : X) :
    collectionEnergyIncrement rate rewards C_star C_h u t a q z ≤
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
        rate rewards C_star C_h u t a q z +
      (ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
        rate rewards C_star C_h u t q).indicator (fun _ => (1 : ℝ)) z +
      collectionMultiplier rate rewards C_star C_h u t q a z *
        Real.exp (beta * ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
          rate rewards C_star C_h u t q a z) -
      collectionMultiplier rate rewards C_star C_h u t q a z := by
  by_cases hx : z ∈ correctedCell rate rewards C_star C_h u t
  · by_cases hold : q.val < endDate rate rewards C_star C_h t z
    · have hnot : z ∉ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
          rate rewards C_star C_h u t q := fun hg =>
        (not_le_of_gt hold) (collectionCausal_endpoint_coverage rate rewards C_star C_h u t q htq z hg.1.1).1
      have heq : collectionEnergyIncrement rate rewards C_star C_h u t a q z =
          ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
            rate rewards C_star C_h u t a q z := by
        unfold collectionEnergyIncrement ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
        rw [collectionStoppedEnergy_eq_old rate rewards C_star C_h u t a (q.val + 1) z (by omega),
          collectionStoppedEnergy_eq_old rate rewards C_star C_h u t a q.val z hold.le]
      simp only [heq, collectionMultiplier, Set.indicator_of_notMem hnot,
        zero_mul, add_zero, sub_zero, le_refl]
    · have hold0 := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement_eq_zero
        rate rewards C_star C_h u t a q z (Or.inr (by omega))
      rw [hold0, zero_add]
      by_cases hend : collectionEndpoint rate rewards C_star C_h t z ≤ q.val
      · have hnot : z ∉ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
            rate rewards C_star C_h u t q := fun hg => by
          have h := (collectionCausal_endpoint_coverage rate rewards C_star C_h u t q htq z hg.1.1).2
          omega
        rw [collectionEnergyIncrement_eq_zero rate rewards C_star C_h u t a q z (Or.inr hend)]
        simp only [collectionMultiplier, Set.indicator_of_notMem hnot, zero_mul, add_zero, sub_zero, le_refl]
      · have hcausal := collectionCausal_of_new_date rate rewards C_star C_h u t q z hx
          (by omega) (by omega)
        by_cases hg : z ∈ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
            rate rewards C_star C_h u t q
        · have h := collectionRetained_energy_increment_le rate rewards C_star C_h u t q a z hx htq hg
          simp only [collectionMultiplier, Set.indicator_of_mem hg]
          nlinarith only [h]
        · rw [collectionCausal_increment_off_retained rate rewards C_star C_h u t q htq a z hcausal hg]
          simp only [collectionMultiplier, Set.indicator_of_notMem hg, zero_mul, add_zero, sub_zero, le_refl]
  · have hnot : z ∉ ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
        rate rewards C_star C_h u t q := fun hg => hx hg.1.1.1
    simp only [collectionEnergyIncrement, collectionStoppedEnergy, dite_eq_right hx, sub_self,
      ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement_off_cell
        rate rewards C_star C_h u t a q z hx,
      collectionMultiplier, Set.indicator_of_notMem hnot, zero_mul, add_zero, le_refl]

/-- One original-law date costs the union of disjoint old and collection
retention gates, hence at most the same corrected-cell mass. -/
theorem integral_collectionEnergyIncrement_le_cell (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) (q : Fin p.T) :
    (∫ z, collectionEnergyIncrement rate rewards C_star C_h u t a q z ∂mu) ≤
      (mu (correctedCell rate rewards C_star C_h u t)).toReal := by
  by_cases htq : t.val < q.val
  · let H := ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate
      rate rewards C_star C_h u t q
    let G := ReferenceFirstCollectionCorrectedFutureRetainedMoment.retainedGate
      rate rewards C_star C_h u t q
    let W := collectionMultiplier rate rewards C_star C_h u t q a
    let Z : X → ℝ := fun z => Real.exp (beta *
      ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedIncrement
        rate rewards C_star C_h u t q a z)
    have hH : MeasurableSet H :=
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1)) _
        (ReferenceFirstCorrectedCollectionRetainedMoment.collectionRetainedGate_measurable
          rate rewards C_star C_h control0 u t q htq)
    have hHi : Integrable (H.indicator (fun _ : X => (1 : ℝ))) mu :=
      (integrable_const _).indicator hH
    have hWi : Integrable W mu :=
      integrable_collectionMultiplier rate rewards C_star C_h control0 u t q htq a
    have hWZi : Integrable (fun z => W z * Z z) mu :=
      integrable_collectionMultiplier_exp rate rewards C_star C_h control0 u t q htq a
    have hEi := ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.integrable_energyIncrement
      rate rewards C_star C_h u t a q
    have hcompare : (∫ z, collectionEnergyIncrement rate rewards C_star C_h u t a q z ∂mu) ≤
        (∫ z, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
          rate rewards C_star C_h u t a q z ∂mu) + (mu H).toReal := by
      have hi := integral_mono
        (integrable_collectionEnergyIncrement rate rewards C_star C_h u t a q)
        (((hEi.add hHi).add hWZi).sub hWi)
        (collectionEnergyIncrement_le_old_add rate rewards C_star C_h u t q htq a)
      simp only [Pi.add_apply, Pi.sub_apply] at hi
      rw [integral_sub (f := fun z =>
          ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
            rate rewards C_star C_h u t a q z + H.indicator (fun _ => (1 : ℝ)) z + W z * Z z)
          ((hEi.add hHi).add hWZi) hWi,
        integral_add (f := fun z => ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
          rate rewards C_star C_h u t a q z + H.indicator (fun _ => (1 : ℝ)) z)
          (hEi.add hHi) hWZi,
        integral_add hEi hHi, integral_indicator hH] at hi
      simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def] at hi
      have hm := integral_collectionMultiplier_exp_le rate rewards C_star C_h control0 u t q htq a
      linarith only [hi, hm]
    have hOld : (∫ z, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.energyIncrement
        rate rewards C_star C_h u t a q z ∂mu) ≤ (mu G).toReal := by
      by_cases heq : q.val = t.val + 1
      · have hq : t.val + 1 < p.T := by omega
        have hqeq : q = ⟨t.val + 1, hq⟩ := Fin.ext heq
        subst q
        dsimp only [G]
        rw [← ReferenceFirstCollectionCorrectedOriginalSourceOverflow.nextGate_eq_future
          rate rewards C_star C_h u t hq]
        exact ReferenceFirstCollectionCorrectedOriginalSourceOverflow.integral_energyIncrement_le_next_gate
          rate rewards C_star C_h control0 u t hq a
      · exact ReferenceFirstCollectionCorrectedOriginalSourceOverflow.integral_energyIncrement_le_future_gate
          rate rewards C_star C_h control0 u t q (by omega) a
    have hdisjoint : Disjoint G H := Set.disjoint_left.mpr fun z hg hh => by
      have hend := (collectionCausal_endpoint_coverage rate rewards C_star C_h u t q htq z hh.1.1).1
      exact (not_lt_of_ge hend) hg.1.1.2
    have hmass : (mu G).toReal + (mu H).toReal ≤
        (mu (correctedCell rate rewards C_star C_h u t)).toReal := by
      change (mu).real G + (mu).real H ≤ (mu).real _
      rw [← measureReal_union hdisjoint hH]
      exact measureReal_mono (Set.union_subset
        (fun _ hz => hz.1.1.1) (fun _ hz => hz.1.1.1))
    linarith only [hcompare, hOld, hmass]
  · have hz : collectionEnergyIncrement rate rewards C_star C_h u t a q = (fun _ => 0) := by
      funext z
      exact collectionEnergyIncrement_eq_zero rate rewards C_star C_h u t a q z (Or.inl (by omega))
    rw [hz, integral_zero]
    exact ENNReal.toReal_nonneg

/-- The same inherited birth budget and one calendar budget extend through
this actual first collection, without a second horizon charge. -/
theorem integral_terminal_collectionStoppedEnergy_le (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (∫ z, collectionStoppedEnergy rate rewards C_star C_h u t a p.T z ∂mu) ≤
      (∫ z, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
        rate rewards C_star C_h u t a (t.val + 1) z ∂mu) +
        (p.T : ℝ) * (mu (correctedCell rate rewards C_star C_h u t)).toReal := by
  rw [integral_collectionStoppedEnergy_telescope rate rewards C_star C_h u t a]
  apply add_le_add
  · apply le_of_eq
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hx : z ∈ correctedCell rate rewards C_star C_h u t
    · exact collectionStoppedEnergy_birth_eq_old rate rewards C_star C_h u t a z hx
    · simp only [collectionStoppedEnergy, dite_eq_right hx,
        ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy_off_cell
          rate rewards C_star C_h u t a (t.val + 1) z hx]
  · calc
      _ ≤ ∑ _q : Fin p.T, (mu (correctedCell rate rewards C_star C_h u t)).toReal :=
        Finset.sum_le_sum fun q _ => integral_collectionEnergyIncrement_le_cell
          rate rewards C_star C_h control0 u t a q
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Every boundary included by the extension has its actual initialized word. -/
theorem collection_prefix_present (u t : Fin p.T) (z : X)
    (hx : z ∈ correctedCell rate rewards C_star C_h u t) (n : ℕ)
    (hn : t.val + 1 ≤ n) (he : n ≤ collectionEndpoint rate rewards C_star C_h t z) :
    ∃ L, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
      rate rewards C_star C_h n z = some L := by
  by_cases hold : n ≤ endDate rate rewards C_star C_h t z
  · obtain ⟨L, hL, _⟩ := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.firstCell_prefix_inputs
      rate rewards C_star C_h u t z hx n hn hold
    exact ⟨L, hL⟩
  · have hb := collectionEndpoint_bounds rate rewards C_star C_h u t z hx
    have ho := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.endDate_bounds
      rate rewards C_star C_h u t z hx
    let q : Fin p.T := ⟨n - 1, by omega⟩
    have hc := collectionCausal_of_new_date rate rewards C_star C_h u t q z hx (by dsimp [q]; omega)
      (by dsimp [q]; omega)
    obtain ⟨L, c, _hL, _hc, hnext⟩ := collectionCausal_prefix_step
      rate rewards C_star C_h u t q (by dsimp [q]; omega) z hc
    have hqn : q.val + 1 = n := by dsimp [q]; omega
    exact ⟨L ++ [c], by simpa only [hqn] using hnext⟩

private theorem source_prefix_append (n m : ℕ) (z : X) (hnm : n ≤ m)
    (L N : List (RecordedQueueRun.RoundInput p.K))
    (hL : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h n z = some L)
    (hN : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h m z = some N) :
    ∃ tail, N = L ++ tail := by
  have hn := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch rate rewards C_star C_h n z L hL
  have hm := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_launch rate rewards C_star C_h m z N hN
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs, ite_eq_left hn] at hL
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs, ite_eq_left hm] at hN
  have hp := ((List.take_isPrefix_take (l := sourceRecords rate rewards C_star C_h z)).mpr
    (Or.inl (Nat.sub_le_sub_right hnm (sourceStart rate rewards C_star C_h z)))).map
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)
  obtain ⟨slots, hslots⟩ := hp
  rw [← hslots, List.mapM_append, hL] at hN
  cases ht : slots.mapM id with
  | none => simp [ht] at hN
  | some tail => exact ⟨tail, by simpa [ht] using hN.symm⟩

/-- A crossing anywhere in the actual word persists to its own endpoint. -/
theorem collectionOverflowEvent_terminal_energy_gt (u t : Fin p.T) (a : Fin p.K) (z : X)
    (hz : z ∈ collectionOverflowEvent rate rewards C_star C_h u t a) :
    Real.exp (beta / (32 * rate.eta.val)) <
      collectionStoppedEnergy rate rewards C_star C_h u t a p.T z := by
  obtain ⟨hx, n, hn, hne, o, ho, hcap⟩ := hz
  obtain ⟨L, hL, hLo⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨N, hN⟩ := collection_prefix_present rate rewards C_star C_h u t z hx
    (collectionEndpoint rate rewards C_star C_h t z)
    (collectionEndpoint_bounds rate rewards C_star C_h u t z hx).1 le_rfl
  obtain ⟨tail, hjoin⟩ := source_prefix_append rate rewards C_star C_h n _ z hne L N hL hN
  have hflag := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefix_threshold_overflow
    rate rewards C_star C_h n z a o ho hcap
  have hf : (RecordedQueueRun.run Q L).overflow = true :=
    (congrArg (fun v : Readout => v.2.1) hLo).trans hflag
  have hrun : RecordedQueueRun.run Q N = RecordedQueueRun.execute Q tail (RecordedQueueRun.run Q L) := by
    rw [hjoin, RecordedQueueRun.run, RecordedEpisodeStability.execute_append]
    rfl
  have hreg := (RecordedQueueRun.execute_after_overflow_preserves Q tail _ hf).2 a
  have he := collectionEndpoint_bounds rate rewards C_star C_h u t z hx
  have hidx : collectionClampedIndex rate rewards C_star C_h t p.T z =
      collectionEndpoint rate rewards C_star C_h t z := by
    unfold collectionClampedIndex
    exact min_eq_right (he.2.trans (le_max_right _ _))
  have henergy : collectionStoppedEnergy rate rewards C_star C_h u t a p.T z =
      Real.exp (beta * ((o.1 a).2 : ℝ) / ((Q).n : ℝ)) := by
    simp only [collectionStoppedEnergy, dite_eq_left hx, hidx, prefixReadout, hN,
      Option.map_some, Option.elim_some, collectionReadoutEnergy,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, hrun, hreg]
    rw [← hLo]
    rfl
  rw [henergy]
  apply Real.exp_lt_exp.mpr
  simpa only [mul_div_assoc, mul_one_div] using
    mul_lt_mul_of_pos_left hcap (CanonicalRecordingRates.beta_pos p rate.eta.property)

theorem collectionOverflowEvent_measure_le (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (mu (collectionOverflowEvent rate rewards C_star C_h u t a)).toReal ≤
      Real.exp (-beta / (32 * rate.eta.val)) *
        ((∫ z, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
          rate rewards C_star C_h u t a (t.val + 1) z ∂mu) +
          (p.T : ℝ) * (mu (correctedCell rate rewards C_star C_h u t)).toReal) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun z => (collectionStoppedEnergy_bounds rate rewards C_star C_h u t a p.T z).1)
    (integrable_collectionStoppedEnergy rate rewards C_star C_h u t a p.T)
    (Real.exp (beta / (32 * rate.eta.val)))
  have hsubset := measureReal_mono (μ := mu) (fun z hz =>
    (collectionOverflowEvent_terminal_energy_gt rate rewards C_star C_h u t a z hz).le)
  have hm : Real.exp (beta / (32 * rate.eta.val)) *
      (mu (collectionOverflowEvent rate rewards C_star C_h u t a)).toReal ≤
      ∫ z, collectionStoppedEnergy rate rewards C_star C_h u t a p.T z ∂mu :=
    (mul_le_mul_of_nonneg_left hsubset (Real.exp_pos _).le).trans hmarkov
  rw [neg_div, Real.exp_neg]
  exact (le_inv_mul_iff₀ (Real.exp_pos _)).mpr
    (hm.trans (integral_terminal_collectionStoppedEnergy_le rate rewards C_star C_h control0 u t a))

/-- The finite sum uses the same inherited birth budget for every arm. -/
theorem collectionOverflowEvent_measure_sum_le (control0 : TimeControl p) :
    (∑ a : Fin p.K, ∑ u : Fin p.T, ∑ t : Fin p.T,
      (mu (collectionOverflowEvent rate rewards C_star C_h u t a)).toReal) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-beta / (32 * rate.eta.val)) := by
  let decay := Real.exp (-beta / (32 * rate.eta.val))
  have hcell := ReferenceFirstCollectionCorrectedNumericalOverflowSum.correctedCell_measure_sum_le_one
    rate rewards C_star C_h
  have harm (a : Fin p.K) :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (mu (collectionOverflowEvent rate rewards C_star C_h u t a)).toReal) ≤
      decay * (2 * ((p.T : ℝ) + 1)) := by
    have hbirth := ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy_integral_sum_le_T_add_two
      rate rewards C_star C_h control0 a
    simp only [ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy] at hbirth
    calc
      _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
          decay * ((∫ z, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
            rate rewards C_star C_h u t a (t.val + 1) z ∂mu) +
              (p.T : ℝ) * (mu (correctedCell rate rewards C_star C_h u t)).toReal) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun t _ =>
          collectionOverflowEvent_measure_le rate rewards C_star C_h control0 u t a
      _ = decay * ((∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z, ReferenceFirstCollectionCorrectedStoppedEnergyTelescope.stoppedEnergy
            rate rewards C_star C_h u t a (t.val + 1) z ∂mu) +
              (p.T : ℝ) * (∑ u : Fin p.T, ∑ t : Fin p.T,
                (mu (correctedCell rate rewards C_star C_h u t)).toReal)) := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ decay * (((p.T : ℝ) + 2) + (p.T : ℝ) * 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hbirth
          (mul_le_mul_of_nonneg_left hcell (Nat.cast_nonneg p.T))) (Real.exp_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∑ _a : Fin p.K, decay * (2 * ((p.T : ℝ) + 1)) := Finset.sum_le_sum fun a _ => harm a
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, decay]; ring

/-- The actual numerical event family through each cell's first collection. -/
def allArmCollectionOverflowEvent : Set X :=
  ⋃ a : Fin p.K, ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    collectionOverflowEvent rate rewards C_star C_h u t a

theorem allArmCollectionOverflowEvent_measure_le (control0 : TimeControl p) :
    (mu).real (allArmCollectionOverflowEvent rate rewards C_star C_h) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) * Real.exp (-beta / (32 * rate.eta.val)) := by
  have h := measureReal_iUnion_fintype_le (μ := mu)
    (f := fun z : Fin p.K × (Fin p.T × Fin p.T) =>
      collectionOverflowEvent rate rewards C_star C_h z.2.1 z.2.2 z.1)
  have hsum := collectionOverflowEvent_measure_sum_le rate rewards C_star C_h control0
  apply le_trans _ hsum
  simpa only [allArmCollectionOverflowEvent, Set.iUnion_prod', Fintype.sum_prod_type, measureReal_def] using h

end Bandits.Support.ReferenceFirstCorrectedCollectionPostCutoffNumericalOverflow
end
