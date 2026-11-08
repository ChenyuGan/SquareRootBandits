/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments

import Mathlib.Tactic

/-!
# Optional numerical cells and the existing stopped queue run

This module records the unmasked LIVE/collection option for an original
physical record and proves the deterministic option-preserving append law for
the existing `RecordedQueueRun.run`.  The run is observed only when every
cell in the supplied literal prefix is present.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.Source
  rate rewards C_star C_h u t

/-- The literal unmasked optional numerical cell of an original complete
physical record. Both readouts use the zero baseline of the complete
observation; an absent readout remains absent. -/
def calendarCell (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).or
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r)

/-- The same original complete physical suffix retained by the renewal
source. -/
def sourceRecords (z : Z) : List (ReferenceFirstCollectionSamplerCall.RoundRecord p rate) :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h

/-- The original physical launch date for this renewal source. -/
def sourceStart (z : Z) : ℕ :=
  ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h

/-- The renewal call is a record of the original complete suffix, so its
launch start precedes the call date. -/
theorem sourceStart_le_call (z : Z) :
    sourceStart rate rewards C_star C_h u t z ≤ t.val := by
  have hb := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_boundaries
    rate rewards C_star C_h u t z
  have hstart := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z
  change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ t.val
  rw [← hstart]
  omega

private theorem sourceRecords_length (z : Z) :
    (sourceRecords rate rewards C_star C_h u t z).length =
      p.T - sourceStart rate rewards C_star C_h u t z := by
  change (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
      rate rewards C_star C_h u t z).length =
    p.T - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  rw [← _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z]
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords_length
    rate rewards C_star C_h u t z

/-- The literal optional numerical prefix of the original complete suffix.
This is the optional LIVE/collection projection at each retained source
record; absent outcomes retain their positions. -/
def calendarCells (n : ℕ) (z : Z) : List (Option (RecordedQueueRun.RoundInput p.K)) :=
  (sourceRecords rate rewards C_star C_h u t z).take
    (n - sourceStart rate rewards C_star C_h u t z) |>.map (calendarCell rate)

/-- Keep the full run input only when every optional calendar cell is present. -/
def optionalPrefixCells (cells : List (Option (RecordedQueueRun.RoundInput p.K))) :
    Option (List (RecordedQueueRun.RoundInput p.K)) :=
  cells.mapM id

/-- Apply the existing stopped run to the full prefix when present, and retain
the absence otherwise. -/
def optionalPrefixReadout (cells : List (Option (RecordedQueueRun.RoundInput p.K))) :
    Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))) :=
  (optionalPrefixCells cells).map fun inputs =>
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run Q inputs)

/-- The literal dated LIVE/collection join of the original unmasked complete
observation. -/
def calendarRawJoinedPrefix (n : ℕ) (z : Z) :=
  List.zipWith (fun live collection => live.2.or collection.2)
    (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z.val)))
    (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z.val)))

private theorem zipWith_map_same {α β γ δ : Type*} (xs : List α)
    (f : β → γ → δ) (g : α → β) (h : α → γ) :
    List.zipWith f (xs.map g) (xs.map h) =
      xs.map (fun a => f (g a) (h a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons]
      exact congrArg (List.cons (f (g a) (h a))) ih

def joinedNumericalEntry
    (entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate) :
    Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) :=
  (ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2).or
    (ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2)

/-- Joining the two partial branch projections is measurable in the original
option/sum Borel structures. -/
private theorem measurable_option_isSome {X : Type*} [MeasurableSpace X]
    {α : Type*} [MeasurableSpace α] (f : X → Option α)
    (hf : Measurable f) : Measurable (fun x => (f x).isSome) := by
  let code := Equiv.optionEquivSumPUnit α
  have hcode : Measurable (fun x => code (f x)) := (comap_measurable code).comp hf
  have htag : Measurable (Sum.elim (fun _ : α => true) (fun _ : PUnit => false)) :=
    measurable_const.sumElim measurable_const
  have heq : (fun x => (f x).isSome) =
      fun x => Sum.elim (fun _ : α => true) (fun _ : PUnit => false) (code (f x)) := by
    funext x
    cases f x <;> simp [code, Equiv.optionEquivSumPUnit_none,
      Equiv.optionEquivSumPUnit_some]
  rw [heq]
  exact htag.comp hcode

private theorem measurable_option_or {X : Type*} [MeasurableSpace X]
    {α : Type*} [MeasurableSpace α] (left right : X → Option α)
    (hleft : Measurable left) (hright : Measurable right) :
    Measurable (fun x => (left x).or (right x)) := by
  have hsome := measurable_option_isSome left hleft
  have hcondition : MeasurableSet {x | (left x).isSome} :=
    MeasurableSet.preimage (measurableSet_singleton true) hsome
  have heq : (fun x => (left x).or (right x)) =
      fun x => if (left x).isSome then left x else right x := by
    funext x
    cases left x <;> rfl
  rw [heq]
  exact Measurable.ite hcondition hleft hright

private theorem measurable_leftProjection {X : Type*} [MeasurableSpace X]
    (f : X → Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p ⊕
        ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
    (hf : Measurable f) :
    Measurable (fun x => ReferenceCompleteNumericalBranchObservation.leftProjection (f x)) := by
  let A := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  let B := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  let inputCode := Equiv.optionEquivSumPUnit (A ⊕ B)
  let outputCode := Equiv.optionEquivSumPUnit A
  have hinput : Measurable (fun x => inputCode (f x)) := (comap_measurable inputCode).comp hf
  let innerCode : A ⊕ B → A ⊕ PUnit.{1} := Sum.elim (fun a : A => Sum.inl a)
      (fun _ : B => (Sum.inr PUnit.unit : A ⊕ PUnit.{1}))
  let outerCode : (A ⊕ B) ⊕ PUnit.{1} → A ⊕ PUnit.{1} := Sum.elim innerCode
      (fun _ : PUnit.{1} => (Sum.inr PUnit.unit : A ⊕ PUnit.{1}))
  have hinner : Measurable innerCode :=
    measurable_inl.sumElim measurable_const
  have houter : Measurable outerCode := by
    dsimp [outerCode, innerCode]
    exact hinner.sumElim measurable_const
  apply measurable_comap_iff.mpr
  change Measurable (fun x => outputCode
    (ReferenceCompleteNumericalBranchObservation.leftProjection (f x)))
  have heq : (fun x => outputCode
      (ReferenceCompleteNumericalBranchObservation.leftProjection (f x))) =
      fun x => outerCode (inputCode (f x)) := by
    funext x
    cases h : f x with
    | none => simp [inputCode, outputCode, outerCode, innerCode,
        Equiv.optionEquivSumPUnit_none,
        ReferenceCompleteNumericalBranchObservation.leftProjection]
    | some value => cases value <;>
        simp [inputCode, outputCode, outerCode, innerCode, Equiv.optionEquivSumPUnit_none,
          Equiv.optionEquivSumPUnit_some, ReferenceCompleteNumericalBranchObservation.leftProjection]
  rw [heq]
  exact houter.comp hinput

private theorem measurable_rightProjection {X : Type*} [MeasurableSpace X]
    (f : X → Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p ⊕
        ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
    (hf : Measurable f) :
    Measurable (fun x => ReferenceCompleteNumericalBranchObservation.rightProjection (f x)) := by
  let A := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  let B := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  let inputCode := Equiv.optionEquivSumPUnit (A ⊕ B)
  let outputCode := Equiv.optionEquivSumPUnit B
  have hinput : Measurable (fun x => inputCode (f x)) := (comap_measurable inputCode).comp hf
  let innerCode : A ⊕ B → B ⊕ PUnit.{1} :=
      Sum.elim (fun _ : A => (Sum.inr PUnit.unit : B ⊕ PUnit.{1}))
      (fun b : B => Sum.inl b)
  let outerCode : (A ⊕ B) ⊕ PUnit.{1} → B ⊕ PUnit.{1} := Sum.elim innerCode
      (fun _ : PUnit.{1} => (Sum.inr PUnit.unit : B ⊕ PUnit.{1}))
  have hinner : Measurable innerCode := by
    dsimp [innerCode]
    exact measurable_const.sumElim measurable_inl
  have houter : Measurable outerCode := by
    dsimp [outerCode, innerCode]
    exact hinner.sumElim measurable_const
  apply measurable_comap_iff.mpr
  change Measurable (fun x => outputCode
    (ReferenceCompleteNumericalBranchObservation.rightProjection (f x)))
  have heq : (fun x => outputCode
      (ReferenceCompleteNumericalBranchObservation.rightProjection (f x))) =
      fun x => outerCode (inputCode (f x)) := by
    funext x
    cases h : f x with
    | none => simp [inputCode, outputCode, outerCode, innerCode, Equiv.optionEquivSumPUnit_none,
        ReferenceCompleteNumericalBranchObservation.rightProjection]
    | some value => cases value <;>
        simp [inputCode, outputCode, outerCode, innerCode, Equiv.optionEquivSumPUnit_none,
          ReferenceCompleteNumericalBranchObservation.rightProjection]
  rw [heq]
  exact houter.comp hinput

private theorem measurable_joinedNumericalEntry :
    Measurable (joinedNumericalEntry rate) := by
  have hbranch : Measurable
      (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate => entry.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_id)
  exact measurable_option_or _ _
    (measurable_leftProjection _ hbranch) (measurable_rightProjection _ hbranch)

/-- The raw join is a literal map of the original dated complete-observation
prefix. -/
theorem calendarRawJoinedPrefix_map (n : ℕ) (z : Z) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t n z =
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z.val)).map (joinedNumericalEntry rate) := by
  unfold calendarRawJoinedPrefix
  dsimp only [ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder,
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder]
  rw [zipWith_map_same]
  rfl

/-- Borel measurability of the literal joined output in the exact source
prefix field `F_n`; all original rows, private coordinates, and controls
below `n` remain in `sourcePrefixFiltration`. -/
theorem measurable_calendarRawJoinedPrefix
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) :
    @Measurable Z (List (Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)))
      (MeasurableSpace.comap (fun z : Z => z.val)
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)))
      (inferInstance : MeasurableSpace (List (Option
        (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))))
      (fun z : Z => calendarRawJoinedPrefix rate rewards C_star C_h u t n z) := by
  have hfun : (fun z : Z => calendarRawJoinedPrefix rate rewards C_star C_h u t n z) =
      (fun z : Z =>
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z.val)).map (joinedNumericalEntry rate)) := by
    funext z
    exact calendarRawJoinedPrefix_map rate rewards C_star C_h u t n z
  rw [hfun]
  have hprefix := _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_completeObservationPrefix
    rate rewards C_star C_h u t control0 n hn
  let : MeasurableSpace Z := MeasurableSpace.comap (fun z : Z => z.val)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1))
  simpa [_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation] using
    ReferenceActiveHorizonMeasurability.measurable_list_map
      (fun z : Z => ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z.val))
      hprefix (joinedNumericalEntry rate) (measurable_joinedNumericalEntry rate)

/-- The exact source-prefix field is coarser than the ambient Borel field, so
the same joined decoder is ambient Borel. -/
theorem measurable_calendarRawJoinedPrefix_ambient
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun z : Z => calendarRawJoinedPrefix rate rewards C_star C_h u t n z) := by
  refine Measurable.mono
    (measurable_calendarRawJoinedPrefix rate rewards C_star C_h u t control0 n hn) ?_ ?_
  · exact MeasurableSpace.comap_mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (n + 1))
  · exact le_rfl

/-- Dated form of the same optional literal source-prefix cells. -/
def datedCalendarCells (n : ℕ) (z : Z) :
    List (Fin p.T × Option (RecordedQueueRun.RoundInput p.K)) :=
  ((sourceRecords rate rewards C_star C_h u t z).take
    (n - sourceStart rate rewards C_star C_h u t z)).map
      (fun r => (r.input.time, calendarCell rate r))

private theorem map_or_option {α β : Type*} (f : α → β)
    (left right : Option α) :
    (left.map f).or (right.map f) = (left.or right).map f := by
  cases left <;> rfl

private theorem rawLive_datePrefix_take (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z.val)) =
    (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z.val)).take
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) := by
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h n hn z.val]
  exact List.map_take

private theorem rawCollection_datePrefix_take (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
      (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h z.val)) =
    (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
      (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
        rate rewards C_star C_h z.val)).take
      (n - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) := by
  rw [ReferenceCompleteObservationPrefixInformation.datePrefix_eq_take
    rate rewards C_star C_h n hn z.val]
  exact List.map_take

/-- The raw joined decoder is exactly the encoded literal option prefix,
with each original physical date retained. -/
theorem calendarRawJoinedPrefix_dated (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t n z =
      (datedCalendarCells rate rewards C_star C_h u t n z).map
        (fun entry => entry.2.map
          _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
  unfold calendarRawJoinedPrefix datedCalendarCells
  rw [rawLive_datePrefix_take rate rewards C_star C_h u t n hn z,
    rawCollection_datePrefix_take rate rewards C_star C_h u t n hn z,
    ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    ← List.map_take, ← List.map_take]
  simp only [sourceRecords, sourceStart]
  rw [zipWith_map_same]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro r hr
  exact map_or_option
    _ (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r)
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r)

/-- Erasing the decoder's date projection gives exactly the encoded
`calendarCells` list. Absent cells stay in their positions. -/
theorem calendarCells_rawJoinedPrefix (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    (calendarCells rate rewards C_star C_h u t n z).map
        (Option.map _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical) =
      calendarRawJoinedPrefix rate rewards C_star C_h u t n z := by
  rw [calendarRawJoinedPrefix_dated rate rewards C_star C_h u t n hn z]
  simp [calendarCells, datedCalendarCells, List.map_map, Function.comp_def]

/-- The locally exposed joined decoder is the admitted stopped-prefix
decoder on the same original source and calendar. -/
theorem calendarRawJoinedPrefix_eq_existing (n : ℕ) (z : Z) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t n z =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z n := rfl

/-- The exact exported numerical observation is the raw suffix projection;
each `none` remains at its source calendar coordinate. -/
theorem calendarCells_existingRawJoinedPrefix (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    (calendarCells rate rewards C_star C_h u t n z).map
        (Option.map
          _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical) =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z n := by
  rw [calendarCells_rawJoinedPrefix rate rewards C_star C_h u t n hn z,
    calendarRawJoinedPrefix_eq_existing rate rewards C_star C_h u t n z]

/-- Factoring the joined decoder through the exact source-prefix filtration
keeps all source coordinates and changes only controls at dates not yet
observed. -/
theorem calendarRawJoinedPrefix_factor
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t n z =
      List.zipWith (fun live collection => live.2.or collection.2)
        (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
          (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
            (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate
              rewards C_star C_h
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z.val))))
        (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
          (ReferenceCompleteObservationPrefixInformation.datePrefix rate n
            (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate
              rewards C_star C_h
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z.val)))) := by
  rw [calendarRawJoinedPrefix_eq_existing]
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_factor
    rate rewards C_star C_h u t control0 z n hn

/-- At the horizon the existing date prefix is the complete observation,
with no additional calendar position. -/
theorem calendarCompleteObservation_terminal (z : Z)
    (hterminal : t.val + 1 = p.T) :
    ReferenceCompleteObservationPrefixInformation.datePrefix rate p.T
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z) =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
        rate rewards C_star C_h u t z :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.terminal_physical_prefix
    rate rewards C_star C_h u t z hterminal).1

/-- At the terminal horizon the joined prefix is exactly the existing
current-cell output and contains no fictitious future `Fin p.T` action. -/
theorem calendarRawJoinedPrefix_terminal (z : Z)
    (hterminal : t.val + 1 = p.T) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t p.T z =
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z).map (fun c => some
          (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) := by
  rw [calendarRawJoinedPrefix_eq_existing]
  exact (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.terminal_physical_prefix
    rate rewards C_star C_h u t z hterminal).2

/-- At the renewal boundary the actual raw join is the admitted prefix of
the same past cells followed by the original whole current cell. -/
theorem calendarRawJoinedPrefix_current (z : Z) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t (t.val + 1) z =
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z ++
        [_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t z]).map
        (fun cell => some
          (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
            cell)) := by
  rw [calendarRawJoinedPrefix_eq_existing]
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.appendedCells_rawPrefix_join
    rate rewards C_star C_h u t z

private theorem encodeNumerical_injective :
    Function.Injective
      (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (p := p)) := by
  intro a b h
  cases a with
  | mk ae aa ar arate arp arl atp =>
    cases b with
    | mk be ba br brate brp brl btp =>
      simp only [_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical,
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] at h
      cases h
      rfl

private theorem option_encode_injective
    (left right : Option (RecordedQueueRun.RoundInput p.K))
    (h : left.map
        (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
          (p := p)) =
      right.map
        (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
          (p := p))) : left = right := by
  cases left with
  | none => cases right <;> simp_all
  | some a =>
    cases right with
    | none => simp at h
    | some b =>
      simp only [Option.map_some] at h
      congr 1
      exact encodeNumerical_injective (Option.some.inj h)

private theorem list_map_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) : Function.Injective (List.map f) := by
  intro left right h
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons head' tail' =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hh, ht⟩ := h
          have hhead : head = head' := hf hh
          subst head'
          congr 1
          exact ih ht

/-- Equal joined raw prefixes determine the same optional cells. This uses
the injective exposed numerical encoding and retains every absent slot. -/
theorem calendarCells_eq_of_calendarRawJoinedPrefix_eq
    (n : ℕ) (hn : n ≤ p.T) (z w : Z)
    (hraw : calendarRawJoinedPrefix rate rewards C_star C_h u t n z =
      calendarRawJoinedPrefix rate rewards C_star C_h u t n w) :
    calendarCells rate rewards C_star C_h u t n z =
      calendarCells rate rewards C_star C_h u t n w := by
  apply list_map_injective
    (Option.map
      (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (p := p)))
    (fun a b h => option_encode_injective a b h)
  rw [calendarCells_rawJoinedPrefix rate rewards C_star C_h u t n hn z,
    calendarCells_rawJoinedPrefix rate rewards C_star C_h u t n hn w, hraw]

/-- The optional cells at the renewal date are exactly the existing
`currentCells`; the option traversal neither skips nor reconstructs entries. -/
theorem calendarCells_current_mapM (z : Z) :
    optionalPrefixCells (calendarCells rate rewards C_star C_h u t (t.val + 1) z) =
      some (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z) := by
  have hlen : t.val + 1 ≤ p.T := by omega
  have hencoded := calendarCells_rawJoinedPrefix rate rewards C_star C_h u t
    (t.val + 1) hlen z
  rw [calendarRawJoinedPrefix_current rate rewards C_star C_h u t z] at hencoded
  have hmap : calendarCells rate rewards C_star C_h u t (t.val + 1) z =
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z).map some := by
    apply list_map_injective (Option.map
      (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (p := p)))
      (fun a b h => option_encode_injective a b h)
    simpa [List.map_map, Function.comp_def,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells]
      using hencoded
  rw [hmap]
  change List.mapM id
      (List.map some
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z)) = _
  induction _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z with
  | nil => rfl
  | cons c cells ih =>
      change (some c :: List.map some cells).mapM id = some (c :: cells)
      rw [List.mapM_cons]
      simp [ih]

/-- The source-bound optional readout at the renewal boundary is the actual
whole post-readout, with every inherited register, overflow bit, and history. -/
theorem calendarCells_current_readout (z : Z) :
    optionalPrefixReadout rate
        (calendarCells rate rewards C_star C_h u t (t.val + 1) z) =
      some (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z) := by
  rw [optionalPrefixReadout, calendarCells_current_mapM rate rewards C_star C_h u t z]
  exact congrArg some
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
      rate rewards C_star C_h u t z)

/-- The original suffix record at a future date, using its calendar offset. -/
def futureRecord (q : Fin p.T) (z : Z) :
    ReferenceFirstCollectionSamplerCall.RoundRecord p rate :=
  (sourceRecords rate rewards C_star C_h u t z).get ⟨
    q.val - sourceStart rate rewards C_star C_h u t z,
    by
      rw [sourceRecords_length rate rewards C_star C_h u t z]
      have hstart := sourceStart_le_call rate rewards C_star C_h u t z
      have hq := q.isLt
      omega⟩

/-- The actual optional numerical cell at future date `q`, with no success
search or date compression. -/
def futureCell (q : Fin p.T) (z : Z) : Option (RecordedQueueRun.RoundInput p.K) :=
  calendarCell rate (futureRecord rate rewards C_star C_h u t q z)

/-- Optional readout of the same original-suffix prefix through natural date
`n`; the public run is applied only when the whole option list is present. -/
def futurePrefixReadout (n : ℕ) (z : Z) :=
  optionalPrefixReadout rate (calendarCells rate rewards C_star C_h u t n z)

/-- The source lookup is exactly `q.val - start`; the selected record retains
its original time, rows, private source, and whole reward table. -/
theorem futureRecord_lookup_fields (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    (sourceRecords rate rewards C_star C_h u t z)[
      q.val - sourceStart rate rewards C_star C_h u t z]? =
        some (futureRecord rate rewards C_star C_h u t q z) ∧
      (futureRecord rate rewards C_star C_h u t q z).input.time = q ∧
      (futureRecord rate rewards C_star C_h u t q z).input.rows = z.val.1.2 ∧
      (futureRecord rate rewards C_star C_h u t q z).input.selected =
        ActualInitializationPhysicalStep.selectedRowIndex p z.val ∧
      (futureRecord rate rewards C_star C_h u t q z).input.rewards = rewards := by
  have hstart := sourceStart_le_call rate rewards C_star C_h u t z
  change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ t.val at hstart
  have hindex : q.val - sourceStart rate rewards C_star C_h u t z <
      (sourceRecords rate rewards C_star C_h u t z).length := by
    rw [sourceRecords_length rate rewards C_star C_h u t z]
    have hq := q.isLt
    have hstart := sourceStart_le_call rate rewards C_star C_h u t z
    omega
  have hlookup := List.getElem?_eq_getElem hindex
  have hrecordSpec :=
    ReferenceLaterLiveNumericalReadout.source_record_prefix rate rewards C_star C_h z.val
      ⟨q.val - sourceStart rate rewards C_star C_h u t z, hindex⟩
  obtain ⟨_, _, hactual⟩ := hrecordSpec
  change futureRecord rate rewards C_star C_h u t q z = _ at hactual
  refine ⟨hlookup, ?_, ?_, ?_, ?_⟩
  · rw [hactual]
    apply Fin.ext
    change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h +
      (q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) = q.val
    omega
  · rw [hactual]
    rfl
  · rw [hactual]
    rfl
  · rw [hactual]
    rfl

/-- The separate dated LIVE decoder appends the readout of the original
record at `q`, including an absent readout. -/
theorem rawLive_futurePrefix_append (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate (q.val + 1)
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z.val)) =
      ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate q.val
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z.val)) ++
        [(q, (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
          (futureRecord rate rewards C_star C_h u t q z)).map
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical)] := by
  have hq1 : q.val + 1 ≤ p.T := by omega
  have hstart := sourceStart_le_call rate rewards C_star C_h u t z
  change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ t.val at hstart
  have hsub : q.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h =
      (q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) + 1 := by
    omega
  have hlookup := (futureRecord_lookup_fields rate rewards C_star C_h u t q z hfuture).1
  change (sourceRecords rate rewards C_star C_h u t z)[
    q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h]? = _ at hlookup
  have htime := (futureRecord_lookup_fields rate rewards C_star C_h u t q z hfuture).2.1
  rw [rawLive_datePrefix_take rate rewards C_star C_h u t (q.val + 1) hq1 z,
    rawLive_datePrefix_take rate rewards C_star C_h u t q.val (by omega) z,
    ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    hsub, List.take_add_one]
  have hget :
      ((sourceRecords rate rewards C_star C_h u t z).map fun r =>
        (r.input.time,
          (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r).map
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical))[
        q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h]? =
        some (q, (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
          (futureRecord rate rewards C_star C_h u t q z)).map
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
    rw [List.getElem?_map, hlookup]
    simp [htime]
  simp only [sourceRecords] at hget
  rw [hget]
  simp

/-- The separate dated collection decoder appends the same original record's
collection projection, retaining its independent `none` outcome. -/
theorem rawCollection_futurePrefix_append (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate (q.val + 1)
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z.val)) =
      ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
        (ReferenceCompleteObservationPrefixInformation.datePrefix rate q.val
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h z.val)) ++
        [(q, (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (futureRecord rate rewards C_star C_h u t q z)).map
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical)] := by
  have hq1 : q.val + 1 ≤ p.T := by omega
  have hstart := sourceStart_le_call rate rewards C_star C_h u t z
  change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ t.val at hstart
  have hsub : q.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h =
      (q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) + 1 := by
    omega
  have hlookup := (futureRecord_lookup_fields rate rewards C_star C_h u t q z hfuture).1
  change (sourceRecords rate rewards C_star C_h u t z)[
    q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h]? = _ at hlookup
  have htime := (futureRecord_lookup_fields rate rewards C_star C_h u t q z hfuture).2.1
  rw [rawCollection_datePrefix_take rate rewards C_star C_h u t (q.val + 1) hq1 z,
    rawCollection_datePrefix_take rate rewards C_star C_h u t q.val (by omega) z,
    ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder_completeSuffixRecords
      rate rewards C_star C_h z.val,
    hsub, List.take_add_one]
  have hget :
      ((sourceRecords rate rewards C_star C_h u t z).map fun r =>
        (r.input.time,
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r).map
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical))[
        q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h]? =
        some (q, (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (futureRecord rate rewards C_star C_h u t q z)).map
            _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
    rw [List.getElem?_map, hlookup]
    simp [htime]
  simp only [sourceRecords] at hget
  rw [hget]
  simp

/-- Extending through future date `q` appends precisely its actual optional
cell. -/
theorem calendarCells_succ (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    calendarCells rate rewards C_star C_h u t (q.val + 1) z =
      calendarCells rate rewards C_star C_h u t q.val z ++
        [futureCell rate rewards C_star C_h u t q z] := by
  have hstart := sourceStart_le_call rate rewards C_star C_h u t z
  change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h ≤ t.val at hstart
  have hindex : q.val - sourceStart rate rewards C_star C_h u t z <
      (sourceRecords rate rewards C_star C_h u t z).length := by
    rw [sourceRecords_length rate rewards C_star C_h u t z]
    have hq := q.isLt
    have hstart := sourceStart_le_call rate rewards C_star C_h u t z
    omega
  have hsub : q.val + 1 - sourceStart rate rewards C_star C_h u t z =
      (q.val - sourceStart rate rewards C_star C_h u t z) + 1 := by
    change q.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h =
      (q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h) + 1
    omega
  have hlookup : (sourceRecords rate rewards C_star C_h u t z)[
      q.val - sourceStart rate rewards C_star C_h u t z]? =
        some (futureRecord rate rewards C_star C_h u t q z) :=
    List.getElem?_eq_getElem hindex
  rw [calendarCells, calendarCells, hsub, List.take_add_one, hlookup,
    List.map_append]
  rfl

/-- The actual joined raw observation appends exactly the encoded optional
cell at `q`; the two decoder branches keep their separate dated append laws. -/
theorem calendarRawJoinedPrefix_succ (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    calendarRawJoinedPrefix rate rewards C_star C_h u t (q.val + 1) z =
      calendarRawJoinedPrefix rate rewards C_star C_h u t q.val z ++
        [(futureCell rate rewards C_star C_h u t q z).map
          _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical] := by
  rw [← calendarCells_rawJoinedPrefix rate rewards C_star C_h u t (q.val + 1) (by omega) z,
    ← calendarCells_rawJoinedPrefix rate rewards C_star C_h u t q.val (by omega) z,
    calendarCells_succ rate rewards C_star C_h u t q z hfuture]
  simp [List.map_append]

/-- The exposed joined decoder's successor law is the corresponding public
`rawJoinedPrefix` law on the same original source. -/
theorem existingRawJoinedPrefix_succ (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z (q.val + 1) =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z q.val ++
        [(futureCell rate rewards C_star C_h u t q z).map
          _root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical] := by
  rw [← calendarRawJoinedPrefix_eq_existing rate rewards C_star C_h u t (q.val + 1) z,
    ← calendarRawJoinedPrefix_eq_existing rate rewards C_star C_h u t q.val z,
    calendarRawJoinedPrefix_succ rate rewards C_star C_h u t q z hfuture]

/-- The optional run observation is congruent under equality of its literal
option list, including every accepted-history register. -/
theorem optionalPrefixReadout_congr
    (left right : List (Option (RecordedQueueRun.RoundInput p.K)))
    (heq : left = right) :
    optionalPrefixReadout rate left = optionalPrefixReadout rate right := by
  rw [heq]

/-- Equality of the original J source-prefix coordinates gives equality of
the full optional stopped readout, including registers, overflow, and every
accepted-history list. -/
theorem optionalPrefixReadout_sourcePrefix_congr
    (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z w : Z)
    (hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n w.val) :
    futurePrefixReadout rate rewards C_star C_h u t n z =
      futurePrefixReadout rate rewards C_star C_h u t n w := by
  have hraw : calendarRawJoinedPrefix rate rewards C_star C_h u t n z =
      calendarRawJoinedPrefix rate rewards C_star C_h u t n w := by
    rw [calendarRawJoinedPrefix_factor rate rewards C_star C_h u t control0 n hn z,
      calendarRawJoinedPrefix_factor rate rewards C_star C_h u t control0 n hn w,
      hprefix]
  apply optionalPrefixReadout_congr
  exact calendarCells_eq_of_calendarRawJoinedPrefix_eq
    rate rewards C_star C_h u t n hn z w hraw

/-- An absent cell makes the full-prefix run observation absent. -/
theorem optionalPrefixReadout_none_of_absent
    (cells : List (Option (RecordedQueueRun.RoundInput p.K)))
    (habsent : optionalPrefixCells cells = none) :
    optionalPrefixReadout rate cells = none := by
  simp [optionalPrefixReadout, habsent]

/-- The existing run satisfies its one-cell recursion, preserving the first
overflowing update. -/
theorem run_append_one (cells : List (RecordedQueueRun.RoundInput p.K))
    (cell : RecordedQueueRun.RoundInput p.K) :
    RecordedQueueRun.run Q (cells ++ [cell]) =
      RecordedQueueRun.step Q (RecordedQueueRun.run Q cells) cell := by
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.run_append_one
    rate cells cell

/-- The same optional match governs the successor readout. If an earlier
cell is absent, or the appended cell is absent, the full-prefix observation
stays absent. -/
theorem optionalPrefixReadout_append
    (cells : List (Option (RecordedQueueRun.RoundInput p.K)))
    (cell : Option (RecordedQueueRun.RoundInput p.K)) :
    optionalPrefixReadout rate (cells ++ [cell]) =
      match optionalPrefixCells cells, cell with
      | some inputs, some c => some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c))
      | _, _ => none := by
  cases hprefix : optionalPrefixCells cells with
  | none =>
      change List.mapM id cells = none at hprefix
      cases cell <;>
        simp [optionalPrefixReadout, optionalPrefixCells, List.mapM_append, hprefix]
  | some inputs =>
      change List.mapM id cells = some inputs at hprefix
      cases cell with
      | none =>
          simp [optionalPrefixReadout, optionalPrefixCells, List.mapM_append, hprefix]
      | some c =>
          simp [optionalPrefixReadout, optionalPrefixCells, List.mapM_append, hprefix,
            run_append_one]

/-- The actual future calendar successor follows the same Option match as
the existing stopped run. An earlier absence remains absent; no reset or
physical-date skip is introduced. -/
theorem futurePrefixReadout_succ (q : Fin p.T) (z : Z)
    (hfuture : t.val + 1 < q.val) :
    futurePrefixReadout rate rewards C_star C_h u t (q.val + 1) z =
      match optionalPrefixCells (calendarCells rate rewards C_star C_h u t q.val z),
          futureCell rate rewards C_star C_h u t q z with
      | some inputs, some c => some
          (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
            (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c))
      | _, _ => none := by
  unfold futurePrefixReadout
  rw [calendarCells_succ rate rewards C_star C_h u t q z hfuture]
  exact optionalPrefixReadout_append rate
    (calendarCells rate rewards C_star C_h u t q.val z)
    (futureCell rate rewards C_star C_h u t q z)

/-- On the present arm of the same option match, every register is the actual
`QueueReplay.transition` result and every per-arm accepted-history list gets
the current record appended. -/
theorem optionalPrefixReadout_present_projections
    (cells : List (Option (RecordedQueueRun.RoundInput p.K)))
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (c : RecordedQueueRun.RoundInput p.K)
    (hinputs : optionalPrefixCells cells = some inputs) :
    optionalPrefixReadout rate (cells ++ [some c]) =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c)) := by
  rw [optionalPrefixReadout_append rate cells (some c), hinputs]

/-- The first update exposes the actual register transition at every arm. -/
theorem step_registers (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    (RecordedQueueRun.step Q state c).registers a =
      QueueReplay.transition (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
        (state.registers a) (RecordedQueueRun.acceptedRecord Q state c a) := rfl

/-- Overflow is computed from the registers after the current transition, so
the first detecting update remains in the run. -/
theorem step_overflow (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) :
    (RecordedQueueRun.step Q state c).overflow =
      (state.overflow || decide (∃ a, 32 * (QueueReplay.transition
        (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
        (state.registers a) (RecordedQueueRun.acceptedRecord Q state c a)).2 >
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D)) := by
  change (state.overflow || decide (∃ a, 32 * (QueueReplay.transition
      (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
      (state.registers a) (RecordedQueueRun.acceptedRecord Q state c a)).2 >
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D)) = _
  rfl

/-- Every accepted-history list appends the record from this actual update. -/
theorem step_records (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    (RecordedQueueRun.step Q state c).records a =
      state.records a ++ [RecordedQueueRun.acceptedRecord Q state c a] := rfl

/-- A disabled date produces the literal disabled accepted record. -/
theorem acceptedRecord_disabled (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K)
    (hdisabled : c.enabled = false) :
    RecordedQueueRun.acceptedRecord Q state c a = (false, 0) := by
  simp [RecordedQueueRun.acceptedRecord, hdisabled]

/-- A prior-overflow date produces the literal disabled accepted record. -/
theorem acceptedRecord_priorOverflow (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K)
    (hoverflow : state.overflow = true) :
    RecordedQueueRun.acceptedRecord Q state c a = (false, 0) := by
  simp [RecordedQueueRun.acceptedRecord, hoverflow]

/-- A disabled cell appends the actual `(false, 0)` accepted record for each
arm and leaves each register unchanged. -/
theorem disabled_step_registers_and_records
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (hdisabled : c.enabled = false) :
    (RecordedQueueRun.step Q state c).registers = state.registers ∧
      ((RecordedQueueRun.step Q state c).records =
        fun a => state.records a ++ [(false, 0)]) := by
  constructor
  · funext a
    simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, hdisabled,
      QueueReplay.transition]
  · funext a
    simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, hdisabled]

/-- A prior-overflow cell is retained as `(false,0)` for every arm, while the
run's overflow flag remains true. -/
theorem overflow_step_records
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (hoverflow : state.overflow = true) :
    ((RecordedQueueRun.step Q state c).records =
        fun a => state.records a ++ [(false, 0)]) ∧
      (RecordedQueueRun.step Q state c).overflow = true := by
  constructor
  · funext a
    simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord, hoverflow]
  · simp [RecordedQueueRun.step, hoverflow]

/-- Prior overflow freezes every register and still appends one disabled
record for every arm. -/
theorem overflow_step_registers_and_records
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (hoverflow : state.overflow = true) :
    (RecordedQueueRun.step Q state c).registers = state.registers ∧
      (RecordedQueueRun.step Q state c).records =
        fun a => state.records a ++ [(false, 0)] := by
  constructor
  · funext a
    rw [step_registers, acceptedRecord_priorOverflow rate state c a hoverflow]
    rfl
  · funext a
    rw [step_records, acceptedRecord_priorOverflow rate state c a hoverflow]

/-- A retained enabled cell with zero quantized arrival records `(true,0)`;
the existing run still applies its service transition. -/
theorem enabled_zero_arrival_record
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K)
    (henabled : c.enabled = true) (hoverflow : state.overflow = false)
    (hzero : RecordedQueueRun.quantizedArrival Q c a = 0) :
    RecordedQueueRun.acceptedRecord Q state c a = (true, 0) := by
  simp [RecordedQueueRun.acceptedRecord, henabled, hoverflow, hzero]

/-- A retained enabled zero-arrival cell still executes the queue's service
transition on the existing backlog. -/
theorem enabled_zero_arrival_transition
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K)
    (henabled : c.enabled = true) (hoverflow : state.overflow = false)
    (hzero : RecordedQueueRun.quantizedArrival Q c a = 0) :
    (RecordedQueueRun.step Q state c).registers a =
      let registers := state.registers a
      (registers.1 + min (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) registers.2,
        registers.2 - min (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) registers.2) := by
  rw [step_registers, enabled_zero_arrival_record rate state c a henabled hoverflow hzero]
  exact QueueReplay.transition_enabled_zero_arrival
    (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
    (state.registers a).1 (state.registers a).2

/-- At the terminal date there is no future `Fin T` action coordinate. -/
theorem no_future_date_at_terminal (t : Fin p.T)
    (hterminal : t.val + 1 = p.T) :
    ¬ ∃ q : Fin p.T, t.val + 1 < q.val := by
  rintro ⟨q, hq⟩
  have hqT := q.isLt
  omega

open ReferenceActiveHorizonMeasurability

private instance listMeasurableSingleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] : MeasurableSingletonClass (List α) where
  measurableSet_singleton l := by
    let : MeasurableSingletonClass (Unit ⊕ α) := ⟨fun x => by
      cases x with
      | inl a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inl_image
      | inr a => simpa only [Set.image_singleton] using (MeasurableSet.singleton a).inr_image⟩
    have hinj : Function.Injective (listObservationCoordinates (α := α)) := by
      intro a b h
      apply List.ext_getElem (congrArg Prod.fst h)
      intro i hi hj
      have he := congrFun (congrArg Prod.snd h) i
      simpa only [listObservationCoordinates, listObservationAt,
        List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Sum.inr.injEq] using he
    have hh := measurable_listObservationCoordinates
      (MeasurableSet.singleton (listObservationCoordinates l))
    convert hh using 1
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]

private theorem measurable_option_map {X A B : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    (f : A → B) (hf : Measurable f) (g : X → Option A) (hg : Measurable g) :
    Measurable (fun x => (g x).map f) :=
  ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : A × X => f v.1) (hf.comp measurable_fst) g hg

private theorem measurable_option_map_countable {X A B : Type}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (f : A → B) (hf : Measurable f) (g : X → Option A) (hg : Measurable g) :
    Measurable (fun x => (g x).map f) := by
  let borelOption := LaterAssignmentStartMeasurability.optionMeasurableSpace (α := B)
  have hs : @MeasurableSingletonClass (Option B) borelOption := by
    let : MeasurableSpace (Option B) := borelOption
    let : MeasurableSingletonClass (B ⊕ PUnit.{1}) := ⟨fun x => by
      cases x with
      | inl b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inl_image
      | inr b => simpa only [Set.image_singleton] using (measurableSet_singleton b).inr_image⟩
    constructor
    intro c
    have h := (comap_measurable (Equiv.optionEquivSumPUnit B))
      (measurableSet_singleton (Equiv.optionEquivSumPUnit B c))
    convert h using 1
    ext x
    exact (Equiv.optionEquivSumPUnit B).injective.eq_iff.symm
  have hid : @Measurable (Option B) (Option B) borelOption
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace B) id := by
    let : MeasurableSpace (Option B) := borelOption
    let : MeasurableSingletonClass (Option B) := hs
    intro s _
    exact s.to_countable.measurableSet
  exact hid.comp (measurable_option_map f hf g hg)

/-- The literal register, overflow and history update on the existing state's
readout, after projecting only the enabled bit and actual integer arrivals. -/
private def readoutUpdate
    (state : (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))
    (cell : Bool × (Fin p.K → ℕ)) :=
  let accepted := fun a =>
    if state.2.1 then (false, 0) else if cell.1 then (true, cell.2 a) else (false, 0)
  let registers := fun a => QueueReplay.transition
    (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) (state.1 a) (accepted a)
  (registers, state.2.1 || decide (∃ a, 32 * (registers a).2 >
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D),
    fun a => state.2.2 a ++ [accepted a])

private theorem readoutUpdate_actual (state : RecordedQueueRun.RunState p.K)
    (cell : RecordedQueueRun.RoundInput p.K) :
    readoutUpdate rate
        (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state)
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell) =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step Q state cell) := rfl

/-- A literal absence-preserving fold of the countable arrival coordinates.
It observes the existing run; it constructs no numerical input or run state. -/
private def optionalArrivalFold
    (cells : List (Option (Bool × (Fin p.K → ℕ))))
    (state : Option ((Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ))))) :=
  cells.foldl (fun prior cell =>
    prior.bind fun s => cell.map (readoutUpdate rate s)) state

private theorem optionalArrivalFold_none
    (cells : List (Option (Bool × (Fin p.K → ℕ)))) :
    optionalArrivalFold rate cells none = none := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => exact ih

private theorem optionalArrivalFold_actual
    (cells : List (Option (RecordedQueueRun.RoundInput p.K)))
    (state : RecordedQueueRun.RunState p.K) :
    optionalArrivalFold rate
        (cells.map (Option.map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate)))
        (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state)) =
      (cells.mapM id).map (fun inputs =>
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.execute Q inputs state)) := by
  induction cells generalizing state with
  | nil => rfl
  | cons cell cells ih =>
      cases cell with
      | none =>
          simp only [List.map_cons, Option.map_none, optionalArrivalFold,
            List.foldl_cons, Option.bind_some, Option.map_none]
          rw [← optionalArrivalFold, optionalArrivalFold_none]
          simp [List.mapM_cons]
      | some cell =>
          simp only [List.map_cons, Option.map_some, optionalArrivalFold,
            List.foldl_cons, Option.bind_some, readoutUpdate_actual]
          rw [← optionalArrivalFold, ih]
          cases h : cells.mapM id <;>
            simp [List.mapM_cons, h, RecordedQueueRun.execute]

private theorem futurePrefixReadout_arrivalFold
    (n : ℕ) (hn : n ≤ p.T) (z : Z) :
    futurePrefixReadout rate rewards C_star C_h u t n z =
      optionalArrivalFold rate
        ((calendarRawJoinedPrefix rate rewards C_star C_h u t n z).map
          (Option.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))
        (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.initialState p.K))) := by
  rw [← calendarCells_rawJoinedPrefix rate rewards C_star C_h u t n hn z]
  rw [List.map_map]
  have hmap :
      (fun c : Option (RecordedQueueRun.RoundInput p.K) =>
        (c.map ReferenceCompleteNumericalBranchObservation.encodeNumerical).map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) =
      Option.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate) := by
    funext c
    cases c <;> rfl
  change _ = optionalArrivalFold rate
    ((calendarCells rate rewards C_star C_h u t n z).map
      (fun c => (c.map ReferenceCompleteNumericalBranchObservation.encodeNumerical).map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))) _
  rw [hmap, optionalArrivalFold_actual]
  rfl

/-- Borelness of the entire optional stopped readout in exactly `F_n`.
The fold keeps the overflow flag, every register and every accepted history;
the arrival arithmetic uses the original real vectors and literal floor. -/
theorem measurable_futurePrefixReadout
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1))]
      (futurePrefixReadout rate rewards C_star C_h u t n) := by
  let : MeasurableSpace Z := MeasurableSpace.comap (fun z : Z => z.val)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1))
  have hraw := measurable_calendarRawJoinedPrefix rate rewards C_star C_h u t control0 n hn
  have harrival : Measurable (fun c : Option
      (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
      c.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) :=
    measurable_option_map_countable _
      (ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate)
      id measurable_id
  have hlist := measurable_list_map _ hraw _ harrival
  have hfold := (measurable_of_countable (fun cells :
      List (Option (Bool × (Fin p.K → ℕ))) => optionalArrivalFold rate cells
        (some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.initialState p.K))))).comp hlist
  convert hfold using 1
  funext z
  exact futurePrefixReadout_arrivalFold rate rewards C_star C_h u t n hn z

/-- The same full optional readout is Borel in the original ambient source. -/
theorem measurable_futurePrefixReadout_ambient
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (futurePrefixReadout rate rewards C_star C_h u t n) := by
  refine Measurable.mono
    (measurable_futurePrefixReadout rate rewards C_star C_h u t control0 n hn) ?_ le_rfl
  exact MeasurableSpace.comap_mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (n + 1))

private theorem measurable_optionalLast {X A : Type*}
    [MeasurableSpace X] [MeasurableSpace A]
    (f : X → List (Option A)) (hf : Measurable f) :
    Measurable (fun x => Sum.elim (fun _ : Unit => none) id
      (listObservationAt (f x) ((f x).length - 1))) := by
  have hcoordinates := measurable_listObservationCoordinates.comp hf
  have hindex := (measurable_of_countable (fun n : ℕ => n - 1)).comp
    (measurable_fst.comp hcoordinates)
  have heval : Measurable (fun v : (ℕ → Unit ⊕ Option A) × ℕ => v.1 v.2) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply n)
  exact (measurable_const.sumElim measurable_id).comp
    (heval.comp ((measurable_snd.comp hcoordinates).prodMk hindex))

/-- All numerical coordinates of the actual optional future cell are Borel
after its calendar date. The outer option retains absence and the inner
marker option retains a present recording call with no recorded arm. -/
theorem measurable_futureCell_numericalCoordinates
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))]
      (fun z : Z => (futureCell rate rewards C_star C_h u t q z).map
        ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
  let : MeasurableSpace Z := MeasurableSpace.comap (fun z : Z => z.val)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))
  have hlast := measurable_optionalLast _
    (measurable_calendarRawJoinedPrefix rate rewards C_star C_h u t control0
      (q.val + 1) (by omega))
  convert hlast using 1
  funext z
  rw [calendarRawJoinedPrefix_succ rate rewards C_star C_h u t q z hfuture]
  simp [listObservationAt]

/-- Ambient Borelness keeps the same original source and optional cell. -/
theorem measurable_futureCell_numericalCoordinates_ambient
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    Measurable (fun z : Z => (futureCell rate rewards C_star C_h u t q z).map
      ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
  refine Measurable.mono
    (measurable_futureCell_numericalCoordinates rate rewards C_star C_h u t
      control0 q hfuture) ?_ le_rfl
  exact MeasurableSpace.comap_mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (q.val + 1 + 1))

private theorem measurable_cell_projections {X : Type} [MeasurableSpace X]
    (cell : X → Option (RecordedQueueRun.RoundInput p.K))
    (hcell : Measurable (fun x => (cell x).map
      ReferenceCompleteNumericalBranchObservation.encodeNumerical)) :
    Measurable (fun x => (cell x).map (fun c => c.enabled)) ∧
      Measurable (fun x => (cell x).map (fun c => c.rate)) ∧
      Measurable (fun x => (cell x).map (fun c => c.reward)) ∧
      Measurable (fun x => (cell x).map (fun c => c.recordedArm)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Option.map_map, Function.comp_def,
      ReferenceCompleteNumericalBranchObservation.encodeNumerical,
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] using
      measurable_option_map_countable
        (fun c : ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p => c.1)
        measurable_fst _ hcell
  · simpa only [Option.map_map, Function.comp_def,
      ReferenceCompleteNumericalBranchObservation.encodeNumerical,
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] using
      measurable_option_map
        (fun c : ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p => c.2.2.2)
        (measurable_snd.comp (measurable_snd.comp measurable_snd)) _ hcell
  · simpa only [Option.map_map, Function.comp_def,
      ReferenceCompleteNumericalBranchObservation.encodeNumerical,
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] using
      measurable_option_map
        (fun c : ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p => c.2.2.1)
        (measurable_fst.comp (measurable_snd.comp measurable_snd)) _ hcell
  · simpa only [Option.map_map, Function.comp_def,
      ReferenceCompleteNumericalBranchObservation.encodeNumerical,
      ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates] using
      measurable_option_map_countable
        (fun c : ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p => c.2.1)
        (measurable_fst.comp measurable_snd) _ hcell

/-- The separate enabled, full rate, full reward, and nested marker
projections are measurable in exactly the post-date field `F_(q.val+1)`. -/
theorem measurable_futureCell_coordinates
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))]
      (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.enabled)) ∧
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))]
      (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.rate)) ∧
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))]
      (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.reward)) ∧
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))]
      (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.recordedArm)) := by
  let : MeasurableSpace Z := MeasurableSpace.comap (fun z : Z => z.val)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1 + 1))
  exact measurable_cell_projections _
    (measurable_futureCell_numericalCoordinates rate rewards C_star C_h u t control0 q hfuture)

/-- The same four optional projections are ambient Borel. In particular the
marker has type `Option (Option (Fin p.K))`, retaining both kinds of absence. -/
theorem measurable_futureCell_coordinates_ambient
    (control0 : ContinuousLearningRows.TimeControl p) (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    Measurable (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.enabled)) ∧
    Measurable (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.rate)) ∧
    Measurable (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.reward)) ∧
    Measurable (fun z : Z =>
      (futureCell rate rewards C_star C_h u t q z).map (fun c => c.recordedArm)) :=
  measurable_cell_projections _
    (measurable_futureCell_numericalCoordinates_ambient rate rewards C_star C_h u t
      control0 q hfuture)

end Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalPrefix
