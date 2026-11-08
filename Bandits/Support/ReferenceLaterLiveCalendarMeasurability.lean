/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterLiveReadoutDomain
public import Bandits.Support.ReferenceLaterLiveReadoutValuesMeasurability

/-!
# Measurable optional later-live calendars

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

This module composes the jointly measurable readout domain with the measured
values on its genuine subtype, retaining `none` on the complement. It then
measures the two finite, unfiltered source calendars by their length and every
sum-tagged indexed entry. No physical queue law or manuscript closure follows.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLaterLiveCalendarMeasurability

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput p

abbrev IndexedSource (k : ℕ) :=
  ReferenceCompleteSuffixInputMeasurability.IndexedSource rate rewards C_star C_h k

abbrev NumericalCoordinates :=
  Bool × (Option (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℝ)))

abbrev ArrivalCoordinates := Bool × (Fin p.K → ℕ)

/-- The existing suffix record at an actual natural index. -/
abbrev indexedRecord (k : ℕ) (x : IndexedSource rate rewards C_star C_h k) :=
  ReferenceLaterLiveReadoutValuesMeasurability.actualRecord
    rate rewards C_star C_h k x

/-- The literal later-live readout on the existing complete-suffix record. -/
def indexedReadout (k : ℕ)
    (z : ℕ × IndexedSource rate rewards C_star C_h k) :
    Option (RecordedQueueRun.RoundInput p.K) :=
  ReferenceLaterLiveNumericalReadout.laterLiveReadout z.1
    (indexedRecord rate rewards C_star C_h k z.2)

/-- The exact joint domain of that same readout on the actual index subtype. -/
def indexedReadoutDomain (k : ℕ) :
    Set (ℕ × IndexedSource rate rewards C_star C_h k) :=
  {z | (indexedReadout rate rewards C_star C_h k z).isSome = true}

/-- The readout locus with its inherited product-source measurable space. -/
abbrev GenuineReadoutSource (k : ℕ) :=
  {z : ℕ × IndexedSource rate rewards C_star C_h k //
    z ∈ indexedReadoutDomain rate rewards C_star C_h k}

/-- Map the domain certificate to the exact subtype consumed by the value
producer. The underlying point and its genuine-readout certificate are kept. -/
private def toValuesReadoutSource (k : ℕ)
    (z : GenuineReadoutSource rate rewards C_star C_h k) :
    ReferenceLaterLiveReadoutValuesMeasurability.ReadoutSource
      rate rewards C_star C_h k :=
  ⟨z.1, z.2⟩

private theorem actualCell_eq_readoutGet (k : ℕ)
    (z : GenuineReadoutSource rate rewards C_star C_h k) :
    ReferenceLaterLiveReadoutValuesMeasurability.actualCell
      rate rewards C_star C_h k
      (toValuesReadoutSource rate rewards C_star C_h k z) =
    (indexedReadout rate rewards C_star C_h k z.1).get z.2 := by
  rfl

private theorem measurable_toValuesReadoutSource (k : ℕ) : Measurable
    (toValuesReadoutSource rate rewards C_star C_h k) := by
  exact measurable_subtype_coe.subtype_mk

private theorem measurableSet_indexedReadoutDomain (k : ℕ) :
    MeasurableSet (indexedReadoutDomain rate rewards C_star C_h k) := by
  simpa only [indexedReadoutDomain, indexedReadout, indexedRecord,
    ReferenceLaterLiveReadoutValuesMeasurability.actualRecord] using
    ReferenceLaterLiveReadoutDomain.measurableSet_indexedReadoutDomain
      rate rewards C_star C_h k

private theorem measurable_subtype_extension {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (s : Set Ω) [DecidablePred (fun x : Ω => x ∈ s)]
    (hs : MeasurableSet s)
    (f : {x : Ω // x ∈ s} → α) (hf : Measurable f) (outside : α) :
    Measurable (fun x : Ω => if hx : x ∈ s then f ⟨x, hx⟩ else outside) := by
  exact hf.dite measurable_const hs

private theorem indexedReadout_sumCode (k : ℕ)
    {α : Type*} (coordinates : RecordedQueueRun.RoundInput p.K → α)
    [DecidablePred (fun z : ℕ × IndexedSource rate rewards C_star C_h k =>
      z ∈ indexedReadoutDomain rate rewards C_star C_h k)]
    (z : ℕ × IndexedSource rate rewards C_star C_h k) :
    Equiv.optionEquivSumPUnit α
        ((indexedReadout rate rewards C_star C_h k z).map coordinates) =
      if hz : z ∈ indexedReadoutDomain rate rewards C_star C_h k then
        Sum.inl (coordinates
          (ReferenceLaterLiveReadoutValuesMeasurability.actualCell
            rate rewards C_star C_h k
            (toValuesReadoutSource rate rewards C_star C_h k ⟨z, hz⟩)))
      else Sum.inr PUnit.unit := by
  cases hr : indexedReadout rate rewards C_star C_h k z with
  | none => simp [indexedReadoutDomain, hr]
  | some cell =>
      have hz : z ∈ indexedReadoutDomain rate rewards C_star C_h k := by
        simp [indexedReadoutDomain, hr]
      have hcell :
          ReferenceLaterLiveReadoutValuesMeasurability.actualCell
              rate rewards C_star C_h k
              (toValuesReadoutSource rate rewards C_star C_h k ⟨z, hz⟩) = cell := by
        rw [actualCell_eq_readoutGet]
        simp [hr]
      simp [hr, indexedReadoutDomain]
      exact congrArg coordinates hcell.symm

private theorem measurable_indexedOptionMap (k : ℕ)
    {α : Type*} [MeasurableSpace α]
    (coordinates : RecordedQueueRun.RoundInput p.K → α)
    (hvalues : Measurable (fun z :
      ReferenceLaterLiveReadoutValuesMeasurability.ReadoutSource
        rate rewards C_star C_h k =>
      coordinates (ReferenceLaterLiveReadoutValuesMeasurability.actualCell
        rate rewards C_star C_h k z))) :
    @Measurable (ℕ × IndexedSource rate rewards C_star C_h k) (Option α)
      (inferInstance : MeasurableSpace
        (ℕ × IndexedSource rate rewards C_star C_h k))
      LaterAssignmentStartMeasurability.optionMeasurableSpace
      (fun z => (indexedReadout rate rewards C_star C_h k z).map coordinates) := by
  classical
  let : MeasurableSpace (Option α) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let locusValue : GenuineReadoutSource rate rewards C_star C_h k → α :=
    fun z => coordinates
      (ReferenceLaterLiveReadoutValuesMeasurability.actualCell
        rate rewards C_star C_h k
        (toValuesReadoutSource rate rewards C_star C_h k z))
  have hlocus : Measurable locusValue :=
    hvalues.comp (measurable_toValuesReadoutSource rate rewards C_star C_h k)
  have hleft : Measurable (fun z : GenuineReadoutSource rate rewards C_star C_h k =>
      (Sum.inl (locusValue z) : α ⊕ PUnit)) := measurable_inl.comp hlocus
  have hextension := measurable_subtype_extension
    (indexedReadoutDomain rate rewards C_star C_h k)
    (measurableSet_indexedReadoutDomain rate rewards C_star C_h k)
    (fun z : GenuineReadoutSource rate rewards C_star C_h k =>
      (Sum.inl (locusValue z) : α ⊕ PUnit))
    hleft (Sum.inr PUnit.unit : α ⊕ PUnit)
  have hcode : Measurable (fun z : ℕ × IndexedSource rate rewards C_star C_h k =>
      Equiv.optionEquivSumPUnit α
        ((indexedReadout rate rewards C_star C_h k z).map coordinates)) := by
    have heq :
        (fun z : ℕ × IndexedSource rate rewards C_star C_h k =>
          Equiv.optionEquivSumPUnit α
            ((indexedReadout rate rewards C_star C_h k z).map coordinates)) =
          fun z => if hz : z ∈ indexedReadoutDomain rate rewards C_star C_h k then
            Sum.inl (locusValue ⟨z, hz⟩) else Sum.inr PUnit.unit := by
      funext z
      simpa only [locusValue] using
        indexedReadout_sumCode rate rewards C_star C_h k coordinates z
    rw [heq]
    exact hextension
  exact measurable_comap_iff.mpr hcode

/-- Joint measurability of the numerical `Option.map` readout on
`ℕ × IndexedSource`. The absent branch remains `none` on the full complement
of the genuine domain. -/
theorem measurable_indexedNumericalReadout (k : ℕ) :
    @Measurable (ℕ × IndexedSource rate rewards C_star C_h k)
      (Option NumericalCoordinates)
      (inferInstance : MeasurableSpace
        (ℕ × IndexedSource rate rewards C_star C_h k))
      LaterAssignmentStartMeasurability.optionMeasurableSpace
      (fun z =>
      (indexedReadout rate rewards C_star C_h k z).map
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates) := by
  exact measurable_indexedOptionMap rate rewards C_star C_h k
    ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates
    (ReferenceLaterLiveReadoutValuesMeasurability.measurable_numericalCoordinates_actualCell
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k)

/-- Joint measurability of integer arrivals from the same readout, using the
original marker, complete reward and rate vectors, and exact `rate.n`. -/
theorem measurable_indexedArrivalReadout (k : ℕ) :
    @Measurable (ℕ × IndexedSource rate rewards C_star C_h k)
      (Option ArrivalCoordinates)
      (inferInstance : MeasurableSpace
        (ℕ × IndexedSource rate rewards C_star C_h k))
      LaterAssignmentStartMeasurability.optionMeasurableSpace
      (fun z =>
      (indexedReadout rate rewards C_star C_h k z).map
        (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)) := by
  exact measurable_indexedOptionMap rate rewards C_star C_h k
    (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)
    (ReferenceLaterLiveReadoutValuesMeasurability.measurable_arrivalCoordinates_actualCell
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) k)

-- This source map always uses the canonical Option sum-comap space. Later
-- calendar observations inherit this exact output space.
local instance (priority := 5000) canonicalArrivalOptionMeasurableSpace :
    MeasurableSpace (Option (ArrivalCoordinates (p := p))) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- Specialization of the joint numerical map to this original source's
actual physical start, on the same actual suffix-index subtype. -/
theorem measurable_indexedNumericalReadoutAtPhysicalStart (k : ℕ) :
    Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
        (indexedRecord rate rewards C_star C_h k x)).map
          ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates) := by
  have hstart : Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hpair : Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)) :=
    hstart.prodMk measurable_id
  exact (measurable_indexedNumericalReadout rate rewards C_star C_h k).comp hpair

/-- Specialization of the joint integer-arrival map to the source's actual
physical start. -/
theorem measurable_indexedArrivalReadoutAtPhysicalStart (k : ℕ) :
    Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
        (indexedRecord rate rewards C_star C_h k x)).map
          (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)) := by
  have hstart : Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h) :=
    (ReferenceCompleteSuffixInputMeasurability.measurable_physicalStart
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hpair : Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h, x)) :=
    hstart.prodMk measurable_id
  exact (measurable_indexedArrivalReadout rate rewards C_star C_h k).comp hpair

/-- The original numerical calendar: map the exact optional coordinates over
the existing unfiltered later-live partial calendar. -/
def laterLiveNumericalCalendar (source : SourceInput (p := p)) :=
  (ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
    rate rewards C_star C_h source).map (fun entry =>
      (entry.1, entry.2.map
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates))

/-- The original integer-arrival calendar, with the same times and optional
readouts as the numerical calendar. -/
def laterLiveArrivalCalendar (source : SourceInput (p := p)) :=
  (ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
    rate rewards C_star C_h source).map (fun entry =>
      (entry.1, entry.2.map
        (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)))

private theorem measurable_actualRecordTimeAt (k : ℕ) :
    Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      (indexedRecord rate rewards C_star C_h k x).input.time) := by
  let code := ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt
    rate rewards C_star C_h k
  have hcode : Measurable code :=
    ReferenceCompleteSuffixInputMeasurability.measurable_actualRecordCodeAt
      rate rewards C_star C_h k
  have hval : Measurable (fun x => (code x).1) := measurable_fst.comp hcode
  have hfields := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
    rate rewards C_star C_h k
  have hbound (x : IndexedSource rate rewards C_star C_h k) : (code x).1 < p.T := by
    have htime := (ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt
      rate rewards C_star C_h k x).time.isLt
    rw [hfields x |>.2.2.2.1] at htime
    exact htime
  have htime (i : Fin p.T) : MeasurableSet
      {x : IndexedSource rate rewards C_star C_h k |
        (indexedRecord rate rewards C_star C_h k x).input.time = i} := by
    have heq : {x : IndexedSource rate rewards C_star C_h k |
        (indexedRecord rate rewards C_star C_h k x).input.time = i} =
        {x | (code x).1 = i.val} := by
      ext x
      constructor
      · intro h
        calc
          (code x).1 = (ReferenceLaterLiveReadoutValuesMeasurability.actualRecord
              rate rewards C_star C_h k x).input.time.val := (hfields x).2.2.2.1.symm
          _ = i.val := congrArg Fin.val h
      · intro h
        apply Fin.ext
        calc
          (ReferenceLaterLiveReadoutValuesMeasurability.actualRecord
              rate rewards C_star C_h k x).input.time.val = (code x).1 :=
            (hfields x).2.2.2.1
          _ = i.val := h
    rw [heq]
    exact (measurableSet_singleton i.val).preimage hval
  intro s hs
  have hpre : {x : IndexedSource rate rewards C_star C_h k |
      (indexedRecord rate rewards C_star C_h k x).input.time ∈ s} =
        ⋃ i ∈ s, {x | (indexedRecord rate rewards C_star C_h k x).input.time = i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨(indexedRecord rate rewards C_star C_h k x).input.time, h, rfl⟩,
      fun ⟨i, hi, heq⟩ => heq.symm ▸ hi⟩
  change MeasurableSet {x | (indexedRecord rate rewards C_star C_h k x).input.time ∈ s}
  rw [hpre]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => htime i

private def numericalEntryAtIndex (k : ℕ)
    (x : IndexedSource rate rewards C_star C_h k) :=
  ((indexedRecord rate rewards C_star C_h k x).input.time,
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
      (indexedRecord rate rewards C_star C_h k x)).map
        ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates)

private def arrivalEntryAtIndex (k : ℕ)
    (x : IndexedSource rate rewards C_star C_h k) :=
  ((indexedRecord rate rewards C_star C_h k x).input.time,
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
      (indexedRecord rate rewards C_star C_h k x)).map
        (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate))

private theorem measurable_numericalEntryAtIndex (k : ℕ) :
    Measurable (numericalEntryAtIndex rate rewards C_star C_h k) := by
  exact (measurable_actualRecordTimeAt rate rewards C_star C_h k).prodMk
    (measurable_indexedNumericalReadoutAtPhysicalStart rate rewards C_star C_h k)

private theorem measurable_arrivalEntryAtIndex (k : ℕ) :
    Measurable (arrivalEntryAtIndex rate rewards C_star C_h k) := by
  exact (measurable_actualRecordTimeAt rate rewards C_star C_h k).prodMk
    (measurable_indexedArrivalReadoutAtPhysicalStart rate rewards C_star C_h k)

private theorem measurable_indexedSource_map (k : ℕ) :
    Measurable (fun x : {source : SourceInput (p := p) // k <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length} =>
      (⟨x.val, x.property⟩ : IndexedSource rate rewards C_star C_h k)) := by
  exact measurable_subtype_coe.subtype_mk

/-- Exact indexed values in the numerical calendar, including every absent
readout and every enabled zero-valued cell. -/
theorem laterLiveNumericalCalendar_get (source : SourceInput (p := p))
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (laterLiveNumericalCalendar rate rewards C_star C_h source).get ⟨k.val, by
      simp [laterLiveNumericalCalendar,
        ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar]⟩ =
      Prod.mk ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).input.time
        ((ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k)).map
          ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates) := by
  simp [laterLiveNumericalCalendar,
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar]

/-- Exact indexed values in the integer-arrival calendar, retaining `none`
separately from the genuine zero arrival vector. -/
theorem laterLiveArrivalCalendar_get (source : SourceInput (p := p))
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (laterLiveArrivalCalendar rate rewards C_star C_h source).get ⟨k.val, by
      simp [laterLiveArrivalCalendar,
        ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar]⟩ =
      Prod.mk ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k).input.time
        ((ReferenceLaterLiveNumericalReadout.laterLiveReadout
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k)).map
          (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)) := by
  simp [laterLiveArrivalCalendar,
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar]

private theorem measurable_numericalEntryObservation (k : ℕ) : Measurable
    (fun source : SourceInput (p := p) =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (laterLiveNumericalCalendar rate rewards C_star C_h source) k) := by
  classical
  let indexDomain : Set (SourceInput (p := p)) :=
    {source | k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length}
  have hdomain : MeasurableSet indexDomain :=
    ReferenceCompleteSuffixInputMeasurability.measurableSet_indexDomain
      rate rewards C_star C_h k
  let onIndex : {source : SourceInput (p := p) // source ∈ indexDomain} →
      Unit ⊕ (Fin p.T × Option NumericalCoordinates) :=
    fun x => Sum.inr (numericalEntryAtIndex rate rewards C_star C_h k
      (⟨x.val, x.property⟩ : IndexedSource rate rewards C_star C_h k))
  have hindexMap : Measurable (fun x :
      {source : SourceInput (p := p) // source ∈ indexDomain} =>
        (⟨x.val, x.property⟩ : IndexedSource rate rewards C_star C_h k)) :=
    measurable_indexedSource_map rate rewards C_star C_h k
  have honIndex : Measurable onIndex :=
    measurable_inr.comp ((measurable_numericalEntryAtIndex rate rewards C_star C_h k).comp
      hindexMap)
  have hext := measurable_subtype_extension indexDomain hdomain onIndex honIndex
    (Sum.inl () : Unit ⊕ (Fin p.T × Option NumericalCoordinates))
  have hpointwise :
      (fun source : SourceInput (p := p) =>
        ReferenceActiveHorizonMeasurability.listObservationAt
          (laterLiveNumericalCalendar rate rewards C_star C_h source) k) =
      fun source => if hk : source ∈ indexDomain then onIndex ⟨source, hk⟩ else Sum.inl () := by
    funext source
    by_cases hk : source ∈ indexDomain
    · have hkBound : k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length := by
          simpa only [indexDomain, Set.mem_ofPred_eq] using hk
      have hget := laterLiveNumericalCalendar_get rate rewards C_star C_h source
        (⟨k, hkBound⟩ : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length)
      have hbound : k < (laterLiveNumericalCalendar rate rewards C_star C_h source).length := by
        simpa [laterLiveNumericalCalendar,
          ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar] using hkBound
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hbound]
      have hgetNat : (laterLiveNumericalCalendar rate rewards C_star C_h source)[k]'hbound =
          (((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get ⟨k, hkBound⟩).input.time,
            (ReferenceLaterLiveNumericalReadout.laterLiveReadout
              (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h).get ⟨k, hkBound⟩)).map
              ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates) := by
        simpa only [List.get_eq_getElem, Fin.val_mk] using hget
      rw [hgetNat]
      simp only [dite_eq_left hk, onIndex]
      rfl
    · have hnot : ¬ k < (laterLiveNumericalCalendar rate rewards C_star C_h source).length := by
        have hkBound : ¬ k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length := by
            simpa only [indexDomain, Set.mem_ofPred_eq] using hk
        simpa [laterLiveNumericalCalendar,
          ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar] using hkBound
      simp [ReferenceActiveHorizonMeasurability.listObservationAt, hnot, hk]
  rw [hpointwise]
  exact hext

private theorem measurable_arrivalEntryObservation (k : ℕ) : Measurable
    (fun source : SourceInput (p := p) =>
      ReferenceActiveHorizonMeasurability.listObservationAt
        (laterLiveArrivalCalendar rate rewards C_star C_h source) k) := by
  classical
  let indexDomain : Set (SourceInput (p := p)) :=
    {source | k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length}
  have hdomain : MeasurableSet indexDomain :=
    ReferenceCompleteSuffixInputMeasurability.measurableSet_indexDomain
      rate rewards C_star C_h k
  let onIndex : {source : SourceInput (p := p) // source ∈ indexDomain} →
      Unit ⊕ (Fin p.T × Option ArrivalCoordinates) :=
    fun x => Sum.inr (arrivalEntryAtIndex rate rewards C_star C_h k
      (⟨x.val, x.property⟩ : IndexedSource rate rewards C_star C_h k))
  have hindexMap : Measurable (fun x :
      {source : SourceInput (p := p) // source ∈ indexDomain} =>
        (⟨x.val, x.property⟩ : IndexedSource rate rewards C_star C_h k)) :=
    measurable_indexedSource_map rate rewards C_star C_h k
  have honIndex : Measurable onIndex :=
    measurable_inr.comp ((measurable_arrivalEntryAtIndex rate rewards C_star C_h k).comp
      hindexMap)
  have hext := measurable_subtype_extension indexDomain hdomain onIndex honIndex
    (Sum.inl () : Unit ⊕ (Fin p.T × Option ArrivalCoordinates))
  have hpointwise :
      (fun source : SourceInput (p := p) =>
        ReferenceActiveHorizonMeasurability.listObservationAt
          (laterLiveArrivalCalendar rate rewards C_star C_h source) k) =
      fun source => if hk : source ∈ indexDomain then onIndex ⟨source, hk⟩ else Sum.inl () := by
    funext source
    by_cases hk : source ∈ indexDomain
    · have hkBound : k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length := by
          simpa only [indexDomain, Set.mem_ofPred_eq] using hk
      have hget := laterLiveArrivalCalendar_get rate rewards C_star C_h source
        (⟨k, hkBound⟩ : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length)
      have hbound : k < (laterLiveArrivalCalendar rate rewards C_star C_h source).length := by
        simpa [laterLiveArrivalCalendar,
          ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar] using hkBound
      simp only [ReferenceActiveHorizonMeasurability.listObservationAt,
        List.getElem?_eq_getElem hbound]
      have hgetNat : (laterLiveArrivalCalendar rate rewards C_star C_h source)[k]'hbound =
          (((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get ⟨k, hkBound⟩).input.time,
            (ReferenceLaterLiveNumericalReadout.laterLiveReadout
              (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h).get ⟨k, hkBound⟩)).map
              (ReferenceLaterLiveReadoutValuesMeasurability.arrivalCoordinates rate)) := by
        simpa only [List.get_eq_getElem, Fin.val_mk] using hget
      rw [hgetNat]
      simp only [dite_eq_left hk, onIndex]
      rfl
    · have hnot : ¬ k < (laterLiveArrivalCalendar rate rewards C_star C_h source).length := by
        have hkBound : ¬ k < (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length := by
            simpa only [indexDomain, Set.mem_ofPred_eq] using hk
        simpa [laterLiveArrivalCalendar,
          ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar] using hkBound
      simp [ReferenceActiveHorizonMeasurability.listObservationAt, hnot, hk]
  rw [hpointwise]
  exact hext

/-- The numerical list map is measurable on the full original source product.
Its measurable list code consists of its exact length and all indexed,
sum-tagged optional entries. -/
theorem measurable_laterLiveNumericalCalendar :
    Measurable (laterLiveNumericalCalendar rate rewards C_star C_h) := by
  apply measurable_comap_iff.mpr
  have hcode := ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
    (rate := rate) rewards C_star C_h
  have hcodeCoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hcode
  have hlength : Measurable (fun source : SourceInput (p := p) =>
      (laterLiveNumericalCalendar rate rewards C_star C_h source).length) := by
    have heq : (fun source : SourceInput (p := p) =>
        (laterLiveNumericalCalendar rate rewards C_star C_h source).length) =
        fun source => (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h source).length := by
      funext source
      calc
        (laterLiveNumericalCalendar rate rewards C_star C_h source).length =
            (ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
              rate rewards C_star C_h source).length := by
                simp only [laterLiveNumericalCalendar, List.length_map]
        _ = p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h :=
          ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar_length
            rate rewards C_star C_h source
        _ = (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
            (rate := rate) rewards C_star C_h source).length :=
          (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_length
            (rate := rate) rewards C_star C_h source).symm
    rw [heq]
    exact measurable_fst.comp hcodeCoordinates
  have hstream : Measurable (fun source : SourceInput (p := p) =>
      fun k => ReferenceActiveHorizonMeasurability.listObservationAt
        (laterLiveNumericalCalendar rate rewards C_star C_h source) k) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_numericalEntryObservation rate rewards C_star C_h k
  have hcoordinates : Measurable (fun source : SourceInput (p := p) =>
      ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (laterLiveNumericalCalendar rate rewards C_star C_h source)) := by
    convert hlength.prodMk hstream using 1
    funext source
    rfl
  exact hcoordinates

/-- The integer-arrival list map is measurable on the full original source
product, retaining the complete finite length-indexed calendar. -/
theorem measurable_laterLiveArrivalCalendar :
    Measurable (laterLiveArrivalCalendar rate rewards C_star C_h) := by
  apply measurable_comap_iff.mpr
  have hcode := ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
    (rate := rate) rewards C_star C_h
  have hcodeCoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp hcode
  have hlength : Measurable (fun source : SourceInput (p := p) =>
      (laterLiveArrivalCalendar rate rewards C_star C_h source).length) := by
    have heq : (fun source : SourceInput (p := p) =>
        (laterLiveArrivalCalendar rate rewards C_star C_h source).length) =
        fun source => (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h source).length := by
      funext source
      calc
        (laterLiveArrivalCalendar rate rewards C_star C_h source).length =
            (ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar
              rate rewards C_star C_h source).length := by
                simp only [laterLiveArrivalCalendar, List.length_map]
        _ = p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h :=
          ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar_length
            rate rewards C_star C_h source
        _ = (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
            (rate := rate) rewards C_star C_h source).length :=
          (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_length
            (rate := rate) rewards C_star C_h source).symm
    rw [heq]
    exact measurable_fst.comp hcodeCoordinates
  have hstream : Measurable (fun source : SourceInput (p := p) =>
      fun k => ReferenceActiveHorizonMeasurability.listObservationAt
        (laterLiveArrivalCalendar rate rewards C_star C_h source) k) := by
    apply measurable_pi_iff.mpr
    intro k
    exact measurable_arrivalEntryObservation rate rewards C_star C_h k
  have hcoordinates : Measurable (fun source : SourceInput (p := p) =>
      ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (laterLiveArrivalCalendar rate rewards C_star C_h source)) := by
    convert hlength.prodMk hstream using 1
    funext source
    rfl
  exact hcoordinates

/-- Both calendars have exactly the original complete suffix length. -/
theorem laterLiveNumericalCalendar_length (source : SourceInput (p := p)) :
    (laterLiveNumericalCalendar rate rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp [laterLiveNumericalCalendar,
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar_length]

theorem laterLiveArrivalCalendar_length (source : SourceInput (p := p)) :
    (laterLiveArrivalCalendar rate rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp [laterLiveArrivalCalendar,
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar_length]

/-- Both mapped lists retain the exact physical-time stream of the existing
partial calendar. -/
theorem laterLiveNumericalCalendar_times (source : SourceInput (p := p)) :
    (laterLiveNumericalCalendar rate rewards C_star C_h source).map
        (fun entry => entry.1.val) =
      ReferenceActivePhysicalHorizon.calendar
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  simpa [laterLiveNumericalCalendar, List.map_map, Function.comp_def] using
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar_times
      rate rewards C_star C_h source

theorem laterLiveArrivalCalendar_times (source : SourceInput (p := p)) :
    (laterLiveArrivalCalendar rate rewards C_star C_h source).map
        (fun entry => entry.1.val) =
      ReferenceActivePhysicalHorizon.calendar
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  simpa [laterLiveArrivalCalendar, List.map_map, Function.comp_def] using
    ReferenceLaterLiveNumericalReadout.laterLivePartialCalendar_times
      rate rewards C_star C_h source

/-- A no-launch path has physical start `T`, so its original suffix and both
optional calendars are empty. -/
theorem laterLiveNumericalCalendar_empty_of_no_launch (source : SourceInput (p := p))
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    laterLiveNumericalCalendar rate rewards C_star C_h source = [] := by
  have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
    rate source rewards C_star C_h hno
  cases hcal : laterLiveNumericalCalendar rate rewards C_star C_h source with
  | nil => rfl
  | cons head tail =>
      have hlen := laterLiveNumericalCalendar_length rate rewards C_star C_h source
      rw [hcal, hstart] at hlen
      simp at hlen

theorem laterLiveArrivalCalendar_empty_of_no_launch (source : SourceInput (p := p))
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    laterLiveArrivalCalendar rate rewards C_star C_h source = [] := by
  have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
    rate source rewards C_star C_h hno
  cases hcal : laterLiveArrivalCalendar rate rewards C_star C_h source with
  | nil => rfl
  | cons head tail =>
      have hlen := laterLiveArrivalCalendar_length rate rewards C_star C_h source
      rw [hcal, hstart] at hlen
      simp at hlen

/-- A terminal launch retains its existing empty suffix. The premise is the
actual terminal physical boundary of the existing source, with its launch
witness. -/
theorem laterLiveNumericalCalendar_empty_of_terminal_launch (source : SourceInput (p := p))
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    laterLiveNumericalCalendar rate rewards C_star C_h source = [] := by
  have hterminal := ReferenceCompletePhysicalHistory.terminal_crossing_sentinel_round
    rate source rewards C_star C_h active hlaunch hstart
  have hnonempty := hterminal.1
  rw [hlaunch] at hnonempty
  cases hcal : laterLiveNumericalCalendar rate rewards C_star C_h source with
  | nil => rfl
  | cons head tail =>
      have hlen := laterLiveNumericalCalendar_length rate rewards C_star C_h source
      rw [hcal, hstart] at hlen
      simp at hlen

theorem laterLiveArrivalCalendar_empty_of_terminal_launch (source : SourceInput (p := p))
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    laterLiveArrivalCalendar rate rewards C_star C_h source = [] := by
  have hterminal := ReferenceCompletePhysicalHistory.terminal_crossing_sentinel_round
    rate source rewards C_star C_h active hlaunch hstart
  have hnonempty := hterminal.1
  rw [hlaunch] at hnonempty
  cases hcal : laterLiveArrivalCalendar rate rewards C_star C_h source with
  | nil => rfl
  | cons head tail =>
      have hlen := laterLiveArrivalCalendar_length rate rewards C_star C_h source
      rw [hcal, hstart] at hlen
      simp at hlen

end Bandits.Support.ReferenceLaterLiveCalendarMeasurability

end
