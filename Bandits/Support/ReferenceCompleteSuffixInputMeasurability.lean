/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterLiveNumericalReadout

/-!
# Borel inputs at actual complete-suffix indices

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The index domain restricts the original source to sources having an actual
record at that index. Its input and record code are literal projections of
that same record in the existing complete suffix. The measurable structures
are the existing source product space, induced subtype space, lossless state
and input comaps, and length/index-generated list space. The reconstruction
retains whole continuous rows, the original selected index and whole rewards.

These are unconditional internal Borel producers on the displayed index
domain. They establish neither numerical readout coverage, physical queue or
score truth, smaller local-history adaptation, nor an execution law or any
manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCompleteSuffixInputMeasurability

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The genuine source subtype on which the existing suffix has index `k`.
There is no record or input assigned outside this domain. -/
abbrev IndexedSource (k : ℕ) :=
  {source : BootstrapPrivateRoundStreams.SourceInput p // k <
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length}

/-- The input of the actual record at `k`, without replay or padding. -/
def actualRoundInputAt (k : ℕ) (x : IndexedSource rate rewards C_star C_h k) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate x.val rewards C_star C_h).get ⟨k, x.property⟩).input

/-- H's existing lossless code of the very same actual record. -/
def actualRecordCodeAt (k : ℕ) (x : IndexedSource rate rewards C_star C_h k) :
    ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) :=
  ReferenceActiveHorizonMeasurability.roundRecordCode
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate x.val rewards C_star C_h).get ⟨k, x.property⟩)

private theorem measurable_suffixLength : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length) := by
  have hcoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
      (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
        (rate := rate) rewards C_star C_h)
  simpa only [Function.comp_def,
    ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode, List.length_map]
    using measurable_fst.comp hcoordinates

/-- Having an actual record at a fixed natural index is a Borel source event. -/
theorem measurableSet_indexDomain (k : ℕ) : MeasurableSet
    {source : BootstrapPrivateRoundStreams.SourceInput p | k <
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).length} :=
  measurableSet_lt measurable_const (measurable_suffixLength rate rewards C_star C_h)

-- Only the existing code list is optionally observed off the index domain.
-- The public input and record-code definitions above have no off-domain value.
private def recordCodeOptionAt (k : ℕ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) :=
  Sum.elim (fun _ => none) some
    (ReferenceActiveHorizonMeasurability.listObservationAt
      (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
        (rate := rate) rewards C_star C_h source) k)

private theorem measurable_recordCodeOptionAt (k : ℕ) :
    Measurable (recordCodeOptionAt rate rewards C_star C_h k) := by
  have hsome : Measurable
      (some : ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate) → Option _) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have htag : Measurable
      (Sum.elim (fun _ : Unit =>
        (none : Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate)))) some) :=
    Measurable.sumElim measurable_const hsome
  have hcoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
      (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
        (rate := rate) rewards C_star C_h)
  exact htag.comp ((measurable_pi_apply k).comp (measurable_snd.comp hcoordinates))

private theorem recordCodeOptionAt_some (k : ℕ)
    (x : IndexedSource rate rewards C_star C_h k) :
    recordCodeOptionAt rate rewards C_star C_h k x.val =
      some (actualRecordCodeAt rate rewards C_star C_h k x) := by
  simp only [recordCodeOptionAt,
    ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
    ReferenceActiveHorizonMeasurability.listObservationAt, List.getElem?_map,
    List.getElem?_eq_getElem x.property, Option.map_some, actualRecordCodeAt,
    List.get_eq_getElem]
  rfl

-- Mathlib's measurable embedding API extracts the value after the actual
-- equality to `some` is proved. The Option space is the existing canonical
-- comap along optionEquivSumPUnit; no new Option instances are introduced.
private theorem measurable_of_some {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] (f : Ω → α)
    (hf : Measurable (fun x => some (f x))) : Measurable f := by
  have hencode : Measurable (Equiv.optionEquivSumPUnit α) := comap_measurable _
  have hsum : Measurable (fun x => (Sum.inl (f x) : α ⊕ PUnit)) := hencode.comp hf
  have hinl : MeasurableEmbedding (@Sum.inl α PUnit) :=
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩
  exact hinl.measurable_comp_iff.mp hsum

/-- Joint Borelness in all original source factors on the genuine index domain. -/
theorem measurable_actualRecordCodeAt (k : ℕ) :
    Measurable (actualRecordCodeAt rate rewards C_star C_h k) := by
  apply measurable_of_some
  have h : Measurable (fun x : IndexedSource rate rewards C_star C_h k =>
      recordCodeOptionAt rate rewards C_star C_h k x.val) :=
    (measurable_recordCodeOptionAt rate rewards C_star C_h k).comp measurable_subtype_coe
  have heq : (fun x : IndexedSource rate rewards C_star C_h k =>
      recordCodeOptionAt rate rewards C_star C_h k x.val) =
      fun x => some (actualRecordCodeAt rate rewards C_star C_h k x) :=
    funext (recordCodeOptionAt_some rate rewards C_star C_h k)
  rwa [heq] at h

private theorem record_input_fields (k : ℕ)
    (x : IndexedSource rate rewards C_star C_h k) :
    (actualRoundInputAt rate rewards C_star C_h k x).rows = x.val.1.2 ∧
      (actualRoundInputAt rate rewards C_star C_h k x).selected =
        ActualInitializationPhysicalStep.selectedRowIndex p x.val ∧
      (actualRoundInputAt rate rewards C_star C_h k x).rewards = rewards := by
  classical
  obtain ⟨hcross, hspan, hrecord⟩ :=
    ReferenceLaterLiveNumericalReadout.source_record_prefix
      rate rewards C_star C_h x.val ⟨k, x.property⟩
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate x.val rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate x.val rewards C_star C_h hcross
  have hactive : ReferenceActivePhysicalHorizon.allActiveAtStart initial
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h) :=
    seed.activeAtStart
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial x.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
    k hspan hactive
  have hmember : record ∈ (ReferenceActivePhysicalHorizon.run initial x.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
      (k + 1) hspan hactive).records := by
    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
      initial x.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p x.val)
      rewards (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
      k hspan hactive]
    exact List.mem_append_right _ (by simp only [List.mem_singleton]; rfl)
  have hfields := ReferenceActivePhysicalHorizon.run_record_inputs initial x.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p x.val) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate x.val rewards C_star C_h)
    (k + 1) hspan hactive record hmember
  unfold actualRoundInputAt
  rw [hrecord]
  exact hfields

/-- Full input coordinates of the actual record, including its incoming state.
Rows, selected index and rewards follow from membership in the actual run;
time and state are the literal coordinates of this same record's code. -/
theorem actualRoundInputAt_fields (k : ℕ)
    (x : IndexedSource rate rewards C_star C_h k) :
    (actualRoundInputAt rate rewards C_star C_h k x).rows = x.val.1.2 ∧
      (actualRoundInputAt rate rewards C_star C_h k x).selected =
        ActualInitializationPhysicalStep.selectedRowIndex p x.val ∧
      (actualRoundInputAt rate rewards C_star C_h k x).rewards = rewards ∧
      (actualRoundInputAt rate rewards C_star C_h k x).time.val =
        (actualRecordCodeAt rate rewards C_star C_h k x).1 ∧
      ReferenceActivePhysicalStepMeasurability.encodeState
          (actualRoundInputAt rate rewards C_star C_h k x).state =
        (actualRecordCodeAt rate rewards C_star C_h k x).2.1 := by
  obtain ⟨hrows, hselected, hrewards⟩ := record_input_fields rate rewards C_star C_h k x
  exact ⟨hrows, hselected, hrewards, rfl, rfl⟩

/-- The full existing input is Borel, with no ordinary, successful, live,
readout or adaptation hypothesis. All original source coordinates are retained. -/
theorem measurable_actualRoundInputAt (k : ℕ) :
    Measurable (actualRoundInputAt rate rewards C_star C_h k) := by
  apply measurable_comap_iff.mpr
  let input := actualRoundInputAt rate rewards C_star C_h k
  have hcode := measurable_actualRecordCodeAt rate rewards C_star C_h k
  have hfields (x : IndexedSource rate rewards C_star C_h k) :=
    actualRoundInputAt_fields rate rewards C_star C_h k x
  have hstate : Measurable (fun x => (input x).state) := by
    apply measurable_comap_iff.mpr
    exact measurable_fst.comp (measurable_snd.comp hcode)
  have hrows : Measurable (fun x => (input x).rows) := by
    have heq : (fun x => (input x).rows) = fun x => x.val.1.2 :=
      funext fun x => (hfields x).1
    rw [heq]
    exact measurable_snd.comp
      ((BootstrapPrivateRoundStreams.measurable_sourcePublishedOutput p).comp
        measurable_subtype_coe)
  have hselected : Measurable (fun x => (input x).selected) := by
    have heq : (fun x => (input x).selected) =
        fun x => ActualInitializationPhysicalStep.selectedRowIndex p x.val :=
      funext fun x => (hfields x).2.1
    rw [heq]
    exact (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp
      measurable_subtype_coe
  have htimeVal : Measurable (fun x => (input x).time.val) :=
    measurable_fst.comp hcode
  have htime : Measurable (fun x => (input x).time) := by
    intro s _hs
    have hfiber (i : Fin p.T) : MeasurableSet
        {x : IndexedSource rate rewards C_star C_h k | (input x).time = i} := by
      have heq : {x : IndexedSource rate rewards C_star C_h k | (input x).time = i} =
          {x | (input x).time.val = i.val} := by
        ext x
        exact ⟨fun h => congrArg Fin.val h, Fin.ext⟩
      rw [heq]
      exact (measurableSet_singleton i.val).preimage htimeVal
    have hpre : {x : IndexedSource rate rewards C_star C_h k | (input x).time ∈ s} =
        ⋃ i ∈ s, {x : IndexedSource rate rewards C_star C_h k | (input x).time = i} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
      exact ⟨fun h => ⟨(input x).time, h, rfl⟩,
        fun ⟨i, hi, heq⟩ => heq.symm ▸ hi⟩
    change MeasurableSet {x | (input x).time ∈ s}
    rw [hpre]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hfiber i
  have hrewards : Measurable (fun x => (input x).rewards) := by
    have heq : (fun x => (input x).rewards) = fun _ => rewards :=
      funext fun x => (hfields x).2.2.1
    rw [heq]
    exact measurable_const
  have hcoordinates :=
    hstate.prodMk (hrows.prodMk (hselected.prodMk (htime.prodMk hrewards)))
  exact hcoordinates.subtype_mk

/-- Recover the actual physical start from the actual suffix code length.
No launch and launch at `T` both retain their genuine empty suffix. -/
theorem physicalStart_eq_horizon_sub_code_length
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
      p.T - (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
        (rate := rate) rewards C_star C_h source).length := by
  rw [ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_length]
  have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  omega

/-- The actual source-generated physical start is jointly Borel in the whole
original source, including the no-launch and terminal-launch paths. -/
theorem measurable_physicalStart : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  have hcoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates.comp
      (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
        (rate := rate) rewards C_star C_h)
  have hlength : Measurable (fun source =>
      (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
        (rate := rate) rewards C_star C_h source).length) := measurable_fst.comp hcoordinates
  have hsub : Measurable (fun n : ℕ => p.T - n) := measurable_from_nat
  have heq : (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) =
      fun source => p.T -
        (ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
          (rate := rate) rewards C_star C_h source).length :=
    funext (physicalStart_eq_horizon_sub_code_length rate rewards C_star C_h)
  rw [heq]
  exact hsub.comp hlength

end Bandits.Support.ReferenceCompleteSuffixInputMeasurability
