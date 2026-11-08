/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteObservationCalendarDecoders
public import Bandits.Support.ReferenceFirstPhasesNumericalObservationIdentification

/-!
# First-phase projections of the complete observation

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The raw projections below retain every observation position and optional
numerical cell.  They are administrative maps on the complete observation
carrier; they do not define another calendar or physical execution.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCompleteFirstPhaseObservationRecovery

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  ReferenceCompleteObservationCalendarDecoders.SourceInput p

abbrev OBS {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceCompleteObservationCalendarDecoders.OBS rate

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)


/-- The unmasked LIVE coordinate of each retained complete-observation entry.
This total administrative projection preserves all dates and absent cells. -/
def rawLiveNumericalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
  Omega.map fun entry => (entry.1, ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2)

/-- The unmasked collection coordinate of each retained complete-observation
entry.  No assignment-sigma test is applied. -/
def rawCollectionNumericalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
  Omega.map fun entry => (entry.1, ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2)

/-- The raw LIVE projection followed by the admitted numerical arrival map. -/
def rawLiveArrivalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (Bool × (Fin p.K → ℕ))) :=
  (rawLiveNumericalDecoder rate Omega).map fun cell =>
    (cell.1, cell.2.map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

/-- The raw collection projection followed by the admitted numerical arrival
map. -/
def rawCollectionArrivalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (Bool × (Fin p.K → ℕ))) :=
  (rawCollectionNumericalDecoder rate Omega).map fun cell =>
    (cell.1, cell.2.map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

private theorem measurable_leftProjection :
    Measurable (ReferenceCompleteNumericalBranchObservation.leftProjection (p := p)) := by
  apply measurable_comap_iff.mpr
  let Code := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  let inputEquiv := Equiv.optionEquivSumPUnit (Code ⊕ Code)
  let outputEquiv := Equiv.optionEquivSumPUnit Code
  let decode : (Code ⊕ Code) ⊕ PUnit → Code ⊕ PUnit :=
    Sum.elim
      (fun value => Sum.elim (fun cell => Sum.inl cell) (fun _ => Sum.inr PUnit.unit) value)
      (fun _ => Sum.inr PUnit.unit)
  have hinput : Measurable inputEquiv := comap_measurable inputEquiv
  have hdecode : Measurable decode := by
    dsimp [decode]
    exact ((measurable_inl.comp measurable_id).sumElim measurable_const).sumElim
      measurable_const
  have heq :
      (fun value => outputEquiv (ReferenceCompleteNumericalBranchObservation.leftProjection value)) =
        fun value => decode (inputEquiv value) := by
    funext value
    cases value with
    | none => rfl
    | some cell => cases cell <;> rfl
  change Measurable (fun value => outputEquiv (ReferenceCompleteNumericalBranchObservation.leftProjection value))
  rw [heq]
  exact hdecode.comp hinput

private theorem measurable_rightProjection :
    Measurable (ReferenceCompleteNumericalBranchObservation.rightProjection (p := p)) := by
  apply measurable_comap_iff.mpr
  let Code := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p
  let inputEquiv := Equiv.optionEquivSumPUnit (Code ⊕ Code)
  let outputEquiv := Equiv.optionEquivSumPUnit Code
  let decode : (Code ⊕ Code) ⊕ PUnit → Code ⊕ PUnit :=
    Sum.elim
      (fun value => Sum.elim (fun _ => Sum.inr PUnit.unit) (fun cell => Sum.inl cell) value)
      (fun _ => Sum.inr PUnit.unit)
  have hinput : Measurable inputEquiv := comap_measurable inputEquiv
  have hdecode : Measurable decode := by
    dsimp [decode]
    exact (measurable_const.sumElim (measurable_inl.comp measurable_id)).sumElim
      measurable_const
  have heq :
      (fun value => outputEquiv (ReferenceCompleteNumericalBranchObservation.rightProjection value)) =
        fun value => decode (inputEquiv value) := by
    funext value
    cases value with
    | none => rfl
    | some cell => cases cell <;> rfl
  change Measurable (fun value => outputEquiv (ReferenceCompleteNumericalBranchObservation.rightProjection value))
  rw [heq]
  exact hdecode.comp hinput

private theorem measurable_rawLiveEntry :
    Measurable (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (entry.1, ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2)) := by
  exact measurable_fst.prodMk
    ((measurable_leftProjection (p := p)).comp
      (measurable_snd.comp (measurable_snd.comp measurable_id)))

private theorem measurable_rawCollectionEntry :
    Measurable (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (entry.1, ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2)) := by
  exact measurable_fst.prodMk
    ((measurable_rightProjection (p := p)).comp
      (measurable_snd.comp (measurable_snd.comp measurable_id)))

theorem measurable_rawLiveNumericalDecoder :
    Measurable (rawLiveNumericalDecoder rate) := by
  let : MeasurableSpace (Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
      (α := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    id measurable_id
    (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (entry.1, ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2))
    (measurable_rawLiveEntry rate)

theorem measurable_rawCollectionNumericalDecoder :
    Measurable (rawCollectionNumericalDecoder rate) := by
  let : MeasurableSpace (Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
      (α := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    id measurable_id
    (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (entry.1, ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2))
    (measurable_rawCollectionEntry rate)

private theorem measurable_optionMap {X A C : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace C]
    (g : X → Option A)
    (hg : @Measurable X (Option A) ‹MeasurableSpace X›
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := A)) g)
    (f : A → C) (hf : Measurable f) :
    @Measurable X (Option C) ‹MeasurableSpace X›
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := C))
      (fun x => (g x).map f) := by
  change @Measurable X (Option C) ‹MeasurableSpace X›
    ((inferInstance : MeasurableSpace (C ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit C)) (fun x => (g x).map f)
  apply measurable_comap_iff.mpr
  let inputEquiv := Equiv.optionEquivSumPUnit A
  let outputEquiv := Equiv.optionEquivSumPUnit C
  have hinput : Measurable (fun x => inputEquiv (g x)) :=
    (comap_measurable inputEquiv).comp hg
  have hsum : Measurable (fun value : A ⊕ PUnit =>
      Sum.elim (fun a : A => (Sum.inl (f a) : C ⊕ PUnit))
        (fun _ : PUnit => Sum.inr PUnit.unit) value) :=
    (measurable_inl.comp hf).sumElim measurable_const
  have heq :
      (fun x => outputEquiv ((g x).map f)) =
        fun x => Sum.elim (fun a : A => (Sum.inl (f a) : C ⊕ PUnit))
          (fun _ : PUnit => Sum.inr PUnit.unit) (inputEquiv (g x)) := by
    funext x
    cases g x <;> rfl
  change Measurable (fun x => outputEquiv ((g x).map f))
  rw [heq]
  exact hsum.comp hinput

private theorem laterOptionSpace_eq_top {A : Type*} (mA : MeasurableSpace A)
    (hA : mA = ⊤) :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace A mA = ⊤ := by
  subst mA
  let _ : MeasurableSpace A := ⊤
  let e := Equiv.optionEquivSumPUnit A
  have hsum : (inferInstance : MeasurableSpace (A ⊕ PUnit)) = ⊤ := by
    ext s
    rw [measurableSet_sum_iff]
    simp
  have hcomap : (MeasurableSpace.comap e (⊤ : MeasurableSpace (A ⊕ PUnit))) = ⊤ := by
    apply MeasurableSpace.ext
    intro s
    rw [MeasurableSpace.measurableSet_comap]
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨e '' s, trivial, ?_⟩
      ext x
      simp [e.injective]
  unfold LaterAssignmentStartMeasurability.optionMeasurableSpace
  rw [hsum]
  exact hcomap

private theorem measurable_rawArrivalCell :
    Measurable (fun cell : Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
      (cell.1, cell.2.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))) := by
  let Arrival := Bool × (Fin p.K → ℕ)
  have hoption : @Measurable
      (Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) (Option Arrival)
      (LaterAssignmentStartMeasurability.optionMeasurableSpace
        (α := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := Arrival))
      (fun value => value.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) :=
    measurable_optionMap id measurable_id
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)
      (ReferenceLaterCollectionSourceReadoutMeasurability.measurable_arrivalsFromNumerical rate)
  have hArrivalSpace : (inferInstance : MeasurableSpace Arrival) = ⊤ := by
    apply le_antisymm le_top
    intro s hs
    exact (Set.to_countable s).measurableSet
  have hOptionSpace := laterOptionSpace_eq_top
    (A := Arrival) (inferInstance : MeasurableSpace Arrival) hArrivalSpace
  have hoptionTop : @Measurable
      (Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) (Option Arrival)
      (LaterAssignmentStartMeasurability.optionMeasurableSpace
        (α := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace Arrival)
      (fun value => value.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) := by
    exact hoption.mono le_rfl (by rw [hOptionSpace]; exact le_rfl)
  exact measurable_fst.prodMk (hoptionTop.comp measurable_snd)

theorem measurable_rawLiveArrivalDecoder :
    Measurable (rawLiveArrivalDecoder rate) := by
  let : MeasurableSpace (Option (Bool × (Fin p.K → ℕ))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (rawLiveNumericalDecoder rate) (measurable_rawLiveNumericalDecoder rate)
    (fun cell : Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
      (cell.1, cell.2.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))
    (measurable_rawArrivalCell rate)

theorem measurable_rawCollectionArrivalDecoder :
    Measurable (rawCollectionArrivalDecoder rate) := by
  let : MeasurableSpace (Option (Bool × (Fin p.K → ℕ))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (rawCollectionNumericalDecoder rate)
    (measurable_rawCollectionNumericalDecoder rate)
    (fun cell : Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
      (cell.1, cell.2.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))
    (measurable_rawArrivalCell rate)

@[simp] theorem rawLiveNumericalDecoder_length (Omega : OBS rate) :
    (rawLiveNumericalDecoder rate Omega).length = Omega.length := by
  simp [rawLiveNumericalDecoder]

@[simp] theorem rawCollectionNumericalDecoder_length (Omega : OBS rate) :
    (rawCollectionNumericalDecoder rate Omega).length = Omega.length := by
  simp [rawCollectionNumericalDecoder]

@[simp] theorem rawLiveArrivalDecoder_length (Omega : OBS rate) :
    (rawLiveArrivalDecoder rate Omega).length = Omega.length := by
  simp [rawLiveArrivalDecoder, rawLiveNumericalDecoder]

@[simp] theorem rawCollectionArrivalDecoder_length (Omega : OBS rate) :
    (rawCollectionArrivalDecoder rate Omega).length = Omega.length := by
  simp [rawCollectionArrivalDecoder, rawCollectionNumericalDecoder]

@[simp] theorem rawLiveNumericalDecoder_dates (Omega : OBS rate) :
    (rawLiveNumericalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [rawLiveNumericalDecoder]

@[simp] theorem rawCollectionNumericalDecoder_dates (Omega : OBS rate) :
    (rawCollectionNumericalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [rawCollectionNumericalDecoder]

@[simp] theorem rawLiveArrivalDecoder_dates (Omega : OBS rate) :
    (rawLiveArrivalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [rawLiveArrivalDecoder, rawLiveNumericalDecoder]

@[simp] theorem rawCollectionArrivalDecoder_dates (Omega : OBS rate) :
    (rawCollectionArrivalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [rawCollectionArrivalDecoder, rawCollectionNumericalDecoder]

private theorem branchCalendar_getElem
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    (ReferenceCompleteNumericalBranchObservation.branchCalendar rate rewards C_star C_h 0 source)[k.val]'(by
      simp [ReferenceCompleteNumericalBranchObservation.branchCalendar]) =
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k).input.time,
        (ReferenceActiveHorizonMeasurability.roundRecordCode
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h).get k),
          ReferenceCompleteNumericalBranchObservation.branchReadout rate 0
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h).get k))) := by
  simpa [ReferenceCompleteNumericalBranchObservation.branchCalendar] using
    (ReferenceCompleteNumericalBranchObservation.branchCalendar_get rate rewards C_star C_h 0 source k)

/-- Sourcewise raw LIVE projection of the one enriched observation. -/
theorem rawLiveNumericalDecoder_completeSuffixRecords
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    rawLiveNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source) =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map fun record =>
          (record.input.time,
            (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map
              ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  apply List.ext_getElem
  · simp [rawLiveNumericalDecoder, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, records]
  · intro n hnLeft hnRight
    have hn : n < records.length := by
      simpa [rawLiveNumericalDecoder, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar, records] using hnLeft
    let k : Fin records.length := ⟨n, hn⟩
    have hentry := branchCalendar_getElem rate rewards C_star C_h source k
    have hprojection := congrArg
      (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (entry.1, ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2)) hentry
    have hreadout := congrArg Prod.fst
      (ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 (records.get k))
    simpa [rawLiveNumericalDecoder, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, records, k, List.getElem_map] using
        hprojection.trans (congrArg (fun cell => ((records.get k).input.time, cell)) hreadout)

/-- Sourcewise raw collection projection of the same enriched observation. -/
theorem rawCollectionNumericalDecoder_completeSuffixRecords
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    rawCollectionNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source) =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map fun record =>
          (record.input.time,
            (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
              ReferenceCompleteNumericalBranchObservation.encodeNumerical) := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  apply List.ext_getElem
  · simp [rawCollectionNumericalDecoder, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, records]
  · intro n hnLeft hnRight
    have hn : n < records.length := by
      simpa [rawCollectionNumericalDecoder, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
        ReferenceCompleteNumericalBranchObservation.branchCalendar, records] using hnLeft
    let k : Fin records.length := ⟨n, hn⟩
    have hentry := branchCalendar_getElem rate rewards C_star C_h source k
    have hprojection := congrArg
      (fun entry : ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (entry.1, ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2)) hentry
    have hreadout := congrArg Prod.snd
      (ReferenceCompleteNumericalBranchObservation.branch_readout_projections rate 0 (records.get k))
    simpa [rawCollectionNumericalDecoder, ReferenceCompleteNumericalBranchObservation.completeBranchObservation,
      ReferenceCompleteNumericalBranchObservation.branchCalendar, records, k, List.getElem_map] using
        hprojection.trans (congrArg (fun cell => ((records.get k).input.time, cell)) hreadout)

/-- The raw arrival map keeps the same option and actual date as the numerical
projection and applies the public arithmetic coordinatewise. -/
theorem rawLiveArrivalDecoder_completeSuffixRecords
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    rawLiveArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source) =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map fun record =>
          (record.input.time,
            ((ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).map
              ReferenceCompleteNumericalBranchObservation.encodeNumerical).map
              (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) := by
  rw [rawLiveArrivalDecoder, rawLiveNumericalDecoder_completeSuffixRecords]
  simp only [List.map_map, Function.comp_def]

theorem rawCollectionArrivalDecoder_completeSuffixRecords
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    rawCollectionArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source) =
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).map fun record =>
          (record.input.time,
            ((ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record).map
              ReferenceCompleteNumericalBranchObservation.encodeNumerical).map
              (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) := by
  rw [rawCollectionArrivalDecoder, rawCollectionNumericalDecoder_completeSuffixRecords]
  simp only [List.map_map, Function.comp_def]

/-- The zero-length source branches remain empty in the original enriched
observation, with their actual branch hypotheses visible. -/
theorem completeBranchObservation_empty_of_no_launch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source = [] :=
  ReferenceCompleteObservationCalendarDecoders.completeBranchObservation_empty_of_no_launch
    rate rewards C_star C_h source hlaunch

theorem completeBranchObservation_empty_of_terminal_launch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source = [] :=
  ReferenceCompleteObservationCalendarDecoders.completeBranchObservation_empty_of_terminal_launch
    rate rewards C_star C_h source active hlaunch hstart

theorem startOf_completeBranchObservation_terminal_launch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    ReferenceCompleteObservationCalendarDecoders.startOf rate (ReferenceCompleteNumericalBranchObservation.completeBranchObservation rate rewards C_star C_h source) = p.T :=
  ReferenceCompleteObservationCalendarDecoders.startOf_completeBranchObservation_terminal_launch
    rate rewards C_star C_h source active hlaunch hstart

theorem firstPhaseSpan
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h) ≤ p.T := by
  have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  dsimp [ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput] at hstart ⊢
  omega

theorem firstPhaseReadySpan
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h) ≤ p.T := by
  simpa [ReferenceFirstCollectionReadyStream.startTime,
    ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput] using
      firstPhaseSpan rate rewards C_star C_h source

/-- On the actual crossing branch, the complete physical suffix is the
existing first-live run with its full horizon count. -/
theorem completeSuffixRecords_eq_actualFirstLiveRun
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate source rewards C_star C_h
        hcross (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h)
        (firstPhaseSpan rate rewards C_star C_h source)).records := by
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h hcross
  have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h
    (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
    hlaunch
  simpa [ReferenceCompletePhysicalHistory.physicalStart,
    ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput,
    ReferenceFirstWindowNumericalStream.actualFirstLiveRun] using hrecords

/-- The same complete suffix is the existing actual first-collection epoch;
only the producer's genuine initialization crossing is used. -/
theorem completeSuffixRecords_eq_actualFirstEpoch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h =
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross
        (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h source)).records := by
  have hrun := completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h source hcross
  have hphase :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate source rewards C_star C_h
        hcross (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h)
        (firstPhaseSpan rate rewards C_star C_h source)).records =
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross
        (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
          source rewards C_star C_h)
        rfl (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h)
        (firstPhaseReadySpan rate rewards C_star C_h source)).records := by
    rfl
  have hgenerated := ReferenceFirstCollectionReadyStream.generatedFirstCutoffRun_records_eq
    (rate := rate) source rewards C_star C_h hcross
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (firstPhaseReadySpan rate rewards C_star C_h source)
  calc
    _ = (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate source rewards C_star C_h
          hcross (p.T - ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h)
          (firstPhaseSpan rate rewards C_star C_h source)).records := hrun
    _ = (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross
          (ReferenceFirstCollectionReadyStream.startTime (rate := rate)
            source rewards C_star C_h)
          rfl (p.T - ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h)
          (firstPhaseReadySpan rate rewards C_star C_h source)).records := hphase
    _ = (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross
          (p.T - ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h)
          (firstPhaseReadySpan rate rewards C_star C_h source)).records := hgenerated

private theorem takeWhile_length_le {α : Type*} (test : α → Bool) (xs : List α) :
    (xs.takeWhile test).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases htest : test head = true
      · simp [List.takeWhile, htest]
        omega
      · simp [List.takeWhile, htest]

private theorem getElem_takeWhile_eq {α : Type*} (test : α → Bool)
    (xs : List α) (n : ℕ) (hn : n < (xs.takeWhile test).length) :
    (xs.takeWhile test)[n] = xs[n]'(by
      exact Nat.lt_of_lt_of_le hn (takeWhile_length_le test xs)) := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
      cases htest : test head with
      | false => simp [List.takeWhile, htest] at hn
      | true =>
          cases n with
          | zero => simp [List.takeWhile, htest]
          | succ n =>
              have hnTail : n < (tail.takeWhile test).length := by
                simpa [List.takeWhile, htest] using hn
              simpa only [List.takeWhile, htest, List.getElem_cons_succ] using
                ih n hnTail

/-- Compose P's actual first-live producer with the raw full-suffix
projection.  The inherited source, whole reward table, rate, enabled bit,
reward vector, rate vector and marker remain explicit in the conclusion. -/
theorem actualFirstLiveRawObservationIdentity
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let count := p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let hspan := firstPhaseSpan rate rewards C_star C_h source
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hcross count hspan
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hcross count hspan
    ∃ seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h),
      0 < ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h ∧
      ∀ k : Fin W.length,
        let record := W[k.val]
        let cell := cells[k.val]'(by
          rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
          exact k.isLt)
        k.val < (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).length ∧
        record.input.time.val = ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h + k.val ∧
        (rawLiveNumericalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source))[k.val]? =
          some (record.input.time, some
            (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell)) ∧
        (rawCollectionNumericalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source))[k.val]? =
          some (record.input.time, none) ∧
        (rawLiveArrivalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source))[k.val]? =
          some (record.input.time, some
            (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell)) ∧
        (rawCollectionArrivalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source))[k.val]? =
          some (record.input.time, none) ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = some cell ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = none ∧
        record.input.rows = source.1.2 ∧
        record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        record.input.rewards = rewards ∧
        cell.enabled = true ∧
        cell.reward = (fun arm => ((record.input.rewards record.input.time arm).val : ℝ) /
          (ConstructorDimensions.D p : ℝ)) ∧
        cell.rate = (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
          rate source rewards C_star C_h hcross count hspan k).selected.view.payload.rate ∧
        cell.recordedArm = ReferenceFirstWindowNumericalStream.sourceArm record
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.payload
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.pendingAtChoice
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).states
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.complementWeights
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).selected.view.cutoff
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
            rate source rewards C_star C_h hcross count hspan k).choiceInputsValid ∧
        ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
          (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell) =
        ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell := by
  classical
  dsimp only
  let count := p.T - ReferenceCompletePhysicalHistory.physicalStart
    rate source rewards C_star C_h
  let hspan := firstPhaseSpan rate rewards C_star C_h source
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let Omega := ReferenceCompleteNumericalBranchObservation.completeBranchObservation
    rate rewards C_star C_h source
  let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate source rewards C_star C_h hcross count hspan
  let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate source rewards C_star C_h hcross count hspan
  have hrecords := completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h source hcross
  have hwindow : W = ReferenceFirstLiveConfirmationHistory.firstLiveWindow records := by
    dsimp [W, ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    rw [← hrecords]
  have hwindowBound : W.length ≤ records.length := by
    rw [hwindow]
    exact takeWhile_length_le _ records
  have hlive := ReferenceFirstPhasesNumericalObservationIdentification.actual_first_live_numerical_observation_identity
    rate source rewards C_star C_h hcross count hspan
  rcases hlive with ⟨seed, hstart, hcells⟩
  refine ⟨seed, ?_, ?_⟩
  · simpa [ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hstart
  · intro k
    let record := W[k.val]
    let cell := cells[k.val]'(by
      rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
      exact k.isLt)
    have hbound : k.val < records.length := lt_of_lt_of_le k.isLt hwindowBound
    have hkWindow : k.val <
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length := by
      rw [← congrArg List.length hwindow]
      exact k.isLt
    have hkWindow' : k.val <
        (records.takeWhile
          (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input)).length := by
      simpa [ReferenceFirstLiveConfirmationHistory.firstLiveWindow] using hkWindow
    let kWindow : Fin (records.takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input)).length :=
      ⟨k.val, hkWindow'⟩
    have htakeAt :
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records)[k.val]? =
          some (records[k.val]'hbound) := by
      change (records.takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.cutoffChosen record.input))[k.val]? = _
      exact (List.getElem?_eq_getElem hkWindow').trans
        (congrArg some (getElem_takeWhile_eq _ records k.val hkWindow'))
    have hwindowAt := congrArg (fun xs : List ReferenceFirstLiveConfirmationHistory.Record => xs[k.val]?) hwindow
    have hrecordAt : W[k.val]? = some (records[k.val]'hbound) := hwindowAt.trans htakeAt
    have hrecord : record = records[k.val]'hbound := by
      have hrecordGet : W[k.val]? = some record := by
        simpa [record] using List.getElem?_eq_getElem k.isLt
      exact Option.some.inj (hrecordGet.symm.trans hrecordAt)
    have hfacts := hcells k
    dsimp only [W, cells, record, cell] at hfacts
    rcases hfacts with ⟨hreadLive, hreadCollection, htime, hrows, hselected,
      hrewardTable, henabled, hreward, hrate, hmarker, _harrivalProducer⟩
    have hreadLiveRecord :
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = some cell := by
      simpa [record, cell] using hreadLive
    have hreadCollectionRecord :
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = none := by
      simpa [record] using hreadCollection
    have hreadLiveSuffix :
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 (records[k.val]'hbound) = some cell := by
      rw [← hrecord]
      exact hreadLiveRecord
    have hreadCollectionSuffix :
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (records[k.val]'hbound) = none := by
      rw [← hrecord]
      exact hreadCollectionRecord
    have hliveWhole := congrArg (fun xs => xs[k.val]?)
      (rawLiveNumericalDecoder_completeSuffixRecords rate rewards C_star C_h source)
    have hcollectionWhole := congrArg (fun xs => xs[k.val]?)
      (rawCollectionNumericalDecoder_completeSuffixRecords rate rewards C_star C_h source)
    have hliveAt :
        (rawLiveNumericalDecoder rate Omega)[k.val]? =
          some (record.input.time,
            some (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell)) := by
      rw [hliveWhole]
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem hbound]
      apply congrArg some
      apply Prod.ext
      · exact congrArg (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
          r.input.time) hrecord.symm
      · dsimp only
        rw [hreadLiveSuffix]
        rfl
    have hcollectionAt :
        (rawCollectionNumericalDecoder rate Omega)[k.val]? = some (record.input.time, none) := by
      rw [hcollectionWhole]
      simp only [List.getElem?_map]
      rw [List.getElem?_eq_getElem hbound]
      apply congrArg some
      apply Prod.ext
      · exact congrArg (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
          r.input.time) hrecord.symm
      · dsimp only
        rw [hreadCollectionSuffix]
        rfl
    have harrivalCell :=
      ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates
        rate cell
    have hliveArrivalAt :
        (rawLiveArrivalDecoder rate Omega)[k.val]? =
          some (record.input.time,
            some (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell)) := by
      simp [rawLiveArrivalDecoder, hliveAt, harrivalCell]
    have hcollectionArrivalAt :
        (rawCollectionArrivalDecoder rate Omega)[k.val]? = some (record.input.time, none) := by
      simp [rawCollectionArrivalDecoder, hcollectionAt]
    refine ⟨hbound, ?_, hliveAt, hcollectionAt, hliveArrivalAt,
      hcollectionArrivalAt, hreadLive, hreadCollection, hrows, hselected,
      hrewardTable, henabled, hreward, hrate, hmarker, harrivalCell⟩
    simpa [count, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using htime

/-- On the actual shortened first-live branch, every produced cell of P's
initialized first-collection stream is the same dated optional value in the
unmasked collection projection of the complete observation.  The finite
prefix length is the producer's `out.ell`; the actual crossing, short-window
condition, stream dispatch, checked cutoff source cell, and physical queue
record equalities remain explicit. -/
theorem actualFirstCollectionRawObservationIdentity
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let count := p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h
    let hspan := firstPhaseReadySpan rate rewards C_star C_h source
    let suffix := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let epoch := ReferenceFirstCollectionReadyStream.actualEpoch
      (rate := rate) source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records
    ∀ hshort : W.length < count,
      let hshortP : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch
          (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count := by
            simpa [W] using hshort
      ∃ seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
          (ReferenceFirstCollectionReadyStream.startTime
            (rate := rate) source rewards C_star C_h),
        0 < ReferenceFirstCollectionReadyStream.startTime
          (rate := rate) source rewards C_star C_h ∧
        ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
            (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshortP,
          let out := d.stream
          ∃ head : ReferenceCollectionSegmentExtraction.Choice rate,
            ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
              ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  out.cutoff.cut.output.preparation head.payload head.started head.weights),
                ∃ D : List (RecordedQueueRun.RoundInput p.K),
                  ReferenceCollectionSegmentExtraction.choice out.cutoff.cut.input = some head ∧
                  head.payload = out.payload ∧
                  head.initializer = some initializer ∧
                  initializer.checkedStart rate = .success head.preLedger ∧
                  ∃ hDlen : D.length = out.ell,
                    D[0]'(by rw [hDlen]; have h := out.positiveLength; omega) =
                      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
                        rate out.cutoff.cut head rewards valid ∧
                  ∀ n : Fin out.ell,
                    let index := W.length + n.val
                    let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
                    let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
                    ∃ call : ReferenceCollectionSegmentExtraction.Choice rate,
                      ∃ validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
                        (ReferenceActivePhysicalStep.collectionRecordingInput
                          record.output.preparation call.payload call.started call.weights),
                        ReferenceCollectionSegmentExtraction.choice record.input = some call ∧
                        call.payload = out.payload ∧
                        CollectionBufferProvenance.collectionContext call.preLedger =
                          CollectionBufferProvenance.collectionContext head.preLedger ∧
                        cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
                          rate record call rewards validCall ∧
                        record.input.rows = source.1.2 ∧
                        record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                        record.input.rewards = rewards ∧
                        record.input.time.val =
                          ReferenceFirstCollectionReadyStream.startTime
                            (rate := rate) source rewards C_star C_h + W.length + n.val ∧
                        cell.enabled =
                          ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
                        cell.reward = (fun a => ((rewards record.input.time a).val : ℝ) /
                          (ConstructorDimensions.D p : ℝ)) ∧
                        cell.rate = out.payload.rate ∧
                        (∀ a : Fin p.K,
                          ReferenceCollectionRawBufferHistory.physicalQueueRecord
                            head.preLedger a record =
                            (cell.enabled, RecordedQueueRun.quantizedArrival
                              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell a)) ∧
                        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record =
                          some cell ∧
                        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none ∧
                        index < suffix.length ∧
                        (rawCollectionNumericalDecoder rate
                          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
                            rate rewards C_star C_h source))[index]? =
                          some (record.input.time,
                            some (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
                              cell)) ∧
                        (rawLiveNumericalDecoder rate
                          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
                            rate rewards C_star C_h source))[index]? =
                          some (record.input.time, none) ∧
                        (rawCollectionArrivalDecoder rate
                          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
                            rate rewards C_star C_h source))[index]? =
                          some (record.input.time,
                            some (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates
                              rate cell)) ∧
                        (rawLiveArrivalDecoder rate
                          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
                            rate rewards C_star C_h source))[index]? =
                          some (record.input.time, none) ∧
                        ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate
                          (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell) =
                            ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell := by
  classical
  dsimp only
  let count := p.T - ReferenceCompletePhysicalHistory.physicalStart
    rate source rewards C_star C_h
  let hspan := firstPhaseReadySpan rate rewards C_star C_h source
  let epoch := ReferenceFirstCollectionReadyStream.actualEpoch
    (rate := rate) source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records
  intro hshort
  let hshortP : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspan).records).length < count := by
    simpa [W] using hshort
  have hfullRecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h = epoch.records := by
    exact completeSuffixRecords_eq_actualFirstEpoch
      rate rewards C_star C_h source hcross
  have hcollection :=
    ReferenceFirstPhasesNumericalObservationIdentification.actual_first_collection_numerical_observation_identity
      rate source rewards C_star C_h hcross count hspan hshortP
  dsimp only at hcollection
  rcases hcollection with ⟨seed, hstart, d, head, initializer, valid, D,
    hhead, hpayload, hinitializer, hchecked, hDlen, hzero, hcells⟩
  let out := d.stream
  refine ⟨seed, hstart, d, head, initializer, valid, D,
    hhead, hpayload, hinitializer, hchecked, hDlen, hzero, ?_⟩
  intro n
  let suffix := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let index := W.length + n.val
  let record := out.window[n.val]'(lt_of_lt_of_le n.isLt out.withinWindow)
  let cell := D[n.val]'(by rw [hDlen]; exact n.isLt)
  obtain ⟨call, validCall, hcall, hcallPayload, hcontext, hsourceCell,
    hrows, hselected, hrecordRewards, htime, henabled, hreward, hrate,
    hphysical, hcollectionReadout, hliveNone⟩ := hcells n
  have hwindowIndex : n.val < out.window.length := lt_of_lt_of_le n.isLt out.withinWindow
  have halignment := out.alignment ⟨n.val, hwindowIndex⟩
  have hindexEq : epoch.records[index]? = some record := by
    simpa [index, W, record] using halignment.1
  have hrecordIndex : suffix[index]? = some record := by
    calc
      _ = epoch.records[index]? := congrArg (fun xs => xs[index]?) hfullRecords
      _ = some record := hindexEq
  have hindexBound : index < suffix.length :=
    (List.getElem?_eq_some_iff.mp hrecordIndex).1
  have hrecordEq : suffix[index]'hindexBound = record :=
    Option.some.inj ((List.getElem?_eq_getElem hindexBound).symm.trans hrecordIndex)
  have hcollectionWhole := congrArg (fun xs => xs[index]?)
    (rawCollectionNumericalDecoder_completeSuffixRecords rate rewards C_star C_h source)
  have hliveWhole := congrArg (fun xs => xs[index]?)
    (rawLiveNumericalDecoder_completeSuffixRecords rate rewards C_star C_h source)
  have hcollectionAt :
      (rawCollectionNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source))[index]? =
        some (record.input.time,
          some (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell)) := by
    rw [hcollectionWhole]
    simp only [List.getElem?_map]
    rw [List.getElem?_eq_getElem hindexBound]
    apply congrArg some
    apply Prod.ext
    · exact congrArg (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
        r.input.time) hrecordEq
    · change Option.map ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
          (suffix[index]'hindexBound)) =
        some (ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates cell)
      rw [hrecordEq, hcollectionReadout]
      rfl
  have hliveAt :
      (rawLiveNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source))[index]? = some (record.input.time, none) := by
    rw [hliveWhole]
    simp only [List.getElem?_map]
    rw [List.getElem?_eq_getElem hindexBound]
    apply congrArg some
    apply Prod.ext
    · exact congrArg (fun r : ReferenceCompletePhysicalHistory.RoundRecord p rate =>
        r.input.time) hrecordEq
    · change Option.map ReferenceCompleteNumericalBranchObservation.encodeNumerical
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
          (suffix[index]'hindexBound)) = none
      rw [hrecordEq, hliveNone]
      rfl
  have harrivalCell :=
    ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical_numericalCoordinates
      rate cell
  have hcollectionArrivalAt :
      (rawCollectionArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source))[index]? =
        some (record.input.time,
          some (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalCoordinates rate cell)) := by
    simp [rawCollectionArrivalDecoder, hcollectionAt, harrivalCell]
  have hliveArrivalAt :
      (rawLiveArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source))[index]? = some (record.input.time, none) := by
    simp [rawLiveArrivalDecoder, hliveAt]
  refine ⟨call, validCall, hcall, hcallPayload, hcontext, hsourceCell, hrows,
    hselected, hrecordRewards, htime, henabled, hreward, hrate, hphysical,
    hcollectionReadout, hliveNone, hindexBound, hcollectionAt, hliveAt,
    hcollectionArrivalAt, hliveArrivalAt, harrivalCell⟩

end Bandits.Support.ReferenceCompleteFirstPhaseObservationRecovery

end
