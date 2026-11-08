/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteNumericalBranchObservation

/-!
# Observation-only recovery of the original optional calendars

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-75`.

The observation keeps the original suffix date, whole canonical record code,
dispatcher tag, optional marker, enabled bit, and full real reward/rate vectors.
The four decoders below are total administrative projections of that list.
They preserve its positions and absent cells. They do not define a physical
queue, establish coverage, or assert an execution law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceCompleteObservationCalendarDecoders

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  ReferenceCompleteNumericalBranchObservation.SourceInput p

abbrev OBS {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  List (ReferenceCompleteNumericalBranchObservation.NumericalEntry rate)

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)

/-- Administrative suffix-origin recovery on every list, including lists that
are not observations of a physical execution. -/
def startOf (Omega : OBS rate) : ℕ := p.T - Omega.length

/-- Project the retained LIVE numerical cell, applying the actual strict
assignment-start mask and retaining every date and `none`. -/
def liveNumericalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
  Omega.map fun entry =>
    (entry.1,
      if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
          (startOf rate Omega) entry.2.1 then
        ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2
      else none)

/-- Project the retained collection numerical cell. The strict-sigma test is
used only when the incoming coordinator state is LIVE; a continuing first
collection entry keeps its unmasked right cell. -/
def collectionNumericalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p)) :=
  Omega.map fun entry =>
    (entry.1,
      if ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate entry.2.1 then
        if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
            (startOf rate Omega) entry.2.1 then
          ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2
        else none
      else ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2)

/-- Apply the public numerical-to-arrival projection to each same dated
optional LIVE cell. -/
def liveArrivalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (Bool × (Fin p.K → ℕ))) :=
  (liveNumericalDecoder rate Omega).map fun cell =>
    (cell.1, cell.2.map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

/-- Apply the public numerical-to-arrival projection to each same dated
optional collection cell. -/
def collectionArrivalDecoder (Omega : OBS rate) :
    List (Fin p.T × Option (Bool × (Fin p.K → ℕ))) :=
  (collectionNumericalDecoder rate Omega).map fun cell =>
    (cell.1, cell.2.map
      (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))

@[simp] theorem liveNumericalDecoder_length (Omega : OBS rate) :
    (liveNumericalDecoder rate Omega).length = Omega.length := by
  simp [liveNumericalDecoder]

@[simp] theorem collectionNumericalDecoder_length (Omega : OBS rate) :
    (collectionNumericalDecoder rate Omega).length = Omega.length := by
  simp [collectionNumericalDecoder]

@[simp] theorem liveArrivalDecoder_length (Omega : OBS rate) :
    (liveArrivalDecoder rate Omega).length = Omega.length := by
  simp [liveArrivalDecoder]

@[simp] theorem collectionArrivalDecoder_length (Omega : OBS rate) :
    (collectionArrivalDecoder rate Omega).length = Omega.length := by
  simp [collectionArrivalDecoder]

@[simp] theorem liveNumericalDecoder_dates (Omega : OBS rate) :
    (liveNumericalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [liveNumericalDecoder]

@[simp] theorem collectionNumericalDecoder_dates (Omega : OBS rate) :
    (collectionNumericalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [collectionNumericalDecoder]

@[simp] theorem liveArrivalDecoder_dates (Omega : OBS rate) :
    (liveArrivalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [liveArrivalDecoder, liveNumericalDecoder]

@[simp] theorem collectionArrivalDecoder_dates (Omega : OBS rate) :
    (collectionArrivalDecoder rate Omega).map Prod.fst = Omega.map Prod.fst := by
  simp [collectionArrivalDecoder, collectionNumericalDecoder]

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

private theorem measurable_leftProjection :
    Measurable
      (ReferenceCompleteNumericalBranchObservation.leftProjection
        (p := p)) := by
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
      (fun value => outputEquiv
        (ReferenceCompleteNumericalBranchObservation.leftProjection value)) =
        fun value => decode (inputEquiv value) := by
    funext value
    cases value with
    | none => rfl
    | some cell => cases cell <;> rfl
  change Measurable (fun value => outputEquiv
    (ReferenceCompleteNumericalBranchObservation.leftProjection value))
  rw [heq]
  exact hdecode.comp hinput

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

private theorem measurable_rightProjection :
    Measurable
      (ReferenceCompleteNumericalBranchObservation.rightProjection
        (p := p)) := by
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
      (fun value => outputEquiv
        (ReferenceCompleteNumericalBranchObservation.rightProjection value)) =
        fun value => decode (inputEquiv value) := by
    funext value
    cases value with
    | none => rfl
    | some cell => cases cell <;> rfl
  change Measurable (fun value => outputEquiv
    (ReferenceCompleteNumericalBranchObservation.rightProjection value))
  rw [heq]
  exact hdecode.comp hinput

private theorem measurable_selection :
    Measurable (fun code : ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
      ReferenceCoordinatorRecorderCallTrace.selection code) := by
  change Measurable (fun code : ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
    code.2.2.1.1)
  exact measurable_fst.comp (measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp measurable_id)))

private theorem measurable_selectionPayloadSigma :
    Measurable (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      selected.1.payload.sigma.val) := by
  have hview : Measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)) := comap_measurable _
  have hpayload : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        selected.1.payload) :=
    measurable_fst.comp (hview.comp measurable_fst)
  have hpayloadObservation : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        LaterAssignmentStartMeasurability.payloadObservation selected.1.payload) :=
    (comap_measurable _).comp hpayload
  have hsigma : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        (LaterAssignmentStartMeasurability.payloadObservation selected.1.payload).2.1) :=
    measurable_fst.comp (measurable_snd.comp hpayloadObservation)
  exact (measurable_of_countable (fun t : Fin p.T => t.val)).comp hsigma

private theorem measurable_optionGetDFalse :
    @Measurable (Option Bool) Bool
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := Bool))
      inferInstance (fun value => value.getD false) := by
  let encode := Equiv.optionEquivSumPUnit Bool
  let decode : Bool ⊕ PUnit → Bool := Sum.elim id (fun _ => false)
  have hencode : @Measurable (Option Bool) (Bool ⊕ PUnit)
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := Bool))
      inferInstance encode := by
    change Measurable[(inferInstance : MeasurableSpace (Bool ⊕ PUnit)).comap encode] encode
    exact comap_measurable encode
  have hdecode : Measurable decode := measurable_id.sumElim measurable_const
  have heq : (fun value : Option Bool => value.getD false) = decode ∘ encode := by
    funext value
    cases value <;> rfl
  rw [heq]
  exact hdecode.comp hencode

private theorem measurable_strictSigmaMask_fixed (start : ℕ) :
    Measurable (fun code : ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
      ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate start code) := by
  let selectedMask := fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
    decide (start < selected.1.payload.sigma.val)
  have hselected : Measurable selectedMask :=
    (measurable_of_countable _).comp (measurable_selectionPayloadSigma rate)
  have hselection := measurable_selection rate
  have hmap : @Measurable
      (ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate) (Option Bool)
      (ReferenceActiveHorizonMeasurability.roundRecordCodeMeasurableSpace
        (p := p) (rate := rate))
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := Bool))
      (fun code => (ReferenceCoordinatorRecorderCallTrace.selection code).map selectedMask) :=
    measurable_optionMap
      ReferenceCoordinatorRecorderCallTrace.selection hselection selectedMask hselected
  have hfinal := measurable_optionGetDFalse.comp hmap
  have heq :
      (fun code : ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
        ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate start code) =
      fun code =>
        ((ReferenceCoordinatorRecorderCallTrace.selection code).map selectedMask).getD false := by
    funext code
    cases hsel : ReferenceCoordinatorRecorderCallTrace.selection code <;>
      simp [ReferenceCompleteNumericalBranchObservation.strictSigmaMask, selectedMask, hsel]
  rw [heq]
  exact hfinal

private theorem measurable_strictSigmaMask_joint :
    Measurable (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
      ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate pair.1 pair.2) := by
  apply measurable_from_prod_countable_right
  intro start
  exact measurable_strictSigmaMask_fixed rate start

private theorem measurable_incomingLiveTag :
    Measurable (fun code : ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
      ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate code) := by
  let coordinator := fun code :
      ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate => code.2.1.1
  have hcoordinator : Measurable coordinator :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_id))
  let tag : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → Bool :=
    fun code => match code with
      | .inl _ => false
      | .inr (.inl _) => true
      | .inr (.inr _) => false
  have htag : Measurable tag := by
    change Measurable (Sum.elim (fun _ : Unit => false)
      (Sum.elim (fun _ :
        (ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) => true)
        (fun _ :
          ((ReferenceActivePhysicalStep.Payload rate ×
            (ReferenceActivePhysicalStep.Ledger rate × Option (Fin p.T × Bool))) ⊕ Unit) =>
          false)))
    exact measurable_const.sumElim
      (measurable_const.sumElim measurable_const)
  have heq :
      (fun code : ReferenceCompleteNumericalBranchObservation.RoundRecordCode rate =>
        ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate code) =
        tag ∘ coordinator := by
    funext code
    cases h : code.2.1.1 with
    | inl _ => simp [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
        tag, coordinator, h]
    | inr inner =>
        cases inner with
        | inl _ => simp [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
            tag, coordinator, h]
        | inr _ => simp [ReferenceCompleteNumericalBranchObservation.incomingLiveTag,
            tag, coordinator, h]
  rw [heq]
  exact htag.comp hcoordinator

private theorem measurable_liveEntryDecoderJoint :
    Measurable (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (pair.2.1,
        if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
            (p.T - pair.1) pair.2.2.1 then
          ReferenceCompleteNumericalBranchObservation.leftProjection pair.2.2.2
        else none)) := by
  have hstart : Measurable (fun pair : ℕ ×
      ReferenceCompleteNumericalBranchObservation.NumericalEntry rate => p.T - pair.1) :=
    (measurable_of_countable _).comp measurable_fst
  have hcode : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        pair.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hmask : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
          (p.T - pair.1) pair.2.2.1) :=
    (measurable_strictSigmaMask_joint rate).comp (hstart.prodMk hcode)
  have hcell : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
            (p.T - pair.1) pair.2.2.1 then
          ReferenceCompleteNumericalBranchObservation.leftProjection pair.2.2.2
        else none) :=
    Measurable.ite (hmask.eq_const true).setOf
      ((measurable_leftProjection (p := p)).comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))))
      measurable_const
  exact (measurable_fst.comp (measurable_snd.comp measurable_id)).prodMk hcell

private theorem measurable_collectionEntryDecoderJoint :
    Measurable (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
      (pair.2.1,
        if ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate pair.2.2.1 then
          if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
              (p.T - pair.1) pair.2.2.1 then
            ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2
          else none
        else ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2)) := by
  have hstart : Measurable (fun pair : ℕ ×
      ReferenceCompleteNumericalBranchObservation.NumericalEntry rate => p.T - pair.1) :=
    (measurable_of_countable _).comp measurable_fst
  have hcode : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        pair.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hcell : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        pair.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have htag : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate pair.2.2.1) :=
    (measurable_incomingLiveTag rate).comp hcode
  have hmask : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
          (p.T - pair.1) pair.2.2.1) :=
    (measurable_strictSigmaMask_joint rate).comp (hstart.prodMk hcode)
  have hright : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2) :=
    (measurable_rightProjection (p := p)).comp hcell
  have hmasked : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
            (p.T - pair.1) pair.2.2.1 then
          ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2
        else none) :=
    Measurable.ite (hmask.eq_const true).setOf hright measurable_const
  have hcell' : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        if ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate pair.2.2.1 then
          if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
              (p.T - pair.1) pair.2.2.1 then
            ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2
          else none
        else ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2) :=
    Measurable.ite (htag.eq_const true).setOf hmasked hright
  exact (measurable_fst.comp (measurable_snd.comp measurable_id)).prodMk hcell'

private def mapObservationTag {A C : Type*} (f : A → C) : Unit ⊕ A → Unit ⊕ C
  | .inl _ => .inl ()
  | .inr value => .inr (f value)

private theorem listObservationAt_map {A C : Type*} (f : A → C)
    (records : List A) (n : ℕ) :
    ReferenceActiveHorizonMeasurability.listObservationAt (records.map f) n =
      mapObservationTag f
        (ReferenceActiveHorizonMeasurability.listObservationAt records n) := by
  induction records generalizing n with
  | nil => cases n <;> rfl
  | cons head tail ih =>
      cases n with
      | zero => rfl
      | succ n => exact ih n

private def mapLengthObservationTag {A C : Type*} (f : ℕ × A → C) :
    ℕ × (Unit ⊕ A) → Unit ⊕ C := fun pair =>
  mapObservationTag (fun value => f (pair.1, value)) pair.2

private theorem measurable_list_map_length_param {A C : Type*}
    [MeasurableSpace A] [MeasurableSpace C]
    (f : ℕ × A → C) (hf : Measurable f) :
    Measurable (fun records : List A =>
      records.map (fun value => f (records.length, value))) := by
  apply measurable_comap_iff.mpr
  have hcoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := A)
  have hlength : Measurable (fun records : List A => records.length) :=
    measurable_fst.comp hcoordinates
  have htag : Measurable (mapLengthObservationTag f) := by
    apply measurable_from_prod_countable_right
    intro length
    change Measurable (Sum.elim (fun _ : Unit => (Sum.inl () : Unit ⊕ C))
      (fun value => Sum.inr (f (length, value))))
    exact measurable_const.sumElim
      (measurable_inr.comp (hf.comp (measurable_const.prodMk measurable_id)))
  have hstream : Measurable (fun records : List A => fun n =>
      mapLengthObservationTag f
        (records.length,
          ReferenceActiveHorizonMeasurability.listObservationAt records n)) := by
    apply measurable_pi_iff.mpr
    intro n
    exact htag.comp
      ((measurable_fst.comp hcoordinates).prodMk
        ((measurable_pi_apply n).comp (measurable_snd.comp hcoordinates)))
  have hcoordinatesMap (records : List A) :
      ReferenceActiveHorizonMeasurability.listObservationCoordinates
          (records.map (fun value => f (records.length, value))) =
        (records.length, fun n => mapLengthObservationTag f
          (records.length,
            ReferenceActiveHorizonMeasurability.listObservationAt records n)) := by
    apply Prod.ext
    · simp [ReferenceActiveHorizonMeasurability.listObservationCoordinates]
    · funext n
      simpa [ReferenceActiveHorizonMeasurability.listObservationCoordinates,
        mapLengthObservationTag, mapObservationTag] using
        (listObservationAt_map (fun value => f (records.length, value)) records n)
  have hmapCoordinates : Measurable (fun records : List A =>
      ReferenceActiveHorizonMeasurability.listObservationCoordinates
        (records.map (fun value => f (records.length, value)))) := by
    have heq :
        (fun records : List A =>
          ReferenceActiveHorizonMeasurability.listObservationCoordinates
            (records.map (fun value => f (records.length, value)))) =
        fun records => (records.length, fun n => mapLengthObservationTag f
          (records.length,
            ReferenceActiveHorizonMeasurability.listObservationAt records n)) := by
      funext records
      exact hcoordinatesMap records
    rw [heq]
    exact hlength.prodMk hstream
  exact hmapCoordinates

theorem measurable_liveNumericalDecoder :
    Measurable (liveNumericalDecoder rate) := by
  have hentry : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (pair.2.1,
          if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
              (p.T - pair.1) pair.2.2.1 then
            ReferenceCompleteNumericalBranchObservation.leftProjection pair.2.2.2
          else none)) := measurable_liveEntryDecoderJoint rate
  change Measurable (fun Omega : OBS rate => Omega.map (fun entry =>
    (entry.1,
      if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
          (p.T - Omega.length) entry.2.1 then
        ReferenceCompleteNumericalBranchObservation.leftProjection entry.2.2
      else none)))
  exact measurable_list_map_length_param
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (pair.2.1,
          if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
              (p.T - pair.1) pair.2.2.1 then
            ReferenceCompleteNumericalBranchObservation.leftProjection pair.2.2.2
          else none)) hentry

theorem measurable_collectionNumericalDecoder :
    Measurable (collectionNumericalDecoder rate) := by
  have hentry : Measurable
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (pair.2.1,
          if ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate pair.2.2.1 then
            if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
                (p.T - pair.1) pair.2.2.1 then
              ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2
            else none
          else ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2)) :=
    measurable_collectionEntryDecoderJoint rate
  change Measurable (fun Omega : OBS rate => Omega.map (fun entry =>
    (entry.1,
      if ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate entry.2.1 then
        if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
            (p.T - Omega.length) entry.2.1 then
          ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2
        else none
      else ReferenceCompleteNumericalBranchObservation.rightProjection entry.2.2)))
  exact measurable_list_map_length_param
      (fun pair : ℕ × ReferenceCompleteNumericalBranchObservation.NumericalEntry rate =>
        (pair.2.1,
          if ReferenceCompleteNumericalBranchObservation.incomingLiveTag rate pair.2.2.1 then
            if ReferenceCompleteNumericalBranchObservation.strictSigmaMask rate
                (p.T - pair.1) pair.2.2.1 then
              ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2
            else none
          else ReferenceCompleteNumericalBranchObservation.rightProjection pair.2.2.2)) hentry

private theorem measurable_arrivalCell :
    Measurable (fun cell : Fin p.T ×
        Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
      (cell.1, cell.2.map
        (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate))) := by
  let Arrival := Bool × (Fin p.K → ℕ)
  have hoption : @Measurable
      (Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
      (Option Arrival)
      (LaterAssignmentStartMeasurability.optionMeasurableSpace
        (α := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
      (LaterAssignmentStartMeasurability.optionMeasurableSpace (α := Arrival))
      (fun value =>
        value.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) :=
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
      (Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
      (Option Arrival)
      (LaterAssignmentStartMeasurability.optionMeasurableSpace
        (α := ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p))
      (ReferenceInitializationMeasurability.optionCountableMeasurableSpace Arrival)
      (fun value =>
        value.map (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)) := by
    exact hoption.mono le_rfl (by rw [hOptionSpace]; exact le_rfl)
  exact measurable_fst.prodMk (hoptionTop.comp measurable_snd)

theorem measurable_liveArrivalDecoder :
    Measurable (liveArrivalDecoder rate) := by
  let : MeasurableSpace (Option (Bool × (Fin p.K → ℕ))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (liveNumericalDecoder rate) (measurable_liveNumericalDecoder rate)
    (fun cell : Fin p.T ×
      Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
        (cell.1, cell.2.map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))
    (measurable_arrivalCell rate)

theorem measurable_collectionArrivalDecoder :
    Measurable (collectionArrivalDecoder rate) := by
  let : MeasurableSpace (Option (Bool × (Fin p.K → ℕ))) :=
    ReferenceInitializationMeasurability.optionCountableMeasurableSpace _
  exact ReferenceActiveHorizonMeasurability.measurable_list_map
    (collectionNumericalDecoder rate) (measurable_collectionNumericalDecoder rate)
    (fun cell : Fin p.T ×
      Option (ReferenceCompleteNumericalBranchObservation.NumericalCoordinates p) =>
        (cell.1, cell.2.map
          (ReferenceLaterCollectionSourceReadoutMeasurability.arrivalsFromNumerical rate)))
    (measurable_arrivalCell rate)

variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The observation length recovers the physical suffix start without a launch
or successful-initialization premise. -/
theorem startOf_completeBranchObservation (source : SourceInput p) :
    startOf rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  have hbound := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  change p.T -
      (ReferenceCompleteNumericalBranchObservation.branchCalendar
        rate rewards C_star C_h 0 source).length = _
  rw [ReferenceCompleteNumericalBranchObservation.branchCalendar_length]
  omega

theorem completeBranchObservation_empty_of_no_launch (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source = [] := by
  exact ReferenceCompleteNumericalBranchObservation.empty_no_launch
    rate rewards C_star C_h 0 source hlaunch

theorem startOf_completeBranchObservation_no_launch (source : SourceInput p)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    startOf rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) = p.T := by
  rw [completeBranchObservation_empty_of_no_launch rate rewards C_star C_h source hlaunch]
  rfl

theorem completeBranchObservation_empty_of_terminal_launch (source : SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    ReferenceCompleteNumericalBranchObservation.completeBranchObservation
      rate rewards C_star C_h source = [] := by
  exact ReferenceCompleteNumericalBranchObservation.empty_terminal
    rate rewards C_star C_h 0 source active hlaunch hstart

theorem startOf_completeBranchObservation_terminal_launch (source : SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = p.T) :
    startOf rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) = p.T := by
  rw [completeBranchObservation_empty_of_terminal_launch
    rate rewards C_star C_h source active hlaunch hstart]
  rfl

theorem liveNumericalDecoder_eq_maskedLiveCalendar (source : SourceInput p) :
    liveNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedLiveCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := by
  rw [← startOf_completeBranchObservation rate rewards C_star C_h source]
  rfl

theorem collectionNumericalDecoder_eq_maskedCollectionCalendar (source : SourceInput p) :
    collectionNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedCollectionCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := by
  rw [← startOf_completeBranchObservation rate rewards C_star C_h source]
  rfl

theorem liveArrivalDecoder_eq_maskedLiveArrivalCalendar (source : SourceInput p) :
    liveArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedLiveArrivalCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := by
  rw [liveArrivalDecoder, liveNumericalDecoder_eq_maskedLiveCalendar
    rate rewards C_star C_h source]
  unfold ReferenceCompleteNumericalBranchObservation.maskedLiveCalendar
    ReferenceCompleteNumericalBranchObservation.maskedLiveArrivalCalendar
  rw [List.map_map]
  rfl

theorem collectionArrivalDecoder_eq_maskedCollectionArrivalCalendar (source : SourceInput p) :
    collectionArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedCollectionArrivalCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := by
  rw [collectionArrivalDecoder, collectionNumericalDecoder_eq_maskedCollectionCalendar
    rate rewards C_star C_h source]
  unfold ReferenceCompleteNumericalBranchObservation.maskedCollectionCalendar
    ReferenceCompleteNumericalBranchObservation.maskedCollectionArrivalCalendar
  rw [List.map_map]
  rfl

/-- The original LIVE numerical calendar is a function of the enriched
observation, with no additional source premise. -/
theorem liveNumericalDecoder_factors (source : SourceInput p) :
    liveNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
        rate rewards C_star C_h source := by
  calc
    liveNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedLiveCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := liveNumericalDecoder_eq_maskedLiveCalendar rate rewards C_star C_h source
    _ = ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
        rate rewards C_star C_h source :=
      (ReferenceCompleteNumericalBranchObservation.original_calendars_factor
        rate rewards C_star C_h source).1

/-- The original collection numerical calendar is a function of the enriched
observation, using the unmasked continuing-collection branch. -/
theorem collectionNumericalDecoder_factors (source : SourceInput p) :
    collectionNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceLaterCollectionCalendarMeasurability.numericalCalendar
        rate rewards C_star C_h source := by
  calc
    collectionNumericalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedCollectionCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := collectionNumericalDecoder_eq_maskedCollectionCalendar
          rate rewards C_star C_h source
    _ = ReferenceLaterCollectionCalendarMeasurability.numericalCalendar
        rate rewards C_star C_h source :=
      (ReferenceCompleteNumericalBranchObservation.original_calendars_factor
        rate rewards C_star C_h source).2.1

/-- The original LIVE arrival calendar is obtained by mapping the same
dated optional numerical cell through the public arrival arithmetic. -/
theorem liveArrivalDecoder_factors (source : SourceInput p) :
    liveArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar
        rate rewards C_star C_h source := by
  calc
    liveArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedLiveArrivalCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := liveArrivalDecoder_eq_maskedLiveArrivalCalendar
          rate rewards C_star C_h source
    _ = ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar
        rate rewards C_star C_h source :=
      (ReferenceCompleteNumericalBranchObservation.original_calendars_factor
        rate rewards C_star C_h source).2.2.1

/-- The original collection arrival calendar is obtained by mapping the same
dated optional numerical cell through the public arrival arithmetic. -/
theorem collectionArrivalDecoder_factors (source : SourceInput p) :
    collectionArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar
        rate rewards C_star C_h source := by
  calc
    collectionArrivalDecoder rate
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source) =
      ReferenceCompleteNumericalBranchObservation.maskedCollectionArrivalCalendar
        rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        source := collectionArrivalDecoder_eq_maskedCollectionArrivalCalendar
          rate rewards C_star C_h source
    _ = ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar
        rate rewards C_star C_h source :=
      (ReferenceCompleteNumericalBranchObservation.original_calendars_factor
        rate rewards C_star C_h source).2.2.2

theorem measurable_laterLiveNumericalCalendar_comap :
    Measurable[(MeasurableSpace.comap
      (fun source : SourceInput p =>
        ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source)
      (inferInstance : MeasurableSpace (OBS rate)))]
      (ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
        rate rewards C_star C_h) := by
  have hfunction :
      ReferenceLaterLiveCalendarMeasurability.laterLiveNumericalCalendar
          rate rewards C_star C_h =
        fun source => liveNumericalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source) := by
    funext source
    exact (liveNumericalDecoder_factors rate rewards C_star C_h source).symm
  rw [hfunction]
  exact (measurable_liveNumericalDecoder rate).comp (comap_measurable _)

theorem measurable_numericalCalendar_comap :
    Measurable[(MeasurableSpace.comap
      (fun source : SourceInput p =>
        ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source)
      (inferInstance : MeasurableSpace (OBS rate)))]
      (ReferenceLaterCollectionCalendarMeasurability.numericalCalendar
        rate rewards C_star C_h) := by
  have hfunction :
      ReferenceLaterCollectionCalendarMeasurability.numericalCalendar
          rate rewards C_star C_h =
        fun source => collectionNumericalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source) := by
    funext source
    exact (collectionNumericalDecoder_factors rate rewards C_star C_h source).symm
  rw [hfunction]
  exact (measurable_collectionNumericalDecoder rate).comp (comap_measurable _)

theorem measurable_laterLiveArrivalCalendar_comap :
    Measurable[(MeasurableSpace.comap
      (fun source : SourceInput p =>
        ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source)
      (inferInstance : MeasurableSpace (OBS rate)))]
      (ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar
        rate rewards C_star C_h) := by
  have hfunction :
      ReferenceLaterLiveCalendarMeasurability.laterLiveArrivalCalendar
          rate rewards C_star C_h =
        fun source => liveArrivalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source) := by
    funext source
    exact (liveArrivalDecoder_factors rate rewards C_star C_h source).symm
  rw [hfunction]
  exact (measurable_liveArrivalDecoder rate).comp (comap_measurable _)

theorem measurable_arrivalCalendar_comap :
    Measurable[(MeasurableSpace.comap
      (fun source : SourceInput p =>
        ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h source)
      (inferInstance : MeasurableSpace (OBS rate)))]
      (ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar
        rate rewards C_star C_h) := by
  have hfunction :
      ReferenceLaterCollectionCalendarMeasurability.arrivalCalendar
          rate rewards C_star C_h =
        fun source => collectionArrivalDecoder rate
          (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
            rate rewards C_star C_h source) := by
    funext source
    exact (collectionArrivalDecoder_factors rate rewards C_star C_h source).symm
  rw [hfunction]
  exact (measurable_collectionArrivalDecoder rate).comp (comap_measurable _)

end Bandits.Support.ReferenceCompleteObservationCalendarDecoders

end
