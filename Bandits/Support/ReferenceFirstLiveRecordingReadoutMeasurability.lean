/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstLiveRecordingSourceBranch

/-!
# Joint measurability of retained first-live recording readouts

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:376-408`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The carriers below retain the original retained source and the whole current
continuous control.  This module concerns current physical readouts only; it
does not integrate the source, assert an adapted law, or close a manuscript
statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon

namespace Bandits.Support.ReferenceFirstLiveRecordingReadoutMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}

local instance (a : Prop) : Decidable a := Classical.propDecidable a

local instance : Countable ActiveRoundActions.FollowerStatus :=
  (Function.LeftInverse.injective
    FollowerDownMeasurability.followerStatusOfCode_code).countable

/-- The source carrier is exactly the retained launch-start fibre used by B. -/
abbrev SourceX (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :=
  ReferenceFirstLiveRecordingSourceBranch.RetainedBranch
    rate rewards C_star C_h q t s hs control0

/-- Literal subtype carrier for the continuing recording branch. -/
abbrev XPlus (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :=
  {x : SourceX rate rewards C_star C_h q t s hs control0 //
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
      rate rewards C_star C_h q t s hs control0 x}

/-- Literal subtype carrier for one continuing unoccupied follower. -/
abbrev XFollower (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) :=
  {x : SourceX rate rewards C_star C_h q t s hs control0 //
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch
      rate rewards C_star C_h q t s hs control0 i x}

variable {rate : RateInput p} {rewards : RewardTable p}
  {C_star C_h : ℝ} {q : Fin (M p)} {t : Fin p.T} {s : ℕ}
  {hs : s ≤ t.val} {control0 : TimeControl p}

/-- The actual baseline current input selected by the retained source. -/
def sourceCurrentInput (x : SourceX rate rewards C_star C_h q t s hs control0) :=
  ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
    rate rewards C_star C_h q t s hs control0 x

/-- The actual one-step input after replacing the whole current control. -/
def sourceInputAtControl
    (x : SourceX rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :=
  ReferenceContinuingLiveSlicePreparation.inputAtControl (sourceCurrentInput x) u

/-- The actual physical record at the replaced current control. -/
def sourceRecordAtControl
    (x : SourceX rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  ⟨sourceInputAtControl x u,
    ReferenceActivePhysicalStep.step (sourceInputAtControl x u), rfl⟩

/-- The literal canonical one-step code on the original source and complete
current control. -/
def sourceWholeStepCodeAtControl
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceActiveStepCompositionMeasurability.wholeStepCode
    (sourceInputAtControl z.1 z.2)

/-- The payload retained by the actual dispatcher selection in the original
whole-step code.  The option is kept until the continuing branch proves it is
present. -/
def sourceSelectionPayloadOption
    (x : SourceX rate rewards C_star C_h q t s hs control0) :
    Option (ReferenceActivePhysicalStep.Payload rate) :=
  ((ReferenceActiveStepCompositionMeasurability.wholeStepCode
    (sourceCurrentInput x)).1.1).map fun selection => selection.1.payload

private theorem measurable_sourceCurrentInput :
    Measurable (sourceCurrentInput (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  change Measurable (fun x : SourceX rate rewards C_star C_h q t s hs control0 =>
    ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
      rate rewards C_star C_h q t s hs control0 x)
  have heq :
      (fun x : SourceX rate rewards C_star C_h q t s hs control0 =>
        ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
          rate rewards C_star C_h q t s hs control0 x) =
        fun x => ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x := by
    funext x
    exact ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x
  rw [heq]
  exact ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0

private theorem sourceCurrentInput_selected
    (x : SourceX rate rewards C_star C_h q t s hs control0) :
    (sourceCurrentInput x).selected = q := by
  change (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
    rate rewards C_star C_h q t s hs control0 x).selected = q
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  exact ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q
    rate rewards C_star C_h q t s hs control0 x

private theorem sourceCurrentInput_time
    (x : SourceX rate rewards C_star C_h q t s hs control0) :
    (sourceCurrentInput x).time = t := by
  change (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
    rate rewards C_star C_h q t s hs control0 x).time = t
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  rfl

/-- Replacing the actual source input's selected current row is jointly Borel
on the original retained source and the whole control. -/
theorem measurable_sourceInputAtControl :
    Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      sourceInputAtControl (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
        (hs := hs) (control0 := control0) z.1 z.2) := by
  let input : SourceX rate rewards C_star C_h q t s hs control0 →
      ReferenceActivePhysicalStep.RoundInput p rate := sourceCurrentInput
  have hinput : Measurable input := measurable_sourceCurrentInput
  let domain := SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p
  have hstate : Measurable (fun z : domain => (input z.1).state) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hinput).comp
      measurable_fst
  have hrows : Measurable (fun z : domain => (input z.1).rows) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_rows.comp hinput).comp
      measurable_fst
  have hbaseSelected (z : domain) : (input z.1).selected = q :=
    sourceCurrentInput_selected z.1
  have hbaseTime (z : domain) : (input z.1).time = t :=
    sourceCurrentInput_time z.1
  have hselected : Measurable (fun z : domain =>
      (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).selected) := by
    have heq : (fun z : domain =>
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).selected) =
        fun _ => q := by
      funext z
      simp [ReferenceContinuingLiveSlicePreparation.inputAtControl, hbaseSelected z]
    rw [heq]
    exact measurable_const
  have htime : Measurable (fun z : domain =>
      (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).time) := by
    have heq : (fun z : domain =>
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).time) =
        fun _ => t := by
      funext z
      simp [ReferenceContinuingLiveSlicePreparation.inputAtControl, hbaseTime z]
    rw [heq]
    exact measurable_const
  have hrewards : Measurable (fun z : domain =>
      (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).rewards) := by
    exact measurable_const
  let updatedSelectedRow : domain → CompletePublicTable.CompleteRow p := fun z =>
    ((input z.1).row.1,
      Function.update ((input z.1).row.2) t z.2)
  have hforward : Measurable (fun z : domain => (input z.1).row.1) := by
    exact measurable_fst.comp
      ((ReferenceActivePhysicalStepMeasurability.measurable_row.comp hinput).comp
        measurable_fst)
  have hcontrolRows : Measurable (fun z : domain =>
      Function.update ((input z.1).row.2) t z.2) := by
    have hpair : Measurable (fun z : domain => ((input z.1).row.2, z.2)) :=
      ((measurable_snd.comp
        ((ReferenceActivePhysicalStepMeasurability.measurable_row.comp hinput).comp
          measurable_fst)).prodMk measurable_snd)
    exact measurable_update'.comp hpair
  have hselectedRow : Measurable updatedSelectedRow := hforward.prodMk hcontrolRows
  have hupdatedRows : Measurable (fun z : domain =>
      Function.update ((input z.1).rows) q (updatedSelectedRow z)) := by
    exact measurable_update'.comp (hrows.prodMk hselectedRow)
  have hrowsAtControl : Measurable (fun z : domain =>
      (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).rows) := by
    have heq : (fun z : domain =>
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).rows) =
        fun z => Function.update ((input z.1).rows) q (updatedSelectedRow z) := by
      funext z
      change Function.update ((input z.1).rows) (input z.1).selected
          ((input z.1).row.1,
            Function.update (input z.1).row.2 (input z.1).time z.2) = _
      rw [hbaseSelected z, hbaseTime z]
    rw [heq]
    exact hupdatedRows
  have hcoordinates : Measurable (fun z : domain =>
      ((ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).state,
        ((ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).rows,
          ((ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).selected,
            ((ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).time,
              (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).rewards))))) := by
    exact hstate.prodMk (hrowsAtControl.prodMk
      (hselected.prodMk (htime.prodMk hrewards)))
  have hactive : ∀ z : domain,
      ∀ i, ((ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).state.activations i).val ≤
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).time.val + 1 :=
    fun z => (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2).active
  have hencoded : Measurable (fun z : domain =>
      ReferenceActivePhysicalStepMeasurability.encodeRoundInput
        (ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2)) :=
    hcoordinates.subtype_mk (h := hactive)
  change Measurable (fun z : domain =>
    ReferenceContinuingLiveSlicePreparation.inputAtControl (input z.1) z.2)
  exact measurable_comap_iff.mpr hencoded

/-- The same actual input, packaged on the source×control product. -/
def sourceInputAtControlProduct
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  sourceInputAtControl z.1 z.2

/-- The retained actual PREPARE selection payload is jointly Borel on the
original source fibre. -/
theorem measurable_sourceSelectionPayloadOption :
    Measurable (sourceSelectionPayloadOption (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  unfold sourceSelectionPayloadOption
  have hwhole :=
    (ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode
      (p := p) (rate := rate)).comp
      (measurable_sourceCurrentInput (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
        (hs := hs) (control0 := control0))
  have hviewPayload : Measurable
      (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload) := by
    have hobs : Measurable
        (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
          (p := p) (rate := rate)) := comap_measurable _
    change Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate) view).1)
    exact measurable_fst.comp hobs
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (fun selection : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      selection.1.payload)
    (hviewPayload.comp measurable_fst)
    (fun x : SourceX rate rewards C_star C_h q t s hs control0 =>
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode
        (sourceCurrentInput x)).1.1)
    (measurable_fst.comp (measurable_fst.comp hwhole))

/-- At a continuing PREPARE, the option above is the payload from the very
same canonical selection and equals the source's actual register payload. -/
theorem sourceSelectionPayloadOption_eq_some_actual
    (x : SourceX rate rewards C_star C_h q t s hs control0)
    (hbranch : ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
      rate rewards C_star C_h q t s hs control0 x) :
    ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare (sourceCurrentInput x)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      sourceSelectionPayloadOption x = some r.payload := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpending, henabled, _⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_cut_at_control
      rate rewards C_star C_h q t s hs control0 x hbranch
  have hdispatch : ReferenceActivePhysicalStep.dispatch (sourceCurrentInput x) =
      .live r owned base (.continuingChosen d hsStart c arm) := by
    simpa only [ReferenceActivePhysicalStep.prepare, sourceCurrentInput] using hcoord
  have hselected :
      (((ReferenceActiveStepCompositionMeasurability.wholeStepCode
        (sourceCurrentInput x)).1.1).map
          (fun selection => selection.1.payload)) = some r.payload := by
    rw [(ReferenceActiveStepCompositionMeasurability.wholeStepCode_front
      (sourceCurrentInput x)).1]
    rw [hdispatch]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection]
  refine ⟨r, owned, base, d, hsStart, c, arm, hcoord, ?_⟩
  exact hselected

private theorem measurable_get_of_always_some {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : β → Option α) (hf : Measurable f)
    (hSome : ∀ x, ∃ a, f x = some a) :
    Measurable (fun x => (f x).get (by
      obtain ⟨a, ha⟩ := hSome x
      simp [ha])) := by
  let : MeasurableSpace (Option α) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  have hEquiv : Measurable (Equiv.optionEquivSumPUnit α) := comap_measurable _
  intro s hs
  have hSomeImage : MeasurableSet (some '' s : Set (Option α)) := by
    have hleft : MeasurableSet (Sum.inl '' s : Set (α ⊕ PUnit)) := hs.inl_image
    have hset : (some '' s : Set (Option α)) =
        (Equiv.optionEquivSumPUnit α) ⁻¹' (Sum.inl '' s) := by
      ext option
      cases option <;> simp [Equiv.optionEquivSumPUnit]
    rw [hset]
    exact hleft.preimage hEquiv
  have hpre : {x | (f x).get (by
      obtain ⟨a, ha⟩ := hSome x
      simp [ha]) ∈ s} = f ⁻¹' (some '' s) := by
    ext x
    obtain ⟨a, ha⟩ := hSome x
    simp [ha]
  change MeasurableSet {x | (f x).get (by
    obtain ⟨a, ha⟩ := hSome x
    simp [ha]) ∈ s}
  rw [hpre]
  exact hSomeImage.preimage hf

/-- The source's baseline payload is the actual selected PREPARE payload.
Its option getter is justified by the continuing branch witness. -/
def selectedBaselinePayload
    (x : XPlus rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalStep.Payload rate :=
  (sourceSelectionPayloadOption x.val).get (by
    obtain ⟨r, _, _, _, _, _, _, _, hpayload⟩ :=
      sourceSelectionPayloadOption_eq_some_actual x.val x.property
    rw [hpayload]
    simp)

private theorem sourceSelectionPayloadOption_exists
    (x : XPlus rate rewards C_star C_h q t s hs control0) :
    ∃ payload, sourceSelectionPayloadOption x.val = some payload := by
  obtain ⟨r, _, _, _, _, _, _, _, hpayload⟩ :=
    sourceSelectionPayloadOption_eq_some_actual x.val x.property
  exact ⟨r.payload, hpayload⟩

/-- Joint measurability of the actual PREPARE-selected baseline payload on
the inherited branch subtype. -/
theorem measurable_selectedBaselinePayload :
    Measurable (selectedBaselinePayload (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  unfold selectedBaselinePayload
  apply measurable_get_of_always_some
  · exact (measurable_sourceSelectionPayloadOption
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)).comp
        measurable_subtype_coe
  · exact sourceSelectionPayloadOption_exists

/-- The baseline payload's literal derived rate vector remains Borel as it
varies with the actual selected payload. -/
theorem measurable_selectedBaselineInputRate :
    Measurable (fun x : XPlus rate rewards C_star C_h q t s hs control0 =>
      AssignmentPayloadDerivedMeasurability.inputRate
        (selectedBaselinePayload x)) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp
    measurable_selectedBaselinePayload

/-- The baseline payload's literal natural exponent vector remains Borel as
it varies with the actual selected payload. -/
theorem measurable_selectedBaselineInputExponent :
    Measurable (fun x : XPlus rate rewards C_star C_h q t s hs control0 =>
      AssignmentPayloadDerivedMeasurability.inputExponent
        (selectedBaselinePayload x)) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputExponent.comp
    measurable_selectedBaselinePayload

/-- The follower subtype inherits the same source carrier and its branch
property supplies the continuing-recording subtype proof. -/
def followerAsPlus
    (i : Fin (p.m - 1))
    (x : XFollower rate rewards C_star C_h q t s hs control0 i) :
    XPlus rate rewards C_star C_h q t s hs control0 :=
  ⟨x.val, x.property.1⟩

/-- The map from the unoccupied follower carrier to the actual continuing
branch carrier is Borel for their inherited subtype spaces. -/
theorem measurable_followerAsPlus (i : Fin (p.m - 1)) :
    Measurable (followerAsPlus (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  apply measurable_comap_iff.mpr
  exact measurable_subtype_coe

/-- The actual selected payload's canonical assigned arm at follower `i`.
The arm is read from its literal slow-set assignment. -/
def selectedBaselineAssignedArm (i : Fin (p.m - 1))
    (x : XPlus rate rewards C_star C_h q t s hs control0) : Fin p.K :=
  (selectedBaselinePayload x).assignment.assigned i

/-- The canonical arm assignment remains measurable as the retained source
varies, by the existing measurable slow-set payload projection. -/
theorem measurable_selectedBaselineAssignedArm (i : Fin (p.m - 1)) :
    Measurable (selectedBaselineAssignedArm (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  change Measurable (fun x : XPlus rate rewards C_star C_h q t s hs control0 =>
    CanonicalAssignmentVector.followerArm p.two_le_m
      (selectedBaselinePayload x).slowSet i)
  have harm : Measurable (fun slowSet : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m slowSet i) :=
    measurable_of_countable _
  exact harm.comp
    ((ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet).comp
      measurable_selectedBaselinePayload)

/-- The true whole-control coordinate at the actual current time, with its
original scalar subtype retained. -/
def sourceCurrentSlice
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    CanonicalRecordingSlice.Slice p.m p.K := z.2.1

/-- The slice projection keeps every scalar coordinate of the whole control. -/
theorem measurable_sourceCurrentSlice :
    Measurable (sourceCurrentSlice (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) :=
  measurable_fst.comp measurable_snd

/-- Current DATA status is a measurable finite code read from the original
whole slice. -/
theorem measurable_sourceCurrentSlotDraw :
    Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      PublicDiscreteDraws.slotDraw z.2.1) :=
  (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)).comp
    (measurable_fst.comp measurable_snd)

/-- The current recorder source is the finite code from this same slice. -/
theorem measurable_sourceCurrentRecorderSource :
    Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K z.2.1) :=
  (PublicDiscreteDraws.measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp
    (measurable_fst.comp measurable_snd)

/-- The actual coordinator recording result stored in the existing physical
whole-step code. -/
def sourceCoordinatorRecordingAtControl
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ((sourceWholeStepCodeAtControl z).1.2.2.2.2).2.2.2.1

/-- The coordinator's current gate arm is a finite projection of the retained
recording code. -/
def sourceCoordinatorGateArmAtControl
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    Option (Fin p.K) :=
  (sourceCoordinatorRecordingAtControl z).bind fun output => output.gateArm

/-- The stored coordinator result is exactly the actual `RoundRecord`
recording result from this same one-step input. -/
theorem sourceCoordinatorRecordingAtControl_eq_actual
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    sourceCoordinatorRecordingAtControl z =
      (sourceRecordAtControl z.1 z.2).output.coordinator.recording := by
  have hwhole := ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs
    (sourceInputAtControl z.1 z.2)
  change (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode
        (sourceInputAtControl z.1 z.2)).1.2.2.2.2).recording =
    (ReferenceActivePhysicalStep.step (sourceInputAtControl z.1 z.2)).coordinator.recording
  exact (congrArg
    (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
      observation.recording) hwhole.1).trans rfl

/-- The actual coordinator recording code is jointly Borel on retained
source×whole-control. -/
theorem measurable_sourceCoordinatorRecordingAtControl :
    Measurable (sourceCoordinatorRecordingAtControl
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) := by
  have hwhole :=
    (ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode
      (p := p) (rate := rate)).comp
      (measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
        (hs := hs) (control0 := control0))
  have hphysical := measurable_fst.comp hwhole
  have htail := measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp hphysical)))
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp htail)))

/-- The physical coordinator arm projection is jointly Borel. -/
theorem measurable_sourceCoordinatorGateArmAtControl :
    Measurable (sourceCoordinatorGateArmAtControl
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) := by
  have hmap : Measurable (fun output :
      Option (CoordinatorRecordingOperation.Output p) =>
        output.bind fun result => result.gateArm) := measurable_of_countable _
  exact hmap.comp
    measurable_sourceCoordinatorRecordingAtControl

/-- The current continuous thinning scalar, as a real-valued joint
source/control projection. -/
def sourceCurrentThinScalar
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) : ℝ :=
  (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin z.2.1).val

/-- The current thinning scalar retains its ordinary real Borel structure. -/
theorem measurable_sourceCurrentThinScalar :
    Measurable (sourceCurrentThinScalar (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  exact measurable_subtype_coe.comp
    ((measurable_pi_apply ContinuousControlSlice.Label.thin).comp
      (measurable_fst.comp measurable_snd))

/-- The selected payload agrees with each actual continuing PREPARE register
payload recovered from B's branch witness. -/
theorem selectedBaselinePayload_eq_actual
    (x : XPlus rate rewards C_star C_h q t s hs control0) :
    ∃ r owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare (sourceCurrentInput x.val)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) ∧
      selectedBaselinePayload x = r.payload := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hcoord, hpayload⟩ :=
    sourceSelectionPayloadOption_eq_some_actual x.val x.property
  refine ⟨r, owned, base, d, hsStart, c, arm, hcoord, ?_⟩
  simp [selectedBaselinePayload, hpayload]

/-- Any actual continuing constructor, including each constructor returned by
B's `actual_continuing_recording_inputs`, has this same selected payload. The
only conditional input is equality to the actual baseline PREPARE. -/
theorem selectedBaselinePayload_eq_of_continuing
    (x : XPlus rate rewards C_star C_h q t s hs control0) :
    ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) owned base d hsStart c arm,
      (ReferenceActivePhysicalStep.prepare (sourceCurrentInput x.val)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) →
      selectedBaselinePayload x = r.payload := by
  intro r owned base d hsStart c arm hcoord
  have hdispatch : ReferenceActivePhysicalStep.dispatch (sourceCurrentInput x.val) =
      .live r owned base (.continuingChosen d hsStart c arm) := hcoord
  have hpayload : sourceSelectionPayloadOption x.val = some r.payload := by
    unfold sourceSelectionPayloadOption
    rw [(ReferenceActiveStepCompositionMeasurability.wholeStepCode_front
      (sourceCurrentInput x.val)).1, hdispatch]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, ReferenceLiveDispatchOutputMeasurability.encodeSelection]
  simp [selectedBaselinePayload, hpayload]

/-- The exact current follower PREPARE code on the same input and whole
control; its reconstruction is the existing code theorem. -/
def sourcePreparedFollowerCodeAtControl
    (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceActivePhysicalStepMeasurability.preparedFollowerCode
    (sourceInputAtControl z.1 z.2) i

/-- Joint measurability of each existing follower preparation code. -/
theorem measurable_sourcePreparedFollowerCodeAtControl
    (i : Fin (p.m - 1)) :
    Measurable (sourcePreparedFollowerCodeAtControl i
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) :=
  (ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i).comp
    (measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))

/-- The original varying PREPARE operation's actual incoming configuration,
parameterized by any measurable map into the canonical round input. -/
def preparedIncomingForInput {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (z : Ω) : FollowerPrepareJointMeasurability.IncomingConfiguration p rate :=
  FollowerVaryingActivationMeasurability.varyingPreparedConfiguration (rate := rate) i
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      ((input z).state.activations i)
      (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        ((input z).state.followers i))
      (input z).row (input z).time ((input z).active i))

/-- Existing PREPARE code components make the actual incoming configuration
Borel, including its unchanged continuous buffer fibers. -/
theorem measurable_preparedIncomingForInput {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin (p.m - 1)) (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : Measurable input) :
    Measurable (preparedIncomingForInput (rate := rate) i input) := by
  change Measurable (fun z =>
    FollowerVaryingActivationMeasurability.varyingPreparedConfiguration (rate := rate) i
      (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        ((input z).state.activations i)
        (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
          ((input z).state.followers i))
        (input z).row (input z).time ((input z).active i)))
  exact FollowerVaryingActivationMeasurability.measurable_varyingPreparedConfiguration_atComponents
    rate i
    (fun z => (input z).state.activations i)
    (fun z => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      ((input z).state.followers i))
    (fun z => (input z).row) (fun z => (input z).time)
    ((ReferenceActivePhysicalStepMeasurability.measurable_activation i).comp hinput)
    ((ReferenceActivePhysicalStepMeasurability.measurable_incomingFollower i).comp hinput)
    (ReferenceActivePhysicalStepMeasurability.measurable_row.comp hinput)
    (ReferenceActivePhysicalStepMeasurability.measurable_time.comp hinput)
    (fun z => (input z).active i)

/-- The actual prepared incoming configuration on the retained source and
whole current control. -/
def sourcePreparedIncomingAtControl
    (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    FollowerPrepareJointMeasurability.IncomingConfiguration p rate :=
  preparedIncomingForInput (rate := rate) i
    sourceInputAtControlProduct z

/-- The actual prepared configuration remains Borel on source×control. -/
theorem measurable_sourcePreparedIncomingAtControl (i : Fin (p.m - 1)) :
    Measurable (sourcePreparedIncomingAtControl i
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) := by
  exact measurable_preparedIncomingForInput (rate := rate) i
    sourceInputAtControlProduct
    (measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))

/-- Project the ordinary/dagger tag and its exact countable carried-state
index without reconstructing or discretizing any saved scalar. -/
def incomingOfferStatus
    (offer : ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate) :
    Option ActiveRoundActions.FollowerStatus :=
  match offer with
  | .dagger => none
  | .ordinary index =>
      some (FollowerDownMeasurability.followerStatusOfCode index.1.status)

def incomingOfferLastDown
    (offer : ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate) :
    Option (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :=
  match offer with
  | .dagger => none
  | .ordinary index =>
      (FollowerDownMeasurability.followerStateOfCode (rate := rate) index.1 []).lastDown

/-- The real PREPARE status is read from its carried-state code. -/
def sourcePreparedStatusAtControl
    (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  incomingOfferStatus (ReferenceUpReceptionMeasurability.incomingOfferIndex (rate := rate)
    (sourcePreparedIncomingAtControl i z))

/-- The real PREPARE DOWN register is read from its carried-state code. -/
def sourcePreparedLastDownAtControl
    (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  incomingOfferLastDown (ReferenceUpReceptionMeasurability.incomingOfferIndex (rate := rate)
    (sourcePreparedIncomingAtControl i z))

/-- The PREPARE status projection is measurable on source×whole-control. -/
theorem measurable_sourcePreparedStatusAtControl (i : Fin (p.m - 1)) :
    Measurable (sourcePreparedStatusAtControl i
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) := by
  change Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p =>
    incomingOfferStatus (ReferenceUpReceptionMeasurability.incomingOfferIndex
      (rate := rate) (sourcePreparedIncomingAtControl i z)))
  have hcode :=
    (ReferenceUpReceptionMeasurability.measurable_incomingOfferIndex (rate := rate)).comp
      (measurable_sourcePreparedIncomingAtControl
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (q := q) (t := t) (s := s) (hs := hs) (control0 := control0) i)
  exact (Measurable.of_discrete : Measurable
    (fun offer : ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate =>
      incomingOfferStatus offer)).comp hcode

/-- The PREPARE DOWN-register projection is measurable on source×whole-control. -/
theorem measurable_sourcePreparedLastDownAtControl (i : Fin (p.m - 1)) :
    Measurable (sourcePreparedLastDownAtControl i
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) := by
  change Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p =>
    incomingOfferLastDown (ReferenceUpReceptionMeasurability.incomingOfferIndex
      (rate := rate) (sourcePreparedIncomingAtControl i z)))
  have hcode :=
    (ReferenceUpReceptionMeasurability.measurable_incomingOfferIndex (rate := rate)).comp
      (measurable_sourcePreparedIncomingAtControl
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (q := q) (t := t) (s := s) (hs := hs) (control0 := control0) i)
  exact (Measurable.of_discrete : Measurable
    (fun offer : ReferenceUpReceptionMeasurability.IncomingOfferIndex p rate =>
      incomingOfferLastDown offer)).comp hcode

/-- The unchanged active-horizon record code over the actual retained input. -/
def sourceRoundRecordCodeAtControl
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceActiveHorizonMeasurability.roundRecordCode (sourceRecordAtControl z.1 z.2)

/-- Joint measurability of the existing lossless current RoundRecord code. -/
theorem measurable_sourceRoundRecordCodeAtControl :
    Measurable (sourceRoundRecordCodeAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  unfold sourceRoundRecordCodeAtControl
  have hin : Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 ×
      TimeControl p => sourceInputAtControl z.1 z.2) :=
    measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)
  have htime : Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 ×
      TimeControl p => (sourceInputAtControl z.1 z.2).time.val) :=
    (Measurable.of_discrete : Measurable (fun v : Fin p.T => v.val)).comp
      ((ReferenceActivePhysicalStepMeasurability.measurable_time.comp hin))
  have hstate : Measurable (fun z : SourceX rate rewards C_star C_h q t s hs control0 ×
      TimeControl p => ReferenceActivePhysicalStepMeasurability.encodeState
        (sourceInputAtControl z.1 z.2).state) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp
      (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hin))
  have hwhole :=
    (ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode
      (p := p) (rate := rate)).comp hin
  exact htime.prodMk (hstate.prodMk hwhole)

/-- The exact own entry retained by this one-step code for a player. -/
def sourceOwnEntryAtControl (player : Fin p.m)
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
    (sourceRoundRecordCodeAtControl z) player

/-- The physical own entry remains jointly measurable through its action and
grid-feedback code. -/
theorem measurable_sourceOwnEntryAtControl (player : Fin p.m) :
    Measurable (sourceOwnEntryAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) player) :=
  (ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry player).comp
    measurable_sourceRoundRecordCodeAtControl

/-- The actual logging gate for a follower, on the source and complete
control. This retains the finite source-mask tests from the same actual row. -/
def sourceLoggingTestsAtControl (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) : Prop :=
  SparseCalendarReplay.loggingTestsPass
    (ReferencePrelaunchFollower.loggingRound i
      (sourceInputAtControl z.1 z.2).row
      ((sourceInputAtControl z.1 z.2).state.activations i)
      (sourceInputAtControl z.1 z.2).time
      (sourceOwnEntryAtControl (PublicDiscreteDraws.followerPlayer p.two_le_m i) z))

/-- The finite activation, DATA, source, and pilot-mask tests are jointly
measurable while the continuous thinning coordinate stays in the same slice. -/
noncomputable def sourceLoggingTestsPassBit (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) : Bool :=
  by
    classical
    exact decide (sourceLoggingTestsAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i z)

/-- The finite activation, DATA, source, and pilot-mask tests are jointly
measurable while the continuous thinning coordinate stays in the same slice. -/
theorem measurable_sourceLoggingTestsPassBit (i : Fin (p.m - 1)) :
    Measurable (sourceLoggingTestsPassBit (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  classical
  let domain := SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p
  let input : domain → ReferenceActivePhysicalStep.RoundInput p rate :=
    fun z => sourceInputAtControl z.1 z.2
  have hin : Measurable input := measurable_sourceInputAtControl
  let test := fun v : (ReferencePrelaunchFollower.Activation p × Fin p.T) ×
      (PublicDiscreteDraws.Slot × Fin p.m × ((Fin p.m → Fin p.K) × Fin p.K)) =>
    decide (v.1.1.val ≤ v.1.2.val + 1 ∧ v.2.1 = PublicDiscreteDraws.dataSlot ∧
      v.2.2.1 = PublicDiscreteDraws.followerPlayer p.two_le_m i ∧
      ∀ player, player ≠ PublicDiscreteDraws.followerPlayer p.two_le_m i →
        v.2.2.2.1 player ≠ v.2.2.2.2)
  have hp : Measurable (fun z : domain => fun player : Fin p.m =>
      PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player z.2.1) :=
    measurable_pi_iff.mpr fun player =>
      (PublicDiscreteDraws.measurable_pilotDraw
        (ConstructorDimensions.K_pos p) player).comp measurable_sourceCurrentSlice
  have hm := (measurable_of_countable test).comp
    ((((ReferenceActivePhysicalStepMeasurability.measurable_activation i).comp hin).prodMk
      (ReferenceActivePhysicalStepMeasurability.measurable_time.comp hin)).prodMk
      (measurable_sourceCurrentSlotDraw.prodMk
        (measurable_sourceCurrentRecorderSource.prodMk
          (hp.prodMk (measurable_fst.comp (measurable_sourceOwnEntryAtControl
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)))))))
  convert hm using 1
  funext z
  have hslice : ((input z).row.2 (input z).time).1 = z.2.1 := by
    change ((ReferenceContinuingLiveSlicePreparation.inputAtControl
      (sourceCurrentInput z.1) z.2).row.2
      (ReferenceContinuingLiveSlicePreparation.inputAtControl
        (sourceCurrentInput z.1) z.2).time).1 = z.2.1
    rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
  apply Bool.eq_iff_iff.mpr
  simp only [sourceLoggingTestsPassBit, decide_eq_true_eq, Function.comp_apply, test]
  unfold sourceLoggingTestsAtControl
  rw [ActiveFollowerLogging.loggingTestsPass_iff_source_mask]
  rw [show ((sourceInputAtControl z.1 z.2).row.2
    (sourceInputAtControl z.1 z.2).time).1 = z.2.1 from hslice]

/-- Exact existing generated source split; the original source remains in its
accepted Borel subtype. -/
def retainedSourceSplit
    (x : SourceX rate rewards C_star C_h q t s hs control0) :=
  ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1

/-- Launch state from B's actual retained-source facts. -/
def retainedSourceInitial
    (x : SourceX rate rewards C_star C_h q t s hs control0) :=
  ReferenceFirstLaunchNumericalCell.launchState rate (retainedSourceSplit x)
    rewards C_star C_h
    (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
      rate rewards C_star C_h q t s hs control0 x).1

/-- The actual current physical count. -/
def retainedSourceCurrentCount : ℕ := t.val - s

/-- The actual horizon span for this current record. -/
theorem retainedSourceCurrentSpan (hs : s ≤ t.val) :
    s + (retainedSourceCurrentCount (t := t) (s := s) + 1) ≤ p.T := by
  dsimp [retainedSourceCurrentCount]
  have ht := t.isLt
  omega

/-- The actual first-live seed supplies the all-active mode of B's launch
state, with elapsed time taken from B's retained-source fact. -/
theorem retainedSourceInitialMode
    (x : SourceX rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalHorizon.allActiveAtStart (retainedSourceInitial x) s := by
  have hseed := ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
    rate rewards C_star C_h q t s hs control0 x
  rcases ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
      rate rewards C_star C_h q t s hs control0 x with ⟨_, helapsed⟩
  simpa only [retainedSourceInitial, retainedSourceSplit, helapsed] using
    hseed.activeAtStart

/-- Same source-derived candidate record used by the fixed-source producers. -/
def retainedSourceCandidateRecord
    (x : SourceX rate rewards C_star C_h q t s hs control0) (u : TimeControl p) :=
  ReferenceContinuingDataCandidateLogging.candidateRecord (retainedSourceInitial x)
    (retainedSourceSplit x).1.2 q rewards s
    (retainedSourceCurrentCount (t := t) (s := s))
    (retainedSourceCurrentSpan (t := t) (s := s) hs)
    (retainedSourceInitialMode x) u

/-- B's actual current input is the literal candidate input from that same
launch state and original source row. -/
theorem sourceCurrentInput_eq_candidateInput
    (x : SourceX rate rewards C_star C_h q t s hs control0) :
    sourceCurrentInput x =
      ReferenceContinuingDataCandidateLogging.candidateInput
        (retainedSourceInitial x) (retainedSourceSplit x).1.2 q rewards s
        (retainedSourceCurrentCount (t := t) (s := s))
        (retainedSourceCurrentSpan (t := t) (s := s) hs)
        (retainedSourceInitialMode x) := by
  change ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
      rate rewards C_star C_h q t s hs control0 x = _
  simp [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput,
    retainedSourceInitial, retainedSourceSplit, retainedSourceCurrentCount,
    ]

/-- The actual retained input/control record is exactly the candidate record
used by the fixed-source recording producers. -/
theorem sourceRecordAtControl_eq_candidateRecord
    (x : SourceX rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) :
    sourceRecordAtControl x u = retainedSourceCandidateRecord x u := by
  have hin :
      sourceInputAtControl x u =
        ReferenceContinuingLiveSlicePreparation.inputAtControl
          (ReferenceContinuingDataCandidateLogging.candidateInput
            (retainedSourceInitial x) (retainedSourceSplit x).1.2 q rewards s
            (retainedSourceCurrentCount (t := t) (s := s))
            (retainedSourceCurrentSpan (t := t) (s := s) hs)
            (retainedSourceInitialMode x)) u := by
    change ReferenceContinuingLiveSlicePreparation.inputAtControl
        (sourceCurrentInput x) u = _
    rw [sourceCurrentInput_eq_candidateInput]
  unfold sourceRecordAtControl retainedSourceCandidateRecord
  cases hin
  rfl

/-- The actual marker is literally the existing candidate physical marker on
the source-derived launch state, original row, original rewards, and current
whole control. -/
theorem sourcePhysicalMarker_eq_candidatePhysicalMarker
    (x : SourceX rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (payload : ReferenceActivePhysicalStep.Payload rate)
    (enabled : Bool) :
    ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        (sourceRecordAtControl x u) payload enabled =
      ReferenceContinuingRecordingFastPair.candidatePhysicalMarker
        (retainedSourceInitial x) (retainedSourceSplit x).1.2 q rewards s
        (retainedSourceCurrentCount (t := t) (s := s))
        (retainedSourceCurrentSpan (t := t) (s := s) hs)
        (retainedSourceInitialMode x) payload enabled u := by
  rw [sourceRecordAtControl_eq_candidateRecord]
  rfl

/-- The normalized saved map on the actual record is the same literal M map
as on the source-derived candidate record. -/
theorem sourceNormalizedSavedContribution_eq_candidateRecord
    (x : SourceX rate rewards C_star C_h q t s hs control0)
    (u : TimeControl p) (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) :
    ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
        (sourceRecordAtControl x u) payload i =
      ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
        (retainedSourceCandidateRecord x u) payload i := by
  rw [sourceRecordAtControl_eq_candidateRecord]

private theorem preparedIncoming_decodes (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate
        (sourcePreparedIncomingAtControl i z) =
      ((sourceRecordAtControl z.1 z.2).output.preparation.followers.followers i).configuration := by
  exact congrArg DeclaredFollowerLocalRound.PreparedRound.configuration
    (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct
      (sourceInputAtControl z.1 z.2) i)

private theorem offer_status_decodes
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    incomingOfferStatus (ReferenceUpReceptionMeasurability.incomingOfferIndex incoming) =
      match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming with
      | .dagger => none
      | .ordinary state _ => some state.status := by
  cases incoming with
  | none => rfl
  | some data => rfl

private theorem offer_down_decodes
    (incoming : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    incomingOfferLastDown (ReferenceUpReceptionMeasurability.incomingOfferIndex incoming) =
      match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming with
      | .dagger => none
      | .ordinary state _ => state.lastDown := by
  cases incoming with
  | none => rfl
  | some data => rfl

private theorem sourceOwnEntry_eq_actual (player : Fin p.m)
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    sourceOwnEntryAtControl player z =
      (sourceRecordAtControl z.1 z.2).output.ownEntries player := by
  exact (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs
    (sourceRecordAtControl z.1 z.2)).2.2.2.2 player

private theorem sourceSlice_eq_actual
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    ((sourceRecordAtControl z.1 z.2).input.row.2
      (sourceRecordAtControl z.1 z.2).input.time).1 = z.2.1 := by
  change ((ReferenceContinuingLiveSlicePreparation.inputAtControl
    (sourceCurrentInput z.1) z.2).row.2
    (ReferenceContinuingLiveSlicePreparation.inputAtControl
      (sourceCurrentInput z.1) z.2).time).1 = z.2.1
  rw [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
    ReferenceContinuingLiveSlicePreparation.inputAtControl_time,
    ReferenceContinuingLiveSlicePreparation.rowAtControl_time]

private theorem downInput_eq_checkedLogging
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory) (hstatus : state.status = .unoccupied) :
    (record.output.followers i).downInput =
      (ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        state).toOption := by
  rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower]
  have halign := record.output.preparation.follower_alignment i
  rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared]
  simp only [ReferenceActivePhysicalStep.finishFollower, hprep,
    ReferenceActivePhysicalStep.recordFollower, halign.1, halign.2.1,
    halign.2.2.1, halign.2.2.2, hstatus, dite_true]
  cases hlog : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state with
  | error reason => rfl
  | ok logged =>
      dsimp only
      cases hresult : DeclaredFollowerLocalRound.consumeDownResult rate
        (ReferenceDownReception.referenceDownCut p
          record.output.preparation.coordinator.downView i record.input.row record.input.time
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome with
      | error reason => rfl
      | ok next =>
          dsimp only
          cases DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state memory next <;> rfl

private theorem logged_buffer_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : state.status = .unoccupied)
    (hlog : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      state = .ok logged) :
    logged.buffer = state.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  unfold ActiveFollowerLogging.checkedLogging at hlog
  split at hlog
  · dsimp only at hlog
    split at hlog
    · cases hlog
      simp only [ActiveFollowerLogging.loggingUpdate, ActiveFollowerLogging.loggingBranch,
        record.input.active i, hstatus, and_self, ite_true]
    · cases hlog
  · cases hlog

private theorem unoccupied_marker_formula
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hprep : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory) (hstatus : state.status = .unoccupied) :
    ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record payload i state =
      if (record.output.followers i).downInput.isSome = true ∧
          SparseCalendarReplay.loggingTestsPass (ReferencePrelaunchFollower.loggingRound i
            record.input.row (record.input.state.activations i) record.input.time
            (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).1 =
            payload.assignment.assigned i ∧
          ((record.input.row.2 record.input.time).1 ContinuousControlSlice.Label.thin).val ≤
            ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold payload
              (payload.assignment.assigned i)
      then some (payload.assignment.assigned i) else none := by
  classical
  have hdown := downInput_eq_checkedLogging record i state memory hprep hstatus
  have hem : ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    simp only [ReferenceFollowerBufferProvenance.logEmission, hprep, hstatus, dite_true]
  unfold ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker
  rw [hdown]
  cases hlog : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state with
  | error reason => simp [Except.toOption]
  | ok logged =>
      have hbuffer := logged_buffer_eq record i state logged hstatus hlog
      simp only [Except.toOption, hlog, hbuffer, hem, true_and]
      by_cases htests : SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
      · rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests _ _ _ _ _ htests]
        simp only [htests, true_and]
        simp [SparseCalendarReplay.recordAt, ReferencePrelaunchFollower.loggingRound]
      · rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests _ _ _ _ _ htests]
        simp [htests]

/-- The original source/control pair underlying the continuing subtype. -/
def forgetPlusControl
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  (z.1.val, z.2)

private theorem measurable_forgetPlusControl : Measurable
    (forgetPlusControl (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) (q := q) (t := t) (s := s) (hs := hs) (control0 := control0)) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd

/-- The actual retained-source physical marker, with the true selected payload
and learning enabled. -/
def currentPhysicalMarker
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
    (sourceRecordAtControl z.1.val z.2) (selectedBaselinePayload z.1) true

/-- Current saved emission with its original real normalization. This is
also defined on the larger continuing subtype, including dagger controls. -/
def currentNormalizedSavedContribution (i : Fin (p.m - 1))
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
    (sourceRecordAtControl z.1.val z.2) (selectedBaselinePayload z.1) i

private def sourceLoggingSucceededAtControl (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) : Bool :=
  Sum.elim (fun _ => false) (fun _ => true)
    (((sourceWholeStepCodeAtControl z).2.1 i).2.2.1)

private theorem measurable_sourceLoggingSucceededAtControl (i : Fin (p.m - 1)) :
    Measurable (sourceLoggingSucceededAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace (Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  have hwhole := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode.comp
    (measurable_sourceInputAtControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))
  exact (measurable_const.sumElim measurable_const).comp
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp hwhole))))))

private theorem sourceLoggingSucceeded_eq_actual (i : Fin (p.m - 1))
    (z : SourceX rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    sourceLoggingSucceededAtControl i z =
      ((sourceRecordAtControl z.1 z.2).output.followers i).downInput.isSome := by
  have h := congrArg (fun out : ReferenceActivePhysicalStep.FollowerObservation p rate =>
    out.downInput.isSome) ((ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs
      (sourceRecordAtControl z.1 z.2)).2.2.1 i)
  refine Eq.trans ?_ h
  change sourceLoggingSucceededAtControl i z =
    (ReferenceFollowerTailComposition.reconstructFollowerObservable
      ((sourceWholeStepCodeAtControl z).2.1 i)).downInput.isSome
  unfold sourceLoggingSucceededAtControl ReferenceFollowerTailComposition.reconstructFollowerObservable
    ReferenceFollowerTailComposition.reconstructDownInput
  cases ((sourceWholeStepCodeAtControl z).2.1 i).2.2.1 <;> rfl

private theorem measurable_assignedExponent (i : Fin (p.m - 1)) :
    Measurable (fun x : XPlus rate rewards C_star C_h q t s hs control0 =>
      (selectedBaselinePayload x).exponent (selectedBaselineAssignedArm i x)) := by
  have heval : Measurable (fun z : (Fin p.K → ℕ) × Fin p.K => z.1 z.2) :=
    measurable_from_prod_countable_left fun j => measurable_pi_apply j
  exact heval.comp (measurable_selectedBaselineInputExponent.prodMk
    (measurable_selectedBaselineAssignedArm i))

private theorem measurable_assignedThreshold (i : Fin (p.m - 1)) :
    Measurable (fun x : XPlus rate rewards C_star C_h q t s hs control0 =>
      ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold
        (selectedBaselinePayload x) (selectedBaselineAssignedArm i x)) := by
  let threshold : ℕ → ℝ := fun h =>
    (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * (((2 : ℝ) ^ h)⁻¹)) /
      SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  exact (measurable_of_countable threshold).comp (measurable_assignedExponent i)

private def unoccupiedMarkerReadout (i : Fin (p.m - 1))
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) : Option (Fin p.K) :=
  if sourceLoggingSucceededAtControl i (forgetPlusControl z) = true ∧
      sourceLoggingTestsPassBit i (forgetPlusControl z) = true ∧
      (sourceOwnEntryAtControl (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (forgetPlusControl z)).1 = selectedBaselineAssignedArm i z.1 ∧
      sourceCurrentThinScalar (forgetPlusControl z) ≤
        ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold
          (selectedBaselinePayload z.1) (selectedBaselineAssignedArm i z.1)
  then some (selectedBaselineAssignedArm i z.1) else none

private theorem measurable_unoccupiedMarkerReadout (i : Fin (p.m - 1)) :
    Measurable (unoccupiedMarkerReadout (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  have hforget := measurable_forgetPlusControl (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
    (hs := hs) (control0 := control0)
  have harm : Measurable (fun z : XPlus rate rewards C_star C_h q t s hs control0 ×
      TimeControl p => selectedBaselineAssignedArm i z.1) :=
    (measurable_selectedBaselineAssignedArm (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
    (hs := hs) (control0 := control0) i).comp measurable_fst
  have hsome : Measurable (fun z : XPlus rate rewards C_star C_h q t s hs control0 ×
      TimeControl p => some (selectedBaselineAssignedArm i z.1)) :=
    (measurable_of_countable (some : Fin p.K → Option (Fin p.K))).comp harm
  apply Measurable.ite _ hsome measurable_const
  exact (measurableSet_eq_fun ((measurable_sourceLoggingSucceededAtControl i).comp hforget)
    measurable_const).inter
    ((measurableSet_eq_fun ((measurable_sourceLoggingTestsPassBit i).comp hforget)
      measurable_const).inter
      ((measurableSet_eq_fun ((measurable_fst.comp
        (measurable_sourceOwnEntryAtControl (PublicDiscreteDraws.followerPlayer p.two_le_m i))).comp
          hforget) harm).inter
        (measurableSet_le (measurable_sourceCurrentThinScalar.comp hforget)
          ((measurable_assignedThreshold i).comp measurable_fst))))

private def occupiedMarkerReadout (i : Fin (p.m - 1))
    (slice : CanonicalRecordingSlice.Slice p.m p.K)
    (down : Option (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))) :
    Option (Fin p.K) :=
  match down with
  | none => none
  | some d =>
      if CanonicalRecordingSlice.deterministicOwnedRecordingGate p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) (PublicDiscreteDraws.followerPlayer p.two_le_m i)
        (PrelaunchBufferRecovery.downArm rate.eta d)
        (ActiveFollowerQueueOperation.thinningProbability rate.eta d) slice
      then some (PrelaunchBufferRecovery.downArm rate.eta d) else none

private theorem measurable_occupiedMarkerReadout (i : Fin (p.m - 1)) :
    Measurable (fun z : CanonicalRecordingSlice.Slice p.m p.K ×
      Option (OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)) =>
        occupiedMarkerReadout (rate := rate) i z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro down
  cases down with
  | none => exact measurable_const
  | some d =>
      exact Measurable.ite
        (CanonicalRecordingSlice.measurableSet_deterministicOwnedRecordingGate
          p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)
          (PrelaunchBufferRecovery.downArm rate.eta d)
          (ActiveFollowerQueueOperation.thinningProbability rate.eta d))
        measurable_const measurable_const

private def followerMarkerReadout (i : Fin (p.m - 1))
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) : Option (Fin p.K) :=
  if sourcePreparedStatusAtControl i (forgetPlusControl z) = some .unoccupied then
    unoccupiedMarkerReadout i z
  else occupiedMarkerReadout (rate := rate) i z.2.1
    (sourcePreparedLastDownAtControl i (forgetPlusControl z))

private theorem measurable_followerMarkerReadout (i : Fin (p.m - 1)) :
    Measurable (followerMarkerReadout (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  apply Measurable.ite
    (measurableSet_eq_fun ((measurable_sourcePreparedStatusAtControl i).comp
      measurable_forgetPlusControl) measurable_const) (measurable_unoccupiedMarkerReadout i)
  exact (measurable_occupiedMarkerReadout i).comp
    ((measurable_fst.comp measurable_snd).prodMk
      ((measurable_sourcePreparedLastDownAtControl i).comp measurable_forgetPlusControl))

private def dataMarkerReadout (source : Fin p.m)
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) : Option (Fin p.K) :=
  if hc : source = ActiveRoundActions.coordinator p.two_le_m then
    sourceCoordinatorGateArmAtControl (forgetPlusControl z)
  else followerMarkerReadout (ActiveRoundActions.followerIndex p.two_le_m source hc) z

private theorem measurable_dataMarkerReadout (source : Fin p.m) :
    Measurable (dataMarkerReadout (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) source) := by
  unfold dataMarkerReadout
  split
  · exact measurable_sourceCoordinatorGateArmAtControl.comp measurable_forgetPlusControl
  · exact measurable_followerMarkerReadout _

private theorem followerMarkerReadout_eq_actual (i : Fin (p.m - 1))
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    followerMarkerReadout i z =
      match ((sourceRecordAtControl z.1.val z.2).output.preparation.followers.followers i).configuration with
      | .dagger => none
      | .ordinary state _ =>
          if state.status = .unoccupied then
            ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker
              (sourceRecordAtControl z.1.val z.2) (selectedBaselinePayload z.1) i state
          else match state.lastDown with
            | none => none
            | some down => if ActiveFollowerQueueOperation.recorderGate rate.eta i
                (sourceRecordAtControl z.1.val z.2).input.row
                (sourceRecordAtControl z.1.val z.2).input.time down
              then some (PrelaunchBufferRecovery.downArm rate.eta down) else none := by
  have hstatus := offer_status_decodes (sourcePreparedIncomingAtControl i (forgetPlusControl z))
  have hdown := offer_down_decodes (sourcePreparedIncomingAtControl i (forgetPlusControl z))
  rw [preparedIncoming_decodes (rate := rate) i (forgetPlusControl z)] at hstatus hdown
  change sourcePreparedStatusAtControl i (forgetPlusControl z) = _ at hstatus
  change sourcePreparedLastDownAtControl i (forgetPlusControl z) = _ at hdown
  have hslice : ((sourceRecordAtControl z.1.val z.2).input.row.2
      (sourceRecordAtControl z.1.val z.2).input.time).1 = z.2.1 :=
    sourceSlice_eq_actual (z.1.val, z.2)
  unfold followerMarkerReadout
  dsimp only [forgetPlusControl] at hstatus hdown ⊢
  cases hp : ((sourceRecordAtControl z.1.val z.2).output.preparation.followers.followers i).configuration with
  | dagger => simp only [hp] at hstatus hdown ⊢; simp [hstatus, hdown, occupiedMarkerReadout]
  | ordinary state memory =>
      simp only [hp] at hstatus ⊢
      by_cases hu : state.status = .unoccupied
      · simp only [hstatus, hu, ite_true]
        rw [unoccupied_marker_formula _ _ i state memory hp hu]
        unfold unoccupiedMarkerReadout sourceLoggingTestsPassBit sourceLoggingTestsAtControl
          selectedBaselineAssignedArm sourceCurrentThinScalar
        rw [sourceLoggingSucceeded_eq_actual (rate := rate) i (forgetPlusControl z),
          sourceOwnEntry_eq_actual (PublicDiscreteDraws.followerPlayer p.two_le_m i) (forgetPlusControl z)]
        rw [hslice]
        simp only [decide_eq_true_eq]
        rfl
      · simp only [hp] at hdown
        simp only [hstatus, hu, Option.some.injEq, ite_false, hdown]
        cases hd : state.lastDown with
        | none => rfl
        | some down =>
            unfold occupiedMarkerReadout ActiveFollowerQueueOperation.recorderGate
              CanonicalRecordingSlice.deterministicOwnedRecordingGate
            dsimp only
            rw [hslice]

private theorem dataMarkerReadout_eq_actual (source : Fin p.m)
    (z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    dataMarkerReadout source z = ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
      (sourceRecordAtControl z.1.val z.2) (selectedBaselinePayload z.1) source := by
  unfold dataMarkerReadout ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
  split
  · unfold sourceCoordinatorGateArmAtControl
    rw [sourceCoordinatorRecordingAtControl_eq_actual]
    rfl
  · exact followerMarkerReadout_eq_actual _ z

/-- Joint Borel measurability of the literal physical marker as BOTH the
retained source and the whole current control vary. No numerical-cell
transport or non-DATA ordinary-preparation hypothesis is used. -/
theorem measurable_currentPhysicalMarker :
    Measurable (currentPhysicalMarker (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := by
  have hdata : Measurable (fun z :
      (XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p) × Fin p.m =>
        dataMarkerReadout z.2 z.1) :=
    measurable_from_prod_countable_left measurable_dataMarkerReadout
  have hsource := measurable_sourceCurrentRecorderSource.comp
    (measurable_forgetPlusControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0))
  have hread : Measurable (fun z : XPlus rate rewards C_star C_h q t s hs control0 ×
      TimeControl p => if PublicDiscreteDraws.slotDraw z.2.1 = PublicDiscreteDraws.dataSlot
      then dataMarkerReadout
        (PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K z.2.1) z
      else none) := Measurable.ite
    (measurableSet_eq_fun (measurable_sourceCurrentSlotDraw.comp
      measurable_forgetPlusControl) measurable_const)
    (hdata.comp (measurable_id.prodMk hsource)) measurable_const
  convert hread using 1
  funext z
  unfold currentPhysicalMarker ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
  dsimp only
  have hslice : ((sourceRecordAtControl z.1.val z.2).input.row.2
      (sourceRecordAtControl z.1.val z.2).input.time).1 = z.2.1 :=
    sourceSlice_eq_actual (z.1.val, z.2)
  rw [hslice]
  simp only [dite_true]
  rw [dataMarkerReadout_eq_actual]
  rfl

private theorem measurable_savedContribution_varyingExponent :
    Measurable (fun z : FollowerDownMeasurability.SavedScalar × ℕ =>
      SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ) rate.eta.val
        z.2 z.1.1 z.1.2) :=
  measurable_from_prod_countable_left fun h =>
    FollowerDownMeasurability.measurable_savedContribution p.K (p.m - 1)
      (D p : ℝ) rate.eta.val h

private theorem saved_contribution_formula
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution record payload i =
      if (match (record.output.preparation.followers.followers i).configuration with
          | .dagger => none | .ordinary state _ => some state.status) = some .unoccupied ∧
        SparseCalendarReplay.loggingTestsPass (ReferencePrelaunchFollower.loggingRound i
          record.input.row (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).1 =
          payload.assignment.assigned i
      then SparseCalendarReplay.savedContribution p.K (p.m - 1) (D p : ℝ) rate.eta.val
        (payload.exponent (payload.assignment.assigned i))
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val
        ((record.input.row.2 record.input.time).1 ContinuousControlSlice.Label.thin)
      else 0 := by
  unfold ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
    ReferenceFollowerBufferProvenance.logEmission
  dsimp only
  cases hp : (record.output.preparation.followers.followers i).configuration with
  | dagger => simp [SparseCalendarReplay.sparseBufferContribution]
  | ordinary state memory =>
      by_cases hu : state.status = .unoccupied
      · simp only [hu, dite_true, true_and]
        by_cases ht : SparseCalendarReplay.loggingTestsPass (ReferencePrelaunchFollower.loggingRound i
          record.input.row (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
        · rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests _ _ _ _ _ ht]
          simp only [ht, true_and]
          simp [SparseCalendarReplay.sparseBufferContribution, SparseCalendarReplay.recordAt,
            ReferencePrelaunchFollower.loggingRound,
            ReferenceContinuingRecordingPhysicalReward.bufferFollowerIndex]
          rfl
        · rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests _ _ _ _ _ ht]
          simp [ht, SparseCalendarReplay.sparseBufferContribution]
      · simp [hu, SparseCalendarReplay.sparseBufferContribution]

/-- Joint Borel measurability of M's literal current saved contribution. The
proof keeps the actual empty/singleton emission, true assigned arm, dynamic
exponent, real observation, inclusive thinning, and `eta*D` normalization. -/
theorem measurable_currentNormalizedSavedContribution (i : Fin (p.m - 1)) :
    Measurable (currentNormalizedSavedContribution (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0) i) := by
  let domain := XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p
  let own : domain → Fin p.K × ReferencePrelaunchFollower.Observation p := fun z =>
    sourceOwnEntryAtControl (PublicDiscreteDraws.followerPlayer p.two_le_m i) (forgetPlusControl z)
  let arm : domain → Fin p.K := fun z => selectedBaselineAssignedArm i z.1
  let tests : domain → Prop := fun z =>
    sourcePreparedStatusAtControl i (forgetPlusControl z) = some .unoccupied ∧
    sourceLoggingTestsPassBit i (forgetPlusControl z) = true ∧ (own z).1 = arm z
  let value : domain → ℕ := fun z => SparseCalendarReplay.savedContribution p.K (p.m - 1)
    (D p : ℝ) rate.eta.val ((selectedBaselinePayload z.1).exponent (arm z))
    (own z).2.val (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin z.2.1)
  have hforget : Measurable (forgetPlusControl (rate := rate) (rewards := rewards)
      (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
      (hs := hs) (control0 := control0)) := measurable_forgetPlusControl
  have hown : Measurable own := (measurable_sourceOwnEntryAtControl _).comp hforget
  have harm : Measurable arm := (measurable_selectedBaselineAssignedArm i).comp measurable_fst
  have htests : MeasurableSet {z | tests z} :=
    (measurableSet_eq_fun ((measurable_sourcePreparedStatusAtControl i).comp hforget)
      measurable_const).inter
      ((measurableSet_eq_fun ((measurable_sourceLoggingTestsPassBit i).comp hforget)
        measurable_const).inter (measurableSet_eq_fun (measurable_fst.comp hown) harm))
  have hvalue : Measurable value := measurable_savedContribution_varyingExponent.comp
    (((measurable_subtype_coe.comp (measurable_snd.comp hown)).prodMk
      ((measurable_pi_apply ContinuousControlSlice.Label.thin).comp
        (measurable_fst.comp measurable_snd))).prodMk
      ((measurable_assignedExponent i).comp measurable_fst))
  have hnat : Measurable (fun z => if tests z then value z else 0) :=
    Measurable.ite htests hvalue measurable_const
  have hreal : Measurable (fun z => ((if tests z then value z else 0 : ℕ) : ℝ) /
      (rate.eta.val * (D p : ℝ))) :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hnat).div_const _
  convert hreal using 1
  funext z
  unfold currentNormalizedSavedContribution
    ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
  congr 2
  have hstatus := offer_status_decodes (sourcePreparedIncomingAtControl i (forgetPlusControl z))
  rw [preparedIncoming_decodes (rate := rate) i (forgetPlusControl z)] at hstatus
  change sourcePreparedStatusAtControl i (forgetPlusControl z) = _ at hstatus
  dsimp only [forgetPlusControl] at hstatus
  simp only [tests, value, own, arm, sourceLoggingTestsPassBit, decide_eq_true_eq,
    sourceLoggingTestsAtControl, sourceOwnEntry_eq_actual]
  dsimp only [forgetPlusControl]
  rw [saved_contribution_formula]
  rw [← hstatus]
  have hslice : ((sourceRecordAtControl z.1.val z.2).input.row.2
      (sourceRecordAtControl z.1.val z.2).input.time).1 = z.2.1 :=
    sourceSlice_eq_actual (z.1.val, z.2)
  rw [hslice]
  rfl

/-- The square of the same literal saved readout is jointly Borel. -/
theorem measurable_currentNormalizedSavedContribution_sq (i : Fin (p.m - 1)) :
    Measurable (fun z : XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      currentNormalizedSavedContribution i z ^ 2) :=
  (measurable_currentNormalizedSavedContribution i).pow_const 2

/-- Restriction to the requested literal unoccupied-follower subtype. -/
theorem measurable_follower_current_saved_contribution (i : Fin (p.m - 1)) :
    Measurable (fun z : XFollower rate rewards C_star C_h q t s hs control0 i × TimeControl p =>
      ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
        (sourceRecordAtControl (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
          (hs := hs) (control0 := control0) z.1.val z.2)
        (selectedBaselinePayload (followerAsPlus (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
          (hs := hs) (control0 := control0) i z.1)) i) := by
  let domain := XFollower rate rewards C_star C_h q t s hs control0 i × TimeControl p
  let f : domain → XPlus rate rewards C_star C_h q t s hs control0 × TimeControl p :=
    fun z => (⟨z.1.val, z.1.property.1⟩, z.2)
  have hv : Measurable (fun z : domain => z.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hf : Measurable f := (hv.subtype_mk).prodMk measurable_snd
  have h := (measurable_currentNormalizedSavedContribution (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
    (hs := hs) (control0 := control0) i).comp hf
  convert h using 1
  funext z
  rfl

/-- Second-moment readout on that same inherited follower subtype. -/
theorem measurable_follower_current_saved_contribution_sq (i : Fin (p.m - 1)) :
    Measurable (fun z : XFollower rate rewards C_star C_h q t s hs control0 i × TimeControl p =>
      (ReferenceContinuingSavedIncrementMoments.normalizedCurrentSavedContribution
        (sourceRecordAtControl (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
          (hs := hs) (control0 := control0) z.1.val z.2)
        (selectedBaselinePayload (followerAsPlus (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (q := q) (t := t) (s := s)
          (hs := hs) (control0 := control0) i z.1)) i) ^ 2) :=
  (measurable_follower_current_saved_contribution i).pow_const 2

end Bandits.Support.ReferenceFirstLiveRecordingReadoutMeasurability

end
