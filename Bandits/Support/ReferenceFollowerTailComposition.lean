/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep
public import Bandits.Support.ReferenceDownCutJointMeasurability
public import Bandits.Support.ReferenceFollowerLoggingMeasurability

/-!
# Lossless Borel composition of the reference follower tail

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:235-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,54-60`.

This internal result composes the accepted checked logger, reference DOWN,
occupied service, and release/finish on their actual inputs. The observation
retains the entire output configuration, failure stage, original logged DOWN
input, and full cut diagnostics. Saved scalar fibers and complete public rows
keep their existing measurable spaces. There is no valid-domain, successful
operation, no-mismatch, or history premise. Whole-step input producers remain
separate obligations; no physical-run, probability, or manuscript closure is
asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair

namespace Bandits.Support.ReferenceFollowerTailComposition


abbrev Parameters := ConstructorDimensions.Parameters

abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The full independent input requested by the local composition. -/
abbrev FinishFollowerInput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    (FollowerPrepareJointMeasurability.PrepareOutput p rate activation × Fin (D p + 1))

/-- Absence or the original carried state, with its existing continuous fibers. -/
abbrev DownInputObservable (p : Parameters) (rate : RateInput p) :=
  Unit ⊕ CarriedState p rate

/-- A lossless product observation of the four actual follower output fields. -/
abbrev FollowerObservable (p : Parameters) (rate : RateInput p) :=
  FollowerPrepareJointMeasurability.IncomingConfiguration p rate ×
    (Option DeclaredFollowerLocalRound.RoundFailure ×
      (DownInputObservable p rate × Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)))

/-- Intermediate output coordinates, carrying every record-stage diagnostic. -/
abbrev RecordObservable (p : Parameters) (rate : RateInput p) :=
  (DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate) ×
    (DownInputObservable p rate × Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate))

/-- Reconstruct every register and original saved scalar of a carried state. -/
def reconstructCarry (carry : CarriedState p rate) : State p rate.eta :=
  reconstructCarriedState carry.1 carry.2

/-- Decode the original logged input without reevaluating logging. -/
def reconstructDownInput (input : DownInputObservable p rate) :
    Option (State p rate.eta) :=
  match input with
  | .inl _ => none
  | .inr carry => some (reconstructCarry carry)

/-- Decode the cut using precisely its accompanying original logged buffer. -/
def reconstructDown (input : DownInputObservable p rate)
    (cut : Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)) :
    Option (ReferenceDownReception.ReferenceDownCutOutput p rate) :=
  match input with
  | .inl _ => none
  | .inr carry => cut.map fun code =>
      ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode code (carriedStateBuffer carry)

/-- Literal decoder of the complete product observation. -/
def reconstructFollowerObservable (output : FollowerObservable p rate) :
    ReferenceActivePhysicalStep.FollowerObservation p rate :=
  ⟨FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate output.1, output.2.1,
    reconstructDownInput output.2.2.1,
    reconstructDown output.2.2.1 output.2.2.2⟩

/-- Decode the checked record/service result and its retained DOWN evidence. -/
def reconstructRecord (output : RecordObservable p rate) :
    ReferenceActivePhysicalStep.FollowerRecord (rate := rate) :=
  ⟨Sum.elim Except.error (fun carry => Except.ok (reconstructCarry carry)) output.1,
    reconstructDownInput output.2.1, reconstructDown output.2.1 output.2.2⟩

private theorem measurable_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
    (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_sum_parameter {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (f : α → γ → δ) (g : β → γ → δ)
    (hf : Measurable (fun x : α × γ => f x.1 x.2))
    (hg : Measurable (fun x : β × γ => g x.1 x.2)) :
    Measurable (fun x : (α ⊕ β) × γ =>
      match x.1 with | .inl a => f a x.2 | .inr b => g b x.2) := by
  convert (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib α β γ).measurable using 1
  funext x
  rcases x with ⟨a | b, c⟩ <;> rfl

private theorem measurable_withStateCode (rate : RateInput p) :
    Measurable (fun x : CarriedState p rate × FollowerStateCode p rate =>
      FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode x.1 x.2) := by
  apply measurable_from_prod_countable_left
  intro code
  apply measurable_of_sigma_sections
  intro index
  exact measurable_sigmaMk (code, index.2)

/-- Acceptance clears the buffer while retaining the returned registers. -/
def emptyCarry (code : FollowerStateCode p rate) : CarriedState p rate :=
  ⟨(code, ⟨0, Fin.elim0⟩), Fin.elim0⟩

private theorem reconstruct_withStateCode (carry : CarriedState p rate)
    (code : FollowerStateCode p rate) :
    reconstructCarry (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry code) =
      followerStateOfCode rate code (carriedStateBuffer carry) := rfl

private theorem reconstruct_emptyCarry (code : FollowerStateCode p rate) :
    reconstructCarry (emptyCarry code) = followerStateOfCode rate code [] := rfl

/-- Carry-level interpretation of the existing DOWN result constructors. -/
def consumeDownCode (carry : CarriedState p rate)
    (code : LocalDownResultCode p rate) :
    DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate :=
  match code with
  | .skipped before _ => .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry before)
  | .inputFailure _ reason => .inl (.downInput (inputFailureOfCode reason))
  | .decodeOrParseRejected _ after _ => .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry after)
  | .parsedButUnaccepted _ after _ _ => .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry after)
  | .outputFailure _ reason => .inl (.downOutput (outputFailureOfCode reason))
  | .accepted _ after _ _ _ _ _ => .inr (emptyCarry after)

private theorem measurable_consumeDownCode (rate : RateInput p) :
    Measurable (fun x : CarriedState p rate × LocalDownResultCode p rate =>
      consumeDownCode x.1 x.2) := by
  apply measurable_from_prod_countable_left
  intro code
  have hupdate (c : FollowerStateCode p rate) :
      Measurable (fun carry : CarriedState p rate =>
        Sum.inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry c) :
          CarriedState p rate → DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate) :=
    measurable_inr.comp ((measurable_withStateCode rate).comp
      (measurable_id.prodMk measurable_const))
  cases code with
  | skipped before reason => exact hupdate before
  | inputFailure before reason => exact measurable_const
  | decodeOrParseRejected before after raw => exact hupdate after
  | parsedButUnaccepted before after raw reply => exact hupdate after
  | outputFailure before reason => exact measurable_const
  | accepted before after raw reply scan registers lastService => exact measurable_const

private theorem consumeDownCode_reconstruct (carry : CarriedState p rate)
    (code : LocalDownResultCode p rate) :
    Sum.elim Except.error (fun c => Except.ok (reconstructCarry c))
        (consumeDownCode carry code) =
      DeclaredFollowerLocalRound.consumeDownResult rate
        (reconstructLocalDownResult code (carriedStateBuffer carry)) := by
  cases code <;> rfl

/-- Accepted occupied service code on the original observation coordinates. -/
def occupiedCode (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : ObservationInput p rate activation) :
    FollowerServiceMeasurability.OccupiedRoundCode p rate :=
  FollowerServiceMeasurability.occupiedRoundCodeAtJoint rate i activation
    (representativeState rate x.1) (serviceInputOfFiber x.2)

private theorem measurable_occupiedCode (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable (occupiedCode rate i activation) := by
  apply measurable_of_sigma_sections
  intro index
  apply (FollowerServiceMeasurability.measurable_occupiedRoundCodeAtJoint
    rate i activation (representativeState rate index)).comp
  have hvalues : Measurable (fun x : ObservationFiber p rate activation index =>
      representativeValues index (fiberValues x)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact (measurable_pi_apply (Fin.cast (sparseSkeletonBuffer_length index.2.2) j)).comp
      measurable_fst
  have hrow : Measurable (fiberRow (p := p) (rate := rate)
      (activation := activation) (index := index)) :=
    measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have htime : Measurable (fun x : ObservationFiber p rate activation index =>
      (fiberTime x).val) := measurable_subtype_coe.comp
    (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hfeedback : Measurable (fiberFeedbackIndex (p := p) (rate := rate)
      (activation := activation) (index := index)) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  exact ((hrow.prodMk htime).prodMk hfeedback).prodMk hvalues

/-- Occupied service replaces registers and retains the original scalar fiber. -/
def occupiedCarried (carry : CarriedState p rate)
    (code : FollowerServiceMeasurability.OccupiedRoundCode p rate) :
    DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate :=
  match code with
  | .serviceFailure => .inl .service
  | .success _ _ state => .inr (FollowerReleaseFinishJointMeasurability.carriedStateWithStateCode carry state)

private theorem measurable_occupiedCarried (rate : RateInput p) :
    Measurable (fun x : CarriedState p rate ×
        FollowerServiceMeasurability.OccupiedRoundCode p rate => occupiedCarried x.1 x.2) := by
  apply measurable_from_prod_countable_left
  intro code
  cases code with
  | serviceFailure => exact measurable_const
  | success arrival service state =>
      exact measurable_inr.comp ((measurable_withStateCode rate).comp
        (measurable_id.prodMk measurable_const))

private theorem occupiedCarried_reconstruct (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : ObservationInput p rate activation)
    (hoccupied : (reconstructCarry (observationInputCarriedState x)).status ≠ .unoccupied) :
    Sum.elim Except.error (fun c => Except.ok (reconstructCarry c))
        (occupiedCarried (observationInputCarriedState x) (occupiedCode rate i activation x)) =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i (observationInputRow x)
        activation (observationInputTime x).val (observationInputTime x).property
        (observationInputPlayedArm x) (feedbackAtGrid p (observationInputFeedbackIndex x))
        (reconstructCarry (observationInputCarriedState x)) := by
  have hstatus : (representativeState rate x.1).status ≠ .unoccupied := hoccupied
  have hcode : observationResultCode rate i activation x = .occupied (occupiedCode rate i activation x) := by
    simp only [observationResultCode, observationResultCodeOnFiber, dite_eq_right hstatus,
      occupiedCode, FollowerServiceMeasurability.occupiedRoundCodeAtJoint]
  have hactual := decode_observationResultCode_eq_actual rate i activation x
  rw [hcode] at hactual
  refine Eq.trans ?_ hactual
  cases occupiedCode rate i activation x <;> rfl

/-- The separately supplied inputs of one actual reference DOWN call. -/
abbrev DownCallInput (p : Parameters) (rate : RateInput p) :=
  Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    (CarriedState p rate × ((CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1)))

/-- The full reference cut and its consumed result, with the exact input carry. -/
def downCall (rate : RateInput p) (i : Fin (p.m - 1))
    (x : DownCallInput p rate) : RecordObservable p rate :=
  let cut := ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
    (ReferenceDownReception.referenceDownCut p x.1 i x.2.2.1.1 x.2.2.1.2
      (feedbackAtGrid p x.2.2.2) rate (reconstructCarry x.2.1))
  (consumeDownCode x.2.1 cut.outcome, (.inr x.2.1, some cut))

private theorem measurable_downCall (rate : RateInput p) (i : Fin (p.m - 1)) :
    Measurable (downCall rate i) := by
  have hcarry : Measurable (fun x : DownCallInput p rate => x.2.1) :=
    measurable_fst.comp measurable_snd
  have hrow : Measurable (fun x : DownCallInput p rate => x.2.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have htime : Measurable (fun x : DownCallInput p rate => x.2.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hfeedback : Measurable (fun x : DownCallInput p rate => x.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hcut := ReferenceDownCutJointMeasurability.measurable_referenceDownCutCode_comp rate
    (fun x : DownCallInput p rate => x.1) (fun x => x.2.1) (fun _ => i)
    (fun x => x.2.2.1.1) (fun x => x.2.2.1.2) (fun x => x.2.2.2)
    measurable_fst hcarry measurable_const hrow htime hfeedback
  have houtcome := (measurable_of_countable fun c : ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate =>
    c.outcome).comp hcut
  exact ((measurable_consumeDownCode rate).comp (hcarry.prodMk houtcome)).prodMk
    ((measurable_inr.comp hcarry).prodMk
      ((measurable_of_countable fun c : ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate => some c).comp hcut))

/-- Logging failure retains its stage; success calls DOWN on the returned carry. -/
def unoccupiedRecord (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p)
    (x : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      ReferenceFollowerLoggingMeasurability.LoggingInput p rate activation) : RecordObservable p rate :=
  match ReferenceFollowerLoggingMeasurability.checkedLoggingObservable rate i activation x.2 with
  | .inl reason => (.inl (.logging reason), (.inl (), none))
  | .inr logged => downCall rate i
      (x.1, (logged, ((observationInputRow x.2.val,
        (observationInputTime x.2.val).val), observationInputFeedbackIndex x.2.val)))

private theorem measurable_unoccupiedRecord (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable (unoccupiedRecord rate i activation) := by
  let Ω := Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    ReferenceFollowerLoggingMeasurability.LoggingInput p rate activation
  have hrow := (ReferenceFollowerLoggingMeasurability.measurable_loggingInputRow rate activation).comp
    (measurable_snd : Measurable (Prod.snd : Ω → _))
  have htime := measurable_subtype_coe.comp
    ((ReferenceFollowerLoggingMeasurability.measurable_loggingInputTime rate activation).comp
      (measurable_snd : Measurable (Prod.snd : Ω → _)))
  have hfeedback := (ReferenceFollowerLoggingMeasurability.measurable_loggingInputFeedbackIndex rate activation).comp
    (measurable_snd : Measurable (Prod.snd : Ω → _))
  have hsuccess : Measurable (fun x : CarriedState p rate × Ω => downCall rate i
      (x.2.1, (x.1, ((observationInputRow x.2.2.val,
        (observationInputTime x.2.2.val).val), observationInputFeedbackIndex x.2.2.val)))) :=
    (measurable_downCall rate i).comp
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (((hrow.comp measurable_snd).prodMk
          (htime.comp measurable_snd)).prodMk (hfeedback.comp measurable_snd))))
  have hboth := measurable_sum_parameter
    (fun reason : ActiveFollowerLogging.LoggingFailure => fun _ : Ω =>
      ((.inl (.logging reason), (.inl (), none)) : RecordObservable p rate))
    (fun logged : CarriedState p rate => fun x : Ω => downCall rate i
      (x.1, (logged, ((observationInputRow x.2.val,
        (observationInputTime x.2.val).val), observationInputFeedbackIndex x.2.val))))
    ((((show Measurable (fun reason : ActiveFollowerLogging.LoggingFailure =>
      (Sum.inl (.logging reason) : DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate)) from
        fun _ _ => trivial)).comp
      measurable_fst).prodMk measurable_const) hsuccess
  convert hboth.comp
    (((ReferenceFollowerLoggingMeasurability.measurable_checkedLoggingObservable rate i activation).comp
      measurable_snd).prodMk measurable_id) using 1
  funext x
  dsimp only [Function.comp_def, id_eq]
  unfold unoccupiedRecord
  cases ReferenceFollowerLoggingMeasurability.checkedLoggingObservable rate i activation x.2 <;> rfl

private theorem downCall_reconstruct (rate : RateInput p) (i : Fin (p.m - 1))
    (x : DownCallInput p rate) :
    reconstructRecord (downCall rate i x) =
      let cut := ReferenceDownReception.referenceDownCut p x.1 i x.2.2.1.1 x.2.2.1.2
        (feedbackAtGrid p x.2.2.2) rate (reconstructCarry x.2.1)
      (⟨DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome,
        some (reconstructCarry x.2.1), some cut⟩ : ReferenceActivePhysicalStep.FollowerRecord) := by
  have hcut := ReferenceDownCutJointMeasurability.referenceDownCutCode_reconstruct
    x.1 x.2.1 i x.2.2.1.1 x.2.2.1.2 x.2.2.2
  unfold downCall reconstructRecord
  rw [consumeDownCode_reconstruct]
  change
    (⟨DeclaredFollowerLocalRound.consumeDownResult rate
        (ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode
          (ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
            (ReferenceDownReception.referenceDownCut p x.1 i x.2.2.1.1 x.2.2.1.2
              (feedbackAtGrid p x.2.2.2) rate (reconstructCarry x.2.1)))
          (carriedStateBuffer x.2.1)).outcome,
      some (reconstructCarry x.2.1),
      some (ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode
        (ReferenceDownReceptionMeasurability.encodeReferenceDownCutCode
          (ReferenceDownReception.referenceDownCut p x.1 i x.2.2.1.1 x.2.2.1.2
            (feedbackAtGrid p x.2.2.2) rate (reconstructCarry x.2.1)))
        (carriedStateBuffer x.2.1))⟩ : ReferenceActivePhysicalStep.FollowerRecord) = _
  dsimp only [reconstructCarry]
  rw [hcut]

private theorem unoccupiedRecord_reconstruct (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p)
    (x : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      ReferenceFollowerLoggingMeasurability.LoggingInput p rate activation) :
    reconstructRecord (unoccupiedRecord rate i activation x) =
      ReferenceActivePhysicalStep.recordFollower x.1 i (observationInputRow x.2.val)
        activation (observationInputTime x.2.val).val (observationInputTime x.2.val).property
        (observationInputPlayedArm x.2.val)
        (feedbackAtGrid p (observationInputFeedbackIndex x.2.val))
        (reconstructCarry (observationInputCarriedState x.2.val)) := by
  have hstatus : (reconstructCarry (observationInputCarriedState x.2.val)).status =
      .unoccupied := x.2.property
  have hlog := ReferenceFollowerLoggingMeasurability.checkedLoggingObservable_reconstruct
    rate i activation x.2
  unfold unoccupiedRecord
  cases hout : ReferenceFollowerLoggingMeasurability.checkedLoggingObservable
      rate i activation x.2 with
  | inl reason =>
      rw [hout] at hlog
      change Except.error reason = _ at hlog
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus]
      dsimp only [reconstructCarry, observationInputCarriedState]
      rw [← hlog]
      rfl
  | inr logged =>
      rw [hout] at hlog
      change Except.ok (reconstructCarry logged) = _ at hlog
      simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus]
      dsimp only [reconstructCarry, observationInputCarriedState]
      rw [← hlog]
      exact downCall_reconstruct rate i _

/-- View together with the existing complete observation input. -/
abbrev RecordInput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    ObservationInput p rate activation

/-- Occupied record branch uses accepted service and produces no DOWN call. -/
def occupiedRecord (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : ObservationInput p rate activation) :
    RecordObservable p rate :=
  (occupiedCarried (observationInputCarriedState x) (occupiedCode rate i activation x),
    (.inl (), none))

private theorem measurable_occupiedRecord (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable (occupiedRecord rate i activation) :=
  ((measurable_occupiedCarried rate).comp
    ((measurable_observationInputCarriedState rate activation).prodMk
      (measurable_occupiedCode rate i activation))).prodMk measurable_const

/-- The logger subtype selector is derived from the actual choice-state status. -/
def recordObservable (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : RecordInput p rate activation) :
    RecordObservable p rate :=
  if h : x.2 ∈ ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation then
    unoccupiedRecord rate i activation (x.1, ⟨x.2, h⟩)
  else occupiedRecord rate i activation x.2

private theorem measurable_recordObservable (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable (recordObservable rate i activation) := by
  let s : Set (RecordInput p rate activation) :=
    {x | x.2 ∈ ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation}
  have hs : MeasurableSet s :=
    (ReferenceFollowerLoggingMeasurability.measurableSet_unoccupiedLoggingInputs
      rate activation).preimage measurable_snd
  have hin : Measurable (fun x : s =>
      (x.val.1, (⟨x.val.2, x.property⟩ :
        ReferenceFollowerLoggingMeasurability.LoggingInput p rate activation))) :=
    (measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)
  exact ((measurable_unoccupiedRecord rate i activation).comp hin).dite
    ((measurable_occupiedRecord rate i activation).comp
      (measurable_snd.comp measurable_subtype_coe)) hs

private theorem recordObservable_reconstruct (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : RecordInput p rate activation) :
    reconstructRecord (recordObservable rate i activation x) =
      ReferenceActivePhysicalStep.recordFollower x.1 i (observationInputRow x.2)
        activation (observationInputTime x.2).val (observationInputTime x.2).property
        (observationInputPlayedArm x.2) (feedbackAtGrid p (observationInputFeedbackIndex x.2))
        (reconstructCarry (observationInputCarriedState x.2)) := by
  by_cases h : x.2 ∈ ReferenceFollowerLoggingMeasurability.unoccupiedLoggingInputs rate activation
  · rw [recordObservable, dite_eq_left h]
    exact unoccupiedRecord_reconstruct rate i activation _
  · rw [recordObservable, dite_eq_right h]
    have hstatus : (reconstructCarry (observationInputCarriedState x.2)).status ≠
        .unoccupied := h
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hstatus]
    have hresult := occupiedCarried_reconstruct rate i activation x.2 hstatus
    change (⟨_, none, none⟩ : ReferenceActivePhysicalStep.FollowerRecord) = _
    dsimp only [occupiedRecord]
    rw [hresult]

/-- Final local configuration and exact optional failure-stage coordinates. -/
abbrev FinishedPair (p : Parameters) (rate : RateInput p) :=
  FollowerPrepareJointMeasurability.IncomingConfiguration p rate ×
    Option DeclaredFollowerLocalRound.RoundFailure

/-- Interpret the accepted carried release/finish result literally. -/
def finishedPair (output :
    FollowerReleaseFinishJointMeasurability.ReleaseAndFinishCarriedOutput p rate) :
    FinishedPair p rate :=
  match output with
  | .inl reason => (none, some reason)
  | .inr data => (some data, none)

private theorem measurable_finishedPair (rate : RateInput p) :
    Measurable (finishedPair (p := p) (rate := rate)) := by
  apply Measurable.sumElim
  · exact measurable_const.prodMk (measurable_of_countable fun reason => some reason)
  · have hsome : Measurable (fun data : CarriedState p rate ×
        FollowerLifecycleMeasurability.LocalMemoryCode p =>
        (some data : FollowerPrepareJointMeasurability.IncomingConfiguration p rate)) := by
      apply measurable_comap_iff.mpr
      exact measurable_inr
    exact hsome.prodMk measurable_const

/-- Run release/finish with the original choice carry and memory, and the
independently returned post-record carry. Record failure stops the tail. -/
def finishRecordResult (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p)
    (result : DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate)
    (original : ObservationInput p rate activation ×
      FollowerLifecycleMeasurability.LocalMemoryCode p) : FinishedPair p rate :=
  match result with
  | .inl reason => (none, some reason)
  | .inr postRecord => finishedPair
      (FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput postRecord
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents rate i
          (observationInputCarriedState original.1) postRecord original.2
          (observationInputRow original.1) (observationInputTime original.1).val
          (observationInputFeedbackIndex original.1)))

private theorem measurable_finishRecordResult (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable
      (fun x : (DeclaredFollowerLocalRound.RoundFailure ⊕ CarriedState p rate) ×
        (ObservationInput p rate activation × FollowerLifecycleMeasurability.LocalMemoryCode p) =>
        finishRecordResult rate i activation x.1 x.2) := by
  have hpre : Measurable (fun x : CarriedState p rate ×
        (ObservationInput p rate activation × FollowerLifecycleMeasurability.LocalMemoryCode p) =>
        observationInputCarriedState x.2.1) :=
    (measurable_observationInputCarriedState rate activation).comp
      (measurable_fst.comp measurable_snd)
  let Ω := CarriedState p rate ×
    (ObservationInput p rate activation × FollowerLifecycleMeasurability.LocalMemoryCode p)
  have hinput : Measurable (fun x : Ω => x.2.1) := measurable_fst.comp measurable_snd
  have hrow := (measurable_observationInputRow rate activation).comp hinput
  have htime := measurable_subtype_coe.comp
    ((measurable_observationInputTime rate activation).comp hinput)
  have hfeedback := (measurable_observationInputFeedbackIndex rate activation).comp hinput
  have hrelease :=
    FollowerReleaseFinishJointMeasurability.measurable_releaseAndFinishCarriedOutputAtComponents
      rate i _ _ _ _ _ _ hpre measurable_fst
      (measurable_snd.comp measurable_snd) hrow htime hfeedback
  convert measurable_sum_parameter
    (fun reason : DeclaredFollowerLocalRound.RoundFailure =>
      fun _ : ObservationInput p rate activation × FollowerLifecycleMeasurability.LocalMemoryCode p =>
        ((none, some reason) : FinishedPair p rate))
    (fun postRecord : CarriedState p rate => fun original => finishedPair
      (FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput postRecord
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents rate i
          (observationInputCarriedState original.1) postRecord original.2
          (observationInputRow original.1) (observationInputTime original.1).val
          (observationInputFeedbackIndex original.1))))
    (measurable_const.prodMk
      ((measurable_of_countable fun reason : DeclaredFollowerLocalRound.RoundFailure =>
        some reason).comp measurable_fst))
    ((measurable_finishedPair rate).comp hrelease) using 1
  funext x
  rcases x with ⟨result, original⟩
  cases result <;> rfl

/-- Ordinary branch coordinates retain the entire choice snapshot and memory. -/
abbrev OrdinaryInput (p : Parameters) (rate : RateInput p)
    (activation : Activation p) :=
  Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    (ObservationInput p rate activation × FollowerLifecycleMeasurability.LocalMemoryCode p)

/-- Compose recording, service or reference DOWN, and the checked final tail. -/
def ordinaryObservable (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : OrdinaryInput p rate activation) :
    FollowerObservable p rate :=
  let recorded := recordObservable rate i activation (x.1, x.2.1)
  let finished := finishRecordResult rate i activation recorded.1 x.2
  (finished.1, (finished.2, recorded.2))

private theorem measurable_ordinaryObservable (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable (ordinaryObservable rate i activation) := by
  have hinput : Measurable (fun x : OrdinaryInput p rate activation => (x.1, x.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hrecord := (measurable_recordObservable rate i activation).comp hinput
  have hfinish := (measurable_finishRecordResult rate i activation).comp
    ((measurable_fst.comp hrecord).prodMk measurable_snd)
  exact (measurable_fst.comp hfinish).prodMk
    ((measurable_snd.comp hfinish).prodMk (measurable_snd.comp hrecord))

/-- Full reference follower tail on all prepared outputs, including dagger,
logging errors, reference mismatch suppression, rejected/accepted DOWN,
occupied zero-arrival service, release errors, and final proposal-read errors. -/
def finishFollowerObservable (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : FinishFollowerInput p rate activation) :
    FollowerObservable p rate :=
  match x.2.1.2.2 with
  | none => (none, (none, (.inl (), none)))
  | some (carry, memory) => ordinaryObservable rate i activation
      (x.1, (assembleObservationInput carry x.2.1.1.1 x.2.1.1.2 x.2.2 x.2.1.2.1, memory))

/-- Borel measurability on the exact full product input, with no operation
success, buffer-domain, or mismatch hypothesis. -/
theorem measurable_finishFollowerObservable (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) : Measurable (finishFollowerObservable rate i activation) := by
  let Ω := FinishFollowerInput p rate activation
  have hrow : Measurable (fun x : (CarriedState p rate ×
        FollowerLifecycleMeasurability.LocalMemoryCode p) × Ω => x.2.2.1.1.1) :=
    measurable_fst.comp (measurable_fst.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have htime : Measurable (fun x : (CarriedState p rate ×
        FollowerLifecycleMeasurability.LocalMemoryCode p) × Ω => x.2.2.1.1.2) :=
    measurable_snd.comp (measurable_fst.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hfeedback : Measurable (fun x : (CarriedState p rate ×
        FollowerLifecycleMeasurability.LocalMemoryCode p) × Ω => x.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have harm : Measurable (fun x : (CarriedState p rate ×
        FollowerLifecycleMeasurability.LocalMemoryCode p) × Ω => x.2.2.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hobservation := measurable_assembleObservationInput _ _ _ _ _
    (measurable_fst.comp measurable_fst) hrow htime hfeedback harm
  have hordinary := (measurable_ordinaryObservable rate i activation).comp
    ((measurable_fst.comp measurable_snd).prodMk
      (hobservation.prodMk (measurable_snd.comp measurable_fst)))
  have hsum := measurable_sum_parameter
    (fun _ : Unit => fun _ : Ω =>
      ((none, (none, (.inl (), none))) : FollowerObservable p rate))
    (fun data : CarriedState p rate × FollowerLifecycleMeasurability.LocalMemoryCode p =>
      fun x : Ω => ordinaryObservable rate i activation
        (x.1, (assembleObservationInput data.1 x.2.1.1.1 x.2.1.1.2 x.2.2 x.2.1.2.1, data.2)))
    measurable_const hordinary
  have hconfig : Measurable (fun x : Ω => x.2.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hfull := hsum.comp
    (((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
      hconfig).prodMk measurable_id)
  convert hfull using 1
  funext x
  rcases x with ⟨view, ⟨⟨⟨row, time⟩, ⟨arm, configuration⟩⟩, k⟩⟩
  cases configuration with
  | none => rfl
  | some data => cases data; rfl

private theorem ordinaryObservable_reconstruct (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : OrdinaryInput p rate activation) :
    reconstructFollowerObservable (ordinaryObservable rate i activation x) =
      ReferenceActivePhysicalStep.finishFollower x.1
        ⟨i, observationInputRow x.2.1, activation, (observationInputTime x.2.1).val,
          (observationInputTime x.2.1).property, observationInputPlayedArm x.2.1,
          .ordinary (reconstructCarry (observationInputCarriedState x.2.1))
            (FollowerLifecycleMeasurability.localMemoryOfCode x.2.2)⟩
        (feedbackAtGrid p (observationInputFeedbackIndex x.2.1)) := by
  have hrecord := recordObservable_reconstruct rate i activation (x.1, x.2.1)
  dsimp only [ReferenceActivePhysicalStep.finishFollower]
  rw [← hrecord]
  unfold ordinaryObservable
  generalize recordObservable rate i activation (x.1, x.2.1) = recorded
  rcases recorded with ⟨result, diagnostics⟩
  cases result with
  | inl reason => rfl
  | inr postRecord =>
      have hfinish :=
        FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutputAtComponents_reconstruct
          rate i (observationInputCarriedState x.2.1) postRecord x.2.2
          (observationInputRow x.2.1) (observationInputTime x.2.1).val
          (observationInputFeedbackIndex x.2.1)
      dsimp only [reconstructRecord, Sum.elim, reconstructCarry, finishRecordResult]
      rw [← hfinish]
      generalize FollowerReleaseFinishJointMeasurability.releaseAndFinishCarriedOutput postRecord
        (FollowerReleaseFinishJointMeasurability.releaseAndFinishResultCodeAtComponents rate i
          (observationInputCarriedState x.2.1) postRecord x.2.2
          (observationInputRow x.2.1) (observationInputTime x.2.1).val
          (observationInputFeedbackIndex x.2.1)) = finished
      cases finished <;> rfl

/-- Exact reconstruction of all four fields of `finishFollower`, on every
input branch of the full product. -/
theorem finishFollowerObservable_reconstruct (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : FinishFollowerInput p rate activation) :
    reconstructFollowerObservable (finishFollowerObservable rate i activation x) =
      ReferenceActivePhysicalStep.finishFollower x.1
        (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i activation x.2.1)
        (feedbackAtGrid p x.2.2) := by
  rcases x with ⟨view, ⟨⟨⟨row, time⟩, ⟨arm, configuration⟩⟩, k⟩⟩
  cases configuration with
  | none => rfl
  | some data =>
      rcases data with ⟨carry, memory⟩
      exact ordinaryObservable_reconstruct rate i activation
        (view, (assembleObservationInput carry row time k arm, memory))

/-- Complete actual field identities, including the original logged input
and the entire reconstructed reference cut on failure as well as success. -/
theorem finishFollowerObservable_fields (rate : RateInput p) (i : Fin (p.m - 1))
    (activation : Activation p) (x : FinishFollowerInput p rate activation) :
    let output := finishFollowerObservable rate i activation x
    let actual := ReferenceActivePhysicalStep.finishFollower x.1
      (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i activation x.2.1)
      (feedbackAtGrid p x.2.2)
    FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate output.1 =
        actual.configuration ∧
      output.2.1 = actual.failure ∧
      reconstructDownInput output.2.2.1 = actual.downInput ∧
      reconstructDown output.2.2.1 output.2.2.2 = actual.down := by
  have h := finishFollowerObservable_reconstruct rate i activation x
  exact ⟨congrArg ReferenceActivePhysicalStep.FollowerObservation.configuration h,
    congrArg ReferenceActivePhysicalStep.FollowerObservation.failure h,
    congrArg ReferenceActivePhysicalStep.FollowerObservation.downInput h,
    congrArg ReferenceActivePhysicalStep.FollowerObservation.down h⟩

/-- Componentwise composition has only the three separately measurable maps
to the exact view, prepared output, and own feedback grid. -/
theorem measurable_finishFollowerObservable_comp (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (view : Ω → Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : Ω → FollowerPrepareJointMeasurability.PrepareOutput p rate activation)
    (feedback : Ω → Fin (D p + 1))
    (hview : Measurable view) (hprepared : Measurable prepared)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => finishFollowerObservable rate i activation
      (view ω, (prepared ω, feedback ω))) :=
  (measurable_finishFollowerObservable rate i activation).comp
    (hview.prodMk (hprepared.prodMk hfeedback))

private theorem preparedRoundOfOutput_atConfiguration (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (row : CompletePublicTable.CompleteRow p)
    (time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation) :
    FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i activation
        (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
          (FollowerPrepareJointMeasurability.assemblePrepareInput
            (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration)
            row time)) =
      DeclaredFollowerLocalRound.prepare rate i row activation time.val time.property configuration := by
  rw [FollowerPrepareJointMeasurability.preparedRoundOfOutput_prepare]
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
      change DeclaredFollowerLocalRound.prepare rate i row activation time.val time.property
        (.ordinary
          (followerStateOfCode rate (carriedStateOfState rate state).1.1
            (carriedStateBuffer (carriedStateOfState rate state)))
          (FollowerLifecycleMeasurability.localMemoryOfCode
            (FollowerLifecycleMeasurability.localMemoryCode memory))) = _
      rw [carriedStateOfState_reconstruct,
        FollowerLifecycleMeasurability.localMemoryOfCode_code]

/-- The canonical consumer input uses the actual selected row and incoming
configuration, the accepted PREPARE producer, the retained dispatcher's view,
and this follower's own simultaneous collision-feedback grid coordinate. -/
def canonicalFollowerInput {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) (i : Fin (p.m - 1)) :
    FinishFollowerInput p rate (x.state.activations i) :=
  (prepared.coordinator.downView,
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i (x.state.activations i)
      (FollowerPrepareJointMeasurability.assemblePrepareInput
        (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (x.state.followers i))
        x.row ⟨x.time, x.active i⟩),
      prepared.feedback.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))

/-- Lossless observable of the named canonical whole-step follower consumer. -/
def observeFollowerObservable {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) (i : Fin (p.m - 1)) :
    FollowerObservable p rate :=
  finishFollowerObservable rate i (x.state.activations i) (canonicalFollowerInput prepared i)

/-- Exact whole-step consumer identity. The two whole-step projections are
the actual dispatcher view and own grid feedback, never independent substitutes. -/
theorem observeFollowerObservable_reconstruct {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x) (i : Fin (p.m - 1)) :
    reconstructFollowerObservable (observeFollowerObservable prepared i) =
      prepared.observeFollower i := by
  rw [observeFollowerObservable, finishFollowerObservable_reconstruct]
  change ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
    (FollowerPrepareJointMeasurability.preparedRoundOfOutput rate i (x.state.activations i)
      (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i (x.state.activations i)
        (FollowerPrepareJointMeasurability.assemblePrepareInput
          (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate (x.state.followers i))
          x.row ⟨x.time, x.active i⟩)))
    (feedbackAtGrid p (prepared.feedback.feedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))) = _
  rw [preparedRoundOfOutput_atConfiguration]
  have hprepared : prepared.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
        x.time (x.active i) (x.state.followers i) := prepared.followers.followers_eq i
  have hfeedback : feedbackAtGrid p (prepared.feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) =
      prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    rw [prepared.feedback.observations_eq]
    rfl
  rw [hfeedback]
  exact congrArg (fun localPrepared => ReferenceActivePhysicalStep.finishFollower
    prepared.coordinator.downView localPrepared
      (prepared.feedback.observations (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    hprepared.symm

/-- Borel composer for the named consumer on a fixed activation fiber.
The activation equality is only typing for this fixed-activation theorem.
The five remaining hypotheses expose the actual incoming configuration,
selected complete row, time, dispatcher view, and own grid-feedback producers.
Their whole-step measurability is not asserted here. -/
theorem measurable_observeFollowerObservable_comp (rate : RateInput p)
    (i : Fin (p.m - 1)) (activation : Activation p)
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ∀ ω, ReferenceActivePhysicalStep.PreparedRound (input ω))
    (hactivation : ∀ ω, (input ω).state.activations i = activation)
    (hincoming : Measurable (fun ω =>
      FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate ((input ω).state.followers i)))
    (hrow : Measurable (fun ω => (input ω).row))
    (htime : Measurable (fun ω => (input ω).time))
    (hview : Measurable (fun ω => (prepared ω).coordinator.downView))
    (hfeedback : Measurable (fun ω => (prepared ω).feedback.feedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    Measurable (fun ω => observeFollowerObservable (prepared ω) i) := by
  let activeTime (ω : Ω) : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation :=
    ⟨(input ω).time, by rw [← hactivation ω]; exact (input ω).active i⟩
  have hactiveTime : Measurable activeTime := htime.subtype_mk
  have hprepare := FollowerPrepareJointMeasurability.measurable_prepareOutput_atComponents
    rate i activation
    (fun ω => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      ((input ω).state.followers i)) (fun ω => (input ω).row) activeTime
    hincoming hrow hactiveTime
  have h := measurable_finishFollowerObservable_comp rate i activation
    (fun ω => (prepared ω).coordinator.downView) _
    (fun ω => (prepared ω).feedback.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    hview hprepare hfeedback
  convert h using 1
  funext ω
  unfold observeFollowerObservable canonicalFollowerInput
  cases hactivation ω
  rfl

end Bandits.Support.ReferenceFollowerTailComposition
