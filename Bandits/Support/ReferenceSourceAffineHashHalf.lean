/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFixedTimeSourceControlCoupling
public import Bandits.Support.ReferenceDownPhysicalHashRule
public import Bandits.Support.ReferenceUpPhysicalHashRule
public import Bandits.Support.ReferenceActiveStepCompositionMeasurability

/-!
# Original-source fixed-boundary affine hash-half identity

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-150`,
`sources/zip4/manuscript/05_binary_transport.tex:7-42,74-124`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-42`.

These results integrate the actual selected physical DOWN and UP tests over
the original source law at one externally fixed round boundary.  They do not
assert a generated-history conditional law, an adaptive batch recurrence, a
decoder tail, or a manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActiveAffinePositiveTest
open Bandits.Support.ReferenceSelectedAffinePairLaw
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling

namespace Bandits.Support.ReferenceSourceAffineHashHalf

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Pair := ReferenceSelectedAffinePairLaw.Pair
abbrev Remainder := ReferenceSelectedAffinePairLaw.Remainder

variable {p : Parameters} {rate : RateInput p}

/-- The original whole-source input at a fixed incoming physical boundary.
Only the complete row table and the original private coordinator selection
are replaced; state, time, active typing, and the full reward grid are frozen. -/
def roundInputAtOriginalSource (boundary : RoundInput p rate) (source : SourceInput p) :
    RoundInput p rate :=
  ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary source

/-- The actual DOWN executed-positive event on the original selected-index
stratum and a full-remainder cylinder. -/
def downPositiveSourceEvent (boundary : RoundInput p rate) (q : Fin (M p))
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (0, i))) : Set (SourceInput p) :=
  {source | source ∈ ReferenceSelectedAffinePairLaw.stratumEvent p q boundary.time
      (0, i) C ∧
    ReferenceActiveAffinePositiveTest.downPositive
      (roundInputAtOriginalSource boundary source) = true ∧
    ReferenceActiveAffinePositiveTest.downSent
      (roundInputAtOriginalSource boundary source) ≠ some candidate}

/-- The corresponding DOWN event intersected with the actual full affine
coefficient-plus-offset sample hashing the fixed candidate to one. -/
def downPositiveHashOneSourceEvent (boundary : RoundInput p rate) (q : Fin (M p))
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (0, i))) : Set (SourceInput p) :=
  {source | source ∈ downPositiveSourceEvent boundary q i candidate C ∧
    AffineChannelLaw.affineHash
      (((source.1.2 q).2 boundary.time).2 (0, i)) candidate = 1}

/-- The actual UP executed-positive event on the original selected-index
stratum and a full-remainder cylinder. -/
def upPositiveSourceEvent (boundary : RoundInput p rate) (q : Fin (M p))
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (1, i))) : Set (SourceInput p) :=
  {source | source ∈ ReferenceSelectedAffinePairLaw.stratumEvent p q boundary.time
      (1, i) C ∧
    ReferenceActiveAffinePositiveTest.upPositive
      (roundInputAtOriginalSource boundary source) = true ∧
    ReferenceActiveAffinePositiveTest.upSent
      (roundInputAtOriginalSource boundary source) ≠ some candidate}

/-- The corresponding UP event intersected with the actual full affine
coefficient-plus-offset sample hashing the fixed candidate to one. -/
def upPositiveHashOneSourceEvent (boundary : RoundInput p rate) (q : Fin (M p))
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (1, i))) : Set (SourceInput p) :=
  {source | source ∈ upPositiveSourceEvent boundary q i candidate C ∧
    AffineChannelLaw.affineHash
      (((source.1.2 q).2 boundary.time).2 (1, i)) candidate = 1}

private def directionPositive (direction : Fin 2) (x : RoundInput p rate) : Bool :=
  if direction = 0 then ReferenceActiveAffinePositiveTest.downPositive x
  else ReferenceActiveAffinePositiveTest.upPositive x

private def directionSent (direction : Fin 2) (x : RoundInput p rate) :
    Option (Word (AffineBatchDecoder.width p)) :=
  if direction = 0 then ReferenceActiveAffinePositiveTest.downSent x
  else ReferenceActiveAffinePositiveTest.upSent x

private def directionPositiveSourceEvent (boundary : RoundInput p rate) (q : Fin (M p))
    (direction : Fin 2) (i : Fin (p.m - 1))
    (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (direction, i))) : Set (SourceInput p) :=
  {source | source ∈ ReferenceSelectedAffinePairLaw.stratumEvent
      p q boundary.time (direction, i) C ∧
    directionPositive direction (roundInputAtOriginalSource boundary source) = true ∧
    directionSent direction (roundInputAtOriginalSource boundary source) ≠ some candidate}

private def directionPositiveHashOneSourceEvent (boundary : RoundInput p rate)
    (q : Fin (M p)) (direction : Fin 2) (i : Fin (p.m - 1))
    (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (direction, i))) : Set (SourceInput p) :=
  {source | source ∈ directionPositiveSourceEvent boundary q direction i candidate C ∧
    AffineChannelLaw.affineHash
      (((source.1.2 q).2 boundary.time).2 (direction, i)) candidate = 1}

/-- Evaluate a measurable finite-index family at a measurable index. -/
private theorem measurable_pi_eval {Ω ι β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [Countable ι] [MeasurableSingletonClass ι] [MeasurableSpace β]
    (f : Ω → ι → β) (j : Ω → ι)
    (hf : Measurable f) (hj : Measurable j) : Measurable (fun x => f x (j x)) := by
  have heval : Measurable (fun z : (ι → β) × ι => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro i
    exact measurable_pi_apply i
  exact heval.comp (hf.prodMk hj)

/-- The fixed-boundary original-source round input is Borel on the genuine
original source product space. -/
theorem measurable_roundInputAtOriginalSource (boundary : RoundInput p rate) :
    Measurable (roundInputAtOriginalSource boundary) := by
  have hrows : Measurable (fun source : SourceInput p => source.1.2) := by
    exact measurable_snd.comp measurable_fst
  have hselected : Measurable (fun source : SourceInput p =>
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source) := by
    exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hcoordinates : Measurable (fun source : SourceInput p =>
      (boundary.state,
        (source.1.2,
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source,
            (boundary.time, boundary.rewards))))) :=
    measurable_const.prodMk (hrows.prodMk
      (hselected.prodMk (measurable_const.prodMk measurable_const)))
  have hactive : Measurable (fun source : SourceInput p =>
      (⟨(boundary.state,
        (source.1.2,
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source,
            (boundary.time, boundary.rewards)))), boundary.active⟩ :
        ReferenceActivePhysicalStepMeasurability.ActiveRoundCoordinates p rate)) := by
    exact hcoordinates.subtype_mk (h := fun _ => boundary.active)
  have hdecode := ReferenceActivePhysicalStepMeasurability.measurable_decodeRoundInput.comp hactive
  convert hdecode using 1
  rfl

/-- Measurability of the actual selector used by the UP and DOWN physical
word projections. -/
private theorem measurable_upSenderIndex :
    Measurable (fun x : RoundInput p rate => ReferenceActivePhysicalStep.upSenderIndex x) := by
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row
      (p := p) (rate := rate)
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time
      (p := p) (rate := rate)
  have hcontrol : Measurable (fun x : RoundInput p rate => (x.row.2 x.time)) := by
    have heval : Measurable (fun z : (Fin p.T → TimeControl p) × Fin p.T => z.1 z.2) := by
      apply measurable_from_prod_countable_left
      intro t
      exact measurable_pi_apply t
    exact heval.comp ((measurable_snd.comp hrow).prodMk htime)
  have hdraw : Measurable (fun x : RoundInput p rate =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((x.row.2 x.time).1)) := by
    exact (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      (measurable_fst.comp hcontrol)
  have hEq : (fun x : RoundInput p rate => ReferenceActivePhysicalStep.upSenderIndex x) =
      fun x => PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((x.row.2 x.time).1) := by
    funext x
    exact ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x
  rw [hEq]
  exact hdraw

/-- The actual selected DOWN expected word is Borel, including dispatch
failure and the map-independent `none` branch. -/
theorem measurable_downSent :
    Measurable (fun x : RoundInput p rate => ReferenceActiveAffinePositiveTest.downSent x) := by
  let : MeasurableSpace (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
    MeasurableSpace.pi
  have hWord : (MeasurableSpace.pi : MeasurableSpace
      (AffineChannelLaw.Word (AffineBatchDecoder.width p))) =
        CoordinatorUpMeasurability.affineWordMeasurableSpace
          (AffineBatchDecoder.width p) := by
    let : MeasurableSpace
        (AffineChannelLaw.Word (AffineBatchDecoder.width p)) := MeasurableSpace.pi
    let : MeasurableSingletonClass
        (AffineChannelLaw.Word (AffineBatchDecoder.width p)) := Pi.instMeasurableSingletonClass
    ext s
    constructor
    · intro _
      trivial
    · intro _
      have hsingleton (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
          MeasurableSet ({w} : Set (AffineChannelLaw.Word (AffineBatchDecoder.width p))) := by
        exact Set.univ_pi_singleton w ▸ MeasurableSet.univ_pi
          (fun i => measurableSet_singleton (w i))
      rw [show s = ⋃ w : s, ({(w : AffineChannelLaw.Word
        (AffineBatchDecoder.width p))} : Set (AffineChannelLaw.Word
          (AffineBatchDecoder.width p))) from by
          ext w
          simp]
      exact MeasurableSet.iUnion fun w => hsingleton w
  have hWordTop : (MeasurableSpace.pi : MeasurableSpace
      (AffineChannelLaw.Word (AffineBatchDecoder.width p))) = ⊤ := by
    simpa [CoordinatorUpMeasurability.affineWordMeasurableSpace] using hWord
  have hsum : (inferInstance : MeasurableSpace
      (AffineChannelLaw.Word (AffineBatchDecoder.width p) ⊕ PUnit.{1})) = ⊤ := by
    apply MeasurableSpace.ext
    intro s
    rw [measurableSet_sum_iff]
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨?_, trivial⟩
      change MeasurableSet[MeasurableSpace.pi] (Sum.inl ⁻¹' s)
      rw [hWordTop]
      trivial
  have hOption : (LaterAssignmentStartMeasurability.optionMeasurableSpace :
      MeasurableSpace (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))) =
        CoordinatorUpMeasurability.rawDecoderOutputMeasurableSpace
          (AffineBatchDecoder.width p) := by
    rw [CoordinatorUpMeasurability.rawDecoderOutputMeasurableSpace]
    change MeasurableSpace.comap (Equiv.optionEquivSumPUnit
      (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
      (inferInstance : MeasurableSpace
        (AffineChannelLaw.Word (AffineBatchDecoder.width p) ⊕ PUnit.{1})) = ⊤
    rw [hsum]
    apply MeasurableSpace.ext
    intro s
    rw [MeasurableSpace.measurableSet_comap]
    constructor
    · intro _
      trivial
    · intro _
      refine ⟨Equiv.optionEquivSumPUnit
        (AffineChannelLaw.Word (AffineBatchDecoder.width p)) '' s, trivial, ?_⟩
      exact Set.preimage_image_eq _ (Equiv.optionEquivSumPUnit
        (AffineChannelLaw.Word (AffineBatchDecoder.width p))).injective
  have hview := ReferenceActiveStepCompositionMeasurability.measurable_downView
      (p := p) (rate := rate)
  have hrow := ReferenceActivePhysicalStepMeasurability.measurable_row
      (p := p) (rate := rate)
  have htime := ReferenceActivePhysicalStepMeasurability.measurable_time
      (p := p) (rate := rate)
  have hfixed (i : Fin (p.m - 1)) : Measurable
      (fun z : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
          (CompletePublicTable.CompleteRow p × Fin p.T) =>
        ReferenceDownReception.expectedDownFlatWord z.1 i z.2.1 z.2.2) := by
    have h := ReferenceDownReceptionMeasurability.measurable_expectedDownFlatWord
      (p := p) (rate := rate) i
    exact hOption ▸ h
  have hall : Measurable (fun z : Fin (p.m - 1) ×
      (Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
        (CompletePublicTable.CompleteRow p × Fin p.T)) =>
      ReferenceDownReception.expectedDownFlatWord z.2.1 z.1 z.2.2.1 z.2.2.2) := by
    apply measurable_from_prod_countable_right
    intro i
    exact hfixed i
  exact hall.comp ((measurable_upSenderIndex (p := p) (rate := rate)).prodMk
    (hview.prodMk (hrow.prodMk htime)))

/-- The executed DOWN-positive test is Borel from the actual whole follower
observation and the simultaneous collision-sensitive feedback. -/
theorem measurable_downPositive :
    Measurable (fun x : RoundInput p rate =>
      ReferenceActiveAffinePositiveTest.downPositive x) := by
  let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace
      (Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let call (output : ReferenceFollowerTailComposition.FollowerObservable p rate) : Bool :=
    match output.2.2.1, output.2.2.2 with
    | .inl _, _ => false
    | .inr _, none => false
    | .inr _, some code => code.rawComparison.isSome
  have hcall : Measurable call := by
    let cut := ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate
    let e : (ReferenceFollowerTailComposition.DownInputObservable p rate ×
        Option cut) ≃ᵐ (Unit × Option cut) ⊕
          (FollowerObservationStageMeasurabilityRepair.CarriedState p rate × Option cut) :=
      MeasurableEquiv.sumProdDistrib Unit
        (FollowerObservationStageMeasurabilityRepair.CarriedState p rate) (Option cut)
    have hleft : Measurable (fun _ : Unit × Option cut => false) := measurable_const
    let : MeasurableSingletonClass cut := ⟨fun _ => by simp⟩
    let eOption : Option cut ≃ᵐ cut ⊕ PUnit := {
      toEquiv := Equiv.optionEquivSumPUnit cut
      measurable_toFun := comap_measurable _
      measurable_invFun := by
        rw [measurable_comap_iff]
        exact measurable_id
    }
    have hraw : Measurable (fun code : cut => code.rawComparison.isSome) :=
      measurable_of_countable (fun code : cut => code.rawComparison.isSome)
    have hoption : Measurable (fun value : Option cut =>
        (value.map fun code => code.rawComparison.isSome).getD false) := by
      let branches : cut ⊕ PUnit → Bool :=
        Sum.elim (fun code => code.rawComparison.isSome) (fun _ => false)
      have hbranches : Measurable branches := hraw.sumElim measurable_const
      have hfactor : (fun value : Option cut =>
          (value.map fun code => code.rawComparison.isSome).getD false) =
          fun value => branches (eOption value) := by
        funext value
        cases value <;> rfl
      rw [hfactor]
      exact hbranches.comp eOption.measurable
    have hright : Measurable (fun z :
        FollowerObservationStageMeasurabilityRepair.CarriedState p rate × Option cut =>
        (z.2.map fun code => code.rawComparison.isSome).getD false) :=
      hoption.comp measurable_snd
    let branch : (Unit × Option cut) ⊕
        (FollowerObservationStageMeasurabilityRepair.CarriedState p rate × Option cut) → Bool :=
      Sum.elim (fun _ => false)
        (fun z : FollowerObservationStageMeasurabilityRepair.CarriedState p rate × Option cut =>
          (z.2.map fun code => code.rawComparison.isSome).getD false)
    have hbranch : Measurable branch := hleft.sumElim hright
    have hfactor : call = fun output => branch (e (output.2.2.1, output.2.2.2)) := by
      funext output
      cases hin : output.2.2.1 <;> cases hcut : output.2.2.2 <;>
        simp [call, branch, e, MeasurableEquiv.sumProdDistrib,
          Equiv.sumProdDistrib, hin, hcut]
    have hprojection : Measurable (fun output :
        ReferenceFollowerTailComposition.FollowerObservable p rate =>
        (output.2.2.1, output.2.2.2)) := by
      exact (measurable_fst.prodMk measurable_snd).comp
        (measurable_snd.comp measurable_snd)
    rw [hfactor]
    exact hbranch.comp (e.measurable.comp hprojection)
  have hobsAll : Measurable (fun x : RoundInput p rate => fun i : Fin (p.m - 1) =>
      ReferenceActiveStepCompositionMeasurability.followerObservable x i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ReferenceActiveStepCompositionMeasurability.measurable_followerObservable
      (p := p) (rate := rate) i
  have hfeedbackAll : Measurable (fun x : RoundInput p rate =>
      fun i : Fin (p.m - 1) => (ReferenceActivePhysicalStep.prepare x).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_of_countable fun y : Fin (D p + 1) => y).comp
      (ReferenceActiveStepCompositionMeasurability.measurable_playerFeedback
        (p := p) (rate := rate) (PublicDiscreteDraws.followerPlayer p.two_le_m i))
  have hselectedObs := measurable_pi_eval
    (fun x i => ReferenceActiveStepCompositionMeasurability.followerObservable x i)
    ReferenceActivePhysicalStep.upSenderIndex hobsAll
    (measurable_upSenderIndex (p := p) (rate := rate))
  have hselectedFeedback := measurable_pi_eval
    (fun x i => (ReferenceActivePhysicalStep.prepare x).feedback.feedback
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    ReferenceActivePhysicalStep.upSenderIndex hfeedbackAll
    (measurable_upSenderIndex (p := p) (rate := rate))
  have hpositive : Measurable (fun x : RoundInput p rate =>
      call (ReferenceActiveStepCompositionMeasurability.followerObservable x
        (ReferenceActivePhysicalStep.upSenderIndex x)) &&
        decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p
          ((ReferenceActivePhysicalStep.prepare x).feedback.feedback
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ReferenceActivePhysicalStep.upSenderIndex x)))).val.val)) := by
    exact (measurable_of_finite fun z : Bool × Bool => z.1 && z.2).comp
      ((hcall.comp hselectedObs).prodMk
        ((measurable_of_countable (fun y : Fin (D p + 1) =>
          decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p y).val.val))).comp
            hselectedFeedback))
  have hcallEq (output : ReferenceFollowerTailComposition.FollowerObservable p rate) :
      call output = ReferenceActiveAffinePositiveTest.downDiagnosticCall
        (ReferenceFollowerTailComposition.reconstructFollowerObservable output) := by
    cases hin : output.2.2.1 <;> cases hcut : output.2.2.2 <;>
      simp [call, ReferenceActiveAffinePositiveTest.downDiagnosticCall,
        ReferenceFollowerTailComposition.reconstructFollowerObservable,
        ReferenceFollowerTailComposition.reconstructDown,
        ReferenceDownReceptionMeasurability.reconstructReferenceDownCutCode, hin, hcut]
  have heq (x : RoundInput p rate) :
      ReferenceActiveAffinePositiveTest.downPositive x =
        (call (ReferenceActiveStepCompositionMeasurability.followerObservable x
          (ReferenceActivePhysicalStep.upSenderIndex x)) &&
          decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p
            ((ReferenceActivePhysicalStep.prepare x).feedback.feedback
              (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ReferenceActivePhysicalStep.upSenderIndex x)))).val.val)) := by
    calc
      ReferenceActiveAffinePositiveTest.downPositive x =
          (ReferenceActiveAffinePositiveTest.downDiagnosticCall
              ((ReferenceActivePhysicalStep.prepare x).observeFollower
                (ReferenceActivePhysicalStep.upSenderIndex x)) &&
            decide (0 < ((ReferenceActivePhysicalStep.prepare x).feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ReferenceActivePhysicalStep.upSenderIndex x))).val.val)) :=
        ReferenceActiveAffinePositiveTest.downPositive_eq_diagnostic x
      _ = (call (ReferenceActiveStepCompositionMeasurability.followerObservable x
            (ReferenceActivePhysicalStep.upSenderIndex x)) &&
          decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p
            ((ReferenceActivePhysicalStep.prepare x).feedback.feedback
              (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ReferenceActivePhysicalStep.upSenderIndex x)))).val.val)) := by
        rw [← ReferenceActiveStepCompositionMeasurability.followerObservable_reconstruct x
          (ReferenceActivePhysicalStep.upSenderIndex x)]
        rw [hcallEq]
        rw [(ReferenceActivePhysicalStep.prepare x).feedback.observations_eq
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ReferenceActivePhysicalStep.upSenderIndex x))]
  rw [show (fun x : RoundInput p rate => ReferenceActiveAffinePositiveTest.downPositive x) =
      fun x => (call (ReferenceActiveStepCompositionMeasurability.followerObservable x
          (ReferenceActivePhysicalStep.upSenderIndex x)) &&
        decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p
          ((ReferenceActivePhysicalStep.prepare x).feedback.feedback
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ReferenceActivePhysicalStep.upSenderIndex x)))).val.val)) from funext heq]
  exact hpositive

/-- The positive UP call is Borel from the retained actual UP diagnostic. The
complete collection code preserves the receiver's true input and also records
invalid/no-call results as `none`. -/
private def upPositiveFromDiagnosticCode
    (diagnostic : Option
      (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate)) : Bool := by
  classical
  exact match diagnostic with
  | none => false
  | some code => decide (AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput code.input))

private def collectionTailUpDiagnostic
    (code : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate) :=
  code.2.2.2.2

private theorem upPositive_decodeCollectionTail
    (code : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate) :
    ReferenceActiveAffinePositiveTest.upDiagnosticPositive
        (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation code).up =
      upPositiveFromDiagnosticCode (collectionTailUpDiagnostic code) := by
  classical
  cases hdiag : code.2.2.2.2 <;>
    simp [upPositiveFromDiagnosticCode, collectionTailUpDiagnostic,
      ReferenceActiveAffinePositiveTest.upDiagnosticPositive,
      ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation,
      ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic, hdiag]

/-- The executed UP-positive test is Borel even when a later coordinator
operation fails: the full diagnostic is retained independently of the successor. -/
theorem measurable_upPositive :
    Measurable (fun x : RoundInput p rate =>
      ReferenceActiveAffinePositiveTest.upPositive x) := by
  let : MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  let : MeasurableSpace
      (Option (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate)) :=
    LaterAssignmentStartMeasurability.optionMeasurableSpace
  have hwhole := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode
      (p := p) (rate := rate)
  have hphysical : Measurable (fun x : RoundInput p rate =>
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1) :=
    measurable_fst.comp hwhole
  have htail : Measurable (fun x : RoundInput p rate =>
      (ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2) := by
    exact measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp hphysical)))
  have hdiagnostic : Measurable (fun x : RoundInput p rate =>
      collectionTailUpDiagnostic
        ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2)) := by
    exact ((measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id)))).comp htail)
  have hresult : Measurable (fun x : RoundInput p rate =>
      upPositiveFromDiagnosticCode
        (collectionTailUpDiagnostic
          ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2))) := by
    exact (measurable_of_countable upPositiveFromDiagnosticCode).comp hdiagnostic
  have heq (x : RoundInput p rate) :
      ReferenceActiveAffinePositiveTest.upPositive x =
        upPositiveFromDiagnosticCode
          (collectionTailUpDiagnostic
            ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2)) := by
    have hdecode := (ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs x).1
    unfold ReferenceActiveAffinePositiveTest.upPositive
    rw [← hdecode]
    exact upPositive_decodeCollectionTail
      ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2)
  rw [show (fun x : RoundInput p rate => ReferenceActiveAffinePositiveTest.upPositive x) =
      fun x => upPositiveFromDiagnosticCode
        (collectionTailUpDiagnostic
          ((ReferenceActiveStepCompositionMeasurability.wholeStepCode x).1.2.2.2.2)) from
      funext heq]
  exact hresult

private theorem measurable_upSent :
    Measurable (fun x : RoundInput p rate => ReferenceActiveAffinePositiveTest.upSent x) := by
  have hmap : Measurable
      (ReferenceCollectionServiceTailMeasurability.collectionExpectedMap rate
        (fun x : RoundInput p rate => x)) :=
    ReferenceCollectionServiceTailMeasurability.measurable_collectionExpectedMap
      (p := p) (round := fun x : RoundInput p rate => x) measurable_id
  have heq : (fun x : RoundInput p rate =>
      ReferenceCollectionServiceTailMeasurability.collectionExpectedMap rate
        (fun y : RoundInput p rate => y) x) =
      fun x => ReferenceActiveAffinePositiveTest.upSent x := by
    funext x
    change ReferenceCollectionServiceTailMeasurability.collectionExpectedMap rate
        (fun _ : Unit => x) () =
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)
    have hprepared := ReferenceCollectionServiceTailMeasurability.selectedUpPrepared_reconstruct x
    exact congrArg (fun sender : DeclaredFollowerLocalRound.PreparedRound p rate =>
      ReferenceUpReception.currentOfferWord rate sender.row sender.follower sender.time
        sender rfl rfl rfl) hprepared
  exact heq ▸ hmap

private theorem measurable_sourcePair (q : Fin (M p)) (t : Fin p.T)
    (c : ContinuousLearningRows.Channel p) :
    Measurable (fun source : SourceInput p => ((source.1.2 q).2 t).2 c) := by
  have h := measurable_fst.comp
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).measurable
  convert h using 1
  funext source
  exact (ReferenceSelectedAffinePairLaw.fixedPairSplit_pair p q t c source).symm

private def referencePairSample : Pair p := (fun _ => 0, 0)

/-- On the actual selected-channel remainder stratum, replacing the extracted
original pair changes the injected fixed-boundary input exactly as the
physical pair replacement does. -/
private theorem roundInputAtPairSplit_eq_replaceCurrentPair
    (boundary : RoundInput p rate) (q : Fin (M p)) (d : Fin 2)
    (i : Fin (p.m - 1)) (a₀ a : Pair p)
    (r : Remainder p q boundary.time (d, i))
    (hr : r ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent
      p q boundary.time (d, i)) :
    roundInputAtOriginalSource boundary
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time (d, i)).symm (a, r)) =
      ReferenceActiveAffinePositiveTest.replaceCurrentPair
        (roundInputAtOriginalSource boundary
          ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time (d, i)).symm (a₀, r)))
        d a := by
  let iChannel : Fin (ContinuousLearningRows.d p) :=
    ⟨i.val, by simpa only [ContinuousLearningRows.d] using i.isLt⟩
  let c : ContinuousLearningRows.Channel p := (d, iChannel)
  change Remainder p q boundary.time c at r
  change r ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent
    p q boundary.time c at hr
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time c
  let source₀ := split.symm (a₀, r)
  let source := split.symm (a, r)
  rcases ReferenceSelectedAffinePairLaw.fixedPairSplit_inverse_coordinates
      p q boundary.time c a₀ r with
    ⟨hpair₀, _, hprivate₀, hforward₀, hslice₀, hchannels₀, htimes₀, hrows₀⟩
  rcases ReferenceSelectedAffinePairLaw.fixedPairSplit_inverse_coordinates
      p q boundary.time c a r with
    ⟨hpair, _, hprivate, hforward, hslice, hchannels, htimes, hrows⟩
  have hselected₀ : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀ = q := by
    change PrivateSourceStreams.coordinatorIndex p source₀.2.1.2 = q
    rw [hprivate₀]
    exact hr.1
  have hselected : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q := by
    change PrivateSourceStreams.coordinatorIndex p source.2.1.2 = q
    rw [hprivate]
    exact hr.1
  have hdrawR : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      r.1.2.1.2.1.1 = i := by
    have hchannel := hr.2
    by_cases hdown : PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1 =
        PublicDiscreteDraws.downSlot
    · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hdown] at hchannel
      have h := Option.some.inj hchannel
      exact congrArg Prod.snd h
    · by_cases hup : PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1 =
          PublicDiscreteDraws.upSlot
      · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hup] at hchannel
        have h := Option.some.inj hchannel
        exact congrArg Prod.snd h
      · have hdata : PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1 =
            PublicDiscreteDraws.dataSlot := by
          have hbound : (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).val < 3 :=
            (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).isLt
          have hdownVal : (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).val ≠ 1 := by
            intro hv
            apply hdown
            exact Fin.ext hv
          have hupVal : (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).val ≠ 2 := by
            intro hv
            apply hup
            exact Fin.ext hv
          apply Fin.ext
          simp only [PublicDiscreteDraws.dataSlot]
          omega
        rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_data p _ hdata] at hchannel
        cases hchannel
  have hindex : ReferenceActivePhysicalStep.upSenderIndex
      (roundInputAtOriginalSource boundary source₀) = iChannel := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((source₀.1.2
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
        boundary.time).1 = iChannel
    rw [hselected₀, hslice₀]
    apply Fin.ext
    change (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      r.1.2.1.2.1.1).val = i.val
    exact congrArg Fin.val hdrawR
  have hrows : source.1.2 = Function.update source₀.1.2 q
      ((source₀.1.2 q).1,
        Function.update (source₀.1.2 q).2 boundary.time
          (((source₀.1.2 q).2 boundary.time).1,
            Function.update ((source₀.1.2 q).2 boundary.time).2 c a)) := by
    funext j
    by_cases hj : j = q
    · subst j
      simp only [Function.update_self]
      apply Prod.ext
      · exact hforward.trans hforward₀.symm
      · funext t'
        by_cases ht : t' = boundary.time
        · subst t'
          simp only [Function.update_self]
          apply Prod.ext
          · exact hslice.trans hslice₀.symm
          · funext channel
            by_cases hc : channel = c
            · subst channel
              simp only [Function.update_self]
              exact hpair
            ·
              let other : ReferenceSelectedAffinePairLaw.Other c := ⟨channel, hc⟩
              simp only [Function.update_of_ne hc]
              exact (hchannels other).trans (hchannels₀ other).symm
        · simp only [Function.update_of_ne ht]
          let other : ReferenceSelectedAffinePairLaw.Other boundary.time := ⟨t', ht⟩
          exact (htimes other).trans (htimes₀ other).symm
    · simp only [Function.update_of_ne hj]
      let other : ReferenceSelectedAffinePairLaw.Other q := ⟨j, hj⟩
      exact (hrows other).trans (hrows₀ other).symm
  have input_ext (left right : RoundInput p rate)
      (hs : left.state = right.state) (hr : left.rows = right.rows)
      (hj : left.selected = right.selected) (ht : left.time = right.time)
      (hw : left.rewards = right.rewards) : left = right := by
    rcases left with ⟨state, table, j, time, active, reward⟩
    rcases right with ⟨otherState, otherTable, otherJ, otherTime, otherActive, otherReward⟩
    dsimp only at hs hr hj ht hw
    cases hs
    cases hr
    cases hj
    cases ht
    cases hw
    rfl
  apply input_ext
  · rfl
  · change source.1.2 = Function.update source₀.1.2
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)
      ((source₀.1.2
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).1,
        Function.update (source₀.1.2
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
          boundary.time
          (((source₀.1.2
              (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
              boundary.time).1,
            Function.update ((source₀.1.2
                (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
                boundary.time).2
              (d, ReferenceActivePhysicalStep.upSenderIndex
                (roundInputAtOriginalSource boundary source₀)) a))
    have hchannelIndex :
        (d, ReferenceActivePhysicalStep.upSenderIndex
          (roundInputAtOriginalSource boundary source₀)) = c := by
      apply Prod.ext
      · rfl
      exact hindex
    have hrows' := hrows
    rw [← hchannelIndex] at hrows'
    rw [hselected₀]
    exact hrows'
  · change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source =
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀
    rw [hselected, hselected₀]
  · rfl
  · rfl

/-- Borel measurability of the literal original-source DOWN event, with the
remainder cylinder kept as an explicit parameter. -/
theorem measurableSet_downPositiveSourceEvent (boundary : RoundInput p rate)
    (q : Fin (M p)) (i : Fin (p.m - 1))
    (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (0, i))) (hC : MeasurableSet C) :
    MeasurableSet (downPositiveSourceEvent boundary q i candidate C) := by
  let input := roundInputAtOriginalSource boundary
  have hinput : Measurable input := measurable_roundInputAtOriginalSource boundary
  have hpositive : Measurable (fun source : SourceInput p =>
      ReferenceActiveAffinePositiveTest.downPositive (input source)) :=
    measurable_downPositive.comp hinput
  have hsent : Measurable (fun source : SourceInput p =>
      ReferenceActiveAffinePositiveTest.downSent (input source)) :=
    measurable_downSent.comp hinput
  have hstratum := ReferenceSelectedAffinePairLaw.measurableSet_stratumEvent
    p q boundary.time (0, i) C hC
  have hsentNe : MeasurableSet {source : SourceInput p |
      ReferenceActiveAffinePositiveTest.downSent (input source) ≠ some candidate} := by
    have h := (hsent (measurableSet_singleton (some candidate))).compl
    have hset : {source : SourceInput p |
        ReferenceActiveAffinePositiveTest.downSent (input source) ≠ some candidate} =
        (fun source => ReferenceActiveAffinePositiveTest.downSent (input source)) ⁻¹'
          ({some candidate}ᶜ) := by
      ext source
      simp
    rw [hset]
    exact h
  change MeasurableSet
    (ReferenceSelectedAffinePairLaw.stratumEvent p q boundary.time (0, i) C ∩
      ({source | ReferenceActiveAffinePositiveTest.downPositive (input source) = true} ∩
        {source | ReferenceActiveAffinePositiveTest.downSent (input source) ≠ some candidate}))
  exact hstratum.inter ((hpositive (measurableSet_singleton true)).inter hsentNe)

/-- Borel measurability of the DOWN hash-one event on the original source. -/
theorem measurableSet_downPositiveHashOneSourceEvent (boundary : RoundInput p rate)
    (q : Fin (M p)) (i : Fin (p.m - 1))
    (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (0, i))) (hC : MeasurableSet C) :
    MeasurableSet (downPositiveHashOneSourceEvent boundary q i candidate C) := by
  have hbase := measurableSet_downPositiveSourceEvent boundary q i candidate C hC
  have hhash : Measurable (fun source : SourceInput p =>
      AffineChannelLaw.affineHash (((source.1.2 q).2 boundary.time).2 (0, i)) candidate) := by
    exact (measurable_of_finite fun a : Pair p =>
      AffineChannelLaw.affineHash a candidate).comp
        (measurable_sourcePair q boundary.time (0, i))
  have hbit := hhash (measurableSet_singleton (1 : AffineChannelLaw.Bit))
  change MeasurableSet (downPositiveSourceEvent boundary q i candidate C ∩
    {source | AffineChannelLaw.affineHash
      (((source.1.2 q).2 boundary.time).2 (0, i)) candidate = 1})
  exact hbase.inter hbit

/-- Borel measurability of the literal original-source UP event, with the
remainder cylinder kept as an explicit parameter. -/
theorem measurableSet_upPositiveSourceEvent (boundary : RoundInput p rate)
    (q : Fin (M p)) (i : Fin (p.m - 1))
    (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (1, i))) (hC : MeasurableSet C) :
    MeasurableSet (upPositiveSourceEvent boundary q i candidate C) := by
  let input := roundInputAtOriginalSource boundary
  have hinput : Measurable input := measurable_roundInputAtOriginalSource boundary
  have hpositive : Measurable (fun source : SourceInput p =>
      ReferenceActiveAffinePositiveTest.upPositive (input source)) :=
    measurable_upPositive.comp hinput
  have hsent : Measurable (fun source : SourceInput p =>
      ReferenceActiveAffinePositiveTest.upSent (input source)) := by
    exact measurable_upSent.comp hinput
  have hstratum := ReferenceSelectedAffinePairLaw.measurableSet_stratumEvent
    p q boundary.time (1, i) C hC
  have hsentNe : MeasurableSet {source : SourceInput p |
      ReferenceActiveAffinePositiveTest.upSent (input source) ≠ some candidate} := by
    have h := (hsent (measurableSet_singleton (some candidate))).compl
    have hset : {source : SourceInput p |
        ReferenceActiveAffinePositiveTest.upSent (input source) ≠ some candidate} =
        (fun source => ReferenceActiveAffinePositiveTest.upSent (input source)) ⁻¹'
          ({some candidate}ᶜ) := by
      ext source
      simp
    rw [hset]
    exact h
  change MeasurableSet
    (ReferenceSelectedAffinePairLaw.stratumEvent p q boundary.time (1, i) C ∩
      ({source | ReferenceActiveAffinePositiveTest.upPositive (input source) = true} ∩
        {source | ReferenceActiveAffinePositiveTest.upSent (input source) ≠ some candidate}))
  exact hstratum.inter ((hpositive (measurableSet_singleton true)).inter hsentNe)

/-- Borel measurability of the UP hash-one event on the original source. -/
theorem measurableSet_upPositiveHashOneSourceEvent (boundary : RoundInput p rate)
    (q : Fin (M p)) (i : Fin (p.m - 1))
    (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (1, i))) (hC : MeasurableSet C) :
    MeasurableSet (upPositiveHashOneSourceEvent boundary q i candidate C) := by
  have hbase := measurableSet_upPositiveSourceEvent boundary q i candidate C hC
  have hhash : Measurable (fun source : SourceInput p =>
      AffineChannelLaw.affineHash (((source.1.2 q).2 boundary.time).2 (1, i)) candidate) := by
    exact (measurable_of_finite fun a : Pair p =>
      AffineChannelLaw.affineHash a candidate).comp
        (measurable_sourcePair q boundary.time (1, i))
  have hbit := hhash (measurableSet_singleton (1 : AffineChannelLaw.Bit))
  change MeasurableSet (upPositiveSourceEvent boundary q i candidate C ∩
    {source | AffineChannelLaw.affineHash
      (((source.1.2 q).2 boundary.time).2 (1, i)) candidate = 1})
  exact hbase.inter hbit

private theorem lintegral_affineSample_indicator
    (P : Pair p → Prop) :
    ∫⁻ a, AdaptiveAffineBatchTail.indicator (P a) ∂
        (AffineChannelLaw.jointLaw (B p)).toMeasure =
      ∑ a : Pair p, AffineChannelLaw.jointLaw (B p) a *
        AdaptiveAffineBatchTail.indicator (P a) := by
  classical
  rw [MeasureTheory.lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a ha
  rw [PMF.toMeasure_apply_singleton (AffineChannelLaw.jointLaw (B p)) a
    (measurableSet_singleton a)]
  ac_rfl

/-- The original source law at a fixed boundary follows by splitting the one
reserved pair, applying the actual physical one-step law on each actual
selected-channel remainder fiber, and integrating the genuine retained law. -/
private theorem originalSource_direction_hash_half
    (boundary : RoundInput p rate) (q : Fin (M p)) (direction : Fin 2)
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (direction, i))) (hC : MeasurableSet C) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (directionPositiveHashOneSourceEvent boundary q direction i candidate C) =
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (directionPositiveSourceEvent boundary q direction i candidate C) := by
  classical
  have hBaseSourceMeas : MeasurableSet
      (directionPositiveSourceEvent boundary q direction i candidate C) := by
    fin_cases direction
    · change MeasurableSet (downPositiveSourceEvent boundary q i candidate C)
      exact measurableSet_downPositiveSourceEvent boundary q i candidate C hC
    · change MeasurableSet (upPositiveSourceEvent boundary q i candidate C)
      exact measurableSet_upPositiveSourceEvent boundary q i candidate C hC
  have hHashSourceMeas : MeasurableSet
      (directionPositiveHashOneSourceEvent boundary q direction i candidate C) := by
    fin_cases direction
    · change MeasurableSet (downPositiveHashOneSourceEvent boundary q i candidate C)
      exact measurableSet_downPositiveHashOneSourceEvent boundary q i candidate C hC
    · change MeasurableSet (upPositiveHashOneSourceEvent boundary q i candidate C)
      exact measurableSet_upPositiveHashOneSourceEvent boundary q i candidate C hC
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time (direction, i)
  let pairMeasure := (AffineChannelLaw.jointLaw (B p)).toMeasure
  let retainedMeasure := ReferenceSelectedAffinePairLaw.remainderLaw p q boundary.time (direction, i)
  let productMeasure := pairMeasure.prod retainedMeasure
  let selectedRemainder : Set (Remainder p q boundary.time (direction, i)) :=
    ReferenceSelectedAffinePairLaw.remainderSelectorEvent p q boundary.time (direction, i) ∩ C
  let referenceInput (r : Remainder p q boundary.time (direction, i)) :=
    roundInputAtOriginalSource boundary (split.symm (referencePairSample, r))
  let fiberBase : Set (Pair p × Remainder p q boundary.time (direction, i)) :=
    {z | z.2 ∈ selectedRemainder ∧
      directionPositive direction
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair
          (referenceInput z.2) direction z.1) = true ∧
      directionSent direction (referenceInput z.2) ≠ some candidate}
  let fiberHash : Set (Pair p × Remainder p q boundary.time (direction, i)) :=
    fiberBase ∩ {z | AffineChannelLaw.affineHash z.1 candidate = 1}
  have hselectorRemainder (a : Pair p) (r : Remainder p q boundary.time (direction, i)) :
      split.symm (a, r) ∈ ReferenceSelectedAffinePairLaw.stratumEvent
          p q boundary.time (direction, i) C ↔ r ∈ selectedRemainder := by
    have hselector := ReferenceSelectedAffinePairLaw.selector_remainder_iff
      p q boundary.time (direction, i) (split.symm (a, r))
    constructor
    · intro h
      change ReferenceSelectedAffinePairLaw.selector p boundary.time (split.symm (a, r)) =
          (q, some (direction, i)) ∧
        (ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time (direction, i)
          (split.symm (a, r))).2 ∈ C at h
      have hsel := hselector.mp h.1
      refine ⟨?_, ?_⟩
      · simpa [split] using hsel
      · simpa [split] using h.2
    · intro hr
      change ReferenceSelectedAffinePairLaw.selector p boundary.time (split.symm (a, r)) =
          (q, some (direction, i)) ∧
        (ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time (direction, i)
          (split.symm (a, r))).2 ∈ C
      refine ⟨hselector.mpr ?_, ?_⟩
      · simpa [split] using hr.1
      · simpa [split] using hr.2
  have hsentReplace (x : RoundInput p rate) (sample : Pair p) :
      directionSent direction
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x direction sample) =
        directionSent direction x := by
    fin_cases direction
    · simpa [directionSent] using
        ReferenceAffineDispatchPairInvariance.downSent_replace x 0 sample
    · simpa [directionSent] using
        ReferenceActiveAffinePositiveTest.upSent_replace x 1 sample
  have hsourceBase (a : Pair p) (r : Remainder p q boundary.time (direction, i)) :
      split.symm (a, r) ∈ directionPositiveSourceEvent boundary q direction i candidate C ↔
        (a, r) ∈ fiberBase := by
    have hstratumIff := hselectorRemainder a r
    change (split.symm (a, r) ∈
        ReferenceSelectedAffinePairLaw.stratumEvent p q boundary.time (direction, i) C ∧
      directionPositive direction (roundInputAtOriginalSource boundary
        (split.symm (a, r))) = true ∧
      directionSent direction (roundInputAtOriginalSource boundary
        (split.symm (a, r))) ≠ some candidate) ↔
        (a, r) ∈ fiberBase
    constructor
    · rintro ⟨hstratumMem, hpositive, hsent⟩
      have hr := hstratumIff.mp hstratumMem
      have hreplace : roundInputAtOriginalSource boundary (split.symm (a, r)) =
          ReferenceActiveAffinePositiveTest.replaceCurrentPair
            (referenceInput r) direction a := by
        simpa [split] using roundInputAtPairSplit_eq_replaceCurrentPair
          boundary q direction i referencePairSample a r hr.1
      rw [hreplace] at hpositive hsent
      rw [hsentReplace] at hsent
      exact ⟨hr, hpositive, hsent⟩
    · intro h
      change r ∈ selectedRemainder ∧
        directionPositive direction
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair
            (referenceInput r) direction a) = true ∧
        directionSent direction (referenceInput r) ≠ some candidate at h
      have hreplace : roundInputAtOriginalSource boundary (split.symm (a, r)) =
          ReferenceActiveAffinePositiveTest.replaceCurrentPair
            (referenceInput r) direction a := by
        simpa [split] using roundInputAtPairSplit_eq_replaceCurrentPair
          boundary q direction i referencePairSample a r h.1.1
      rcases h with ⟨hr, hpositive, hsent⟩
      refine ⟨hstratumIff.mpr hr, ?_, ?_⟩
      · rw [hreplace]
        exact hpositive
      · rw [hreplace, hsentReplace]
        exact hsent
  have hsourceHash (a : Pair p) (r : Remainder p q boundary.time (direction, i)) :
      split.symm (a, r) ∈ directionPositiveHashOneSourceEvent
          boundary q direction i candidate C ↔ (a, r) ∈ fiberHash := by
    have hpair := ReferenceSelectedAffinePairLaw.fixedPairSplit_pair
      p q boundary.time (direction, i) (split.symm (a, r))
    rw [split.apply_symm_apply] at hpair
    have hpair' : (((split.symm (a, r)).1.2 q).2 boundary.time).2
        (direction, i) = a := hpair.symm
    change (split.symm (a, r) ∈ directionPositiveSourceEvent
          boundary q direction i candidate C ∧
      AffineChannelLaw.affineHash
        ((((split.symm (a, r)).1.2 q).2 boundary.time).2
          (direction, i)) candidate = 1) ↔
      (a, r) ∈ fiberHash
    rw [hsourceBase, hpair']
    rfl
  have hBasePreimage : split.symm ⁻¹'
        directionPositiveSourceEvent boundary q direction i candidate C = fiberBase := by
    ext z
    rcases z with ⟨a, r⟩
    exact hsourceBase a r
  have hHashPreimage : split.symm ⁻¹'
        directionPositiveHashOneSourceEvent boundary q direction i candidate C = fiberHash := by
    ext z
    rcases z with ⟨a, r⟩
    exact hsourceHash a r
  have hFiberBaseMeas : MeasurableSet fiberBase := by
    rw [← hBasePreimage]
    exact hBaseSourceMeas.preimage split.symm.measurable
  have hFiberHashMeas : MeasurableSet fiberHash := by
    rw [← hHashPreimage]
    exact hHashSourceMeas.preimage split.symm.measurable
  have hBaseIntegrand : Measurable (fiberBase.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hFiberBaseMeas
  have hHashIntegrand : Measurable (fiberHash.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hFiberHashMeas
  have hOneStep (x : RoundInput p rate) :
      (∑ sample : Pair p, AffineChannelLaw.jointLaw (B p) sample *
        AdaptiveAffineBatchTail.indicator
          (directionPositive direction
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair x direction sample) = true ∧
            directionSent direction x ≠ some candidate ∧
            AffineChannelLaw.affineHash sample candidate = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ sample : Pair p,
        AffineChannelLaw.jointLaw (B p) sample * AdaptiveAffineBatchTail.indicator
          (directionPositive direction
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair x direction sample) = true ∧
            directionSent direction x ≠ some candidate) := by
    fin_cases direction
    · exact ReferenceDownPhysicalHashRule.down_jointLaw_hash_half x candidate
    · exact ReferenceUpPhysicalHashRule.upPositive_one_step_half x candidate
  have hFiberHalf (r : Remainder p q boundary.time (direction, i)) :
      ∫⁻ sample, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r) ∂pairMeasure =
        ((1 : ℝ≥0∞) / 2) *
          ∫⁻ sample, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r) ∂pairMeasure := by
    have hhashConvert :
        (fun sample : Pair p => fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r)) =
          fun sample => AdaptiveAffineBatchTail.indicator ((sample, r) ∈ fiberHash) := by
      funext sample
      simp [Set.indicator, AdaptiveAffineBatchTail.indicator]
    have hbaseConvert :
        (fun sample : Pair p => fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r)) =
          fun sample => AdaptiveAffineBatchTail.indicator ((sample, r) ∈ fiberBase) := by
      funext sample
      simp [Set.indicator, AdaptiveAffineBatchTail.indicator]
    rw [hhashConvert, hbaseConvert,
      lintegral_affineSample_indicator (fun sample => (sample, r) ∈ fiberHash),
      lintegral_affineSample_indicator (fun sample => (sample, r) ∈ fiberBase)]
    by_cases hrSelector : r ∈
        ReferenceSelectedAffinePairLaw.remainderSelectorEvent
          p q boundary.time (direction, i)
    · by_cases hrCylinder : r ∈ C
      · simpa [fiberHash, fiberBase, selectedRemainder, hrSelector, hrCylinder,
          AdaptiveAffineBatchTail.indicator, and_assoc] using hOneStep (referenceInput r)
      · simp [fiberHash, fiberBase, selectedRemainder, hrSelector, hrCylinder,
          AdaptiveAffineBatchTail.indicator]
    · simp [fiberHash, fiberBase, selectedRemainder, hrSelector,
        AdaptiveAffineBatchTail.indicator]
  have hBaseInnerMeas : Measurable (fun r =>
      ∫⁻ sample, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r) ∂pairMeasure) := by
    exact (measurable_swap_iff.mpr hBaseIntegrand).lintegral_prod_right'
  have hProductIdentity :
      ∫⁻ z, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure =
        ((1 : ℝ≥0∞) / 2) *
          ∫⁻ z, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
    calc
      ∫⁻ z, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure =
          ∫⁻ r, ∫⁻ sample, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r)
            ∂pairMeasure ∂retainedMeasure :=
        MeasureTheory.lintegral_prod_symm' _ hHashIntegrand
      _ = ∫⁻ r, ((1 : ℝ≥0∞) / 2) *
            ∫⁻ sample, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r)
              ∂pairMeasure ∂retainedMeasure := by
        apply MeasureTheory.lintegral_congr
        exact hFiberHalf
      _ = ((1 : ℝ≥0∞) / 2) *
            ∫⁻ r, ∫⁻ sample, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) (sample, r)
              ∂pairMeasure ∂retainedMeasure :=
        MeasureTheory.lintegral_const_mul _ hBaseInnerMeas
      _ = ((1 : ℝ≥0∞) / 2) *
            ∫⁻ z, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
        rw [← MeasureTheory.lintegral_prod_symm' _ hBaseIntegrand]
  have hMeasureHash :
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (directionPositiveHashOneSourceEvent boundary q direction i candidate C) =
        ∫⁻ z, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
    calc
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (directionPositiveHashOneSourceEvent boundary q direction i candidate C) =
          ((AffineChannelLaw.jointLaw (B p)).toMeasure.prod retainedMeasure)
            (split.symm ⁻¹' directionPositiveHashOneSourceEvent
              boundary q direction i candidate C) := by
        rw [← (ReferenceSelectedAffinePairLaw.fixedPairSplit_measurePreserving_symm
          p q boundary.time (direction, i)).map_eq,
          Measure.map_apply split.symm.measurable hHashSourceMeas]
      _ = productMeasure fiberHash := by rw [hHashPreimage]
      _ = ∫⁻ z, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure :=
        (MeasureTheory.lintegral_indicator_one hFiberHashMeas).symm
  have hMeasureBase :
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (directionPositiveSourceEvent boundary q direction i candidate C) =
        ∫⁻ z, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
    calc
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (directionPositiveSourceEvent boundary q direction i candidate C) =
          ((AffineChannelLaw.jointLaw (B p)).toMeasure.prod retainedMeasure)
            (split.symm ⁻¹' directionPositiveSourceEvent
              boundary q direction i candidate C) := by
        rw [← (ReferenceSelectedAffinePairLaw.fixedPairSplit_measurePreserving_symm
          p q boundary.time (direction, i)).map_eq,
          Measure.map_apply split.symm.measurable hBaseSourceMeas]
      _ = productMeasure fiberBase := by rw [hBasePreimage]
      _ = ∫⁻ z, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure :=
        (MeasureTheory.lintegral_indicator_one hFiberBaseMeas).symm
  calc
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (directionPositiveHashOneSourceEvent boundary q direction i candidate C) =
        ∫⁻ z, fiberHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := hMeasureHash
    _ = ((1 : ℝ≥0∞) / 2) *
          ∫⁻ z, fiberBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := hProductIdentity
    _ = ((1 : ℝ≥0∞) / 2) *
          BootstrapPrivateRoundStreams.sourceInputLaw p
            (directionPositiveSourceEvent boundary q direction i candidate C) := by
      rw [hMeasureBase]

/-- Original-source fixed-boundary DOWN affine hash-half identity. -/
theorem downPositiveSource_hash_half (boundary : RoundInput p rate) (q : Fin (M p))
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (0, i))) (hC : MeasurableSet C) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (downPositiveHashOneSourceEvent boundary q i candidate C) =
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (downPositiveSourceEvent boundary q i candidate C) := by
  simpa [directionPositiveHashOneSourceEvent, directionPositiveSourceEvent,
    directionPositive, directionSent, downPositiveHashOneSourceEvent,
    downPositiveSourceEvent] using
      originalSource_direction_hash_half boundary q 0 i candidate C hC

/-- Original-source fixed-boundary UP affine hash-half identity. -/
theorem upPositiveSource_hash_half (boundary : RoundInput p rate) (q : Fin (M p))
    (i : Fin (p.m - 1)) (candidate : Word (AffineBatchDecoder.width p))
    (C : Set (Remainder p q boundary.time (1, i))) (hC : MeasurableSet C) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (upPositiveHashOneSourceEvent boundary q i candidate C) =
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (upPositiveSourceEvent boundary q i candidate C) := by
  simpa [directionPositiveHashOneSourceEvent, directionPositiveSourceEvent,
    directionPositive, directionSent, upPositiveHashOneSourceEvent,
    upPositiveSourceEvent] using
      originalSource_direction_hash_half boundary q 1 i candidate C hC

end Bandits.Support.ReferenceSourceAffineHashHalf

end
