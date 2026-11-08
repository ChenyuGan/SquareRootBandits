/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveRecordingSourceBranch

/-!
# Borel events for the retained first-live recording branch

The sets in this module are the literal continuing-recording predicates on
the original retained source fibre. Their Borel proofs read the actual
generated prefix and canonical PREPARE observations. The whole-step export
keeps the existing round input and all of its continuous coordinates.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:376-408`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

These are internal Borel producers. They establish no source law,
integration, first-launch recording law, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLaunchNumericalCell
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceActiveStepCompositionMeasurability
open Bandits.Support.ReferenceFirstLiveCoordinatorStepMeasurability
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceFirstLiveRecordingSourceBranch

-- Match the canonical whole-step composer on its countable clock and option
-- skeletons. The continuous input coordinates retain their inherited spaces.
namespace Bandits.Support.ReferenceFirstLiveRecordingBranchMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
variable {p : Parameters}

local instance (priority := 3000) optionCountableMeasurableSpace
    {α : Type*} [Countable α] : MeasurableSpace (Option α) := ⊤

local instance (priority := 4000) roundFailureOptionMeasurableSpace :
    MeasurableSpace (Option DeclaredFollowerLocalRound.RoundFailure) := ⊤

local instance coordinatorFailureOptionMeasurableSpace :
    MeasurableSpace (Option ReferenceActivePhysicalStep.CoordinatorFailure) := ⊤

private theorem laterOptionSpace_eq_top {α : Type*} (mα : MeasurableSpace α)
    (hα : mα = ⊤) :
    @LaterAssignmentStartMeasurability.optionMeasurableSpace α mα = ⊤ := by
  subst mα
  let : MeasurableSpace α := ⊤
  let e := Equiv.optionEquivSumPUnit α
  have hsum : (inferInstance : MeasurableSpace (α ⊕ PUnit)) = ⊤ := by
    ext s
    rw [measurableSet_sum_iff]
    simp
  have hcomap : (MeasurableSpace.comap e
      (⊤ : MeasurableSpace (α ⊕ PUnit))) = ⊤ := by
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

local instance : MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance : MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤

abbrev X (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :=
  RetainedBranch rate rewards C_star C_h q t s hs control0

/-- The actual incoming boundary identity on the retained source fibre. -/
theorem actualCurrentInput_eq_retainedIncomingBoundary
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : X rate rewards C_star C_h q t s hs control0) :
    actualCurrentInput rate rewards C_star C_h q t s hs control0 x =
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x :=
  ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x

/-- Replacing the entire current control uses the generated next input from
the same original source split. -/
theorem actualCurrentInput_control_eq_retainedGeneratedNextInput
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 u : TimeControl p)
    (x : X rate rewards C_star C_h q t s hs control0) :
    ReferenceContinuingLiveSlicePreparation.inputAtControl
        (actualCurrentInput rate rewards C_star C_h q t s hs control0 x) u =
      ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
        rate rewards C_star C_h q t s hs control0 x u :=
  ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_control_eq_retainedGeneratedNextInput
    rate rewards C_star C_h q t s hs control0 u x

/-- The existing physical input after replacing its whole current control. -/
def currentInputAtControl
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    ReferenceActivePhysicalStep.RoundInput p rate :=
  ReferenceContinuingLiveSlicePreparation.inputAtControl
    (actualCurrentInput rate rewards C_star C_h q t s hs control0 xu.1) xu.2

private theorem measurable_inputAtControl_roundInput
    (rate : RateInput p) :
    Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      ReferenceContinuingLiveSlicePreparation.inputAtControl xu.1 xu.2) := by
  let rowInput := fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
    xu.1.row.2
  have hrowInput : Measurable rowInput :=
    (measurable_snd.comp measurable_row).comp measurable_fst
  have htime : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      xu.1.time) := measurable_time.comp measurable_fst
  have hrowControl : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      Function.update (rowInput xu) xu.1.time xu.2) := by
    have hfixed : Measurable (fun z :
        (ContinuousLearningRows.LearningRow p × TimeControl p) × Fin p.T =>
          Function.update z.1.1 z.2 z.1.2) := by
      apply measurable_from_prod_countable_left
      intro j
      exact (measurable_update' (a := j)).comp measurable_id
    have hcode : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
        ((rowInput xu, xu.2), xu.1.time)) :=
      (hrowInput.prodMk measurable_snd).prodMk htime
    convert hfixed.comp hcode using 1
    funext xu
    rfl
  have hforward : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      xu.1.row.1) := (measurable_fst.comp measurable_row).comp measurable_fst
  have hrowAtControl : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      ReferenceContinuingLiveSlicePreparation.rowAtControl xu.1 xu.2) := by
    change Measurable (fun xu =>
      (xu.1.row.1, Function.update (rowInput xu) xu.1.time xu.2))
    exact hforward.prodMk hrowControl
  have hselected : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      xu.1.selected) := measurable_selected.comp measurable_fst
  have hrows : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      ReferenceContinuingLiveSlicePreparation.rowsAtControl xu.1 xu.2) := by
    have hfixed : ∀ j : Fin (M p), Measurable (fun z :
        CompletePublicTable.CompleteRows p × CompletePublicTable.CompleteRow p =>
          Function.update z.1 j z.2) := by
      intro j
      exact (measurable_update' (a := j)).comp measurable_id
    have hupdate : Measurable (fun z :
        (CompletePublicTable.CompleteRows p × CompletePublicTable.CompleteRow p) × Fin (M p) =>
          Function.update z.1.1 z.2 z.1.2) := by
      apply measurable_from_prod_countable_left
      intro j
      exact hfixed j
    have hcode : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
        ((xu.1.rows, ReferenceContinuingLiveSlicePreparation.rowAtControl xu.1 xu.2),
          xu.1.selected)) :=
      ((measurable_rows.comp measurable_fst).prodMk hrowAtControl).prodMk hselected
    change Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      Function.update xu.1.rows xu.1.selected
      (ReferenceContinuingLiveSlicePreparation.rowAtControl xu.1 xu.2))
    exact hupdate.comp hcode
  have hstate : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      xu.1.state) := measurable_state.comp measurable_fst
  have hcoordinates : Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
      (xu.1.state, (ReferenceContinuingLiveSlicePreparation.rowsAtControl xu.1 xu.2,
        (xu.1.selected, (xu.1.time, xu.1.rewards))))) := by
    exact hstate.prodMk (hrows.prodMk (hselected.prodMk
      (htime.prodMk (measurable_rewards.comp measurable_fst))))
  apply measurable_comap_iff.mpr
  change Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
    ReferenceActivePhysicalStepMeasurability.encodeRoundInput
      (ReferenceContinuingLiveSlicePreparation.inputAtControl xu.1 xu.2))
  change Measurable (fun xu : ReferenceActivePhysicalStep.RoundInput p rate × TimeControl p =>
    (⟨
    (xu.1.state, (ReferenceContinuingLiveSlicePreparation.rowsAtControl xu.1 xu.2,
      (xu.1.selected, (xu.1.time, xu.1.rewards)))), xu.1.active⟩ :
      ReferenceActivePhysicalStepMeasurability.ActiveRoundCoordinates p rate))
  exact hcoordinates.subtype_mk (h := fun xu => xu.1.active)

/-- The actual controlled input is jointly Borel on the original retained
source and the whole current control. -/
theorem measurable_currentInputAtControl
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    Measurable (currentInputAtControl rate rewards C_star C_h q t s hs control0) := by
  have hboundary := ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0
  have hactual : Measurable (fun x : X rate rewards C_star C_h q t s hs control0 =>
      actualCurrentInput rate rewards C_star C_h q t s hs control0 x) := by
    rw [show (fun x : X rate rewards C_star C_h q t s hs control0 =>
        actualCurrentInput rate rewards C_star C_h q t s hs control0 x) =
      ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 from by
          funext x
          exact actualCurrentInput_eq_retainedIncomingBoundary
            rate rewards C_star C_h q t s hs control0 x]
    exact hboundary
  have hpair : Measurable (fun xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p =>
      (actualCurrentInput rate rewards C_star C_h q t s hs control0 xu.1, xu.2)) :=
    (hactual.comp measurable_fst).prodMk measurable_snd
  exact (measurable_inputAtControl_roundInput rate).comp hpair

/-- The record used for the current whole-control observation, retaining the
same input and the existing physical step output. -/
def currentRecordAtControl
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  ⟨currentInputAtControl rate rewards C_star C_h q t s hs control0 xu,
    ReferenceActivePhysicalStep.step
      (currentInputAtControl rate rewards C_star C_h q t s hs control0 xu), rfl⟩

@[simp] theorem currentRecordAtControl_input
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    (currentRecordAtControl rate rewards C_star C_h q t s hs control0 xu).input =
      currentInputAtControl rate rewards C_star C_h q t s hs control0 xu := rfl

/-- The controlled record uses the actual physical step output on its input. -/
@[simp] theorem currentRecordAtControl_output
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    (currentRecordAtControl rate rewards C_star C_h q t s hs control0 xu).output =
      ReferenceActivePhysicalStep.step
        (currentInputAtControl rate rewards C_star C_h q t s hs control0 xu) := rfl

/-- The canonical whole-step code on the actual controlled input. -/
def wholeStepCodeAtControl
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p) :=
  ReferenceActiveStepCompositionMeasurability.wholeStepCode
    (currentInputAtControl rate rewards C_star C_h q t s hs control0 xu)

/-- Joint measurability of the existing canonical whole-step code. -/
theorem measurable_wholeStepCodeAtControl
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    Measurable (wholeStepCodeAtControl rate rewards C_star C_h q t s hs control0) := by
  have h := ReferenceActiveStepCompositionMeasurability.measurable_wholeStepCode.comp
    (measurable_currentInputAtControl rate rewards C_star C_h q t s hs control0)
  have hfailure : @LaterAssignmentStartMeasurability.optionMeasurableSpace
      DeclaredFollowerLocalRound.RoundFailure ⊤ = ⊤ :=
    laterOptionSpace_eq_top ⊤ rfl
  have hdown : @LaterAssignmentStartMeasurability.optionMeasurableSpace
      (ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate) ⊤ = ⊤ :=
    laterOptionSpace_eq_top ⊤ rfl
  have hcoordinatorFailure :
      @LaterAssignmentStartMeasurability.optionMeasurableSpace
        ReferenceActivePhysicalStep.CoordinatorFailure ⊤ = ⊤ :=
    laterOptionSpace_eq_top ⊤ rfl
  rw [hfailure, hdown, hcoordinatorFailure] at h
  exact h

/-- The canonical code reconstructs the coordinator observation, all follower
observations, and the successor state of the same current record. -/
theorem wholeStepCodeAtControl_reconstructs
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (xu : X rate rewards C_star C_h q t s hs control0 × TimeControl p) :
    ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
        (wholeStepCodeAtControl rate rewards C_star C_h q t s hs control0 xu).1.2.2.2.2 =
        (ReferenceActivePhysicalStep.prepare
          (currentRecordAtControl rate rewards C_star C_h q t s hs control0 xu).input).observeCoordinator ∧
      (∀ i, ReferenceFollowerTailComposition.reconstructFollowerObservable
        ((wholeStepCodeAtControl rate rewards C_star C_h q t s hs control0 xu).2.1 i) =
          (ReferenceActivePhysicalStep.prepare
            (currentRecordAtControl rate rewards C_star C_h q t s hs control0 xu).input).observeFollower i) ∧
      ReferenceActivePhysicalStepMeasurability.decodeState
        ((wholeStepCodeAtControl rate rewards C_star C_h q t s hs control0 xu).2.2) =
          (ReferenceActivePhysicalStep.step
            (currentRecordAtControl rate rewards C_star C_h q t s hs control0 xu).input).next := by
  exact ReferenceActiveStepCompositionMeasurability.wholeStepCode_reconstructs
    (currentRecordAtControl rate rewards C_star C_h q t s hs control0 xu).input

section

variable {rate : RateInput p}

-- The horizon's RoundRecordCode keeps the option measurable space captured by
-- the canonical whole-step code. Match that existing code space while taking
-- its product projections.
local instance (priority := 5000) codeCoordinatorFailureOptionMeasurableSpace :
    MeasurableSpace (Option ReferenceActivePhysicalStep.CoordinatorFailure) :=
  @LaterAssignmentStartMeasurability.optionMeasurableSpace _ inferInstance

private abbrev CoordinatorCode (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate

private abbrev CollectionTailCode (p : Parameters) (rate : RateInput p) :=
  ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate

private def incomingLiveCoordinatorCode (code : CoordinatorCode p rate) : Bool :=
  match code with
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr _) => false

private theorem measurable_incomingLiveCoordinatorCode :
    Measurable (incomingLiveCoordinatorCode (p := p) (rate := rate)) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.sumElim
    · exact measurable_const
    · exact measurable_const

private def collectionCoordinatorCode (code : CoordinatorCode p rate) : Bool :=
  match code with
  | .inl _ => false
  | .inr (.inl _) => false
  | .inr (.inr (.inl _)) => true
  | .inr (.inr (.inr _)) => false

private theorem measurable_collectionCoordinatorCode :
    Measurable (collectionCoordinatorCode (p := p) (rate := rate)) := by
  apply Measurable.sumElim
  · exact measurable_const
  · apply Measurable.sumElim
    · exact measurable_const
    · apply Measurable.sumElim
      · exact measurable_const
      · exact measurable_const

private def collectionFailureCode
    (failure : Option ReferenceActivePhysicalStep.CoordinatorFailure) : Bool :=
  match failure with
  | some (.collection _) => true
  | _ => false

private theorem measurable_collectionFailureCode :
    Measurable collectionFailureCode := by
  have hopt : codeCoordinatorFailureOptionMeasurableSpace = ⊤ := by
    unfold codeCoordinatorFailureOptionMeasurableSpace
    exact laterOptionSpace_eq_top ⊤ rfl
  change @Measurable (Option ReferenceActivePhysicalStep.CoordinatorFailure) Bool
    codeCoordinatorFailureOptionMeasurableSpace inferInstance collectionFailureCode
  rw [hopt]
  intro s hs
  trivial

/-- A cutoff tag is read from the actual returned collection state or
collection-stage failure. The incoming state tag is checked separately. -/
private def collectionTailTag (code : CollectionTailCode p rate) : Bool :=
  collectionCoordinatorCode code.1 || collectionFailureCode code.2.2.1

private theorem measurable_collectionTailTag (p : Parameters) (rate : RateInput p) :
    Measurable (collectionTailTag (p := p) (rate := rate)) := by
  have hleft : Measurable (fun code : CollectionTailCode p rate =>
      collectionCoordinatorCode code.1) :=
    measurable_collectionCoordinatorCode.comp measurable_fst
  have hright : Measurable (fun code : CollectionTailCode p rate =>
      collectionFailureCode code.2.2.1) :=
    measurable_collectionFailureCode.comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id)))
  have hpair : Measurable (fun code : CollectionTailCode p rate =>
      (collectionCoordinatorCode code.1, collectionFailureCode code.2.2.1)) :=
    hleft.prodMk hright
  exact (measurable_of_countable (fun bits : Bool × Bool => bits.1 || bits.2)).comp hpair

private def recordIncomingCoordinatorCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : CoordinatorCode p rate :=
  code.2.1.1

private def recordPhysicalCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) :=
  code.2.2.1

private def recordCollectionTailCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : CollectionTailCode p rate :=
  (recordPhysicalCode code).2.2.2.2

/-- The cutoff bit stored in an actual chronological record code. -/
private def cutoffRecordCode
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool :=
  incomingLiveCoordinatorCode (recordIncomingCoordinatorCode code) &&
    collectionTailTag (recordCollectionTailCode code)

private theorem measurable_cutoffRecordCode :
    Measurable (cutoffRecordCode (p := p) (rate := rate)) := by
  have hlive : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
      incomingLiveCoordinatorCode (recordIncomingCoordinatorCode code)) := by
    exact measurable_incomingLiveCoordinatorCode.comp
      (measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_id)))
  have htail : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
      collectionTailTag (recordCollectionTailCode code)) := by
    have hphysical : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate) =>
        code.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
    have hrecordTailCode : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate) =>
        recordCollectionTailCode code) := by
      exact measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp (measurable_snd.comp hphysical)))
    exact (measurable_collectionTailTag p rate).comp hrecordTailCode
  exact (measurable_of_countable (fun bits : Bool × Bool => bits.1 && bits.2)).comp
    (hlive.prodMk htail)

private def collectionObservationTag
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) : Bool :=
  match observation.failure with
  | some (.collection _) => true
  | _ =>
      match observation.configuration with
      | .collection _ _ _ => true
      | _ => false

private theorem collectionTailTag_encodeObservation
    (observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate) :
    collectionTailTag (p := p) (rate := rate)
        (ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation observation) =
      collectionObservationTag observation := by
  cases observation with
  | mk configuration bank failure recording up =>
      cases failure with
      | none =>
          cases configuration <;>
            simp [collectionTailTag, collectionCoordinatorCode, collectionFailureCode,
              collectionObservationTag,
              ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator]
      | some failure =>
          cases failure <;> cases configuration <;>
            simp [collectionTailTag, collectionCoordinatorCode, collectionFailureCode,
              collectionObservationTag,
              ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation,
              ReferenceActivePhysicalStepMeasurability.encodeCoordinator]

private theorem collectionFinish_collectionObservationTag
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    collectionObservationTag
      (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut) = true := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hresult : cut.result with
  | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure]
  | success result =>
      cases hfinish : CoordinatorCollectionLedger.finishRound result.1 with
      | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | rejected rejected => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | success ledger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledger.pending x.row with
          | error error => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
              hfinish, hclock]
          | ok clock => simp [collectionObservationTag, hfinish, hclock]
  | rejected result =>
      cases hfinish : CoordinatorCollectionLedger.finishRound result.1 with
      | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | rejected rejected => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hfinish]
      | success ledger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
              ledger.pending x.row with
          | error error => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
              hfinish, hclock]
          | ok clock => simp [collectionObservationTag, hfinish, hclock]

private theorem collectionPostChoice_collectionObservationTag
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    collectionObservationTag
      (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights) = true := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hstart]
      | rejected rejected => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hstart]
      | success ledgerStarted =>
          simp only [hstart]
          exact collectionFinish_collectionObservationTag x payload started recording
            (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)

private theorem livePostChoice_collectionObservationTag
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    collectionObservationTag
      (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started) = false := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error error => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
          hservice]
      | ok serviced =>
          cases hconfirm : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
              hservice]
          | some pending =>
              cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
                  pending x.row with
              | error error => simp [collectionObservationTag,
                  ReferenceActivePhysicalStep.coordinatorFailure, hservice,
                  hclock]
              | ok finished => simp [collectionObservationTag, hservice, hclock]

private theorem liveOutcome_collectionObservationTag
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x registers owned base))
    (hprepared : prepared.coordinator = .live registers owned base outcome) :
    collectionObservationTag prepared.observeCoordinator =
      match outcome with
      | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
      | _ => false := by
  rw [ReferenceActivePhysicalStep.observeCoordinator_live_equation prepared registers owned base
    outcome hprepared]
  cases outcome with
  | clockFailure failure proof =>
      simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceActivePhysicalStep.DispatchCut.selection]
  | initializerFailure dispatched start checked checkedEq =>
      simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceActivePhysicalStep.DispatchCut.selection]
  | localFailure dispatched start reason =>
      simp [collectionObservationTag, ReferenceActivePhysicalStep.coordinatorFailure,
        ReferenceActivePhysicalStep.DispatchCut.selection]
  | cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected =>
      have hselection :
          (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
            (.cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected)).selection ≠ none := by
        simp [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt]
      have hpost := collectionPostChoice_collectionObservationTag x prepared
        registers.payload (ReferenceActivePhysicalStep.sharedLedger ledger)
        dispatched.startResult
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights
      simpa [hselection] using hpost
  | continuingChosen dispatched start continuation selected =>
      have hselection :
          (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
            (.continuingChosen dispatched start continuation selected)).selection ≠ none := by
        simp [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt]
      have hpost := livePostChoice_collectionObservationTag x prepared
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time)
        base dispatched.startResult
      simpa [hselection] using hpost

private theorem cutoffRecordCode_roundRecordCode
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    cutoffRecordCode (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      ReferenceCollectionPhaseHistory.cutoffChosen record.input := by
  have htail : collectionTailTag
      (recordCollectionTailCode (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
      collectionObservationTag
        (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator := by
    rw [show recordCollectionTailCode
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) =
      ReferenceCollectionServiceTailMeasurability.encodeCollectionObservation
        (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator by rfl]
    exact collectionTailTag_encodeObservation _
  change (incomingLiveCoordinatorCode
      (recordIncomingCoordinatorCode
        (ReferenceActiveHorizonMeasurability.roundRecordCode record)) &&
      collectionTailTag
        (recordCollectionTailCode
          (ReferenceActiveHorizonMeasurability.roundRecordCode record))) =
    ReferenceCollectionPhaseHistory.cutoffChosen record.input
  cases hstate : record.input.state.coordinator with
  | first =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
          .first (CoordinatorRoundDispatch.dispatchFirst
            (ReferenceActivePhysicalStep.firstInput record.input)) := by
        rw [ReferenceActivePhysicalStep.dispatch, hstate,
          CoordinatorRoundDispatch.dispatch]
        rfl
      have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch]
      simp [recordIncomingCoordinatorCode,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        incomingLiveCoordinatorCode, hstate, hcutoff]
  | live registers owned base =>
      have hdispatch := ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction
        record.input registers owned base hstate
      cases hout : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput record.input registers owned base) with
      | clockFailure failure proof =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.clockFailure failure proof) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.clockFailure failure proof) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | initializerFailure dispatched start checked checkedEq =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.initializerFailure dispatched start checked checkedEq) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.initializerFailure dispatched start checked checkedEq) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | localFailure dispatched start reason =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.localFailure dispatched start reason) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.localFailure dispatched start reason) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base
                (.cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.cutoffChosen dispatched start ledger initEq ledgerEq domain clock pending noAssign selected)
            hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
      | continuingChosen dispatched start continuation selected =>
          have hprepared' : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
              .live registers owned base (.continuingChosen dispatched start continuation selected) := by
            simp [ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          have htag' := liveOutcome_collectionObservationTag record.input
            (ReferenceActivePhysicalStep.prepare record.input) registers owned base
            (.continuingChosen dispatched start continuation selected) hprepared'
          have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
            simp [ReferenceCollectionPhaseHistory.cutoffChosen,
              ReferenceActivePhysicalStep.prepare, hdispatch, hout]
          rw [htail, htag']
          simp [recordIncomingCoordinatorCode,
            ReferenceActiveHorizonMeasurability.roundRecordCode,
            ReferenceActivePhysicalStepMeasurability.encodeState,
            ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
            incomingLiveCoordinatorCode, hstate, hcutoff]
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)) := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp only [dite_eq_left hvalid, CoordinatorRoundDispatch.dispatch]
          rfl
        have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
          simp [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, hdispatch]
        simp [recordIncomingCoordinatorCode,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLiveCoordinatorCode, hstate, hcutoff]
      · have hdispatch : ReferenceActivePhysicalStep.dispatch record.input =
            .invalidCollectionCutoff := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp [hvalid]
        have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
          simp [ReferenceCollectionPhaseHistory.cutoffChosen,
            ReferenceActivePhysicalStep.prepare, hdispatch]
        simp [recordIncomingCoordinatorCode,
          ReferenceActiveHorizonMeasurability.roundRecordCode,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
          incomingLiveCoordinatorCode, hstate, hcutoff]
  | dagger =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch record.input = .dagger := by
        rw [ReferenceActivePhysicalStep.dispatch, hstate]
      have hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch]
      simp [recordIncomingCoordinatorCode,
        ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        incomingLiveCoordinatorCode, hstate, hcutoff]

private def cutoffFreeTag
    (tagged : Unit ⊕ ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : Bool :=
  tagged.elim (fun _ => true) (fun code => !(cutoffRecordCode code))

private theorem measurable_cutoffFreeTag : Measurable (cutoffFreeTag (p := p) (rate := rate)) := by
  have hnot : Measurable (fun code :
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      !(cutoffRecordCode code)) := by
    exact (measurable_of_countable (fun bit : Bool => !bit)).comp measurable_cutoffRecordCode
  exact Measurable.sumElim measurable_const hnot

private def cutoffFreePrefixCode
    (codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) (count : ℕ) : Prop :=
  ∀ j, j < count → cutoffFreeTag
    (ReferenceActiveHorizonMeasurability.listObservationAt codes j) = true

private theorem measurableSet_cutoffFreePrefixCode (count : ℕ) :
    MeasurableSet {codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) | cutoffFreePrefixCode codes count} := by
  have hset : {codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) | cutoffFreePrefixCode codes count} =
      ⋂ j : ℕ, {codes : List (ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate)) | j < count → cutoffFreeTag
          (ReferenceActiveHorizonMeasurability.listObservationAt codes j) = true} := by
    ext codes
    simp [cutoffFreePrefixCode]
  rw [hset]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j < count
  · have hcoordinates :=
      ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
        (α := ReferenceActiveHorizonMeasurability.RoundRecordCode
          (p := p) (rate := rate))
    have htag : Measurable (fun codes : List
        (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
        cutoffFreeTag (ReferenceActiveHorizonMeasurability.listObservationAt codes j)) :=
      measurable_cutoffFreeTag.comp ((measurable_pi_apply j).comp
        (measurable_snd.comp hcoordinates))
    simpa [hj] using measurableSet_eq_fun htag
      (show Measurable (fun _ : List
        (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) => true) from
          measurable_const)
  · simp [hj]
private theorem cutoffFreePrefixCode_map_iff
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (count : ℕ) :
    cutoffFreePrefixCode (records.map ReferenceActiveHorizonMeasurability.roundRecordCode) count ↔
      ∀ record ∈ records.take count,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  constructor
  · intro h record hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hmem
    have hjlength : j < records.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
    have hjcount : j < count := lt_of_lt_of_le hj (Nat.min_le_left _ _)
    have htag := h j hjcount
    have hbool : ∀ bit : Bool, (!bit) = true ↔ bit = false := by decide
    simpa only [ReferenceActiveHorizonMeasurability.listObservationAt,
      List.getElem?_map, List.getElem?_eq_getElem hjlength, Option.map_some,
      cutoffFreeTag, Sum.elim_inr, cutoffRecordCode_roundRecordCode, hbool] using htag
  · intro h j hj
    unfold ReferenceActiveHorizonMeasurability.listObservationAt
    rw [List.getElem?_map]
    cases hrecord : records[j]? with
    | none => rfl
    | some record =>
        obtain ⟨hjlength, hvalue⟩ := List.getElem?_eq_some_iff.mp hrecord
        have hmem : record ∈ records.take count :=
          List.mem_take_iff_getElem.mpr ⟨j, lt_min hj hjlength, hvalue⟩
        have hbool : ∀ bit : Bool, (!bit) = true ↔ bit = false := by decide
        simpa only [Option.map_some, cutoffFreeTag, Sum.elim_inr, cutoffRecordCode_roundRecordCode,
          hbool] using h record hmem

end

/-- The generated seed is the actual corrected launch state, including its
original carried buffers. Both sides reconstruct the same corrected-launch option. -/
theorem retainedGeneratedActiveSeed_eq_launchState
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : X rate rewards C_star C_h q t s hs control0) :
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x =
      ReferenceFirstLaunchNumericalCell.launchState rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
        rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1 := by
  have hgenerated := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).1
  have hactual := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)
    rewards C_star C_h (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).1
  exact Option.some.inj (hgenerated.symm.trans hactual)

private theorem actualRetainedPrefixRun_eq_runOfInput
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p)
    (x : X rate rewards C_star C_h q t s hs control0) :
    actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x =
      ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega)
        ⟨(ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
            rate rewards C_star C_h q t s hs control0 x,
          ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2,
            (q, rewards))),
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1⟩ := by
  have helapsed := (retainedSourceFacts rate rewards C_star C_h q t s hs control0 x).2
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1
  have hseed := retainedGeneratedActiveSeed_eq_launchState
    rate rewards C_star C_h q t s hs control0 x
  cases hseed
  simp only [actualRetainedPrefixRun, ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
    ReferenceActiveHorizonMeasurability.runOfInput, helapsed, hselected]
  rfl

private theorem measurable_actualRetainedPrefixRecordCodes
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    Measurable (fun x : X rate rewards C_star C_h q t s hs control0 =>
      (actualRetainedPrefixRun rate rewards C_star C_h q t s hs control0 x).records.map
        ReferenceActiveHorizonMeasurability.roundRecordCode) := by
  have hsource : Measurable (fun x : X rate rewards C_star C_h q t s hs control0 =>
      ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) :=
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hrows : Measurable (fun x : X rate rewards C_star C_h q t s hs control0 =>
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2) :=
    measurable_snd.comp (measurable_fst.comp hsource)
  have hdata : Measurable (fun x : X rate rewards C_star C_h q t s hs control0 =>
      (ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x,
        ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2,
          (q, rewards)))) := (ReferenceRetainedBoundaryMeasurability.measurable_retainedGeneratedActiveSeed
    rate rewards C_star C_h q t s hs control0).prodMk
      (hrows.prodMk (measurable_const.prodMk measurable_const))
  let input : X rate rewards C_star C_h q t s hs control0 →
      ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
    fun x => ⟨(ReferenceRetainedBoundaryMeasurability.retainedGeneratedActiveSeed
        rate rewards C_star C_h q t s hs control0 x,
      ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2,
        (q, rewards))), (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
          rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1⟩
  have hinput : Measurable input := hdata.subtype_mk
  have hobservation := measurable_snd.comp
    ((ReferenceActiveHorizonMeasurability.measurable_runObservation
      s (t.val - s + 1) (by omega)).comp hinput)
  convert hobservation using 1
  funext x
  rw [actualRetainedPrefixRun_eq_runOfInput]
  rfl

private def continuingPreparedEvent {rate : RateInput p} (round : ℕ)
    (x : ReferenceActivePhysicalStep.RoundInput p rate) : Prop :=
  match (ReferenceActivePhysicalStep.prepare x).coordinator with
  | .live _ _ _ (.continuingChosen dispatched _ _ _) =>
      dispatched.startResult.pending.Nonempty ∧ round < dispatched.startResult.clock.g
  | _ => False

private def continuingOutcomeEvent (round : ℕ)
    (outcome : ReferenceLiveDispatchOutputMeasurability.OutcomeData p) : Prop :=
  match outcome with
  | .continuingChosen dispatched _ _ =>
      dispatched.1.pending.Nonempty ∧ round < dispatched.1.clock.g
  | _ => False

private theorem continuingPreparedEvent_live_iff {rate : RateInput p} (round : ℕ)
    (x : ReferenceFirstLiveCoordinatorStepMeasurability.LiveInput p rate) :
    continuingPreparedEvent round x.1 ↔ continuingOutcomeEvent round
      (ReferenceLiveDispatchOutputMeasurability.dispatchObservation (liveCoordinates x)).2 := by
  have hdata := ReferenceLiveDispatchOutputMeasurability.outcomeData_originalInput
    x.1 (liveRegisters x) (liveOwned x) (liveBase x)
  change continuingPreparedEvent round x.1 ↔ continuingOutcomeEvent round
    (ReferenceLiveDispatchOutputMeasurability.outcomeData
      (CoordinatorRoundDispatch.dispatchLive
        (ReferenceLiveDispatchMeasurability.liveInputOfCoordinates (liveCoordinates x))))
  unfold liveCoordinates
  rw [hdata]
  unfold continuingPreparedEvent ReferenceActivePhysicalStep.prepare
  dsimp only
  rw [live_dispatch_eq x]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput x.1 (liveRegisters x) (liveOwned x) (liveBase x)) <;>
    rfl

private theorem continuingPreparedEvent_mem_liveSet {rate : RateInput p} (round : ℕ)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hx : continuingPreparedEvent round x) : x ∈ liveSet := by
  cases hstate : x.state.coordinator with
  | first =>
      have hdispatch : ReferenceActivePhysicalStep.dispatch x =
          .first (CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x)) := by
        rw [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
        rfl
      simp only [continuingPreparedEvent, ReferenceActivePhysicalStep.prepare, hdispatch] at hx
  | live registers owned base =>
      exact ⟨(registers.payload, encodeLive registers owned base), by
        simp [ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hstate]⟩
  | collection payload ledger proposal =>
      by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        have hdispatch : ReferenceActivePhysicalStep.dispatch x =
            .collection payload ledger clock cutoff
              (CoordinatorRoundDispatch.dispatchCollection
                (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp only [dite_eq_left hvalid, CoordinatorRoundDispatch.dispatch]
          rfl
        simp only [continuingPreparedEvent, ReferenceActivePhysicalStep.prepare, hdispatch] at hx
      · have hdispatch : ReferenceActivePhysicalStep.dispatch x = .invalidCollectionCutoff := by
          rw [ReferenceActivePhysicalStep.dispatch, hstate]
          simp only [dite_eq_right hvalid]
        simp only [continuingPreparedEvent, ReferenceActivePhysicalStep.prepare, hdispatch] at hx
  | dagger =>
      simp [continuingPreparedEvent, ReferenceActivePhysicalStep.prepare,
        ReferenceActivePhysicalStep.dispatch, hstate] at hx

private theorem measurableSet_continuingPreparedEvent {rate : RateInput p} (round : ℕ) :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      continuingPreparedEvent round x} := by
  have hsub : MeasurableSet {x : ReferenceFirstLiveCoordinatorStepMeasurability.LiveInput p rate |
      continuingPreparedEvent round x.1} := by
    have h := (measurable_of_countable (continuingOutcomeEvent (p := p) round)).comp
      (measurable_snd.comp (measurable_liveDispatchObservation (rate := rate)))
    simpa only [Function.comp_apply, ← continuingPreparedEvent_live_iff] using h.setOf
  have himage := (MeasurableEmbedding.subtype_coe measurableSet_liveSet).measurableSet_image.mpr hsub
  convert himage using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, continuingPreparedEvent_mem_liveSet round x hx⟩, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

/-- Borel measurability of the literal actual continuing recording branch.
No safety or trace event is an input. The strict clock and nonempty pending
tests are read from the actual canonical LIVE dispatch code. -/
theorem measurableSet_continuingRecordingBranch
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) :
    MeasurableSet {x : X rate rewards C_star C_h q t s hs control0 |
      continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x} := by
  have hpast := (measurableSet_cutoffFreePrefixCode (p := p) (rate := rate) (t.val - s)).preimage
    (measurable_actualRetainedPrefixRecordCodes rate rewards C_star C_h q t s hs control0)
  have hactual : Measurable (fun x : X rate rewards C_star C_h q t s hs control0 =>
      actualCurrentInput rate rewards C_star C_h q t s hs control0 x) := by
    convert ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 using 1
    funext x
    exact actualCurrentInput_eq_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0 x
  have hcurrent := (measurableSet_continuingPreparedEvent (rate := rate) (t.val + 1)).preimage hactual
  have hpositive : MeasurableSet {x : X rate rewards C_star C_h q t s hs control0 |
      t.val - s > 0} := by
    by_cases h : t.val - s > 0 <;> simp only [h, Set.ofPred_true, Set.ofPred_false] <;> measurability
  convert hpositive.inter (hpast.inter hcurrent) using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
    cutoffFreePrefixCode_map_iff, continuingRecordingBranch, continuingPreparedEvent]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  cases (ReferenceActivePhysicalStep.prepare
    (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).coordinator with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

private theorem measurable_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ) (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) :
    Measurable f := by
  intro set hset
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ set}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hset

-- Only the ordinary/dagger tag and countable status coordinate are read.
-- Every saved scalar remains in the original carried-state fiber.
private def incomingUnoccupiedTag {rate : RateInput p}
    (code : Unit ⊕ (FollowerPrepareJointMeasurability.CarriedState p rate ×
      FollowerPrepareJointMeasurability.LocalMemoryCode p)) : Bool :=
  code.elim (fun _ => false) (fun data =>
    decide (FollowerDownMeasurability.followerStatusOfCode data.1.1.1.status = .unoccupied))

private theorem measurable_incomingUnoccupiedTag {rate : RateInput p} :
    Measurable (incomingUnoccupiedTag (p := p) (rate := rate)) := by
  apply Measurable.sumElim
  · exact measurable_const
  · have hstate : Measurable (fun state : FollowerPrepareJointMeasurability.CarriedState p rate =>
        decide (FollowerDownMeasurability.followerStatusOfCode state.1.1.status = .unoccupied)) := by
      apply measurable_sigma_sections
      intro index
      change Measurable (fun _ : FollowerDownMeasurability.SavedScalarFamily index.2.1 =>
        decide (FollowerDownMeasurability.followerStatusOfCode index.1.status = .unoccupied))
      exact measurable_const
    exact hstate.comp measurable_fst

private def preparedUnoccupiedTag {rate : RateInput p}
    (code : FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) : Bool :=
  incomingUnoccupiedTag
    (FollowerPrepareJointMeasurability.incomingConfigurationToSum code.2.2.2)

private theorem measurable_preparedUnoccupiedTag {rate : RateInput p} :
    Measurable (preparedUnoccupiedTag (p := p) (rate := rate)) := by
  apply measurable_sigma_sections
  intro activation
  exact measurable_incomingUnoccupiedTag.comp
    ((FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
      (measurable_snd.comp measurable_snd))

private theorem preparedUnoccupiedTag_iff {rate : RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1)) :
    preparedUnoccupiedTag (ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i) = true ↔
      match ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration with
      | .ordinary state _ => state.status = .unoccupied
      | .dagger => False := by
  rw [← ReferenceActivePhysicalStepMeasurability.preparedFollowerCode_reconstruct x i]
  generalize ReferenceActivePhysicalStepMeasurability.preparedFollowerCode x i = code
  cases hconfig : code.2.2.2 with
  | none =>
      simp [preparedUnoccupiedTag, incomingUnoccupiedTag,
        FollowerPrepareJointMeasurability.incomingConfigurationToSum,
        FollowerPrepareJointMeasurability.preparedRoundOfOutput,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hconfig]
  | some data =>
      rcases data with ⟨state, memory⟩
      simp [preparedUnoccupiedTag, incomingUnoccupiedTag,
        FollowerPrepareJointMeasurability.incomingConfigurationToSum,
        FollowerPrepareJointMeasurability.preparedRoundOfOutput,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
        FollowerObservationStageMeasurabilityRepair.reconstructCarriedState,
        FollowerDownMeasurability.followerStateOfCode, hconfig]

/-- Borel measurability of the literal follower recording branch. The status
test reconstructs actual PREPARE; the dagger code contributes false. -/
theorem measurableSet_continuingRecordingFollowerBranch
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) :
    MeasurableSet {x : X rate rewards C_star C_h q t s hs control0 |
      continuingRecordingFollowerBranch rate rewards C_star C_h q t s hs control0 i x} := by
  have hinput := ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0
  have htag := measurable_preparedUnoccupiedTag.comp
    ((ReferenceActivePhysicalStepMeasurability.measurable_preparedFollowerCode i).comp hinput)
  have hset := measurableSet_eq_fun htag
    (show Measurable (fun _ : X rate rewards C_star C_h q t s hs control0 => true) from
      measurable_const)
  convert (measurableSet_continuingRecordingBranch
    rate rewards C_star C_h q t s hs control0).inter hset using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Function.comp_apply,
    continuingRecordingFollowerBranch, preparedUnoccupiedTag_iff,
    ← actualCurrentInput_eq_retainedIncomingBoundary]
  apply and_congr_right
  intro _
  cases ((ReferenceActivePhysicalStep.prepare
    (actualCurrentInput rate rewards C_star C_h q t s hs control0 x)).followers.followers i).configuration <;>
    rfl

/-- The FIRST current round is excluded by the literal positive-prefix test. -/
theorem continuingRecordingBranch_eq_empty_of_offset_eq_zero
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) (hoffset : t.val - s = 0) :
    {x : X rate rewards C_star C_h q t s hs control0 |
      continuingRecordingBranch rate rewards C_star C_h q t s hs control0 x} = ∅ := by
  ext x
  simp only [Set.mem_ofPred_eq, continuingRecordingBranch, hoffset, gt_iff_lt,
    Nat.lt_irrefl, false_and, Set.mem_empty_iff_false]

end Bandits.Support.ReferenceFirstLiveRecordingBranchMeasurability

end
