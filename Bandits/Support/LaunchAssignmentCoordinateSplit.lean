/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaunchJointFutureLaw
public import Bandits.Support.ReferenceLaunchAssignmentLaw
public import Bandits.Support.CompleteRowStoppingLaw
public import Bandits.Support.ContinuousControlSlice
public import Bandits.Support.ContinuousLearningRows
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The complete assignment vector separated from the joint launch future

At a nonterminal actual launch index, the accepted joint future has one full
calendar entry at the launch coordinate, every later full calendar entry, and
all original future player-round private scalars (including the launch round).
This module separates the entire K+1 assignment vector from that launch entry
and leaves every other coordinate in an explicitly labelled remainder.

The split is a composition of finite Pi-subtype equivalences and the accepted
product laws. Its inverse is the inverse measurable equivalence, and the
recovery theorems below identify every original scalar, affine sample,
forward-bit vector, later calendar entry, and private scalar. The actual launch
factorization then gives the unnormalized assignment/remainder product on the
original coordinate space, also when the launch event has zero mass.

Sources: sources/zip4/manuscript/appendix_b_communication.tex:25-58,794-798,
sources/zip4/manuscript/07_public_setup.tex:123-164, and
sources/zip4/manuscript/06_interruptions.tex:410-423.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CompleteRowStoppingLaw
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceLaunchJointFutureLaw
open Bandits.Support.ReferenceLaunchAssignmentLaw
open Bandits.Support.ReferenceLaunchPrivateRoundLaw
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.CanonicalRecordingRates
open scoped ENNReal

namespace Bandits.Support.LaunchAssignmentCoordinateSplit

abbrev Parameters := ConstructorDimensions.Parameters
abbrev LaunchIndex (p : Parameters) := Fin (p.T + 1)
abbrev AssignmentVector (p : Parameters) :=
  ReferenceLaunchAssignmentLaw.AssignmentVector p
abbrev Scalar (_p : Parameters) := ContinuousControlSlice.Scalar
abbrev Label (p : Parameters) := ContinuousControlSlice.Label p.m p.K
abbrev AffineSamples (p : Parameters) := ContinuousLearningRows.AffineSamples p
abbrev ForwardBits (p : Parameters) := Fin (A_id p) → Bool

/-- The actual launch-calendar index inside the accepted non-strict future. -/
def launchFutureIndex (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) : FutureIndex p σ :=
  ⟨⟨σ.val, hσ⟩, by change ¬ σ.val < σ.val; exact not_lt_of_ge le_rfl⟩

/-- Every non-assignment scalar label at launch, retaining its source label. -/
abbrev NonAssignmentLabel (p : Parameters) :=
  {c : Label p // ¬ ∃ r : Fin (p.K + 1), c = Label.assign r}

/-- The assignment-labelled part of the original scalar label type. -/
abbrev AssignmentLabel (p : Parameters) :=
  {c : Label p // ∃ r : Fin (p.K + 1), c = Label.assign r}

abbrev NonAssignmentScalars (p : Parameters) := NonAssignmentLabel p → Scalar p

/-- Calendar indices strictly after launch, with their original future labels.
-/
abbrev AfterLaunchIndex (p : Parameters) (σ : LaunchIndex p) :=
  {i : FutureIndex p σ // i.1.val ≠ σ.val}

abbrev AfterLaunchCalendarArray (p : Parameters) (σ : LaunchIndex p) :=
  AfterLaunchIndex p σ → CompleteRowStoppingLaw.CalendarEntry p

/-- Launch-round fields left in the remainder, in their original carriers. -/
abbrev LaunchEntryRemainder (p : Parameters) :=
  NonAssignmentScalars p × (ForwardBits p × AffineSamples p)

/-- The exact remainder: non-assignment launch scalars, the full launch
forward vector, all launch affine samples, every later complete calendar
entry, and every future player-round private scalar. -/
abbrev Remainder (p : Parameters) (σ : LaunchIndex p) :=
  NonAssignmentScalars p ×
    (ForwardBits p ×
      (AffineSamples p ×
        (AfterLaunchCalendarArray p σ ×
          ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundScalars p σ)))

/-- The literal product law of the non-assignment launch-slice scalars. -/
def nonAssignmentScalarLaw (p : Parameters) : Measure (NonAssignmentScalars p) :=
  by
    classical
    exact Measure.pi (fun _ : NonAssignmentLabel p => ContinuousControlSlice.scalarLaw)

/-- The literal product law of every launch forward bit. -/
def launchForwardBitsLaw (p : Parameters) : Measure (ForwardBits p) :=
  Measure.pi (fun _ : Fin (A_id p) => CompletePublicTable.forwardBitLaw p)

/-- The literal law of all complete calendar entries strictly after launch. -/
def afterLaunchCalendarLaw (p : Parameters) (σ : LaunchIndex p) :
    Measure (AfterLaunchCalendarArray p σ) :=
  by
    classical
    exact Measure.pi
      (fun _ : AfterLaunchIndex p σ => CompleteRowStoppingLaw.calendarEntryLaw p)

/-- Literal product law of the entire labelled remainder. -/
def remainderLaw (p : Parameters) (σ : LaunchIndex p) : Measure (Remainder p σ) :=
  (nonAssignmentScalarLaw p).prod
    ((launchForwardBitsLaw p).prod
      ((ContinuousLearningRows.affineSamplesLaw p).prod
        ((afterLaunchCalendarLaw p σ).prod
          (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ))))

/-- Literal product law of the fields retained from the launch calendar entry
after removing the assignment vector. -/
def launchEntryRemainderLaw (p : Parameters) : Measure (LaunchEntryRemainder p) :=
  (nonAssignmentScalarLaw p).prod
    ((launchForwardBitsLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))

instance nonAssignmentScalarLaw_probability (p : Parameters) :
    IsProbabilityMeasure (nonAssignmentScalarLaw p) := by
  dsimp [nonAssignmentScalarLaw]
  infer_instance

instance launchForwardBitsLaw_probability (p : Parameters) :
    IsProbabilityMeasure (launchForwardBitsLaw p) := by
  dsimp [launchForwardBitsLaw]
  infer_instance

instance launchEntryRemainderLaw_probability (p : Parameters) :
    IsProbabilityMeasure (launchEntryRemainderLaw p) := by
  dsimp [launchEntryRemainderLaw]
  infer_instance

instance afterLaunchCalendarLaw_probability (p : Parameters) (σ : LaunchIndex p) :
    IsProbabilityMeasure (afterLaunchCalendarLaw p σ) := by
  dsimp [afterLaunchCalendarLaw]
  infer_instance

instance remainderLaw_probability (p : Parameters) (σ : LaunchIndex p) :
    IsProbabilityMeasure (remainderLaw p σ) := by
  dsimp [remainderLaw]
  infer_instance

/-- Reindex the assignment-label subtype by its exact source index Fin(K+1).
-/
def assignmentLabelEquiv (p : Parameters) : Fin (p.K + 1) ≃ AssignmentLabel p :=
  Equiv.ofBijective
    (fun r : Fin (p.K + 1) =>
      (⟨Label.assign r, ⟨r, rfl⟩⟩ : AssignmentLabel p))
    ⟨by
      intro r s h
      have hv : Label.assign r = Label.assign s := congrArg Subtype.val h
      exact Label.assign_injective p.m p.K hv,
     by
      intro c
      rcases c.2 with ⟨r, hr⟩
      exact ⟨r, Subtype.ext hr.symm⟩⟩

@[simp] theorem assignmentLabelEquiv_apply_val (p : Parameters) (r : Fin (p.K + 1)) :
    (assignmentLabelEquiv p r).1 = Label.assign r := rfl

/-- Exact scalar-slice split using Mathlib's Pi-subtype split for the
assignment range and its complement. -/
def sliceAssignmentSplitEquiv (p : Parameters) :
    ContinuousControlSlice.Slice p.m p.K ≃ᵐ
      (AssignmentVector p × NonAssignmentScalars p) := by
  classical
  exact
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Label p => Scalar p)
      (fun c : Label p => ∃ r : Fin (p.K + 1), c = Label.assign r)).trans
      (MeasurableEquiv.prodCongr
        ((MeasurableEquiv.piCongrLeft
          (fun _ : AssignmentLabel p => Scalar p) (assignmentLabelEquiv p)).symm)
        (MeasurableEquiv.refl _))

theorem measurePreserving_sliceAssignmentSplitEquiv (p : Parameters) :
    MeasurePreserving (sliceAssignmentSplitEquiv p)
      (ContinuousControlSlice.sliceLaw p.m p.K)
      ((ContinuousControlSlice.assignmentLaw p.K).prod (nonAssignmentScalarLaw p)) := by
  classical
  let pred : Label p → Prop :=
    fun c => ∃ r : Fin (p.K + 1), c = Label.assign r
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Label p => ContinuousControlSlice.scalarLaw) pred
  have hreindex :=
    (measurePreserving_piCongrLeft
      (fun _ : AssignmentLabel p => ContinuousControlSlice.scalarLaw)
      (assignmentLabelEquiv p)).symm
  have hpair := hreindex.prod
    (MeasurePreserving.id (nonAssignmentScalarLaw p))
  exact hpair.comp hsplit

/-- Split the launch TimeControl into the complete assignment vector and every
other scalar and affine coordinate. -/
def controlAssignmentSplitEquiv (p : Parameters) :
    ContinuousLearningRows.TimeControl p ≃ᵐ
      (AssignmentVector p × (NonAssignmentScalars p × AffineSamples p)) :=
  (MeasurableEquiv.prodCongr (sliceAssignmentSplitEquiv p)
    (MeasurableEquiv.refl (AffineSamples p))).trans MeasurableEquiv.prodAssoc

theorem measurePreserving_controlAssignmentSplitEquiv (p : Parameters) :
    MeasurePreserving (controlAssignmentSplitEquiv p)
      (ContinuousLearningRows.timeControlLaw p)
      ((ContinuousControlSlice.assignmentLaw p.K).prod
        ((nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))) := by
  have hpair := (measurePreserving_sliceAssignmentSplitEquiv p).prod
    (MeasurePreserving.id (ContinuousLearningRows.affineSamplesLaw p))
  exact (measurePreserving_prodAssoc
    (ContinuousControlSlice.assignmentLaw p.K) (nonAssignmentScalarLaw p)
    (ContinuousLearningRows.affineSamplesLaw p)).comp hpair

/-- Reassociate the non-assignment scalar, forward, and affine launch
coordinates into the remainder's source-label order. -/
def launchEntryRemainderAssocEquiv (p : Parameters) :
    ((NonAssignmentScalars p × AffineSamples p) × ForwardBits p) ≃ᵐ
      (NonAssignmentScalars p × (ForwardBits p × AffineSamples p)) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) MeasurableEquiv.prodComm)

/-- Split the actual launch calendar entry into the full assignment vector
and its labelled remainder. -/
def launchEntrySplitEquiv (p : Parameters) :
    CompleteRowStoppingLaw.CalendarEntry p ≃ᵐ
      (AssignmentVector p × LaunchEntryRemainder p) :=
  (MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.prodCongr (controlAssignmentSplitEquiv p)
      (MeasurableEquiv.refl (ForwardBits p))).trans MeasurableEquiv.prodAssoc)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (AssignmentVector p))
      (launchEntryRemainderAssocEquiv p))

theorem measurePreserving_launchEntrySplitEquiv (p : Parameters) :
    MeasurePreserving (launchEntrySplitEquiv p)
      (CompleteRowStoppingLaw.calendarEntryLaw p)
      ((ContinuousControlSlice.assignmentLaw p.K).prod
        ((nonAssignmentScalarLaw p).prod
          ((launchForwardBitsLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)))) := by
  have hswap : MeasurePreserving Prod.swap
      ((launchForwardBitsLaw p).prod (ContinuousLearningRows.timeControlLaw p))
      ((ContinuousLearningRows.timeControlLaw p).prod (launchForwardBitsLaw p)) :=
    Measure.measurePreserving_swap
  have hfirst :=
    ((measurePreserving_controlAssignmentSplitEquiv p).prod
      (MeasurePreserving.id (launchForwardBitsLaw p))).comp hswap
  have hsecond := (measurePreserving_prodAssoc
    (ContinuousControlSlice.assignmentLaw p.K)
    ((nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))
    (launchForwardBitsLaw p)).comp hfirst
  have hremainder : MeasurePreserving (launchEntryRemainderAssocEquiv p)
      (((nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)).prod
        (launchForwardBitsLaw p))
      ((nonAssignmentScalarLaw p).prod
        ((launchForwardBitsLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))) := by
    have h₁ := measurePreserving_prodAssoc (nonAssignmentScalarLaw p)
      (ContinuousLearningRows.affineSamplesLaw p) (launchForwardBitsLaw p)
    exact ((MeasurePreserving.id (nonAssignmentScalarLaw p)).prod
      Measure.measurePreserving_swap).comp h₁
  exact ((MeasurePreserving.id (ContinuousControlSlice.assignmentLaw p.K)).prod
    hremainder).comp hsecond

/-- The unique future-array index with the original calendar label sigma. -/
abbrev LaunchCalendarIndex (p : Parameters) (σ : LaunchIndex p) :=
  {i : FutureIndex p σ // i.1.val = σ.val}

/-- A finite subtype of actual future calendar indices excluding launch. -/
abbrev LaterCalendarIndex (p : Parameters) (σ : LaunchIndex p) :=
  AfterLaunchIndex p σ

def launchCalendarIndexEquivUnit (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) : LaunchCalendarIndex p σ ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨launchFutureIndex p σ hσ, rfl⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    exact i.property.symm
  right_inv u := by
    cases u
    rfl

/-- Split the entire future calendar at its actual launch index. The
launch singleton is reindexed by Unit, while later coordinates keep their
original future-index labels. -/
def calendarLaunchSplitEquiv (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) :
    CompleteRowStoppingLaw.FutureArray p σ ≃ᵐ
      (CompleteRowStoppingLaw.CalendarEntry p × AfterLaunchCalendarArray p σ) := by
  classical
  let launchIndexEquiv := launchCalendarIndexEquivUnit p σ hσ
  let launchPiEquiv :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : LaunchCalendarIndex p σ => CompleteRowStoppingLaw.CalendarEntry p)
      launchIndexEquiv.symm).symm
      |>.trans (MeasurableEquiv.piUnique
        (fun _ : Unit => CompleteRowStoppingLaw.CalendarEntry p))
  exact
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : FutureIndex p σ => CompleteRowStoppingLaw.CalendarEntry p)
      (fun i : FutureIndex p σ => i.1.val = σ.val)).trans
      (MeasurableEquiv.prodCongr launchPiEquiv (MeasurableEquiv.refl _))

theorem measurePreserving_calendarLaunchSplitEquiv (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    MeasurePreserving (calendarLaunchSplitEquiv p σ hσ)
      (CompleteRowStoppingLaw.futureArrayLaw p σ)
      ((CompleteRowStoppingLaw.calendarEntryLaw p).prod (afterLaunchCalendarLaw p σ)) := by
  classical
  let launchIndexEquiv := launchCalendarIndexEquivUnit p σ hσ
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : FutureIndex p σ => CompleteRowStoppingLaw.calendarEntryLaw p)
    (fun i : FutureIndex p σ => i.1.val = σ.val)
  have hindex :=
    (measurePreserving_piCongrLeft
      (fun _ : LaunchCalendarIndex p σ => CompleteRowStoppingLaw.calendarEntryLaw p)
      launchIndexEquiv.symm).symm
  have hsingleton := (measurePreserving_piUnique
    (fun _ : Unit => CompleteRowStoppingLaw.calendarEntryLaw p)).comp hindex
  exact (hsingleton.prod (MeasurePreserving.id (afterLaunchCalendarLaw p σ))).comp hsplit

@[simp] theorem calendarLaunchSplitEquiv_launch (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : CompleteRowStoppingLaw.FutureArray p σ) :
    (calendarLaunchSplitEquiv p σ hσ future).1 =
      future (launchFutureIndex p σ hσ) := by
  simp [calendarLaunchSplitEquiv, launchCalendarIndexEquivUnit,
    launchFutureIndex, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, MeasurableEquiv.piUnique, Equiv.piUnique,
    MeasurableEquiv.prodCongr, MeasurableEquiv.trans,
    Equiv.trans_apply]

@[simp] theorem calendarLaunchSplitEquiv_later (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : CompleteRowStoppingLaw.FutureArray p σ)
    (i : AfterLaunchIndex p σ) :
    (calendarLaunchSplitEquiv p σ hσ future).2 i = future i.1 := by
  simp [calendarLaunchSplitEquiv, launchCalendarIndexEquivUnit,
    launchFutureIndex, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, Equiv.trans_apply,
    MeasurableEquiv.prodCongr, MeasurableEquiv.trans,
    Equiv.prodCongr_apply]

/-- Reassociate the launch-entry remainder with later calendar entries and
all future private player-round scalars. -/
def remainderAssocEquiv (p : Parameters) (σ : LaunchIndex p) :
    (LaunchEntryRemainder p ×
      (AfterLaunchCalendarArray p σ ×
        ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundScalars p σ)) ≃ᵐ
      Remainder p σ :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (NonAssignmentScalars p))
      MeasurableEquiv.prodAssoc)

/-- Exact measurable equivalence from the accepted whole joint future to the
entire original assignment vector paired with the labelled coordinate
remainder. Its inverse is the composed inverse of these finite product and
Pi-subtype equivalences. -/
def jointFutureCoordinateSplitEquiv (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) :
    ReferenceLaunchJointFutureLaw.JointFuture p σ ≃ᵐ
      (AssignmentVector p × Remainder p σ) :=
  (((MeasurableEquiv.prodCongr (calendarLaunchSplitEquiv p σ hσ)
      (MeasurableEquiv.refl
        (ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundScalars p σ))).trans
      MeasurableEquiv.prodAssoc).trans
      ((MeasurableEquiv.prodCongr (launchEntrySplitEquiv p)
        (MeasurableEquiv.refl
          (AfterLaunchCalendarArray p σ ×
            ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundScalars p σ))).trans
        MeasurableEquiv.prodAssoc)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (AssignmentVector p))
        (remainderAssocEquiv p σ))

theorem measurePreserving_jointFutureCoordinateSplitEquiv (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    MeasurePreserving (jointFutureCoordinateSplitEquiv p σ hσ)
      (ReferenceLaunchJointFutureLaw.jointFutureLaw p σ)
      ((ContinuousControlSlice.assignmentLaw p.K).prod (remainderLaw p σ)) := by
  have h₁ :=
    (measurePreserving_calendarLaunchSplitEquiv p σ hσ).prod
      (MeasurePreserving.id
        (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ))
  have h₂ := (measurePreserving_prodAssoc
    (CompleteRowStoppingLaw.calendarEntryLaw p)
    (afterLaunchCalendarLaw p σ)
    (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ)).comp h₁
  have h₃ := (measurePreserving_launchEntrySplitEquiv p).prod
    (MeasurePreserving.id
      ((afterLaunchCalendarLaw p σ).prod
        (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ)))
  have h₄ := (measurePreserving_prodAssoc
    (ContinuousControlSlice.assignmentLaw p.K)
    (launchEntryRemainderLaw p)
    ((afterLaunchCalendarLaw p σ).prod
      (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ))).comp
        (h₃.comp h₂)
  have hremainder : MeasurePreserving (remainderAssocEquiv p σ)
      ((launchEntryRemainderLaw p).prod
        ((afterLaunchCalendarLaw p σ).prod
          (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ)))
      (remainderLaw p σ) := by
    have hₐ := measurePreserving_prodAssoc
      (nonAssignmentScalarLaw p)
      ((launchForwardBitsLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))
      ((afterLaunchCalendarLaw p σ).prod
        (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ))
    exact ((MeasurePreserving.id (nonAssignmentScalarLaw p)).prod
      (measurePreserving_prodAssoc
        (launchForwardBitsLaw p) (ContinuousLearningRows.affineSamplesLaw p)
        ((afterLaunchCalendarLaw p σ).prod
          (ReferenceLaunchPrivateRoundLaw.futurePlayerRoundScalarLaw p σ)))).comp hₐ
  exact ((MeasurePreserving.id (ContinuousControlSlice.assignmentLaw p.K)).prod
    hremainder).comp h₄

/-- Exact pushforward identity for the whole joint-future split. -/
theorem map_jointFutureCoordinateSplitEquiv (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) :
    (ReferenceLaunchJointFutureLaw.jointFutureLaw p σ).map
        (jointFutureCoordinateSplitEquiv p σ hσ) =
      (ContinuousControlSlice.assignmentLaw p.K).prod (remainderLaw p σ) :=
  (measurePreserving_jointFutureCoordinateSplitEquiv p σ hσ).map_eq

/-- The forward split's first coordinate is exactly the accepted complete
assignment vector at the original launch-calendar coordinate. -/
theorem jointFutureCoordinateSplit_first (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T)
    (future : ReferenceLaunchJointFutureLaw.JointFuture p σ) :
    (jointFutureCoordinateSplitEquiv p σ hσ future).1 =
      ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma p σ hσ future.1 := by
  funext r
  simp [jointFutureCoordinateSplitEquiv, remainderAssocEquiv,
    launchEntryRemainderAssocEquiv, launchEntrySplitEquiv,
    controlAssignmentSplitEquiv, sliceAssignmentSplitEquiv,
    assignmentLabelEquiv_apply_val, launchFutureIndex,
    ReferenceLaunchAssignmentLaw.launchSourceIndex,
    ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma,
    ContinuousControlSlice.assignmentVector,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply]

/-- Every non-assignment scalar at launch is retained under its original
Appendix B label. -/
theorem jointFutureCoordinateSplit_launchScalar (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : ReferenceLaunchJointFutureLaw.JointFuture p σ)
    (c : NonAssignmentLabel p) :
      ((jointFutureCoordinateSplitEquiv p σ hσ future).2).1 c =
      ((future.1 (launchFutureIndex p σ hσ)).2.1) c.1 := by
  simp [jointFutureCoordinateSplitEquiv, remainderAssocEquiv,
    launchEntryRemainderAssocEquiv, launchEntrySplitEquiv,
    controlAssignmentSplitEquiv, sliceAssignmentSplitEquiv,
    launchFutureIndex, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply]

/-- The full launch forward-ID vector is retained. -/
theorem jointFutureCoordinateSplit_launchForward (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : ReferenceLaunchJointFutureLaw.JointFuture p σ) (u : Fin (A_id p)) :
    (((jointFutureCoordinateSplitEquiv p σ hσ future).2).2.1) u =
      (future.1 (launchFutureIndex p σ hσ)).1 u := by
  simp [jointFutureCoordinateSplitEquiv, remainderAssocEquiv,
    launchEntryRemainderAssocEquiv, launchEntrySplitEquiv,
    controlAssignmentSplitEquiv, sliceAssignmentSplitEquiv,
    launchFutureIndex, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply]

/-- Every launch affine sample, hence all its coefficients and offset, is
retained at its original direction/follower channel. -/
theorem jointFutureCoordinateSplit_launchAffine (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : ReferenceLaunchJointFutureLaw.JointFuture p σ)
    (channel : ContinuousLearningRows.Channel p) :
    ((((jointFutureCoordinateSplitEquiv p σ hσ future).2).2.2.1) channel) =
      (future.1 (launchFutureIndex p σ hσ)).2.2 channel := by
  simp [jointFutureCoordinateSplitEquiv, remainderAssocEquiv,
    launchEntryRemainderAssocEquiv, launchEntrySplitEquiv,
    controlAssignmentSplitEquiv, sliceAssignmentSplitEquiv,
    launchFutureIndex, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply,
    Equiv.prodAssoc_apply]

/-- Every complete strictly-later calendar entry retains its original
future-index label. -/
theorem jointFutureCoordinateSplit_laterCalendar (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : ReferenceLaunchJointFutureLaw.JointFuture p σ)
    (i : AfterLaunchIndex p σ) :
    (((((jointFutureCoordinateSplitEquiv p σ hσ future).2).2.2.2).1) i) =
      future.1 i.1 := by
  simp [jointFutureCoordinateSplitEquiv, remainderAssocEquiv,
    launchEntryRemainderAssocEquiv, launchEntrySplitEquiv,
    controlAssignmentSplitEquiv, sliceAssignmentSplitEquiv,
    launchFutureIndex, MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft,
    MeasurableEquiv.prodAssoc, MeasurableEquiv.prodComm,
    MeasurableEquiv.prodCongr]

/-- Every future private player-round scalar, including launch-round
coordinates, is retained under its original player/calendar label. -/
theorem jointFutureCoordinateSplit_private (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (future : ReferenceLaunchJointFutureLaw.JointFuture p σ)
    (label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ) :
    (((((jointFutureCoordinateSplitEquiv p σ hσ future).2).2.2.2).2) label) =
      future.2 label := rfl

/-- The inverse equivalence recovers each original assignment scalar,
including the final orientation coordinate Fin.last K. -/
theorem jointFutureCoordinateSplit_symm_assignment (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (v : AssignmentVector p) (rem : Remainder p σ) (r : Fin (p.K + 1)) :
    (((jointFutureCoordinateSplitEquiv p σ hσ).symm (v, rem)).1
      (launchFutureIndex p σ hσ)).2.1 (Label.assign r) = v r := by
  have h := congrArg (fun x : AssignmentVector p × Remainder p σ => x.1 r)
    ((jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply (v, rem))
  rw [jointFutureCoordinateSplit_first] at h
  exact h

/-- The inverse recovers each non-assignment launch scalar at its original
Appendix B label. -/
theorem jointFutureCoordinateSplit_symm_launchScalar (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (v : AssignmentVector p) (rem : Remainder p σ)
    (c : NonAssignmentLabel p) :
    (((jointFutureCoordinateSplitEquiv p σ hσ).symm (v, rem)).1
      (launchFutureIndex p σ hσ)).2.1 c.1 = rem.1 c := by
  have h := congrArg (fun x : AssignmentVector p × Remainder p σ => x.2.1 c)
    ((jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply (v, rem))
  rw [jointFutureCoordinateSplit_launchScalar] at h
  exact h

/-- The inverse recovers the entire launch forward-ID vector pointwise. -/
theorem jointFutureCoordinateSplit_symm_launchForward (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (v : AssignmentVector p) (rem : Remainder p σ) (u : Fin (A_id p)) :
    (((jointFutureCoordinateSplitEquiv p σ hσ).symm (v, rem)).1
      (launchFutureIndex p σ hσ)).1 u = rem.2.1 u := by
  have h := congrArg (fun x : AssignmentVector p × Remainder p σ => x.2.2.1 u)
    ((jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply (v, rem))
  rw [jointFutureCoordinateSplit_launchForward] at h
  exact h

/-- The inverse recovers each launch affine coefficient vector and offset
sample unchanged. -/
theorem jointFutureCoordinateSplit_symm_launchAffine (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (v : AssignmentVector p) (rem : Remainder p σ)
    (channel : ContinuousLearningRows.Channel p) :
    (((jointFutureCoordinateSplitEquiv p σ hσ).symm (v, rem)).1
      (launchFutureIndex p σ hσ)).2.2 channel = rem.2.2.1 channel := by
  have h := congrArg (fun x : AssignmentVector p × Remainder p σ => x.2.2.2.1 channel)
    ((jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply (v, rem))
  rw [jointFutureCoordinateSplit_launchAffine] at h
  exact h

/-- The inverse recovers every later complete calendar entry. -/
theorem jointFutureCoordinateSplit_symm_laterCalendar (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (v : AssignmentVector p) (rem : Remainder p σ)
    (i : AfterLaunchIndex p σ) :
    ((jointFutureCoordinateSplitEquiv p σ hσ).symm (v, rem)).1 i.1 =
      rem.2.2.2.1 i := by
  have h := congrArg (fun x : AssignmentVector p × Remainder p σ => x.2.2.2.2.1 i)
    ((jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply (v, rem))
  rw [jointFutureCoordinateSplit_laterCalendar] at h
  exact h

/-- The inverse recovers every original future private scalar by label. -/
theorem jointFutureCoordinateSplit_symm_private (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (v : AssignmentVector p) (rem : Remainder p σ)
    (label : ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p σ) :
    ((jointFutureCoordinateSplitEquiv p σ hσ).symm (v, rem)).2 label =
      rem.2.2.2.2 label := by
  have h := congrArg (fun x : AssignmentVector p × Remainder p σ => x.2.2.2.2.2 label)
    ((jointFutureCoordinateSplitEquiv p σ hσ).apply_symm_apply (v, rem))
  exact h

/-- Assignment coordinate of the explicit inverse reconstruction on original
source coordinates. -/
def originalAssignmentVectorAtLaunch (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p) :
    AssignmentVector p :=
  (jointFutureCoordinateSplitEquiv p σ hσ
    (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).2).1

/-- Exact remainder coordinate of the inverse reconstruction on original
source coordinates. -/
def exactRemainderAtLaunch (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T) (z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p) :
    Remainder p σ :=
  (jointFutureCoordinateSplitEquiv p σ hσ
    (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).2).2

theorem measurable_originalAssignmentVectorAtLaunch (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (originalAssignmentVectorAtLaunch p σ hσ) :=
  (measurable_fst.comp (jointFutureCoordinateSplitEquiv p σ hσ).measurable).comp
    (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).measurable.snd

theorem measurable_exactRemainderAtLaunch (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T) :
    Measurable (exactRemainderAtLaunch p σ hσ) :=
  (measurable_snd.comp (jointFutureCoordinateSplitEquiv p σ hσ).measurable).comp
    (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).measurable.snd

/-- The split's original-source assignment vector agrees with the accepted
future projection and the accepted original-row identity. -/
theorem originalAssignmentVectorAtLaunch_eq_original (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p) :
    originalAssignmentVectorAtLaunch p σ hσ z =
      ReferenceLaunchAssignmentLaw.originalAssignmentVectorAt p σ hσ z.2 := by
  rw [originalAssignmentVectorAtLaunch, jointFutureCoordinateSplit_first]
  exact ReferenceLaunchAssignmentLaw.futureAssignmentVectorAtSigma_eq_original
    p σ hσ z

/-- The accepted actual first-start payload consumes exactly the complete
assignment vector placed in the split at its source launch coordinate. -/
theorem actualStart_coordinates_eq_split_first (p : Parameters)
    (eta : LearningRate)
    (hcap : eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (n : ℕ) (hn : (n : ℝ) = eta.val * (D p : ℝ))
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p) :
    (ReferenceLaunchAssignmentLaw.actualStartAtSigma p eta hcap n hn σ hσ z.2).coordinates =
      originalAssignmentVectorAtLaunch p σ hσ z := by
  exact (ReferenceLaunchAssignmentLaw.actualStart_coordinates
    p eta hcap n hn σ hσ z.2).trans
      (originalAssignmentVectorAtLaunch_eq_original p σ hσ z).symm

/-- The rectangular assignment/remainder event in the joint future is
measurable for arbitrary measurable cube and remainder events. -/
theorem measurable_jointFutureRectanglePreimage (p : Parameters)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C)
    (E : Set (Remainder p σ)) (hE : MeasurableSet E) :
    MeasurableSet
      ((jointFutureCoordinateSplitEquiv p σ hσ) ⁻¹' (C ×ˢ E)) :=
  (hC.prod hE).preimage (jointFutureCoordinateSplitEquiv p σ hσ).measurable

/-- The joint-future mass of a split rectangle is the exact product of the
complete assignment-vector law and the literal remainder product law. -/
theorem jointFuture_rectangle_mass (p : Parameters) (σ : LaunchIndex p)
    (hσ : σ.val < p.T)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C)
    (E : Set (Remainder p σ)) (hE : MeasurableSet E) :
    ReferenceLaunchJointFutureLaw.jointFutureLaw p σ
      ((jointFutureCoordinateSplitEquiv p σ hσ) ⁻¹' (C ×ˢ E)) =
      (ContinuousControlSlice.assignmentLaw p.K) C * (remainderLaw p σ) E := by
  calc
    _ = ((ReferenceLaunchJointFutureLaw.jointFutureLaw p σ).map
        (jointFutureCoordinateSplitEquiv p σ hσ)) (C ×ˢ E) := by
      rw [Measure.map_apply_of_aemeasurable
        (jointFutureCoordinateSplitEquiv p σ hσ).measurable.aemeasurable (hC.prod hE)]
    _ = ((ContinuousControlSlice.assignmentLaw p.K).prod (remainderLaw p σ))
        (C ×ˢ E) := by rw [map_jointFutureCoordinateSplitEquiv p σ hσ]
    _ = _ := Measure.prod_prod _ _

/-- The unnormalized actual-launch/past/assignment/remainder identity on the
original coordinate space. It remains valid at zero launch-event mass. -/
theorem actual_launch_assignment_remainder_factorization (p : Parameters)
    (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (ReferenceLaunchJointFutureLaw.JointPast p σ))
    (hA : MeasurableSet A)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C)
    (E : Set (Remainder p σ)) (hE : MeasurableSet E) :
    ReferenceLaunchJointFutureLaw.originalLaw p
      {z | ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1 ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A ∧
        originalAssignmentVectorAtLaunch p σ hσ z ∈ C ∧
        exactRemainderAtLaunch p σ hσ z ∈ E} =
    (ReferenceLaunchJointFutureLaw.originalLaw p
      {z | ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1 ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A}) *
      (ContinuousControlSlice.assignmentLaw p.K) C * (remainderLaw p σ) E := by
  let futureRectangle : Set (ReferenceLaunchJointFutureLaw.JointFuture p σ) :=
    (jointFutureCoordinateSplitEquiv p σ hσ) ⁻¹' (C ×ˢ E)
  have hFuture : MeasurableSet futureRectangle :=
    measurable_jointFutureRectanglePreimage p σ hσ C hC E hE
  have hset :
      {z | ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1 ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A ∧
        originalAssignmentVectorAtLaunch p σ hσ z ∈ C ∧
        exactRemainderAtLaunch p σ hσ z ∈ E} =
      {z | ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1 ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).2 ∈ futureRectangle} := by
    ext z
    simp [futureRectangle, originalAssignmentVectorAtLaunch,
      exactRemainderAtLaunch, Set.mem_preimage, Set.mem_prod]
  rw [hset]
  calc
    _ = _ := ReferenceLaunchJointFutureLaw.actual_launch_event_factorization
      p ids rewards C_star C_h eta σ A hA futureRectangle hFuture
    _ = _ := by
      rw [jointFuture_rectangle_mass p σ hσ C hC E hE, mul_assoc]

/-- Measurability of the actual launch/past/assignment/remainder event in the
unnormalized source identity. -/
theorem measurable_actual_launch_assignment_remainder_event (p : Parameters)
    (ids : IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : LearningRate)
    (σ : LaunchIndex p) (hσ : σ.val < p.T)
    (A : Set (ReferenceLaunchJointFutureLaw.JointPast p σ))
    (hA : MeasurableSet A)
    (C : Set (AssignmentVector p)) (hC : MeasurableSet C)
    (E : Set (Remainder p σ)) (hE : MeasurableSet E) :
    MeasurableSet
      {z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p |
        ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1 ∧
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A ∧
        originalAssignmentVectorAtLaunch p σ hσ z ∈ C ∧
        exactRemainderAtLaunch p σ hσ z ∈ E} := by
  have hlaunch : MeasurableSet
      {z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p |
        ReferenceInitializationRun.launchRound
          (ReferenceLaunchJointFutureLaw.actualInput p ids rewards C_star C_h eta z) =
            σ.val + 1} :=
    (measurableSet_singleton (σ.val + 1)).preimage
      (ReferenceLaunchJointFutureLaw.measurable_sourceLaunchRound
        p ids rewards C_star C_h eta)
  have hpast : MeasurableSet
      {z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p |
        (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ z).1 ∈ A} :=
    hA.preimage
      (measurable_fst.comp (ReferenceLaunchJointFutureLaw.jointSplitEquiv p σ).measurable)
  have hassignment : MeasurableSet
      {z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p |
        originalAssignmentVectorAtLaunch p σ hσ z ∈ C} :=
    hC.preimage (measurable_originalAssignmentVectorAtLaunch p σ hσ)
  have hremainder : MeasurableSet
      {z : ReferenceLaunchJointFutureLaw.OriginalCoordinates p |
        exactRemainderAtLaunch p σ hσ z ∈ E} :=
    hE.preimage (measurable_exactRemainderAtLaunch p σ hσ)
  exact hlaunch.inter (hpast.inter (hassignment.inter hremainder))

/-- At the source sentinel there is no calendar or private future label, so
there is no assignment coordinate to call or split. This is exactly the
accepted empty-future fact. -/
theorem terminal_joint_future_labels_empty (p : Parameters) :
    IsEmpty (CompleteRowStoppingLaw.FutureIndex p
      (CompleteRowStoppingLaw.horizonStoppingIndex p)) ∧
    IsEmpty (ReferenceLaunchPrivateRoundLaw.FuturePlayerRoundLabel p
      (ReferenceLaunchPrivateRoundLaw.terminalLaunchIndex p)) :=
  ReferenceLaunchJointFutureLaw.joint_future_labels_at_terminal_isEmpty p

end Bandits.Support.LaunchAssignmentCoordinateSplit

end
