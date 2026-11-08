/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRankInstallationRecorderFoundation

/-!
# Reserved FAST observation and joint slice law at rank installation

This file connects the accepted actual rank-installation view to the reserved
FAST coordinate. It constructs the Borel optional reserved arm on the original
source, retains the canonical view's absence, and uses the existing same-slice
recorder/FAST law. The original-source history/output cylinder and proposal
factor are separate subsequent obligations.

Source evidence: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FastRewardSliceLaw
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceRankInstallationRecorderFoundation

namespace Bandits.Support.ReferenceRankInstallationRecorderFastLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "View" => ReferenceDownReception.ChoiceTimeView p rate.eta
local notation "SourceInput" =>
  ReferenceRankInstallationRecorderFoundation.SourceInput p
local notation "installEvent" =>
  ReferenceRankInstallationRecorderFoundation.installationEvent rate rewards C_star C_h
local notation "viewAt" =>
  ReferenceRankInstallationRecorderFoundation.actualInstallationView rate rewards C_star C_h
local notation "currentControl" => ReferenceSourceCurrentControlFreshness.u_t p
local notation "sliceLaw" => ContinuousControlSlice.sliceLaw p.m p.K
local notation "markerAt" =>
  ReferenceRankInstallationRecorderFoundation.actualMarker rate rewards C_star C_h

/-- The actual optional installation view paired with the reserved FAST
scalar from the same original current source control. -/
def actualReservedFastInput (t : Fin p.T) (z : SourceInput) :
    Option View × ContinuousCategorical.Scalar :=
  (viewAt t z,
    ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      (currentControl t z).1)

/-- The reserved FAST input is Borel on the original source. The view's
absence remains the literal absence of the actual installation readout. -/
theorem measurable_actualReservedFastInput (t : Fin p.T) :
    Measurable (actualReservedFastInput rate rewards C_star C_h t) := by
  have hs : Measurable (fun z : SourceInput =>
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (currentControl t z).1) :=
    (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast).comp
      (measurable_fst.comp (ReferenceSourceCurrentControlFreshness.measurable_u_t t))
  exact (ReferenceRankInstallationRecorderFoundation.measurable_actualInstallationView
      rate rewards C_star C_h t).prodMk hs

/-- Apply the existing local FAST sampler to an actual installation view and
the supplied current slice. This function is only called with validity proved
from the successful local installation producer. -/
def reservedFastAtView (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (x : ContinuousControlSlice.Slice p.m p.K) : FastArm v.payload.slowSet :=
  FastComplementLocality.sampleLocalFast p rate.eta.val valid.learning_rate_pos
    valid.learning_rate_le_source_cap v.payload.anchor v.payload.anchor_pos
    v.payload.slowSet v.complementWeights valid.current_weight_pos
    valid.anchor_le_current valid.current_le_twice_anchor
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x)

/-- Measurability of the reserved local draw for one fixed valid actual view. -/
theorem measurable_reservedFastAtView (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    Measurable (reservedFastAtView rate t v valid) :=
  (FastComplementLocality.measurable_sampleLocalFast p rate.eta.val
    valid.learning_rate_pos valid.learning_rate_le_source_cap v.payload.anchor
    v.payload.anchor_pos v.payload.slowSet v.complementWeights
    valid.current_weight_pos valid.anchor_le_current valid.current_le_twice_anchor).comp
      (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast)

private theorem payloadSlowSet_eq_assignmentSlowSet (v : View) :
    v.payload.slowSet =
      SnapshotRecordingKernel.assignmentSlowSet p v.payload.assignment := by
  apply Subtype.ext
  change v.payload.slowSet.1 =
    Finset.univ.image v.payload.assignment.assigned
  exact v.payload.assignment_image.symm

private theorem sourceWeights_restrict_complement (v : View) :
    v.complementWeights = fun j : FastArm v.payload.slowSet =>
      ReferenceFirstWindowNumericalStream.sourceWeights v.payload
        v.complementWeights j.1 := by
  funext j
  have hj : j.1 ∉ v.payload.slowSet.1 :=
    (Finset.mem_sdiff.mp j.2).2
  simp [ReferenceFirstWindowNumericalStream.sourceWeights, hj]

/-- The reserved local draw is pathwise the accepted canonical draw using the
source weight extension. Only the complement is consumed by FAST. -/
theorem reservedFastAtView_eq_sampleFast (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (x : ContinuousControlSlice.Slice p.m p.K) :
    reservedFastAtView rate t v valid x =
      CanonicalFastSampling.sampleFast p rate.eta.val valid.learning_rate_pos
        valid.learning_rate_le_source_cap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid)
        v.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x) := by
  let W := ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights
  let localW := fun j : FastArm v.payload.slowSet => W j.1
  have hlocalW : v.complementWeights = localW :=
    sourceWeights_restrict_complement rate v
  have hlocalPos : ∀ j : FastArm v.payload.slowSet, 0 < localW j :=
    fun j => ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid j.1
  have hlocalLower : ∀ j : FastArm v.payload.slowSet,
      v.payload.anchor j.1 ≤ localW j :=
    fun j => ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid j.1
  have hlocalUpper : ∀ j : FastArm v.payload.slowSet,
      localW j ≤ 2 * v.payload.anchor j.1 :=
    fun j => ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid j.1
  change FastComplementLocality.sampleLocalFast p rate.eta.val
    valid.learning_rate_pos valid.learning_rate_le_source_cap v.payload.anchor
    v.payload.anchor_pos v.payload.slowSet v.complementWeights
    valid.current_weight_pos valid.anchor_le_current valid.current_le_twice_anchor
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x) = _
  calc
    _ = FastComplementLocality.sampleLocalFast p rate.eta.val
        valid.learning_rate_pos valid.learning_rate_le_source_cap v.payload.anchor
        v.payload.anchor_pos v.payload.slowSet localW hlocalPos hlocalLower hlocalUpper
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x) := by
          exact FastComplementLocality.sampleLocalFast_eq_of_weights_eq p
            rate.eta.property rate.sourceCap v.payload.anchor v.payload.anchor_pos
            v.payload.slowSet v.complementWeights localW valid.current_weight_pos
            hlocalPos valid.anchor_le_current hlocalLower valid.current_le_twice_anchor
            hlocalUpper hlocalW (ContinuousControlSlice.coordinate
              ContinuousControlSlice.Label.fast x)
    _ = CanonicalFastSampling.sampleFast p rate.eta.val valid.learning_rate_pos
        valid.learning_rate_le_source_cap v.payload.anchor W v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) v.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x) := by
          exact FastComplementLocality.sampleLocalFast_eq_sampleFast p
            rate.eta.property rate.sourceCap v.payload.anchor W v.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
              v.complementWeights v.cutoff t valid)
            v.payload.slowSet (ContinuousControlSlice.coordinate
              ContinuousControlSlice.Label.fast x)

/-- The fixed-view reserved draw has the accepted `qGamma` marginal for the
anchor-filled source vector. The original numerical complement is identified
separately on the actual installation event below. -/
theorem reservedFastAtView_pushforward (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    (sliceLaw).map (reservedFastAtView rate t v valid) =
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
        rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) v.payload.slowSet).toMeasure := by
  have hfunction : reservedFastAtView rate t v valid =
      fun x => CanonicalFastSampling.sampleFast p rate.eta.val
        valid.learning_rate_pos valid.learning_rate_le_source_cap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) v.payload.slowSet
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast x) := by
    funext x
    exact reservedFastAtView_eq_sampleFast rate t v valid x
  rw [hfunction]
  change (sliceLaw).map
      (CanonicalFastSampling.sampleFast p rate.eta.val valid.learning_rate_pos
        valid.learning_rate_le_source_cap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) v.payload.slowSet ∘
          ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast) = _
  rw [← Measure.map_map
      (CanonicalFastSampling.measurable_sampleFast p rate.eta.val
        valid.learning_rate_pos valid.learning_rate_le_source_cap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) v.payload.slowSet)
      (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast),
    ContinuousControlSlice.map_coordinate,
    PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
  exact CanonicalFastSampling.uniform_map_sampleFast p rate.eta.val
    rate.eta.property rate.sourceCap v.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
    v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid) v.payload.slowSet

/-- The nested actual marker is never outer absent on the literal invocation
event; bottom remains a present recorder outcome. -/
theorem installationEvent_actualMarker_ne_absent (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput)
    (hz : z ∈ installEvent k t) : markerAt t z ≠ none := by
  obtain ⟨_, _, _, _, _, _, hmarker⟩ :=
    ReferenceRankInstallationRecorderFoundation.installationEvent_marker_formula
      rate rewards C_star C_h control0 k t z hz
  rw [hmarker]
  exact Option.some_ne_none _

private theorem reservedFastAtView_eq_livePair_snd (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (x : ContinuousControlSlice.Slice p.m p.K) :
    (reservedFastAtView rate t v valid x).1 =
      (FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
        rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid)
        v.payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot
          v.payload.assignment) x).2.1 := by
  rw [reservedFastAtView_eq_sampleFast rate t v valid x]
  have hslow := payloadSlowSet_eq_assignmentSlowSet rate v
  rw [hslow]
  rfl

/-- The fixed-view recorder/FAST output on one original continuous slice.
Both coordinates use the same slice. -/
def installationRecorderFastPair (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (x : ContinuousControlSlice.Slice p.m p.K) : Option (Fin p.K) × Fin p.K :=
  (ReferenceRankInstallationRecorderFoundation.installationRecordingMap
      rate t v valid x,
    (reservedFastAtView rate t v valid x).1)

private theorem sliceAssignmentSplit_symm_nonassignment
    (vector : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p)
    (c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
      (vector, d)) c.1 = d c := by
  have h := congrArg (fun z => z.2 c)
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).apply_symm_apply
      (vector, d))
  simpa [LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.assignmentLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply] using h

private theorem installationRecordingMap_eq_of_nonassignment
    (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (x y : ContinuousControlSlice.Slice p.m p.K)
    (hcoord : ∀ c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      x c.1 = y c.1) :
    ReferenceRankInstallationRecorderFoundation.installationRecordingMap
      rate t v valid x =
    ReferenceRankInstallationRecorderFoundation.installationRecordingMap
      rate t v valid y := by
  have hslot : CanonicalRecordingSlice.slotFromScalar
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot x) =
      CanonicalRecordingSlice.slotFromScalar
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot y) :=
    congrArg CanonicalRecordingSlice.slotFromScalar
      (hcoord ⟨ContinuousControlSlice.Label.slot,
        by simp [ContinuousControlSlice.Label.slot, ContinuousControlSlice.Label.assign]⟩)
  have hsourceScalar : ContinuousControlSlice.coordinate
      ContinuousControlSlice.Label.rec x = ContinuousControlSlice.coordinate
        ContinuousControlSlice.Label.rec y :=
    hcoord ⟨ContinuousControlSlice.Label.rec,
      by simp [ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.assign]⟩
  have hsource : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec x) =
    CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec y) :=
    congrArg (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m) hsourceScalar
  have hthin : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin x =
      ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin y :=
    hcoord ⟨ContinuousControlSlice.Label.thin,
      by simp [ContinuousControlSlice.Label.thin, ContinuousControlSlice.Label.assign]⟩
  have hpilot (i : Fin p.m) :
      PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) i x =
        PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) i y := by
    unfold PublicDiscreteDraws.pilotDraw
    exact congrArg (PublicDiscreteDraws.pilotFromScalar p.K
      (ConstructorDimensions.K_pos p))
      (hcoord ⟨ContinuousControlSlice.Label.pilot i,
        by simp [ContinuousControlSlice.Label.pilot,
          ContinuousControlSlice.Label.assign]⟩)
  have haction (i : Fin p.m) :
      SnapshotRecordingKernel.dataAction p
        (.live v.payload.assignment
          (ReferenceRankInstallationRecorderFoundation.installationSnapshot
            v.payload.assignment))
        rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) x i =
      SnapshotRecordingKernel.dataAction p
        (.live v.payload.assignment
          (ReferenceRankInstallationRecorderFoundation.installationSnapshot
            v.payload.assignment))
        rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) y i := by
    by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m
    · have huniv :
          (Finset.univ : Finset (ActiveRoundActions.Follower p.m)) ≠ ∅ := by
        have hm := p.two_le_m
        exact Finset.ne_empty_of_mem (Finset.mem_univ
          (⟨0, by simp only [PublicDiscreteDraws.followerCount]; omega⟩ :
            ActiveRoundActions.Follower p.m))
      simp [SnapshotRecordingKernel.dataAction, hi,
        ReferenceRankInstallationRecorderFoundation.installationSnapshot,
        huniv, hpilot]
    · simp [SnapshotRecordingKernel.dataAction, hi,
        ReferenceRankInstallationRecorderFoundation.installationSnapshot, hpilot]
  have hmask (i : Fin p.m) (j : Fin p.K) :
      CanonicalRecordingSlice.recordingMask (ConstructorDimensions.K_pos p) i j x =
        CanonicalRecordingSlice.recordingMask (ConstructorDimensions.K_pos p) i j y := by
    apply propext
    unfold CanonicalRecordingSlice.recordingMask
    constructor
    · intro hx ell hne
      rw [← hpilot ell]
      exact hx ell hne
    · intro hy ell hne
      rw [hpilot ell]
      exact hy ell hne
  have hthinval := congrArg Subtype.val hthin
  unfold ReferenceRankInstallationRecorderFoundation.installationRecordingMap
  unfold SnapshotRecordingKernel.recordingMap
  simp only [dite_eq_left (show True from trivial)]
  by_cases hx : CanonicalRecordingSlice.slotFromScalar
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot x) =
        PublicDiscreteDraws.dataSlot
  · have hy : CanonicalRecordingSlice.slotFromScalar
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot y) =
          PublicDiscreteDraws.dataSlot := by rw [← hslot]; exact hx
    simp only [dite_eq_left hx, dite_eq_left hy]
    rw [hsource]
    let src := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec y)
    have hactionAt := haction src
    rw [hactionAt]
    have hmaskAt := hmask src
      (SnapshotRecordingKernel.dataAction p
        (.live v.payload.assignment
          (ReferenceRankInstallationRecorderFoundation.installationSnapshot
            v.payload.assignment))
        rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid) y src)
    rw [hmaskAt, hthinval]
  · have hy : ¬ CanonicalRecordingSlice.slotFromScalar
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.slot y) =
          PublicDiscreteDraws.dataSlot := by
      intro h
      apply hx
      rw [hslot]
      exact h
    simp only [dite_eq_right hx, dite_eq_right hy]

private theorem installationRecorderFastPair_eq_of_nonassignment
    (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (x y : ContinuousControlSlice.Slice p.m p.K)
    (hcoord : ∀ c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      x c.1 = y c.1) :
    installationRecorderFastPair rate t v valid x =
      installationRecorderFastPair rate t v valid y := by
  apply Prod.ext
  · exact installationRecordingMap_eq_of_nonassignment rate t v valid x y hcoord
  · have hfast := hcoord ⟨ContinuousControlSlice.Label.fast,
      by simp [ContinuousControlSlice.Label.fast, ContinuousControlSlice.Label.assign]⟩
    simp only [installationRecorderFastPair, reservedFastAtView,
      ContinuousControlSlice.coordinate, hfast]

private theorem measurable_installationRecorderFastPair
    (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    Measurable (installationRecorderFastPair rate t v valid) := by
  have hrec : Measurable
      (ReferenceRankInstallationRecorderFoundation.installationRecordingMap
        rate t v valid) := by
    unfold ReferenceRankInstallationRecorderFoundation.installationRecordingMap
    exact SnapshotRecordingKernel.measurable_recordingMap p
      (.live v.payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot
          v.payload.assignment)) rate.eta.val rate.eta.property rate.sourceCap
      v.payload.anchor
      (ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights)
      v.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
        v.complementWeights v.cutoff t valid) true
  exact hrec.prodMk (measurable_subtype_coe.comp
    (measurable_reservedFastAtView rate t v valid))

/-- With the full assignment vector fixed, the pair still has the accepted
same-slice law: the actual unoccupied installation recorder and reserved FAST
read only non-assignment labels. -/
theorem installationRecorderFastPair_nonassignment_pushforward
    (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights)
    (vector : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
    (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).map
        (fun d => installationRecorderFastPair rate t v valid
          ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
            (vector, d))) =
      (sliceLaw).map (installationRecorderFastPair rate t v valid) := by
  let split := LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
  let pair := installationRecorderFastPair rate t v valid
  let g := fun d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
    pair (split.symm (vector, d))
  have hg : Measurable g := (measurable_installationRecorderFastPair rate t v valid).comp
    (split.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hsnd := (measurePreserving_snd
    (μ := ContinuousControlSlice.assignmentLaw p.K)
    (ν := LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p)).comp
      (LaunchAssignmentCoordinateSplit.measurePreserving_sliceAssignmentSplitEquiv p)
  have heq : g ∘ (Prod.snd ∘ split) = pair := by
    funext x
    apply installationRecorderFastPair_eq_of_nonassignment rate t v valid
      (split.symm (vector, (split x).2)) x
    intro c
    rw [sliceAssignmentSplit_symm_nonassignment vector (split x).2 c]
    have h := sliceAssignmentSplit_symm_nonassignment (split x).1
      (split x).2 c
    rw [split.symm_apply_apply] at h
    exact h.symm
  calc
    _ = ((sliceLaw).map (Prod.snd ∘ split)).map g := by rw [hsnd.map_eq]
    _ = (sliceLaw).map pair := by
      rw [Measure.map_map hg hsnd.measurable]
      exact congrArg (fun f => (sliceLaw).map f) heq
    _ = _ := rfl

/-- The fixed-view pair is the existing same-slice pushforward, followed by
forgetting only the dependent proof that the FAST arm lies in the complement.
No independence of recorder and FAST is used. -/
theorem installationRecorderFastPair_pushforward (t : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    (sliceLaw).map (installationRecorderFastPair rate t v valid) =
      (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val
        rate.eta.property rate.sourceCap v.payload.anchor
        (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights)
        v.payload.anchor_pos
        (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
          v.complementWeights v.cutoff t valid)
        (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
          v.complementWeights v.cutoff t valid)
        v.payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot
          v.payload.assignment)).map (fun q => (q.1, q.2.1)) := by
  let W := ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights
  let a := v.payload.assignment
  let snap := ReferenceRankInstallationRecorderFoundation.installationSnapshot a
  let pair := FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val
    rate.eta.property rate.sourceCap v.payload.anchor W v.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
      v.complementWeights v.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
      v.complementWeights v.cutoff t valid) a snap
  let project := fun q : Option (Fin p.K) × FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p a) => (q.1, q.2.1)
  have hslow : v.payload.slowSet =
      SnapshotRecordingKernel.assignmentSlowSet p a := payloadSlowSet_eq_assignmentSlowSet rate v
  have hpoint : installationRecorderFastPair rate t v valid = project ∘ pair := by
    funext x
    change
      (ReferenceRankInstallationRecorderFoundation.installationRecordingMap
          rate t v valid x,
        (reservedFastAtView rate t v valid x).1) =
        ((pair x).1, (pair x).2.1)
    apply Prod.ext
    · rfl
    · exact reservedFastAtView_eq_livePair_snd rate t v valid x
  have hpair : Measurable pair :=
    FastRewardSliceLaw.measurable_liveRecordingFastPair p rate.eta.val
      rate.eta.property rate.sourceCap v.payload.anchor W v.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
        v.complementWeights v.cutoff t valid) a snap
  have hproject : Measurable project :=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [hpoint]
  calc
    (sliceLaw).map (project ∘ pair) = ((sliceLaw).map pair).map project := by
      rw [Measure.map_map hproject hpair]
    _ = _ := rfl

/-- On the actual invocation event, the canonical view is present, its local
choice inputs are valid by the successful installation producer, the reserved
FAST output is the fast component of the same-slice pair, and the marker is
that pair's recorder component. -/
theorem installationEvent_actualReservedFast_pair (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput)
    (hz : z ∈ installEvent k t) :
    ∃ v : View,
      ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights,
        viewAt t z = some v ∧
        actualReservedFastInput rate rewards C_star C_h t z =
          (some v, ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (currentControl t z).1) ∧
        (reservedFastAtView rate t v valid ((currentControl t z).1)).1 =
          (FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
            rate.sourceCap v.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
              v.complementWeights)
            v.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
              v.complementWeights v.cutoff t valid)
            v.payload.assignment
            (ReferenceRankInstallationRecorderFoundation.installationSnapshot
              v.payload.assignment)
            ((currentControl t z).1)).2.1 ∧
        markerAt t z = some
          (FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
            rate.sourceCap v.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
              v.complementWeights)
            v.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
              v.complementWeights v.cutoff t valid)
            v.payload.assignment
            (ReferenceRankInstallationRecorderFoundation.installationSnapshot
              v.payload.assignment)
            ((currentControl t z).1)).1 := by
  obtain ⟨b, native, _hr, ht, hview, _hparameters, hmarker⟩ :=
    ReferenceRankInstallationRecorderFoundation.installationEvent_marker_formula
      rate rewards C_star C_h control0 k t z hz
  have hactualView : viewAt t z = some native.selected.view := by
    rw [ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
      rate rewards C_star C_h control0 k t z]
    exact hview
  have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      native.selected.view.payload native.selected.view.cutoff t
      native.selected.view.complementWeights := by
    rw [← ht]
    exact native.choiceInputsValid
  refine ⟨native.selected.view, hvalid, hactualView, ?_, ?_, ?_⟩
  · simp [actualReservedFastInput, hactualView]
  · exact reservedFastAtView_eq_livePair_snd rate t native.selected.view hvalid
      ((currentControl t z).1)
  · rw [hmarker]
    rfl

/-- The same-slice reserved FAST marginal at an actual installation uses the
original numerical calendar-replay weights on the full fast complement. The
anchor-filled source vector is only an extension on the slow set; the stated
equality is restricted to the actual complement. -/
theorem installationEvent_originalNumericalFastMarginal (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput)
    (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length) (v : View)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h p.T z = some L ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] ∧
      viewAt t z = some v ∧
      (sliceLaw).map (reservedFastAtView rate t v valid) =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property
          rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid) v.payload.slowSet).toMeasure ∧
      ∀ j : FastArm v.payload.slowSet,
        ReferenceFirstWindowNumericalStream.sourceWeights v.payload
          v.complementWeights j.1 = AssignmentScoreReconstruction.sourceWeightBase p ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
              j.1 b.val).1 := by
  obtain ⟨L, b, v, hL, hb, hview, hweights⟩ :=
    ReferenceRankInstallationRecorderFoundation.installationEvent_originalComplementWeights
      rate rewards C_star C_h k t z hz
  obtain ⟨v', valid, hview', _, _, _⟩ :=
    installationEvent_actualReservedFast_pair rate rewards C_star C_h control0 k t z hz
  have hv : v = v' := Option.some.inj (hview.symm.trans hview')
  subst v'
  refine ⟨L, b, v, valid, hL, hb, hview, ?_, ?_⟩
  · exact reservedFastAtView_pushforward rate t v valid
  · intro j
    have hrestrict := congrFun (sourceWeights_restrict_complement rate v) j
    rw [← hrestrict]
    exact hweights j

/-- On the actual fast complement, the accepted qGamma mass is computed from
the same original numerical calendar-replay weights. This uses the
complement-local FAST law, so it makes no claim that slow-set extension values
equal the original numerical weights. -/
theorem installationEvent_originalComplement_qGamma_eq_localFastLaw
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput) (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length) (v : View)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights),
      (∀ j : FastArm v.payload.slowSet,
        v.complementWeights j = AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.1 b.val).1) ∧
      (∀ hweights : ∀ j : FastArm v.payload.slowSet,
        v.complementWeights j = AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.1 b.val).1,
       ∀ j : FastArm v.payload.slowSet,
        CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
            valid.learning_rate_le_source_cap v.payload.anchor
            (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
              v.complementWeights)
            v.payload.anchor_pos
            (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
              v.complementWeights v.cutoff t valid)
            (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
              v.complementWeights v.cutoff t valid) v.payload.slowSet j =
          FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
            valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
            (fun j => AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
                j.1 b.val).1)
            v.payload.anchor_pos
            (fun j => by rw [← hweights j]; exact valid.current_weight_pos j)
            (fun j => by rw [← hweights j]; exact valid.anchor_le_current j)
            (fun j => by rw [← hweights j]; exact valid.current_le_twice_anchor j)
            j) := by
  obtain ⟨L, b, v, valid, _hprefix, _hrecord, _hview, _hpush, hweights⟩ :=
    installationEvent_originalNumericalFastMarginal rate rewards C_star C_h control0 k t z hz
  refine ⟨L, b, v, valid, ?_, ?_⟩
  · intro j
    have hrestrict := congrFun (sourceWeights_restrict_complement rate v) j
    calc
      v.complementWeights j =
          ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights j.1 := hrestrict
      _ = AssignmentScoreReconstruction.sourceWeightBase p ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
            j.1 b.val).1 := hweights j
  · intro hweights j
    let W := ReferenceFirstWindowNumericalStream.sourceWeights v.payload v.complementWeights
    let numerical := fun j : FastArm v.payload.slowSet =>
      AssignmentScoreReconstruction.sourceWeightBase p ^
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
          j.1 b.val).1
    have hW : (fun j : FastArm v.payload.slowSet => W j.1) = numerical := by
      funext j
      have hrestrict := congrFun (sourceWeights_restrict_complement rate v) j
      calc
        W j.1 = v.complementWeights j := hrestrict.symm
        _ = numerical j := by
          rw [hweights j]
    have hq := FastComplementLocality.localFastLaw_eq_qGamma p
      valid.learning_rate_pos valid.learning_rate_le_source_cap
      v.payload.anchor W v.payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
        v.complementWeights v.cutoff t valid)
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
        v.complementWeights v.cutoff t valid) v.payload.slowSet j
    calc
      CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
          valid.learning_rate_le_source_cap v.payload.anchor W
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid) v.payload.slowSet j =
        FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
          valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
          (fun j => W j.1) v.payload.anchor_pos
          (fun j => ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid j.1)
          (fun j => ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid j.1)
          (fun j => ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid j.1) j := hq.symm
      _ = FastComplementLocality.localFastLaw p rate.eta.val rate.eta.property
          valid.learning_rate_le_source_cap v.payload.anchor v.payload.slowSet
          numerical v.payload.anchor_pos
          (fun j => by
            change 0 < AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
                j.1 b.val).1
            rw [← hweights j]
            exact valid.current_weight_pos j)
          (fun j => by
            change v.payload.anchor j.1 ≤ AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
                j.1 b.val).1
            rw [← hweights j]
            exact valid.anchor_le_current j)
          (fun j => by
            change AssignmentScoreReconstruction.sourceWeightBase p ^
              (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L
                j.1 b.val).1 ≤ 2 * v.payload.anchor j.1
            rw [← hweights j]
            exact valid.current_le_twice_anchor j) j := by
        unfold FastComplementLocality.localFastLaw
          FastComplementLocality.localConditionalFastMass
          FastComplementLocality.localFastCandidateMass
          FastComplementLocality.localFastNormalizer
        rw [hW]

/-- On an actual rank-installation invocation, disintegrating the unreduced
current remainder at the retained strict prefix, earlier marks, and complete
assignment vector gives the same-slice recorder/reserved-FAST law. All
non-assignment scalars and all affine samples remain under their original
product law. -/
theorem installationEvent_actualRemainder_joint_pushforward
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput) (hz : z ∈ installEvent k t) :
    ∃ v : View,
      ∃ valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
        v.complementWeights,
      viewAt t z = some v ∧
      ReferenceRankInstallationRecorderFoundation.viewFromHistory
          rate rewards C_star C_h control0 t
          (ReferenceRankInstallationRecorderFoundation.history
            rate rewards C_star C_h control0 k t z) = some v ∧
      (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        (fun d => installationRecorderFastPair rate t v valid
          ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
            (ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z,
              d.1))) =
        (FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val
          rate.eta.property rate.sourceCap v.payload.anchor
          (ReferenceFirstWindowNumericalStream.sourceWeights v.payload
            v.complementWeights)
          v.payload.anchor_pos
          (ReferenceFirstWindowNumericalStream.sourceWeights_pos v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_lower v.payload
            v.complementWeights v.cutoff t valid)
          (ReferenceFirstWindowNumericalStream.sourceWeights_upper v.payload
            v.complementWeights v.cutoff t valid)
          v.payload.assignment
          (ReferenceRankInstallationRecorderFoundation.installationSnapshot
            v.payload.assignment)).map (fun q => (q.1, q.2.1)) := by
  obtain ⟨v, valid, hview, _, _, _⟩ :=
    installationEvent_actualReservedFast_pair rate rewards C_star C_h control0 k t z hz
  let vector := ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z
  let split := LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
  let pair := installationRecorderFastPair rate t v valid
  let g := fun d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
    pair (split.symm (vector, d))
  have hg : Measurable g :=
    (measurable_installationRecorderFastPair rate t v valid).comp
      (split.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hmap := installationRecorderFastPair_nonassignment_pushforward
    rate t v valid vector
  have hhistoryView :=
    (ReferenceRankInstallationRecorderFoundation.actualInstallationView_eq_history
      rate rewards C_star C_h control0 k t z).symm.trans hview
  refine ⟨v, valid, hview, hhistoryView, ?_⟩
  calc
    _ = ((ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
        Prod.fst).map g := by
      change (ReferenceLaterOptionalControlResampling.controlRemainderLaw p).map
          (g ∘ Prod.fst) = _
      rw [Measure.map_map hg measurable_fst]
    _ = _ := by
      rw [ReferenceLaterOptionalControlResampling.controlRemainderLaw,
        Measure.map_fst_prod, measure_univ, one_smul, hmap,
        installationRecorderFastPair_pushforward rate t v valid]

/-- Apply the admitted actual-remainder reconstruction to obtain the exact
original numerical complement vector at the same actual installation record,
rank, and view. The assignment coordinates on the slow set are not identified
with this vector by this statement. -/
theorem installationEvent_originalComplementWeights (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput)
    (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)
      ) (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length) (v : View),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h p.T z = some L ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
        some (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val] ∧
      viewAt t z = some v ∧
      ∀ j, v.complementWeights j = AssignmentScoreReconstruction.sourceWeightBase p ^
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.val b.val).1 := by
  obtain ⟨L, b, v, _valid, hL, hb, hv, _hlaw, hw⟩ :=
    installationEvent_originalNumericalFastMarginal rate rewards C_star C_h control0 k t z hz
  refine ⟨L, b, v, hL, hb, hv, ?_⟩
  intro j
  exact (congrFun (sourceWeights_restrict_complement rate v) j).trans (hw j)

/-- Every replacement of the current remainder that fixes the whole
assignment vector preserves both the actual invocation event and its
canonical installed view. -/
theorem installationEvent_remainder_view_invariant (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput)
    (hz : z ∈ installEvent k t) (c : TimeControl p)
    (hvector : ContinuousControlSlice.assignmentVector c.1 =
      ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c ∈
          installEvent k t ∧
      viewAt t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) =
          viewAt t z := by
  constructor
  · exact (ReferenceRankInstallationRecorderFoundation.installationEvent_replaceSourceControl
      rate rewards C_star C_h control0 k t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c).mpr
        ((ReferenceRankInstallationRecorderFoundation.installationEvent_sourcePrefix
          rate rewards C_star C_h control0 k t z).mpr hz)
  · exact ReferenceRankInstallationRecorderFoundation.actualInstallationView_replace
      rate rewards C_star C_h control0 t z c hvector


local instance reservedMarkerMeasurableSpace :
    MeasurableSpace (Option (Option (Fin p.K))) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The reserved draw on a present local view, retaining the local input-check
failure as absence. This uses the FAST scalar even when physical play is pilot. -/
def reservedFastObservation (t : Fin p.T) (q : View × ContinuousCategorical.Scalar) :
    Option (Fin p.K) := by
  classical
  exact if valid : CoordinatorLocalArmChoice.ChoiceInputsValid q.1.payload q.1.cutoff t
      q.1.complementWeights then
    some (FastComplementLocality.sampleLocalFast p rate.eta.val
      valid.learning_rate_pos valid.learning_rate_le_source_cap q.1.payload.anchor
      q.1.payload.anchor_pos q.1.payload.slowSet q.1.complementWeights
      valid.current_weight_pos valid.anchor_le_current valid.current_le_twice_anchor q.2).1
  else none

private theorem measurable_varyingCategorical {X : Type*} [MeasurableSpace X]
    {n : ℕ} (hn : 0 < n) (mass : X → Fin n → ℝ)
    (hmass : ∀ i, Measurable (fun x => mass x i))
    (hsum : ∀ x, ∑ i, mass x i = 1)
    (scalar : X → ContinuousCategorical.Scalar) (hscalar : Measurable scalar) :
    Measurable (fun x => ContinuousCategorical.sample hn (mass x) (hsum x) (scalar x)) := by
  classical
  apply measurable_to_countable'
  intro i
  have hupper (j : Fin n) : Measurable (fun x => ContinuousCategorical.upper (mass x) j) :=
    Finset.measurable_fun_sum _ fun k _ => hmass k
  have hfiber : (fun x => ContinuousCategorical.sample hn (mass x) (hsum x) (scalar x)) ⁻¹'
      {i} = {x | (scalar x).val < ContinuousCategorical.upper (mass x) i} ∩
        ⋂ j : Fin n, {x | j < i → ContinuousCategorical.upper (mass x) j ≤ (scalar x).val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_iInter]
    exact ContinuousCategorical.sample_eq_iff_least hn (mass x) (hsum x) (scalar x) i
  rw [hfiber]
  apply (measurableSet_lt (measurable_subtype_coe.comp hscalar) (hupper i)).inter
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j < i
  · simpa only [hj, true_implies, Function.comp_def] using
      measurableSet_le (hupper j) (measurable_subtype_coe.comp hscalar)
  · simp only [hj, false_implies, Set.ofPred_true, MeasurableSet.univ]

private abbrev ValidReservedFastInput (t : Fin p.T) :=
  {q : View × ContinuousCategorical.Scalar //
    CoordinatorLocalArmChoice.ChoiceInputsValid q.1.payload q.1.cutoff t q.1.complementWeights}

private def vectorFastMass (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (i : Fin (p.K - p.m + 1)) (z : (Fin p.K → ℝ) × (Fin p.K → ℝ)) : ℝ :=
  (1 - CanonicalRecordingRates.gamma p rate.eta.val) *
    ((z.2 (CanonicalFastSampling.fastArmOrderIso U i).val /
      (1 + FiniteOrientationDisintegration.inverseAnchorSum z.1 U.val *
        z.1 (CanonicalFastSampling.fastArmOrderIso U i).val)) /
      ∑ j : FastArm U, z.2 j.val /
        (1 + FiniteOrientationDisintegration.inverseAnchorSum z.1 U.val * z.1 j.val)) +
    CanonicalRecordingRates.gamma p rate.eta.val / ((p.K - p.m + 1 : ℕ) : ℝ)

private theorem measurable_vectorFastMass (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (i : Fin (p.K - p.m + 1)) : Measurable (vectorFastMass rate U i) := by
  have hinv : Measurable (fun z : (Fin p.K → ℝ) × (Fin p.K → ℝ) =>
      FiniteOrientationDisintegration.inverseAnchorSum z.1 U.val) := by
    unfold FiniteOrientationDisintegration.inverseAnchorSum
    exact Finset.measurable_fun_sum _ fun j _ =>
      measurable_const.div ((measurable_pi_apply j).comp measurable_fst)
  have hc (j : FastArm U) : Measurable
      (fun z : (Fin p.K → ℝ) × (Fin p.K → ℝ) =>
        z.2 j.val / (1 + FiniteOrientationDisintegration.inverseAnchorSum z.1 U.val *
          z.1 j.val)) :=
    ((measurable_pi_apply j.val).comp measurable_snd).div
      (measurable_const.add (hinv.mul ((measurable_pi_apply j.val).comp measurable_fst)))
  exact (measurable_const.mul ((hc (CanonicalFastSampling.fastArmOrderIso U i)).div
    (Finset.measurable_fun_sum _ fun j _ => hc j))).add measurable_const

private def validReservedFastMass (t : Fin p.T) (q : ValidReservedFastInput rate t)
    (i : Fin (p.K - p.m + 1)) : ℝ :=
  FastComplementLocality.localFastLaw p rate.eta.val
    q.property.learning_rate_pos q.property.learning_rate_le_source_cap
    q.val.1.payload.anchor q.val.1.payload.slowSet q.val.1.complementWeights
    q.val.1.payload.anchor_pos q.property.current_weight_pos
    q.property.anchor_le_current q.property.current_le_twice_anchor
    (CanonicalFastSampling.fastArmOrderIso q.val.1.payload.slowSet i)

private theorem measurable_validReservedFastMass (t : Fin p.T)
    (i : Fin (p.K - p.m + 1)) :
    Measurable (fun q : ValidReservedFastInput rate t => validReservedFastMass rate t q i) := by
  have hv : Measurable (fun q : ValidReservedFastInput rate t => q.val.1) :=
    measurable_fst.comp measurable_subtype_coe
  have hobs := (comap_measurable
    (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (rate := rate))).comp hv
  have hp : Measurable (fun q : ValidReservedFastInput rate t => q.val.1.payload) :=
    measurable_fst.comp hobs
  have ha : Measurable (fun q : ValidReservedFastInput rate t => q.val.1.payload.anchor) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp hp
  have hw : Measurable (fun q : ValidReservedFastInput rate t =>
      ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector q.val.1) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hobs))
  have hU : Measurable (fun q : ValidReservedFastInput rate t => q.val.1.payload.slowSet) :=
    ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp hp
  let f : ((Fin p.K → ℝ) × (Fin p.K → ℝ)) ×
      CanonicalOrientedSetLaw.SlowSet p.K p.m → ℝ := fun z => vectorFastMass rate z.2 i z.1
  have hf : Measurable f :=
    measurable_from_prod_countable_left fun U => measurable_vectorFastMass rate U i
  have heq : (fun q : ValidReservedFastInput rate t => validReservedFastMass rate t q i) =
      fun q => f ((q.val.1.payload.anchor,
        ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector q.val.1),
          q.val.1.payload.slowSet) := by
    funext q
    have hwj (j : FastArm q.val.1.payload.slowSet) :
        ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector q.val.1 j.val =
          q.val.1.complementWeights j := by
      simp only [ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector,
        dite_eq_left j.property]
    dsimp only [validReservedFastMass, f, vectorFastMass]
    unfold FastComplementLocality.localFastLaw FastComplementLocality.localConditionalFastMass
      FastComplementLocality.localFastNormalizer FastComplementLocality.localFastCandidateMass
    simp only [hwj]
  rw [heq]
  exact hf.comp ((ha.prodMk hw).prodMk hU)

private theorem validReservedFastMass_sum (t : Fin p.T)
    (q : ValidReservedFastInput rate t) : ∑ i, validReservedFastMass rate t q i = 1 :=
  (Equiv.sum_comp (CanonicalFastSampling.fastArmOrderIso q.val.1.payload.slowSet).toEquiv _).trans
    (FastComplementLocality.localFastLaw_sum_eq_one p q.property.learning_rate_pos
      q.property.learning_rate_le_source_cap q.val.1.payload.anchor q.val.1.payload.anchor_pos
      q.val.1.payload.slowSet q.val.1.complementWeights q.property.current_weight_pos
      q.property.anchor_le_current q.property.current_le_twice_anchor)

private def validReservedFastArm (t : Fin p.T) (q : ValidReservedFastInput rate t) : Fin p.K :=
  (FastComplementLocality.sampleLocalFast p rate.eta.val
    q.property.learning_rate_pos q.property.learning_rate_le_source_cap
    q.val.1.payload.anchor q.val.1.payload.anchor_pos q.val.1.payload.slowSet
    q.val.1.complementWeights q.property.current_weight_pos
    q.property.anchor_le_current q.property.current_le_twice_anchor q.val.2).val

private theorem validReservedFastArm_eq_index (t : Fin p.T)
    (q : ValidReservedFastInput rate t) (hn : 0 < p.K - p.m + 1) :
    validReservedFastArm rate t q =
      (CanonicalFastSampling.fastArmOrderIso q.val.1.payload.slowSet
        (ContinuousCategorical.sample hn (validReservedFastMass rate t q)
          (validReservedFastMass_sum rate t q) q.val.2)).val := rfl

private theorem measurable_validReservedFastArm (t : Fin p.T) :
    Measurable (validReservedFastArm rate t) := by
  have hU : Measurable (fun q : ValidReservedFastInput rate t => q.val.1.payload.slowSet) :=
    ReferenceCollectionDispatchMeasurability.measurable_payloadSlowSet.comp
      (measurable_fst.comp ((comap_measurable
        (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (rate := rate))).comp
          (measurable_fst.comp measurable_subtype_coe)))
  have hn : 0 < p.K - p.m + 1 := by omega
  have hdraw := measurable_varyingCategorical hn (validReservedFastMass rate t)
    (measurable_validReservedFastMass rate t) (validReservedFastMass_sum rate t)
    (fun q : ValidReservedFastInput rate t => q.val.2)
    (measurable_snd.comp measurable_subtype_coe)
  let decode : CanonicalOrientedSetLaw.SlowSet p.K p.m × Fin (p.K - p.m + 1) → Fin p.K :=
    fun q => (CanonicalFastSampling.fastArmOrderIso q.1 q.2).val
  have hd : Measurable decode := measurable_of_countable _
  have heq : validReservedFastArm rate t = fun q => decode
      (q.val.1.payload.slowSet, ContinuousCategorical.sample hn (validReservedFastMass rate t q)
        (validReservedFastMass_sum rate t q) q.val.2) :=
    funext fun q => validReservedFastArm_eq_index rate t q hn
  rw [heq]
  exact hd.comp (hU.prodMk hdraw)

/-- Joint Borelness includes varying real anchors and complement weights.
Only the finite slow-set key is discrete; the sampler remains the accepted
local inverse CDF on its genuine continuous scalar. -/
theorem measurable_reservedFastObservation (t : Fin p.T) :
    Measurable (reservedFastObservation rate t) := by
  classical
  let s : Set (View × ContinuousCategorical.Scalar) :=
    {q | CoordinatorLocalArmChoice.ChoiceInputsValid q.1.payload q.1.cutoff t
      q.1.complementWeights}
  have hbit : Measurable (fun q : View × ContinuousCategorical.Scalar =>
      ReferenceDownReceptionMeasurability.choiceInputsValidBit q.1 t) :=
    ReferenceDownReceptionMeasurability.measurable_choiceInputsValid.comp
      (measurable_fst.prodMk measurable_const)
  have hs : MeasurableSet s := by
    have heq : s = (fun q : View × ContinuousCategorical.Scalar =>
        ReferenceDownReceptionMeasurability.choiceInputsValidBit q.1 t) ⁻¹' {true} := by
      ext q
      simp only [s, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff,
        ReferenceDownReceptionMeasurability.choiceInputsValidBit, decide_eq_true_eq]
    rw [heq]
    exact hbit (measurableSet_singleton true)
  unfold reservedFastObservation
  exact Measurable.dite
    ((measurable_of_countable (some : Fin p.K → Option (Fin p.K))).comp
      (measurable_validReservedFastArm rate t))
    measurable_const hs

/-- The canonical optional arm observation on the original source. Neither
an arbitrary view nor a chosen successful representative is supplied. -/
def actualReservedFast (t : Fin p.T) (z : SourceInput) : Option (Fin p.K) :=
  (viewAt t z).bind fun v => reservedFastObservation rate t
    (v, ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      (currentControl t z).1)

/-- Literal pairing with the actual nested-option recorder on the same source. -/
def actualMarkerReservedFast (t : Fin p.T) (z : SourceInput) :
    Option (Option (Fin p.K)) × Option (Fin p.K) :=
  (markerAt t z, actualReservedFast rate rewards C_star C_h t z)

/-- Borelness of the optional reserved arm for the actual varying view. -/
theorem measurable_actualReservedFast (t : Fin p.T) :
    Measurable (actualReservedFast rate rewards C_star C_h t) := by
  let X := Option View × ContinuousCategorical.Scalar
  let e := MeasurableEquiv.sumProdDistrib View PUnit ContinuousCategorical.Scalar
  let left : View × ContinuousCategorical.Scalar → Option (Fin p.K) :=
    reservedFastObservation rate t
  let right : PUnit × ContinuousCategorical.Scalar → Option (Fin p.K) := fun _ => none
  have hlift : Measurable (fun q : X =>
      Sum.elim left right (e (Equiv.optionEquivSumPUnit View q.1, q.2))) :=
    ((measurable_reservedFastObservation rate t).sumElim measurable_const).comp
      (e.measurable.comp
        ((comap_measurable (Equiv.optionEquivSumPUnit View)).prodMap measurable_id))
  have heq : actualReservedFast rate rewards C_star C_h t = fun z =>
      Sum.elim left right (e
        (Equiv.optionEquivSumPUnit View (viewAt t z),
          ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (currentControl t z).1)) := by
    funext z
    unfold actualReservedFast
    cases hv : viewAt t z <;> rfl
  rw [heq]
  exact hlift.comp (measurable_actualReservedFastInput rate rewards C_star C_h t)

/-- Both readouts are Borel on the original source, with recorder bottom and
outer absence still distinct. -/
theorem measurable_actualMarkerReservedFast (t : Fin p.T) :
    Measurable (actualMarkerReservedFast rate rewards C_star C_h t) :=
  (ReferenceRankInstallationRecorderFoundation.measurable_actualMarker
    rate rewards C_star C_h t).prodMk
      (measurable_actualReservedFast rate rewards C_star C_h t)

open ReferenceActivePhysicalStep
open ReferenceCollectionDispatchMeasurability
open ReferenceCollectionInstallOutputMeasurability
open ReferenceCollectionOutcomeMeasurability

private theorem installationViewOnInput_pending_empty
    (x : RoundInput p rate) (v : View)
    (hv : installationViewOnInput rate x = some v) :
    ∃ P l saved, x.state.coordinator = .collection P l saved ∧ l.pending = ∅ := by
  classical
  cases hstate : x.state.coordinator with
  | first =>
      simp only [installationViewOnInput, canonicalCollectionFullObservation, hstate,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, collectionCoordinates?,
        mapOptional, Option.map_none, optionalElim] at hv
      cases hv
  | live registers owned base =>
      simp only [installationViewOnInput, canonicalCollectionFullObservation, hstate,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, collectionCoordinates?,
        mapOptional, Option.map_none, optionalElim] at hv
      cases hv
  | dagger =>
      simp only [installationViewOnInput, canonicalCollectionFullObservation, hstate,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator, collectionCoordinates?,
        mapOptional, Option.map_none, optionalElim] at hv
      cases hv
  | collection P l saved =>
      refine ⟨P, l, saved, rfl, ?_⟩
      by_contra hpending
      have hne := Finset.nonempty_iff_ne_empty.mpr hpending
      by_cases hb : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T
      · let u : Fin p.T := ⟨l.cutoff - 1, by omega⟩
        have hu : u.val + 1 = l.cutoff := by dsimp only [u]; omega
        rw [installationViewOnInput_collection rate x P l saved hstate u hu] at hv
        unfold installationPrechoiceView laterInstalledObservation? at hv
        split at hv
        · unfold laterInstalledAtClock at hv
          split at hv
          · cases hv
          · simp only [hne, ite_true, Option.map_none] at hv
            cases hv
        · cases hv
      · have hinvalid : ¬ cutoffValid
            ((P, x.row), l, saved, x.state.upDecoderBank, x.time) := hb
        rw [installationViewOnInput,
          canonicalCollectionFullObservation_collection x P l saved hstate] at hv
        simp only [optionalElim, boundaryFullObservation, dite_eq_right hinvalid,
          Sum.elim_inl] at hv
        cases hv

/-- Every present canonical installation view on the original source has
valid choice inputs. Validity comes from the same successful local producer,
including its real complement envelope and clock, without a success premise. -/
theorem actualInstallationView_valid (t : Fin p.T) (z : SourceInput)
    (v : View) (hv : viewAt t z = some v) :
    CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t v.complementWeights := by
  change ((ReferenceSourcePrefixHistoryFiltration.actualRecord
    rate rewards C_star C_h t z).bind (fun r => installationViewOnInput rate r.input)) =
      some v at hv
  obtain ⟨r, hr, hv⟩ := Option.bind_eq_some_iff.mp hv
  obtain ⟨b, hb⟩ := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
    rate rewards C_star C_h t z r hr
  have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z r hr).2.2.1
  rw [← hb] at ht hv
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  obtain ⟨P, l, saved, hstate, hpending⟩ :=
    installationViewOnInput_pending_empty rate R[b.val].input v hv
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z b
  dsimp only at hstep
  rw [hstate] at hstep
  dsimp only at hstep
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, _hkind,
    consistent, output, hlocal, hsuccess, clockData, installed, arm, hinstall,
    hresult, _hdispatch, _hprepared, _⟩ := hstep hpending
  subst installed
  let localInput : LocalInput p rate :=
    ((P, R[b.val].input.row), l, saved, R[b.val].input.state.upDecoderBank,
      R[b.val].input.time, u)
  let checked : CoreInput p rate := ⟨localInput, core⟩
  have hcons : consistent = localConsistency checked := by
    cases consistent with
    | mk hstart hassignment oldFreeze hfreeze =>
        have he : oldFreeze = l.freezeAt := hfreeze
        subst oldFreeze
        rfl
  have hlocal' : output.localConsistency = localConsistency checked := hlocal.trans hcons
  have hsuccess' : LaterAssignmentStartOperation.laterAssignmentStart P
      (operationLedger checked) instruction R[b.val].input.row (localConsistency checked) =
        .success output hlocal' := by
    cases hcons
    exact hsuccess
  have hobs := laterInstalledObservation?_of_actual_success checked started hstart
    (by rw [hpending]; exact Finset.not_nonempty_empty) instruction hassignment
    output hlocal' hsuccess'
  have hgenerated := congrArg (Option.map (fun c : InstalledObservation p rate => c.2.1)) hobs
  change installationPrechoiceView rate localInput = some
    (installedView (installationCoordinates (output.payload, output.baseScore) l instruction started)
      started) at hgenerated
  have hvactual := installedView_eq_actual checked instruction output clockData
  dsimp only at hvactual
  rw [hresult] at hvactual
  rw [installationViewOnInput_collection rate R[b.val].input P l saved hstate u hu] at hv
  have heq := Option.some.inj (hv.symm.trans hgenerated)
  rw [heq, hvactual]
  change CoordinatorLocalArmChoice.ChoiceInputsValid
    (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) t
    (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights
  rw [← ht, ← htime]
  exact arm.choiceInputsValid

/-- On any valid present canonical view, the global readout is precisely the
reserved local draw with the original current FAST coordinate. -/
theorem actualReservedFast_eq_of_view (t : Fin p.T) (z : SourceInput)
    (v : View) (hv : viewAt t z = some v)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff t
      v.complementWeights) :
    actualReservedFast rate rewards C_star C_h t z =
      some (reservedFastAtView rate t v valid ((currentControl t z).1)).val := by
  simp only [actualReservedFast, hv, Option.bind_some, reservedFastObservation,
    dite_eq_left valid, reservedFastAtView]

/-- The original-source evaluation needs no supplied validity certificate:
the same canonical producer supplies every local FAST input check. -/
theorem actualReservedFast_eq_some_of_view (t : Fin p.T) (z : SourceInput)
    (v : View) (hv : viewAt t z = some v) :
    actualReservedFast rate rewards C_star C_h t z =
      some (reservedFastAtView rate t v
        (actualInstallationView_valid rate rewards C_star C_h t z v hv)
        ((currentControl t z).1)).val :=
  actualReservedFast_eq_of_view rate rewards C_star C_h t z v hv
    (actualInstallationView_valid rate rewards C_star C_h t z v hv)

/-- Actual-source absence is precisely absence of the canonical installation
view. The checked invalid branch cannot occur on a present actual view. -/
theorem actualReservedFast_eq_none_iff (t : Fin p.T) (z : SourceInput) :
    actualReservedFast rate rewards C_star C_h t z = none ↔ viewAt t z = none := by
  cases hv : viewAt t z with
  | none => simp only [actualReservedFast, hv, Option.bind_none]
  | some v =>
      rw [actualReservedFast_eq_some_of_view rate rewards C_star C_h t z v hv]
      simp only [Option.some_ne_none]

/-- At the actual rank invocation, the Borel pair is the literal same-slice
recording map and reserved FAST draw. No product of their marginals is used. -/
theorem installationEvent_actualMarkerReservedFast (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput) (hz : z ∈ installEvent k t) :
    ∃ (v : View) (valid : CoordinatorLocalArmChoice.ChoiceInputsValid
        v.payload v.cutoff t v.complementWeights),
      viewAt t z = some v ∧
      actualMarkerReservedFast rate rewards C_star C_h t z =
        (some (installationRecorderFastPair rate t v valid ((currentControl t z).1)).1,
          some (installationRecorderFastPair rate t v valid ((currentControl t z).1)).2) := by
  obtain ⟨v, valid, hv, _, _hfast, hmarker⟩ :=
    installationEvent_actualReservedFast_pair rate rewards C_star C_h control0 k t z hz
  refine ⟨v, valid, hv, ?_⟩
  apply Prod.ext
  · exact hmarker
  · exact actualReservedFast_eq_of_view rate rewards C_star C_h t z v hv valid

/-- The reserved arm has no outer absence on the actual invocation event,
including installations whose physical action does not consume FAST. -/
theorem installationEvent_actualReservedFast_ne_none (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput) (hz : z ∈ installEvent k t) :
    actualReservedFast rate rewards C_star C_h t z ≠ none := by
  obtain ⟨v, _valid, hv, _⟩ :=
    installationEvent_actualMarkerReservedFast rate rewards C_star C_h control0 k t z hz
  rw [actualReservedFast_eq_some_of_view rate rewards C_star C_h t z v hv]
  exact Option.some_ne_none _

end Bandits.Support.ReferenceRankInstallationRecorderFastLaw

end
