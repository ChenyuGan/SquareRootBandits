/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalExpectedLearningBound

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Original-source first-launch auxiliary reward

The actual first launch is read on its original unnormalized source stratum.
Its complete assignment vector and nonassignment coordinates remain in the
source-coordinate product; the reserved fast scalar is the original `fast`
label. This module treats only the birth contribution.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SlowSet (K m : ℕ) := CanonicalOrientedSetLaw.SlowSet K m
abbrev FastArm {p : Parameters} (U : SlowSet p.K p.m) := CanonicalFastSampling.FastArm U

local instance slowSetMeasurableSpace (K m : ℕ) : MeasurableSpace (SlowSet K m) := ⊤

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p))
  (t : Fin p.T) (control0 : ContinuousLearningRows.TimeControl p)

local notation "i₀" => ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t i₀
local notation "X" => ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
  rate rewards C_star C_h q t control0
local notation "V" => ReferenceFirstLaunchRecordingSourceLaw.AssignmentVector p
local notation "Dctl" => ReferenceFirstLaunchRecordingSourceLaw.NonAssignmentControl p
local notation "muZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t i₀
local notation "muC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "coords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h q t control0

/-- The denominator-normalized whole reward vector at this birth round. -/
public def birthRewardRate : Fin p.K → ℝ :=
  fun i => ((rewards t i).val : ℝ) / (ConstructorDimensions.D p : ℝ)

/-- The actual first-launch payload, evaluated on the original retained point
and the complete original assignment/nonassignment coordinates. -/
public def actualFirstPayload (z : Z) : ReferenceActivePhysicalStep.Payload rate :=
  ReferenceFirstLaunchRecordingPhysicalMarker.payload rate rewards C_star C_h q t control0
    (coords z).1 (coords z).2.1 (coords z).2.2

/-- The actual slow set assigned at the first launch. -/
public def actualFirstSlowSet (z : Z) : SlowSet p.K p.m :=
  SnapshotRecordingKernel.assignmentSlowSet p (actualFirstPayload rate rewards C_star C_h q t control0 z).assignment

private def firstFastLabel : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p :=
  ⟨ContinuousControlSlice.Label.fast, by
    rintro ⟨r, h⟩
    simp [ContinuousControlSlice.Label.fast, ContinuousControlSlice.Label.assign] at h⟩

/-- The fast scalar in the original nonassignment slice. -/
private def fastScalarOfRemainder (d : Dctl) : ContinuousControlSlice.Scalar :=
  d.1 firstFastLabel

/-- The reserved actual fast draw for a fixed slow set, evaluated at the
original `Label.fast` scalar. -/
private def fastDrawOfRemainder (rate : RateInput p) (U : SlowSet p.K p.m)
    (d : Dctl) : FastArm U :=
  CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
    (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) (by intro _; norm_num) U (fastScalarOfRemainder d)

/-- The payload above is the payload of the actual first physical record on
this original source stratum. -/
theorem actualFirstPayload_eq_originalRecord (z : Z) :
    actualFirstPayload rate rewards C_star C_h q t control0 z =
      AssignmentStartPayload.Input.ofFirstAssignment
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput
            (ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
              z.property.2.1 (by rw [z.property.2.2]; exact t.isLt)).input)) := by
  rw [actualFirstPayload, ← ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
    rate rewards C_star C_h q t control0 z]
  rfl

/-- The actual first-launch fast draw, using the original full scalar slice. -/
public def actualFirstFastArm (z : Z) :
    FastArm (actualFirstSlowSet rate rewards C_star C_h q t control0 z) :=
  SnapshotRecordingKernel.fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
    (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) (by intro _; norm_num)
    (actualFirstPayload rate rewards C_star C_h q t control0 z).assignment
    (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
      (coords z).2.1 (coords z).2.2).1

/-- The actual assigned-set auxiliary reward on the source stratum. -/
public def actualFirstAuxiliaryReward (z : Z) : ℝ :=
  MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t)
    (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
    (actualFirstFastArm rate rewards C_star C_h q t control0 z)

private def auxiliaryRewardAt (U : SlowSet p.K p.m) (a : Fin p.K) : ℝ :=
  if ha : a ∈ (Finset.univ : Finset (Fin p.K)) \ U.1 then
    MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U ⟨a, ha⟩
  else 0

private theorem assignmentSlowSet_eq_start (s : FirstAssignmentLaunch.Input p rate.eta) :
    SnapshotRecordingKernel.assignmentSlowSet p s.start.assignment = s.start.slowSet := by
  apply Subtype.ext
  change Finset.univ.image s.start.assignment.assigned = s.start.slowSet.1
  exact s.start_assignment_image

/-- The actual payload assignment has exactly the whole-vector first-start
slow set; this uses the actual first physical record, not a selected anchor. -/
theorem actualFirstSlowSet_eq_canonical (z : Z) :
    actualFirstSlowSet rate rewards C_star C_h q t control0 z =
      CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
        (coords z).2.1 := by
  have hpayload := ReferenceFirstLaunchRecordingPhysicalMarker.payload_assignment
    rate rewards C_star C_h q t control0 (coords z).1 (coords z).2.1 (coords z).2.2
  rw [actualFirstSlowSet, actualFirstPayload, hpayload]
  exact assignmentSlowSet_eq_start rate
    (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t (coords z).2.1)

/-- The original scalar slice reconstructed from the source split retains its
literal `fast` coordinate in the nonassignment scalar array. -/
private theorem split_nonassignment (v : V)
    (b : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p)
    (c : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, b)) c.val = b c := by
  have h := congrArg (fun z => z.2 c)
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).apply_symm_apply (v, b))
  simpa [LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv,
    LaunchAssignmentCoordinateSplit.assignmentLabelEquiv,
    MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.prodCongr, Equiv.prodCongr_apply] using h

private theorem currentControl_fast_coordinate (v : V) (d : Dctl) :
    ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl v d).1 =
        fastScalarOfRemainder d := by
  rw [ReferenceFirstLaunchRecordingSourceLaw.currentControl_scalar]
  exact split_nonassignment v d.1 firstFastLabel

private theorem remainderFastScalar_eq_original (z : Z) :
    fastScalarOfRemainder ((coords z).2.2) =
      (((z.val.1.2 q).2 t).1) firstFastLabel.val := by
  change ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    ((z.val.1.2 q).2 t)).2.1) firstFastLabel = _
  have h := split_nonassignment
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
      (((z.val.1.2 q).2 t).1)).1)
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
      (((z.val.1.2 q).2 t).1)).2) firstFastLabel
  rw [(LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm_apply_apply] at h
  exact h.symm

/-- The actual reserved fast draw is the `sampleFast` map of the original
nonassignment `fast` scalar, after the actual slow set is fixed. -/
private theorem actualFirstFastArm_eq_remainder (z : Z) :
    actualFirstFastArm rate rewards C_star C_h q t control0 z =
      fastDrawOfRemainder rate (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
        (coords z).2.2 := by
  simp only [actualFirstFastArm, SnapshotRecordingKernel.fastArmDraw,
    fastDrawOfRemainder, fastScalarOfRemainder]
  rw [currentControl_fast_coordinate (coords z).2.1 (coords z).2.2]
  rfl

/-- The actual reserved draw uses the original source's literal `Label.fast`
coordinate, while retaining the complete recorded assignment and remainder. -/
theorem actualFirstFastArm_eq_originalFastScalar (z : Z) :
    actualFirstFastArm rate rewards C_star C_h q t control0 z =
      CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
        (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
        (by intro _; norm_num) (by intro _; norm_num)
        (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
        ((((z.val.1.2 q).2 t).1) ContinuousControlSlice.Label.fast) := by
  rw [actualFirstFastArm_eq_remainder rate rewards C_star C_h q t control0 z]
  simp only [fastDrawOfRemainder]
  rw [remainderFastScalar_eq_original rate rewards C_star C_h q t control0 z]
  rfl

/-- Measurability of the actual first-launch slow-set selector. -/
theorem measurable_actualFirstSlowSet :
    Measurable (actualFirstSlowSet rate rewards C_star C_h q t control0) := by
  have heq : actualFirstSlowSet rate rewards C_star C_h q t control0 =
      fun z : Z => CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
        (coords z).2.1 := by
    funext z
    exact actualFirstSlowSet_eq_canonical rate rewards C_star C_h q t control0 z
  rw [heq]
  have hc := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have hv : Measurable (fun z : Z => (coords z).2.1) :=
    measurable_fst.comp (measurable_snd.comp hc)
  exact (CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
    (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)).comp hv

private theorem measurable_finIndex_eval {α ι β : Type*} [MeasurableSpace α]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    [MeasurableSpace β] (f : ι → α → β)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x : α × ι => f x.2 x.1) := by
  intro s hs
  have hset : (fun x : α × ι => f x.2 x.1) ⁻¹' s =
      ⋃ i : ι, {x | x.2 = i} ∩ (fun x => f i x.1) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨x.2, rfl, hx⟩
    · rintro ⟨i, hi, hx⟩
      rw [hi]
      exact hx
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  exact (measurable_snd (measurableSet_singleton i)).inter
    (((hf i).comp measurable_fst) hs)

/-- Measurability of a fixed-slow-set reserved draw from the remainder. -/
private theorem measurable_fastDrawOfRemainder (rate : RateInput p)
    (U : SlowSet p.K p.m) : Measurable (fastDrawOfRemainder rate U) := by
  change Measurable (fun d : Dctl =>
    CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
      (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) (by intro _; norm_num) U (d.1 firstFastLabel))
  have hs := CanonicalFastSampling.measurable_sampleFast p rate.eta.val rate.eta.property
    rate.sourceCap (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) (by intro _; norm_num) U
  have hcoord : Measurable (fun d : Dctl => fastScalarOfRemainder d) :=
    (measurable_pi_apply firstFastLabel).comp measurable_fst
  exact hs.comp hcoord

/-- Measurability of the actual reserved fast-arm value. -/
theorem measurable_actualFirstFastArmValue :
    Measurable (fun z : Z =>
      (actualFirstFastArm rate rewards C_star C_h q t control0 z).val) := by
  have hslow := measurable_actualFirstSlowSet rate rewards C_star C_h q t control0
  have hc := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have hd : Measurable (fun z : Z => (coords z).2.2) := measurable_snd.comp
    (measurable_snd.comp hc)
  have hpair : Measurable (fun z : Z => ((coords z).2.2,
      actualFirstSlowSet rate rewards C_star C_h q t control0 z)) := hd.prodMk hslow
  have hf : Measurable (fun x : Dctl × SlowSet p.K p.m =>
      (fastDrawOfRemainder rate x.2 x.1).val) := by
    exact measurable_finIndex_eval
      (fun U d => (fastDrawOfRemainder rate U d).val)
      (fun U => (measurable_of_finite (fun j : FastArm U => j.val)).comp
        (measurable_fastDrawOfRemainder rate U))
  have hcomp := hf.comp hpair
  have hEq : (fun z : Z => (actualFirstFastArm rate rewards C_star C_h q t control0 z).val) =
      (fun z : Z =>
        (fastDrawOfRemainder rate
          (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
          (coords z).2.2).val) := by
    funext z
    exact congrArg Subtype.val
      (actualFirstFastArm_eq_remainder rate rewards C_star C_h q t control0 z)
  rw [hEq]
  exact hcomp

/-- Measurability follows from the actual measurable slow-set and fast-arm
selectors; the reward is a finite-valued function of those selectors. -/
theorem measurable_actualFirstAuxiliaryReward :
    Measurable (actualFirstAuxiliaryReward rate rewards C_star C_h q t control0) := by
  let h : SlowSet p.K p.m × Fin p.K → ℝ := fun x => auxiliaryRewardAt rewards t x.1 x.2
  have hh : Measurable h := measurable_of_finite h
  have hpair : Measurable (fun z : Z =>
      (actualFirstSlowSet rate rewards C_star C_h q t control0 z,
        (actualFirstFastArm rate rewards C_star C_h q t control0 z).val) :
        Z → SlowSet p.K p.m × Fin p.K) :=
    (measurable_actualFirstSlowSet rate rewards C_star C_h q t control0).prodMk
      (measurable_actualFirstFastArmValue rate rewards C_star C_h q t control0)
  have heq : actualFirstAuxiliaryReward rate rewards C_star C_h q t control0 =
      fun z => h (actualFirstSlowSet rate rewards C_star C_h q t control0 z,
        (actualFirstFastArm rate rewards C_star C_h q t control0 z).val) := by
    funext z
    have hj := (actualFirstFastArm rate rewards C_star C_h q t control0 z).property
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hj
    simp [h, auxiliaryRewardAt, actualFirstAuxiliaryReward, hj]
  rw [heq]
  exact hh.comp hpair

/-- The literal whole-reward rate lies in `[0,1]`, derived from the grid
carrier and the positive denominator. -/
theorem birthRewardRate_bounds (i : Fin p.K) :
    0 ≤ birthRewardRate rewards t i ∧ birthRewardRate rewards t i ≤ 1 := by
  have hD : 0 < (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.D_pos p
  have hvalNat : (rewards t i).val ≤ ConstructorDimensions.D p :=
    Nat.lt_succ_iff.mp (rewards t i).isLt
  have hval : ((rewards t i).val : ℝ) ≤ (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast hvalNat
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hD.le
  · exact (div_le_one hD).2 hval

/-- The actual auxiliary reward is bounded and integrable on the original
finite source stratum; finiteness is inherited from that source measure. -/
theorem actualFirstAuxiliaryReward_bounds (z : Z) :
    0 ≤ actualFirstAuxiliaryReward rate rewards C_star C_h q t control0 z ∧
      actualFirstAuxiliaryReward rate rewards C_star C_h q t control0 z ≤ (p.m : ℝ) :=
  MixedAuxiliaryReward.oneRoundAuxiliaryReward_bounds (birthRewardRate rewards t)
    (birthRewardRate_bounds rewards t) (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
    (actualFirstFastArm rate rewards C_star C_h q t control0 z)

theorem integrable_actualFirstAuxiliaryReward :
    Integrable (actualFirstAuxiliaryReward rate rewards C_star C_h q t control0) muZ := by
  apply Integrable.of_bound
    (measurable_actualFirstAuxiliaryReward rate rewards C_star C_h q t control0).aestronglyMeasurable
    (p.m : ℝ)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (actualFirstAuxiliaryReward_bounds rate rewards C_star C_h q t control0 z).1]
  exact (actualFirstAuxiliaryReward_bounds rate rewards C_star C_h q t control0 z).2

private theorem measurable_fastArmPair_cylinder (A : Set X) (hA : MeasurableSet A)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    MeasurableSet {z : Z | (coords z).1 ∈ A ∧
      actualFirstSlowSet rate rewards C_star C_h q t control0 z = U ∧
      (actualFirstFastArm rate rewards C_star C_h q t control0 z).val = j.val} := by
  have hc := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have hx : Measurable (fun z : Z => (coords z).1) := measurable_fst.comp hc
  have hu := measurable_actualFirstSlowSet rate rewards C_star C_h q t control0
  have hj := measurable_actualFirstFastArmValue rate rewards C_star C_h q t control0
  exact hA.preimage hx |>.inter
    ((measurableSet_singleton U).preimage hu |>.inter
      ((measurableSet_singleton j.val).preimage hj))

/-- The nonassignment remainder retains an independent original fast scalar;
its actual draw has exactly the existing `qGammaPMF`. -/
private theorem map_fastDrawOfRemainder (U : SlowSet p.K p.m) :
    (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p).map
      (fastDrawOfRemainder rate U) =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (by intro _; norm_num) U).toMeasure := by
  have hfst := measurePreserving_fst
    (μ := LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p)
    (ν := ContinuousLearningRows.affineSamplesLaw p)
  have heval : MeasurePreserving
      (fun b : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p => b firstFastLabel)
      (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p)
      ContinuousControlSlice.scalarLaw := by
    exact measurePreserving_eval
      (fun _ : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p =>
        ContinuousControlSlice.scalarLaw) firstFastLabel
  have hscalar : MeasurePreserving fastScalarOfRemainder
      (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p)
      ContinuousControlSlice.scalarLaw := by
    change MeasurePreserving
      ((fun b : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p => b firstFastLabel)
        ∘ Prod.fst)
      (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p)
      ContinuousControlSlice.scalarLaw
    exact heval.comp hfst
  have hs := CanonicalFastSampling.measurable_sampleFast p rate.eta.val rate.eta.property
    rate.sourceCap (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) (by intro _; norm_num) U
  calc
    _ = (ContinuousControlSlice.scalarLaw).map
        (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (by intro _; norm_num) U) := by
      change (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p).map
        (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (by intro _; norm_num) U ∘ fastScalarOfRemainder) = _
      calc
        _ = ((ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p).map
              fastScalarOfRemainder).map
              (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
                (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
                (by intro _; norm_num) (by intro _; norm_num) U) :=
              (Measure.map_map hs hscalar.measurable).symm
        _ = _ := congrArg (fun μ => μ.map
          (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
            (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
            (by intro _; norm_num) (by intro _; norm_num) U)) hscalar.map_eq
    _ = (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (by intro _; norm_num) U).toMeasure := by
      rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
      exact CanonicalFastSampling.uniform_map_sampleFast p rate.eta.val rate.eta.property
        rate.sourceCap (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
        (by intro _; norm_num) (by intro _; norm_num) U

/-- The actual first-launch slow/fast marginal on the original source stratum.
The test set on the retained source is arbitrary and Borel; no positive-mass
or successful-launch condition is imposed. -/
theorem actualFirstChoice_cylinder (A : Set X) (hA : MeasurableSet A)
    (U : SlowSet p.K p.m) (j : FastArm U) :
    muZ {z | (coords z).1 ∈ A ∧
        actualFirstSlowSet rate rewards C_star C_h q t control0 z = U ∧
        (actualFirstFastArm rate rewards C_star C_h q t control0 z).val = j.val} =
      muC A *
        CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _; norm_num) (by intro _; norm_num) U *
        CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (by intro _; norm_num) U j := by
  let sampler : V → SlowSet p.K p.m :=
    CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
      (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
  let slowFiber : Set V := {v | sampler v = U}
  let fastFiber : Set Dctl :=
    {d | (fastDrawOfRemainder rate U d).val = j.val}
  let S : Set (X × (V × Dctl)) := A ×ˢ (slowFiber ×ˢ fastFiber)
  have hslow : Measurable sampler := by
    exact CanonicalAssignmentVector.measurable_canonicalSlowSampler p.two_le_m p.m_lt_K
      (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
  have hslowFiber : MeasurableSet slowFiber :=
    (measurableSet_singleton U).preimage hslow
  have hfast : Measurable (fastDrawOfRemainder rate U) :=
    measurable_fastDrawOfRemainder rate U
  have hfastFiber : MeasurableSet fastFiber :=
    (measurableSet_singleton j.val).preimage
      ((measurable_of_finite (fun a : FastArm U => a.val)).comp hfast)
  have hS : MeasurableSet S := hA.prod (hslowFiber.prod hfastFiber)
  have hset :
      {z : Z | (coords z).1 ∈ A ∧
        actualFirstSlowSet rate rewards C_star C_h q t control0 z = U ∧
        (actualFirstFastArm rate rewards C_star C_h q t control0 z).val = j.val} =
      coords ⁻¹' S := by
    ext z
    simp only [S, slowFiber, fastFiber, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_prod]
    constructor
    · rintro ⟨hA', hU, hj⟩
      refine ⟨hA', ?_, ?_⟩
      · simpa only [sampler] using
          (actualFirstSlowSet_eq_canonical rate rewards C_star C_h q t control0 z).symm.trans hU
      · have hdraw := actualFirstFastArm_eq_remainder rate rewards C_star C_h q t control0 z
        have hdep :
            (fastDrawOfRemainder rate
              (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
              (coords z).2.2).val = (fastDrawOfRemainder rate U (coords z).2.2).val := by
          cases hU
          rfl
        exact hdep.symm.trans ((congrArg Subtype.val hdraw).symm.trans hj)
    · rintro ⟨hA', hU, hj⟩
      refine ⟨hA', ?_, ?_⟩
      · exact (actualFirstSlowSet_eq_canonical rate rewards C_star C_h q t control0 z).trans
          (by simpa only [sampler] using hU)
      · have hslow := (actualFirstSlowSet_eq_canonical rate rewards C_star C_h q t control0 z).trans
          (by simpa only [sampler] using hU)
        have hdraw := actualFirstFastArm_eq_remainder rate rewards C_star C_h q t control0 z
        have hdep :
            (fastDrawOfRemainder rate
              (actualFirstSlowSet rate rewards C_star C_h q t control0 z)
              (coords z).2.2).val = (fastDrawOfRemainder rate U (coords z).2.2).val := by
          cases hslow
          rfl
        exact (congrArg Subtype.val hdraw).trans (hdep.trans hj)
  have hmapSlow := CanonicalAssignmentVector.assignmentLaw_map_canonicalSlowSampler
    p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
    (by intro _; norm_num) (by intro _; norm_num)
  have hmeasureSlow :
      ContinuousControlSlice.assignmentLaw p.K slowFiber =
        (CanonicalOrientedSetLaw.slowSetPMF (fun _ => 1) (fun _ => 1)
          p.two_le_m p.m_lt_K (by intro _; norm_num) (by intro _; norm_num)).toMeasure {U} := by
    calc
      _ = ((ContinuousControlSlice.assignmentLaw p.K).map sampler) {U} := by
        symm
        exact Measure.map_apply hslow (measurableSet_singleton U)
      _ = _ := congrArg (fun μ : Measure (SlowSet p.K p.m) => μ {U}) hmapSlow
  have hmeasureFast :
      ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p fastFiber =
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
          (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (by intro _; norm_num) U).toMeasure {j} := by
    have hsetFast : fastFiber = (fastDrawOfRemainder rate U) ⁻¹' {j} := by
      ext d
      simp [fastFiber, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hsetFast, ← Measure.map_apply hfast (measurableSet_singleton j),
      map_fastDrawOfRemainder rate U]
  calc
    _ = muZ (coords ⁻¹' S) := by rw [hset]
    _ = (Measure.map coords
          (ReferenceTotalSourceDisintegration.sourceStratumMeasure
            rate rewards C_star C_h t i₀)) S := (Measure.map_apply
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h q t control0) hS).symm
    _ = (ReferenceRetainedSourceCoupling.retainedRemainderMeasure
          rate rewards C_star C_h q t t.val le_rfl control0).prod
        ((ContinuousControlSlice.assignmentLaw p.K).prod
          (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p)) S := by
      rw [ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
        rate rewards C_star C_h q t control0]
    _ = ReferenceRetainedSourceCoupling.retainedRemainderMeasure
          rate rewards C_star C_h q t t.val le_rfl control0 A *
        (ContinuousControlSlice.assignmentLaw p.K slowFiber) *
        (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p fastFiber) := by
      calc
        _ = ReferenceRetainedSourceCoupling.retainedRemainderMeasure
              rate rewards C_star C_h q t t.val le_rfl control0 A *
            ((ContinuousControlSlice.assignmentLaw p.K).prod
              (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p))
              (slowFiber ×ˢ fastFiber) :=
            Measure.prod_prod A (slowFiber ×ˢ fastFiber)
        _ = ReferenceRetainedSourceCoupling.retainedRemainderMeasure
              rate rewards C_star C_h q t t.val le_rfl control0 A *
            (ContinuousControlSlice.assignmentLaw p.K slowFiber *
              ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p fastFiber) := by
            rw [Measure.prod_prod slowFiber fastFiber]
        _ = _ := by rw [mul_assoc]
    _ = _ := by
      rw [hmeasureSlow, hmeasureFast,
        PMF.toMeasure_apply_singleton _ U (measurableSet_singleton U),
        PMF.toMeasure_apply_singleton _ j (measurableSet_singleton j)]

private def auxiliaryRewardCell (A : Set X) (U : SlowSet p.K p.m)
    (j : FastArm U) : Set Z :=
  {z | (coords z).1 ∈ A ∧
    actualFirstSlowSet rate rewards C_star C_h q t control0 z = U ∧
    (actualFirstFastArm rate rewards C_star C_h q t control0 z).val = j.val}

private theorem indicator_auxiliaryReward_eq_sum_cells (A : Set X) :
    ({z | (coords z).1 ∈ A}).indicator
      (actualFirstAuxiliaryReward rate rewards C_star C_h q t control0) =
    fun z => ∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
      (auxiliaryRewardCell rate rewards C_star C_h q t control0 A U j).indicator
        (fun _ => MixedAuxiliaryReward.oneRoundAuxiliaryReward
          (birthRewardRate rewards t) U j) z := by
  classical
  funext z
  let U0 := actualFirstSlowSet rate rewards C_star C_h q t control0 z
  let j0 : FastArm U0 := actualFirstFastArm rate rewards C_star C_h q t control0 z
  by_cases hA : (coords z).1 ∈ A
  · have hmem : z ∈ {z : Z | (coords z).1 ∈ A} := hA
    rw [Set.indicator_of_mem hmem]
    symm
    rw [Finset.sum_eq_single U0]
    · calc
        (∑ j : FastArm U0,
            (auxiliaryRewardCell rate rewards C_star C_h q t control0 A U0 j).indicator
              (fun _ => MixedAuxiliaryReward.oneRoundAuxiliaryReward
                (birthRewardRate rewards t) U0 j) z) =
            MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U0 j0 := by
          rw [Finset.sum_eq_single j0]
          · simp [j0, U0, auxiliaryRewardCell, hA]
          · intro j hj hne
            have hval : j0.val ≠ j.val := by
              intro heq
              apply hne
              exact (Subtype.ext heq).symm
            have hnot : z ∉ auxiliaryRewardCell rate rewards C_star C_h q t control0 A U0 j := by
              intro hz
              exact hval hz.2.2
            simp [hnot]
          · simp
        _ = actualFirstAuxiliaryReward rate rewards C_star C_h q t control0 z := by
          simp [U0, j0, actualFirstAuxiliaryReward]
    · intro U hU hne
      apply Finset.sum_eq_zero
      intro j hj
      have hnot : z ∉ auxiliaryRewardCell rate rewards C_star C_h q t control0 A U j := by
        intro hz
        apply hne
        simpa [U0] using hz.2.1.symm
      simp [hnot]
    · simp
  · have hmem : z ∉ {z : Z | (coords z).1 ∈ A} := hA
    rw [Set.indicator_of_notMem hmem]
    symm
    apply Finset.sum_eq_zero
    intro U hU
    apply Finset.sum_eq_zero
    intro j hj
    simp [auxiliaryRewardCell, hA]

/-- The localized original-source integral is the retained source mass times
the mixed slow/fast expectation. The test event is any Borel set of the
retained source coordinate. -/
theorem localizedAuxiliaryReward_integral_eq (A : Set X) (hA : MeasurableSet A) :
    (∫ z : Z, ({z | (coords z).1 ∈ A}).indicator
      (actualFirstAuxiliaryReward rate rewards C_star C_h q t control0) z ∂muZ) =
      (muC).real A * MixedAuxiliaryReward.mixedAuxiliaryRewardExpectation p
        rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
        (by intro _; norm_num) (by intro _; norm_num)
        (by intro _; norm_num) (by intro _; norm_num) (birthRewardRate rewards t) := by
  classical
  let cell := auxiliaryRewardCell rate rewards C_star C_h q t control0 A
  let unit : Fin p.K → ℝ := fun _ => 1
  have hunit : ∀ i, 0 < unit i := by intro _; norm_num [unit]
  have hunit_le : ∀ i, unit i ≤ unit i := by intro _; rfl
  have hunit_two : ∀ i, unit i ≤ 2 * unit i := by intro _; norm_num [unit]
  have hcellMeas (U : SlowSet p.K p.m) (j : FastArm U) : MeasurableSet (cell U j) := by
    change MeasurableSet {z : Z | (coords z).1 ∈ A ∧
      actualFirstSlowSet rate rewards C_star C_h q t control0 z = U ∧
      (actualFirstFastArm rate rewards C_star C_h q t control0 z).val = j.val}
    exact measurable_fastArmPair_cylinder rate rewards C_star C_h q t control0 A hA U j
  have hcellInt (U : SlowSet p.K p.m) (j : FastArm U) :
      Integrable ((cell U j).indicator (fun _ =>
        MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j)) muZ :=
    (integrable_const _).indicator (hcellMeas U j)
  have hinnerInt (U : SlowSet p.K p.m) :
      Integrable (fun z : Z => ∑ j : FastArm U,
        (cell U j).indicator (fun _ =>
          MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) z) muZ :=
    integrable_finsetSum Finset.univ (fun j _ => hcellInt U j)
  have hsumInt : Integrable (fun z : Z => ∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
        (cell U j).indicator (fun _ =>
          MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) z) muZ :=
    integrable_finsetSum Finset.univ (fun U _ => hinnerInt U)
  have hmass (U : SlowSet p.K p.m) (j : FastArm U) :
      (muZ).real (cell U j) = (muC).real A *
        (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
          hunit hunit U).toReal *
        (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
          unit unit hunit hunit hunit_le hunit_two U j).toReal := by
    change (muZ).real {z | (coords z).1 ∈ A ∧
      actualFirstSlowSet rate rewards C_star C_h q t control0 z = U ∧
      (actualFirstFastArm rate rewards C_star C_h q t control0 z).val = j.val} = _
    rw [measureReal_def,
      actualFirstChoice_cylinder rate rewards C_star C_h q t control0 A hA U j]
    simp only [ENNReal.toReal_mul, measureReal_def]
    simp [unit]
  have hqreal (U : SlowSet p.K p.m) (j : FastArm U) :
      (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
        unit unit hunit hunit hunit_le hunit_two U j).toReal =
        CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
          unit unit hunit hunit hunit_le hunit_two U j := by
    rw [CanonicalFastSampling.qGammaPMF_apply, ENNReal.toReal_ofReal]
    exact CanonicalFastSampling.qGamma_nonneg p rate.eta.property rate.sourceCap
      unit unit hunit hunit hunit_le hunit_two U j
  have hfactor :
      (∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
        ((muC).real A *
          (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
            hunit hunit U).toReal *
          (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
            unit unit hunit hunit hunit_le hunit_two U j).toReal) *
          MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) =
      (muC).real A * ∑ U : SlowSet p.K p.m,
        (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
          hunit hunit U).toReal *
        ∑ j : FastArm U,
          CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
            unit unit hunit hunit hunit_le hunit_two U j *
          MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j := by
    calc
      _ = ∑ U : SlowSet p.K p.m,
          ((muC).real A *
            (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
              hunit hunit U).toReal) *
            ∑ j : FastArm U,
              (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
                unit unit hunit hunit hunit_le hunit_two U j).toReal *
              MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j := by
        apply Finset.sum_congr rfl
        intro U hU
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (muC).real A * ∑ U : SlowSet p.K p.m,
          (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
            hunit hunit U).toReal *
            ∑ j : FastArm U,
              (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
                unit unit hunit hunit hunit_le hunit_two U j).toReal *
              MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U hU
        ring
      _ = _ := by
        apply congrArg (fun x : ℝ => (muC).real A * x)
        apply Finset.sum_congr rfl
        intro U hU
        apply congrArg (fun x : ℝ =>
          (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
            hunit hunit U).toReal * x)
        apply Finset.sum_congr rfl
        intro j hj
        rw [hqreal]
  calc
    _ = ∫ z : Z, (fun z => ∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
          (cell U j).indicator (fun _ =>
            MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) z) z ∂muZ := by
      rw [indicator_auxiliaryReward_eq_sum_cells rate rewards C_star C_h q t control0 A]
    _ = ∑ U : SlowSet p.K p.m, ∫ z : Z, ∑ j : FastArm U,
          (cell U j).indicator (fun _ =>
            MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) z ∂muZ :=
      integral_finsetSum Finset.univ (fun U _ => hinnerInt U)
    _ = ∑ U : SlowSet p.K p.m, ∑ j : FastArm U, ∫ z : Z,
          (cell U j).indicator (fun _ =>
            MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) z ∂muZ := by
      apply Finset.sum_congr rfl
      intro U hU
      exact integral_finsetSum Finset.univ (fun j _ => hcellInt U j)
    _ = ∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
          (muZ).real (cell U j) *
            MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j := by
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_indicator_const _ (hcellMeas U j), smul_eq_mul]
    _ = _ := by
      rw [show (∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
          (muZ).real (cell U j) *
            MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) =
          (∑ U : SlowSet p.K p.m, ∑ j : FastArm U,
            ((muC).real A *
              (CanonicalOrientedSetLaw.slowSetPMF unit unit p.two_le_m p.m_lt_K
                hunit hunit U).toReal *
              (CanonicalFastSampling.qGammaPMF p rate.eta.val rate.eta.property rate.sourceCap
                unit unit hunit hunit hunit_le hunit_two U j).toReal) *
              MixedAuxiliaryReward.oneRoundAuxiliaryReward (birthRewardRate rewards t) U j) from by
          apply Finset.sum_congr rfl
          intro U hU
          apply Finset.sum_congr rfl
          intro j hj
          rw [hmass U j]]
      simpa [MixedAuxiliaryReward.mixedAuxiliaryRewardExpectation, unit] using hfactor

/-- The localized birth contribution retains the original source exploration
penalty and the whole-table reward marginal. -/
theorem localizedAuxiliaryReward_integral_ge_theta_sub_gamma
    (A : Set X) (hA : MeasurableSet A) :
    (∫ z : Z, ({z | (coords z).1 ∈ A}).indicator
      (actualFirstAuxiliaryReward rate rewards C_star C_h q t control0) z ∂muZ) ≥
      (muC).real A *
        ((∑ i : Fin p.K, ProductSetLaw.theta p.m (fun _ => 1) i *
          birthRewardRate rewards t i) - CanonicalRecordingRates.gamma p rate.eta.val) := by
  rw [localizedAuxiliaryReward_integral_eq rate rewards C_star C_h q t control0 A hA]
  have hmix := MixedAuxiliaryReward.mixedAuxiliaryRewardExpectation_ge_theta_sub_gamma
    p rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
    (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) (by intro _; norm_num) (birthRewardRate rewards t)
    (birthRewardRate_bounds rewards t)
  exact mul_le_mul_of_nonneg_left hmix measureReal_nonneg

/-- This source stratum is the same first retained calendar cell used by the
original first-live calendar: birth starts from the initial state, carries the
constant all-one incoming marginal, and is retained, including an overflow
detected by its first update. -/
theorem birthCalendarCell_identification
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
        rate rewards C_star C_h t.val z.val = RecordedQueueRun.initialState p.K ∧
      (∀ j : Fin p.K,
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
            rate rewards C_star C_h t j z.val = ProductSetLaw.theta p.m (fun _ => 1) j) ∧
      z.val ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
        rate rewards C_star C_h t := by
  refine ⟨?_, ?_, ?_⟩
  · exact ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRunAt_birth
      rate rewards C_star C_h q t z
  · intro j
    exact ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
      rate rewards C_star C_h q t j z
  · exact ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
      rate rewards C_star C_h q t control0 z

end Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward

end
