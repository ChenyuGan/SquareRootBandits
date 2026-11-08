/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw

/-!
# First-launch saved contribution moments on the original source

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:41-64,391-397`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module computes first and second moments of the actual checked first
physical logging emission. Its source-cylinder integrals retain the original
source, selected index, complete assignment vector, and the unnormalized
retained remainder measure. It does not identify an adapted history, a queue
update, a stopped law, or a manuscript theorem closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstLaunchSavedSourceMoments

open ConstructorDimensions ContinuousControlSlice ContinuousLearningRows
open ReferenceFirstLaunchRecordingPhysicalMarker
open ReferenceFirstLaunchRecordingSourceLaw
open CanonicalRecordingRates QuantizedRecordingMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev AssignmentVector := ReferenceFirstLaunchRecordingSourceLaw.AssignmentVector
abbrev NonAssignmentControl := ReferenceFirstLaunchRecordingSourceLaw.NonAssignmentControl

/-- The normalized value of the actual first-launch checked log emission. -/
def normalizedCurrentSaved {p : Parameters} (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control0 : TimeControl p)
    (x : RetainedStart rate rewards C_star C_h q t control0)
    (v : AssignmentVector p) (d : NonAssignmentControl p)
    (i : Fin (p.m - 1)) : ℝ :=
  (ReferenceFirstLaunchRecordingSourceLaw.currentSaved rate rewards C_star C_h q t
    control0 x v d i : ℝ) / (rate.eta.val * (D p : ℝ))

/-- The same normalized physical readout pulled back along the original-source
coordinates of the actual first-launch stratum. -/
def sourceSaved {p : Parameters} (rate : RateInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control0 : TimeControl p)
    (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
    (i : Fin (p.m - 1)) : ℝ :=
  let c := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates rate rewards
    C_star C_h q t control0 z
  normalizedCurrentSaved rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 i

/-- The true first-launch assigned arm, read from the actual sampled whole vector. -/
@[expose] def firstLaunchAssignedArm {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (v : AssignmentVector p) (i : Fin (p.m - 1)) : Fin p.K :=
  (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i

/-- The canonical unit-anchor rate of that same actual assigned arm. -/
@[expose] def firstLaunchXi {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (v : AssignmentVector p) (i : Fin (p.m - 1)) : ℝ :=
  CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1)
    (firstLaunchAssignedArm rate t v i)

/-- The rounded reward of the actual arm at the actual first-launch time. -/
@[expose] def firstLaunchReward {p : Parameters} (rate : RateInput p)
    (rewards : RewardTable p) (t : Fin p.T) (v : AssignmentVector p)
    (i : Fin (p.m - 1)) : ℝ :=
  (((rewards t (firstLaunchAssignedArm rate t v i)).val : ℝ) /
    (D p : ℝ))

/-- The source's quantized value at that arm, with the exact integer scale. -/
@[expose] def firstLaunchQuantizedValue {p : Parameters} (rate : RateInput p)
    (rewards : RewardTable p) (t : Fin p.T) (v : AssignmentVector p)
    (i : Fin (p.m - 1)) : ℝ :=
  QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
    (firstLaunchXi rate t v i) (firstLaunchReward rate rewards t v i)

/-- The finite-outcome formula characterized by the actual first-launch log
emission. -/
@[expose] def firstLaunchMarkerValue {p : Parameters} (rate : RateInput p)
    (rewards : RewardTable p) (t : Fin p.T) (v : AssignmentVector p)
    (i : Fin (p.m - 1)) (o : Option (Fin p.K)) : ℝ :=
  if o = some (firstLaunchAssignedArm rate t v i) then
    firstLaunchQuantizedValue rate rewards t v i else 0

section FirstLaunch

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (control0 : TimeControl p)

local notation "X" => RetainedStart rate rewards C_star C_h q t control0
local notation "V" => AssignmentVector p
local notation "Dctl" => NonAssignmentControl p
local notation "λA" => ContinuousControlSlice.assignmentLaw p.K
local notation "λD" => ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards
  C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate
  rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "Iphys" => ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
local notation "firstArm" => firstLaunchAssignedArm rate t
local notation "xiAt" => firstLaunchXi rate t
local notation "rhoAt" => firstLaunchReward rate rewards t
local notation "quantizedAt" => firstLaunchQuantizedValue rate rewards t
local notation "markerValue" => firstLaunchMarkerValue rate rewards t

/-- The actual assigned arm's rate is positive and dominates the canonical
beta; the rounded reward and exact quantized value use the whole vector. -/
theorem firstLaunchParameters (v : V) (i : Fin (p.m - 1)) :
    0 < xiAt v i ∧
      0 < CanonicalRecordingRates.beta p rate.eta.val ∧
      CanonicalRecordingRates.beta p rate.eta.val ≤ xiAt v i ∧
      rhoAt v i ∈ Set.Icc (0 : ℝ) 1 := by
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property
    (fun _ => 1) (firstArm v i)
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbetaxi := CanonicalRecordingRates.beta_le_xi p rate.eta.property
    (fun _ => 1) (firstArm v i)
  have hD : 0 < (D p : ℝ) := by exact_mod_cast ConstructorDimensions.D_pos p
  have hgridNat : (rewards t (firstArm v i)).val ≤ D p :=
    Nat.le_of_lt_succ (rewards t (firstArm v i)).isLt
  have hgrid : ((rewards t (firstArm v i)).val : ℝ) ≤ (D p : ℝ) := by
    exact_mod_cast hgridNat
  refine ⟨hxi, hbeta, hbetaxi, ?_⟩
  constructor
  · dsimp [firstLaunchReward]
    exact div_nonneg (Nat.cast_nonneg _) hD.le
  · dsimp [firstLaunchReward]
    exact (div_le_one hD).2 hgrid

/-- The literal floor identity for the checked current log emission. -/
theorem normalizedCurrentSaved_eq_marker (x : X) (v : V) (d : Dctl)
    (i : Fin (p.m - 1)) :
    normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i =
      markerValue v i
        (Iphys rate rewards C_star C_h q t control0 x v d) := by
  classical
  rw [normalizedCurrentSaved,
    ReferenceFirstLaunchRecordingSourceLaw.currentSaved_eq rate rewards C_star C_h q t
      control0 x v d i]
  by_cases hm : Iphys rate rewards C_star C_h q t control0 x v d =
      some (firstArm v i)
  · have hassigned : firstArm v i =
        (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i := rfl
    have hm' : Iphys rate rewards C_star C_h q t control0 x v d =
        some ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i) := by
      simpa [hassigned] using hm
    simp only [hm']
    let arm := (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i
    have hfloor : Nat.floor ((rate.n : ℝ) *
        (((rewards t arm).val : ℝ) / (D p : ℝ)) /
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) arm) =
      QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
        (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) arm)
        (((rewards t arm).val : ℝ) / (D p : ℝ)) := by
      simp only [QuantizedRecordingMoments.quantizedIndex]
      rw [rate.n_scale]
      congr 1
      ring
    rw [hfloor]
    have hcond : some arm = some (firstLaunchAssignedArm rate t v i) :=
      congrArg some hassigned.symm
    rw [firstLaunchMarkerValue, if_pos hcond]
    have hreadout : firstLaunchQuantizedValue rate rewards t v i =
        (QuantizedRecordingMoments.quantizedIndex (D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) arm)
          (((rewards t arm).val : ℝ) / (D p : ℝ)) : ℝ) /
          (rate.eta.val * (D p : ℝ)) := by
      simp [firstLaunchQuantizedValue, firstLaunchXi, firstLaunchReward,
        QuantizedRecordingMoments.quantizedValue, hassigned, arm]
    rw [hreadout]
    simpa [arm]
  · have hm' : ¬ Iphys rate rewards C_star C_h q t control0 x v d =
        some ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i) := by
      intro h
      apply hm
      simpa [firstLaunchAssignedArm] using h
    simp [firstLaunchMarkerValue, hm, hm']

theorem normalizedCurrentSaved_nonneg (x : X) (v : V) (d : Dctl)
    (i : Fin (p.m - 1)) :
    0 ≤ normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i := by
  rw [normalizedCurrentSaved_eq_marker rate rewards C_star C_h q t control0 x v d i]
  by_cases hm : Iphys rate rewards C_star C_h q t control0 x v d =
      some (firstArm v i)
  · have hnonneg := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
      (xiAt v i) (rhoAt v i) rate.eta.property
    simpa [firstLaunchMarkerValue, firstLaunchQuantizedValue, hm] using hnonneg
  · simp [firstLaunchMarkerValue, hm]

theorem quantizedValue_le_beta_inv (v : V) (i : Fin (p.m - 1)) :
    quantizedAt v i ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (D p) rate.eta.val (xiAt v i)
    (rhoAt v i)
    (CanonicalRecordingRates.beta p rate.eta.val)
    (ConstructorDimensions.D_pos p) rate.eta.property
    (firstLaunchParameters rate rewards t v i).1
    (firstLaunchParameters rate rewards t v i).2.2.2
    (firstLaunchParameters rate rewards t v i).2.1
    (firstLaunchParameters rate rewards t v i).2.2.1

private theorem markerValue_range (v : V) (i : Fin (p.m - 1))
    (o : Option (Fin p.K)) :
    0 ≤ markerValue v i o ∧
      markerValue v i o ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  by_cases h : o = some (firstArm v i)
  · have hnonneg := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
      (xiAt v i) (rhoAt v i) rate.eta.property
    have hbound := quantizedValue_le_beta_inv rate rewards t v i
    constructor
    · simpa [firstLaunchMarkerValue, firstLaunchQuantizedValue, h] using hnonneg
    · simpa [firstLaunchMarkerValue, firstLaunchQuantizedValue, h] using hbound
  · simp only [firstLaunchMarkerValue, h]
    constructor
    · norm_num
    · exact div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le

theorem normalizedCurrentSaved_le_beta_inv (x : X) (v : V) (d : Dctl)
    (i : Fin (p.m - 1)) :
    normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  rw [normalizedCurrentSaved_eq_marker rate rewards C_star C_h q t control0 x v d i]
  by_cases hm : Iphys rate rewards C_star C_h q t control0 x v d =
      some (firstArm v i)
  · simpa [firstLaunchMarkerValue, firstLaunchQuantizedValue, hm] using
      (quantizedValue_le_beta_inv rate rewards t v i)
  · simp only [firstLaunchMarkerValue, hm]
    exact div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le

private theorem markerValue_measurable (v : V) (i : Fin (p.m - 1)) :
    Measurable (markerValue v i) := by
  exact measurable_of_countable _

theorem normalizedCurrentSaved_measurable (x : X) (v : V) (i : Fin (p.m - 1)) :
    Measurable (fun d : Dctl =>
      normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) := by
  have hpair := ReferenceFirstLaunchRecordingSourceLaw.measurable_currentSaved_real_square
    rate rewards C_star C_h q t control0 i
  have hmarker := ReferenceFirstLaunchRecordingSourceLaw.measurable_physicalMarker
    rate rewards C_star C_h q t control0
  have hmap : Measurable (fun d : Dctl =>
      (x, (v, d))) := measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hnat := (measurable_fst.comp hpair).comp hmap
  change Measurable (fun d : Dctl => ((ReferenceFirstLaunchRecordingSourceLaw.currentSaved
    rate rewards C_star C_h q t control0 x v d i : ℝ) /
      (rate.eta.val * (D p : ℝ))))
  exact hnat.div_const _

theorem normalizedCurrentSaved_integrable (x : X) (v : V) (i : Fin (p.m - 1)) :
    Integrable (fun d : Dctl =>
      normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) λD := by
  have hmeas := normalizedCurrentSaved_measurable rate rewards C_star C_h q t control0 x v i
  have hbound : ∀ d : Dctl,
      ‖normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro d
    rw [Real.norm_eq_abs, abs_of_nonneg
      (normalizedCurrentSaved_nonneg rate rewards C_star C_h q t control0 x v d i)]
    exact normalizedCurrentSaved_le_beta_inv rate rewards C_star C_h q t control0 x v d i
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
    (Filter.Eventually.of_forall hbound)

theorem normalizedCurrentSaved_sq_integrable (x : X) (v : V) (i : Fin (p.m - 1)) :
    Integrable (fun d : Dctl =>
      (normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) ^ 2) λD := by
  have hmeas := Measurable.pow_const
    (normalizedCurrentSaved_measurable rate rewards C_star C_h q t control0 x v i) 2
  have hbound : ∀ d : Dctl,
      ‖(normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro d
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := normalizedCurrentSaved_nonneg rate rewards C_star C_h q t control0 x v d i
    have hle := normalizedCurrentSaved_le_beta_inv rate rewards C_star C_h q t control0 x v d i
    nlinarith [sq_nonneg (1 / CanonicalRecordingRates.beta p rate.eta.val -
      normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i)]
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    (Filter.Eventually.of_forall hbound)

private theorem markerValue_integral (v : V) (i : Fin (p.m - 1)) :
    (∫ o, markerValue v i o ∂
      ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        xiAt v i *
          quantizedAt v i := by
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap (fun _ => 1) (by intro _; norm_num)
  have hrate : rates.rate (firstLaunchAssignedArm rate t v i) =
      firstLaunchXi rate t v i := rfl
  have hxi : 0 ≤ firstLaunchXi rate t v i :=
    (firstLaunchParameters rate rewards t v i).1.le
  rw [ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw]
  rw [PMF.integral_eq_sum]
  simp [firstLaunchMarkerValue, firstLaunchQuantizedValue, rates, hrate, hxi,
    RecordedRoundMoments.recordingOutcomePMF,
    RecordedRoundMoments.outcomeMass, ENNReal.toReal_ofReal,
    RecordedRoundMoments.RecordingRates.rate_nonneg]

private theorem markerValue_sq_integral (v : V) (i : Fin (p.m - 1)) :
    (∫ o, (markerValue v i o) ^ 2 ∂
      ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        xiAt v i *
          (quantizedAt v i) ^ 2 := by
  let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
    rate.sourceCap (fun _ => 1) (by intro _; norm_num)
  have hrate : rates.rate (firstLaunchAssignedArm rate t v i) =
      firstLaunchXi rate t v i := rfl
  have hxi : 0 ≤ firstLaunchXi rate t v i :=
    (firstLaunchParameters rate rewards t v i).1.le
  rw [ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw]
  rw [PMF.integral_eq_sum]
  simp [firstLaunchMarkerValue, firstLaunchQuantizedValue, rates, hrate, hxi,
    RecordedRoundMoments.recordingOutcomePMF,
    RecordedRoundMoments.outcomeMass, ENNReal.toReal_ofReal,
    RecordedRoundMoments.RecordingRates.rate_nonneg]

theorem normalizedCurrentSaved_integral (x : X) (v : V) (i : Fin (p.m - 1)) :
    (∫ d, normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i ∂λD) =
      xiAt v i *
        quantizedAt v i := by
  have hphi : AEMeasurable (fun d : Dctl =>
      Iphys rate rewards C_star C_h q t control0 x v d) λD :=
    ((ReferenceFirstLaunchRecordingSourceLaw.measurable_physicalMarker
      rate rewards C_star C_h q t control0).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aemeasurable
  have hmap := MeasureTheory.integral_map (μ := λD)
    (φ := fun d : Dctl => Iphys rate rewards C_star C_h q t control0 x v d)
    hphi (markerValue_measurable rate rewards t v i).aestronglyMeasurable
  calc
    _ = ∫ d, markerValue v i
        (Iphys rate rewards C_star C_h q t control0 x v d) ∂λD := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (normalizedCurrentSaved_eq_marker
        rate rewards C_star C_h q t control0 x v · i)
    _ = ∫ o, markerValue v i o ∂
        (MeasureTheory.Measure.map (fun d : Dctl =>
          Iphys rate rewards C_star C_h q t control0 x v d) λD) := hmap.symm
    _ = ∫ o, markerValue v i o ∂
        ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate := by
      rw [ReferenceFirstLaunchRecordingSourceLaw.map_physicalMarker
        rate rewards C_star C_h q t control0 x v]
    _ = xiAt v i *
        quantizedAt v i :=
      markerValue_integral rate rewards t v i

theorem normalizedCurrentSaved_sq_integral (x : X) (v : V) (i : Fin (p.m - 1)) :
    (∫ d, (normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) ^ 2 ∂λD) =
      xiAt v i *
        (quantizedAt v i) ^ 2 := by
  have hphi : AEMeasurable (fun d : Dctl =>
      Iphys rate rewards C_star C_h q t control0 x v d) λD :=
    ((ReferenceFirstLaunchRecordingSourceLaw.measurable_physicalMarker
      rate rewards C_star C_h q t control0).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aemeasurable
  have hmap := MeasureTheory.integral_map (μ := λD)
    (φ := fun d : Dctl => Iphys rate rewards C_star C_h q t control0 x v d)
    hphi ((Measurable.pow_const
      (markerValue_measurable rate rewards t v i) 2).aestronglyMeasurable)
  calc
    _ = ∫ d, (markerValue v i
        (Iphys rate rewards C_star C_h q t control0 x v d)) ^ 2 ∂λD := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun d => congrArg (fun y : ℝ => y ^ 2)
        (normalizedCurrentSaved_eq_marker rate rewards C_star C_h q t control0 x v d i))
    _ = ∫ o, (markerValue v i o) ^ 2 ∂
        (MeasureTheory.Measure.map (fun d : Dctl =>
          Iphys rate rewards C_star C_h q t control0 x v d) λD) := hmap.symm
    _ = ∫ o, (markerValue v i o) ^ 2 ∂
        ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate := by
      rw [ReferenceFirstLaunchRecordingSourceLaw.map_physicalMarker
        rate rewards C_star C_h q t control0 x v]
    _ = xiAt v i *
        (quantizedAt v i) ^ 2 :=
      markerValue_sq_integral rate rewards t v i

theorem normalizedCurrentSaved_firstMoment_bounds (x : X) (v : V) (i : Fin (p.m - 1)) :
    rhoAt v i -
        xiAt v i /
          (rate.eta.val * (D p : ℝ)) ≤
      ∫ d, normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i ∂λD ∧
    (∫ d, normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i ∂λD) ≤
      rhoAt v i ∧
    rhoAt v i ≤ 1 := by
  rw [normalizedCurrentSaved_integral rate rewards C_star C_h q t control0 x v i]
  have hp := firstLaunchParameters rate rewards t v i
  have hD := ConstructorDimensions.D_pos p
  exact ⟨QuantizedRecordingMoments.quantizedValue_roundingError
      (D p) rate.eta.val (xiAt v i)
      (rhoAt v i) hD rate.eta.property hp.1 hp.2.2.2,
    QuantizedRecordingMoments.quantizedValue_firstMoment_le
      (D p) rate.eta.val (xiAt v i)
      (rhoAt v i) hD rate.eta.property hp.1 hp.2.2.2,
    hp.2.2.2.2⟩

theorem normalizedCurrentSaved_secondMoment_bounds (x : X) (v : V)
    (i : Fin (p.m - 1)) :
    (∫ d, (normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) ^ 2 ∂λD) ≤
        (rhoAt v i) ^ 2 /
          xiAt v i ∧
    (∫ d, (normalizedCurrentSaved rate rewards C_star C_h q t control0 x v d i) ^ 2 ∂λD) ≤
      1 / xiAt v i := by
  rw [normalizedCurrentSaved_sq_integral rate rewards C_star C_h q t control0 x v i]
  have hp := firstLaunchParameters rate rewards t v i
  have hsq : (rhoAt v i) ^ 2 ≤ 1 := by
    nlinarith [hp.2.2.2.1, hp.2.2.2.2]
  have hq := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (xiAt v i)
    (rhoAt v i) (ConstructorDimensions.D_pos p)
    rate.eta.property hp.1 hp.2.2.2
  exact ⟨hq, hq.trans (div_le_div_of_nonneg_right hsq hp.1.le)⟩

end FirstLaunch

section OriginalSource

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (control0 : TimeControl p)

local notation "X" => RetainedStart rate rewards C_star C_h q t control0
local notation "V" => AssignmentVector p
local notation "Dctl" => NonAssignmentControl p
local notation "λA" => ContinuousControlSlice.assignmentLaw p.K
local notation "λD" => ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards
  C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate
  rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "xiAt" => firstLaunchXi rate t
local notation "rhoAt" => firstLaunchReward rate rewards t
local notation "quantizedAt" => firstLaunchQuantizedValue rate rewards t
local notation "markerValue" => firstLaunchMarkerValue rate rewards t
local notation "sourceCoords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
local notation "sourceMark" => ReferenceFirstLaunchRecordingSourceLaw.sourceMarker

/-- The original-source readout is the actual first record's first-payload
buffer contribution, divided by the source's exact `eta * D` scale. -/
theorem sourceSaved_eq_firstPhysicalRecord (z : Z) (i : Fin (p.m - 1)) :
    sourceSaved rate rewards C_star C_h q t control0 z i =
      let r := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards
        C_star C_h z.property.2.1 (by rw [z.property.2.2]; exact t.isLt)
      let firstPayload := AssignmentStartPayload.Input.ofFirstAssignment
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput r.input))
      ((SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
        rate.eta.val (firstPayload.exponent (firstPayload.assignment.assigned i))
        (firstPayload.assignment.assigned i) (r.input.time.val + 1)
        (ReferenceFollowerBufferProvenance.logEmission i r) : ℝ) /
          (rate.eta.val * (D p : ℝ))) := by
  let c := sourceCoords rate rewards C_star C_h q t control0 z
  let r := ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards C_star C_h
    z.property.2.1 (by rw [z.property.2.2]; exact t.isLt)
  let firstPayload := AssignmentStartPayload.Input.ofFirstAssignment
    (CoordinatorRoundDispatch.firstLaunchInput
      (ReferenceActivePhysicalStep.firstInput r.input))
  have hrecord : ReferenceFirstLaunchRecordingPhysicalMarker.record rate rewards C_star C_h
      q t control0 c.1 c.2.1 c.2.2 = r := by
    exact ReferenceFirstLaunchRecordingSourceLaw.source_record_eq rate rewards C_star C_h
      q t control0 z
  have hpayload : ReferenceFirstLaunchRecordingPhysicalMarker.payload rate rewards C_star C_h
      q t control0 c.1 c.2.1 c.2.2 = firstPayload := by
    simp only [ReferenceFirstLaunchRecordingPhysicalMarker.payload,
      ReferenceFirstLaunchRecordingPhysicalMarker.launchInput]
    rw [hrecord]
    rfl
  change ((ReferenceFirstLaunchRecordingSourceLaw.currentSaved rate rewards C_star C_h q t
    control0 c.1 c.2.1 c.2.2 i : ℝ) / (rate.eta.val * (D p : ℝ))) = _
  rw [ReferenceFirstLaunchRecordingSourceLaw.currentSaved, hpayload, hrecord]
  rfl

/-- The source-cylinder integrands are jointly Borel on the original source. -/
theorem sourceSaved_measurable (i : Fin (p.m - 1)) :
    Measurable (fun z : Z => sourceSaved rate rewards C_star C_h q t control0 z i) := by
  have hpair := ReferenceFirstLaunchRecordingSourceLaw.measurable_currentSaved_real_square
    rate rewards C_star C_h q t control0 i
  have hcoords := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have h := (measurable_fst.comp hpair).comp hcoords
  change Measurable (fun z : Z =>
    ((ReferenceFirstLaunchRecordingSourceLaw.currentSaved rate rewards C_star C_h q t
      control0 (sourceCoords rate rewards C_star C_h q t control0 z).1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i : ℝ) /
        (rate.eta.val * (D p : ℝ))))
  exact h.div_const _

theorem sourceSaved_sq_measurable (i : Fin (p.m - 1)) :
    Measurable (fun z : Z =>
      (sourceSaved rate rewards C_star C_h q t control0 z i) ^ 2) :=
  (sourceSaved_measurable rate rewards C_star C_h q t control0 i).pow_const 2

theorem retainedJoint_currentSaved_integrable (i : Fin (p.m - 1)) :
    Integrable (fun z : X × (V × Dctl) =>
      normalizedCurrentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i) (MeasureTheory.Measure.prod μC (MeasureTheory.Measure.prod λA λD)) := by
  have hpair := ReferenceFirstLaunchRecordingSourceLaw.measurable_currentSaved_real_square
    rate rewards C_star C_h q t control0 i
  have h := (measurable_fst.comp hpair).div_const (rate.eta.val * (D p : ℝ))
  have hbound : ∀ z : X × (V × Dctl),
      ‖normalizedCurrentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (normalizedCurrentSaved_nonneg rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i)]
    exact normalizedCurrentSaved_le_beta_inv rate rewards C_star C_h q t control0
      z.1 z.2.1 z.2.2 i
  exact Integrable.of_bound h.aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val) (Filter.Eventually.of_forall hbound)

theorem retainedJoint_currentSaved_sq_integrable (i : Fin (p.m - 1)) :
    Integrable (fun z : X × (V × Dctl) =>
      (normalizedCurrentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i) ^ 2) (MeasureTheory.Measure.prod μC (MeasureTheory.Measure.prod λA λD)) := by
  have hmeas := (ReferenceFirstLaunchRecordingSourceLaw.measurable_currentSaved_real_square
    rate rewards C_star C_h q t control0 i).fst.div_const (rate.eta.val * (D p : ℝ))
  have hsqMeas := hmeas.pow_const 2
  have hbound : ∀ z : X × (V × Dctl),
      ‖(normalizedCurrentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := normalizedCurrentSaved_nonneg rate rewards C_star C_h q t control0
      z.1 z.2.1 z.2.2 i
    have hle := normalizedCurrentSaved_le_beta_inv rate rewards C_star C_h q t control0
      z.1 z.2.1 z.2.2 i
    nlinarith [sq_nonneg (1 / CanonicalRecordingRates.beta p rate.eta.val -
      normalizedCurrentSaved rate rewards C_star C_h q t control0 z.1 z.2.1 z.2.2 i)]
  exact Integrable.of_bound hsqMeas.aestronglyMeasurable
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    (Filter.Eventually.of_forall hbound)

theorem sourceSaved_integrable (i : Fin (p.m - 1)) :
    Integrable (fun z : Z => sourceSaved rate rewards C_star C_h q t control0 z i) μZ := by
  have hmeas := sourceSaved_measurable rate rewards C_star C_h q t control0 i
  have hbound : ∀ z : Z,
      ‖sourceSaved rate rewards C_star C_h q t control0 z i‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact normalizedCurrentSaved_le_beta_inv rate rewards C_star C_h q t control0
        (sourceCoords rate rewards C_star C_h q t control0 z).1
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1
        (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i
    · exact normalizedCurrentSaved_nonneg rate rewards C_star C_h q t control0
        (sourceCoords rate rewards C_star C_h q t control0 z).1
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1
        (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val) (Filter.Eventually.of_forall hbound)

theorem sourceSaved_sq_integrable (i : Fin (p.m - 1)) :
    Integrable (fun z : Z => (sourceSaved rate rewards C_star C_h q t control0 z i) ^ 2) μZ := by
  have hmeas := sourceSaved_sq_measurable rate rewards C_star C_h q t control0 i
  have hbound : ∀ z : Z,
      ‖(sourceSaved rate rewards C_star C_h q t control0 z i) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h0 := normalizedCurrentSaved_nonneg rate rewards C_star C_h q t control0
      (sourceCoords rate rewards C_star C_h q t control0 z).1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i
    have hle := normalizedCurrentSaved_le_beta_inv rate rewards C_star C_h q t control0
      (sourceCoords rate rewards C_star C_h q t control0 z).1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i
    change (normalizedCurrentSaved rate rewards C_star C_h q t control0
      (sourceCoords rate rewards C_star C_h q t control0 z).1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.1
      (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i) ^ 2 ≤ _
    nlinarith [sq_nonneg (1 / CanonicalRecordingRates.beta p rate.eta.val -
      normalizedCurrentSaved rate rewards C_star C_h q t control0
        (sourceCoords rate rewards C_star C_h q t control0 z).1
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1
        (sourceCoords rate rewards C_star C_h q t control0 z).2.2 i)]
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    (Filter.Eventually.of_forall hbound)

private theorem assignedFirstMoment_integrable (i : Fin (p.m - 1)) :
    Integrable (fun v : V => xiAt v i * quantizedAt v i) λA := by
  have hArm := ReferenceFirstLaunchRecordingSourceLaw.measurable_sampled_assigned rate t i
  let qarm : Fin p.K → ℝ := fun a =>
    QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
      (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) a)
      (((rewards t a).val : ℝ) / (D p : ℝ))
  let xarm : Fin p.K → ℝ := fun a =>
    CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) a
  have hqmeas : Measurable (fun v : V => qarm
      ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i)) :=
    (measurable_of_countable qarm).comp hArm
  have hxmeas : Measurable (fun v : V => xarm
      ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i)) :=
    (measurable_of_countable xarm).comp hArm
  have hmeas : Measurable (fun v : V => xiAt v i * quantizedAt v i) := by
    change Measurable (fun v =>
      xarm ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i) *
      qarm ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i))
    exact hxmeas.mul hqmeas
  have hbound : ∀ v : V, ‖xiAt v i * quantizedAt v i‖ ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro v
    have hp := firstLaunchParameters rate rewards t v i
    have hq0 := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
      (xiAt v i) (rhoAt v i) rate.eta.property
    have hq := quantizedValue_le_beta_inv rate rewards t v i
    have hxi : xiAt v i ≤ 1 := by
      let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
        rate.sourceCap (fun _ => 1) (by intro _; norm_num)
      have hrate : rates.rate (firstLaunchAssignedArm rate t v i) = xiAt v i := rfl
      rw [← hrate]
      exact rates.rate_le_one _
    have hq0' : 0 ≤ quantizedAt v i := by simpa [firstLaunchQuantizedValue] using hq0
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.1.le hq0')]
    calc
      xiAt v i * quantizedAt v i ≤ 1 * quantizedAt v i :=
        mul_le_mul_of_nonneg_right hxi hq0'
      _ = quantizedAt v i := one_mul _
      _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := hq
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
    (Filter.Eventually.of_forall hbound)

private theorem assignedSecondMoment_integrable (i : Fin (p.m - 1)) :
    Integrable (fun v : V => xiAt v i * (quantizedAt v i) ^ 2) λA := by
  have hArm := ReferenceFirstLaunchRecordingSourceLaw.measurable_sampled_assigned rate t i
  let qarm : Fin p.K → ℝ := fun a =>
    QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
      (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) a)
      (((rewards t a).val : ℝ) / (D p : ℝ))
  let xarm : Fin p.K → ℝ := fun a =>
    CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) a
  have hqmeas : Measurable (fun v : V => qarm
      ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i)) :=
    (measurable_of_countable qarm).comp hArm
  have hxmeas : Measurable (fun v : V => xarm
      ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i)) :=
    (measurable_of_countable xarm).comp hArm
  have hmeas : Measurable (fun v : V => xiAt v i * (quantizedAt v i) ^ 2) := by
    change Measurable (fun v =>
      xarm ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i) *
      (qarm ((ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t v).start.assignment.assigned i)) ^ 2)
    exact hxmeas.mul (hqmeas.pow_const 2)
  have hbound : ∀ v : V,
      ‖xiAt v i * (quantizedAt v i) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro v
    have hp := firstLaunchParameters rate rewards t v i
    have hq0 := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
      (xiAt v i) (rhoAt v i) rate.eta.property
    have hq := quantizedValue_le_beta_inv rate rewards t v i
    have hxi : xiAt v i ≤ 1 := by
      let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
        rate.sourceCap (fun _ => 1) (by intro _; norm_num)
      have hrate : rates.rate (firstLaunchAssignedArm rate t v i) = xiAt v i := rfl
      rw [← hrate]
      exact rates.rate_le_one _
    have hq0' : 0 ≤ quantizedAt v i := by simpa [firstLaunchQuantizedValue] using hq0
    have hsq : (quantizedAt v i) ^ 2 ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
      have hbeta : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
        div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      nlinarith [sq_nonneg (1 / CanonicalRecordingRates.beta p rate.eta.val -
        quantizedAt v i), hq0']
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp.1.le (sq_nonneg _))]
    calc
      xiAt v i * (quantizedAt v i) ^ 2 ≤ 1 * (quantizedAt v i) ^ 2 :=
        mul_le_mul_of_nonneg_right hxi (sq_nonneg _)
      _ = (quantizedAt v i) ^ 2 := one_mul _
      _ ≤ (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := hsq
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    (Filter.Eventually.of_forall hbound)

theorem sourceSaved_moment_readout_integrable (i : Fin (p.m - 1)) :
    Integrable (fun v : V => xiAt v i * quantizedAt v i) λA ∧
      Integrable (fun v : V => xiAt v i * (quantizedAt v i) ^ 2) λA :=
  ⟨assignedFirstMoment_integrable rate rewards t i,
    assignedSecondMoment_integrable rate rewards t i⟩

private theorem sourceSaved_eq_markerValue (z : Z) (i : Fin (p.m - 1)) :
    sourceSaved rate rewards C_star C_h q t control0 z i =
      markerValue
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1 i
        (sourceMark rate rewards C_star C_h q t control0 z) := by
  let c := sourceCoords rate rewards C_star C_h q t control0 z
  change normalizedCurrentSaved rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 i = _
  rw [normalizedCurrentSaved_eq_marker]
  rfl

private theorem sourceMomentKernel_measurable (i : Fin (p.m - 1)) :
    Measurable (fun w : (X × V) × Option (Fin p.K) =>
      markerValue w.1.2 i w.2) := by
  let qarm : Fin p.K → ℝ := fun a =>
    QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
      (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) a)
      (((rewards t a).val : ℝ) / (D p : ℝ))
  let fromMarker : Option (Fin p.K) × Fin p.K → ℝ := fun u =>
    if u.1 = some u.2 then qarm u.2 else 0
  have hfinite : Measurable fromMarker := measurable_of_countable _
  have harm : Measurable (fun w : (X × V) × Option (Fin p.K) =>
      (w.2, (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t w.1.2).start.assignment.assigned i)) :=
    measurable_snd.prodMk
      ((ReferenceFirstLaunchRecordingSourceLaw.measurable_sampled_assigned rate t i).comp
        (measurable_snd.comp measurable_fst))
  change Measurable (fromMarker ∘ fun w : (X × V) × Option (Fin p.K) =>
    (w.2, (ReferenceFirstLaunchRecordingPhysicalMarker.coordinateLaunch rate t w.1.2).start.assignment.assigned i))
  exact hfinite.comp harm

private theorem markerValue_firstMoment_readout (v : V) (i : Fin (p.m - 1)) :
    (∫ o, markerValue v i o ∂
      ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        xiAt v i * quantizedAt v i :=
  markerValue_integral rate rewards t v i

private theorem markerValue_secondMoment_readout (v : V) (i : Fin (p.m - 1)) :
    (∫ o, (markerValue v i o) ^ 2 ∂
      ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        xiAt v i * (quantizedAt v i) ^ 2 :=
  markerValue_sq_integral rate rewards t v i

/-- The original-source first-moment cylinder identity. The set is measured
under the inherited unnormalized source law, with the entire vector retained. -/
theorem sourceSaved_firstMoment_cylinder_integral (Aset : Set X) (Bset : Set V)
    (hA : MeasurableSet Aset) (hB : MeasurableSet Bset) (i : Fin (p.m - 1)) :
    (∫ z in {z : Z | (sourceCoords rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1 ∈ Bset},
      sourceSaved rate rewards C_star C_h q t control0 z i ∂μZ) =
      (μC Aset).toReal *
        (∫ v in Bset, xiAt v i * quantizedAt v i ∂λA) := by
  classical
  let cyl : Set (X × V) := Aset ×ˢ Bset
  let E : Set Z := {z | (sourceCoords rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
    (sourceCoords rate rewards C_star C_h q t control0 z).2.1 ∈ Bset}
  let F : Z → (X × V) × Option (Fin p.K) := fun z =>
    let c := sourceCoords rate rewards C_star C_h q t control0 z
    ((c.1, c.2.1), sourceMark rate rewards C_star C_h q t control0 z)
  let targetSet : Set ((X × V) × Option (Fin p.K)) := cyl ×ˢ Set.univ
  let kernel : (X × V) × Option (Fin p.K) → ℝ := fun w =>
    markerValue w.1.2 i w.2
  let H : ((X × V) × Option (Fin p.K)) → ℝ := targetSet.indicator kernel
  have hcyl : MeasurableSet cyl := hA.prod hB
  have htarget : MeasurableSet targetSet := hcyl.prod MeasurableSet.univ
  have hE : MeasurableSet E := by
    exact (hA.preimage ((ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
      rate rewards C_star C_h q t control0).fst)).inter
      (hB.preimage ((ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h q t control0).snd.fst))
  have hcoords := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have hF : Measurable F := by
    change Measurable (fun z : Z =>
      (((sourceCoords rate rewards C_star C_h q t control0 z).1,
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1),
        sourceMark rate rewards C_star C_h q t control0 z))
    exact ((hcoords.fst.prodMk hcoords.snd.fst).prodMk
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceMarker
        rate rewards C_star C_h q t control0))
  have hFmap : MeasureTheory.Measure.map F μZ = MeasureTheory.Measure.prod (MeasureTheory.Measure.prod μC λA)
      (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) := by
    simpa only [F] using ReferenceFirstLaunchRecordingSourceLaw.source_joint_map
      rate rewards C_star C_h q t control0
  have hkernel : Measurable kernel := sourceMomentKernel_measurable
    rate rewards C_star C_h q t control0 i
  have hH : Measurable H := hkernel.indicator htarget
  have hBound : ∀ w, ‖H w‖ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    intro w
    by_cases hw : w ∈ targetSet
    · simp only [H, Set.indicator_of_mem hw]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (markerValue_range rate rewards t w.1.2 i w.2).1]
      exact (markerValue_range rate rewards t w.1.2 i w.2).2
    · have hzero : H w = 0 := by simp [H, hw]
      simp only [hzero, norm_zero]
      exact le_of_lt (div_pos (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property))
  have hHint : Integrable H (MeasureTheory.Measure.prod (MeasureTheory.Measure.prod μC λA)
      (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) := by
    exact Integrable.of_bound hH.aestronglyMeasurable
      (1 / CanonicalRecordingRates.beta p rate.eta.val)
      (Filter.Eventually.of_forall hBound)
  have hSourceIndicator : E.indicator
      (fun z => sourceSaved rate rewards C_star C_h q t control0 z i) = H ∘ F := by
    funext z
    by_cases hz : z ∈ E
    · have hmem : F z ∈ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Set.indicator_apply, Function.comp_apply, H, targetSet, cyl, hz, hmem]
      rw [sourceSaved_eq_markerValue]
    · have hmem : F z ∉ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Set.indicator_apply, Function.comp_apply, H, targetSet, cyl, hmem, hz]
  have hFiber : ∀ y : X × V,
      (∫ o, H (y, o) ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        cyl.indicator (fun y => xiAt y.2 i * quantizedAt y.2 i) y := by
    intro y
    by_cases hy : y ∈ cyl
    · have heq : (fun o => H (y, o)) =
          (fun o => markerValue y.2 i o) := by
        funext o
        simp [H, targetSet, kernel, hy]
      rw [heq, markerValue_firstMoment_readout]
      simp [hy]
    · have heq : (fun o => H (y, o)) = fun _ => (0 : ℝ) := by
        funext o
        simp [H, targetSet, hy]
      rw [heq]
      simp [hy]
  have hAint : (∫ x in Aset, (1 : ℝ) ∂μC) = (μC Aset).toReal := by
    rw [setIntegral_const]
    simp [measureReal_def]
  calc
    _ = ∫ z, E.indicator
        (fun z => sourceSaved rate rewards C_star C_h q t control0 z i) z ∂μZ := by
      rw [← integral_indicator hE]
    _ = ∫ z, H (F z) ∂μZ := by rw [hSourceIndicator]; simp only [Function.comp_apply]
    _ = ∫ w, H w ∂(MeasureTheory.Measure.map F μZ) :=
      (MeasureTheory.integral_map hF.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ w, H w ∂(MeasureTheory.Measure.prod (MeasureTheory.Measure.prod μC λA)
        (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) := by rw [hFmap]
    _ = ∫ y, ∫ o, H (y, o)
        ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate ∂(MeasureTheory.Measure.prod μC λA) :=
      integral_prod H hHint
    _ = ∫ y, cyl.indicator (fun y => xiAt y.2 i * quantizedAt y.2 i) y
        ∂(MeasureTheory.Measure.prod μC λA) := by
      congr 1
      funext y
      exact hFiber y
    _ = ∫ y in cyl, (1 : ℝ) * (xiAt y.2 i * quantizedAt y.2 i) ∂(MeasureTheory.Measure.prod μC λA) := by
      rw [integral_indicator hcyl]
      congr 1
      funext y
      simp [one_mul]
    _ = (∫ x in Aset, (1 : ℝ) ∂μC) *
        (∫ v in Bset, xiAt v i * quantizedAt v i ∂λA) := by
      exact (setIntegral_prod_mul (fun _ : X => (1 : ℝ))
        (fun v => xiAt v i * quantizedAt v i) Aset Bset)
    _ = (μC Aset).toReal *
        (∫ v in Bset, xiAt v i * quantizedAt v i ∂λA) := by rw [hAint]

/-- The original-source second-moment cylinder identity. -/
theorem sourceSaved_secondMoment_cylinder_integral (Aset : Set X) (Bset : Set V)
    (hA : MeasurableSet Aset) (hB : MeasurableSet Bset) (i : Fin (p.m - 1)) :
    (∫ z in {z : Z | (sourceCoords rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1 ∈ Bset},
      (sourceSaved rate rewards C_star C_h q t control0 z i) ^ 2 ∂μZ) =
      (μC Aset).toReal *
        (∫ v in Bset, xiAt v i * (quantizedAt v i) ^ 2 ∂λA) := by
  classical
  let cyl : Set (X × V) := Aset ×ˢ Bset
  let E : Set Z := {z | (sourceCoords rate rewards C_star C_h q t control0 z).1 ∈ Aset ∧
    (sourceCoords rate rewards C_star C_h q t control0 z).2.1 ∈ Bset}
  let F : Z → (X × V) × Option (Fin p.K) := fun z =>
    let c := sourceCoords rate rewards C_star C_h q t control0 z
    ((c.1, c.2.1), sourceMark rate rewards C_star C_h q t control0 z)
  let targetSet : Set ((X × V) × Option (Fin p.K)) := cyl ×ˢ Set.univ
  let kernel : (X × V) × Option (Fin p.K) → ℝ := fun w =>
    markerValue w.1.2 i w.2
  let H : ((X × V) × Option (Fin p.K)) → ℝ := targetSet.indicator (fun w => kernel w ^ 2)
  have hcyl : MeasurableSet cyl := hA.prod hB
  have htarget : MeasurableSet targetSet := hcyl.prod MeasurableSet.univ
  have hE : MeasurableSet E := by
    exact (hA.preimage ((ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
      rate rewards C_star C_h q t control0).fst)).inter
      (hB.preimage ((ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h q t control0).snd.fst))
  have hcoords := ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
    rate rewards C_star C_h q t control0
  have hF : Measurable F := by
    change Measurable (fun z : Z =>
      (((sourceCoords rate rewards C_star C_h q t control0 z).1,
        (sourceCoords rate rewards C_star C_h q t control0 z).2.1),
        sourceMark rate rewards C_star C_h q t control0 z))
    exact ((hcoords.fst.prodMk hcoords.snd.fst).prodMk
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceMarker
        rate rewards C_star C_h q t control0))
  have hFmap : MeasureTheory.Measure.map F μZ = MeasureTheory.Measure.prod (MeasureTheory.Measure.prod μC λA)
      (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) := by
    simpa only [F] using ReferenceFirstLaunchRecordingSourceLaw.source_joint_map
      rate rewards C_star C_h q t control0
  have hkernel : Measurable kernel := sourceMomentKernel_measurable
    rate rewards C_star C_h q t control0 i
  have hH : Measurable H := (hkernel.pow_const 2).indicator htarget
  have hBound : ∀ w, ‖H w‖ ≤
      (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro w
    by_cases hw : w ∈ targetSet
    · simp only [H, Set.indicator_of_mem hw]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hr := markerValue_range rate rewards t w.1.2 i w.2
      have hbpos : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
        div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      nlinarith [sq_nonneg (1 / CanonicalRecordingRates.beta p rate.eta.val -
        markerValue w.1.2 i w.2)]
    · have hzero : H w = 0 := by simp [H, hw]
      simp only [hzero, norm_zero]
      exact sq_nonneg (1 / CanonicalRecordingRates.beta p rate.eta.val)
  have hHint : Integrable H (MeasureTheory.Measure.prod (MeasureTheory.Measure.prod μC λA)
      (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) := by
    exact Integrable.of_bound hH.aestronglyMeasurable
      ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
      (Filter.Eventually.of_forall hBound)
  have hSourceIndicator : E.indicator
      (fun z => (sourceSaved rate rewards C_star C_h q t control0 z i) ^ 2) = H ∘ F := by
    funext z
    by_cases hz : z ∈ E
    · have hmem : F z ∈ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Set.indicator_apply, Function.comp_apply, H, targetSet, cyl, hz, hmem]
      rw [sourceSaved_eq_markerValue]
    · have hmem : F z ∉ targetSet := by simpa [F, E, targetSet, cyl] using hz
      simp [Set.indicator_apply, Function.comp_apply, H, targetSet, cyl, hmem, hz]
  have hFiber : ∀ y : X × V,
      (∫ o, H (y, o) ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) =
        cyl.indicator (fun y => xiAt y.2 i * (quantizedAt y.2 i) ^ 2) y := by
    intro y
    by_cases hy : y ∈ cyl
    · have heq : (fun o => H (y, o)) =
          (fun o => (markerValue y.2 i o) ^ 2) := by
        funext o
        simp [H, targetSet, kernel, hy]
      rw [heq, markerValue_secondMoment_readout]
      simp [hy]
    · have heq : (fun o => H (y, o)) = fun _ => (0 : ℝ) := by
        funext o
        simp [H, targetSet, hy]
      rw [heq]
      simp [hy]
  have hAint : (∫ x in Aset, (1 : ℝ) ∂μC) = (μC Aset).toReal := by
    rw [setIntegral_const]
    simp [measureReal_def]
  calc
    _ = ∫ z, E.indicator
        (fun z => (sourceSaved rate rewards C_star C_h q t control0 z i) ^ 2) z ∂μZ := by
      rw [← integral_indicator hE]
    _ = ∫ z, H (F z) ∂μZ := by rw [hSourceIndicator]; simp only [Function.comp_apply]
    _ = ∫ w, H w ∂(MeasureTheory.Measure.map F μZ) :=
      (MeasureTheory.integral_map hF.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ w, H w ∂(MeasureTheory.Measure.prod (MeasureTheory.Measure.prod μC λA)
        (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate)) := by rw [hFmap]
    _ = ∫ y, ∫ o, H (y, o)
        ∂ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate ∂(MeasureTheory.Measure.prod μC λA) :=
      integral_prod H hHint
    _ = ∫ y, cyl.indicator (fun y => xiAt y.2 i * (quantizedAt y.2 i) ^ 2) y
        ∂(MeasureTheory.Measure.prod μC λA) := by
      congr 1
      funext y
      exact hFiber y
    _ = ∫ y in cyl, (1 : ℝ) * (xiAt y.2 i * (quantizedAt y.2 i) ^ 2) ∂(MeasureTheory.Measure.prod μC λA) := by
      rw [integral_indicator hcyl]
      congr 1
      funext y
      simp [one_mul]
    _ = (∫ x in Aset, (1 : ℝ) ∂μC) *
        (∫ v in Bset, xiAt v i * (quantizedAt v i) ^ 2 ∂λA) := by
      exact (setIntegral_prod_mul (fun _ : X => (1 : ℝ))
        (fun v => xiAt v i * (quantizedAt v i) ^ 2) Aset Bset)
    _ = (μC Aset).toReal *
        (∫ v in Bset, xiAt v i * (quantizedAt v i) ^ 2 ∂λA) := by rw [hAint]

end OriginalSource


end Bandits.Support.ReferenceFirstLaunchSavedSourceMoments

end
