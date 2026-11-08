/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveEmptyPendingSourceMoments

import Mathlib.Tactic

/-!
# Accepted strict-past moments on the actual empty-pending source

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The current cell is the original index `t.val - s` cell of the actual
`t.val - s + 1` source run. The retained set tests only the preceding cells.
The accepted projection uses the existing chronological queue record, so an
update which first overflows remains included. These are internal conditional
moment results on the original unnormalized empty-pending measure; they do not
identify `Fempty` with a manuscript history or close a source-facing theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingAcceptedMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q t s hs control0
local notation "Xe" => ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty rate rewards C_star C_h q t s hs control0
local notation "xofE" => ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0
local notation "xiE" => ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control0
local notation "muE" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0
local notation "nuE" => ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty rate rewards C_star C_h q t s hs control0
local notation "Fempty" => ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty rate rewards C_star C_h q t s hs control0
local notation "prefixEmpty" => ReferenceFirstLiveEmptyPendingMarkerLaw.prefixEmpty rate rewards C_star C_h q t s hs control0
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

/-- The literal numerical run over the first `t.val - s` cells of the
original source window. -/
def past (z : Ze) : RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run queue (ReferenceFirstLiveEmptyPendingSourceMoments.actualPastCells rate rewards C_star C_h q t s hs control0 z)

/-- Strict-past retention tests the queue state before the current original
source cell is applied. -/
def G : Set Ze := {z | (past rate rewards C_star C_h q t s hs control0 z).overflow = false}

/-- The actual accepted arrival from the chronological record for the current
original source cell. -/
def acceptedA (j : Fin p.K) (z : Ze) : ℝ :=
  (RecordedQueueRun.acceptedArrival
    (RecordedQueueRun.acceptedRecord queue
      (past rate rewards C_star C_h q t s hs control0 z)
      (ReferenceFirstLiveEmptyPendingSourceMoments.cell rate rewards C_star C_h q t s hs control0 z) j) : ℝ) / scale

/-- The first source coefficient on the original empty carrier. -/
def firstCoefficient (j : Fin p.K) (z : Ze) : ℝ :=
  xiE (xofE z) j * ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 (xofE z) j

/-- The square coefficient is the marker rate times the square of the
quantized source value. -/
def secondCoefficient (j : Fin p.K) (z : Ze) : ℝ :=
  xiE (xofE z) j * (ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 (xofE z) j) ^ 2

/-- The actual accepted record is the current quantized arrival exactly when
the strict-past run has not overflowed. The current cell is enabled on every
empty-pending source point. -/
theorem acceptedRecord_eq_if_G (j : Fin p.K) (z : Ze) :
    RecordedQueueRun.acceptedRecord queue
        (past rate rewards C_star C_h q t s hs control0 z)
        (ReferenceFirstLiveEmptyPendingSourceMoments.cell rate rewards C_star C_h q t s hs control0 z) j =
      if z ∈ G rate rewards C_star C_h q t s hs control0 then
        (true, RecordedQueueRun.quantizedArrival queue
          (ReferenceFirstLiveEmptyPendingSourceMoments.cell rate rewards C_star C_h q t s hs control0 z) j)
      else (false, 0) := by
  have henabled := (ReferenceFirstLiveEmptyPendingSourceMoments.cell_actual_facts rate rewards C_star C_h q t s hs control0 z).1
  by_cases hz : z ∈ G rate rewards C_star C_h q t s hs control0
  · have hpast : (past rate rewards C_star C_h q t s hs control0 z).overflow = false := by
      simpa [G] using hz
    simp [RecordedQueueRun.acceptedRecord, hpast, henabled, G]
  · have hoverflow :
        (past rate rewards C_star C_h q t s hs control0 z).overflow = true := by
      cases h : (past rate rewards C_star C_h q t s hs control0 z).overflow <;>
        simp_all [G]
    simp [RecordedQueueRun.acceptedRecord, hoverflow, G]

/-- The accepted-record projection equals the strict-past indicator times the
literal quantized arrival from `M`. -/
theorem acceptedA_eq_indicator_a (j : Fin p.K) (z : Ze) :
    acceptedA rate rewards C_star C_h q t s hs control0 j z =
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z => ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) z := by
  by_cases hz : z ∈ G rate rewards C_star C_h q t s hs control0
  · have hpast : (past rate rewards C_star C_h q t s hs control0 z).overflow = false := by
      simpa [G] using hz
    simp [acceptedA, G, hpast, acceptedRecord_eq_if_G,
      ReferenceFirstLiveEmptyPendingSourceMoments.a, RecordedQueueRun.acceptedArrival]
  · have hpast : (past rate rewards C_star C_h q t s hs control0 z).overflow = true := by
      cases h : (past rate rewards C_star C_h q t s hs control0 z).overflow <;>
        simp_all [G]
    simp [acceptedA, G, hpast, acceptedRecord_eq_if_G,
      ReferenceFirstLiveEmptyPendingSourceMoments.a, RecordedQueueRun.acceptedArrival]

/-- The past queue state is unchanged when the actual source is replaced by
its literal strict prefix. This is the public numerical prefix transport on
the original `n + 1` source run. -/
theorem past_prefixEmpty_eq (z : Ze) :
    past rate rewards C_star C_h q t s hs control0
        (prefixEmpty z) =
      past rate rewards C_star C_h q t s hs control0 z := by
  let w := prefixEmpty z
  have hw : w.val.val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val := by
    change (ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ
      rate rewards C_star C_h q t s hs control0 z.val).val = _
    rw [ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val]
  have hrun := ReferenceFirstLiveNumericalPrefixTemporal.numerical_run_prefix_eq
    rate rewards C_star C_h q t s hs control0 z.val w.val hw
  have htakeZ := ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor
    rate rewards C_star C_h q t s hs control0 z.val
  have htakeW := ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor
    rate rewards C_star C_h q t s hs control0 w.val
  have hrun' :
      RecordedQueueRun.run queue (ReferenceFirstLiveEmptyPendingSourceMoments.actualPastCells rate rewards C_star C_h q t s hs control0 z) =
        RecordedQueueRun.run queue
          (ReferenceFirstLiveEmptyPendingSourceMoments.actualPastCells rate rewards C_star C_h q t s hs control0 w) := by
    simpa only [ReferenceFirstLiveEmptyPendingSourceMoments.actualPastCells, ← htakeZ, ← htakeW] using hrun
  simpa only [past] using hrun'.symm

/-- Ambient Borel measurability of the literal strict-past event, from the
public Borel readout of the same actual numerical queue run. -/
theorem measurableSet_G_ambient :
    MeasurableSet (G rate rewards C_star C_h q t s hs control0) := by
  have hread : Measurable (fun z : Ze =>
      ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0 z.val) :=
    (ReferenceFirstLiveNumericalQueueBorel.measurable_numericalCountRunReadout
      rate rewards C_star C_h q t s hs control0).comp
        (measurable_subtype_coe : Measurable (fun z : Ze => z.val))
  have hover : Measurable (fun z : Ze =>
      (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
        rate rewards C_star C_h q t s hs control0 z.val).2.1) :=
    measurable_fst.comp (measurable_snd.comp hread)
  have heq : G rate rewards C_star C_h q t s hs control0 =
      (fun z : Ze =>
        (ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout
          rate rewards C_star C_h q t s hs control0 z.val).2.1) ⁻¹' {false} := by
    ext z
    change (past rate rewards C_star C_h q t s hs control0 z).overflow = false ↔ _
    simp [past, ReferenceFirstLiveEmptyPendingSourceMoments.actualPastCells,
      ReferenceFirstLiveNumericalQueueBorel.numericalCountRunReadout]
  rw [heq]
  exact (measurableSet_singleton false).preimage hover

/-- Strict-past retention is measurable in the original current-control
field. Prefix invariance is derived from actual numerical cells, not assumed
as a premise. -/
theorem measurableSet_G : MeasurableSet[Fempty] (G rate rewards C_star C_h q t s hs control0) := by
  have hprefix := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_prefixEmpty rate rewards C_star C_h q t s hs control0
  have heq : G rate rewards C_star C_h q t s hs control0 =
      (prefixEmpty) ⁻¹'
        G rate rewards C_star C_h q t s hs control0 := by
    ext z
    change (past rate rewards C_star C_h q t s hs control0 z).overflow = false ↔
      (past rate rewards C_star C_h q t s hs control0
        (prefixEmpty z)).overflow = false
    rw [past_prefixEmpty_eq]
  rw [heq]
  exact (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0).preimage hprefix

/-- The original remainder-prefix map restricted to the empty carrier. -/
def remainderPrefixEmpty (x : Xe) : ReferenceFirstLiveSourceSavedConditionalMoments.SourceInput p :=
  ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix
    rate rewards C_star C_h q t s hs control0 x.val

theorem measurable_remainderPrefixEmpty :
    Measurable (remainderPrefixEmpty rate rewards C_star C_h q t s hs control0) :=
  (ReferenceFirstLiveSourceSavedConditionalMoments.measurable_remainderPrefix
    rate rewards C_star C_h q t s hs control0).comp measurable_subtype_coe

/-- On the actual source projection, the restricted remainder prefix is the
original `c_t` readout that defines `Fempty`. -/
theorem remainderPrefixEmpty_xof (z : Ze) :
    remainderPrefixEmpty rate rewards C_star C_h q t s hs control0
        (xofE z) =
      ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val := by
  change ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix
      rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z.val) = _
  rw [ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix_sourceRetained,
    ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val,
    ← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]

/-- Every set measurable in `Fempty` factors through the public remainder
prefix restricted to `Xe`. -/
theorem Fempty_cell (S : Set Ze) (hS : MeasurableSet[Fempty] S) :
    ∃ Aset : Set Xe, MeasurableSet Aset ∧ {z : Ze | xofE z ∈ Aset} = S := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace (ReferenceFirstLiveSourceSavedConditionalMoments.SourceInput p)).comap
      (fun z : Ze => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)] S at hS
  obtain ⟨V, hV, hVS⟩ := MeasurableSpace.measurableSet_comap.mp hS
  let Aset : Set Xe :=
    (remainderPrefixEmpty rate rewards C_star C_h q t s hs control0) ⁻¹' V
  refine ⟨Aset, hV.preimage
    (measurable_remainderPrefixEmpty rate rewards C_star C_h q t s hs control0), ?_⟩
  calc
    {z : Ze | xofE z ∈ Aset} =
        (fun z : Ze =>
          ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val) ⁻¹' V := by
      ext z
      change remainderPrefixEmpty rate rewards C_star C_h q t s hs control0 (xofE z) ∈ V ↔ _
      rw [remainderPrefixEmpty_xof]
      rfl
    _ = S := hVS

/-- The marker rate transports unchanged under the actual prefix replacement. -/
theorem xiEmpty_xof_prefix (j : Fin p.K) (z : Ze) :
    xiE (xofE (prefixEmpty z)) j =
      xiE (xofE z) j := by
  simpa [ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty, ReferenceFirstLiveEmptyPendingMarkerLaw.selectedBaselinePayload] using
    congrArg (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor j)
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selected_payload_prefix rate rewards C_star C_h q t s hs control0 z)

/-- The first coefficient transports unchanged under the actual prefix
replacement because the selected payload anchor and source reward are the
same. -/
theorem firstCoefficient_prefixEmpty (j : Fin p.K) (z : Ze) :
    firstCoefficient rate rewards C_star C_h q t s hs control0 j
        (prefixEmpty z) =
      firstCoefficient rate rewards C_star C_h q t s hs control0 j z := by
  have hxi := xiEmpty_xof_prefix rate rewards C_star C_h q t s hs control0 j z
  have hv : ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0
      (xofE (prefixEmpty z)) j =
      ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 (xofE z) j := by
    unfold ReferenceFirstLiveEmptyPendingSourceMoments.v
    rw [hxi]
  simp only [firstCoefficient]
  rw [hxi, hv]

/-- The square coefficient transports on the same source prefix. -/
theorem secondCoefficient_prefixEmpty (j : Fin p.K) (z : Ze) :
    secondCoefficient rate rewards C_star C_h q t s hs control0 j
        (prefixEmpty z) =
      secondCoefficient rate rewards C_star C_h q t s hs control0 j z := by
  have hxi := xiEmpty_xof_prefix rate rewards C_star C_h q t s hs control0 j z
  have hv : ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0
      (xofE (prefixEmpty z)) j =
      ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 (xofE z) j := by
    unfold ReferenceFirstLiveEmptyPendingSourceMoments.v
    rw [hxi]
  simp only [secondCoefficient]
  rw [hxi, hv]

/-- The first source coefficient is measurable in the original `Fempty`
field. -/
theorem measurable_firstCoefficient (j : Fin p.K) :
    Measurable[Fempty] (firstCoefficient rate rewards C_star C_h q t s hs control0 j) := by
  have hxi := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty_source rate rewards C_star C_h q t s hs control0 j
  have hpref := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_prefixEmpty
    rate rewards C_star C_h q t s hs control0
  have hxof : Measurable[Fempty] (fun z : Ze => xofE (prefixEmpty z)) :=
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
      rate rewards C_star C_h q t s hs control0).comp hpref
  have hv : Measurable[Fempty]
      (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 (xofE z) j) :=
    (by
      have hvpre := (ReferenceFirstLiveEmptyPendingSourceMoments.measurable_v
        rate rewards C_star C_h q t s hs control0 j).comp hxof
      have htransport :
          (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.v
            rate rewards C_star C_h q t s hs control0 (xofE (prefixEmpty z)) j) =
          (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.v
            rate rewards C_star C_h q t s hs control0 (xofE z) j) := by
        funext z
        unfold ReferenceFirstLiveEmptyPendingSourceMoments.v
        rw [xiEmpty_xof_prefix rate rewards C_star C_h q t s hs control0 j z]
      rw [← htransport]
      exact hvpre)
  exact hxi.mul hv

/-- The square source coefficient is measurable in the original `Fempty`
field. -/
theorem measurable_secondCoefficient (j : Fin p.K) :
    Measurable[Fempty] (secondCoefficient rate rewards C_star C_h q t s hs control0 j) := by
  have hxi := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty_source rate rewards C_star C_h q t s hs control0 j
  have hpref := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_prefixEmpty
    rate rewards C_star C_h q t s hs control0
  have hxof : Measurable[Fempty] (fun z : Ze => xofE (prefixEmpty z)) :=
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
      rate rewards C_star C_h q t s hs control0).comp hpref
  have hv : Measurable[Fempty]
      (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 (xofE z) j) :=
    (by
      have hvpre := (ReferenceFirstLiveEmptyPendingSourceMoments.measurable_v
        rate rewards C_star C_h q t s hs control0 j).comp hxof
      have htransport :
          (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.v
            rate rewards C_star C_h q t s hs control0 (xofE (prefixEmpty z)) j) =
          (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.v
            rate rewards C_star C_h q t s hs control0 (xofE z) j) := by
        funext z
        unfold ReferenceFirstLiveEmptyPendingSourceMoments.v
        rw [xiEmpty_xof_prefix rate rewards C_star C_h q t s hs control0 j z]
      rw [← htransport]
      exact hvpre)
  exact hxi.mul (hv.pow_const 2)

theorem measurable_firstCoefficient_ambient (j : Fin p.K) :
    Measurable (firstCoefficient rate rewards C_star C_h q t s hs control0 j) := by
  exact
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty
      rate rewards C_star C_h q t s hs control0 j).comp
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
          rate rewards C_star C_h q t s hs control0) |>.mul
      ((ReferenceFirstLiveEmptyPendingSourceMoments.measurable_v
        rate rewards C_star C_h q t s hs control0 j).comp
          (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
            rate rewards C_star C_h q t s hs control0))

theorem measurable_secondCoefficient_ambient (j : Fin p.K) :
    Measurable (secondCoefficient rate rewards C_star C_h q t s hs control0 j) := by
  exact
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty
      rate rewards C_star C_h q t s hs control0 j).comp
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
          rate rewards C_star C_h q t s hs control0) |>.mul
      (((ReferenceFirstLiveEmptyPendingSourceMoments.measurable_v
        rate rewards C_star C_h q t s hs control0 j).comp
          (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
            rate rewards C_star C_h q t s hs control0)).pow_const 2)

theorem firstCoefficient_bounds (j : Fin p.K) (z : Ze) :
    ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j - xiE (xofE z) j / scale ≤
        firstCoefficient rate rewards C_star C_h q t s hs control0 j z ∧
      0 ≤ firstCoefficient rate rewards C_star C_h q t s hs control0 j z ∧
      firstCoefficient rate rewards C_star C_h q t s hs control0 j z ≤
        ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j ∧
      ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j ≤ 1 := by
  exact ReferenceFirstLiveEmptyPendingSourceMoments.xi_mul_v_bounds rate rewards C_star C_h q t s hs control0 (xofE z) j

theorem secondCoefficient_bounds (j : Fin p.K) (z : Ze) :
    0 ≤ secondCoefficient rate rewards C_star C_h q t s hs control0 j z ∧
      secondCoefficient rate rewards C_star C_h q t s hs control0 j z ≤
        (ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j) ^ 2 / xiE (xofE z) j ∧
      (ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j) ^ 2 / xiE (xofE z) j ≤
        1 / xiE (xofE z) j ∧
      1 / xiE (xofE z) j ≤ 1 / beta := by
  exact ReferenceFirstLiveEmptyPendingSourceMoments.xi_mul_v_sq_bounds rate rewards C_star C_h q t s hs control0 (xofE z) j

/-- The first coefficient is integrable under the same unnormalized original
source measure, including null strata. -/
theorem integrable_firstCoefficient (j : Fin p.K) :
    Integrable (firstCoefficient rate rewards C_star C_h q t s hs control0 j) muE := by
  apply Integrable.of_bound (μ := muE)
    (measurable_firstCoefficient_ambient rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (firstCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.1]
  exact (firstCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.2.1.trans
    (firstCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.2.2

/-- The square coefficient is integrable under the same finite measure. -/
theorem integrable_secondCoefficient (j : Fin p.K) :
    Integrable (secondCoefficient rate rewards C_star C_h q t s hs control0 j) muE := by
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  apply Integrable.of_bound (μ := muE)
    (measurable_secondCoefficient_ambient rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    (1 / beta)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).1]
  exact (secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.1.trans
    ((secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.2.1.trans
      (secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.2.2)

/-- Integrating a source coefficient on a prefix cell is the pushforward of
the corresponding remainder coefficient under `xofEmpty`. -/
theorem firstCoefficient_cell_integral (Aset : Set Xe) (hAset : MeasurableSet Aset)
    (j : Fin p.K) :
    (∫ z in {z : Ze | xofE z ∈ Aset},
      firstCoefficient rate rewards C_star C_h q t s hs control0 j z ∂muE) =
    ∫ x in Aset, xiE x j * ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 x j ∂nuE := by
  let sourceCell : Set Ze := {z | xofE z ∈ Aset}
  let g : Xe → ℝ := fun x => xiE x j * ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 x j
  have hsourceCell : MeasurableSet sourceCell :=
    hAset.preimage (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty rate rewards C_star C_h q t s hs control0)
  have hg : Measurable g :=
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty rate rewards C_star C_h q t s hs control0 j).mul
      (ReferenceFirstLiveEmptyPendingSourceMoments.measurable_v rate rewards C_star C_h q t s hs control0 j)
  have hindicator :
      (fun z : Ze => sourceCell.indicator (fun z => g (xofE z)) z) =
        (Aset.indicator g) ∘ xofE := by
    funext z
    exact Set.indicator_comp_right xofE (s := Aset) (g := g) (x := z)
  calc
    _ = ∫ z, sourceCell.indicator (fun z => g (xofE z)) z ∂muE :=
      (integral_indicator hsourceCell).symm
    _ = ∫ z, (Aset.indicator g) (xofE z) ∂muE := by rw [hindicator]; rfl
    _ = ∫ x, Aset.indicator g x ∂((muE).map xofE) :=
      (integral_map
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty rate rewards C_star C_h q t s hs control0).aemeasurable
        (hg.indicator hAset).aestronglyMeasurable).symm
    _ = ∫ x in Aset, g x ∂nuE := by
      rw [ReferenceFirstLiveEmptyPendingSourceMoments.map_xofEmpty rate rewards C_star C_h q t s hs control0,
        integral_indicator hAset]

/-- Integrating the square coefficient uses the same original source map. -/
theorem secondCoefficient_cell_integral (Aset : Set Xe) (hAset : MeasurableSet Aset)
    (j : Fin p.K) :
    (∫ z in {z : Ze | xofE z ∈ Aset},
      secondCoefficient rate rewards C_star C_h q t s hs control0 j z ∂muE) =
    ∫ x in Aset, xiE x j * (ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∂nuE := by
  let sourceCell : Set Ze := {z | xofE z ∈ Aset}
  let g : Xe → ℝ := fun x => xiE x j * (ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 x j) ^ 2
  have hsourceCell : MeasurableSet sourceCell :=
    hAset.preimage (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty rate rewards C_star C_h q t s hs control0)
  have hg : Measurable g :=
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty rate rewards C_star C_h q t s hs control0 j).mul
      ((ReferenceFirstLiveEmptyPendingSourceMoments.measurable_v rate rewards C_star C_h q t s hs control0 j).pow_const 2)
  have hindicator :
      (fun z : Ze => sourceCell.indicator (fun z => g (xofE z)) z) =
        (Aset.indicator g) ∘ xofE := by
    funext z
    exact Set.indicator_comp_right xofE (s := Aset) (g := g) (x := z)
  calc
    _ = ∫ z, sourceCell.indicator (fun z => g (xofE z)) z ∂muE :=
      (integral_indicator hsourceCell).symm
    _ = ∫ z, (Aset.indicator g) (xofE z) ∂muE := by rw [hindicator]; rfl
    _ = ∫ x, Aset.indicator g x ∂((muE).map xofE) :=
      (integral_map
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty rate rewards C_star C_h q t s hs control0).aemeasurable
        (hg.indicator hAset).aestronglyMeasurable).symm
    _ = ∫ x in Aset, g x ∂nuE := by
      rw [ReferenceFirstLiveEmptyPendingSourceMoments.map_xofEmpty rate rewards C_star C_h q t s hs control0,
        integral_indicator hAset]

/-- The raw first moment of `ReferenceFirstLiveEmptyPendingSourceMoments.a` conditioned on the actual original
strict-past field. -/
theorem a_condExp_firstMoment (j : Fin p.K) :
    muE[(fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) | Fempty] =ᵐ[muE]
      firstCoefficient rate rewards C_star C_h q t s hs control0 j := by
  have hfield := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le rate rewards C_star C_h q t s hs control0
  have : IsFiniteMeasure ((muE).trim hfield) := by infer_instance
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hfield
    (ReferenceFirstLiveEmptyPendingSourceMoments.integrable_a rate rewards C_star C_h q t s hs control0 j)
  · intro S hS _
    exact (integrable_firstCoefficient rate rewards C_star C_h q t s hs control0 j).integrableOn
  · intro S hS _
    obtain ⟨Aset, hAset, hSA⟩ :=
      Fempty_cell rate rewards C_star C_h q t s hs control0 S hS
    exact (calc
      (∫ z in S, ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j ∂muE) =
          ∫ z in {z : Ze | xofE z ∈ Aset},
            ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j ∂muE := by rw [hSA]
      _ = ∫ x in Aset, xiE x j * ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 x j ∂nuE :=
        ReferenceFirstLiveEmptyPendingSourceMoments.source_firstMoment_cell_integral rate rewards C_star C_h q t s hs control0 Aset hAset j
      _ = ∫ z in {z : Ze | xofE z ∈ Aset},
            firstCoefficient rate rewards C_star C_h q t s hs control0 j z ∂muE :=
        (firstCoefficient_cell_integral rate rewards C_star C_h q t s hs control0 Aset hAset j).symm
      _ = ∫ z in S, firstCoefficient rate rewards C_star C_h q t s hs control0 j z ∂muE := by
        rw [hSA]).symm
  · exact (measurable_firstCoefficient
      rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable

/-- The raw square moment of `ReferenceFirstLiveEmptyPendingSourceMoments.a` conditioned on the same original field. -/
theorem a_condExp_secondMoment (j : Fin p.K) :
    muE[(fun z : Ze => (ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2) | Fempty] =ᵐ[muE]
      secondCoefficient rate rewards C_star C_h q t s hs control0 j := by
  have hfield := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le rate rewards C_star C_h q t s hs control0
  have : IsFiniteMeasure ((muE).trim hfield) := by infer_instance
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hfield
    (ReferenceFirstLiveEmptyPendingSourceMoments.integrable_a_sq rate rewards C_star C_h q t s hs control0 j)
  · intro S hS _
    exact (integrable_secondCoefficient rate rewards C_star C_h q t s hs control0 j).integrableOn
  · intro S hS _
    obtain ⟨Aset, hAset, hSA⟩ :=
      Fempty_cell rate rewards C_star C_h q t s hs control0 S hS
    exact (calc
      (∫ z in S, (ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2 ∂muE) =
          ∫ z in {z : Ze | xofE z ∈ Aset},
            (ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2 ∂muE := by rw [hSA]
      _ = ∫ x in Aset,
            xiE x j * (ReferenceFirstLiveEmptyPendingSourceMoments.v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∂nuE :=
        ReferenceFirstLiveEmptyPendingSourceMoments.source_secondMoment_cell_integral rate rewards C_star C_h q t s hs control0 Aset hAset j
      _ = ∫ z in {z : Ze | xofE z ∈ Aset},
            secondCoefficient rate rewards C_star C_h q t s hs control0 j z ∂muE :=
        (secondCoefficient_cell_integral rate rewards C_star C_h q t s hs control0
          Aset hAset j).symm
      _ = ∫ z in S, secondCoefficient rate rewards C_star C_h q t s hs control0 j z ∂muE := by
        rw [hSA]).symm
  · exact (measurable_secondCoefficient
      rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable

/-- The literal accepted projection is ambient Borel measurable. -/
theorem measurable_acceptedA (j : Fin p.K) :
    Measurable (fun z : Ze => acceptedA rate rewards C_star C_h q t s hs control0 j z) := by
  rw [funext (acceptedA_eq_indicator_a rate rewards C_star C_h q t s hs control0 j)]
  exact (ReferenceFirstLiveEmptyPendingSourceMoments.measurable_a
    rate rewards C_star C_h q t s hs control0 j).indicator
      (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)

theorem acceptedA_sq_eq_indicator_a_sq (j : Fin p.K) (z : Ze) :
    (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2 =
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z => (ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2) z := by
  rw [acceptedA_eq_indicator_a]
  by_cases hz : z ∈ G rate rewards C_star C_h q t s hs control0 <;>
    simp [Set.indicator, hz]

/-- The accepted square is measurable in the original field. -/
theorem measurable_acceptedA_sq (j : Fin p.K) :
    Measurable (fun z : Ze =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) := by
  rw [funext (acceptedA_sq_eq_indicator_a_sq rate rewards C_star C_h q t s hs control0 j)]
  exact (ReferenceFirstLiveEmptyPendingSourceMoments.measurable_a_sq
    rate rewards C_star C_h q t s hs control0 j).indicator
      (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)

/-- Integrability of the literal accepted projection on the original finite
measure. -/
theorem integrable_acceptedA (j : Fin p.K) :
    Integrable (fun z : Ze => acceptedA rate rewards C_star C_h q t s hs control0 j z) muE := by
  rw [funext (acceptedA_eq_indicator_a rate rewards C_star C_h q t s hs control0 j)]
  exact (ReferenceFirstLiveEmptyPendingSourceMoments.integrable_a rate rewards C_star C_h q t s hs control0 j).indicator
    (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)

/-- Integrability of the square of the literal accepted projection. -/
theorem integrable_acceptedA_sq (j : Fin p.K) :
    Integrable (fun z : Ze => (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) muE := by
  rw [funext (acceptedA_sq_eq_indicator_a_sq rate rewards C_star C_h q t s hs control0 j)]
  exact (ReferenceFirstLiveEmptyPendingSourceMoments.integrable_a_sq rate rewards C_star C_h q t s hs control0 j).indicator
    (measurableSet_G_ambient rate rewards C_star C_h q t s hs control0)

/-- The actual accepted value is nonnegative and at most `1 / beta`, including
the enabled current update which first overflows. -/
theorem acceptedA_pointwise_bounds (j : Fin p.K) (z : Ze) :
    0 ≤ acceptedA rate rewards C_star C_h q t s hs control0 j z ∧
      acceptedA rate rewards C_star C_h q t s hs control0 j z ≤ 1 / beta := by
  rw [acceptedA_eq_indicator_a]
  by_cases hz : z ∈ G rate rewards C_star C_h q t s hs control0
  · simpa [Set.indicator_of_mem hz] using
      ReferenceFirstLiveEmptyPendingSourceMoments.a_bounds rate rewards C_star C_h q t s hs control0 z j
  · simp only [Set.indicator_of_notMem hz]
    exact ⟨le_rfl,
      div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le⟩

/-- Conditional first moment of the actual chronological accepted record. -/
theorem acceptedA_condExp_firstMoment (j : Fin p.K) :
    muE[(fun z : Ze => acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fempty] =ᵐ[muE]
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => firstCoefficient rate rewards C_star C_h q t s hs control0 j z) := by
  rw [funext (acceptedA_eq_indicator_a rate rewards C_star C_h q t s hs control0 j)]
  have hmask := MeasureTheory.condExp_indicator
    (ReferenceFirstLiveEmptyPendingSourceMoments.integrable_a rate rewards C_star C_h q t s hs control0 j)
    (measurableSet_G rate rewards C_star C_h q t s hs control0)
  have hbase := a_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j
  filter_upwards [hmask, hbase] with z hzMask hzBase
  rw [hzMask]
  by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
  · simpa [hkeep] using hzBase
  · simp [hkeep]

/-- Conditional square moment of the accepted record. The coefficient is
`xi * v^2`, rather than the square of the first coefficient. -/
theorem acceptedA_condExp_secondMoment (j : Fin p.K) :
    muE[(fun z : Ze => (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fempty] =ᵐ[muE]
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => secondCoefficient rate rewards C_star C_h q t s hs control0 j z) := by
  have hpoint : (fun z : Ze =>
      (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) =
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => (ReferenceFirstLiveEmptyPendingSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2) := by
    funext z
    exact acceptedA_sq_eq_indicator_a_sq rate rewards C_star C_h q t s hs control0 j z
  rw [hpoint]
  have hmask := MeasureTheory.condExp_indicator
    (ReferenceFirstLiveEmptyPendingSourceMoments.integrable_a_sq rate rewards C_star C_h q t s hs control0 j)
    (measurableSet_G rate rewards C_star C_h q t s hs control0)
  have hbase := a_condExp_secondMoment rate rewards C_star C_h q t s hs control0 j
  filter_upwards [hmask, hbase] with z hzMask hzBase
  rw [hzMask]
  by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
  · simpa [hkeep] using hzBase
  · simp [hkeep]

/-- The conditional first moment is nonnegative almost everywhere. -/
theorem acceptedA_condExp_first_nonneg (j : Fin p.K) :
    0 ≤ᵐ[muE]
      muE[(fun z : Ze => acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fempty] := by
  have hce := acceptedA_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j
  filter_upwards [hce] with z hz
  rw [hz]
  by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
  · simpa [hkeep] using
      (firstCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.1
  · simp [hkeep]

/-- The conditional first moment has the rounded reward lower bound and
upper bound on the strict-past event. -/
theorem acceptedA_condExp_first_bounds (j : Fin p.K) :
    (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j -
          xiE (xofE z) j / scale) ≤ᵐ[muE]
      muE[(fun z : Ze => acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fempty] ∧
    muE[(fun z : Ze => acceptedA rate rewards C_star C_h q t s hs control0 j z) | Fempty] ≤ᵐ[muE]
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun _ : Ze => ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j) := by
  have hce := acceptedA_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j
  refine ⟨?_, ?_⟩
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
    · simpa [hkeep] using
        (firstCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).1
    · simp [hkeep]
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
    · simpa [hkeep] using
        (firstCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.2.1
    · simp [hkeep]

/-- The square conditional moment is bounded by the masked `rho^2 / xi`
coefficient and then by the masked `1 / xi` envelope. -/
theorem acceptedA_condExp_second_bounds (j : Fin p.K) :
    0 ≤ᵐ[muE]
      muE[(fun z : Ze => (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fempty] ∧
    muE[(fun z : Ze => (acceptedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fempty] ≤ᵐ[muE]
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => (ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j) ^ 2 /
          xiE (xofE z) j) ∧
    (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => (ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j) ^ 2 /
          xiE (xofE z) j) ≤ᵐ[muE]
      (G rate rewards C_star C_h q t s hs control0).indicator
        (fun z : Ze => 1 / xiE (xofE z) j) := by
  have hce := acceptedA_condExp_secondMoment rate rewards C_star C_h q t s hs control0 j
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
    · simpa [hkeep] using
        (secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).1
    · simp [hkeep]
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
    · simpa [hkeep] using
        (secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ G rate rewards C_star C_h q t s hs control0
    · simpa [hkeep] using
        (secondCoefficient_bounds rate rewards C_star C_h q t s hs control0 j z).2.2.1
    · simp [hkeep]

end Bandits.Support.ReferenceFirstLiveEmptyPendingAcceptedMoments

end
