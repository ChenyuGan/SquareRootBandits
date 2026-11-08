/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceCellReadout

/-!
# Original-source all-arm first-live numerical arrival moments

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-168,256-264`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-408`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The current numerical cell is integrated over the original continuing
first-live source using its inherited unnormalized source and remainder
measures. Each arm uses the actual original marker and the whole current
control law. No follower subtype is selected, no law is normalized, and no
conditional history or post-update claim is made.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceFirstLiveAllArmSourceMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "Xplus" => ReferenceFirstLiveRecordingReadoutMeasurability.XPlus
  rate rewards C_star C_h q t s hs control0
local notation "μPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "νPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
  rate rewards C_star C_h q t s hs control0
local notation "ctrlLaw" => ContinuousLearningRows.timeControlLaw p


/-- The literal current original-source remainder coordinate of the existing
branch product split. -/
@[expose] def xof (z : Zplus) : Xplus :=
  (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0 z).1

/-- The existing canonical marker rate for arm `j` at the actual selected
baseline payload on the continuing remainder. -/
@[expose] def xi (x : Xplus) (j : Fin p.K) : ℝ :=
  ReferenceFirstLiveRecordingSourceCylinder.markerRate rate rewards C_star C_h q t s hs control0 x j

/-- The whole-table reward at the fixed source time, scaled by the source
grid denominator. -/
@[expose] def rho {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (j : Fin p.K) : ℝ :=
  ((rewards t j).val : ℝ) / (D p : ℝ)

/-- The literal natural-floor numerical arrival for arm `j`, with the source
integer `rate.n` and the actual varying marker rate. -/
@[expose] def v (x : Xplus) (j : Fin p.K) : ℝ :=
  (Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
    xi rate rewards C_star C_h q t s hs control0 x j) : ℝ) /
    (rate.eta.val * (D p : ℝ))

/-- The actual first-live numerical cell arrival at the same original source
point, normalized by the same source denominator. -/
@[expose] def a (z : Zplus) (j : Fin p.K) : ℝ :=
  (RecordedQueueRun.quantizedArrival
    (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (ReferenceFirstLiveSourceCellReadout.cell rate rewards C_star C_h q t s hs control0 z).input j : ℝ) /
    (rate.eta.val * (D p : ℝ))

theorem xof_measurable : Measurable (xof rate rewards C_star C_h q t s hs control0) :=
  measurable_fst.comp
    (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0)

/-- Projection of the actual branch product split recovers exactly the
inherited unnormalized remainder measure. The second factor is the whole
`timeControlLaw`, including its original private coordinates. -/
theorem branchSourceMeasure_map_xof :
    (μPlus).map (xof rate rewards C_star C_h q t s hs control0) = νPlus := by
  change (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0).map
        (Prod.fst ∘ ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0) = _
  rw [← Measure.map_map measurable_fst
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0),
    ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product rate rewards C_star C_h q t s hs control0,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- Every actual canonical current marker rate is positive and dominates the
source threshold `beta`. -/
theorem xi_bounds (x : Xplus) (j : Fin p.K) :
    0 < xi rate rewards C_star C_h q t s hs control0 x j ∧
      CanonicalRecordingRates.beta p rate.eta.val ≤
        xi rate rewards C_star C_h q t s hs control0 x j := by
  change 0 < CanonicalRecordingRates.xi p rate.eta.val
        (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload x).anchor j ∧
      CanonicalRecordingRates.beta p rate.eta.val ≤
        CanonicalRecordingRates.xi p rate.eta.val
          (ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload x).anchor j
  exact ⟨CanonicalRecordingRates.xi_pos p rate.eta.property _ _,
    CanonicalRecordingRates.beta_le_xi p rate.eta.property _ _⟩

/-- The source grid range gives the actual scalar reward interval. -/
theorem rho_bounds (j : Fin p.K) :
    0 ≤ rho rate rewards C_star C_h q t s hs control0 j ∧
      rho rate rewards C_star C_h q t s hs control0 j ≤ 1 := by
  have hD : 0 < (D p : ℝ) := Nat.cast_pos.mpr (D_pos p)
  have hreward0 : 0 ≤ ((rewards t j).val : ℝ) := Nat.cast_nonneg _
  have hrewardD : ((rewards t j).val : ℝ) ≤ (D p : ℝ) := by
    have hval := (rewards t j).isLt
    exact_mod_cast Nat.le_of_lt_succ hval
  constructor
  · exact div_nonneg hreward0 hD.le
  · unfold rho
    exact (div_le_one hD).2 hrewardD

private theorem v_eq_quantizedValue (x : Xplus) (j : Fin p.K) :
    v rate rewards C_star C_h q t s hs control0 x j =
      QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (xi rate rewards C_star C_h q t s hs control0 x j)
        (rho rate rewards C_star C_h q t s hs control0 j) := by
  have harg : (rate.n : ℝ) *
      rho rate rewards C_star C_h q t s hs control0 j /
        xi rate rewards C_star C_h q t s hs control0 x j =
      ((D p : ℝ) * rate.eta.val *
        rho rate rewards C_star C_h q t s hs control0 j) /
        xi rate rewards C_star C_h q t s hs control0 x j := by
    rw [rate.n_scale]
    ring
  unfold v QuantizedRecordingMoments.quantizedValue
    QuantizedRecordingMoments.quantizedIndex
  rw [harg]

/-- Floor quantization is nonnegative and bounded by the actual canonical
lower recording rate. -/
theorem v_bounds (x : Xplus) (j : Fin p.K) :
    0 ≤ v rate rewards C_star C_h q t s hs control0 x j ∧
      v rate rewards C_star C_h q t s hs control0 x j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hxi := xi_bounds rate rewards C_star C_h q t s hs control0 x j
  have hrho := rho_bounds rate rewards C_star C_h q t s hs control0 j
  have hq0 := QuantizedRecordingMoments.quantizedValue_nonneg
    (D p) rate.eta.val (xi rate rewards C_star C_h q t s hs control0 x j)
    (rho rate rewards C_star C_h q t s hs control0 j) rate.eta.property
  have hqle := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (D p) rate.eta.val (xi rate rewards C_star C_h q t s hs control0 x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (CanonicalRecordingRates.beta p rate.eta.val) (D_pos p) rate.eta.property
    hxi.1 ⟨hrho.1, hrho.2⟩
    (CanonicalRecordingRates.beta_pos p rate.eta.property) hxi.2
  rw [v_eq_quantizedValue rate rewards C_star C_h q t s hs control0 x j]
  exact ⟨hq0, hqle⟩

/-- Exact first-moment floor bounds for the same numerical value used by the
actual cell. -/
theorem xi_mul_v_bounds (x : Xplus) (j : Fin p.K) :
    rho rate rewards C_star C_h q t s hs control0 j -
        xi rate rewards C_star C_h q t s hs control0 x j /
          (rate.eta.val * (D p : ℝ)) ≤
      xi rate rewards C_star C_h q t s hs control0 x j *
        v rate rewards C_star C_h q t s hs control0 x j ∧
    xi rate rewards C_star C_h q t s hs control0 x j *
        v rate rewards C_star C_h q t s hs control0 x j ≤
      rho rate rewards C_star C_h q t s hs control0 j ∧
    rho rate rewards C_star C_h q t s hs control0 j ≤ 1 := by
  have hxi := xi_bounds rate rewards C_star C_h q t s hs control0 x j
  have hrho := rho_bounds rate rewards C_star C_h q t s hs control0 j
  have hlow := QuantizedRecordingMoments.quantizedValue_roundingError
    (D p) rate.eta.val (xi rate rewards C_star C_h q t s hs control0 x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
  have hup := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (D p) rate.eta.val (xi rate rewards C_star C_h q t s hs control0 x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
  have hlow' := hlow
  have hup' := hup
  rw [← v_eq_quantizedValue rate rewards C_star C_h q t s hs control0 x j] at hlow' hup'
  exact ⟨hlow', hup', hrho.2⟩

/-- Exact second-moment floor bound and its canonical-rate envelope. -/
theorem xi_mul_v_sq_bounds (x : Xplus) (j : Fin p.K) :
    0 ≤ xi rate rewards C_star C_h q t s hs control0 x j *
        (v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∧
      xi rate rewards C_star C_h q t s hs control0 x j *
          (v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ≤
        (rho rate rewards C_star C_h q t s hs control0 j) ^ 2 /
          xi rate rewards C_star C_h q t s hs control0 x j ∧
      (rho rate rewards C_star C_h q t s hs control0 j) ^ 2 /
          xi rate rewards C_star C_h q t s hs control0 x j ≤
        1 / xi rate rewards C_star C_h q t s hs control0 x j ∧
      1 / xi rate rewards C_star C_h q t s hs control0 x j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hxi := xi_bounds rate rewards C_star C_h q t s hs control0 x j
  have hrho := rho_bounds rate rewards C_star C_h q t s hs control0 j
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (xi rate rewards C_star C_h q t s hs control0 x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
  have hrhoSq : (rho rate rewards C_star C_h q t s hs control0 j) ^ 2 ≤ 1 := by
    nlinarith [hrho.1, hrho.2]
  have hratio := div_le_div_of_nonneg_right hrhoSq hxi.1.le
  have hbeta := one_div_le_one_div_of_le
    (CanonicalRecordingRates.beta_pos p rate.eta.property) hxi.2
  rw [← v_eq_quantizedValue rate rewards C_star C_h q t s hs control0 x j] at hsecond
  exact ⟨mul_nonneg hxi.1.le (sq_nonneg _), hsecond, hratio, hbeta⟩

/-- The computed numerical cell's queue arrival is exactly the source marker
gate applied to the same-arm natural floor value. -/
theorem a_eq_source_marker (z : Zplus) (j : Fin p.K) :
    a rate rewards C_star C_h q t s hs control0 z j =
      if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j then
        v rate rewards C_star C_h q t s hs control0
          (xof rate rewards C_star C_h q t s hs control0 z) j
      else 0 := by
  classical
  have hfields := ReferenceFirstLiveSourceCellReadout.source_current_cell_fields
    rate rewards C_star C_h q t s hs control0 z
  dsimp only at hfields
  rcases hfields with ⟨_, _, _, _, harr⟩
  change (RecordedQueueRun.quantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (ReferenceFirstLiveSourceCellReadout.cell rate rewards C_star C_h q t s hs control0 z).input j : ℝ) /
      (rate.eta.val * (D p : ℝ)) = _
  rw [harr j]
  by_cases hm : ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j
  · simp [hm, v, rho, xi, xof, ReferenceFirstLiveRecordingSourceCylinder.markerRate]
  · simp [hm]

/-- The actual normalized all-arm arrival inherits the source's uniform
nonnegative and inverse-beta envelope. -/
theorem a_bounds (z : Zplus) (j : Fin p.K) :
    0 ≤ a rate rewards C_star C_h q t s hs control0 z j ∧
      a rate rewards C_star C_h q t s hs control0 z j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  rw [a_eq_source_marker rate rewards C_star C_h q t s hs control0 z j]
  by_cases hm : ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j
  · simp only [hm, if_pos]
    exact v_bounds rate rewards C_star C_h q t s hs control0
      (xof rate rewards C_star C_h q t s hs control0 z) j
  · constructor
    · simp [hm]
    · simpa [hm] using div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le

/-- The literal all-arm floor readout is Borel on the existing remainder
subtype. -/
theorem measurable_v (j : Fin p.K) :
    Measurable (fun x : Xplus => v rate rewards C_star C_h q t s hs control0 x j) := by
  have hxi := ReferenceFirstLiveRecordingSourceCylinder.measurable_markerRate rate rewards C_star C_h q t s hs control0 j
  have harg : Measurable (fun x : Xplus =>
      (rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
        xi rate rewards C_star C_h q t s hs control0 x j) := by
    exact (measurable_const.mul measurable_const).div hxi
  have hfloor : Measurable (fun x : Xplus => Nat.floor
      ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
        xi rate rewards C_star C_h q t s hs control0 x j)) :=
    Nat.measurable_floor.comp harg
  have hcast : Measurable (fun x : Xplus =>
      (Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
        xi rate rewards C_star C_h q t s hs control0 x j) : ℝ)) :=
    (measurable_of_countable _).comp hfloor
  change Measurable (fun x : Xplus =>
    (Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
      xi rate rewards C_star C_h q t s hs control0 x j) : ℝ) /
      (rate.eta.val * (D p : ℝ)))
  exact hcast.div_const _

/-- The same coefficient rate and quantized value used by the source marker
law are Borel on the current remainder carrier. -/
theorem measurable_xi_mul_v (j : Fin p.K) :
    Measurable (fun x : Xplus => xi rate rewards C_star C_h q t s hs control0 x j *
      v rate rewards C_star C_h q t s hs control0 x j) :=
  (ReferenceFirstLiveRecordingSourceCylinder.measurable_markerRate rate rewards C_star C_h q t s hs control0 j).mul
    (measurable_v rate rewards C_star C_h q t s hs control0 j)

/-- The square-moment coefficient is Borel on the same remainder carrier. -/
theorem measurable_xi_mul_v_sq (j : Fin p.K) :
    Measurable (fun x : Xplus => xi rate rewards C_star C_h q t s hs control0 x j *
      (v rate rewards C_star C_h q t s hs control0 x j) ^ 2) :=
  (ReferenceFirstLiveRecordingSourceCylinder.measurable_markerRate rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_v rate rewards C_star C_h q t s hs control0 j).pow_const 2)

/-- The actual recorded-cell arrival is Borel without requiring measurability
of an arbitrary full cell state. -/
theorem measurable_a (j : Fin p.K) :
    Measurable (fun z : Zplus => a rate rewards C_star C_h q t s hs control0 z j) := by
  have hmarker : MeasurableSet {z : Zplus |
      ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j} :=
    measurableSet_eq_fun
      (ReferenceFirstLiveRecordingSourceCylinder.measurable_sourceMarker rate rewards C_star C_h q t s hs control0)
      measurable_const
  have hvalue : Measurable (fun z : Zplus =>
      v rate rewards C_star C_h q t s hs control0
        (xof rate rewards C_star C_h q t s hs control0 z) j) :=
    (measurable_v rate rewards C_star C_h q t s hs control0 j).comp
      (xof_measurable rate rewards C_star C_h q t s hs control0)
  have hformula : Measurable (fun z : Zplus =>
      if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j then
        v rate rewards C_star C_h q t s hs control0
          (xof rate rewards C_star C_h q t s hs control0 z) j else 0) :=
    Measurable.ite hmarker hvalue measurable_const
  have heq : (fun z : Zplus => a rate rewards C_star C_h q t s hs control0 z j) =
      (fun z : Zplus =>
        if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j then
          v rate rewards C_star C_h q t s hs control0
            (xof rate rewards C_star C_h q t s hs control0 z) j else 0) := by
    funext z
    exact a_eq_source_marker rate rewards C_star C_h q t s hs control0 z j
  rw [heq]
  exact hformula

/-- The square of the actual arrival is Borel on the original source
subtype. -/
theorem measurable_a_sq (j : Fin p.K) :
    Measurable (fun z : Zplus =>
      (a rate rewards C_star C_h q t s hs control0 z j) ^ 2) :=
  (measurable_a rate rewards C_star C_h q t s hs control0 j).pow_const 2

private theorem beta_pos : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
  CanonicalRecordingRates.beta_pos p rate.eta.property

private theorem a_norm_bound (j : Fin p.K) (z : Zplus) :
    ‖a rate rewards C_star C_h q t s hs control0 z j‖ ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (a_bounds rate rewards C_star C_h q t s hs control0 z j).1]
  exact (a_bounds rate rewards C_star C_h q t s hs control0 z j).2

/-- The arrival and its square are integrable under the inherited source
measure, including when the continuing branch has zero mass. -/
theorem integrable_a (j : Fin p.K) :
    Integrable (fun z : Zplus => a rate rewards C_star C_h q t s hs control0 z j) μPlus := by
  exact Integrable.of_bound
    (measurable_a rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
    (Filter.Eventually.of_forall (a_norm_bound rate rewards C_star C_h q t s hs control0 j))

theorem integrable_a_sq (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      (a rate rewards C_star C_h q t s hs control0 z j) ^ 2) μPlus := by
  have hbound : ∀ z : Zplus,
      ‖(a rate rewards C_star C_h q t s hs control0 z j) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha := a_bounds rate rewards C_star C_h q t s hs control0 z j
    have hB : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
      (div_pos (by norm_num) (beta_pos rate)).le
    nlinarith
  exact Integrable.of_bound
    (measurable_a_sq rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    (Filter.Eventually.of_forall hbound)

private theorem xi_mul_v_norm_bound (j : Fin p.K) (x : Xplus) :
    ‖xi rate rewards C_star C_h q t s hs control0 x j *
      v rate rewards C_star C_h q t s hs control0 x j‖ ≤ 1 := by
  have hnonneg : 0 ≤ xi rate rewards C_star C_h q t s hs control0 x j *
      v rate rewards C_star C_h q t s hs control0 x j :=
    mul_nonneg (xi_bounds rate rewards C_star C_h q t s hs control0 x j).1.le
      (v_bounds rate rewards C_star C_h q t s hs control0 x j).1
  have hcoef := xi_mul_v_bounds rate rewards C_star C_h q t s hs control0 x j
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hcoef.2.1.trans hcoef.2.2

private theorem xi_mul_v_sq_norm_bound (j : Fin p.K) (x : Xplus) :
    ‖xi rate rewards C_star C_h q t s hs control0 x j *
      (v rate rewards C_star C_h q t s hs control0 x j) ^ 2‖ ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hcoef := xi_mul_v_sq_bounds rate rewards C_star C_h q t s hs control0 x j
  rw [Real.norm_eq_abs, abs_of_nonneg hcoef.1]
  exact hcoef.2.1.trans (hcoef.2.2.1.trans hcoef.2.2.2)

/-- The first-moment coefficient and the second-moment coefficient are
integrable on the inherited continuing remainder measure. -/
theorem integrable_xi_mul_v (j : Fin p.K) :
    Integrable (fun x : Xplus => xi rate rewards C_star C_h q t s hs control0 x j *
      v rate rewards C_star C_h q t s hs control0 x j) νPlus := by
  exact Integrable.of_bound
    (measurable_xi_mul_v rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    1 (Filter.Eventually.of_forall
      (xi_mul_v_norm_bound rate rewards C_star C_h q t s hs control0 j))

theorem integrable_xi_mul_v_sq (j : Fin p.K) :
    Integrable (fun x : Xplus => xi rate rewards C_star C_h q t s hs control0 x j *
      (v rate rewards C_star C_h q t s hs control0 x j) ^ 2) νPlus := by
  exact Integrable.of_bound
    (measurable_xi_mul_v_sq rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
    (Filter.Eventually.of_forall
      (xi_mul_v_sq_norm_bound rate rewards C_star C_h q t s hs control0 j))

private theorem source_marker_weight_cell_integral
    (Aset : Set Xplus) (hAset : MeasurableSet Aset) (j : Fin p.K)
    (w : Xplus → ℝ) (hw : Measurable w) (B : ℝ) (hB : 0 ≤ B)
    (hw_bound : ∀ x, ‖w x‖ ≤ B) :
    (∫ z in {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset},
      (if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j then
        w (xof rate rewards C_star C_h q t s hs control0 z) else 0) ∂μPlus) =
      ∫ x in Aset,
        xi rate rewards C_star C_h q t s hs control0 x j * w x ∂νPlus := by
  classical
  let split := ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit rate rewards C_star C_h q t s hs control0
  let sourceSet : Set Zplus :=
    {z | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset}
  let cellControl : Set (Xplus × TimeControl p) := Aset ×ˢ Set.univ
  let H : Xplus × TimeControl p → ℝ := cellControl.indicator
    (fun y =>
      if ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker y = some j
      then w y.1 else 0)
  have hsourceSet : MeasurableSet sourceSet := by
    exact hAset.preimage (xof_measurable rate rewards C_star C_h q t s hs control0)
  have hmarkerEvent : MeasurableSet {y : Xplus × TimeControl p |
      ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker y = some j} :=
    measurableSet_eq_fun
      ReferenceFirstLiveRecordingReadoutMeasurability.measurable_currentPhysicalMarker
      measurable_const
  have hconditional : Measurable (fun y : Xplus × TimeControl p =>
      if ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker y = some j
      then w y.1 else 0) :=
    Measurable.ite hmarkerEvent (hw.comp measurable_fst) measurable_const
  have hcellControl : MeasurableSet cellControl := hAset.prod MeasurableSet.univ
  have hH : Measurable H := hconditional.indicator hcellControl
  have hHbound : ∀ y, ‖H y‖ ≤ B := by
    intro y
    by_cases hy : y ∈ cellControl
    · by_cases hm : ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker y = some j
      · simpa [H, hy, hm] using hw_bound y.1
      · simp [H, hy, hm, hB]
    · simp [H, hy, hB]
  have hHint : Integrable H
      ((ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
        rate rewards C_star C_h q t s hs control0).prod ctrlLaw) :=
    Integrable.of_bound hH.aestronglyMeasurable B
      (Filter.Eventually.of_forall hHbound)
  have hsplit : Measurable split :=
    ReferenceFirstLiveRecordingSourceCylinder.measurable_branchSourceSplit rate rewards C_star C_h q t s hs control0
  have hcellPreimage (z : Zplus) : split z ∈ cellControl ↔ z ∈ sourceSet := by
    simp [cellControl, sourceSet, split, xof]
  have hsourceIndicator :
      sourceSet.indicator
        (fun z => if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j
          then w (xof rate rewards C_star C_h q t s hs control0 z) else 0) = H ∘ split := by
    funext z
    by_cases hz : z ∈ sourceSet
    · have hsplitCell : split z ∈ cellControl := (hcellPreimage z).2 hz
      change sourceSet.indicator
          (fun z => if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
            rate rewards C_star C_h q t s hs control0 z = some j
              then w (xof rate rewards C_star C_h q t s hs control0 z) else 0) z =
        cellControl.indicator
          (fun y => if ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker y = some j
            then w y.1 else 0) (split z)
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hsplitCell]
      rfl
    · have hsplitCell : split z ∉ cellControl := fun h => hz ((hcellPreimage z).1 h)
      change sourceSet.indicator
          (fun z => if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
            rate rewards C_star C_h q t s hs control0 z = some j
              then w (xof rate rewards C_star C_h q t s hs control0 z) else 0) z =
        cellControl.indicator
          (fun y => if ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker y = some j
            then w y.1 else 0) (split z)
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hsplitCell]
  have hfiber : ∀ x : Xplus,
      (∫ u, H (x, u) ∂ctrlLaw) =
        Aset.indicator (fun x =>
          xi rate rewards C_star C_h q t s hs control0 x j * w x) x := by
    intro x
    by_cases hx : x ∈ Aset
    · let E : Set (TimeControl p) :=
        {u | ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = some j}
      have hE : MeasurableSet E := by
        exact measurableSet_eq_fun
          (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_currentPhysicalMarker.comp
            (measurable_const.prodMk measurable_id)) measurable_const
      have hfun : (fun u => H (x, u)) = E.indicator (fun _ => w x) := by
        funext u
        by_cases hu : ReferenceFirstLiveRecordingReadoutMeasurability.currentPhysicalMarker (x, u) = some j
        · simp [H, cellControl, hx, E, hu]
        · simp [H, cellControl, hx, E, hu]
      rw [hfun, integral_indicator_const, smul_eq_mul]
      · have hmass := (ReferenceFirstLiveRecordingSourceCylinder.currentPhysicalMarker_masses
          rate rewards C_star C_h q t s hs control0 x).1 j
        change ctrlLaw E = ENNReal.ofReal
          (xi rate rewards C_star C_h q t s hs control0 x j) at hmass
        rw [measureReal_def, hmass,
          ENNReal.toReal_ofReal (xi_bounds rate rewards C_star C_h q t s hs control0 x j).1.le]
        simp [Set.indicator_of_mem hx]
      · exact hE
    · have hfun : (fun u => H (x, u)) = fun _ => (0 : ℝ) := by
        funext u
        simp [H, cellControl, hx]
      rw [hfun]
      simp [Set.indicator_of_notMem hx]
  calc
    _ = ∫ z, sourceSet.indicator
        (fun z => if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j
          then w (xof rate rewards C_star C_h q t s hs control0 z) else 0) z ∂μPlus := by
      rw [← integral_indicator hsourceSet]
    _ = ∫ z, H (split z) ∂μPlus := by
      rw [hsourceIndicator]
      simp only [Function.comp_apply]
    _ = ∫ y, H y ∂((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0).map split) :=
      (MeasureTheory.integral_map hsplit.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ y, H y ∂((ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure
        rate rewards C_star C_h q t s hs control0).prod ctrlLaw) := by
      rw [ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit_product rate rewards C_star C_h q t s hs control0]
    _ = ∫ x, ∫ u, H (x, u) ∂ctrlLaw ∂νPlus := integral_prod H hHint
    _ = ∫ x, Aset.indicator (fun x =>
        xi rate rewards C_star C_h q t s hs control0 x j * w x) x ∂νPlus := by
      congr 1
      funext x
      exact hfiber x
    _ = ∫ x in Aset,
        xi rate rewards C_star C_h q t s hs control0 x j * w x ∂νPlus := by
      rw [integral_indicator hAset]

/-- Exact first numerical-arrival cell identity for every Borel subset of the
same continuing remainder subtype. -/
theorem source_firstMoment_cell_integral
    (Aset : Set Xplus) (hAset : MeasurableSet Aset) (j : Fin p.K) :
    (∫ z in {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset},
      a rate rewards C_star C_h q t s hs control0 z j ∂μPlus) =
      ∫ x in Aset,
        xi rate rewards C_star C_h q t s hs control0 x j *
          v rate rewards C_star C_h q t s hs control0 x j ∂νPlus := by
  have hsourceSet : MeasurableSet
      {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset} :=
    hAset.preimage (xof_measurable rate rewards C_star C_h q t s hs control0)
  calc
    _ = ∫ z in {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset},
        (if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j then
          v rate rewards C_star C_h q t s hs control0
            (xof rate rewards C_star C_h q t s hs control0 z) j else 0) ∂μPlus := by
      apply setIntegral_congr_fun hsourceSet
      intro z _
      exact a_eq_source_marker rate rewards C_star C_h q t s hs control0 z j
    _ = _ := source_marker_weight_cell_integral rate rewards C_star C_h q t s hs control0
      Aset hAset j (v rate rewards C_star C_h q t s hs control0 · j)
      (measurable_v rate rewards C_star C_h q t s hs control0 j)
      (1 / CanonicalRecordingRates.beta p rate.eta.val)
      (div_nonneg (by norm_num) (beta_pos rate).le)
      (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg
          (v_bounds rate rewards C_star C_h q t s hs control0 x j).1]
        exact (v_bounds rate rewards C_star C_h q t s hs control0 x j).2)

/-- Exact square numerical-arrival cell identity, on the same arbitrary
Borel subset and with the same original-source marker kernel. -/
theorem source_secondMoment_cell_integral
    (Aset : Set Xplus) (hAset : MeasurableSet Aset) (j : Fin p.K) :
    (∫ z in {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset},
      (a rate rewards C_star C_h q t s hs control0 z j) ^ 2 ∂μPlus) =
      ∫ x in Aset,
        xi rate rewards C_star C_h q t s hs control0 x j *
          (v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∂νPlus := by
  have hsourceSet : MeasurableSet
      {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset} :=
    hAset.preimage (xof_measurable rate rewards C_star C_h q t s hs control0)
  calc
    _ = ∫ z in {z : Zplus | xof rate rewards C_star C_h q t s hs control0 z ∈ Aset},
        (if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j then
          (v rate rewards C_star C_h q t s hs control0
            (xof rate rewards C_star C_h q t s hs control0 z) j) ^ 2 else 0) ∂μPlus := by
      apply setIntegral_congr_fun hsourceSet
      intro z _
      change (a rate rewards C_star C_h q t s hs control0 z j) ^ 2 = _
      rw [a_eq_source_marker rate rewards C_star C_h q t s hs control0 z j]
      by_cases hm : ReferenceFirstLiveRecordingSourceCylinder.sourceMarker rate rewards C_star C_h q t s hs control0 z = some j <;>
        simp [hm]
    _ = _ := source_marker_weight_cell_integral rate rewards C_star C_h q t s hs control0
      Aset hAset j
      (fun x => (v rate rewards C_star C_h q t s hs control0 x j) ^ 2)
      ((measurable_v rate rewards C_star C_h q t s hs control0 j).pow_const 2)
      ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
      (sq_nonneg _)
      (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hv := v_bounds rate rewards C_star C_h q t s hs control0 x j
        have hB : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
          (div_pos (by norm_num) (beta_pos rate)).le
        nlinarith)

end Bandits.Support.ReferenceFirstLiveAllArmSourceMoments
