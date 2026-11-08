/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentRecordedCell

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Raw first-call recording moments

The scalar is the nominal unserved physical arrival on the actual optional
current cell. The first-cell indicator localizes every probability statement
to the original source law and its exact pre-choice field.

Sources: `04_slow_fast_learner.tex:140-188,245-271`,
`05_binary_transport.tex:352-431`, `06_interruptions.tex:363-426`, and
`appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCurrentRawMoments

open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The nominal physical unserved raw arrival on the existing optional cell. -/
def currentRaw (t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  match ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h t z with
  | none => 0
  | some c => RecordedRoundMoments.normalizedQuantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a

/-- The quantized source reward amplitude at the actual calendar parameter. -/
def currentAmplitude (t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  match calendarParameters rate rewards C_star C_h t z with
  | none => 0
  | some theta =>
      QuantizedRecordingMoments.quantizedValue
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
        (((rewards t a).val : ℝ) / (D p : ℝ))

/-- The literal current-arm test, preserving both optional marker layers. -/
def currentArmTest (t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t z = some (some a) then 1 else 0

/-- First conditional-moment coefficient, localized to the original call. -/
def currentMomentOne (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (firstCell rate rewards C_star C_h u t).indicator (fun z =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some theta =>
        let xi := CanonicalRecordingRates.xi p rate.eta.val theta.2 a
        xi * QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi
          (((rewards t a).val : ℝ) / (D p : ℝ))) z

/-- Square-moment coefficient for the same actual recording arm, localized
to the original call. -/
def currentMomentTwo (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (firstCell rate rewards C_star C_h u t).indicator (fun z =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some theta =>
        let xi := CanonicalRecordingRates.xi p rate.eta.val theta.2 a
        xi * (QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi
          (((rewards t a).val : ℝ) / (D p : ℝ))) ^ 2) z

private theorem measurable_quantizedValue {X : Type*} [MeasurableSpace X]
    (xi reward : X → ℝ) (hxi : Measurable xi) (hreward : Measurable reward)
    (D0 : ℕ) (eta : ℝ) :
    Measurable (fun x => QuantizedRecordingMoments.quantizedValue D0 eta
      (xi x) (reward x)) := by
  have harg : Measurable (fun x =>
      ((D0 : ℝ) * eta * reward x) / xi x) :=
    ((measurable_const.mul measurable_const).mul hreward).div hxi
  have hfloor : Measurable (fun x =>
      (Nat.floor (((D0 : ℝ) * eta * reward x) / xi x) : ℝ)) :=
    (measurable_of_countable _).comp (Nat.measurable_floor.comp harg)
  change Measurable (fun x =>
    (Nat.floor (((D0 : ℝ) * eta * reward x) / xi x) : ℝ) /
      (eta * (D0 : ℝ)))
  exact hfloor.div_const _

private theorem measurable_option_elim {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (default : β) :
    Measurable (fun q : Option α => q.elim default f) := by
  have hsum : Measurable (Sum.elim f (fun _ : PUnit => default)) :=
    hf.sumElim measurable_const
  have heq : (fun q : Option α => q.elim default f) =
      (Sum.elim f (fun _ : PUnit => default)) ∘
        Equiv.optionEquivSumPUnit α := by
    funext q
    cases q <;> rfl
  rw [heq]
  exact hsum.comp (comap_measurable _)

private theorem measurable_calendarXi (control0 : TimeControl p)
    (t : Fin p.T) (a : Fin p.K) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (fun z : SourceInput p =>
      match calendarParameters rate rewards C_star C_h t z with
      | none => 0
      | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
  have hparams : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (calendarParameters rate rewards C_star C_h t) :=
    ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable
      rate rewards C_star C_h control0 t
  have hprod (S : Finset (Fin p.K)) :
      Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun v : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight v)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hprod S)
  have htheta : Measurable (fun v : Fin p.K → ℝ =>
      ProductSetLaw.theta p.m v a) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    unfold FiniteNormalization.normalizedWeight
    exact (hprod S).div htotal
  have hf : Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.f p v a) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  have hxi : Measurable (fun v : Fin p.K → ℝ =>
      CanonicalRecordingRates.xi p rate.eta.val v a) :=
    AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
      ((measurable_const.max hf))
  let xiTheta := fun theta : AssignmentParameterFibreKernel.Theta p =>
    CanonicalRecordingRates.xi p rate.eta.val theta.2 a
  have hxiTheta : Measurable xiTheta :=
    hxi.comp measurable_snd
  have hoption : Measurable (fun q : Option (AssignmentParameterFibreKernel.Theta p) =>
      q.elim 0 xiTheta) := measurable_option_elim xiTheta hxiTheta 0
  have hmatch := hoption.comp hparams
  have hmatch' : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (fun z : SourceInput p =>
      (calendarParameters rate rewards C_star C_h t z).elim 0 xiTheta) := by
    simpa only [Function.comp_def] using hmatch
  have heq : (fun z : SourceInput p =>
      match calendarParameters rate rewards C_star C_h t z with
      | none => 0
      | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) =
      fun z => (calendarParameters rate rewards C_star C_h t z).elim 0 xiTheta := by
    funext z
    cases calendarParameters rate rewards C_star C_h t z <;> rfl
  rw [heq]
  exact hmatch'

/-- The actual current amplitude is measurable in the original pre-choice
field. -/
theorem currentAmplitude_measurable (control0 : TimeControl p)
    (_u t : Fin p.T) (a : Fin p.K) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (currentAmplitude rate rewards C_star C_h t a) := by
  have hxi := measurable_calendarXi rate rewards C_star C_h control0 t a
  have hr : Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)] (fun _ : SourceInput p =>
      (((rewards t a).val : ℝ) / (D p : ℝ))) := measurable_const
  have hq := @measurable_quantizedValue (SourceInput p)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1))
    (fun z => match calendarParameters rate rewards C_star C_h t z with
      | none => 0
        | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
    (fun _ => (((rewards t a).val : ℝ) / (D p : ℝ))) hxi hr
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
  have heq : currentAmplitude rate rewards C_star C_h t a =
      fun z => QuantizedRecordingMoments.quantizedValue
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (match calendarParameters rate rewards C_star C_h t z with
        | none => 0
        | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
        (((rewards t a).val : ℝ) / (D p : ℝ)) := by
    funext z
    cases hP : calendarParameters rate rewards C_star C_h t z <;>
      simp [currentAmplitude, hP, QuantizedRecordingMoments.quantizedValue,
        QuantizedRecordingMoments.quantizedIndex]
  rw [heq]
  exact hq

private theorem actualFirstCellData (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (theta : AssignmentParameterFibreKernel.Theta p)
      (selected : ReferenceActivePhysicalStep.Selection r.input)
      (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
      (c : RecordedQueueRun.RoundInput p.K),
      r.input.time = t ∧ r.input.rewards = rewards ∧
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      selected.view.payload.anchor = theta.2 ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      c.reward a = ((rewards t a).val : ℝ) / (D p : ℝ) ∧
      c.rate a = CanonicalRecordingRates.xi p rate.eta.val theta.2 a ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker
        rate rewards C_star C_h t z = some c.recordedArm ∧
      c = cell.input ∧
      (c.recordedArm = some a →
        ∃ owner : Fin p.m,
          SnapshotRecordingKernel.owns p
            (.live
              cell.selected.view.payload.assignment
              (ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot
                cell.selected.view.payload.assignment))
            owner a ∧
          r.output.preparation.arms.actions owner = a ∧
          r.gridFeedback owner = rewards t a ∧
          (r.output.ownEntries owner).2.val.val =
            ((rewards t a).val : ℝ) / (D p : ℝ)) := by
  obtain ⟨_n, r, theta, selected, c, _hn, ht, hr, _hrows, _hj,
    hrewards, htheta, hselected, _hchosen, hcell, hread, hanchor, _hpos⟩ :=
    ReferenceFirstCollectionCurrentRecordedCell.firstCell_selected
      rate rewards C_star C_h u t z hz
  obtain ⟨_np, rp, thetap, _hpref, _htp, hactualp, _hcallp, _hrowsp,
    _hjp, _hrewardsp, _hrealization⟩ :=
    ReferenceFirstCollectionCurrentNumericalCell.firstCell_realization
      rate rewards C_star C_h u t z hz
  have hrp : rp = r := Option.some.inj (hactualp.symm.trans hr)
  subst rp
  have hphysical :=
    ReferenceFirstCollectionCurrentRecordedCell.firstCell_physical
      rate rewards C_star C_h u t z hz
  obtain ⟨_nph, rph, _tph, cell, _hpref, _htph, hactualph,
    _hrowsph, _hjph, _hrewardsph, _hthetaph, _hchosenph, hcellph,
    hmarkerph, hrecordedph, _hanchorph, _hpendingph, _hstatesph,
    hownerph, _hloggingph⟩ := hphysical
  have hrph : rph = r := Option.some.inj (hactualph.symm.trans hr)
  subst rph
  have hcell_eq : c = cell.input := Option.some.inj (hcell.symm.trans hcellph)
  have hnum := ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    r c hread
  obtain ⟨henabled, selected', hselection', hreward, hrate, _harrival⟩ := hnum
  have hselected_eq : selected' = selected := Option.some.inj (hselection'.symm.trans hselected)
  subst selected'
  rw [hrewards, ht] at hreward
  have hrate' : c.rate a = CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
    rw [hrate, selected.view.payload.rate_eq_canonical, ← hanchor]
  refine ⟨r, theta, selected, cell, c, ht, hrewards, htheta, hanchor, hcell, henabled,
    congrFun hreward a, hrate', ?_, hcell_eq, ?_⟩
  · have hmark :
        ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
          r cell.selected.view.payload true = c.recordedArm := by
      calc
        _ = cell.input.recordedArm := hrecordedph.symm
        _ = c.recordedArm :=
          (congrArg RecordedQueueRun.RoundInput.recordedArm hcell_eq).symm
    exact hmarkerph.trans (congrArg some hmark)
  · intro hrecorded
    have hrecordedCell : cell.input.recordedArm = some a := by
      rw [← hcell_eq]
      exact hrecorded
    obtain ⟨owner, howns, _hunique, haction, hfeedback, hentry⟩ :=
      hownerph a hrecordedCell
    exact ⟨owner, howns, haction, hfeedback, hentry⟩

/-- On the original first-cell event, the nominal raw arrival uses the same
physical marker test and the same actual-calendar quantized amplitude. -/
theorem currentRaw_eq_armTest_mul_amplitude (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    currentRaw rate rewards C_star C_h t a z =
      currentArmTest rate rewards C_star C_h t a z *
        currentAmplitude rate rewards C_star C_h t a z := by
  obtain ⟨r, theta, _selected, cell, c, _ht, _hrewards, htheta, _hanchor, hcell,
    _henabled, hreward, hrate, hmarker, hcell_eq, howner⟩ :=
    actualFirstCellData rate rewards C_star C_h u t a z hz
  have hraw : RecordedRoundMoments.normalizedQuantizedArrival
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
      if c.recordedArm = some a then
        QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
          (c.rate a) (c.reward a) else 0 := by
    by_cases hrecorded : c.recordedArm = some a
    · simpa [hrecorded] using
        RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a hrecorded
    · have hzero : RecordedRoundMoments.normalizedQuantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
        unfold RecordedRoundMoments.normalizedQuantizedArrival
        rw [RecordedQueueRun.quantizedArrival_eq_zero
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a hrecorded]
        simp
      simpa [hrecorded] using hzero
  by_cases hrecorded : c.recordedArm = some a
  · obtain ⟨owner, _owns, _action, hfeedback, hentry⟩ := howner hrecorded
    have _physicalFeedback : r.gridFeedback owner = rewards t a := hfeedback
    have _normalizedEntry : (r.output.ownEntries owner).2.val.val = c.reward a :=
      hentry.trans hreward.symm
    simp only [currentRaw, hcell, currentAmplitude, htheta,
      currentArmTest, hmarker]
    rw [hraw]
    simp [hrecorded, hrate, hreward]
  · simp only [currentRaw, hcell, currentAmplitude, htheta,
      currentArmTest, hmarker]
    rw [hraw]
    simp [hrecorded]

/-- The square uses the square of the same literal zero-one arm test. -/
theorem currentRaw_sq_eq_armTest_mul_amplitude_sq (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    (currentRaw rate rewards C_star C_h t a z) ^ 2 =
      currentArmTest rate rewards C_star C_h t a z *
        (currentAmplitude rate rewards C_star C_h t a z) ^ 2 := by
  rw [currentRaw_eq_armTest_mul_amplitude rate rewards C_star C_h u t a z hz]
  by_cases h : ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t z = some (some a)
  · simp [currentArmTest, h]
  · simp [currentArmTest, h]

private theorem currentAmplitude_bounds_on_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    0 ≤ currentAmplitude rate rewards C_star C_h t a z ∧
      currentAmplitude rate rewards C_star C_h t a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  obtain ⟨_r, theta, _selected, _cell, _c, _ht, _hrewards, htheta,
    _hanchor, _hcell, _henabled, _hreward, _hrate, _hmarker, _hcellEq,
    _howner⟩ := actualFirstCellData rate rewards C_star C_h u t a z hz
  let xi := CanonicalRecordingRates.xi p rate.eta.val theta.2 a
  let reward := ((rewards t a).val : ℝ) / (D p : ℝ)
  let q := QuantizedRecordingMoments.quantizedValue
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi reward
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbetaxi : CanonicalRecordingRates.beta p rate.eta.val ≤ xi := by
    dsimp [xi]
    exact CanonicalRecordingRates.beta_le_xi p rate.eta.property theta.2 a
  have hreward : reward ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hvalue : (rewards t a).val ≤ D p :=
        Nat.le_of_lt_succ (rewards t a).isLt
      dsimp [reward]
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast hvalue
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ rate.eta.property
  have hqle : q ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    dsimp [q, xi, reward]
    exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
      (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
      (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
      (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
      (((rewards t a).val : ℝ) / (D p : ℝ))
      (CanonicalRecordingRates.beta p rate.eta.val)
      (ConstructorDimensions.D_pos p) rate.eta.property
      (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a)
      hreward (CanonicalRecordingRates.beta_pos p rate.eta.property) hbetaxi
  have hqle' : q ≤ (CanonicalRecordingRates.beta p rate.eta.val)⁻¹ := by
    simpa [one_div] using hqle
  simpa [one_div, currentAmplitude, htheta, q, xi, reward,
    ReferenceFirstLaunchNumericalCell.queueParameters] using ⟨hq0, hqle'⟩

/-- On the actual first-cell event, the two coefficients are exactly
`ξ * quantizedValue` and `ξ * quantizedValue ^ 2`. -/
theorem currentMoment_coefficients_on_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      currentMomentOne rate rewards C_star C_h u t a z =
        CanonicalRecordingRates.xi p rate.eta.val theta.2 a *
          QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
            (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
            (((rewards t a).val : ℝ) / (D p : ℝ)) ∧
      currentMomentTwo rate rewards C_star C_h u t a z =
        CanonicalRecordingRates.xi p rate.eta.val theta.2 a *
          (QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
            (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
            (((rewards t a).val : ℝ) / (D p : ℝ))) ^ 2 := by
  obtain ⟨_r, theta, _selected, _cell, _c, _ht, _hrewards, htheta,
    _hanchor, _hcell, _henabled, _hreward, _hrate, _hmarker, _hcellEq,
    _howner⟩ := actualFirstCellData rate rewards C_star C_h u t a z hz
  refine ⟨theta, htheta, ?_, ?_⟩
  · simp [currentMomentOne, Set.indicator, hz, htheta]
  · simp [currentMomentTwo, Set.indicator, hz, htheta]

/-- Exact quantized first and second coefficients, with the manuscript's
rounding error and inverse-rate bounds on the actual first-call event. -/
theorem currentMoment_bounds_on_firstCell (u t : Fin p.T)
    (a : Fin p.K) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ theta : AssignmentParameterFibreKernel.Theta p,
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      (((rewards t a).val : ℝ) / (D p : ℝ)) -
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a /
            (rate.eta.val * (D p : ℝ)) ≤
        currentMomentOne rate rewards C_star C_h u t a z ∧
      0 ≤ currentMomentOne rate rewards C_star C_h u t a z ∧
      currentMomentOne rate rewards C_star C_h u t a z ≤
        ((rewards t a).val : ℝ) / (D p : ℝ) ∧
      currentMomentOne rate rewards C_star C_h u t a z ≤ 1 ∧
      0 ≤ currentMomentTwo rate rewards C_star C_h u t a z ∧
      currentMomentTwo rate rewards C_star C_h u t a z ≤
        (((rewards t a).val : ℝ) / (D p : ℝ)) ^ 2 /
          CanonicalRecordingRates.xi p rate.eta.val theta.2 a ∧
      currentMomentTwo rate rewards C_star C_h u t a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  obtain ⟨_r, theta, _selected, _cell, _c, _ht, _hrewards, htheta,
    _hanchor, _hcell, _henabled, _hreward, _hrate, _hmarker, _hcellEq,
    _howner⟩ := actualFirstCellData rate rewards C_star C_h u t a z hz
  let xi := CanonicalRecordingRates.xi p rate.eta.val theta.2 a
  let reward := ((rewards t a).val : ℝ) / (D p : ℝ)
  let q := QuantizedRecordingMoments.quantizedValue
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi reward
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbetaxi : CanonicalRecordingRates.beta p rate.eta.val ≤ xi := by
    dsimp [xi]
    exact CanonicalRecordingRates.beta_le_xi p rate.eta.property theta.2 a
  have hxi : 0 < xi := hbeta.trans_le hbetaxi
  have hreward : reward ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hvalue : (rewards t a).val ≤ D p :=
        Nat.le_of_lt_succ (rewards t a).isLt
      dsimp [reward]
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast hvalue
  have hone : currentMomentOne rate rewards C_star C_h u t a z = xi * q := by
    simp [currentMomentOne, Set.indicator, hz, htheta, xi, q, reward]
  have htwo : currentMomentTwo rate rewards C_star C_h u t a z = xi * q ^ 2 := by
    simp [currentMomentTwo, Set.indicator, hz, htheta, xi, q, reward]
  have hround := QuantizedRecordingMoments.quantizedValue_roundingError
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi reward
    (ConstructorDimensions.D_pos p) rate.eta.property hxi hreward
  have hfirst := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi reward
    (ConstructorDimensions.D_pos p) rate.eta.property hxi hreward
  have hqnonneg := QuantizedRecordingMoments.quantizedValue_nonneg
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi reward
    rate.eta.property
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta xi reward
    (ConstructorDimensions.D_pos p) rate.eta.property hxi hreward
  have hr2 : reward ^ 2 ≤ 1 := by nlinarith [hreward.1, hreward.2]
  have hsecond1 : reward ^ 2 / xi ≤ 1 / xi :=
    div_le_div_of_nonneg_right hr2 hxi.le
  have hsecond2 : 1 / xi ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
    one_div_le_one_div_of_le hbeta hbetaxi
  have hfirst1 : xi * q ≤ 1 := hfirst.trans hreward.2
  refine ⟨theta, htheta, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [xi, reward, q, ReferenceFirstLaunchNumericalCell.queueParameters,
      hone] using hround
  · rw [hone]
    exact mul_nonneg hxi.le hqnonneg
  · simpa [xi, reward, q, ReferenceFirstLaunchNumericalCell.queueParameters,
      hone] using hfirst
  · simpa [xi, reward, q, ReferenceFirstLaunchNumericalCell.queueParameters,
      hone] using hfirst1
  · rw [htwo]
    exact mul_nonneg hxi.le (sq_nonneg q)
  · rw [htwo]
    exact hsecond
  · calc
      currentMomentTwo rate rewards C_star C_h u t a z = xi * q ^ 2 := htwo
      _ ≤ reward ^ 2 / xi := hsecond
      _ ≤ 1 / xi := hsecond1
      _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := hsecond2

/-- The raw physical arrival has the canonical inverse-β envelope on the
actual first-call event. -/
theorem currentRaw_bounds_on_firstCell (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    0 ≤ currentRaw rate rewards C_star C_h t a z ∧
      currentRaw rate rewards C_star C_h t a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hamp := currentAmplitude_bounds_on_firstCell rate rewards C_star C_h u t a z hz
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  rw [currentRaw_eq_armTest_mul_amplitude rate rewards C_star C_h u t a z hz]
  by_cases h : ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t z = some (some a)
  · simpa [currentArmTest, h] using hamp
  · have htest : currentArmTest rate rewards C_star C_h t a z = 0 := by
      simp [currentArmTest, h]
    rw [htest]
    constructor
    · simp
    · simpa using div_nonneg (show 0 ≤ (1 : ℝ) by norm_num) hbeta.le

private theorem currentMomentOne_factorization (u t : Fin p.T) (a : Fin p.K) :
    currentMomentOne rate rewards C_star C_h u t a = fun z =>
      (firstCell rate rewards C_star C_h u t).indicator
        (currentAmplitude rate rewards C_star C_h t a) z *
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => match calendarParameters rate rewards C_star C_h t z with
          | none => 0
          | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) z := by
  funext z
  by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
  · obtain ⟨_r, theta, _selected, _cell, _c, _ht, _hrewards, htheta,
      _hanchor, _hcell, _henabled, _hreward, _hrate, _hmarker, _hcellEq,
      _howner⟩ := actualFirstCellData rate rewards C_star C_h u t a z hz
    simp [currentMomentOne, currentAmplitude, Set.indicator, hz, htheta]
    ring
  · simp [currentMomentOne, Set.indicator, hz]

private theorem currentMomentTwo_factorization (u t : Fin p.T) (a : Fin p.K) :
    currentMomentTwo rate rewards C_star C_h u t a = fun z =>
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => (currentAmplitude rate rewards C_star C_h t a z) ^ 2) z *
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => match calendarParameters rate rewards C_star C_h t z with
          | none => 0
          | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) z := by
  funext z
  by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
  · obtain ⟨_r, theta, _selected, _cell, _c, _ht, _hrewards, htheta,
      _hanchor, _hcell, _henabled, _hreward, _hrate, _hmarker, _hcellEq,
      _howner⟩ := actualFirstCellData rate rewards C_star C_h u t a z hz
    simp [currentMomentTwo, currentAmplitude, Set.indicator, hz, htheta]
    ring
  · simp [currentMomentTwo, Set.indicator, hz]

/-- The indicated first-moment coefficient is measurable in the exact
pre-choice source-prefix field. -/
theorem currentMomentOne_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (currentMomentOne rate rewards C_star C_h u t a) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0 (t.val + 1)
  let E := firstCell rate rewards C_star C_h u t
  let xi := fun z : SourceInput p =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a
  let base := fun z : SourceInput p =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some theta =>
        CanonicalRecordingRates.xi p rate.eta.val theta.2 a *
          QuantizedRecordingMoments.quantizedValue
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
            (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
            (((rewards t a).val : ℝ) / (D p : ℝ))
  have hxi : Measurable[F] xi := by
    simpa [F, xi] using measurable_calendarXi rate rewards C_star C_h control0 t a
  have hamp : Measurable[F] (currentAmplitude rate rewards C_star C_h t a) :=
    currentAmplitude_measurable rate rewards C_star C_h control0 u t a
  have hbase : base = fun z => xi z * currentAmplitude rate rewards C_star C_h t a z := by
    funext z
    cases hP : calendarParameters rate rewards C_star C_h t z <;>
      simp [base, xi, currentAmplitude, hP]
  have hbaseMeas : Measurable[F] base := by
    rw [hbase]
    exact hxi.mul hamp
  have hE : MeasurableSet[F] E := by
    simpa [F, E] using ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  change Measurable[F] (E.indicator base)
  exact hbaseMeas.indicator hE

/-- The indicated square-moment coefficient is measurable in the same field. -/
theorem currentMomentTwo_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (currentMomentTwo rate rewards C_star C_h u t a) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
    control0 (t.val + 1)
  let E := firstCell rate rewards C_star C_h u t
  let xi := fun z : SourceInput p =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a
  let base := fun z : SourceInput p =>
    match calendarParameters rate rewards C_star C_h t z with
    | none => 0
    | some theta =>
        let q := QuantizedRecordingMoments.quantizedValue
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
          (CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
          (((rewards t a).val : ℝ) / (D p : ℝ))
        CanonicalRecordingRates.xi p rate.eta.val theta.2 a * q ^ 2
  have hxi : Measurable[F] xi := by
    simpa [F, xi] using measurable_calendarXi rate rewards C_star C_h control0 t a
  have hamp : Measurable[F] (currentAmplitude rate rewards C_star C_h t a) :=
    currentAmplitude_measurable rate rewards C_star C_h control0 u t a
  have hbase : base = fun z => xi z * (currentAmplitude rate rewards C_star C_h t a z) ^ 2 := by
    funext z
    cases hP : calendarParameters rate rewards C_star C_h t z <;>
      simp [base, xi, currentAmplitude, hP]
  have hbaseMeas : Measurable[F] base := by
    rw [hbase]
    exact hxi.mul (hamp.pow_const 2)
  have hE : MeasurableSet[F] E := by
    simpa [F, E] using ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  change Measurable[F] (E.indicator base)
  exact hbaseMeas.indicator hE

theorem currentMomentOne_stronglyMeasurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (currentMomentOne rate rewards C_star C_h u t a) :=
  (currentMomentOne_measurable rate rewards C_star C_h control0 u t a).stronglyMeasurable

theorem currentMomentTwo_stronglyMeasurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (currentMomentTwo rate rewards C_star C_h u t a) :=
  (currentMomentTwo_measurable rate rewards C_star C_h control0 u t a).stronglyMeasurable

private theorem firstCell_measurable_ambient (control0 : TimeControl p)
    (u t : Fin p.T) :
    MeasurableSet (firstCell rate rewards C_star C_h u t) := by
  have hle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  exact hle _ (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t)

private theorem integrable_of_measurable_norm_le_const {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (c : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ c) : Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem currentMomentOne_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (currentMomentOne rate rewards C_star C_h u t a)
      (sourceInputLaw p) := by
  let f := currentMomentOne rate rewards C_star C_h u t a
  have hle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hf : Measurable f :=
    (currentMomentOne_measurable rate rewards C_star C_h control0 u t a).mono hle le_rfl
  have hb (z : SourceInput p) : ‖f z‖ ≤ 1 := by
    by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
    · obtain ⟨_theta, _htheta, _hlower, hnonneg, _hupper, hleOne,
        _hsecondNonneg, _hsecondUpper, _hbetaUpper⟩ :=
        currentMoment_bounds_on_firstCell rate rewards C_star C_h u t a z hz
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hleOne
    · simp [f, currentMomentOne, Set.indicator, hz]
  exact integrable_of_measurable_norm_le_const _ hf 1 hb

theorem currentMomentTwo_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (currentMomentTwo rate rewards C_star C_h u t a)
      (sourceInputLaw p) := by
  let f := currentMomentTwo rate rewards C_star C_h u t a
  let C := 1 / CanonicalRecordingRates.beta p rate.eta.val
  have hle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (t.val + 1)
  have hf : Measurable f :=
    (currentMomentTwo_measurable rate rewards C_star C_h control0 u t a).mono hle le_rfl
  have hbeta : 0 ≤ C :=
    div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  have hb (z : SourceInput p) : ‖f z‖ ≤ C := by
    by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
    · obtain ⟨_theta, _htheta, _hlower, _honeNonneg, _honeUpper,
        _honeOne, hnonneg, _hupper, hleC⟩ :=
        currentMoment_bounds_on_firstCell rate rewards C_star C_h u t a z hz
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact hleC
    · simpa [f, currentMomentTwo, Set.indicator, hz] using hbeta
  exact integrable_of_measurable_norm_le_const _ hf C hb

private theorem currentRaw_eq_coordinate_readout (t : Fin p.T) (a : Fin p.K) :
    currentRaw rate rewards C_star C_h t a = fun z =>
      ((ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates
        rate rewards C_star C_h t z).map (fun c =>
          if c.2.1 = some a then
            QuantizedRecordingMoments.quantizedValue
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
              (c.2.2.2 a) (c.2.2.1 a)
          else 0)).elim 0 id := by
  funext z
  cases hc : ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h t z with
  | none => simp [currentRaw,
      ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates, hc]
  | some c =>
      have hraw : RecordedRoundMoments.normalizedQuantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
          if c.recordedArm = some a then
            QuantizedRecordingMoments.quantizedValue
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
              (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
              (c.rate a) (c.reward a) else 0 := by
        by_cases hrecorded : c.recordedArm = some a
        · simpa [hrecorded] using
            RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a hrecorded
        · have hzero : RecordedRoundMoments.normalizedQuantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
            unfold RecordedRoundMoments.normalizedQuantizedArrival
            rw [RecordedQueueRun.quantizedArrival_eq_zero
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a hrecorded]
            simp
          simpa [hrecorded] using hzero
      simp only [currentRaw, ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates,
        hc,
        Option.map_some, ReferenceLaterLiveReadoutValuesMeasurability.numericalCoordinates]
      rw [hraw]
      by_cases hrecorded : c.recordedArm = some a <;> simp [hrecorded]

/-- The actual unserved scalar is measurable on the whole original source. -/
theorem currentRaw_measurable (t : Fin p.T) (a : Fin p.K) :
    Measurable (currentRaw rate rewards C_star C_h t a) := by
  let coords := ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates
    rate rewards C_star C_h t
  let rawCoord := fun c : ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates
      (p := p) =>
    if c.2.1 = some a then
      QuantizedRecordingMoments.quantizedValue
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (c.2.2.2 a) (c.2.2.1 a)
    else 0
  have hmark : Measurable (fun c :
      ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p) => c.2.1) :=
    measurable_fst.comp measurable_snd
  have hreward : Measurable (fun c :
      ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p) =>
        c.2.2.1 a) :=
    (measurable_pi_apply a).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hrate : Measurable (fun c :
      ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p) =>
        c.2.2.2 a) :=
    (measurable_pi_apply a).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hquant := measurable_quantizedValue
    (fun c : ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p) =>
      c.2.2.2 a)
    (fun c : ReferenceLaterLiveCalendarMeasurability.NumericalCoordinates (p := p) =>
      c.2.2.1 a) hrate hreward
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).D
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
  have hrawCoord : Measurable rawCoord := by
    dsimp only [rawCoord]
    exact Measurable.ite (measurableSet_eq_fun hmark measurable_const)
      hquant measurable_const
  have hmapped := LaterAssignmentFullOutputMeasurability.measurable_optionMap
    rawCoord hrawCoord coords
    (ReferenceFirstCollectionCurrentNumericalCell.currentCoordinates_measurable
      rate rewards C_star C_h t)
  have hreadout := (measurable_option_elim id measurable_id (0 : ℝ)).comp hmapped
  rw [currentRaw_eq_coordinate_readout rate rewards C_star C_h t a]
  exact hreadout

theorem currentRaw_sq_measurable (t : Fin p.T) (a : Fin p.K) :
    Measurable (fun z => (currentRaw rate rewards C_star C_h t a z) ^ 2) :=
  (currentRaw_measurable rate rewards C_star C_h t a).pow_const 2

/-- Squaring the localized observation equals localizing its square. -/
theorem currentRaw_indicator_sq_eq (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    ((firstCell rate rewards C_star C_h u t).indicator
      (currentRaw rate rewards C_star C_h t a) z) ^ 2 =
    (firstCell rate rewards C_star C_h u t).indicator
      (fun z => (currentRaw rate rewards C_star C_h t a z) ^ 2) z := by
  by_cases hz : z ∈ firstCell rate rewards C_star C_h u t <;>
    simp [Set.indicator, hz]

theorem currentRaw_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable ((firstCell rate rewards C_star C_h u t).indicator
      (currentRaw rate rewards C_star C_h t a)) (sourceInputLaw p) := by
  let E := firstCell rate rewards C_star C_h u t
  let f := currentRaw rate rewards C_star C_h t a
  have hE := firstCell_measurable_ambient rate rewards C_star C_h control0 u t
  have hf : Measurable (E.indicator f) := by
    exact (currentRaw_measurable rate rewards C_star C_h t a).indicator hE
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hC : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
    div_nonneg (by norm_num) hbeta.le
  have hb (z : SourceInput p) : ‖E.indicator f z‖ ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (currentRaw_bounds_on_firstCell
          rate rewards C_star C_h u t a z hz).1]
      exact (currentRaw_bounds_on_firstCell rate rewards C_star C_h u t a z hz).2
    · simpa [Set.indicator_of_notMem hz] using hC
  exact integrable_of_measurable_norm_le_const _ hf _ hb

theorem currentRaw_sq_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable ((firstCell rate rewards C_star C_h u t).indicator
      (fun z => (currentRaw rate rewards C_star C_h t a z) ^ 2))
      (sourceInputLaw p) := by
  let E := firstCell rate rewards C_star C_h u t
  let f := fun z : SourceInput p => (currentRaw rate rewards C_star C_h t a z) ^ 2
  have hE := firstCell_measurable_ambient rate rewards C_star C_h control0 u t
  have hf : Measurable (E.indicator f) := by
    exact (currentRaw_sq_measurable rate rewards C_star C_h t a).indicator hE
  let C := 1 / CanonicalRecordingRates.beta p rate.eta.val
  have hbeta : 0 < CanonicalRecordingRates.beta p rate.eta.val :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hC : 0 ≤ C := div_nonneg (by norm_num) hbeta.le
  have hb (z : SourceInput p) : ‖E.indicator f z‖ ≤ C ^ 2 := by
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (sq_nonneg _)]
      have hr := currentRaw_bounds_on_firstCell rate rewards C_star C_h u t a z hz
      calc
        (currentRaw rate rewards C_star C_h t a z) ^ 2 ≤
            currentRaw rate rewards C_star C_h t a z * C :=
          by simpa only [pow_two] using mul_le_mul_of_nonneg_left hr.2 hr.1
        _ ≤ C * C := mul_le_mul_of_nonneg_right hr.2 hC
        _ = C ^ 2 := by ring
    · simpa [Set.indicator_of_notMem hz] using sq_nonneg C
  exact integrable_of_measurable_norm_le_const _ hf _ hb

theorem currentRaw_indicator_sq_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => ((firstCell rate rewards C_star C_h u t).indicator
      (currentRaw rate rewards C_star C_h t a) z) ^ 2) (sourceInputLaw p) := by
  have h := currentRaw_sq_integrable rate rewards C_star C_h control0 u t a
  exact h.congr (Filter.Eventually.of_forall fun z =>
    (currentRaw_indicator_sq_eq rate rewards C_star C_h u t a z).symm)

section CurrentArmTestMeasurability

local instance sourceArmOptionMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Fin p.K)) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace _

local instance sourceMarkerOptionMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Option (Fin p.K))) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace _

private theorem currentArmTest_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable ((firstCell rate rewards C_star C_h u t).indicator
      (currentArmTest rate rewards C_star C_h t a)) (sourceInputLaw p) := by
  let E := firstCell rate rewards C_star C_h u t
  let test := currentArmTest rate rewards C_star C_h t a
  have hmarker := ReferenceFirstCollectionCurrentRecordedCell.currentMarker_measurable
    rate rewards C_star C_h t
  have htest : Measurable test := by
    dsimp [test, currentArmTest]
    exact Measurable.ite (measurableSet_eq_fun hmarker measurable_const)
      measurable_const measurable_const
  have hE := firstCell_measurable_ambient rate rewards C_star C_h control0 u t
  have hmeas : Measurable (E.indicator test) := by
    exact htest.indicator hE
  have hb (z : SourceInput p) : ‖E.indicator test z‖ ≤ 1 := by
    by_cases hz : z ∈ E
    · simp [test, currentArmTest, Set.indicator, hz]
      split_ifs <;> norm_num
    · simp [test, Set.indicator, hz]
  exact integrable_of_measurable_norm_le_const _ hmeas 1 hb

end CurrentArmTestMeasurability

/-- The first conditional raw moment is the actual quantized first
coefficient, under the original source law and the exact source-prefix field. -/
theorem currentRaw_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (currentRaw rate rewards C_star C_h t a) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      currentMomentOne rate rewards C_star C_h u t a := by
  let E := firstCell rate rewards C_star C_h u t
  let amp := currentAmplitude rate rewards C_star C_h t a
  let test := fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t z = some (some a) then (1 : ℝ) else 0
  let ampI := E.indicator amp
  let testI := E.indicator test
  let rawI := E.indicator (currentRaw rate rewards C_star C_h t a)
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hE : MeasurableSet[F] E := by
    simpa [E, F] using ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hamp : Measurable[F] ampI := by
    exact (currentAmplitude_measurable rate rewards C_star C_h control0 u t a).indicator hE
  have hprod : rawI = fun z => ampI z * testI z := by
    funext z
    by_cases hz : z ∈ E
    · simp only [rawI, ampI, testI, Set.indicator_of_mem hz]
      rw [currentRaw_eq_armTest_mul_amplitude rate rewards C_star C_h u t a z hz]
      dsimp [amp, test, currentArmTest]
      ring
    · simp [rawI, ampI, testI, Set.indicator_of_notMem hz]
  have hprodInt : Integrable (fun z => ampI z * testI z) (sourceInputLaw p) :=
    (currentRaw_integrable rate rewards C_star C_h control0 u t a).congr
      (Filter.Eventually.of_forall fun z => congrFun hprod z)
  have htestInt := currentArmTest_integrable rate rewards C_star C_h control0 u t a
  have hpull := condExp_mul_of_stronglyMeasurable_left
    hamp.stronglyMeasurable hprodInt htestInt
  have hmarker := ReferenceFirstCollectionCurrentRecordedCell.firstCell_arm_condExp
    rate rewards C_star C_h control0 u t a
  have hmarker' :
      (sourceInputLaw p)[testI | F] =ᵐ[sourceInputLaw p]
        E.indicator (fun z => match calendarParameters rate rewards C_star C_h t z with
          | none => 0
          | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
    change (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
          rate rewards C_star C_h t z = some (some a) then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      (firstCell rate rewards C_star C_h u t).indicator (fun z =>
        match calendarParameters rate rewards C_star C_h t z with
        | none => 0
        | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
    exact hmarker
  calc
    _ =ᵐ[sourceInputLaw p]
        (sourceInputLaw p)[(fun z => ampI z * testI z) | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hprod z)
    _ =ᵐ[sourceInputLaw p] fun z =>
        ampI z * (sourceInputLaw p)[testI | F] z := hpull
    _ =ᵐ[sourceInputLaw p] currentMomentOne rate rewards C_star C_h u t a := by
      filter_upwards [hmarker'] with z hrate
      rw [hrate]
      exact (congrFun
        (currentMomentOne_factorization rate rewards C_star C_h u t a) z).symm

/-- The square conditional raw moment uses the same arm test and squares only
the same predictable quantized amplitude. -/
theorem currentRaw_sq_condExp (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[
      (fun z => ((firstCell rate rewards C_star C_h u t).indicator
        (currentRaw rate rewards C_star C_h t a) z) ^ 2) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      currentMomentTwo rate rewards C_star C_h u t a := by
  let E := firstCell rate rewards C_star C_h u t
  let amp := currentAmplitude rate rewards C_star C_h t a
  let test := fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t z = some (some a) then (1 : ℝ) else 0
  let ampSqI := E.indicator (fun z => (amp z) ^ 2)
  let testI := E.indicator test
  let rawSqI := fun z =>
    (E.indicator (currentRaw rate rewards C_star C_h t a) z) ^ 2
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hE : MeasurableSet[F] E := by
    simpa [E, F] using ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hamp : Measurable[F] ampSqI := by
    exact ((currentAmplitude_measurable rate rewards C_star C_h control0 u t a).pow_const 2).indicator hE
  have hprod : rawSqI = fun z => ampSqI z * testI z := by
    funext z
    by_cases hz : z ∈ E
    · simp only [rawSqI, ampSqI, testI, Set.indicator_of_mem hz]
      rw [currentRaw_sq_eq_armTest_mul_amplitude_sq
        rate rewards C_star C_h u t a z hz]
      dsimp [amp, test, currentArmTest]
      ring_nf
    · simp [rawSqI, ampSqI, testI, Set.indicator_of_notMem hz]
  have hprodInt : Integrable (fun z => ampSqI z * testI z) (sourceInputLaw p) :=
    (currentRaw_indicator_sq_integrable rate rewards C_star C_h control0 u t a).congr
      (Filter.Eventually.of_forall fun z => congrFun hprod z)
  have htestInt := currentArmTest_integrable rate rewards C_star C_h control0 u t a
  have hpull := condExp_mul_of_stronglyMeasurable_left
    hamp.stronglyMeasurable hprodInt htestInt
  have hmarker := ReferenceFirstCollectionCurrentRecordedCell.firstCell_arm_condExp
    rate rewards C_star C_h control0 u t a
  have hmarker' :
      (sourceInputLaw p)[testI | F] =ᵐ[sourceInputLaw p]
        E.indicator (fun z => match calendarParameters rate rewards C_star C_h t z with
          | none => 0
          | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
    change (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
          rate rewards C_star C_h t z = some (some a) then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      (firstCell rate rewards C_star C_h u t).indicator (fun z =>
        match calendarParameters rate rewards C_star C_h t z with
        | none => 0
        | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a)
    exact hmarker
  calc
    _ =ᵐ[sourceInputLaw p]
        (sourceInputLaw p)[(fun z => ampSqI z * testI z) | F] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hprod z)
    _ =ᵐ[sourceInputLaw p] fun z =>
        ampSqI z * (sourceInputLaw p)[testI | F] z := hpull
    _ =ᵐ[sourceInputLaw p] currentMomentTwo rate rewards C_star C_h u t a := by
      filter_upwards [hmarker'] with z hrate
      rw [hrate]
      exact (congrFun
        (currentMomentTwo_factorization rate rewards C_star C_h u t a) z).symm

/-- Every set in the exact pre-choice field tests the first raw moment under
the original source law, including a zero-mass first-call event. -/
theorem currentRaw_setIntegral (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) (A : Set (SourceInput p))
    (hA : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A) :
    (∫ z in A,
      (firstCell rate rewards C_star C_h u t).indicator
        (currentRaw rate rewards C_star C_h t a) z ∂sourceInputLaw p) =
    ∫ z in A, currentMomentOne rate rewards C_star C_h u t a z
      ∂sourceInputLaw p := by
  let μ := sourceInputLaw p
  let f := (firstCell rate rewards C_star C_h u t).indicator
    (currentRaw rate rewards C_star C_h t a)
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hce := currentRaw_condExp rate rewards C_star C_h control0 u t a
  have hceOnA : ∀ᵐ z ∂μ, z ∈ A →
      μ[f | sourcePrefixFiltration control0 (t.val + 1)] z =
        currentMomentOne rate rewards C_star C_h u t a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in A,
        μ[f | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ :=
      (setIntegral_condExp hFle
        (currentRaw_integrable rate rewards C_star C_h control0 u t a) hA).symm
    _ = _ := setIntegral_congr_ae (hFle _ hA) hceOnA

/-- The same arbitrary-field-set identity for the square raw moment. -/
theorem currentRaw_sq_setIntegral (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) (A : Set (SourceInput p))
    (hA : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A) :
    (∫ z in A,
      ((firstCell rate rewards C_star C_h u t).indicator
        (currentRaw rate rewards C_star C_h t a) z) ^ 2
        ∂sourceInputLaw p) =
    ∫ z in A, currentMomentTwo rate rewards C_star C_h u t a z
      ∂sourceInputLaw p := by
  let μ := sourceInputLaw p
  let f := fun z => ((firstCell rate rewards C_star C_h u t).indicator
    (currentRaw rate rewards C_star C_h t a) z) ^ 2
  have hFle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hce := currentRaw_sq_condExp rate rewards C_star C_h control0 u t a
  have hceOnA : ∀ᵐ z ∂μ, z ∈ A →
      μ[f | sourcePrefixFiltration control0 (t.val + 1)] z =
        currentMomentTwo rate rewards C_star C_h u t a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in A,
        μ[f | sourcePrefixFiltration control0 (t.val + 1)] z ∂μ :=
      (setIntegral_condExp hFle
        (currentRaw_indicator_sq_integrable rate rewards C_star C_h control0 u t a) hA).symm
    _ = _ := setIntegral_congr_ae (hFle _ hA) hceOnA

end Bandits.Support.ReferenceFirstCollectionCurrentRawMoments

end
