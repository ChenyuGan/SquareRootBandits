/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

import Mathlib.Tactic

/-!
# Actual original-installation physical sentinel section

This module uses the original complete physical source and retains a fixed
calendar entry index while replacing the whole current control.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw
open Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalInstallationReleaseSentinelSection

variable {p : ConstructorDimensions.Parameters}

private theorem sampleFast_val_congr_slowSet
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (Bandits.Support.CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    {U V : Bandits.Support.CanonicalOrientedSetLaw.SlowSet p.K p.m}
    (hUV : U = V)
    (x : ContinuousControlSlice.Scalar) :
    (CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U x).val =
      (CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv V x).val := by
  cases hUV
  rfl

/-- The physical auxiliary-arm charge, gated by the literal local entry at a
fixed calendar index. An absent or false gate contributes zero; a present
entry with empty pending set also contributes zero. -/
def actualFixedReleaseSentinelCharge
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t z).map
      Prod.fst = some true then
    match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => 0
    | some r =>
      match r.output.preparation.coordinator.selection with
      | none => 0
      | some selected =>
        if selected.arm = (selectedAuxiliaryFastArm rate selected).val ∧
            (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
            selected.view.payload.assignment.auxiliary
        else 0
  else 0

/-- For a fixed original entry index, its physical sentinel charge is bounded
by the canonical auxiliary fast-arm mass after resampling the whole current
control. The index equation is used only for the original source; it is not
transported to the replaced sources. -/
theorem actual_later_local_release_physical_sentinel_section
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (t : Fin p.T)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z).map Prod.fst = some true) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      (∫ control,
        actualFixedReleaseSentinelCharge rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)
        ∂ContinuousLearningRows.timeControlLaw p) ≤
        (if (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
            (1 : ℝ) else 0) *
          selectedFastArmMass rate selected (selectedAuxiliaryFastArm rate selected) *
            ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              (selectedAuxiliaryFastArm rate selected).1 := by
  classical
  obtain ⟨r, selected, states, memories, hr, hselection, hall⟩ :=
    actual_later_local_release_physical_frame_all_controls
      rate rewards C_star C_h control0 z b t hb hg
  let e := selectedAuxiliaryFastArm rate selected
  let P := ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let F : ContinuousControlSlice.Scalar →
      CanonicalFastSampling.FastArm selected.view.payload.slowSet := fun x =>
    CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (completeCurrentWeights selected) selected.view.payload.anchor_pos
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
      selected.view.payload.slowSet x
  have hgate (control : TimeControl p) :
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
        t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)).map
        Prod.fst = some true := by
    have hcode := incomingStateCode_replace_current rate rewards C_star C_h control0 t z control
    have hentry :
        ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
            t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
          ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
            t z := by
      change Option.map
          (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate
            (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) t)
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)) = _
      exact congrArg (Option.map
        (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) t))
        hcode
    rw [hentry]
    exact hg
  have hpoint (control : TimeControl p) :
      actualFixedReleaseSentinelCharge rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
        if (CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
                selected.view.payload.eta_le_source_cap selected.view.payload.anchor
                (completeCurrentWeights selected) selected.view.payload.anchor_pos
                (fun a => (completeCurrentWeights_bounds selected
                  (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
                (fun a => (completeCurrentWeights_bounds selected
                  (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
                (fun a => (completeCurrentWeights_bounds selected
                  (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
                selected.view.payload.slowSet
                (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)).1 = e.1 ∧
            P.Nonempty then row.val e.1 else 0 := by
    obtain ⟨ru, vu, hru, hinput, hstate, htime, hselectionU, hview, hweights,
      hemptyU, hcutoffU, hliveU, hordinaryU, hfieldsU, hpendingU, hfastU,
      hactionsU, hfeedbackU, hownU, hcostU, hzeroU⟩ := hall control
    have hgateU := hgate control
    have hauxVal : (selectedAuxiliaryFastArm rate vu).val = e.1 := by
      have hpayload : vu.view.payload = selected.view.payload :=
        congrArg (fun v => v.payload) hview
      simp only [selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm]
      rw [hpayload]
      rfl
    have hauxAssignment : vu.view.payload.assignment.auxiliary = e.1 := by
      have hpayload : vu.view.payload = selected.view.payload :=
        congrArg (fun v => v.payload) hview
      rw [hpayload]
      rfl
    have hpendingU' : ReferencePhysicalReleaseQuota.pendingSet
        selected.view.payload ru = P := by
      simpa only [hview, P] using hpendingU
    have hrowU : ru.input.row.2 ru.input.time = control := by
      simp only [hinput, ReferenceLaterOptionalControlResampling.withControl_time,
        ReferenceLaterOptionalControlResampling.withControl_currentControl]
    have hcanonical : vu.arm =
        (CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
          vu.view.payload.eta_le_source_cap vu.view.payload.anchor
          (completeCurrentWeights vu) vu.view.payload.anchor_pos
          (fun a => (completeCurrentWeights_bounds vu
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid vu) a).1)
          (fun a => (completeCurrentWeights_bounds vu
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid vu) a).2.1)
          (fun a => (completeCurrentWeights_bounds vu
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid vu) a).2.2)
          vu.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)).1 := by
      have hphysical := hfastU
      dsimp only [actualReleaseKernelInput, ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
        ReleaseRoundKernel.releaseRoundInput] at hphysical
      rw [hrowU] at hphysical
      exact hphysical.symm
    have hfastEq :
        (F (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)).val =
          vu.arm := by
      have hslow : vu.view.payload.slowSet = selected.view.payload.slowSet :=
        congrArg (fun v => v.payload.slowSet) hview
      have hcanon :
          (CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
            selected.view.payload.eta_le_source_cap selected.view.payload.anchor
            (completeCurrentWeights selected) selected.view.payload.anchor_pos
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
            vu.view.payload.slowSet
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)).val = vu.arm := by
        simpa [hview, hweights] using hcanonical.symm
      have hsample := sampleFast_val_congr_slowSet p rate.eta rate.eta.property
        selected.view.payload.eta_le_source_cap selected.view.payload.anchor
        (completeCurrentWeights selected) selected.view.payload.anchor_pos
        (fun a => (completeCurrentWeights_bounds selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
        (fun a => (completeCurrentWeights_bounds selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
        (fun a => (completeCurrentWeights_bounds selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
        hslow.symm (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)
      simpa only [F] using hsample.trans hcanon
    have htest :
        (vu.arm = e.1 ∧ P.Nonempty) ↔
          ((F (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)).val =
            e.1 ∧ P.Nonempty) := by
      constructor
      · rintro ⟨harm, hp⟩
        exact ⟨hfastEq.trans harm, hp⟩
      · rintro ⟨harm, hp⟩
        exact ⟨hfastEq.symm.trans harm, hp⟩
    have hcharge : (if vu.arm = e.1 ∧ P.Nonempty then row.val e.1 else 0) =
        (if (F (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          control.1)).val = e.1 ∧ P.Nonempty then row.val e.1 else 0) := by
      by_cases h : vu.arm = e.1 ∧ P.Nonempty
      · have h' := htest.mp h
        rw [ite_eq_left h, ite_eq_left h']
      · have h' : ¬ ((F (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            control.1)).val = e.1 ∧ P.Nonempty) := fun hh => h (htest.mpr hh)
        rw [ite_eq_right h, ite_eq_right h']
    simpa [actualFixedReleaseSentinelCharge, hgateU, hru, hselectionU,
      hpendingU, hauxVal, hauxAssignment, F] using hcharge
  have hsectionBound :
      (∫ control,
        actualFixedReleaseSentinelCharge rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)
        ∂ContinuousLearningRows.timeControlLaw p) ≤
      (if P.Nonempty then (1 : ℝ) else 0) * selectedFastArmMass rate selected e *
        ReleaseRoundKernel.chi row e.1 := by
    rw [show (∫ control,
        actualFixedReleaseSentinelCharge rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control)
        ∂ContinuousLearningRows.timeControlLaw p) =
      ∫ control, (if (F (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        control.1)).val = e.1 ∧ P.Nonempty then row.val e.1 else 0)
        ∂ContinuousLearningRows.timeControlLaw p by
        apply integral_congr_ae
        filter_upwards [] with control
        exact hpoint control]
    by_cases hpending : P.Nonempty
    · rw [ite_eq_left hpending]
      have hscalar : MeasurePreserving
          (fun control : TimeControl p =>
            ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1)
          (ContinuousLearningRows.timeControlLaw p) ContinuousControlSlice.scalarLaw :=
        (ContinuousControlSlice.measurePreserving_coordinate ContinuousControlSlice.Label.fast).comp
          (ContinuousLearningRows.measurePreserving_slice p)
      let E : Set ContinuousControlSlice.Scalar := F ⁻¹' {e}
      have hF : Measurable F := by
        exact CanonicalFastSampling.measurable_sampleFast _ _ _ _ _ _ _ _ _ _ _
      have hE : MeasurableSet E := (measurableSet_singleton e).preimage hF
      have hmass : ContinuousControlSlice.scalarLaw E =
          ENNReal.ofReal (selectedFastArmMass rate selected e) := by
        rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
        unfold E F selectedFastArmMass
        exact CanonicalFastSampling.uniform_sampleFast_singleton _ _ _ _ _ _ _ _ _ _ _ _
      have hnonneg : 0 ≤ selectedFastArmMass rate selected e := by
        unfold selectedFastArmMass
        exact CanonicalFastSampling.qGamma_nonneg p rate.eta.property
          selected.view.payload.eta_le_source_cap selected.view.payload.anchor
          (completeCurrentWeights selected) selected.view.payload.anchor_pos
          (fun a => (completeCurrentWeights_bounds selected
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
          (fun a => (completeCurrentWeights_bounds selected
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
          (fun a => (completeCurrentWeights_bounds selected
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
          selected.view.payload.slowSet e
      let scalar : TimeControl p → ContinuousControlSlice.Scalar := fun control =>
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1
      let A : Set (TimeControl p) := scalar ⁻¹' E
      have hA : MeasurableSet A := hE.preimage hscalar.measurable
      have hrowIndicator : (fun control : TimeControl p =>
          if (F (scalar control)).val = e.1 then row.val e.1 else 0) =
          A.indicator (fun _ => row.val e.1) := by
        funext control
        by_cases h : F (scalar control) = e
        · simp [Set.indicator, A, E, h]
        · have hv : (F (scalar control)).val ≠ e.1 := by
            intro hv
            exact h (Subtype.ext hv)
          simp [Set.indicator, A, E, h, hv]
      have hconst : A.indicator (fun _ => row.val e.1) =
          fun control => row.val e.1 * (A.indicator (fun _ => (1 : ℝ)) control) := by
        funext control
        by_cases h : control ∈ A
        · simp [Set.indicator, h]
        · simp [Set.indicator, h]
      have hprob : ∫ control, A.indicator (fun _ => (1 : ℝ)) control
          ∂ContinuousLearningRows.timeControlLaw p = selectedFastArmMass rate selected e := by
        calc
          _ = (ContinuousLearningRows.timeControlLaw p A).toReal := integral_indicator_one hA
          _ = selectedFastArmMass rate selected e := by
            rw [hscalar.measure_preimage hE.nullMeasurableSet, hmass,
              ENNReal.toReal_ofReal hnonneg]
      have hfun : (fun control : TimeControl p =>
          if (F (scalar control)).val = e.1 ∧ P.Nonempty then row.val e.1 else 0) =
          fun control => if (F (scalar control)).val = e.1 then row.val e.1 else 0 := by
        funext control
        simp [hpending]
      rw [hfun]
      by_cases hpos : 0 < row.val e.1
      · have hchi : ReleaseRoundKernel.chi row e.1 = 1 := by
          simp [ReleaseRoundKernel.chi, hpos]
        rw [hchi]
        calc
          _ = ∫ control, A.indicator (fun _ => row.val e.1) control
                ∂ContinuousLearningRows.timeControlLaw p := by
            apply integral_congr_ae
            filter_upwards [] with control
            exact congrFun hrowIndicator control
          _ = ∫ control, row.val e.1 *
                (A.indicator (fun _ => (1 : ℝ)) control)
                ∂ContinuousLearningRows.timeControlLaw p := by
            apply integral_congr_ae
            filter_upwards [] with control
            exact congrFun hconst control
          _ = row.val e.1 * selectedFastArmMass rate selected e := by
            rw [integral_const_mul, hprob]
          _ ≤ 1 * selectedFastArmMass rate selected e :=
            mul_le_mul_of_nonneg_right (row.property e.1).2 hnonneg
          _ = 1 * selectedFastArmMass rate selected e * 1 := by ring
      · have hzero : row.val e.1 = 0 := by
          exact le_antisymm (le_of_not_gt hpos) (row.property e.1).1
        have hzeroFun : (fun control : TimeControl p =>
            if (F (scalar control)).val = e.1 then row.val e.1 else 0) = fun _ => 0 := by
          funext control
          simp [hzero]
        rw [hzeroFun, integral_zero]
        simp [hzero, ReleaseRoundKernel.chi]
    · have hzeroFun : (fun control : TimeControl p =>
          if (F (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            control.1)).val = e.1 ∧ P.Nonempty then row.val e.1 else 0) = fun _ => 0 := by
        funext control
        simp [hpending]
      rw [hzeroFun, integral_zero]
      simp [hpending]
  refine ⟨r, selected, hr, hselection, ?_⟩
  exact hsectionBound

/-- Read the literal fixed-index sentinel from the existing lossless record
code. The incoming gate is independent of the current selection; an absent
selection and a present selection with no pending follower both have value zero. -/
def fixedReleaseSentinelCodeValue
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s : ℕ) (t : Fin p.T)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) : ℝ :=
  if (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t code.2.1).1 then
    ReferenceCollectionOutcomeMeasurability.optionalElim 0
      (fun selected =>
        if selected.2.2 = selected.1.payload.assignment.auxiliary ∧
            (ReferencePhysicalReleaseQuota.pendingAtStart selected.1.payload t
              (ReferenceActivePhysicalStepMeasurability.decodeState code.2.1)).Nonempty then
          (wholeGridRewardRow rewards t).val selected.1.payload.assignment.auxiliary
        else 0)
      code.2.2.1.1
  else 0

theorem fixedReleaseSentinelCodeValue_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s : ℕ) (t : Fin p.T) :
    Measurable (fixedReleaseSentinelCodeValue rate rewards s t) := by
  let Code := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  let Sel := ReferenceLiveDispatchOutputMeasurability.SelectionData p rate
  have hstate : Measurable (fun code : Code => code.2.1) :=
    measurable_fst.comp measurable_snd
  have hpayload : Measurable (fun selected : Sel => selected.1.payload) :=
    (measurable_fst.comp (comap_measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)))).comp measurable_fst
  have haux : Measurable (fun selected : Sel => selected.1.payload.assignment.auxiliary) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp hpayload
  have hpending : Measurable (fun v : Sel × Code =>
      ReferencePhysicalReleaseQuota.pendingAtStart v.1.1.payload t
        (ReferenceActivePhysicalStepMeasurability.decodeState v.2.2.1)) :=
    ReferencePhysicalReleaseObservability.measurable_pendingAtStart.comp
      ((hpayload.comp measurable_fst).prodMk
        (measurable_const.prodMk
          ((ReferenceReleaseStrictPastFactor.measurable_decodeState rate).comp
            (hstate.comp measurable_snd))))
  have hnonempty : MeasurableSet {v : Sel × Code |
      (ReferencePhysicalReleaseQuota.pendingAtStart v.1.1.payload t
        (ReferenceActivePhysicalStepMeasurability.decodeState v.2.2.1)).Nonempty} :=
    hpending (Set.to_countable {P : Finset (Fin (p.m - 1)) | P.Nonempty}).measurableSet
  have harm : Measurable (fun selected : Sel => selected.2.2) :=
    measurable_snd.comp measurable_snd
  have htest : MeasurableSet {v : Sel × Code |
      v.1.2.2 = v.1.1.payload.assignment.auxiliary ∧
        (ReferencePhysicalReleaseQuota.pendingAtStart v.1.1.payload t
          (ReferenceActivePhysicalStepMeasurability.decodeState v.2.2.1)).Nonempty} :=
    (measurableSet_eq_fun (harm.comp measurable_fst)
      (haux.comp measurable_fst)).inter hnonempty
  have hvalue : Measurable (fun v : Sel × Code =>
      if v.1.2.2 = v.1.1.payload.assignment.auxiliary ∧
          (ReferencePhysicalReleaseQuota.pendingAtStart v.1.1.payload t
            (ReferenceActivePhysicalStepMeasurability.decodeState v.2.2.1)).Nonempty then
        (wholeGridRewardRow rewards t).val v.1.1.payload.assignment.auxiliary else 0) :=
    (((measurable_of_countable ((wholeGridRewardRow rewards t).val)).comp haux).comp
      measurable_fst).ite htest measurable_const
  have hselection : Measurable (fun code : Code => code.2.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hmap := (ReferenceCollectionOutcomeMeasurability.measurable_mapOptional _ hvalue).comp
    (hselection.prodMk measurable_id)
  have helim := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (0 : ℝ) id measurable_id
  have hgate := (ReferenceReleaseStrictPastFactor.measurable_localReleaseEntry rate s t).comp
    hstate
  have hmeas : Measurable (fun code : Code =>
      if (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t code.2.1).1 then
        ReferenceCollectionOutcomeMeasurability.optionalElim 0 id
          (ReferenceCollectionOutcomeMeasurability.mapOptional
            (fun v : Sel × Code =>
              if v.1.2.2 = v.1.1.payload.assignment.auxiliary ∧
                  (ReferencePhysicalReleaseQuota.pendingAtStart v.1.1.payload t
                    (ReferenceActivePhysicalStepMeasurability.decodeState v.2.2.1)).Nonempty then
                (wholeGridRewardRow rewards t).val v.1.1.payload.assignment.auxiliary else 0)
            (code.2.2.1.1, code)) else 0) :=
    (helim.comp hmap).ite
      (measurableSet_eq_fun (measurable_fst.comp hgate) (measurable_const (a := true)))
      measurable_const
  convert hmeas using 1
  funext code
  dsimp only [fixedReleaseSentinelCodeValue, Function.comp_def,
    ReferenceCollectionOutcomeMeasurability.mapOptional]
  split_ifs
  · cases code.2.2.1.1 <;> rfl
  · rfl

private theorem actualRecord_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) : r.input.time = t := by
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz] at hr
    cases hr

/-- The Borel code readout is exactly the original physical charge, with no
change to the absent, false-gate, zero-reward, or empty-pending branches. -/
theorem actualFixedReleaseSentinelCharge_eq_code
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFixedReleaseSentinelCharge rate rewards C_star C_h s t z =
      ReferenceCollectionOutcomeMeasurability.optionalElim 0
        (fixedReleaseSentinelCodeValue rate rewards s t)
        (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z) := by
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none =>
      simp only [actualFixedReleaseSentinelCharge, entry, incoming, hr,
        Option.map_none, reduceCtorEq, ↓reduceIte,
        ReferenceCalendarActualControlCallbackSections.codeAt,
        ReferenceCollectionOutcomeMeasurability.optionalElim]
  | some r =>
      have ht := actualRecord_time rate rewards C_star C_h t z r hr
      have hstateCode : (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1 =
          ReferenceActivePhysicalStepMeasurability.encodeState r.input.state := rfl
      have hfront := (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1
      have hs : (ReferenceActivePhysicalStep.dispatch r.input).selection =
          r.output.preparation.coordinator.selection := by
        simp only [r.output_eq, ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare]
      simp only [actualFixedReleaseSentinelCharge, entry, incoming, hr, Option.map_some,
        ReferenceCalendarActualControlCallbackSections.codeAt,
        ReferenceCollectionOutcomeMeasurability.optionalElim, fixedReleaseSentinelCodeValue,
        hfront, hs, hstateCode,
        ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
      change (if (some (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))).map
            Prod.fst = some true then _ else 0) = _
      simp only [Option.map_some, Option.some.injEq]
      split_ifs with hg
      · cases hsel : r.output.preparation.coordinator.selection with
        | none => rfl
        | some selected =>
            simp only [Option.map_some,
              ReferenceLiveDispatchOutputMeasurability.encodeSelection,
              ReferencePhysicalReleaseQuota.pendingSet, ht,
              selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm]
      · rfl

/-- Ambient Borel measurability on the original continuous source carrier. -/
theorem actualFixedReleaseSentinelCharge_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (t : Fin p.T) :
    Measurable (actualFixedReleaseSentinelCharge rate rewards C_star C_h s t) := by
  have hm := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ) _
    (fixedReleaseSentinelCodeValue_measurable rate rewards s t)).comp
      (ReferenceCalendarActualControlCallbackSections.measurable_codeAt rate rewards C_star C_h t)
  convert hm using 1
  funext z
  exact actualFixedReleaseSentinelCharge_eq_code rate rewards C_star C_h s t z

theorem actualFixedReleaseSentinelCharge_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ actualFixedReleaseSentinelCharge rate rewards C_star C_h s t z ∧
      actualFixedReleaseSentinelCharge rate rewards C_star C_h s t z ≤ 1 := by
  unfold actualFixedReleaseSentinelCharge
  split_ifs
  · cases actualRecord rate rewards C_star C_h t z with
    | none => norm_num
    | some r =>
        cases hsel : r.output.preparation.coordinator.selection with
        | none => simp only [hsel]; norm_num
        | some selected =>
            simp only [hsel]
            split_ifs
            · exact (wholeGridRewardRow rewards t).property _
            · norm_num
  · norm_num

theorem actualFixedReleaseSentinelCharge_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (t : Fin p.T) :
    Integrable (actualFixedReleaseSentinelCharge rate rewards C_star C_h s t)
      (sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (actualFixedReleaseSentinelCharge_measurable rate rewards C_star C_h s t).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨hzero, hone⟩ := actualFixedReleaseSentinelCharge_bounds rate rewards C_star C_h s t z
  simpa only [Real.norm_eq_abs, abs_of_nonneg hzero] using hone

/-- Causality of the fixed-index physical charge follows from the existing
lossless record-code factorization, including all exceptional branches. -/
theorem actualFixedReleaseSentinelCharge_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFixedReleaseSentinelCharge rate rewards C_star C_h s t z =
      actualFixedReleaseSentinelCharge rate rewards C_star C_h s t
        (sourcePrefix control0 (t.val + 1) z) := by
  rw [actualFixedReleaseSentinelCharge_eq_code, actualFixedReleaseSentinelCharge_eq_code,
    ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
      rate rewards C_star C_h control0 t z]

private theorem sourcePrefix_successor_replace_current
    (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u : TimeControl p) :
    sourcePrefix control0 (t.val + 1)
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (sourcePrefix control0 t.val z) u := by
  rw [prefix_successor_restore,
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z u]
  congr 1
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]

/-- Replacing the whole current control after taking the strict source prefix
has exactly the same fixed-index physical charge as replacing it in the
original source. This is a causal identity, not a calendar-invariance premise. -/
theorem actualFixedReleaseSentinelCharge_replace_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (u : TimeControl p) :
    actualFixedReleaseSentinelCharge rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
      actualFixedReleaseSentinelCharge rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) := by
  rw [actualFixedReleaseSentinelCharge_prefix rate rewards C_star C_h control0 s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
    sourcePrefix_successor_replace_current,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]

theorem actualFixedReleaseSentinelCharge_restore
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFixedReleaseSentinelCharge rate rewards C_star C_h s t z =
      actualFixedReleaseSentinelCharge rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z)
          (ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    ReferenceSourceCurrentControlFreshness.u_t, ← prefix_successor_restore]
  exact actualFixedReleaseSentinelCharge_prefix rate rewards C_star C_h control0 s t z

/-- Literal whole-current-control section of the original fixed-index charge.
Every unused current control coordinate remains integrated on its full law. -/
def actualFixedReleaseSentinelControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∫ u, actualFixedReleaseSentinelCharge rate rewards C_star C_h s t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
    ∂ContinuousLearningRows.timeControlLaw p

/-- A global fixed-`s` original-source conditional section identity. The
conditioning field is the analytical source-prefix field, with no acquired
protocol-history identification. -/
theorem actualFixedReleaseSentinelCharge_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (s : ℕ) (t : Fin p.T) :
    (sourceInputLaw p)[actualFixedReleaseSentinelCharge rate rewards C_star C_h s t |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      actualFixedReleaseSentinelControlSection rate rewards C_star C_h s t := by
  let f : BootstrapPrivateRoundStreams.SourceInput p × TimeControl p → ℝ := fun v =>
    actualFixedReleaseSentinelCharge rate rewards C_star C_h s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2)
  have hf : Measurable f :=
    (actualFixedReleaseSentinelCharge_measurable rate rewards C_star C_h s t).comp
      (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)
  have hbound : ∀ v, ‖f v‖ ≤ 1 := by
    intro v
    obtain ⟨hzero, hone⟩ := actualFixedReleaseSentinelCharge_bounds rate rewards C_star C_h s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2)
    simpa only [f, Real.norm_eq_abs, abs_of_nonneg hzero] using hone
  have hce := ReferenceFirstLiveInspectedFastCollision.source_control_weighted_condExp
    control0 t f hf hbound
  have hrestore : (fun z => f (ReferenceSourceCurrentControlFreshness.c_t p control0 t z,
      ReferenceSourceCurrentControlFreshness.u_t p t z)) =
        actualFixedReleaseSentinelCharge rate rewards C_star C_h s t := by
    funext z
    exact (actualFixedReleaseSentinelCharge_restore rate rewards C_star C_h control0 s t z).symm
  have hsection : (fun z => ∫ u,
      f (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, u)
        ∂ContinuousLearningRows.timeControlLaw p) =
      actualFixedReleaseSentinelControlSection rate rewards C_star C_h s t := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with u
    exact (actualFixedReleaseSentinelCharge_replace_prefix
      rate rewards C_star C_h control0 s t z u).symm
  rw [hrestore, hsection] at hce
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t] using hce

/-- A single original-source null set suffices for all literal fixed calendar
indices and dates. The index remains a parameter of each conditional
expectation; it is not a source-dependent conditioning label. -/
theorem actualFixedReleaseSentinelCharge_condExp_all
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ, ∀ t : Fin p.T,
      (sourceInputLaw p)[actualFixedReleaseSentinelCharge rate rewards C_star C_h s t |
        sourcePrefixFiltration control0 (t.val + 1)] z =
        actualFixedReleaseSentinelControlSection rate rewards C_star C_h s t z := by
  simp only [ae_all_iff]
  intro s t
  exact actualFixedReleaseSentinelCharge_condExp rate rewards C_star C_h control0 s t

/-- At every actual later installation and supported release date, the same
original physical record has both the signed all-player domination and the
conditional sentinel bound. Localization of the fixed index occurs only
after the global almost-everywhere section identity has been established.
No acquired-history or stopped-interval assertion is made. -/
theorem actual_later_local_release_physical_sentinel_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ,
      ∀ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length, ∀ t : Fin p.T,
      s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val →
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val].input = true →
      (entry rate rewards C_star C_h s t z).map Prod.fst = some true →
      ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (selected : ReferenceActivePhysicalStep.Selection r.input),
        actualRecord rate rewards C_star C_h t z = some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        ReleaseRoundKernel.slowReward (wholeGridRewardRow rewards t)
            selected.view.payload.slowSet +
          (wholeGridRewardRow rewards t).val selected.arm -
          (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤
          (∑ follower ∈ pendingSet selected.view.payload r,
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned follower)) +
          actualFixedReleaseSentinelCharge rate rewards C_star C_h s t z ∧
        (sourceInputLaw p)[actualFixedReleaseSentinelCharge rate rewards C_star C_h s t |
          sourcePrefixFiltration control0 (t.val + 1)] z ≤
          (if (pendingSet selected.view.payload r).Nonempty then (1 : ℝ) else 0) *
            selectedFastArmMass rate selected (selectedAuxiliaryFastArm rate selected) *
              ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
                (selectedAuxiliaryFastArm rate selected).val := by
  filter_upwards [actualFixedReleaseSentinelCharge_condExp_all
    rate rewards C_star C_h control0] with z hz
  intro s b t hs hb hg
  have hgate : (entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z).map Prod.fst = some true := by
    simpa only [hs] using hg
  obtain ⟨r, hr, _ht, registers, owned, base, selected, states, memories,
    _hstate, _hpayload, _hregisterPending, hselection, _hpending, _hcutoff,
    _hlive, _hvalid, _hordinary, _hfields, _hbefore, _hafter, _hweights,
    _hfast, _hactions, _hfeedback, hcost, _hcontinue⟩ :=
    actual_later_local_release_physical_frame rate rewards C_star C_h control0 z b t hb hgate
  obtain ⟨rSection, selectedSection, hrSection, hselectionSection, hbound⟩ :=
    actual_later_local_release_physical_sentinel_section
      rate rewards C_star C_h control0 z b t hb hgate
  have hrecord : rSection = r := Option.some.inj (hrSection.symm.trans hr)
  subst rSection
  have hselected : selectedSection = selected :=
    Option.some.inj (hselectionSection.symm.trans hselection)
  subst selectedSection
  refine ⟨r, selected, hr, hselection, ?_, ?_⟩
  · by_cases htest : selected.arm = selected.view.payload.assignment.auxiliary ∧
        (pendingSet selected.view.payload r).Nonempty
    · simpa only [actualFixedReleaseSentinelCharge, hg, ite_true, hr, hselection,
        selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm, htest] using hcost
    · simpa only [actualFixedReleaseSentinelCharge, hg, ite_true, hr, hselection,
        selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm, htest, ite_false] using hcost
  · rw [hz s t, actualFixedReleaseSentinelControlSection, hs]
    exact hbound

end Bandits.Support.ReferenceOriginalInstallationReleaseSentinelSection
