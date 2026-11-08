/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalCalendarLaterBirthRemainderRecorder

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Original-source later-birth recording and retained prefix step

The whole assignment vector remains under its original law. The actual
optional marker is lifted to the original source-prefix field, and actual
later births retain the initialized queue prefix and inherited energy.

Sources: ZIP4 `04_slow_fast_learner.tex:157-188,218-288`,
`06_interruptions.tex:355-426`, and `appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open AssignmentParameterFibreKernel (AssignmentVector)

open ReferenceSourcePrefixHistoryFiltration (actualRecord actualRecord_eq_none_of_not_launchBy
  sourcePrefix sourcePrefixFiltration sourcePrefixFiltration_round sourcePrefixFiltration_succ
  sourcePrefix_control sourcePrefix_eq_suffix sourcePrefix_preserves_actual_launch
  sourcePrefix_selected sourcePrefix_sourcePrefix)
open ReferenceCompletePhysicalHistory (completeSuffixRecords physicalStart)
open ReferenceFirstCollectionCurrentRawMoments (currentAmplitude currentAmplitude_measurable
  currentRaw currentRaw_measurable)
open ReferenceFirstCollectionCurrentRemainderLaw (currentControl currentControl_measurable
  currentMarker currentMarker_none_of_parameters_none currentParameters currentParameters_eq_code
  currentParameters_success_measurable currentSource currentSource_measurable)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open ReferenceLaterOptionalControlResampling (ControlRemainder controlRemainderLaw)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters calendarParameters_factor
  calendarParameters_measurable)
open ContinuousControlSlice (assignmentLaw)
open ReferenceFirstCollectionCurrentNumericalCell (currentCell)
open ReferenceSourceCurrentControlFreshness (c_t u_t)
open ReferenceFirstCollectionCurrentRetainedGate (H pastCells? prefixReadout?)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (prefixInputs prefixInputs_append_one)

open ReferenceActivePhysicalHorizon (RoundRecord)
open ReferenceDownReception (ChoiceTimeView)
open ReferenceFirstWindowNumericalStream (ActualLiveSourceCell)
open ReferenceLaterLiveNumericalReadout (laterLiveReadout laterLiveReadout_physical
  preparedOrdinary preparedStates preparedMemories prepared_configuration
  laterLiveReadout_numerical laterLiveReadout_some selection_choiceValid)
open RecordedQueueRun (RoundInput RunState quantizedArrival)
open ReferenceFirstCollectionCorrectedFutureRetainedMoment (prefixInputs_eq_pastCells)

open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)

variable {p : Parameters}

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

private theorem measurable_option_isSome (α : Type*) [MeasurableSpace α] :
    Measurable (Option.isSome : Option α → Bool) := by
  convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false
    (fun _ : α => true) measurable_const using 1
  funext q
  cases q <;> rfl

private theorem integrable_measurable_norm_le_one {α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ := by
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The real indicator of a Boolean branch. -/
def presentIndicator (b : Bool) : ℝ := if b then 1 else 0

/-- Actual selected-pair mass integrated over the WHOLE original assignment vector. -/
def laterBirthPresenceMassAtPrefix (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (pref : SourceInput p) : ℝ :=
  let w0 := (controlAssignmentSplitEquiv p control0).2
  ∫ v : AssignmentVector p, presentIndicator ((currentParameters
      rate rewards C_star C_h control0 t pref v w0).isSome)
      ∂assignmentLaw p.K

/-- The source-prefix conditional mass, evaluated on the original source by first taking its strict prefix. -/
def laterBirthPresenceMass (rate : RateInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (source : SourceInput p) : ℝ :=
  laterBirthPresenceMassAtPrefix rate rewards C_star C_h control0 t
    (sourcePrefix control0 t.val source)

variable (control0 : TimeControl p) (t : Fin p.T)
local notation "rawAt" => currentRaw rate rewards C_star C_h
local notation "amplitudeAt" => currentAmplitude rate rewards C_star C_h
local notation "parametersAt" => calendarParameters rate rewards C_star C_h
local notation "selectedAt" => currentParameters rate rewards C_star C_h
local notation "prefixAt" => prefixInputs rate rewards C_star C_h
local notation "birthMassAtPrefix" => laterBirthPresenceMassAtPrefix rate rewards C_star C_h
local notation "birthMass" => laterBirthPresenceMass rate rewards C_star C_h
local notation "originalPast" => sourcePrefixFiltration control0 (t.val + 1)
local notation "originalPrefix" => sourcePrefix control0 t.val
local notation "selectedSection" => selectedAt control0 t

private theorem laterBirthPresenceIntegrand_measurable : Measurable (fun q : SourceInput p × AssignmentVector p =>
      presentIndicator ((selectedSection q.1 q.2
        (controlAssignmentSplitEquiv p control0).2).isSome)) := by
  let w0 := (controlAssignmentSplitEquiv p control0).2
  have hc := currentControl_measurable.comp
    ((measurable_snd : Measurable (Prod.snd : SourceInput p × AssignmentVector p → _)).prodMk
      (measurable_const (a := w0)))
  have hp := (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val).comp
    (measurable_fst : Measurable (Prod.fst : SourceInput p × AssignmentVector p → _))
  have hs := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    (hp.prodMk hc)
  have hm := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim none
    (ReferenceFirstCollectionCurrentRemainderLaw.parametersFromCode rate)
    (ReferenceFirstCollectionCurrentRemainderLaw.parametersFromCode_measurable rate)).comp
    ((ReferenceCalendarActualControlCallbackSections.measurable_codeAt rate rewards C_star C_h t).comp hs)
  have heq := currentParameters_eq_code rate rewards C_star C_h control0 t
  have hparams : Measurable (fun q : SourceInput p × AssignmentVector p =>
      selectedSection q.1 q.2 w0) := by
    convert hm using 1
    funext q
    exact heq q.1 q.2 w0
  exact Measurable.ite (measurableSet_eq_fun ((measurable_option_isSome _).comp hparams)
    measurable_const) measurable_const measurable_const

private theorem presentIndicator_bounds (b : Bool) :
    0 ≤ presentIndicator b ∧ presentIndicator b ≤ 1 := by
  cases b <;> norm_num [presentIndicator]

private theorem laterBirthPresenceIntegrand_norm_le_one (pref : SourceInput p) (v : AssignmentVector p) :
    ‖presentIndicator ((selectedSection pref v
      (controlAssignmentSplitEquiv p control0).2).isSome)‖ ≤ 1 := by
  unfold presentIndicator
  cases (selectedSection pref v (controlAssignmentSplitEquiv p control0).2).isSome <;>
    norm_num

theorem laterBirthPresenceMassAtPrefix_bounds (pref : SourceInput p) :
    0 ≤ birthMassAtPrefix control0 t pref ∧ birthMassAtPrefix control0 t pref ≤ 1 := by
  let w0 := (controlAssignmentSplitEquiv p control0).2
  have hindicator := (laterBirthPresenceIntegrand_measurable rate rewards C_star C_h control0 t).comp
    ((measurable_const (a := pref)).prodMk (measurable_id : Measurable (id : AssignmentVector p → _)))
  have hint : Integrable (fun v : AssignmentVector p =>
      presentIndicator ((selectedSection pref v w0).isSome))
      (assignmentLaw p.K) :=
    integrable_measurable_norm_le_one _ hindicator
      (fun v => laterBirthPresenceIntegrand_norm_le_one rate rewards C_star C_h control0 t pref v)
  constructor
  · exact integral_nonneg fun v => (presentIndicator_bounds _).1
  · calc
      _ ≤ ∫ _ : AssignmentVector p, (1 : ℝ) ∂assignmentLaw p.K :=
        integral_mono hint (integrable_const (1 : ℝ)) (fun _ => (presentIndicator_bounds _).2)
      _ = 1 := by simp

theorem laterBirthPresenceMassAtPrefix_measurable : Measurable (birthMassAtPrefix control0 t) := by
  exact ((laterBirthPresenceIntegrand_measurable rate rewards C_star C_h control0 t).stronglyMeasurable.integral_prod_right').measurable

theorem laterBirthPresenceMass_measurable_sourcePrefix :
    Measurable[originalPast] (birthMass control0 t) := by
  have hpref : Measurable[originalPast] (originalPrefix) := by
    rw [sourcePrefixFiltration_succ]
    exact comap_measurable _
  exact (laterBirthPresenceMassAtPrefix_measurable rate rewards C_star C_h control0 t).comp hpref

private theorem sourcePrefixFiltration_eq_currentControlField : sourcePrefixFiltration control0
      (t.val + 1) = ReferenceSourceCurrentControlFreshness.m_t p control0 t := by
  rw [sourcePrefixFiltration_round]
  unfold ReferenceSourceCurrentControlFreshness.m_t
  have hsource : (fun z : SourceInput p =>
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t
        (fun _ => control0)) =
    c_t p control0 t := by
    funext z
    calc
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t
          (fun _ => control0) =
        originalPrefix z := (sourcePrefix_eq_suffix control0 t.val t.isLt z).symm
      _ = c_t p control0 t z :=
        (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z).symm
  rw [hsource]
  rfl

/-- The literal optional later-live marker on the original calendar source. -/
def sourceLaterMarker (source : SourceInput p) : Option (Option (Fin p.K)) :=
  (actualRecord rate rewards C_star C_h t source).bind fun r =>
      (laterLiveReadout (physicalStart rate source rewards C_star C_h) r).map
          fun cell => cell.recordedArm
local notation "birthMarker" => sourceLaterMarker rate rewards C_star C_h

/-- Borelness of the original physical optional marker. -/
theorem sourceLaterMarker_measurable : Measurable (birthMarker t) := by
  convert ReferenceFirstCollectionCurrentRecordedCell.currentMarker_measurable
    rate rewards C_star C_h t using 1
  funext source
  simp only [sourceLaterMarker, ReferenceFirstCollectionCurrentNumericalCell.currentMarker,
    currentCell, Option.map_bind, Function.comp_def]

/-- The SAME current-marker section as the fixed-vector/remainder recorder, now indexed jointly by the original source prefix and the whole control. -/
def sectionCurrentMarker (pref : SourceInput p) (control : TimeControl p) : Option (Option (Fin p.K)) :=
  let split := controlAssignmentSplitEquiv p control
  currentMarker rate rewards C_star C_h control0 t pref split.1 split.2

theorem sectionCurrentMarker_eq_source (pref : SourceInput p) (control : TimeControl p) :
    sectionCurrentMarker rate rewards C_star C_h control0 t pref control = birthMarker t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (originalPrefix pref) control) := by
  change birthMarker t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (originalPrefix pref)
      (currentControl (controlAssignmentSplitEquiv p control).1
        (controlAssignmentSplitEquiv p control).2)) = _
  rw [show currentControl (controlAssignmentSplitEquiv p control).1
      (controlAssignmentSplitEquiv p control).2 = control from
    (controlAssignmentSplitEquiv p).symm_apply_apply control]

/-- Joint Borelness needed by the original-source conditional test API. -/
theorem sectionCurrentMarker_measurable : Measurable (fun x : SourceInput p × TimeControl p =>
      sectionCurrentMarker rate rewards C_star C_h control0 t x.1 x.2) := by
  have hpref := (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
    control0 t.val).comp (measurable_fst : Measurable
      (Prod.fst : SourceInput p × TimeControl p → SourceInput p))
  have hsource := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
    p t).comp (hpref.prodMk measurable_snd)
  convert (sourceLaterMarker_measurable rate rewards C_star C_h t).comp hsource using 1
  funext x
  exact sectionCurrentMarker_eq_source rate rewards C_star C_h control0 t x.1 x.2

/-- The real mass of one present recording outcome at the actual anchor. -/
def viewOutcomeMass (view : ChoiceTimeView p rate.eta) (outcome : Option (Fin p.K)) : ℝ :=
  match outcome with
  | none => 1 - ∑ a, view.payload.rate a
  | some a => view.payload.rate a

/-- Actual present-outcome coefficient, with rejected/absent selected pairs assigned zero. -/
def laterBirthOutcomeCoefficient (pref : SourceInput p) (v : AssignmentVector p) (outcome : Option (Fin p.K)) : ℝ :=
  match selectedSection pref v (controlAssignmentSplitEquiv p control0).2 with
  | none => 0
  | some (view, _) => viewOutcomeMass rate view outcome

/-- The jointly Borel test of one actual present arm-or-bottom outcome. -/
def sectionCurrentMarkerSet (outcome : Option (Fin p.K)) : Set (SourceInput p × TimeControl p) :=
  {x | sectionCurrentMarker rate rewards C_star C_h control0 t x.1 x.2 = some outcome}

theorem sectionCurrentMarkerSet_measurable (outcome : Option (Fin p.K)) : MeasurableSet
      (sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome) :=
  measurableSet_eq_fun
    (sectionCurrentMarker_measurable rate rewards C_star C_h control0 t) measurable_const

private theorem recording_pmf_mass (rates : RecordedRoundMoments.RecordingRates p.K)
    (o : Option (Fin p.K)) : ((RecordedRoundMoments.recordingOutcomePMF rates) o).toReal =
    o.elim (1 - ∑ i, rates.rate i) rates.rate := by
  cases o with
  | none => exact ENNReal.toReal_ofReal rates.none_mass_nonneg
  | some i => exact ENNReal.toReal_ofReal (rates.rate_nonneg i)

/-- The accepted remainder law gives the actual fixed-vector recording probability. -/
theorem laterBirthOutcome_remainder_integral (pref : SourceInput p) (v : AssignmentVector p) (outcome : Option (Fin p.K)) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t pref = some theta →
      (∫ w : ControlRemainder p, (if currentMarker
          rate rewards C_star C_h control0 t pref v w = some outcome then (1 : ℝ) else 0)
        ∂controlRemainderLaw p) =
      laterBirthOutcomeCoefficient rate rewards C_star C_h control0 t pref v outcome := by
  intro theta hparameter
  let μw := controlRemainderLaw p
  let marker := currentMarker rate rewards C_star C_h control0 t pref v
  let test : Option (Option (Fin p.K)) → ℝ := fun m => if m = some outcome then 1 else 0
  have htest : Measurable test := measurable_of_countable _
  have hm := ReferenceOriginalCalendarLaterBirthRemainderRecorder.currentRemainder_laterMarker_measurable
    rate rewards C_star C_h control0 t pref v theta hparameter
  have hlaw := ReferenceOriginalCalendarLaterBirthRemainderRecorder.currentRemainder_laterBirth_optionalMarker_law
    rate rewards C_star C_h control0 t pref v theta hparameter
  change (∫ w, test (marker w) ∂μw) = _
  rw [← integral_map hm.aemeasurable htest.aestronglyMeasurable]
  change (∫ m, test m ∂(μw.map marker)) = _
  rw [hlaw]
  unfold laterBirthOutcomeCoefficient
  cases hp : selectedSection pref v (controlAssignmentSplitEquiv p control0).2 with
  | none => simp [test]
  | some q =>
      rw [integral_map (measurable_of_countable _).aemeasurable htest.aestronglyMeasurable,
        PMF.integral_eq_sum]
      simp only [test, Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [recording_pmf_mass]
      cases outcome <;> simp only [Option.elim_none, Option.elim_some, viewOutcomeMass,
        SnapshotRecordingKernel.recordingRates, ← q.1.payload.rate_eq_canonical]

/-- The genuine original assignment-vector average for one present recording outcome. -/
def laterBirthOutcomeMassAtPrefix (outcome : Option (Fin p.K)) (pref : SourceInput p) : ℝ :=
  ∫ v : AssignmentVector p,
    laterBirthOutcomeCoefficient rate rewards C_star C_h control0 t pref v outcome
    ∂assignmentLaw p.K
local notation "outcomeMassAtPrefix" => laterBirthOutcomeMassAtPrefix rate rewards C_star C_h
local notation "outcomeMass" => outcomeMassAtPrefix control0 t

/-- Fubini lifts the accepted actual fixed-vector law over the WHOLE current assignment vector, including orientation and every rejected branch. -/
theorem laterBirthOutcome_section_integral (pref : SourceInput p) (outcome : Option (Fin p.K)) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t pref = some theta →
      (∫ control : TimeControl p,
        (sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome).indicator
          (fun _ => (1 : ℝ)) (pref, control)
        ∂ContinuousLearningRows.timeControlLaw p) =
      outcomeMass outcome pref := by
  intro theta hparameter
  let split := controlAssignmentSplitEquiv p
  let μv := assignmentLaw p.K
  let μw := controlRemainderLaw p
  let g := fun x : AssignmentVector p × ControlRemainder p =>
    (sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome).indicator
      (fun _ => (1 : ℝ)) (pref, currentControl x.1 x.2)
  have hm : Measurable g := ((measurable_const (a := (1 : ℝ))).indicator
    (sectionCurrentMarkerSet_measurable rate rewards C_star C_h control0 t outcome)).comp
      (measurable_const.prodMk currentControl_measurable)
  have hi : Integrable g (μv.prod μw) := integrable_measurable_norm_le_one _ hm (fun x => by
    dsimp only [g]
    by_cases hx : (pref, currentControl x.1 x.2) ∈
        sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome
    <;> simp only [Set.indicator, hx, ite_true, ite_false, norm_one, norm_zero, zero_le_one, le_refl])
  calc
    _ = ∫ control, g (split control) ∂ContinuousLearningRows.timeControlLaw p := by
      congr 1
      funext control
      exact congrArg (fun u : TimeControl p =>
        (sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome).indicator
          (fun _ => (1 : ℝ)) (pref, u)) ((controlAssignmentSplitEquiv p).symm_apply_apply control).symm
    _ = ∫ x, g x ∂(μv.prod μw) :=
      (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).integral_comp
        split.measurableEmbedding g
    _ = ∫ v, ∫ w, g (v, w) ∂μw ∂μv := integral_prod g hi
    _ = outcomeMass outcome pref := by
      apply integral_congr_ae
      filter_upwards [] with v
      simpa only [g, Set.indicator, sectionCurrentMarkerSet, Set.mem_ofPred_eq,
        sectionCurrentMarker, currentControl, MeasurableEquiv.apply_symm_apply] using
        laterBirthOutcome_remainder_integral rate rewards C_star C_h control0 t pref v outcome theta hparameter

private theorem recordMarker_eq_of_current_code (left right : RoundRecord (p := p) (rate := rate))
    (s : ℕ) (hstate : left.input.state = right.input.state)
    (htime : left.input.time = right.input.time)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode left =
      ReferenceActiveHorizonMeasurability.roundRecordCode right) :
    (laterLiveReadout s left).map (fun c => c.recordedArm) = (laterLiveReadout s right).map
        (fun c => c.recordedArm) := by
  have hview : left.output.preparation.coordinator.downView =
      right.output.preparation.coordinator.downView := by
    rw [left.output.preparation.coordinator_eq, right.output.preparation.coordinator_eq]
    rw [← (ReferenceActiveHorizonMeasurability.roundRecordCode_front left).2.1,
      ← (ReferenceActiveHorizonMeasurability.roundRecordCode_front right).2.1, hcode]
  have hprepared (i : Fin (p.m - 1)) :
      (left.output.preparation.followers.followers i).configuration =
        (right.output.preparation.followers.followers i).configuration := by
    rw [left.output_eq, right.output_eq]
    change (DeclaredFollowerLocalRound.prepare rate i left.input.row
      (left.input.state.activations i) left.input.time (left.input.active i)
      (left.input.state.followers i)).configuration =
      (DeclaredFollowerLocalRound.prepare rate i right.input.row
        (right.input.state.activations i) right.input.time (right.input.active i)
        (right.input.state.followers i)).configuration
    have hc : left.input.row.2 right.input.time = right.input.row.2 right.input.time := by
      simpa only [htime] using hcurrent
    simpa only [hstate, htime] using
      congrArg Prod.snd (ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
        i (right.input.state.activations i) (right.input.active i)
        (right.input.state.followers i) hc)
  have ho : preparedOrdinary left ↔ preparedOrdinary right := by
    simp only [preparedOrdinary, hprepared]
  unfold ReferenceActivePhysicalStep.DispatchCut.downView at hview
  unfold laterLiveReadout
  cases hl : left.output.preparation.coordinator.selection with
  | none =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => rfl
      | some selected => simp only [hl, hr, Option.map_none, Option.map_some, reduceCtorEq] at hview
  | some l =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => simp only [hl, hr, Option.map_none, Option.map_some, reduceCtorEq] at hview
      | some r =>
          have hv : l.view = r.view := by
            simpa only [hl, hr, Option.map_some, Option.some.injEq] using hview
          dsimp only
          by_cases hcl : s < r.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive r.view.payload r.view.cutoff right.input.time
          · simp only [hv, htime, ite_eq_left hcl]
            by_cases hol : preparedOrdinary left
            · have hor := ho.mp hol
              simp only [dite_eq_left hol, dite_eq_left hor, Option.map_some]
              have hstates : preparedStates left hol = preparedStates right hor := by
                funext i
                have hordinary :=
                  (prepared_configuration left hol i).symm.trans ((hprepared i).trans
                      (prepared_configuration right hor i))
                exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hordinary).1
              congr 1
              dsimp only [ReferenceFirstWindowNumericalStream.sourceCell]
              unfold ReferenceFirstWindowNumericalStream.sourceArm
              congr 1
              · rw [hv, hstates]
              · rw [hv]
              · rw [hv]
              · exact congrArg Prod.fst hcurrent
            · have hor : ¬ preparedOrdinary right := fun h => hol (ho.mpr h)
              simp only [dite_eq_right hol, dite_eq_right hor, Option.map_none]
          · simp only [hv, htime, ite_eq_right hcl, Option.map_none]

private theorem optional_bind_congr_of_map_eq {α β γ : Type*}
    (f : α → β) (g h : α → Option γ) (x y : Option α)
    (hmap : x.map f = y.map f)
    (hpoint : ∀ a b, x = some a → y = some b → f a = f b → g a = h b) : x.bind g = y.bind h := by
  cases x with
  | none => cases y <;> simp_all
  | some a =>
      cases y with
      | none => simp only [Option.map_none, Option.map_some, reduceCtorEq] at hmap
      | some b => exact hpoint a b rfl rfl (Option.some.inj hmap)

private theorem sourceLaterMarker_eq_of_observations (source pref : SourceInput p)
    (hcode : ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t source =
      ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t pref)
    (hcontrols : ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) =
      ((pref.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p pref)).2 t))
    (hstarts : ∀ r, actualRecord rate rewards C_star C_h t source = some r →
      physicalStart rate source rewards C_star C_h = physicalStart rate pref rewards C_star C_h) :
    birthMarker t source = birthMarker t pref := by
  change (actualRecord
    rate rewards C_star C_h t source).map ReferenceActiveHorizonMeasurability.roundRecordCode =
    (actualRecord
      rate rewards C_star C_h t pref).map ReferenceActiveHorizonMeasurability.roundRecordCode at hcode
  change (actualRecord rate rewards C_star C_h t source).bind (fun r => (laterLiveReadout
      (physicalStart rate source rewards C_star C_h) r).map (fun c => c.recordedArm)) =
    (actualRecord rate rewards C_star C_h t pref).bind
    (fun r => (laterLiveReadout (physicalStart rate pref rewards C_star C_h) r).map
        (fun c => c.recordedArm))
  apply optional_bind_congr_of_map_eq ReferenceActiveHorizonMeasurability.roundRecordCode
    _ _ _ _ hcode
  intro r r' hr hr' hc
  have hstart := hstarts r hr
  have hstate : r.input.state = r'.input.state := by
    have h := congrArg (fun code =>
      ReferenceActivePhysicalStepMeasurability.decodeState code.2.1) hc
    exact (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).1.symm.trans
      (h.trans (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r').1)
  obtain ⟨hrows, hselected, htime, _⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t source r hr
  obtain ⟨hrows', hselected', htime', _⟩ :=
    ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t pref r' hr'
  have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
    change (r.input.rows r.input.selected).2 r.input.time =
      (r'.input.rows r'.input.selected).2 r'.input.time
    rw [hrows, hselected, htime, hrows', hselected', htime']
    exact hcontrols
  change (laterLiveReadout (physicalStart rate source rewards C_star C_h) r).map
        (fun c => c.recordedArm) = _
  rw [← hstart]
  exact recordMarker_eq_of_current_code rate r r' (physicalStart rate source rewards C_star C_h)
    hstate (htime.trans htime'.symm) hcurrent hc

/-- The original physical marker depends only on the source prefix through this round. -/
theorem sourceLaterMarker_successor_factor (source : SourceInput p) :
    birthMarker t source = birthMarker t (sourcePrefix control0 (t.val + 1) source) := by
  apply sourceLaterMarker_eq_of_observations rate rewards C_star C_h t source
    (sourcePrefix control0 (t.val + 1) source)
    (ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
      rate rewards C_star C_h control0 t source)
  · rw [sourcePrefix_selected, sourcePrefix_control, ite_eq_left (Nat.lt_succ_self _)]
  · intro r hr
    have hby : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h t.val source := by
      by_contra hn
      rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t source hn] at hr
      cases hr
    exact (sourcePrefix_preserves_actual_launch
      rate rewards C_star C_h control0 (t.val + 1) (by omega) source
      ⟨hby.1, hby.2.trans (Nat.le_succ _)⟩).1

/-- The current section restores the unmodified original physical marker when evaluated at the original current control. -/
theorem sectionCurrentMarker_restore (source : SourceInput p) :
    sectionCurrentMarker rate rewards C_star C_h control0 t (c_t p control0 t source)
        (u_t p t source) =
      birthMarker t source := by
  rw [sectionCurrentMarker_eq_source, ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    sourcePrefix_sourcePrefix control0 t.val t.val (Nat.le_refl _)]
  have hrestore := ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t source
  change sourcePrefix control0 (t.val + 1) source =
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t (originalPrefix source)
      (u_t p t source) at hrestore
  rw [← hrestore]
  exact (sourceLaterMarker_successor_factor rate rewards C_star C_h control0 t source).symm

/-- Literal restoration of the original-source event test. -/
theorem sourceControlTest_eq_original_marker (outcome : Option (Fin p.K)) :
    ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
        (sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome) =
      fun source => if birthMarker t source = some outcome then (1 : ℝ) else 0 := by
  funext source
  simp only [ReferenceSourceCurrentControlFreshness.sourceControlTest,
    sectionCurrentMarkerSet, Set.indicator, Set.mem_ofPred_eq,
    sectionCurrentMarker_restore rate rewards C_star C_h control0 t source]

/-- Original physical-source conditional recording law at every actual later pre-sampler branch. -/
theorem originalLaterBirthOutcome_condExp (outcome : Option (Fin p.K)) :
    ∀ᵐ source ∂sourceInputLaw p, (parametersAt t source).isSome →
      (sourceInputLaw p)[ (fun z => if birthMarker t z = some outcome then (1 : ℝ) else 0) |
        originalPast]
        source = outcomeMass outcome (originalPrefix source) := by
  have hc := ReferenceSourceCurrentControlFreshness.source_control_test_condExp (p := p) control0 t
    (sectionCurrentMarkerSet rate rewards C_star C_h control0 t outcome)
    (sectionCurrentMarkerSet_measurable rate rewards C_star C_h control0 t outcome)
  rw [sourceControlTest_eq_original_marker rate rewards C_star C_h control0 t outcome] at hc
  filter_upwards [hc] with z hz
  intro hpresent
  obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hpresent
  have hpp := (calendarParameters_factor rate rewards C_star C_h control0 t z).symm.trans hp
  rw [sourcePrefixFiltration_eq_currentControlField, hz,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  exact laterBirthOutcome_section_integral rate rewards C_star C_h control0 t
    (originalPrefix z) outcome theta hpp

private theorem record_of_parameters (source : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (hp : parametersAt t source = some theta) :
    ∃ r, actualRecord rate rewards C_star C_h t source = some r ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta := by
  exact Option.bind_eq_some_iff.mp hp

/-- Actual selected and pre-sampler anchors agree for EVERY vector and remainder. -/
theorem currentParameters_anchor (source : SourceInput p) (v : AssignmentVector p)
    (w : ControlRemainder p) : ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t source = some theta →
      ∀ view started, currentParameters
          rate rewards C_star C_h control0 t source v w = some (view, started) →
        view.payload.anchor = theta.2 := by
  intro theta hp view started hpair
  have hp' := (ReferenceOriginalCalendarLaterBirthRemainderRecorder.calendarParameters_currentSource
    rate rewards C_star C_h control0 t source v w).trans hp
  obtain ⟨r, hr, hpr⟩ := record_of_parameters rate rewards C_star C_h t _ theta hp'
  have hs : r.output.preparation.coordinator.selection.map (fun x => (x.view, x.started)) =
      some (view, started) := by
    simpa only [currentParameters, hr, Option.bind_some] using hpair
  obtain ⟨selected, hselected, heq⟩ := Option.map_eq_some_iff.mp hs
  have hv := congrArg (fun x => x.1.payload.anchor) heq
  exact hv.symm.trans (ReferenceFirstCollectionCurrentRecordedCell.selected_anchor
    rate r theta hpr selected hselected)

/-- The prescribed arm-or-bottom mass at the actual pre-sampler anchor. -/
def parameterOutcomeMass (theta : AssignmentParameterFibreKernel.Theta p)
    (outcome : Option (Fin p.K)) : ℝ :=
  match outcome with
  | none => 1 - ∑ a, CanonicalRecordingRates.xi p rate.eta.val theta.2 a
  | some a => CanonicalRecordingRates.xi p rate.eta.val theta.2 a

/-- The actual anchor identity factors the prefix rate from vector success. -/
theorem laterBirthOutcomeCoefficient_eq_presence_mul_parameter (source : SourceInput p) (v : AssignmentVector p)
    (outcome : Option (Fin p.K)) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t source = some theta →
      laterBirthOutcomeCoefficient rate rewards C_star C_h control0 t source v outcome =
        presentIndicator ((selectedSection source v
          (controlAssignmentSplitEquiv p control0).2).isSome) *
        parameterOutcomeMass rate theta outcome := by
  intro theta hp
  cases hpair : selectedSection source v (controlAssignmentSplitEquiv p control0).2 with
  | none => simp only [laterBirthOutcomeCoefficient, hpair, Option.isSome_none,
      presentIndicator, Bool.false_eq_true, ite_false, zero_mul]
  | some q =>
      have ha := currentParameters_anchor rate rewards C_star C_h control0 t source v
        _ theta hp q.1 q.2 hpair
      have hrates : q.1.payload.rate = CanonicalRecordingRates.xi p rate.eta.val theta.2 := by
        funext a
        rw [q.1.payload.rate_eq_canonical, ha]
      cases outcome <;>
        simp only [laterBirthOutcomeCoefficient, hpair, Option.isSome_some, presentIndicator,
          ite_true, one_mul, viewOutcomeMass, parameterOutcomeMass, hrates]

/-- The vector integral is `alpha` times the actual prefix arm/bottom mass. -/
theorem laterBirthOutcomeMassAtPrefix_eq_presence_mul (source : SourceInput p) (outcome : Option (Fin p.K)) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t source = some theta →
      outcomeMass outcome source = birthMassAtPrefix control0 t source *
          parameterOutcomeMass rate theta outcome := by
  intro theta hp
  unfold laterBirthOutcomeMassAtPrefix
  simp_rw [laterBirthOutcomeCoefficient_eq_presence_mul_parameter
    rate rewards C_star C_h control0 t source _ outcome theta hp]
  exact integral_mul_const _ _

/-- The actual pre-sampler branch; successful selection is a later event. -/
def preSamplerSet : Set (SourceInput p) := {source | (parametersAt t source).isSome}
local notation "callEvent" => preSamplerSet rate rewards C_star C_h t

theorem preSamplerSet_measurable : MeasurableSet[sourcePrefixFiltration
      control0 (t.val + 1)] (callEvent) :=
  measurableSet_eq_fun ((measurable_option_isSome _).comp (calendarParameters_measurable
      rate rewards C_star C_h control0 t)) measurable_const

/-- On an actual later call, the nominal raw integer arrival is exactly the original physical arm test times the actual, predictable floor amplitude. -/
theorem originalLaterBirthRaw_factor (a : Fin p.K) (source : SourceInput p) : source ∈ callEvent →
    rawAt t a source = (if birthMarker t source = some (some a) then (1 : ℝ) else 0) *
      amplitudeAt t a source := by
  intro hsource
  obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hsource
  obtain ⟨r, hr, hpr⟩ := record_of_parameters rate rewards C_star C_h t source theta hp
  unfold currentRaw currentCell
  rw [hr, Option.bind_some]
  unfold sourceLaterMarker
  rw [hr, Option.bind_some]
  cases hc : laterLiveReadout (physicalStart rate source rewards C_star C_h) r with
  | none => simp only [Option.map_none, reduceCtorEq, ite_false, zero_mul]
  | some c =>
      obtain ⟨_he, selected, hs, hreward, hrate, _hfloor⟩ := laterLiveReadout_numerical _ r c hc
      have ha := ReferenceFirstCollectionCurrentRecordedCell.selected_anchor rate r theta hpr selected hs
      have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h t source r hr).2.2.1
      have hrw := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h t source r hr).2.2.2
      have hca : c.rate a = CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
        rw [hrate, selected.view.payload.rate_eq_canonical, ha]
      have hcr : c.reward a = ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ) := by
        rw [hreward, hrw, ht]
      unfold currentAmplitude
      rw [hp]
      dsimp only
      by_cases hmark : c.recordedArm = some a
      · rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
          _ c a hmark, hca, hcr]
        simp only [Option.map_some, hmark, ite_true, one_mul]
      · rw [RecordedRoundMoments.normalizedQuantizedArrival,
          RecordedQueueRun.quantizedArrival_eq_zero _ c a hmark]
        simp only [Nat.cast_zero, zero_div, Option.map_some, Option.some.injEq,
          hmark, ite_false, zero_mul]

private theorem gridReward_mem (a : Fin p.K) :
    ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · positivity
  · apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
    exact_mod_cast Nat.le_of_lt_succ (rewards t a).isLt

/-- The actual prefix amplitude is uniformly bounded even off a successful birth. -/
theorem currentAmplitude_bounds (a : Fin p.K) (source : SourceInput p) :
    0 ≤ amplitudeAt t a source ∧ currentAmplitude rate rewards C_star C_h t a source ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  unfold currentAmplitude
  cases hp : parametersAt t source with
  | none => exact ⟨le_refl _, one_div_nonneg.mpr
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le⟩
  | some theta =>
      exact ⟨QuantizedRecordingMoments.quantizedValue_nonneg _ _ _ _ rate.eta.property,
        QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le _ _ _ _ _
          (ConstructorDimensions.D_pos p) rate.eta.property
          (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a)
          (gridReward_mem rewards t a)
          (CanonicalRecordingRates.beta_pos p rate.eta.property)
          (CanonicalRecordingRates.beta_le_xi p rate.eta.property theta.2 a)⟩

/-- Original-source first conditional raw moment on the actual pre-sampler branch, retaining the vector-averaged birth coefficient. -/
private theorem weighted_outcome_condExp (outcome : Option (Fin p.K)) (f : SourceInput p → ℝ) (bound : ℝ)
    (hf : Measurable[originalPast] f) (hb : ∀ z, ‖f z‖ ≤ bound) :
    Integrable ((callEvent).indicator (fun z => f z *
      (if birthMarker t z = some outcome then 1 else 0)))
      (sourceInputLaw p) ∧
    (sourceInputLaw p)[ (callEvent).indicator (fun z => f z *
        (if birthMarker t z = some outcome then 1 else 0)) |
      originalPast] =ᵐ[
      sourceInputLaw p]
      (callEvent).indicator (fun z => f z * outcomeMass outcome (originalPrefix z)) := by
  let μ := sourceInputLaw p
  let F := originalPast
  let : MeasurableSpace (SourceInput p) := sourceInputMeasurableSpace p
  let E := callEvent
  let test := fun z => if birthMarker t z = some outcome then (1 : ℝ) else 0
  have hE : MeasurableSet[F] E := preSamplerSet_measurable rate rewards C_star C_h control0 t
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have ht : Measurable test := Measurable.ite
    (measurableSet_eq_fun (sourceLaterMarker_measurable rate rewards C_star C_h t) measurable_const)
    measurable_const measurable_const
  have htb (z) : ‖test z‖ ≤ 1 := by dsimp only [test]; split_ifs <;> norm_num
  have hti : Integrable test μ := integrable_measurable_norm_le_one _ ht htb
  have hp : Integrable (fun z => E.indicator f z * test z) μ := by
    apply (integrable_const bound).mono'
      (((hf.indicator hE).mono hle le_rfl).mul ht).aestronglyMeasurable
    filter_upwards [] with z
    change ‖E.indicator f z * test z‖ ≤ bound
    calc
      _ ≤ ‖E.indicator f z‖ * 1 := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (htb z) (norm_nonneg _)
      _ ≤ bound := by
        rw [mul_one]
        exact (norm_indicator_le_norm_self f z).trans (hb z)
  have heq : E.indicator (fun z => f z * test z) = fun z => E.indicator f z * test z :=
    funext (fun z => Set.indicator_mul_left E f test (i := z))
  constructor
  · rw [heq]
    exact hp
  rw [heq]
  have hpull := condExp_mul_of_stronglyMeasurable_left (hf.indicator hE).stronglyMeasurable hp hti
  filter_upwards [hpull, originalLaterBirthOutcome_condExp rate rewards C_star C_h
    control0 t outcome] with z hpz hcz
  change μ[E.indicator f * test | F] z = _
  rw [hpz]
  change E.indicator f z * μ[test | F] z = E.indicator (fun z => f z *
    outcomeMass outcome (originalPrefix z)) z
  by_cases hz : z ∈ E
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hcz hz]
  · simp only [Set.indicator_of_notMem hz, zero_mul]

private theorem finite_outcomes_condExp (f : Option (Fin p.K) → SourceInput p → ℝ) (bound : ℝ)
    (hf : ∀ o, Measurable[sourcePrefixFiltration
      control0 (t.val + 1)] (f o)) (hb : ∀ o z, ‖f o z‖ ≤ bound) :
    Integrable ((callEvent).indicator (fun z =>
      ∑ o, f o z * (if birthMarker t z = some o then 1 else 0)))
      (sourceInputLaw p) ∧
    (sourceInputLaw p)[ (callEvent).indicator (fun z =>
        ∑ o, f o z * (if birthMarker t z = some o then 1 else 0)) |
      originalPast] =ᵐ[
      sourceInputLaw p]
      (callEvent).indicator (fun z => ∑ o, f o z * outcomeMass o (originalPrefix z)) := by
  let E := callEvent
  let g := fun o => E.indicator (fun z => f o z * (if birthMarker t z = some o then 1 else 0))
  have hg := fun o => weighted_outcome_condExp rate rewards C_star C_h control0 t o
    (f o) bound (hf o) (hb o)
  have hs := condExp_finsetSum (s := Finset.univ) (f := g) (fun o _ => (hg o).1) (originalPast)
  have hall := (ae_all_iff).mpr (fun o => (hg o).2)
  have heq : E.indicator (fun z => ∑ o, f o z *
      (if birthMarker t z = some o then 1 else 0)) = ∑ o, g o := by
    funext z
    by_cases hz : z ∈ E <;> dsimp only [E] at hz <;> simp [g, E, Set.indicator, hz]
  constructor
  · rw [heq]
    exact integrable_finsetSum' _ (fun o _ => (hg o).1)
  rw [heq]
  filter_upwards [hs, hall] with z hsz haz
  rw [hsz]
  simp only [Finset.sum_apply]
  change (∑ o, (sourceInputLaw p)[g o | originalPast] z) = _
  simp_rw [show ∀ o, (sourceInputLaw p)[g o | originalPast] z =
    E.indicator (fun z => f o z * outcomeMass o (originalPrefix z)) z from haz]
  by_cases hz : z ∈ E <;> dsimp only [E] at hz <;> simp [E, Set.indicator, hz]

private theorem marker_basis_sum (f : Option (Fin p.K) → ℝ) (marker : Option (Option (Fin p.K))) :
    (∑ o, f o * (if marker = some o then 1 else 0)) = marker.elim 0 f := by
  cases marker <;> simp

theorem originalLaterBirthRaw_condExp (a : Fin p.K) :
    (sourceInputLaw p)[ (callEvent).indicator (rawAt t a) | originalPast] =ᵐ[ sourceInputLaw p]
      (callEvent).indicator (fun z => amplitudeAt t a z *
        outcomeMass (some a) (originalPrefix z)) := by
  have heq : (callEvent).indicator (rawAt t a) = (callEvent).indicator (fun z => amplitudeAt t a z *
        (if birthMarker t z = some (some a) then 1 else 0)) := by
    apply Set.indicator_congr
    intro z hz
    rw [originalLaterBirthRaw_factor rate rewards C_star C_h t a z hz, mul_comm]
  rw [heq]
  exact (weighted_outcome_condExp rate rewards C_star C_h control0 t (some a) _
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
    (currentAmplitude_measurable rate rewards C_star C_h control0 t t a)
    (fun z => by rw [Real.norm_of_nonneg (currentAmplitude_bounds rate rewards C_star C_h t a z).1]
                 exact (currentAmplitude_bounds rate rewards C_star C_h t a z).2)).2

/-- The original-source square moment uses the SAME integer-arrival amplitude. -/
theorem originalLaterBirthRaw_sq_condExp (a : Fin p.K) :
    (sourceInputLaw p)[ (callEvent).indicator (fun z => (rawAt t a z) ^ 2) |
      originalPast] =ᵐ[
      sourceInputLaw p]
      (callEvent).indicator (fun z => (amplitudeAt t a z) ^ 2 *
        outcomeMass (some a) (originalPrefix z)) := by
  have heq : (callEvent).indicator (fun z => (rawAt t a z) ^ 2) = (callEvent).indicator (fun z =>
        (amplitudeAt t a z) ^ 2 * (if birthMarker t z = some (some a) then 1 else 0)) := by
    apply Set.indicator_congr
    intro z hz
    dsimp only
    rw [originalLaterBirthRaw_factor rate rewards C_star C_h t a z hz]
    split_ifs <;> ring
  rw [heq]
  exact (weighted_outcome_condExp rate rewards C_star C_h control0 t (some a) _
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    ((currentAmplitude_measurable rate rewards C_star C_h control0 t t a).pow_const 2)
    (fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (currentAmplitude_bounds rate rewards C_star C_h t a z).1
        (currentAmplitude_bounds rate rewards C_star C_h t a z).2 2)).2

private theorem actualRecord_index (z : SourceInput p) (r : RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    ∃ k : Fin (completeSuffixRecords rate z rewards C_star C_h).length,
      (completeSuffixRecords rate z rewards C_star C_h).get k = r ∧
      physicalStart rate z rewards C_star C_h + k.val = t.val := by
  unfold actualRecord at hr
  split_ifs at hr with hs
  obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.mp hr
  refine ⟨⟨_, hk⟩, hget, ?_⟩
  exact Nat.add_sub_of_le hs

/-- Actual arbitrary-birth physical marker, unique owner, original feedback, integer arrival, and saved unoccupied-follower contribution. -/
theorem originalLaterBirth_physical (z : SourceInput p) : z ∈ callEvent → (birthMarker t z).isSome →
    ∃ (r : RoundRecord (p := p) (rate := rate)) (cell : ActualLiveSourceCell r),
      actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.time = t ∧ r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧ r.input.rewards = rewards ∧
      physicalStart rate z rewards C_star C_h < cell.selected.view.payload.sigma.val ∧
      currentCell rate rewards C_star C_h t z = some cell.input ∧
      birthMarker t z = some cell.input.recordedArm ∧
      cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
        r cell.selected.view.payload true ∧
      (∀ arm, cell.input.recordedArm = some arm → ∃ owner : Fin p.m,
        SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner arm ∧
        (∀ other, SnapshotRecordingKernel.owns p (.live cell.selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other arm → other = owner) ∧
        r.output.preparation.arms.actions owner = arm ∧ r.gridFeedback owner = rewards t arm ∧
        (r.output.ownEntries owner).2.val.val = ((rewards t arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ∧
      (∀ arm, quantizedArrival (queueParameters rate)
          cell.input arm = if cell.input.recordedArm = some arm then
            Nat.floor ((rate.n : ℝ) * (((rewards t arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)) /
              cell.selected.view.payload.rate arm) else 0) ∧
      (∀ i, (cell.states i).status = .unoccupied) ∧
      (∀ i,
        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
          r cell.selected.view.payload i = quantizedArrival (queueParameters rate) cell.input
              (cell.selected.view.payload.assignment.assigned i)) := by
  intro hz hm
  obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hz
  obtain ⟨r, hr, hpr⟩ := record_of_parameters rate rewards C_star C_h t z theta hp
  have hsome : (laterLiveReadout (physicalStart rate z rewards C_star C_h) r).isSome := by
    simpa only [sourceLaterMarker, hr, Option.bind_some, Option.isSome_map] using hm
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨k, hk, _hdate⟩ := actualRecord_index rate rewards C_star C_h t z r hr
  have hphysical := laterLiveReadout_physical rate rewards C_star C_h z k c (by rw [hk]; exact hc)
  dsimp only at hphysical
  rw [hk] at hphysical
  obtain ⟨cell, hcell, _he, _hl, _hen, hrows, hj, hrewards, hmarker, _hd,
    howner, _hg, hsaved, _hlog, _hrec, hcollection⟩ := hphysical
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by rw [r.output_eq]; rfl
  have hchosen := ReferenceFirstCollectionCurrentRemainderLaw.selected_laterChosen rate r.input theta hpr
    cell.selected (by rw [← hprep]; exact cell.selection_actual)
  have hunoccupied : ∀ i, (cell.states i).status = .unoccupied := by
    rw [hprep] at hcollection
    unfold ReferenceCollectionPhaseHistory.laterChosen at hchosen
    split at hchosen <;> simp_all only [Bool.false_eq_true]
    intro i
    trivial
  have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z r hr).2.2.1
  obtain ⟨selected, _ho, hs, hstrict, _hlive, _hcell⟩ := laterLiveReadout_some _ r c hc
  have hselected : cell.selected = selected := Option.some.inj (cell.selection_actual.symm.trans hs)
  refine ⟨r, cell, hr, ht, hrows, hj, hrewards, ?_, ?_, ?_, ?_, ?_, ?_, hunoccupied, ?_⟩
  · rw [hselected]
    exact hstrict
  · simp only [currentCell, hr, Option.bind_some, hc, hcell]
  · simp only [sourceLaterMarker, hr, Option.bind_some, hc, Option.map_some, hcell]
  · rw [hcell]
    exact hmarker
  · simpa only [hcell, ht] using howner
  · intro arm
    simpa only [← cell.recordedArm_eq, hrewards, ht] using cell.quantizedArrival_eq arm
  · intro i
    simpa only [hcell] using hsaved i (hunoccupied i)

/-- Actual later-birth recurrence on the SAME initialized prefix; the first overflow update is retained. -/
theorem originalLaterBirth_prefix_energy_step (source : SourceInput p) : source ∈ callEvent →
    (birthMarker t source).isSome →
    ∃ (P : List (RoundInput p.K)) (c : RoundInput p.K), prefixAt t.val source = some P ∧
      prefixAt (t.val + 1) source = some (P ++ [c]) ∧
      currentCell rate rewards C_star C_h t source = some c ∧ c.enabled = true ∧
      (source ∈ H rate rewards C_star C_h t ↔
        (RecordedQueueRun.run (queueParameters rate) P).overflow = false) ∧
      ∀ a : Fin p.K, source ∈ H rate rewards C_star C_h t →
        let Q := queueParameters rate
        let beta := CanonicalRecordingRates.beta p rate.eta.val
        let before := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q P) a
        let after := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (P ++ [c])) a
        let raw := rawAt t a source
        after = max (before + raw - 4) 0 ∧ Real.exp (beta * after) ≤
            1 + Real.exp (beta * before) * Real.exp (beta * (raw - 4)) := by
  intro hsource hmarker
  obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hsource
  obtain ⟨r, hr, hpr⟩ := record_of_parameters rate rewards C_star C_h t source theta hp
  have hreadSome : (laterLiveReadout (physicalStart rate source rewards C_star C_h) r).isSome := by
    simpa only [sourceLaterMarker, hr, Option.bind_some, Option.isSome_map] using hmarker
  obtain ⟨c, hread⟩ := Option.isSome_iff_exists.mp hreadSome
  obtain ⟨selected, ho, hs, hbase, hlive, hcell⟩ := laterLiveReadout_some _ r c hread
  have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true :=
    ReferenceFirstCollectionCurrentRemainderLaw.selected_laterChosen rate r.input theta hpr selected
      (by rw [r.output_eq] at hs; exact hs)
  have hzero : laterLiveReadout 0 r = some c := by
    have hz : 0 < selected.view.payload.sigma.val := by omega
    unfold laterLiveReadout
    simp only [hs, hz, hlive, and_self, ite_true, dite_eq_left ho]
    exact congrArg some hcell.symm
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c := by
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hzero]
    rfl
  have hc : currentCell rate rewards C_star C_h t source = some c := by
    simp only [currentCell, hr, Option.bind_some, hread]
  have he := (laterLiveReadout_numerical _ r c hread).1
  obtain ⟨k, hget, hdate⟩ := actualRecord_index rate rewards C_star C_h t source r hr
  have hkchosen : ReferenceCollectionPhaseHistory.laterChosen (completeSuffixRecords
        rate source rewards C_star C_h)[k.val].input = true := by
    change ReferenceCollectionPhaseHistory.laterChosen ((completeSuffixRecords
        rate source rewards C_star C_h).get k).input = true
    rw [hget]
    exact hchosen
  obtain ⟨P, hPlen, _hmap, hprefix⟩ :=
    ReferenceCompleteInstallationPrefixPresence.internal_complete_later_installation_prefix_inputs
      rate rewards C_star C_h source k hkchosen
  have hlookup : (completeSuffixRecords rate source rewards C_star C_h)[k.val]? = some r :=
    List.getElem?_eq_some_iff.mpr ⟨k.isLt, hget⟩
  have hpre : prefixAt t.val source = some P := by
    have h := hprefix k.val (Nat.le_refl _)
    rw [hdate, ← hPlen, List.take_length] at h
    exact h
  have hlookup' : (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
      rate rewards C_star C_h source)[t.val - ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
        rate rewards C_star C_h source]? = some r := by
    have hoff : t.val - physicalStart rate source rewards C_star C_h = k.val := by omega
    simpa only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart, hoff] using hlookup
  have hpost := prefixInputs_append_one
    rate rewards C_star C_h t.val source P hpre r c hlookup' hcell0
  have hpast : pastCells? rate rewards C_star C_h t source = some P := by
    rw [← prefixInputs_eq_pastCells]
    exact hpre
  have hret : source ∈ H rate rewards C_star C_h t ↔
      (RecordedQueueRun.run (queueParameters rate) P).overflow = false := by
    simp only [H, Set.mem_ofPred_eq, prefixReadout?,
      hpast, Option.map_some, Option.some.injEq, stateReadout, exists_eq_left']
  refine ⟨P, c, hpre, hpost, hc, he, hret, ?_⟩
  intro a ha
  dsimp only
  have hrun : RecordedQueueRun.run (queueParameters rate) (P ++ [c]) =
      RecordedQueueRun.step (queueParameters rate)
        (RecordedQueueRun.run (queueParameters rate) P) c := by
    rw [RecordedQueueRun.run, CanonicalQueueProcess.execute_append]
    rfl
  have hrec := CanonicalQueueProcess.normalizedBacklog_step_of_retained
    (queueParameters rate) _ c a (hret.mp ha) he
  rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
    _ _ c a he (hret.mp ha)] at hrec
  have hraw : currentRaw
      rate rewards C_star C_h t a source = RecordedRoundMoments.normalizedQuantizedArrival
        (queueParameters rate) c a := by
    simp only [currentRaw, hc]
  refine ⟨by rw [hrun, hrec, hraw], ?_⟩
  rw [hrun, hrec, ← hraw]
  simpa only [add_sub_assoc] using CanonicalQueueProcess.exp_mul_max_le
    (StoppedQueueBound.normalizedBacklog (queueParameters rate)
      (RecordedQueueRun.run (queueParameters rate) P) a)
    (rawAt t a source - 4)
    (CanonicalRecordingRates.beta p rate.eta.val)

/-- The literal one-arm floor amplitude of an actual selected payload. -/
def viewRawValue (view : ChoiceTimeView p rate.eta)
    (a : Fin p.K) (outcome : Option (Fin p.K)) : ℝ :=
  if outcome = some a then QuantizedRecordingMoments.quantizedValue
    (ConstructorDimensions.D p) rate.eta.val (view.payload.rate a)
    (((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) else 0

/-- Exact finite exponential coefficient, with outer absence assigned zero mass and the actual payload kept inside the whole-vector integral. -/
def laterBirthExponentialCoefficient (source : SourceInput p) (v : AssignmentVector p) (a : Fin p.K) : ℝ :=
  match selectedSection source v (controlAssignmentSplitEquiv p control0).2 with
  | none => 0
  | some (view, _) =>
      ∫ outcome, Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (viewRawValue rate rewards t view a outcome - 4))
        ∂(RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
            rate.sourceCap view.payload.anchor view.payload.anchor_pos)).toMeasure
local notation "mgfCoefficient" => laterBirthExponentialCoefficient rate rewards C_star C_h
local notation "mgfAtPrefix" => mgfCoefficient control0 t

/-- The genuine remainder integral of the original raw estimate, gated by actual birth presence, is its finite recording-law exponential coefficient. -/
theorem laterBirthExponential_remainder_integral (source : SourceInput p) (v : AssignmentVector p) (a : Fin p.K) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t source = some theta →
      (∫ w : ControlRemainder p, if (currentMarker
          rate rewards C_star C_h control0 t source v w).isSome then
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            (rawAt t a (currentSource control0 t source v w) - 4))
        else 0 ∂controlRemainderLaw p) =
      mgfAtPrefix source v a := by
  intro theta hp
  let marker := currentMarker rate rewards C_star C_h control0 t source v
  have hm := ReferenceOriginalCalendarLaterBirthRemainderRecorder.currentRemainder_laterMarker_measurable
    rate rewards C_star C_h control0 t source v theta hp
  have hlaw := ReferenceOriginalCalendarLaterBirthRemainderRecorder.currentRemainder_laterBirth_optionalMarker_law
    rate rewards C_star C_h control0 t source v theta hp
  cases hpair : selectedSection source v (controlAssignmentSplitEquiv p control0).2 with
  | none =>
      have hnone (w) : marker w = none :=
        currentMarker_none_of_parameters_none rate rewards C_star C_h control0 t source v w
          ((ReferenceOriginalCalendarLaterBirthRemainderRecorder.currentRemainder_laterParameters_factor
            rate rewards C_star C_h control0 t source theta hp v w).2.2.1.trans hpair)
      change (∫ w, if (marker w).isSome then _ else 0 ∂_) = _
      simp only [hnone, Option.isSome_none, Bool.false_eq_true, ite_false, integral_zero,
        laterBirthExponentialCoefficient, hpair]
  | some q =>
      let g : Option (Option (Fin p.K)) → ℝ :=
        ReferenceCollectionOutcomeMeasurability.optionalElim 0 (fun outcome =>
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            (viewRawValue rate rewards t q.1 a outcome - 4)))
      have hg : Measurable g := measurable_of_countable _
      obtain ⟨valid, hpoint⟩ :=
        ReferenceOriginalCalendarLaterBirthRemainderRecorder.currentRemainder_laterBirth_marker_on_present
          rate rewards C_star C_h control0 t source theta hp v q.1 q.2 hpair
      have ha := currentParameters_anchor rate rewards C_star C_h control0 t source v
        _ theta hp q.1 q.2 hpair
      have heq (w) : (if (marker w).isSome then
          Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
            (rawAt t a (currentSource control0 t source v w) - 4))
          else 0) = g (marker w) := by
        have hpw := (ReferenceOriginalCalendarLaterBirthRemainderRecorder.calendarParameters_currentSource
          rate rewards C_star C_h control0 t source v w).trans hp
        have hraw := originalLaterBirthRaw_factor rate rewards C_star C_h t a
          (currentSource control0 t source v w)
          (by change (parametersAt t _).isSome = true; rw [hpw]; rfl)
        have hmk := (hpoint w).1
        change marker w = some _ at hmk
        change rawAt t a (currentSource control0 t source v w) =
          (if marker w = some (some a) then 1 else 0) * _ at hraw
        rw [hraw, hmk]
        simp only [Option.isSome_some, ite_true, g,
          ReferenceCollectionOutcomeMeasurability.optionalElim,
          currentAmplitude, hpw]
        rw [← ha]
        unfold viewRawValue
        rw [q.1.payload.rate_eq_canonical]
        split_ifs <;> simp_all [queueParameters]
      calc
        _ = ∫ w, g (marker w) ∂controlRemainderLaw p :=
          integral_congr_ae (Filter.Eventually.of_forall heq)
        _ = ∫ m, g m ∂(controlRemainderLaw p).map marker :=
          (integral_map hm.aemeasurable hg.aestronglyMeasurable).symm
        _ = mgfAtPrefix source v a := by
          rw [hlaw, hpair, integral_map (measurable_of_countable _).aemeasurable hg.aestronglyMeasurable,
            laterBirthExponentialCoefficient, hpair]
          rfl

/-- The accepted finite MGF bound applies to nominal raw arrivals; queues are not restarted. -/
theorem laterBirthExponentialCoefficient_le_presence (source : SourceInput p) (v : AssignmentVector p) (a : Fin p.K) :
    mgfAtPrefix source v a ≤ presentIndicator ((selectedSection source v
        (controlAssignmentSplitEquiv p control0).2).isSome) := by
  unfold laterBirthExponentialCoefficient
  cases selectedSection source v (controlAssignmentSplitEquiv p control0).2 with
  | none => simp only [Option.isSome_none, presentIndicator, Bool.false_eq_true, ite_false, le_refl]
  | some q =>
      simp only [Option.isSome_some, presentIndicator, ite_true]
      have h := RecordedRoundMoments.rawEstimate_exponentialMoment_le_one
        (queueParameters rate) (RecordedQueueRun.initialState p.K)
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
          rate.sourceCap q.1.payload.anchor q.1.payload.anchor_pos)
        (fun a => ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ))
        (gridReward_mem rewards t) a rfl (CanonicalRecordingRates.beta p rate.eta.val)
        (CanonicalRecordingRates.beta_pos p rate.eta.property) (q.1.payload.beta_le_rate a)
      convert h using 1
      apply integral_congr_ae
      filter_upwards [] with outcome
      rw [RecordedRoundMoments.rawEstimate_eq_quantizedValue_of_enabled _ _ _ _ _ outcome a rfl]
      rfl

/-- The actual predictable floor amplitude supplies each finite marker weight. -/
def exponentialWeight (a : Fin p.K) (o : Option (Fin p.K)) (z : SourceInput p) : ℝ :=
  Real.exp (CanonicalRecordingRates.beta p rate.eta.val * ((if o = some a then currentAmplitude
      rate rewards C_star C_h t a z else 0) - 4))

private theorem exponentialWeight_measurable (a : Fin p.K) (o : Option (Fin p.K)) :
    Measurable[sourcePrefixFiltration control0
      (t.val + 1)] (exponentialWeight rate rewards C_star C_h t a o) := by
  unfold exponentialWeight
  by_cases ho : o = some a
  · simp only [ho, ite_true]
    exact (measurable_const.mul ((currentAmplitude_measurable
      rate rewards C_star C_h control0 t t a).sub measurable_const)).exp
  · simp only [ho, ite_false]
    exact measurable_const

private theorem exponentialWeight_bound (a : Fin p.K) (o : Option (Fin p.K)) (z : SourceInput p) :
    ‖exponentialWeight rate rewards C_star C_h t a o z‖ ≤ Real.exp 1 := by
  unfold exponentialWeight
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have hb := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hraw : (if o = some a then currentAmplitude
      rate rewards C_star C_h t a z else 0) ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
    split_ifs
    · exact (currentAmplitude_bounds rate rewards C_star C_h t a z).2
    · exact one_div_nonneg.mpr hb.le
  calc
    _ ≤ CanonicalRecordingRates.beta p rate.eta.val *
        (1 / CanonicalRecordingRates.beta p rate.eta.val) :=
      mul_le_mul_of_nonneg_left (by linarith only [hraw]) hb.le
    _ = 1 := mul_one_div_cancel (ne_of_gt hb)

/-- Original-source birth MGF, with zero contribution at outer absence. -/
def originalLaterBirthExponential (a : Fin p.K) (z : SourceInput p) : ℝ :=
  (callEvent).indicator (fun z =>
    if (birthMarker t z).isSome then Real.exp (CanonicalRecordingRates.beta p rate.eta.val *
        (rawAt t a z - 4))
    else 0) z

private theorem originalLaterBirthExponential_basis (a : Fin p.K) :
    originalLaterBirthExponential rate rewards C_star C_h t a = (callEvent).indicator (fun z =>
        ∑ o, exponentialWeight rate rewards C_star C_h t a o z *
          (if birthMarker t z = some o then 1 else 0)) := by
  apply Set.indicator_congr
  intro z hz
  dsimp only
  rw [marker_basis_sum]
  cases hm : birthMarker t z with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Option.elim_none]
  | some o =>
      rw [originalLaterBirthRaw_factor rate rewards C_star C_h t a z hz]
      simp only [hm, Option.isSome_some, ite_true, Option.elim_some,
        Option.some.injEq, exponentialWeight]
      split_ifs <;> simp only [one_mul, zero_mul]

/-- The literal vector coefficient simplifies only after actual parameter identity; the original success mass remains as its indicator. -/
theorem laterBirthExponentialCoefficient_eq_presence_sum (z : SourceInput p) (v : AssignmentVector p) (a : Fin p.K) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, calendarParameters
        rate rewards C_star C_h t z = some theta →
      mgfAtPrefix z v a = presentIndicator ((selectedSection z v
          (controlAssignmentSplitEquiv p control0).2).isSome) *
        ∑ o, exponentialWeight rate rewards C_star C_h t a o z * parameterOutcomeMass rate theta o := by
  intro theta hp
  unfold laterBirthExponentialCoefficient
  cases hpair : selectedSection z v (controlAssignmentSplitEquiv p control0).2 with
  | none => simp only [Option.isSome_none, presentIndicator, Bool.false_eq_true, ite_false, zero_mul]
  | some q =>
      simp only [Option.isSome_some, presentIndicator, ite_true, one_mul]
      have ha := currentParameters_anchor rate rewards C_star C_h control0 t z v _ theta hp q.1 q.2 hpair
      let rates := SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
        rate.sourceCap q.1.payload.anchor q.1.payload.anchor_pos
      have hrates : rates.rate = CanonicalRecordingRates.xi p rate.eta.val theta.2 := by
        dsimp only [rates, SnapshotRecordingKernel.recordingRates]
        rw [ha]
      have hmass (o : Option (Fin p.K)) :
          ((RecordedRoundMoments.recordingOutcomePMF rates) o).toReal = parameterOutcomeMass rate theta o := by
        rw [recording_pmf_mass]
        cases o <;> simp only [Option.elim_none, Option.elim_some, parameterOutcomeMass, hrates]
      rw [PMF.integral_eq_sum]
      apply Finset.sum_congr rfl
      intro o _
      rw [smul_eq_mul, hmass]
      have hv : viewRawValue rate rewards t q.1 a o = if o = some a then currentAmplitude
            rate rewards C_star C_h t a z else 0 := by
        unfold viewRawValue currentAmplitude
        rw [hp, q.1.payload.rate_eq_canonical, ha]
        rfl
      rw [hv]
      exact mul_comm _ _

/-- The genuine vector average retains its birth mass alpha. -/
theorem laterBirthExponential_vector_integral (z : SourceInput p) (a : Fin p.K) :
    ∀ theta : AssignmentParameterFibreKernel.Theta p, parametersAt t z = some theta →
      Integrable (fun v => mgfAtPrefix z v a) (assignmentLaw p.K) ∧
      (∫ v, mgfAtPrefix z v a ∂assignmentLaw p.K) ≤ birthMassAtPrefix control0 t z := by
  intro theta hp
  have hm := (laterBirthPresenceIntegrand_measurable rate rewards C_star C_h control0 t).comp
    ((measurable_const (a := z)).prodMk (measurable_id : Measurable (id : AssignmentVector p → _)))
  have hi := integrable_measurable_norm_le_one (μ := assignmentLaw p.K) _ hm
    (laterBirthPresenceIntegrand_norm_le_one rate rewards C_star C_h control0 t z)
  have heq : (fun v => mgfAtPrefix z v a) = fun v => presentIndicator ((selectedSection z v
        (controlAssignmentSplitEquiv p control0).2).isSome) *
        ∑ o, exponentialWeight rate rewards C_star C_h t a o z * parameterOutcomeMass rate theta o := by
    funext v
    exact laterBirthExponentialCoefficient_eq_presence_sum rate rewards C_star C_h control0 t z v a theta hp
  have hci : Integrable (fun v => mgfAtPrefix z v a)
      (assignmentLaw p.K) := by rw [heq]; exact hi.mul_const _
  exact ⟨hci, integral_mono hci hi (fun v =>
    laterBirthExponentialCoefficient_le_presence rate rewards C_star C_h control0 t z v a)⟩

private theorem exponential_vector_eq_sum (a : Fin p.K) (z : SourceInput p) (hz : z ∈ callEvent) :
    (∫ v, mgfAtPrefix (originalPrefix z) v a ∂assignmentLaw p.K) =
      ∑ o, exponentialWeight rate rewards C_star C_h t a o z * outcomeMass o
          (originalPrefix z) := by
  obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hz
  let pref := originalPrefix z
  have hpp : parametersAt t pref = some theta :=
    (calendarParameters_factor rate rewards C_star C_h control0 t z).symm.trans hp
  have hw (o) : exponentialWeight rate rewards C_star C_h t a o pref =
      exponentialWeight rate rewards C_star C_h t a o z := by
    unfold exponentialWeight currentAmplitude
    rw [hpp, hp]
  change (∫ v, mgfAtPrefix pref v a ∂assignmentLaw p.K) = ∑ o, _ * outcomeMass o pref
  simp_rw [laterBirthOutcomeMassAtPrefix_eq_presence_mul rate rewards C_star C_h control0 t pref _ theta hpp,
    laterBirthExponentialCoefficient_eq_presence_sum rate rewards C_star C_h control0 t pref _ a theta hpp, hw]
  rw [integral_mul_const]
  change birthMassAtPrefix control0 t pref * _ = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem originalLaterBirthExponential_condExp (a : Fin p.K) :
    Integrable (originalLaterBirthExponential rate rewards C_star C_h t a) (sourceInputLaw p) ∧
    (sourceInputLaw p)[originalLaterBirthExponential rate rewards C_star C_h t a |
      originalPast] =ᵐ[sourceInputLaw p]
      (callEvent).indicator (fun z =>
        ∫ v, mgfAtPrefix (originalPrefix z) v a ∂assignmentLaw p.K) := by
  rw [originalLaterBirthExponential_basis]
  have hc := finite_outcomes_condExp rate rewards C_star C_h control0 t
    (exponentialWeight rate rewards C_star C_h t a) (Real.exp 1)
    (exponentialWeight_measurable rate rewards C_star C_h control0 t a)
    (exponentialWeight_bound rate rewards C_star C_h t a)
  refine ⟨hc.1, ?_⟩
  exact hc.2.trans (Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ callEvent
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        exponential_vector_eq_sum rate rewards C_star C_h control0 t a z hz]
    · simp only [Set.indicator_of_notMem hz])

private theorem outcome_mass_sum (z : SourceInput p) (hz : z ∈ callEvent) : (∑ o, outcomeMass o
      (originalPrefix z)) = birthMass control0 t z := by
  obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hz
  have hpp := (calendarParameters_factor rate rewards C_star C_h control0 t z).symm.trans hp
  simp_rw [laterBirthOutcomeMassAtPrefix_eq_presence_mul rate rewards C_star C_h control0 t _ _ theta hpp]
  rw [← Finset.mul_sum, Fintype.sum_option]
  simp only [parameterOutcomeMass]
  rw [sub_add_cancel, mul_one]
  rfl

/-- The actual successful-birth indicator has conditional mass alpha on the original source. -/
theorem originalLaterBirthPresence_condExp : (sourceInputLaw p)[(callEvent).indicator
      (fun z => presentIndicator (birthMarker t z).isSome) |
      originalPast] =ᵐ[sourceInputLaw p]
      (callEvent).indicator (birthMass control0 t) := by
  have hc := finite_outcomes_condExp rate rewards C_star C_h control0 t
    (fun _ _ => 1) 1 (fun _ => measurable_const) (fun _ _ => by norm_num)
  have heq : (callEvent).indicator (fun z => presentIndicator (birthMarker t z).isSome) =
      (callEvent).indicator (fun z => ∑ o,
        (1 : ℝ) * (if birthMarker t z = some o then 1 else 0)) := by
    apply Set.indicator_congr
    intro z _
    dsimp only
    rw [marker_basis_sum]
    cases birthMarker t z <;> rfl
  rw [heq]
  exact hc.2.trans (Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ callEvent
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      simpa only [one_mul] using outcome_mass_sum rate rewards C_star C_h control0 t z hz
    · simp only [Set.indicator_of_notMem hz])

open ReferenceFirstCollectionCurrentQueueReadout (QueueReadout before? after?
  normalizedReadoutBacklog)

/-- Literal energy of the accepted optional queue-register observation. -/
def readoutEnergy (a : Fin p.K) (v : Option (QueueReadout p.K)) : ℝ :=
  Real.exp (CanonicalRecordingRates.beta p rate.eta.val * normalizedReadoutBacklog rate v a)

def incomingEnergy (a : Fin p.K) (z : SourceInput p) : ℝ :=
  readoutEnergy rate a (before? rate rewards C_star C_h t z)

/-- The SAME stopped prefix after its actual current birth update. -/
def laterBirthRetainedEnergy (a : Fin p.K) (z : SourceInput p) : ℝ :=
  (callEvent ∩ H rate rewards C_star C_h t).indicator (fun z => if (birthMarker t z).isSome then
      readoutEnergy rate a (after? rate rewards C_star C_h t z) else 0) z

section Energy
variable (a : Fin p.K)
local notation "μ" => sourceInputLaw p
local notation "F" => originalPast
local notation "E" => callEvent
local notation "R" => H rate rewards C_star C_h t
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Q" => queueParameters rate
local notation "alpha" => birthMass control0 t
local notation "incoming" => incomingEnergy rate rewards C_star C_h t a
local notation "mgf" => fun z => ∫ v, mgfCoefficient
  control0 t (originalPrefix z) v a ∂assignmentLaw p.K
local notation "capEnergy" => Real.exp (beta * (1 / (32 * rate.eta.val)))

private theorem incomingEnergy_measurable : Measurable[F] incoming :=
  (measurable_of_countable (readoutEnergy rate a)).comp
    (ReferenceFirstCollectionCurrentQueueReadout.before?_measurable rate rewards C_star C_h control0 t)

private theorem incomingEnergy_bound (z : SourceInput p) (hz : z ∈ R) : incoming z ≤ capEnergy := by
  obtain ⟨v, hv, hfalse⟩ := hz
  cases hP : pastCells? rate rewards C_star C_h t z with
  | none => simp only [prefixReadout?, hP, Option.map_none, reduceCtorEq] at hv
  | some P =>
      simp only [prefixReadout?, hP, Option.map_some, Option.some.injEq] at hv
      subst v
      have hb := StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
        Q P P.length a (by simpa only [List.take_length, stateReadout] using hfalse)
      rw [List.take_length] at hb
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (CanonicalRecordingRates.beta_pos p rate.eta.property).le
      simpa only [incomingEnergy, readoutEnergy, before?, prefixReadout?, hP, Option.map_some,
        normalizedReadoutBacklog, stateReadout, StoppedQueueBound.normalizedBacklog, queueParameters] using hb

private def energyWeight (o : Option (Fin p.K)) (z : SourceInput p) : ℝ :=
  (R).indicator (fun z => 1 + incoming z * exponentialWeight rate rewards C_star C_h t a o z) z

private theorem energyWeight_measurable (o : Option (Fin p.K)) :
    Measurable[F] (energyWeight rate rewards C_star C_h t a o) :=
  (measurable_const.add ((incomingEnergy_measurable rate rewards C_star C_h control0 t a).mul
    (exponentialWeight_measurable rate rewards C_star C_h control0 t a o))).indicator
      (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H rate rewards C_star C_h control0 t)

private theorem energyWeight_bound (o : Option (Fin p.K)) (z : SourceInput p) :
    ‖energyWeight rate rewards C_star C_h t a o z‖ ≤ 1 + capEnergy * Real.exp 1 := by
  unfold energyWeight
  by_cases hz : z ∈ R
  · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (by unfold incomingEnergy readoutEnergy exponentialWeight; positivity)]
    apply add_le_add le_rfl
    exact mul_le_mul (incomingEnergy_bound rate rewards C_star C_h t a z hz)
      (by simpa only [exponentialWeight, Real.norm_of_nonneg (Real.exp_nonneg _)] using
        exponentialWeight_bound rate rewards C_star C_h t a o z)
      (Real.exp_nonneg _) (Real.exp_nonneg _)
  · rw [Set.indicator_of_notMem hz, norm_zero]
    positivity

private theorem energy_pointwise (z : SourceInput p) :
    laterBirthRetainedEnergy rate rewards C_star C_h t a z ≤
      (E).indicator (fun z => ∑ o, energyWeight rate rewards C_star C_h t a o z *
        (if birthMarker t z = some o then 1 else 0)) z := by
  by_cases he : z ∈ E
  swap
  · simp only [laterBirthRetainedEnergy, Set.indicator_of_notMem he,
      Set.indicator_of_notMem (fun h : z ∈ E ∩ R => he h.1), le_refl]
  by_cases hr : z ∈ R
  swap
  · simp only [laterBirthRetainedEnergy, Set.indicator_of_notMem (fun h : z ∈ E ∩ R => hr h.2),
      Set.indicator_of_mem he, energyWeight, Set.indicator_of_notMem hr, zero_mul,
      Finset.sum_const_zero, le_refl]
  rw [laterBirthRetainedEnergy, Set.indicator_of_mem (show z ∈ E ∩ R from ⟨he, hr⟩),
    Set.indicator_of_mem he, marker_basis_sum]
  cases hm : birthMarker t z with
  | none => simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Option.elim_none, le_refl]
  | some o =>
      obtain ⟨P, c, hpre, _hpost, hc, _hen, _hret, hstep⟩ :=
        originalLaterBirth_prefix_energy_step rate rewards C_star C_h t z he (by rw [hm]; rfl)
      have hP : pastCells? rate rewards C_star C_h t z = some P :=
        (prefixInputs_eq_pastCells rate rewards C_star C_h t z).symm.trans hpre
      have hbefore : before? rate rewards C_star C_h t z = some (stateReadout (RecordedQueueRun.run Q P)) := by
        simp only [before?, prefixReadout?, hP, Option.map_some]
      have hafter : after? rate rewards C_star C_h t z =
          some (stateReadout (RecordedQueueRun.run Q (P ++ [c]))) := by
        simp only [after?, hP, hc, Option.bind_some, Option.map_some]
        simp only [RecordedQueueRun.run, CanonicalQueueProcess.execute_append, RecordedQueueRun.execute]
      have hw : exponentialWeight rate rewards C_star C_h t a o z =
          Real.exp (beta * (rawAt t a z - 4)) := by
        rw [originalLaterBirthRaw_factor rate rewards C_star C_h t a z he]
        simp only [hm, Option.some.injEq, exponentialWeight]
        split_ifs <;> simp only [one_mul, zero_mul]
      simpa only [Option.isSome_some, ite_true, Option.elim_some, energyWeight,
        Set.indicator_of_mem hr, incomingEnergy, hbefore, hafter, readoutEnergy,
        normalizedReadoutBacklog, stateReadout, StoppedQueueBound.normalizedBacklog, hw] using (hstep a hr).2

private theorem energy_candidate : (E).indicator (fun z => ∑ o,
      energyWeight rate rewards C_star C_h t a o z * laterBirthOutcomeMassAtPrefix
        rate rewards C_star C_h control0 t o (originalPrefix z)) =
    (E ∩ R).indicator (fun z => alpha z + incoming z * mgf z) := by
  funext z
  by_cases he : z ∈ E
  swap
  · simp only [Set.indicator_of_notMem he, Set.indicator_of_notMem (fun h : z ∈ E ∩ R => he h.1)]
  by_cases hr : z ∈ R
  swap
  · simp only [Set.indicator_of_mem he, energyWeight, Set.indicator_of_notMem hr, zero_mul,
      Finset.sum_const_zero, Set.indicator_of_notMem (fun h : z ∈ E ∩ R => hr h.2)]
  rw [Set.indicator_of_mem he, Set.indicator_of_mem (show z ∈ E ∩ R from ⟨he, hr⟩)]
  dsimp only
  rw [exponential_vector_eq_sum rate rewards C_star C_h control0 t a z he]
  simp_rw [energyWeight, Set.indicator_of_mem hr, add_mul, one_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, outcome_mass_sum rate rewards C_star C_h control0 t z he]

/-- Original conditional first and second integer-arrival moments, with the actual success mass and the quantized rounding error. -/
theorem originalLaterBirth_moments : ∀ᵐ z ∂μ, ∀ theta : AssignmentParameterFibreKernel.Theta p,
      parametersAt t z = some theta →
      let xi := CanonicalRecordingRates.xi p rate.eta.val theta.2 a
      let reward := ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ)
      let first := μ[(E).indicator (rawAt t a) | F] z
      let second := μ[(E).indicator (fun z => (rawAt t a z) ^ 2) | F] z
      first = alpha z * xi * amplitudeAt t a z ∧
      second = alpha z * xi * (amplitudeAt t a z) ^ 2 ∧
      alpha z * (reward - xi / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) ≤ first ∧
      first ≤ alpha z * reward ∧ second ≤ alpha z * (reward ^ 2 / xi) := by
  filter_upwards [originalLaterBirthRaw_condExp rate rewards C_star C_h control0 t a,
    originalLaterBirthRaw_sq_condExp rate rewards C_star C_h control0 t a] with z hfirst hsecond
  intro theta hp
  have hz : z ∈ E := by change (parametersAt t z).isSome = true; rw [hp]; rfl
  have hpp := (calendarParameters_factor rate rewards C_star C_h control0 t z).symm.trans hp
  rw [Set.indicator_of_mem hz, laterBirthOutcomeMassAtPrefix_eq_presence_mul
    rate rewards C_star C_h control0 t _ (some a) theta hpp] at hfirst hsecond
  simp only [parameterOutcomeMass] at hfirst hsecond
  dsimp only
  rw [hfirst, hsecond]
  change _ = alpha z * _ * _ ∧ _ = alpha z * _ * _ ∧ _
  have hnonneg := (laterBirthPresenceMassAtPrefix_bounds rate rewards C_star C_h control0 t
    (originalPrefix z)).1
  have hl := QuantizedRecordingMoments.quantizedValue_roundingError (ConstructorDimensions.D p)
    rate.eta.val (CanonicalRecordingRates.xi p rate.eta.val theta.2 a) _ (ConstructorDimensions.D_pos p)
    rate.eta.property (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a) (gridReward_mem rewards t a)
  have hu := QuantizedRecordingMoments.quantizedValue_firstMoment_le (ConstructorDimensions.D p)
    rate.eta.val (CanonicalRecordingRates.xi p rate.eta.val theta.2 a) _ (ConstructorDimensions.D_pos p)
    rate.eta.property (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a) (gridReward_mem rewards t a)
  have hs := QuantizedRecordingMoments.quantizedValue_secondMoment_le (ConstructorDimensions.D p)
    rate.eta.val (CanonicalRecordingRates.xi p rate.eta.val theta.2 a) _ (ConstructorDimensions.D_pos p)
    rate.eta.property (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a) (gridReward_mem rewards t a)
  dsimp only [laterBirthPresenceMass]
  refine ⟨by ring, by ring, ?_, ?_, ?_⟩
  all_goals unfold currentAmplitude; rw [hp]; dsimp only [queueParameters]
  · convert mul_le_mul_of_nonneg_left hl hnonneg using 1
    ring
  · convert mul_le_mul_of_nonneg_left hu hnonneg using 1
    ring
  · convert mul_le_mul_of_nonneg_left hs hnonneg using 1
    ring

/-- Original-mu conditional and integrated birth-energy estimates for the SAME optional prefix. -/
theorem originalLaterBirth_retained_energy :
    Integrable (laterBirthRetainedEnergy rate rewards C_star C_h t a) μ ∧
    (∀ᵐ z ∂μ, μ[laterBirthRetainedEnergy rate rewards C_star C_h t a | F] z ≤
      (E ∩ R).indicator (fun z => alpha z + incoming z * mgf z) z ∧
      μ[laterBirthRetainedEnergy rate rewards C_star C_h t a | F] z ≤
        (E ∩ R).indicator (fun z => incoming z + alpha z) z) ∧
    (∫ z, laterBirthRetainedEnergy rate rewards C_star C_h t a z ∂μ) ≤
      ∫ z, (E ∩ R).indicator (fun z => alpha z + incoming z * mgf z) z ∂μ := by
  let : MeasurableSpace (SourceInput p) := sourceInputMeasurableSpace p
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hE := preSamplerSet_measurable rate rewards C_star C_h control0 t
  have hR := ReferenceFirstCollectionCurrentRetainedGate.measurableSet_H rate rewards C_star C_h control0 t
  have hfinite := finite_outcomes_condExp rate rewards C_star C_h control0 t
    (energyWeight rate rewards C_star C_h t a) (1 + capEnergy * Real.exp 1)
    (energyWeight_measurable rate rewards C_star C_h control0 t a)
    (energyWeight_bound rate rewards C_star C_h t a)
  let upper := (E).indicator (fun z => ∑ o, energyWeight rate rewards C_star C_h t a o z *
    (if birthMarker t z = some o then 1 else 0))
  have hnonneg (z) : 0 ≤ laterBirthRetainedEnergy rate rewards C_star C_h t a z := by
    unfold laterBirthRetainedEnergy readoutEnergy
    by_cases hz : z ∈ E ∩ R
    · rw [Set.indicator_of_mem hz]
      split_ifs <;> positivity
    · rw [Set.indicator_of_notMem hz]
  have hmeas : Measurable (laterBirthRetainedEnergy rate rewards C_star C_h t a) := by
    have ha := (measurable_of_countable (readoutEnergy rate a)).comp
      (ReferenceFirstCollectionCurrentQueueReadout.after?_measurable rate rewards C_star C_h control0 t)
    exact (Measurable.ite (measurableSet_eq_fun
      ((measurable_of_countable Option.isSome).comp (sourceLaterMarker_measurable rate rewards C_star C_h t))
      measurable_const) ha measurable_const).indicator ((hle _ hE).inter (hle _ hR))
  have hi : Integrable (laterBirthRetainedEnergy rate rewards C_star C_h t a) μ :=
    hfinite.1.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hnonneg z)]
      exact energy_pointwise rate rewards C_star C_h t a z)
  have hce : μ[upper | F] =ᵐ[μ] (E ∩ R).indicator (fun z => alpha z + incoming z * mgf z) := by
    simpa only [energy_candidate rate rewards C_star C_h control0 t a] using hfinite.2
  have hc := (condExp_mono (m := F) hi hfinite.1
    (Filter.Eventually.of_forall (energy_pointwise rate rewards C_star C_h t a))).trans_eq hce
  have hsimp : ∀ z, (E ∩ R).indicator (fun z => alpha z + incoming z * mgf z) z ≤
      (E ∩ R).indicator (fun z => incoming z + alpha z) z := by
    intro z
    by_cases hz : z ∈ E ∩ R
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      obtain ⟨theta, hp⟩ := Option.isSome_iff_exists.mp hz.1
      have hpp := (calendarParameters_factor rate rewards C_star C_h control0 t z).symm.trans hp
      have hv := (laterBirthExponential_vector_integral rate rewards C_star C_h control0 t
        (originalPrefix z) a theta hpp).2
      have hb := (laterBirthPresenceMassAtPrefix_bounds rate rewards C_star C_h control0 t
        (originalPrefix z)).2
      have hin : 0 ≤ incoming z := Real.exp_nonneg _
      have hmul := mul_le_mul_of_nonneg_left (hv.trans hb) hin
      linarith only [hmul]
    · simp only [Set.indicator_of_notMem hz, le_refl]
  refine ⟨hi, ?_, ?_⟩
  · filter_upwards [hc] with z hz
    exact ⟨hz, hz.trans (hsimp z)⟩
  · rw [← integral_condExp hle]
    exact integral_mono_ae integrable_condExp (integrable_condExp.congr hce) hc
end Energy

end Bandits.Support.ReferenceOriginalCalendarLaterBirthSourceRetainedEnergyStep

end
