/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData

import Mathlib.Tactic

/-!
# Actual post-rawK sentinel section and signed release cost

The definitions in this module observe the original supported release record
and its retained selection. Off the accepted stopped-date support, each
observation is zero. The conditional law is taken on the original source
prefix filtration.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseAdaptation
open Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReleaseRoundKernel
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw

variable {p : ConstructorDimensions.Parameters}

/-- The canonical fast-arm mass at an actual selected live release choice. -/
def selectedFastArmMass
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (j : CanonicalFastSampling.FastArm selected.view.payload.slowSet) : ℝ :=
  CanonicalFastSampling.qGamma p rate.eta rate.eta.property
    selected.view.payload.eta_le_source_cap
    selected.view.payload.anchor
    (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
    selected.view.payload.anchor_pos
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
      selected (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
      selected (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
      selected (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
    selected.view.payload.slowSet j

/-- The selected payload's literal auxiliary arm in its actual complement. -/
def selectedAuxiliaryFastArm
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x) :
    CanonicalFastSampling.FastArm selected.view.payload.slowSet :=
  ReleaseRoundKernel.auxiliaryFastArm selected.view.payload.assignment
    selected.view.payload.slowSet
    (by simpa [ReleaseRoundKernel.assignedImage] using
      selected.view.payload.assignment_image.symm)

/-- The supported total observation `qGamma_current(e) * chi_t(e)`, read from
the actual stopped release record. It is zero outside that literal support. -/
def postRawKReleaseOmega
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z then
    match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => 0
    | some r =>
      match r.output.preparation.coordinator.selection with
      | none => 0
      | some selected =>
        let e := selectedAuxiliaryFastArm rate selected
        selectedFastArmMass rate selected e *
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) e.1
  else 0

/-- The literal physical fast-arm sentinel charge on a genuine stopped date.
The option branches are off support by the admitted actual-record readout. -/
def postRawKReleaseSentinelObservation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z then
    match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => 0
    | some r =>
      match r.output.preparation.coordinator.selection with
      | none => 0
      | some selected =>
        let e := selectedAuxiliaryFastArm rate selected
        if selected.arm = e ∧
            (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
              rate rewards C_star C_h t z).Nonempty then
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val e.1
        else 0
  else 0

/-- The actual stopped signed physical deficit, using the record's stored slow
set, selected fast arm, and all actual player entries. -/
def postRawKStoppedSignedReleaseDeficit
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z then
    match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => 0
    | some r =>
      match r.output.preparation.coordinator.selection with
      | none => 0
      | some selected =>
        ReleaseRoundKernel.slowReward
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            selected.view.payload.slowSet +
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val selected.arm -
          (∑ player : Fin p.m, ((r.ownEntries player).2).val.val)
  else 0

/-- The canonical fast-arm masses sum to one, so each supported omega lies in
the unit interval; off support it is exactly zero. -/
theorem postRawKReleaseOmega_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ postRawKReleaseOmega rate rewards C_star C_h t z ∧
      postRawKReleaseOmega rate rewards C_star C_h t z ≤ 1 := by
  classical
  unfold postRawKReleaseOmega
  split
  · cases ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => norm_num
    | some r =>
      cases hselection : r.output.preparation.coordinator.selection with
      | none => simp only [hselection]; norm_num
      | some selected =>
        simp only [hselection]
        let e := selectedAuxiliaryFastArm rate selected
        have hn (j) : 0 ≤ selectedFastArmMass rate selected j :=
          CanonicalFastSampling.qGamma_nonneg p rate.eta.property
            selected.view.payload.eta_le_source_cap selected.view.payload.anchor
            (completeCurrentWeights selected) selected.view.payload.anchor_pos
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) _ j
        have hsum : ∑ j, selectedFastArmMass rate selected j = 1 :=
          CanonicalFastSampling.qGamma_sum_eq_one p rate.eta.property
            selected.view.payload.eta_le_source_cap selected.view.payload.anchor
            (completeCurrentWeights selected) selected.view.payload.anchor_pos
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
            (fun a => (completeCurrentWeights_bounds selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2) _
        have hle : selectedFastArmMass rate selected e ≤ 1 := by
          rw [← hsum]
          exact Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ e)
        have hc : 0 ≤ chi (wholeGridRewardRow rewards t) e.val ∧
            chi (wholeGridRewardRow rewards t) e.val ≤ 1 := by
          unfold chi
          split_ifs <;> norm_num
        exact ⟨mul_nonneg (hn e) hc.1,
          (mul_le_mul_of_nonneg_right hle hc.1).trans (by simpa only [one_mul] using hc.2)⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The supported sentinel observation is a literal reward indicator and is
bounded by one on every original source. -/
theorem postRawKReleaseSentinelObservation_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ postRawKReleaseSentinelObservation rate rewards C_star C_h t z ∧
      postRawKReleaseSentinelObservation rate rewards C_star C_h t z ≤ 1 := by
  classical
  by_cases hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z
  · unfold postRawKReleaseSentinelObservation
    simp only [hkeep]
    cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
    | none => simp
    | some r =>
      cases hselection : r.output.preparation.coordinator.selection with
      | none => simp [hselection]
      | some selected =>
        simp only [hselection]
        by_cases hcharge : selected.arm = (selectedAuxiliaryFastArm rate selected).1 ∧
            (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
              rate rewards C_star C_h t z).Nonempty
        · simpa [hcharge] using
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).property
              (selectedAuxiliaryFastArm rate selected).1
        · simp [hcharge]
  · simp [postRawKReleaseSentinelObservation, hkeep]

/-- The signed cost is bounded pathwise by the stopped DATA coefficients and
the actual supported fast-arm sentinel charge. -/
theorem postRawKStoppedSignedReleaseDeficit_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t z ≤
      (∑ i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
        rate rewards C_star C_h t z,
        stoppedAssignedChi rate rewards C_star C_h t i z) +
      postRawKReleaseSentinelObservation rate rewards C_star C_h t z := by
  classical
  by_cases hkeep : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
      rate rewards C_star C_h t z
  · obtain ⟨r, hr, hrecord, _htime, hread⟩ := stoppedDate_record_readouts
      rate rewards C_star C_h control0 t z hkeep
    obtain ⟨r', selected, hrecord', hselection', hpayload, _hweights,
      _hminimum, _hreplace⟩ := stoppedDate_actualWeights_replace_current
        rate rewards C_star C_h control0 t z hkeep
    have hrr : r = r' := Option.some.inj (hrecord.symm.trans hrecord')
    subst r'
    obtain ⟨selected0, _registers, _owned, _base, _states, _memories, _hstate,
      _hregisterPayload, _hemptyRegisters, hselectionGeometry, _hempty, _hlive,
      _hchoices, _hstatus, _hfast, _hup, _hdata, hcost⟩ :=
      rawReleaseRecord_actualGeometry rate rewards C_star C_h z r hr
    have hselectedSame : selected0 = selected :=
      Option.some.inj (hselectionGeometry.symm.trans hselection')
    subst selected0
    have hselected := hselection'
    have hP : ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r =
        ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
          rate rewards C_star C_h t z := by
      exact (hread selected.view.payload hpayload).2.symm
    have hsum :
        (∑ i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
          rate rewards C_star C_h t z,
          stoppedAssignedChi rate rewards C_star C_h t i z) =
        (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) := by
      rw [← hP]
      apply Finset.sum_congr rfl
      intro i hi
      have hiStopped : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
          rate rewards C_star C_h t z := by
        rw [← hP]
        exact hi
      obtain ⟨M, hM, hchi⟩ := stoppedAssignedChi_eq_actual
        rate rewards C_star C_h control0 t i z hiStopped
      have hM' : M = selected.view.payload := by
        have hleft : incomingStoredPayload rate rewards C_star C_h t z = some (some M) := hM
        have hright : incomingStoredPayload rate rewards C_star C_h t z =
            some (some selected.view.payload) := hpayload
        exact Option.some.inj (Option.some.inj (hleft.symm.trans hright))
      subst M
      exact hchi
    have hsent : postRawKReleaseSentinelObservation rate rewards C_star C_h t z =
        (if selected.arm =
          selectedAuxiliaryFastArm rate selected ∧
          (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
            (selectedAuxiliaryFastArm rate selected).1
        else 0) := by
      simp [postRawKReleaseSentinelObservation, hkeep, hrecord, hselected, hP]
    have haux : (selectedAuxiliaryFastArm rate selected).1 =
        selected.view.payload.assignment.auxiliary := by rfl
    unfold postRawKStoppedSignedReleaseDeficit
    simp only [hkeep, ite_true, hrecord, hselected]
    rw [hsum, hsent]
    rw [haux]
    rw [_htime] at hcost
    exact hcost
  · simp [postRawKStoppedSignedReleaseDeficit, postRawKReleaseSentinelObservation,
      ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet,
      hkeep]


/-- The live branch of the accepted lossless incoming state schema. This is
an observation; absent and nonlive states retain the absent option tag. -/
def incomingLiveData
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) :=
  (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).bind
    fun code => match code.1 with
    | .inr (.inl live) => some live
    | _ => none

/-- The whole current weight vector, read literally from the incoming live
payload and its stored score coordinates, including the anchor on slow arms. -/
def liveDataWeights (rate : ReferenceActivePhysicalStep.RateInput p)
    (v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) (a : Fin p.K) : ℝ :=
  if a ∈ v.1.slowSet.val then v.1.anchor a else
    ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (v.2.scores a)

/-- The literal auxiliary mass formula on the incoming live coordinates. -/
def liveDataAuxiliaryMass (rate : ReferenceActivePhysicalStep.RateInput p)
    (v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : ℝ :=
  ReferenceLiveRecorderJointMeasurability.qGammaFormula
    (p := p) (rate := rate) v.1.slowSet.val
    (v.1.anchor, liveDataWeights rate v) v.1.assignment.auxiliary

private theorem measurable_liveDataWeights
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (liveDataWeights rate) := by
  have hobs := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp
      (measurable_fst : Measurable (Prod.fst :
        ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  have hslow := hobs.snd.snd.fst
  have hanchor := AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_fst : Measurable (Prod.fst :
      ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  apply measurable_pi_iff.mpr
  intro a
  exact ((measurable_pi_apply a).comp hanchor).ite
    ((measurableSet_mem_finset a).preimage hslow)
    ((measurable_of_countable (fun d : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (d.scores a))).comp measurable_snd)

private theorem measurable_countable_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

private theorem measurable_liveDataAuxiliaryMass
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (liveDataAuxiliaryMass rate) := by
  have hobs := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp
      (measurable_fst : Measurable (Prod.fst :
        ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  have haux := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
    (measurable_fst : Measurable (Prod.fst :
      ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  have hvalue := (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_fst : Measurable (Prod.fst :
      ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))).prodMk
          (measurable_liveDataWeights rate)
  have hkey : Measurable (fun v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      (v.1.slowSet.val, v.1.assignment.auxiliary)) := hobs.snd.snd.fst.prodMk haux
  exact measurable_countable_cases _ hkey
    (fun c v => ReferenceLiveRecorderJointMeasurability.qGammaFormula
      (p := p) (rate := rate) c.1 (v.1.anchor, liveDataWeights rate v) c.2)
    (fun c => (ReferenceLiveRecorderJointMeasurability.measurable_qGammaFormula
      (p := p) (rate := rate) c.1 c.2).comp hvalue)

private theorem incomingLiveData_measurable_preChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (incomingLiveData rate rewards C_star C_h t) := by
  have hbranch : Measurable (fun code : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
      match code.1 with
      | .inr (.inl live) => some live
      | _ => none) := by
    have hsome : Measurable (some :
        ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → Option _) := by
      apply measurable_comap_iff.mpr
      exact measurable_inl
    have hsum := (Measurable.sumElim (measurable_const (a := (none : Option
        (ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p))))
      (Measurable.sumElim hsome (measurable_const (a := (none : Option
        (ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)))))).comp
        (measurable_fst : Measurable (Prod.fst :
          ReferenceActivePhysicalStepMeasurability.StateCode p rate → _))
    convert hsum using 1
    funext code
    dsimp only [Function.comp_def]
    rcases code.1 with a | b
    · rfl
    · cases b <;> rfl
  have hopt := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (none : Option (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)) _ hbranch
  convert hopt.comp (ReferenceSourcePrefixHistoryFiltration.incoming_measurable
    rate rewards C_star C_h control0 t) using 1
  funext z
  dsimp only [Function.comp_def, incomingLiveData]
  cases ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z <;> rfl

private theorem selectionAt_payload_weights
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (M : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm M.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection M started time weights x.row)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hs : ReferenceActivePhysicalStep.selectionAt x M started time weights arm = some selected) :
    selected.view.payload = M ∧ HEq selected.view.complementWeights weights := by
  unfold ReferenceActivePhysicalStep.selectionAt at hs
  split at hs
  · cases hs
    exact ⟨rfl, HEq.rfl⟩
  · cases hs

private theorem live_selected_payload_weights
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live registers owned base)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected) :
    selected.view.payload = registers.payload ∧
      HEq selected.view.complementWeights registers.complementWeights := by
  let liveInput := ReferenceActivePhysicalStep.liveInput x registers owned base
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live registers owned base (CoordinatorRoundDispatch.dispatchLive liveInput) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have hs : (ReferenceActivePhysicalStep.DispatchCut.live registers owned base
      (CoordinatorRoundDispatch.dispatchLive liveInput)).selection = some selected := by
    simpa only [ReferenceActivePhysicalStep.prepare, hdispatch] using hselected
  cases hout : CoordinatorRoundDispatch.dispatchLive liveInput with
  | clockFailure failure hfailure =>
      simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs
  | initializerFailure dispatched hstart checked hchecked =>
      simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs
  | localFailure dispatched hstart reason =>
      simp only [hout, ReferenceActivePhysicalStep.DispatchCut.selection, reduceCtorEq] at hs
  | continuingChosen dispatched hstart continuation arm =>
      exact selectionAt_payload_weights x registers.payload dispatched.startResult x.time
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights arm selected
        (by simpa only [hout, ReferenceActivePhysicalStep.DispatchCut.selection] using hs)
  | cutoffChosen dispatched hstart ledger hinitial hledger hvalid hclock hpending hnone arm =>
      exact selectionAt_payload_weights x registers.payload dispatched.startResult x.time
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights arm selected
        (by simpa only [hout, ReferenceActivePhysicalStep.DispatchCut.selection] using hs)

private theorem liveDataWeights_encodeLive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) :
    liveDataWeights rate (registers.payload,
      ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base) =
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        registers.payload registers.complementWeights := by
  funext a
  unfold liveDataWeights ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
  split_ifs with ha
  · rfl
  · have hf : a ∈ CanonicalFastSampling.fastArmFinset registers.payload.slowSet :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩
    simp only [ReferenceActivePhysicalStepMeasurability.encodeLive,
      ReferenceActivePhysicalStepMeasurability.extendComplement, dite_eq_left hf]
    rfl

/-- On every genuine stopped date, the incoming live code gives the actual
whole payload and exactly the full current weights of the actual selection. -/
theorem stoppedDate_incomingLiveData
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hkeep : postRawKStoppedDate rate rewards C_star C_h t z) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input)
      (d : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      incomingLiveData rate rewards C_star C_h t z = some (selected.view.payload, d) ∧
      liveDataWeights rate (selected.view.payload, d) = completeCurrentWeights selected ∧
      r.input.time = t := by
  obtain ⟨r, hr, ha, ht, _⟩ := stoppedDate_record_readouts
    rate rewards C_star C_h control0 t z hkeep
  obtain ⟨selected, registers, owned, base, _states, _memories, hstate,
    _hp, _hempty, hselected, _⟩ := rawReleaseRecord_actualGeometry
      rate rewards C_star C_h z r hr
  have hs : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = some selected := by
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselected
  obtain ⟨hM, hw⟩ := live_selected_payload_weights r.input registers owned base hstate selected hs
  refine ⟨r, selected, ReferenceActivePhysicalStepMeasurability.encodeLive registers owned base,
    ha, hselected, ?_, ?_, ht⟩
  · simp only [incomingLiveData, ReferenceSourcePrefixHistoryFiltration.incoming, ha,
      Option.map_some, Option.bind_some, ReferenceActivePhysicalStepMeasurability.encodeState,
      hstate, ReferenceActivePhysicalStepMeasurability.encodeCoordinator, hM]
  · have hcongr (M N : ReferenceActivePhysicalStep.Payload rate) (h : M = N)
        (v : CanonicalFastSampling.FastArm M.slowSet → ℝ)
        (w : CanonicalFastSampling.FastArm N.slowSet → ℝ) (hv : HEq v w) :
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights M v =
          ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights N w := by
      cases h
      cases hv
      rfl
    rw [hM, liveDataWeights_encodeLive]
    exact (hcongr selected.view.payload registers.payload hM
      selected.view.complementWeights registers.complementWeights hw).symm

private theorem selectedFastArmMass_eq_formula
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x) :
    selectedFastArmMass rate selected (selectedAuxiliaryFastArm rate selected) =
      ReferenceLiveRecorderJointMeasurability.qGammaFormula
        (p := p) (rate := rate) selected.view.payload.slowSet.val
        (selected.view.payload.anchor, completeCurrentWeights selected)
        selected.view.payload.assignment.auxiliary := rfl

/-- The literal supported omega is computed by the incoming Borel payload and
whole-weight readouts, before the current fast-arm choice. -/
theorem postRawKReleaseOmega_eq_incoming
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKReleaseOmega rate rewards C_star C_h t z =
      if postRawKStoppedDate rate rewards C_star C_h t z then
        ReferenceCollectionOutcomeMeasurability.optionalElim 0
          (fun v => liveDataAuxiliaryMass rate v *
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) v.1.assignment.auxiliary)
          (incomingLiveData rate rewards C_star C_h t z)
      else 0 := by
  by_cases hk : postRawKStoppedDate rate rewards C_star C_h t z
  · obtain ⟨r, selected, d, ha, hs, hd, hw, _⟩ := stoppedDate_incomingLiveData
      rate rewards C_star C_h control0 t z hk
    simp only [postRawKReleaseOmega, hk, ite_true, ha, hs, hd,
      ReferenceCollectionOutcomeMeasurability.optionalElim, selectedFastArmMass_eq_formula]
    rw [liveDataAuxiliaryMass, hw]
    rfl
  · simp only [postRawKReleaseOmega, hk, ite_false]

/-- Actual omega predictability uses the analytical source-prefix field. -/
theorem postRawKReleaseOmega_measurable_preChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (postRawKReleaseOmega rate rewards C_star C_h t) := by
  classical
  have haux := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
    (measurable_fst : Measurable (Prod.fst :
      ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  have hchi := (measurable_of_countable
    (ReleaseRoundKernel.chi (wholeGridRewardRow rewards t))).comp haux
  have hv := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ)
    _ ((measurable_liveDataAuxiliaryMass rate).mul hchi)
  have hm : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => if postRawKStoppedDate rate rewards C_star C_h t z then
        ReferenceCollectionOutcomeMeasurability.optionalElim 0
          (fun v => liveDataAuxiliaryMass rate v *
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t) v.1.assignment.auxiliary)
          (incomingLiveData rate rewards C_star C_h t z) else (0 : ℝ)) :=
    (hv.comp (incomingLiveData_measurable_preChoice
      rate rewards C_star C_h control0 t)).ite
        (postRawKStoppedDate_measurable_preRound rate rewards C_star C_h control0 t)
        measurable_const
  convert hm using 1
  funext z
  exact postRawKReleaseOmega_eq_incoming rate rewards C_star C_h control0 t z

/-- Integrability is derived on the original source law from the unit bound. -/
theorem postRawKReleaseOmega_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Integrable (postRawKReleaseOmega rate rewards C_star C_h t) (sourceInputLaw p) := by
  have hm := (postRawKReleaseOmega_measurable_preChoice
    rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1)) le_rfl
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    have hb := postRawKReleaseOmega_bounds rate rewards C_star C_h t z
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2


/-- A discrete label for the actual slow set and its actual auxiliary arm. -/
abbrev FastLabel (p : ConstructorDimensions.Parameters) :=
  {v : CanonicalOrientedSetLaw.SlowSet p.K p.m × Fin p.K //
    v.2 ∈ CanonicalFastSampling.fastArmFinset v.1}

def liveDataFastLabel (rate : ReferenceActivePhysicalStep.RateInput p)
    (v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : FastLabel p :=
  ⟨(v.1.slowSet, v.1.assignment.auxiliary),
    (ReleaseRoundKernel.auxiliaryFastArm v.1.assignment v.1.slowSet
      v.1.assignment_image.symm).property⟩

/-- Cumulative mass endpoints in the canonical sampler's original arm order. -/
def fastIntervalEndpoint (rate : ReferenceActivePhysicalStep.RateInput p)
    (upper : Bool) (label : FastLabel p)
    (value : (Fin p.K → ℝ) × (Fin p.K → ℝ)) : ℝ :=
  let U := label.val.1
  let e : CanonicalFastSampling.FastArm U := ⟨label.val.2, label.property⟩
  let masses := fun k : Fin (p.K - p.m + 1) =>
    ReferenceLiveRecorderJointMeasurability.qGammaFormula
      (p := p) (rate := rate) U.val value (CanonicalFastSampling.fastArmOrderIso U k).val
  if upper then ContinuousCategorical.upper masses ((CanonicalFastSampling.fastArmOrderIso U).symm e)
  else ContinuousCategorical.lower masses ((CanonicalFastSampling.fastArmOrderIso U).symm e)

private theorem measurable_liveDataFastLabel (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (liveDataFastLabel rate) := by
  have hobs := (comap_measurable
    (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp
      (measurable_fst : Measurable (Prod.fst : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  have hslow : Measurable (fun v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => v.1.slowSet) :=
    hobs.snd.snd.fst.subtype_mk
  exact (hslow.prodMk
    (AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
      measurable_fst)).subtype_mk

private theorem measurable_fastIntervalEndpoint
    (rate : ReferenceActivePhysicalStep.RateInput p) (upper : Bool) (label : FastLabel p) :
    Measurable (fastIntervalEndpoint rate upper label) := by
  unfold fastIntervalEndpoint
  cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte,
    ContinuousCategorical.lower, ContinuousCategorical.upper]
  · exact Finset.measurable_fun_sum _ fun k _ =>
      ReferenceLiveRecorderJointMeasurability.measurable_qGammaFormula _ _
  · exact Finset.measurable_fun_sum _ fun k _ =>
      ReferenceLiveRecorderJointMeasurability.measurable_qGammaFormula _ _

private theorem measurable_liveEndpoint
    (rate : ReferenceActivePhysicalStep.RateInput p) (upper : Bool) :
    Measurable (fun v : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      fastIntervalEndpoint rate upper (liveDataFastLabel rate v)
        (v.1.anchor, liveDataWeights rate v)) := by
  have hv := (AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    (measurable_fst : Measurable (Prod.fst : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))).prodMk
        (measurable_liveDataWeights rate)
  exact measurable_countable_cases _ (measurable_liveDataFastLabel rate)
    (fun c v => fastIntervalEndpoint rate upper c (v.1.anchor, liveDataWeights rate v))
    (fun c => (measurable_fastIntervalEndpoint rate upper c).comp hv)

/-- The exact canonical fast scalar interval with positive auxiliary reward.
The other coordinates of the whole current control remain on their source law. -/
def liveSentinelTest (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T)
    (v : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (control : ContinuousLearningRows.TimeControl p) : Bool :=
  decide (0 < (wholeGridRewardRow rewards t).val v.1.assignment.auxiliary ∧
    fastIntervalEndpoint rate false (liveDataFastLabel rate v)
      (v.1.anchor, liveDataWeights rate v) ≤
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1).val ∧
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1).val <
      fastIntervalEndpoint rate true (liveDataFastLabel rate v)
        (v.1.anchor, liveDataWeights rate v))

private theorem measurable_liveSentinelTest
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    Measurable (fun v : (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) × TimeControl p =>
        liveSentinelTest rate rewards t v.1 v.2) := by
  have haux := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
    (measurable_fst.comp (measurable_fst : Measurable (Prod.fst :
      (ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) × TimeControl p → _)))
  have hr := (measurable_of_countable ((wholeGridRewardRow rewards t).val)).comp haux
  have hu : Measurable (fun v : (ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) × TimeControl p =>
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast v.2.1).val) :=
    measurable_subtype_coe.comp
      ((ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast).comp
        (measurable_fst.comp measurable_snd))
  apply measurable_to_bool
  have hm := (measurableSet_lt (measurable_const (a := (0 : ℝ))) hr).inter
    ((measurableSet_le ((measurable_liveEndpoint rate false).comp measurable_fst) hu).inter
      (measurableSet_lt hu ((measurable_liveEndpoint rate true).comp measurable_fst)))
  convert hm using 1
  ext v
  simp only [liveSentinelTest, Set.mem_preimage, Set.mem_singleton_iff,
    decide_eq_true_eq, Set.mem_inter_iff, Set.mem_ofPred_eq, Function.comp_def,
    AssignmentPayloadDerivedMeasurability.inputAuxiliary]

/-- The incoming, supported sentinel test for an arbitrary complete current
control. Absent data is a false observation, without an invented live state. -/
def sentinelControlTest
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (control : TimeControl p) : Bool :=
  decide (postRawKStoppedDate rate rewards C_star C_h t z ∧
    (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty) &&
    ((incomingLiveData rate rewards C_star C_h t z).map
      (fun v => liveSentinelTest rate rewards t v control)).getD false

private theorem pendingNonempty_measurable_preChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      {z | (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} := by
  have heq : {z | (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} =
      ⋃ i : Fin (p.m - 1), {z | i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z} := by
    ext z
    simp only [Finset.Nonempty, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    postRawKStoppedPendingSet_mem_measurable_preRound rate rewards C_star C_h control0 t i

private theorem measurable_sentinelControlTest
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (fun v : BootstrapPrivateRoundStreams.SourceInput p × TimeControl p =>
      sentinelControlTest rate rewards C_star C_h t v.1 v.2) := by
  have hin : Measurable (incomingLiveData rate rewards C_star C_h t) :=
    (incomingLiveData_measurable_preChoice rate rewards C_star C_h control0 t).mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1)) le_rfl
  have htest : @Measurable (BootstrapPrivateRoundStreams.SourceInput p × TimeControl p)
      (Option Bool) inferInstance LaterAssignmentStartMeasurability.optionMeasurableSpace
      (fun v => (incomingLiveData rate rewards C_star C_h t v.1).map
        (fun d => liveSentinelTest rate rewards t d v.2)) :=
    (ReferenceCollectionOutcomeMeasurability.measurable_mapOptional _
      (measurable_liveSentinelTest rate rewards t)).comp
        ((hin.comp measurable_fst).prodMk measurable_snd)
  have hkeep : MeasurableSet {z | postRawKStoppedDate rate rewards C_star C_h t z} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1) _
      (postRawKStoppedDate_measurable_preRound rate rewards C_star C_h control0 t)
  have hp : MeasurableSet {z | (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1) _
      (pendingNonempty_measurable_preChoice rate rewards C_star C_h control0 t)
  have hmask : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      decide (postRawKStoppedDate rate rewards C_star C_h t z ∧
        (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty)) := by
    apply measurable_to_bool
    convert hkeep.inter hp using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
  have hget : @Measurable (Option Bool) Bool
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance
      (fun b => b.getD false) := by
    convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim false id measurable_id using 1
    funext b
    cases b <;> rfl
  unfold sentinelControlTest
  exact (measurable_of_countable (fun b : Bool × Bool => b.1 && b.2)).comp
    ((hmask.comp measurable_fst).prodMk (hget.comp htest))


private theorem actualRecord_input_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

/-- The canonical sampler at the actual selected payload and whole weights. -/
def selectedFastSample (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x) (u : ContinuousCategorical.Scalar) :
    CanonicalFastSampling.FastArm selected.view.payload.slowSet :=
  CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
    selected.view.payload.eta_le_source_cap selected.view.payload.anchor
    (completeCurrentWeights selected) selected.view.payload.anchor_pos
    (fun a => (completeCurrentWeights_bounds selected
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
    (fun a => (completeCurrentWeights_bounds selected
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
    (fun a => (completeCurrentWeights_bounds selected
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
    selected.view.payload.slowSet u

private theorem stoppedDate_fast_eq_sample
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hk : postRawKStoppedDate rate rewards C_star C_h t z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (ha : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    (selectedFastSample rate selected
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        (ReferenceSourceCurrentControlFreshness.u_t p t z).1)).val = selected.arm := by
  obtain ⟨r', hr, ha', _⟩ := stoppedDate_record_readouts
    rate rewards C_star C_h control0 t z hk
  have heq : r' = r := Option.some.inj (ha'.symm.trans ha)
  subst r'
  obtain ⟨selected', _registers, _owned, _base, _states, _memories,
    _hstate, _hp, _he, hs', _hempty, _hlive, _hc, _hst, hfast, _⟩ :=
    rawReleaseRecord_actualGeometry rate rewards C_star C_h z r hr
  have hsel : selected' = selected := Option.some.inj (hs'.symm.trans hs)
  subst selected'
  have hf := actualRecord_input_fields rate rewards C_star C_h t z r ha
  have hcontrol : r.input.row.2 r.input.time = ReferenceSourceCurrentControlFreshness.u_t p t z := by
    simp only [ReferenceActivePhysicalStep.RoundInput.row, hf.1, hf.2.1, hf.2.2.1,
      ReferenceSourceCurrentControlFreshness.u_t]
  change (selectedFastSample rate selected
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
      (r.input.row.2 r.input.time).1)).val = selected.arm at hfast
  rw [hcontrol] at hfast
  exact hfast

private theorem selectedFastSample_aux_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (d : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (hw : liveDataWeights rate (selected.view.payload, d) = completeCurrentWeights selected)
    (u : ContinuousCategorical.Scalar) :
    selectedFastSample rate selected u = selectedAuxiliaryFastArm rate selected ↔
      fastIntervalEndpoint rate false (liveDataFastLabel rate (selected.view.payload, d))
        (selected.view.payload.anchor, liveDataWeights rate (selected.view.payload, d)) ≤ u.val ∧
      u.val < fastIntervalEndpoint rate true (liveDataFastLabel rate (selected.view.payload, d))
        (selected.view.payload.anchor, liveDataWeights rate (selected.view.payload, d)) := by
  rw [hw]
  unfold selectedFastSample CanonicalFastSampling.sampleFast
  rw [← OrderIso.eq_symm_apply]
  exact ContinuousCategorical.sample_eq_iff _
    (fun k => CanonicalFastSampling.qGamma_nonneg p rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (completeCurrentWeights selected) selected.view.payload.anchor_pos
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.1)
      (fun a => (completeCurrentWeights_bounds selected
        (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a).2.2)
      selected.view.payload.slowSet _) _ _ _

/-- Auxiliary reward read from the incoming payload, without choosing a
selection or manufacturing a state on absent branches. -/
def incomingAuxiliaryReward
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ReferenceCollectionOutcomeMeasurability.optionalElim 0
    (fun v => (wholeGridRewardRow rewards t).val v.1.assignment.auxiliary)
    (incomingLiveData rate rewards C_star C_h t z)

private theorem incomingAuxiliaryReward_measurable_preChoice
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (incomingAuxiliaryReward rate rewards C_star C_h t) := by
  have ha := AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
    (measurable_fst : Measurable (Prod.fst : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p → _))
  exact (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ) _
    ((measurable_of_countable ((wholeGridRewardRow rewards t).val)).comp ha)).comp
      (incomingLiveData_measurable_preChoice rate rewards C_star C_h control0 t)

/-- The physical supported sentinel is the incoming reward times the literal
canonical fast-interval test. This includes positive and zero rewards. -/
theorem postRawKReleaseSentinelObservation_eq_test
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKReleaseSentinelObservation rate rewards C_star C_h t z =
      incomingAuxiliaryReward rate rewards C_star C_h t z *
        (if sentinelControlTest rate rewards C_star C_h t z
          (ReferenceSourceCurrentControlFreshness.u_t p t z) then (1 : ℝ) else 0) := by
  classical
  by_cases hk : postRawKStoppedDate rate rewards C_star C_h t z
  · obtain ⟨r, selected, d, ha, hs, hd, hw, _ht⟩ :=
      stoppedDate_incomingLiveData rate rewards C_star C_h control0 t z hk
    have hf := stoppedDate_fast_eq_sample rate rewards C_star C_h control0 t z hk r selected ha hs
    have he : selected.arm = (selectedAuxiliaryFastArm rate selected).val ↔
        selectedFastSample rate selected
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            (ReferenceSourceCurrentControlFreshness.u_t p t z).1) =
          selectedAuxiliaryFastArm rate selected := by
      rw [Subtype.ext_iff, hf]
    rw [selectedFastSample_aux_iff rate selected d hw] at he
    simp only [postRawKReleaseSentinelObservation, hk, ite_true, ha, hs,
      incomingAuxiliaryReward, hd, ReferenceCollectionOutcomeMeasurability.optionalElim,
      sentinelControlTest, liveSentinelTest, Option.map_some, Option.getD_some,
      Bool.and_eq_true, decide_eq_true_eq, true_and, ← he]
    by_cases hp : 0 < (wholeGridRewardRow rewards t).val selected.view.payload.assignment.auxiliary
    · by_cases hc : selected.arm = (selectedAuxiliaryFastArm rate selected).val ∧
          (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
      · simp only [hc.1, hc.2, hp, true_and, ↓reduceIte, mul_one]
        rfl
      · have hnc : ¬ ((postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty ∧
            selected.arm = (selectedAuxiliaryFastArm rate selected).val) := by tauto
        simp only [hc, hnc, hp, true_and, ↓reduceIte, mul_zero]
    · have hz : (wholeGridRewardRow rewards t).val selected.view.payload.assignment.auxiliary = 0 :=
        le_antisymm (le_of_not_gt hp) ((wholeGridRewardRow rewards t).property _).1
      simp only [hp, false_and, and_false, ↓reduceIte, mul_zero]
      split_ifs
      · exact hz
      · rfl
  · simp only [postRawKReleaseSentinelObservation, sentinelControlTest, hk, false_and,
      decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, mul_zero]

/-- Ambient Borel measurability of the actual physical sentinel observation. -/
theorem postRawKReleaseSentinelObservation_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (postRawKReleaseSentinelObservation rate rewards C_star C_h t) := by
  have hr := (incomingAuxiliaryReward_measurable_preChoice rate rewards C_star C_h control0 t).mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1)) le_rfl
  have hb := (measurable_sentinelControlTest rate rewards C_star C_h control0 t).comp
    (measurable_id.prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t t))
  have hi : Measurable (fun z => if sentinelControlTest rate rewards C_star C_h t z
      (ReferenceSourceCurrentControlFreshness.u_t p t z) then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp hb
  convert hr.mul hi using 1
  funext z
  exact postRawKReleaseSentinelObservation_eq_test rate rewards C_star C_h control0 t z

/-- Original-law sentinel integrability follows from its physical unit bound. -/
theorem postRawKReleaseSentinelObservation_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Integrable (postRawKReleaseSentinelObservation rate rewards C_star C_h t) (sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (postRawKReleaseSentinelObservation_measurable rate rewards C_star C_h control0 t).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    have hb := postRawKReleaseSentinelObservation_bounds rate rewards C_star C_h t z
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2


private theorem preChoice_event_prefix
    (control0 : TimeControl p) (t : Fin p.T)
    (A : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hA : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] A)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    z ∈ A ↔ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈ A := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hA
  obtain ⟨B, _hB, hfactor⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [← hfactor]
  change _ ∈ B ↔ _ ∈ B
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
    t.val t.val le_rfl]

private theorem sentinelControlTest_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (control : TimeControl p) :
    sentinelControlTest rate rewards C_star C_h t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control =
      sentinelControlTest rate rewards C_star C_h t z control := by
  have hk := preChoice_event_prefix control0 t _
    (postRawKStoppedDate_measurable_preRound rate rewards C_star C_h control0 t) z
  have hp := preChoice_event_prefix control0 t _
    (pendingNonempty_measurable_preChoice rate rewards C_star C_h control0 t) z
  have hi : incomingLiveData rate rewards C_star C_h t z =
      incomingLiveData rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
    congrArg (fun v => v.bind fun code => match code.1 with
      | .inr (.inl live) => some live
      | _ => none)
      (ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 t z)
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  unfold sentinelControlTest
  simp only [Set.mem_ofPred_eq] at hk hp
  rw [← hi]
  congr 1
  exact decide_eq_decide.mpr (hk.and hp).symm

/-- The whole-control section of the actual sentinel test has mass
`1[pending nonempty] * omega`, with the original fast scalar and full weights. -/
theorem sentinelControlTest_integral
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (∫ control, (if sentinelControlTest rate rewards C_star C_h t z control then (1 : ℝ) else 0)
      ∂timeControlLaw p) =
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty then (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z := by
  classical
  by_cases hk : postRawKStoppedDate rate rewards C_star C_h t z
  · obtain ⟨r, selected, d, ha, hs, hd, hw, _⟩ :=
      stoppedDate_incomingLiveData rate rewards C_star C_h control0 t z hk
    by_cases hp : (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty
    · by_cases hpos : 0 < (wholeGridRewardRow rewards t).val selected.view.payload.assignment.auxiliary
      · let e := selectedAuxiliaryFastArm rate selected
        let E := selectedFastSample rate selected ⁻¹' {e}
        have hsample : Measurable (selectedFastSample rate selected) := by
          unfold selectedFastSample
          exact CanonicalFastSampling.measurable_sampleFast _ _ _ _ _ _ _ _ _ _ _
        have hE : MeasurableSet E := (measurableSet_singleton e).preimage hsample
        let scalar : TimeControl p → ContinuousCategorical.Scalar := fun control =>
          ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast control.1
        have hscalar : MeasurePreserving scalar (timeControlLaw p) ContinuousControlSlice.scalarLaw :=
          (ContinuousControlSlice.measurePreserving_coordinate ContinuousControlSlice.Label.fast).comp
            (ContinuousLearningRows.measurePreserving_slice p)
        have hfun : (fun control : TimeControl p =>
            if sentinelControlTest rate rewards C_star C_h t z control then (1 : ℝ) else 0) =
            (scalar ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
          funext control
          simp only [sentinelControlTest, hk, hp, and_self, decide_true, Bool.true_and,
            hd, Option.map_some, Option.getD_some, liveSentinelTest, hpos, true_and,
            decide_eq_true_eq, Set.indicator, Set.mem_preimage, E, Set.mem_singleton_iff,
            ← selectedFastSample_aux_iff rate selected d hw, scalar, e]
        have hmass : ContinuousControlSlice.scalarLaw E =
            ENNReal.ofReal (selectedFastArmMass rate selected e) := by
          rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
          unfold E selectedFastSample selectedFastArmMass
          exact CanonicalFastSampling.uniform_sampleFast_singleton _ _ _ _ _ _ _ _ _ _ _ _
        have hnonneg : 0 ≤ selectedFastArmMass rate selected e := by
          simpa only [postRawKReleaseOmega, hk, ite_true, ha, hs, ReleaseRoundKernel.chi,
            selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm,
            hpos, ite_true, mul_one, e, selectedAuxiliaryFastArm,
            ReleaseRoundKernel.auxiliaryFastArm] using
              (postRawKReleaseOmega_bounds rate rewards C_star C_h t z).1
        rw [hfun]
        calc
          _ = (timeControlLaw p (scalar ⁻¹' E)).toReal :=
            integral_indicator_one (hE.preimage hscalar.measurable)
          _ = selectedFastArmMass rate selected e := by
            rw [hscalar.measure_preimage hE.nullMeasurableSet, hmass, ENNReal.toReal_ofReal hnonneg]
          _ = _ := by
            simp only [postRawKReleaseOmega, hk, ite_true, ha, hs, hp, ReleaseRoundKernel.chi,
              selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm,
              hpos, ite_true, mul_one, one_mul, e]
      · simp only [sentinelControlTest, hk, hp, and_self, decide_true, Bool.true_and,
          hd, Option.map_some, Option.getD_some, liveSentinelTest, false_and,
          decide_false, Bool.false_eq_true, ↓reduceIte, integral_zero,
          postRawKReleaseOmega, ha, hs, ReleaseRoundKernel.chi,
          selectedAuxiliaryFastArm, ReleaseRoundKernel.auxiliaryFastArm, hpos, mul_zero]
    · simp only [sentinelControlTest, hk, hp, and_false, decide_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, integral_zero, zero_mul]
  · simp only [sentinelControlTest, hk, false_and, decide_false, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, integral_zero, postRawKReleaseOmega, mul_zero]

private theorem sentinelTest_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    (sourceInputLaw p)[(fun z => if sentinelControlTest rate rewards C_star C_h t z
        (ReferenceSourceCurrentControlFreshness.u_t p t z) then (1 : ℝ) else 0) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      fun z => (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty then (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z := by
  let B : Set (BootstrapPrivateRoundStreams.SourceInput p × TimeControl p) :=
    {v | sentinelControlTest rate rewards C_star C_h t v.1 v.2 = true}
  have hB : MeasurableSet B :=
    (measurableSet_singleton true).preimage
      (measurable_sentinelControlTest rate rewards C_star C_h control0 t)
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B =
      fun z => if sentinelControlTest rate rewards C_star C_h t z
        (ReferenceSourceCurrentControlFreshness.u_t p t z) then (1 : ℝ) else 0 := by
    funext z
    simp only [ReferenceSourceCurrentControlFreshness.sourceControlTest, B, Set.indicator,
      Set.mem_ofPred_eq, sentinelControlTest_prefix rate rewards C_star C_h control0]
  have h := ReferenceSourceCurrentControlFreshness.source_control_test_condExp control0 t B hB
  rw [htest, ← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t] at h
  filter_upwards [h] with z hz
  rw [hz]
  have heq : (fun control => B.indicator (fun _ => (1 : ℝ))
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, control)) =
      fun control => if sentinelControlTest rate rewards C_star C_h t z control then (1 : ℝ) else 0 := by
    funext control
    simp only [B, Set.indicator, Set.mem_ofPred_eq,
      sentinelControlTest_prefix rate rewards C_star C_h control0]
  rw [heq]
  exact sentinelControlTest_integral rate rewards C_star C_h control0 t z

private def sentinelTestObservation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if sentinelControlTest rate rewards C_star C_h t z
    (ReferenceSourceCurrentControlFreshness.u_t p t z) then 1 else 0

private theorem sentinelTestObservation_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Integrable (sentinelTestObservation rate rewards C_star C_h t) (sourceInputLaw p) := by
  have hpair : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      (z, ReferenceSourceCurrentControlFreshness.u_t p t z)) :=
    measurable_id.prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t)
  have hb := (measurable_sentinelControlTest rate rewards C_star C_h control0 t).comp hpair
  have hm : Measurable (sentinelTestObservation rate rewards C_star C_h t) :=
    (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp hb
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    unfold sentinelTestObservation
    split_ifs <;> norm_num

private theorem sentinel_le_test
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    postRawKReleaseSentinelObservation rate rewards C_star C_h t z ≤
      sentinelTestObservation rate rewards C_star C_h t z := by
  rw [postRawKReleaseSentinelObservation_eq_test rate rewards C_star C_h control0]
  unfold sentinelTestObservation
  split_ifs
  · rw [mul_one]
    unfold incomingAuxiliaryReward
    cases incomingLiveData rate rewards C_star C_h t z with
    | none => norm_num [ReferenceCollectionOutcomeMeasurability.optionalElim]
    | some v => exact ((wholeGridRewardRow rewards t).property _).2
  · rw [mul_zero]

/-- The actual physical sentinel has the one-round conditional upper bound on
one original-source null set for all dates. No manuscript filtration is asserted. -/
theorem postRawKReleaseSentinelObservation_condExp_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ t : Fin p.T,
      (sourceInputLaw p)[postRawKReleaseSentinelObservation rate rewards C_star C_h t |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] z ≤
      (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty then (1 : ℝ) else 0) *
        postRawKReleaseOmega rate rewards C_star C_h t z := by
  classical
  simp only [Filter.eventually_all]
  intro t
  have hmono := condExp_mono
    (m := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1))
    (postRawKReleaseSentinelObservation_integrable rate rewards C_star C_h control0 t)
    (sentinelTestObservation_integrable rate rewards C_star C_h control0 t)
    (Filter.Eventually.of_forall (sentinel_le_test rate rewards C_star C_h control0 t))
  filter_upwards [hmono, sentinelTest_condExp rate rewards C_star C_h control0 t] with z hz htest
  exact hz.trans_eq htest

/-- Every whole current-control replacement uses the same incoming payload
and whole weights. The physical sentinel is evaluated by its canonical fast
section, retaining every other original source coordinate. -/
theorem postRawKReleaseSentinelObservation_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (control : TimeControl p) :
    postRawKReleaseSentinelObservation rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      incomingAuxiliaryReward rate rewards C_star C_h t z *
        (if sentinelControlTest rate rewards C_star C_h t z control then (1 : ℝ) else 0) := by
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control
  have hin : incomingLiveData rate rewards C_star C_h t z' =
      incomingLiveData rate rewards C_star C_h t z :=
    congrArg (fun v => v.bind fun code => match code.1 with
      | .inr (.inl live) => some live
      | _ => none)
      (incomingStateCode_replace_current rate rewards C_star C_h control0 t z control)
  have hr : incomingAuxiliaryReward rate rewards C_star C_h t z' =
      incomingAuxiliaryReward rate rewards C_star C_h t z := by
    unfold incomingAuxiliaryReward
    rw [hin]
  have ht : sentinelControlTest rate rewards C_star C_h t z' control =
      sentinelControlTest rate rewards C_star C_h t z control := by
    unfold sentinelControlTest
    simp only [z', postRawKStoppedDate_replace_current rate rewards C_star C_h control0,
      postRawKStoppedPendingSet_replace_current rate rewards C_star C_h control0, hin]
  have hu : ReferenceSourceCurrentControlFreshness.u_t p t z' = control := by
    simp only [ReferenceSourceCurrentControlFreshness.u_t, z',
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  rw [postRawKReleaseSentinelObservation_eq_test rate rewards C_star C_h control0, hu, hr, ht]

/-- The existing lossless whole-record code of the actual calendar record. -/
def actualCalendarCode
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
    (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate))

private theorem measurable_code_lookup {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (fun records : List α => records[n]?) := by
  have hat := (measurable_pi_apply n).comp
    (measurable_snd.comp (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := α)))
  have hs : Measurable (some : α → Option α) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have hm := (Measurable.sumElim (measurable_const (a := (none : Option α))) hs).comp hat
  convert hm using 1
  funext records
  dsimp only [Function.comp_def, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt]
  cases records[n]? <;> rfl

private theorem actualCalendarCode_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) :
    Measurable (actualCalendarCode rate rewards C_star C_h t) := by
  have hout := (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h rate.eta rewards).comp
      ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
  have hstart : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
    have h := (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
      ReferenceInitializationRun.elapsed p b.completed)).comp hout
    convert h using 1
    funext z
    exact congrArg (fun x => ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed)
      (ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput z rewards C_star C_h rate).symm
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h
  have hlookup := (measurable_from_prod_countable_right
    (f := fun v : ℕ × List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) => v.2[v.1]?) (fun n => measurable_code_lookup n)).comp
      (((measurable_of_countable (fun n : ℕ => t.val - n)).comp hstart).prodMk
        (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
          (rate := rate) rewards C_star C_h))
  have hm : Measurable (fun z : BootstrapPrivateRoundStreams.SourceInput p =>
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
        (codes z)[t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?
      else none) := hlookup.ite
        (hstart (MeasurableSpace.measurableSet_top : MeasurableSet {s : ℕ | s ≤ t.val})) measurable_const
  convert hm using 1
  funext z
  unfold actualCalendarCode ReferenceSourcePrefixHistoryFiltration.actualRecord
  split_ifs
  · simp only [codes, ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
      List.getElem?_map]
  · rfl

/-- Signed geometry read from the existing full selection and all player
entries, retaining negative deficits. -/
def signedCodeValue (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) : ℝ :=
  ReferenceCollectionOutcomeMeasurability.optionalElim 0
    (fun selected => ReleaseRoundKernel.slowReward (wholeGridRewardRow rewards t)
      selected.1.payload.slowSet + (wholeGridRewardRow rewards t).val selected.2.2 -
        ∑ player : Fin p.m,
          ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val)
    code.2.2.1.1

private theorem signedCodeValue_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    Measurable (signedCodeValue rate rewards t) := by
  have hslow : Measurable (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      selected.1.payload.slowSet) := by
    have hp := (measurable_fst.comp (comap_measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation (p := p) (rate := rate)))).comp
        (measurable_fst : Measurable (Prod.fst :
          ReferenceLiveDispatchOutputMeasurability.SelectionData p rate → _))
    exact (((comap_measurable
      (LaterAssignmentStartMeasurability.payloadObservation (p := p) (eta := rate.eta))).comp hp).snd.snd.fst).subtype_mk
  have hcost : Measurable (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      ReleaseRoundKernel.slowReward (wholeGridRewardRow rewards t) selected.1.payload.slowSet +
        (wholeGridRewardRow rewards t).val selected.2.2) :=
    ((measurable_of_countable (ReleaseRoundKernel.slowReward (wholeGridRewardRow rewards t))).comp hslow).add
      ((measurable_of_countable ((wholeGridRewardRow rewards t).val)).comp (measurable_snd.comp measurable_snd))
  have hsum : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => ∑ player : Fin p.m,
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val) :=
    Finset.measurable_fun_sum _ fun player _ => measurable_subtype_coe.comp
      (measurable_subtype_coe.comp (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry player)))
  have hm := ReferenceCollectionOutcomeMeasurability.measurable_mapOptional
    (fun v : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
      ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) =>
      ReleaseRoundKernel.slowReward (wholeGridRewardRow rewards t) v.1.1.payload.slowSet +
        (wholeGridRewardRow rewards t).val v.1.2.2 -
        ∑ player : Fin p.m,
          ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry v.2 player).2).val.val)
    ((hcost.comp measurable_fst).sub (hsum.comp measurable_snd))
  have hphysical : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id))
  have hmap := hm.comp ((measurable_fst.comp hphysical).prodMk measurable_id)
  have helim := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ) id measurable_id
  convert helim.comp hmap using 1
  funext code
  dsimp only [Function.comp_def, ReferenceCollectionOutcomeMeasurability.mapOptional, signedCodeValue]
  cases code.2.2.1.1 <;> rfl

/-- The actual signed stopped deficit is Borel on the original source. -/
theorem postRawKStoppedSignedReleaseDeficit_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t) := by
  have hm := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ) _
    (signedCodeValue_measurable rate rewards t)).comp
      (actualCalendarCode_measurable rate rewards C_star C_h t)
  have hkeep : MeasurableSet {z | postRawKStoppedDate rate rewards C_star C_h t z} :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1) _
      (postRawKStoppedDate_measurable_preRound rate rewards C_star C_h control0 t)
  have hmasked : Measurable (fun z => if postRawKStoppedDate rate rewards C_star C_h t z then
      ReferenceCollectionOutcomeMeasurability.optionalElim 0 (signedCodeValue rate rewards t)
        (actualCalendarCode rate rewards C_star C_h t z) else (0 : ℝ)) := hm.ite hkeep measurable_const
  convert hmasked using 1
  funext z
  unfold postRawKStoppedSignedReleaseDeficit actualCalendarCode
  split_ifs
  · cases ha : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => rfl
    | some r =>
      have hsel := (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1
      have hs : (ReferenceActivePhysicalStep.dispatch r.input).selection =
          r.output.preparation.coordinator.selection := by
        simp only [r.output_eq, ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare]
      simp only [Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim, signedCodeValue,
        hsel, hs]
      cases r.output.preparation.coordinator.selection with
      | none => rfl
      | some selected =>
        simp only [Option.map_some, ReferenceLiveDispatchOutputMeasurability.encodeSelection]
        congr 1
        apply Finset.sum_congr rfl
        intro player _
        rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.2.2.2 player]
  · rfl


/-- The signed deficit is bounded in absolute value, including all negative
physical rewards differences. This gives its original-law integrability. -/
theorem postRawKStoppedSignedReleaseDeficit_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T) :
    Integrable (postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t) (sourceInputLaw p) := by
  apply (integrable_const ((p.K : ℝ) + p.m + 1)).mono'
    (postRawKStoppedSignedReleaseDeficit_measurable
      rate rewards C_star C_h control0 t).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  unfold postRawKStoppedSignedReleaseDeficit
  split
  · cases ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
    | none => simp only [abs_zero]; positivity
    | some r =>
      cases hs : r.output.preparation.coordinator.selection with
      | none => simp only [hs, abs_zero]; positivity
      | some selected =>
        simp only [hs]
        let row := wholeGridRewardRow rewards t
        have hslow0 : 0 ≤ slowReward row selected.view.payload.slowSet :=
          Finset.sum_nonneg fun a _ => (row.property a).1
        have hslow1 : slowReward row selected.view.payload.slowSet ≤
            (selected.view.payload.slowSet.val.card : ℝ) := by
          simpa only [slowReward, Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_le_sum (s := selected.view.payload.slowSet.val)
              (fun a _ => (row.property a).2))
        have hcard : (selected.view.payload.slowSet.val.card : ℝ) ≤ p.K := by
          exact_mod_cast (show selected.view.payload.slowSet.val.card ≤ p.K by
            simpa only [Fintype.card_fin] using Finset.card_le_univ selected.view.payload.slowSet.val)
        have hown0 : 0 ≤ ∑ player : Fin p.m, ((r.ownEntries player).2).val.val :=
          Finset.sum_nonneg fun player _ => ((r.ownEntries player).2).val.property.1
        have hown1 : (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤ (p.m : ℝ) := by
          simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using
            (Finset.sum_le_sum (s := Finset.univ)
              (fun player _ => ((r.ownEntries player).2).val.property.2))
        exact abs_le.mpr ⟨by linarith only [hslow0, hown1, (row.property selected.arm).1,
          (Nat.cast_nonneg (α := ℝ) p.K)], by linarith only [hslow1, hcard, hown0,
            (row.property selected.arm).2, (Nat.cast_nonneg (α := ℝ) p.m)]⟩
  · simp only [abs_zero]
    positivity

/-- A genuine empty-pending date remains supported, and its signed physical
release deficit is nonpositive on the same actual record. -/
theorem postRawKStoppedSignedReleaseDeficit_nonpos_of_empty
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hp : postRawKStoppedPendingSet rate rewards C_star C_h t z = ∅) :
    postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t z ≤ 0 := by
  by_cases hk : postRawKStoppedDate rate rewards C_star C_h t z
  · obtain ⟨r, selected, ha, hs, hcost⟩ := stoppedDate_emptyPending_signedDeficit_nonpos
      rate rewards C_star C_h control0 t z hk hp
    simpa only [postRawKStoppedSignedReleaseDeficit, hk, ite_true, ha, hs] using hcost
  · simp only [postRawKStoppedSignedReleaseDeficit, hk, ite_false, le_refl]

/-- The stopped signed one-round release cost, on the original source law,
is bounded conditionally by the DATA coefficients and the common omega. -/
theorem postRawKStoppedSignedReleaseDeficit_condExp_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ t : Fin p.T,
      (sourceInputLaw p)[postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] z ≤
      (∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z) +
        (if (postRawKStoppedPendingSet rate rewards C_star C_h t z).Nonempty then (1 : ℝ) else 0) *
          postRawKReleaseOmega rate rewards C_star C_h t z := by
  classical
  simp only [Filter.eventually_all]
  intro t
  let coeff := fun z => ∑ i : Fin (p.m - 1), stoppedAssignedChi rate rewards C_star C_h t i z
  have hci : Integrable coeff (sourceInputLaw p) := integrable_finsetSum _ fun i _ =>
    stoppedAssignedChi_integrable rate rewards C_star C_h control0 t i
  have hcm : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] coeff :=
    Finset.measurable_fun_sum _ fun i _ =>
      stoppedAssignedChi_measurable_preChoice rate rewards C_star C_h control0 t i
  have hdom (z) : postRawKStoppedSignedReleaseDeficit rate rewards C_star C_h t z ≤
      coeff z + postRawKReleaseSentinelObservation rate rewards C_star C_h t z := by
    have hsum : (∑ i ∈ postRawKStoppedPendingSet rate rewards C_star C_h t z,
        stoppedAssignedChi rate rewards C_star C_h t i z) = coeff z := by
      exact Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        simp only [stoppedAssignedChi, hi, ite_false]
    rw [← hsum]
    exact postRawKStoppedSignedReleaseDeficit_le rate rewards C_star C_h control0 t z
  have hmono := condExp_mono
    (m := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1))
    (postRawKStoppedSignedReleaseDeficit_integrable rate rewards C_star C_h control0 t)
    (hci.add (postRawKReleaseSentinelObservation_integrable rate rewards C_star C_h control0 t))
    (Filter.Eventually.of_forall hdom)
  have hc := condExp_of_stronglyMeasurable
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1))
    hcm.stronglyMeasurable hci
  filter_upwards [hmono, condExp_add hci
    (postRawKReleaseSentinelObservation_integrable rate rewards C_star C_h control0 t)
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)),
    postRawKReleaseSentinelObservation_condExp_le rate rewards C_star C_h control0] with z hz hadd hsent
  rw [hadd, hc] at hz
  exact hz.trans (add_le_add le_rfl (hsent t))

end Bandits.Support.ReferencePostReplacementCollectionSentinelSectionLaw

end
