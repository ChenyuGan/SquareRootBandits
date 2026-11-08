/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedCallAdmissibility
public import Bandits.Support.ReferenceFirstCollectionCurrentRemainderLaw

/-!
# The actual recording marker at the first collection invocation

The outer option records numerical-cell presence. The inner option records
the bottom or arm outcome, including arms with zero quantized arrival.

Sources: `05_binary_transport.tex:352-431`, `06_interruptions.tex:363-426`,
`04_slow_fast_learner.tex:140-188`, and `appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCurrentRecordedCell

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open CoordinatorPhaseClock (AssignmentStartInstruction)
open ActualInitializationPhysicalStep (GridRewardTable selectedRowIndex)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open AssignmentParameterFibreKernel (AssignmentVector Theta)
open ReferenceLaterOptionalControlResampling (ControlRemainder controlRemainderLaw)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open ReferenceSourcePrefixHistoryFiltration (actualRecord sourcePrefix sourcePrefixFiltration)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters}

private theorem successfulStart_parameters
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters? old
        ⟨ledger, instruction, consistent⟩ = some (output.law.mass, output.law.anchor) := by
  have hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger instruction =
      .success output.reconstruction output.reconstruction_eq := by
    have hpair :
        (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩ :
          LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
        ⟨.success ledger instruction output.reconstruction, output.reconstruction_eq⟩ := by
      apply LaterAssignmentStartOperation.ReconstructionCall.ext
      exact output.reconstruction_eq
    unfold LaterAssignmentStartOperation.decideReconstruction
    rw [hpair]
    rfl
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match, hdecision]
  let selection := LaterAssignmentStartMeasurability.successfulLawSelection old ledger
    instruction output.reconstruction output.reconstruction_eq
  have hlaw : selection.law = output.law :=
    Option.some.inj (selection.lawSelected.symm.trans output.law_selected)
  change some (selection.law.mass, selection.law.anchor) = _
  rw [hlaw]

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- The finite optional marker observation with its discrete measurable space. -/
theorem currentMarker_measurable (t : Fin p.T) :
    Measurable (ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t) := by
  have hspace : ReferenceFirstCollectionCurrentNumericalCell.optionalMarkerMeasurableSpace
      (p := p) = (inferInstance : MeasurableSpace (Option (Option (Fin p.K)))) := by
    apply le_antisymm le_top
    intro S _hS
    change MeasurableSet[(inferInstance : MeasurableSpace
      (Option (Fin p.K) ⊕ PUnit)).comap (Equiv.optionEquivSumPUnit (Option (Fin p.K)))] S
    refine ⟨(Equiv.optionEquivSumPUnit (Option (Fin p.K))) '' S, ?_, ?_⟩
    · rw [measurableSet_sum_iff]
      exact ⟨trivial, trivial⟩
    · exact Equiv.preimage_image _ _
  have hm := ReferenceFirstCollectionCurrentNumericalCell.currentMarker_measurable
    rate rewards C_star C_h t
  rw [hspace] at hm
  exact hm

/-- The anchor of an actual selected first-call payload is the anchor returned
by the real parameter selector, on both corrected and renewal calls. -/
theorem selected_anchor
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (theta : Theta p)
    (hp : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = some theta)
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    selected.view.payload.anchor = theta.2 := by
  have hprep : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hchosen := ReferenceFirstCollectionCurrentRemainderLaw.selected_laterChosen
    rate r.input theta hp selected (by rw [← hprep]; exact hs)
  have hparam := (ReferenceLaterAssignmentFibreStep.parameters?_eq_physicalDispatch
    r.input).symm.trans hp
  change ReferenceLaterAssignmentFibreStep.dispatchParameters?
    (ReferenceActivePhysicalStep.prepare r.input).coordinator = some theta at hparam
  rw [← hprep] at hparam
  have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance r.input
  have hactual : ReferenceActivePhysicalStep.dispatch r.input =
      r.output.preparation.coordinator := by
    rw [hprep]
    rfl
  rw [hactual] at hprovenance
  cases he : r.output.preparation.coordinator with
  | first outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he,
        Bool.false_eq_true] at hchosen
  | live registers owned base outcome =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he,
        Bool.false_eq_true] at hchosen
  | invalidCollectionCutoff =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he,
        Bool.false_eq_true] at hchosen
  | dagger =>
      simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hprep, he,
        Bool.false_eq_true] at hchosen
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> simp only [ReferenceCollectionPhaseHistory.laterChosen,
        ← hprep, he, Bool.false_eq_true] at hchosen
      rename_i core consistent started hstart instruction hi output hlocal clockData installed arm
      rw [he] at hs hparam
      rw [he] at hprovenance
      simp only [ReferenceLaterAssignmentFibreStep.dispatchParameters?,
        ReferenceLaterAssignmentFibreStep.outcomeParameters?] at hparam
      rw [successfulStart_parameters _ _ _ _ _ output] at hparam
      have hanchor : output.payload.anchor = theta.2 :=
        output.payload_anchor.trans (congrArg Prod.snd (Option.some.inj hparam))
      have frames := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
      rw [he] at frames
      dsimp only at frames
      have hsel := ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq r.input
        installed.registers.payload started instruction.time installed.registers.complementWeights
        arm frames.1
      simp only [ReferenceActivePhysicalStep.DispatchCut.selection, hsel,
        Option.some.injEq] at hs
      subst selected
      change installed.registers.payload.anchor = theta.2
      rw [hprovenance.2.1]
      exact hanchor

/-- Total selection and cell presence are consequences of the original first
invocation, with its original complete-suffix index and input fields. -/
theorem firstCell_selected (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (n : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (theta : Theta p) (selected : ReferenceActivePhysicalStep.Selection r.input)
      (c : RecordedQueueRun.RoundInput p.K),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r ∧
      r.input.time = t ∧ actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.rows = z.1.2 ∧ r.input.selected = selectedRowIndex p z ∧ r.input.rewards = rewards ∧
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      r.output.preparation.coordinator.selection = some selected ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) r = some c ∧
      selected.view.payload.anchor = theta.2 ∧ (∀ a, 0 < theta.2 a) := by
  obtain ⟨n, r, theta, _old, _ledger, _saved, _registers, hn, ht, hr, hcall,
    hrows, hj, hrewards, _hstate, _hcut, _hcursor, _hpending, _hregs, _hbounds,
    _hcorrected, hchosen, hpresent⟩ :=
    ReferenceFirstCollectionCorrectedCallAdmissibility.firstCell_corrected_parameters_admissible
      rate rewards C_star C_h u t z hz
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hpresent
  have hread := hc
  simp only [ReferenceFirstCollectionCurrentNumericalCell.currentCell, hr,
    Option.bind_some] at hread
  obtain ⟨selected, _ho, hs, _hstart, _hlive, _hc⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ r c hread
  obtain ⟨_, _, _, _, _, hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hcall
  have ha := selected_anchor rate r theta hp selected hs
  refine ⟨n, r, theta, selected, c, hn, ht, hr, hrows, hj, hrewards, ?_,
    hs, hchosen, hc, hread, ha, ?_⟩
  · simp only [calendarParameters, hr, Option.bind_some]
    exact hp
  · intro a
    rw [← ha]
    exact selected.view.payload.anchor_pos a

/-- Every replacement of the entire assignment vector and entire remainder
has a selected view, using admissibility on that actual replacement source. -/
theorem currentParameters_present (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t)
    (v : AssignmentVector p) (w : ControlRemainder p) :
    ∃ q, ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
      rate rewards C_star C_h control0 t z v w = some q := by
  obtain ⟨_n, r, _theta, selected, _c, _hn, _ht, hr, _hrows, _hj, _hrewards,
    _hp, hs, _hchosen, _hc, _hread, _ha, _hpos⟩ :=
    firstCell_selected rate rewards C_star C_h u t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w)
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource_firstCell
        rate rewards C_star C_h control0 u t z hz v w)
  exact ⟨(selected.view, selected.started), by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentParameters,
      hr, Option.bind_some, hs, Option.map_some]⟩

/-- One actual calendar parameter, with positive anchor, governs the recording
law for every whole assignment vector. No outer absence mass remains. -/
theorem firstCell_fixedVector_law (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (theta : Theta p) (hpos : ∀ a, 0 < theta.2 a),
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      ∀ v : AssignmentVector p,
        (controlRemainderLaw p).map
          (ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
            rate rewards C_star C_h control0 t z v) =
        ((RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
            rate.sourceCap theta.2 hpos)).toMeasure).map some := by
  obtain ⟨theta, hcall⟩ := ReferenceFirstCollectionCurrentRemainderLaw.firstCell_call
    rate rewards C_star C_h u t z hz
  have hp := ReferenceFirstCollectionCurrentRemainderLaw.firstCall_calendarParameters
    rate rewards C_star C_h u t z theta hcall
  have anchor (v : AssignmentVector p) (w : ControlRemainder p)
      (q : ReferenceDownReception.ChoiceTimeView p rate.eta ×
        CoordinatorPhaseClock.StartRoundResult p)
      (hq : ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
        rate rewards C_star C_h control0 t z v w = some q) :
      q.1.payload.anchor = theta.2 := by
    have hcall' := ReferenceFirstCollectionCurrentRemainderLaw.currentSource_firstCall
      rate rewards C_star C_h control0 u t z theta hcall v w
    obtain ⟨r, hr, _ht, hparameters⟩ :=
      ReferenceFirstCollectionCurrentRemainderLaw.firstCall_record
        rate rewards C_star C_h u t _ theta hcall'
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentParameters,
      hr, Option.bind_some] at hq
    obtain ⟨selected, hs, heq⟩ := Option.map_eq_some_iff.mp hq
    cases heq
    exact selected_anchor rate r theta hparameters selected hs
  let v0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).1
  let w0 := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control0).2
  obtain ⟨q0, hq0⟩ := currentParameters_present
    rate rewards C_star C_h control0 u t z hz v0 w0
  have ha0 := anchor v0 w0 q0 hq0
  have hpos : ∀ a, 0 < theta.2 a := by
    rw [← ha0]
    exact q0.1.payload.anchor_pos
  refine ⟨theta, hpos, hp, ?_⟩
  intro v
  obtain ⟨q, hq⟩ := currentParameters_present
    rate rewards C_star C_h control0 u t z hz v w0
  have hlaw := ReferenceFirstCollectionCurrentRemainderLaw.currentRemainder_optionalMarker_law
    rate rewards C_star C_h control0 u t z hz v
  rw [hq] at hlaw
  rw [hlaw]
  rcases q with ⟨view, started⟩
  dsimp only
  have ha := anchor v w0 (view, started) hq
  have hrates : SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
      rate.sourceCap view.payload.anchor view.payload.anchor_pos =
      SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
        rate.sourceCap theta.2 hpos := by
    unfold SnapshotRecordingKernel.recordingRates
    congr 1
    exact congrArg (CanonicalRecordingRates.xi p rate.eta.val) ha
  rw [hrates]

/-- The first-call marker is the existing recording map on the ordinary,
unoccupied snapshot, evaluated at the original entire current control. -/
theorem firstCell_marker_view (_control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
        view.complementWeights),
      ReferenceCollectionOutcomeMeasurability.optionalElim none
        (ReferenceFirstCollectionCurrentRemainderLaw.parametersFromCode rate)
        (ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z) =
          some (view, started) ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t z =
        some (ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap rate t view valid
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (ReferenceSourceCurrentControlFreshness.u_t p t z)).1
          (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
            (ReferenceSourceCurrentControlFreshness.u_t p t z)).2) := by
  obtain ⟨_n, r, theta, selected, c, _hn, ht, hr, hrows, hj, _hrewards,
    _hp, hs, _hchosen, hc, hread, _ha, _hpos⟩ :=
    firstCell_selected rate rewards C_star C_h u t z hz
  obtain ⟨theta', hcall⟩ := ReferenceFirstCollectionCurrentRemainderLaw.firstCell_call
    rate rewards C_star C_h u t z hz
  obtain ⟨ho, _hdomain, hpending, hstates⟩ :=
    ReferenceFirstCollectionCurrentRemainderLaw.firstCall_selected_domain
      rate rewards C_star C_h u t z theta' hcall r hr selected hs
  have valid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff t selected.view.complementWeights := by
    simpa only [ht] using ReferenceLaterLiveNumericalReadout.selection_choiceValid selected
  refine ⟨selected.view, selected.started, valid, ?_, ?_⟩
  · simp only [ReferenceCalendarActualControlCallbackSections.codeAt, hr,
      Option.map_some, ReferenceCollectionOutcomeMeasurability.optionalElim,
      ReferenceFirstCollectionCurrentRemainderLaw.parametersFromCode]
    rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).1]
    have hdispatch : (ReferenceActivePhysicalStep.dispatch r.input).selection = some selected := by
      rw [r.output_eq] at hs
      exact hs
    rw [hdispatch]
    rfl
  · rw [ReferenceFirstCollectionCurrentNumericalCell.currentMarker, hc, Option.map_some]
    congr 1
    obtain ⟨selected', ho', hs', _hstart, _hlive, hcell⟩ :=
      ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ r c hread
    have heq : selected' = selected := Option.some.inj (hs'.symm.trans hs)
    subst selected'
    rw [hcell]
    have hstatus : (fun i => (ReferenceLaterLiveNumericalReadout.preparedStates r ho' i).status) =
        fun _ => ActiveRoundActions.FollowerStatus.unoccupied :=
      funext (fun i => (hstates i).1)
    have hrow : (r.input.row.2 r.input.time).1 =
        (ReferenceSourceCurrentControlFreshness.u_t p t z).1 := by
      change ((r.input.rows r.input.selected).2 r.input.time).1 = _
      rw [hrows, hj, ht]
      rfl
    have hsnapshot :
        (ActiveRoundActions.Snapshot.mk selected.view.pendingAtChoice
          (fun i => (ReferenceLaterLiveNumericalReadout.preparedStates r ho' i).status) :
            ActiveRoundActions.Snapshot selected.view.payload.assignment) =
          ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot selected.view.payload.assignment :=
      congrArg₂ (fun missing status => (ActiveRoundActions.Snapshot.mk missing status :
        ActiveRoundActions.Snapshot selected.view.payload.assignment)) hpending hstatus
    dsimp only [ReferenceFirstWindowNumericalStream.sourceCell,
      ReferenceFirstWindowNumericalStream.sourceArm,
      ReferenceFirstCollectionCurrentRemainderLaw.viewRecordingMap,
      ReferenceFirstCollectionCurrentRemainderLaw.currentControl]
    rw [hsnapshot, hrow,
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply]

/-- Exact predictability factor for the actual first invocation. -/
theorem firstCell_prefix_iff (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) :
    z ∈ firstCell rate rewards C_star C_h u t ↔
      sourcePrefix control0 t.val z ∈ firstCell rate rewards C_star C_h u t := by
  have hmeas := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hmeas
  obtain ⟨B, _hB, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hmeas
  rw [← hpre]
  change sourcePrefix control0 t.val z ∈ B ↔
    sourcePrefix control0 t.val (sourcePrefix control0 t.val z) ∈ B
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val t.val le_rfl]

/-- Restoring the complete current control reconstructs the actual marker.
This is used only on the actual first-cell event; no successful-source
subtype or new numerical execution is introduced. -/
theorem firstCell_marker_restore (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (sourcePrefix control0 t.val z) (ReferenceSourceCurrentControlFreshness.u_t p t z)) =
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t z := by
  let control := ReferenceSourceCurrentControlFreshness.u_t p t z
  let splitControl := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p control
  let z' := ReferenceFirstCollectionCurrentRemainderLaw.currentSource
    control0 t z splitControl.1 splitControl.2
  have hz' := ReferenceFirstCollectionCurrentRemainderLaw.currentSource_firstCell
    rate rewards C_star C_h control0 u t z hz splitControl.1 splitControl.2
  have hrestore : z' = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (sourcePrefix control0 t.val z) control := by
    dsimp only [z', ReferenceFirstCollectionCurrentRemainderLaw.currentSource,
      ReferenceFirstCollectionCurrentRemainderLaw.currentControl, splitControl]
    rw [(LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply]
  have hprefix : z' = sourcePrefix control0 (t.val + 1) z := by
    rw [hrestore]
    exact (ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t z).symm
  have hcode : ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z' =
      ReferenceCalendarActualControlCallbackSections.codeAt rate rewards C_star C_h t z := by
    rw [hprefix]
    exact (ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
      rate rewards C_star C_h control0 t z).symm
  have hcontrol : ReferenceSourceCurrentControlFreshness.u_t p t z' = control := by
    rw [hprefix]
    change ((sourcePrefix control0 (t.val + 1) z).1.2
      (selectedRowIndex p z)).2 t = _
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left (Nat.lt_succ_self _)]
    rfl
  obtain ⟨view, started, valid, hview, hm⟩ :=
    firstCell_marker_view rate rewards C_star C_h control0 u t z hz
  obtain ⟨view', started', valid', hview', hm'⟩ :=
    firstCell_marker_view rate rewards C_star C_h control0 u t z' hz'
  rw [hcode, hview] at hview'
  have heq := Option.some.inj hview'
  have hv : view = view' := congrArg Prod.fst heq
  subst view'
  rw [← hrestore]
  rw [hm', hcontrol]
  exact hm.symm

/-- The literal scalar observation of the actual calendar parameter. Its
probability interpretation below is restricted to the first-call event. -/
def markerProbability (t : Fin p.T) (o : Option (Option (Fin p.K)))
    (z : SourceInput p) : ℝ :=
  match calendarParameters rate rewards C_star C_h t z with
  | none => 0
  | some theta =>
      match o with
      | none => 0
      | some none => 1 - ∑ a, CanonicalRecordingRates.xi p rate.eta.val theta.2 a
      | some (some a) => CanonicalRecordingRates.xi p rate.eta.val theta.2 a

private theorem integral_eq_atom {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) (o : X) :
    (∫ x, if x = o then (1 : ℝ) else 0 ∂μ) = (μ {o}).toReal := by
  have heq : (fun x : X => if x = o then (1 : ℝ) else 0) =
      ({o} : Set X).indicator (fun _ => (1 : ℝ)) := by
    funext x
    simp only [Set.indicator, Set.mem_singleton_iff]
  rw [heq, integral_indicator_const (1 : ℝ) (measurableSet_singleton o)]
  simp only [smul_eq_mul, mul_one, Measure.real]

/-- Every original fixed vector gives the same three distinct scalar masses. -/
theorem fixedVector_marker_integral (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t)
    (v : AssignmentVector p) (o : Option (Option (Fin p.K))) :
    (∫ w, if ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
      rate rewards C_star C_h control0 t z v w = o then (1 : ℝ) else 0
        ∂controlRemainderLaw p) = markerProbability rate rewards C_star C_h t o z := by
  obtain ⟨theta, hpos, hp, hlaw⟩ :=
    firstCell_fixedVector_law rate rewards C_star C_h control0 u t z hz
  have htest : StronglyMeasurable
      (fun y : Option (Option (Fin p.K)) => if y = o then (1 : ℝ) else 0) :=
    (measurable_of_countable _).stronglyMeasurable
  rw [← integral_map_of_stronglyMeasurable
    (ReferenceFirstCollectionCurrentRemainderLaw.currentMarker_measurable
      rate rewards C_star C_h control0 u t z hz v) htest, hlaw v]
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _) htest]
  unfold markerProbability
  rw [hp]
  cases o with
  | none => simp only [reduceCtorEq, ite_false, integral_zero]
  | some inner =>
      simp only [Option.some.injEq]
      have hint := integral_eq_atom ((RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
          rate.sourceCap theta.2 hpos)).toMeasure) inner
      calc
        _ = ((RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
            rate.sourceCap theta.2 hpos)).toMeasure {inner}).toReal := by
          convert hint using 1
          congr 1
          funext x
          by_cases hx : x = inner <;> simp only [hx, ite_true, ite_false]
        _ = _ := ?_
      cases inner with
      | none =>
          rw [RecordedRoundMoments.recordingOutcomePMF_toMeasure_none,
            ENNReal.toReal_ofReal]
          · rfl
          · exact sub_nonneg.mpr
              (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property
                rate.sourceCap theta.2 hpos).rate_sum_le_one
      | some a =>
          rw [RecordedRoundMoments.recordingOutcomePMF_toMeasure_some,
            ENNReal.toReal_ofReal]
          · rfl
          · exact (CanonicalRecordingRates.xi_pos p rate.eta.property theta.2 a).le

/-- Integrating a fresh entire current control preserves the true assignment
and remainder product, rather than normalizing a successful subcarrier. -/
theorem firstCell_currentControl_integral (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t)
    (o : Option (Option (Fin p.K))) :
    (∫ control, if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
      rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (sourcePrefix control0 t.val z) control) = o then (1 : ℝ) else 0
        ∂ContinuousLearningRows.timeControlLaw p) =
      markerProbability rate rewards C_star C_h t o z := by
  let f : AssignmentVector p × ControlRemainder p → ℝ := fun vw =>
    if ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
      rate rewards C_star C_h control0 t z vw.1 vw.2 = o then 1 else 0
  have hmarker : Measurable (fun vw : AssignmentVector p × ControlRemainder p =>
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z vw.1 vw.2)) :=
    (currentMarker_measurable
      rate rewards C_star C_h t).comp
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource_measurable control0 t z)
  have heqMarker (vw : AssignmentVector p × ControlRemainder p) :
      ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
        rate rewards C_star C_h control0 t z vw.1 vw.2 =
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t
        (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z vw.1 vw.2) := by
    simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentMarker,
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker,
      ReferenceFirstCollectionCurrentNumericalCell.currentCell, Option.map_bind, Function.comp_def]
  have hf : Measurable f := by
    have h := (measurable_of_countable
      (fun y : Option (Option (Fin p.K)) => if y = o then (1 : ℝ) else 0)).comp hmarker
    simpa only [f, heqMarker, Function.comp_def] using h
  have hfint : Integrable f
      ((ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)) := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [] with vw
    dsimp only [f]
    split_ifs <;> norm_num
  have hsplit := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have htransport := hsplit.integral_comp' f
  calc
    _ = ∫ control, f ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p) control)
        ∂ContinuousLearningRows.timeControlLaw p := by
      apply integral_congr_ae
      filter_upwards [] with control
      have hsplitControl := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply control
      simp only [f, ReferenceFirstCollectionCurrentRemainderLaw.currentMarker,
        ReferenceFirstCollectionCurrentNumericalCell.currentMarker,
        ReferenceFirstCollectionCurrentNumericalCell.currentCell,
        ReferenceFirstCollectionCurrentRemainderLaw.currentSource,
        ReferenceFirstCollectionCurrentRemainderLaw.currentControl,
        Option.map_bind, hsplitControl, Function.comp_def]
    _ = ∫ vw, f vw ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p) := htransport
    _ = ∫ v, ∫ w, f (v, w) ∂controlRemainderLaw p
        ∂ContinuousControlSlice.assignmentLaw p.K := integral_prod f hfint
    _ = _ := by
      have heq : (fun v => ∫ w, f (v, w) ∂controlRemainderLaw p) =
          fun _ => markerProbability rate rewards C_star C_h t o z := by
        funext v
        exact fixedVector_marker_integral rate rewards C_star C_h control0 u t z hz v o
      rw [heq, integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- Borel test of the literal replacement source, localized by its actual
prechoice first-call event. -/
def markerControlSet (u t : Fin p.T) (o : Option (Option (Fin p.K))) :
    Set (SourceInput p × TimeControl p) :=
  {x | x.1 ∈ firstCell rate rewards C_star C_h u t ∧
    ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2) = o}

theorem markerControlSet_measurable (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) :
    MeasurableSet (markerControlSet rate rewards C_star C_h u t o) := by
  have hcell : MeasurableSet (firstCell rate rewards C_star C_h u t) :=
    (sourcePrefixFiltration control0).le' (t.val + 1) _
      (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
        rate rewards C_star C_h control0 u t)
  exact (hcell.preimage measurable_fst).inter
    (measurableSet_eq_fun
      ((currentMarker_measurable rate rewards C_star C_h t).comp
        (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t))
      measurable_const)

theorem markerControl_test (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) (z : SourceInput p) :
    ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
      (markerControlSet rate rewards C_star C_h u t o) z =
    (firstCell rate rewards C_star C_h u t).indicator
      (fun y => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
        rate rewards C_star C_h t y = o then (1 : ℝ) else 0) z := by
  rw [ReferenceSourceCurrentControlFreshness.sourceControlTest,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
  · have hpref := (firstCell_prefix_iff rate rewards C_star C_h control0 u t z).mp hz
    have hm := firstCell_marker_restore rate rewards C_star C_h control0 u t z hz
    simp only [markerControlSet, Set.indicator, Set.mem_ofPred_eq, hpref, true_and,
      hz, ite_true, hm]
  · have hpref : sourcePrefix control0 t.val z ∉ firstCell rate rewards C_star C_h u t :=
      fun h => hz ((firstCell_prefix_iff rate rewards C_star C_h control0 u t z).mpr h)
    simp only [markerControlSet, Set.indicator, Set.mem_ofPred_eq, hpref,
      false_and, hz, ite_false]

/-- The fresh whole-control section equals the indicated literal coefficient
on the entire original source carrier, including zero first-cell mass. -/
theorem markerControl_section (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) (z : SourceInput p) :
    (∫ control, (markerControlSet rate rewards C_star C_h u t o).indicator
      (fun _ => (1 : ℝ))
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, control)
      ∂ContinuousLearningRows.timeControlLaw p) =
    (firstCell rate rewards C_star C_h u t).indicator
      (markerProbability rate rewards C_star C_h t o) z := by
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
  · have hpref := (firstCell_prefix_iff rate rewards C_star C_h control0 u t z).mp hz
    simp only [markerControlSet, Set.indicator, Set.mem_ofPred_eq, hpref, true_and,
      hz, ite_true]
    exact firstCell_currentControl_integral rate rewards C_star C_h control0 u t z hz o
  · have hpref : sourcePrefix control0 t.val z ∉ firstCell rate rewards C_star C_h u t :=
      fun h => hz ((firstCell_prefix_iff rate rewards C_star C_h control0 u t z).mpr h)
    simp only [markerControlSet, Set.indicator, Set.mem_ofPred_eq, hpref,
      false_and, hz, ite_false, integral_zero]

/-- The indicated coefficient is measurable in precisely the field retaining
controls strictly below `t.val`, with the filtration's original offset. -/
theorem indicatedProbability_stronglyMeasurable (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 1)]
      ((firstCell rate rewards C_star C_h u t).indicator
        (markerProbability rate rewards C_star C_h t o)) := by
  have hB := markerControlSet_measurable rate rewards C_star C_h control0 u t o
  have hfun : Measurable ((markerControlSet rate rewards C_star C_h u t o).indicator
      (fun _ => (1 : ℝ))) := measurable_const.indicator hB
  have hG := hfun.stronglyMeasurable.integral_prod_right'
    (ν := ContinuousLearningRows.timeControlLaw p)
  have hpref : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t) := by
    rw [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t]
    exact comap_measurable _
  have heq : (fun z => ∫ control,
      (markerControlSet rate rewards C_star C_h u t o).indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, control)
          ∂ContinuousLearningRows.timeControlLaw p) =
      (firstCell rate rewards C_star C_h u t).indicator
        (markerProbability rate rewards C_star C_h t o) :=
    funext (markerControl_section rate rewards C_star C_h control0 u t o)
  rw [← heq]
  exact hG.comp_measurable hpref

/-- Boundedness is asserted for the indicated coefficient only. -/
theorem indicatedProbability_bounds (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) (z : SourceInput p) :
    0 ≤ (firstCell rate rewards C_star C_h u t).indicator
        (markerProbability rate rewards C_star C_h t o) z ∧
      (firstCell rate rewards C_star C_h u t).indicator
        (markerProbability rate rewards C_star C_h t o) z ≤ 1 := by
  rw [← markerControl_section rate rewards C_star C_h control0 u t o z]
  let B := markerControlSet rate rewards C_star C_h u t o
  let sourcePast := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
  have hb (control : TimeControl p) :
      0 ≤ B.indicator (fun _ => (1 : ℝ)) (sourcePast, control) ∧
        B.indicator (fun _ => (1 : ℝ)) (sourcePast, control) ≤ 1 := by
    by_cases h : (sourcePast, control) ∈ B <;>
      simp only [Set.indicator, h, ite_true, ite_false] <;> norm_num
  have hmeas : Measurable (fun control : TimeControl p =>
      B.indicator (fun _ => (1 : ℝ)) (sourcePast, control)) :=
    (measurable_const.indicator
      (markerControlSet_measurable rate rewards C_star C_h control0 u t o)).comp
        (measurable_const.prodMk measurable_id)
  have hint : Integrable (fun control : TimeControl p =>
      B.indicator (fun _ => (1 : ℝ)) (sourcePast, control))
      (ContinuousLearningRows.timeControlLaw p) := by
    apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with control
    rw [Real.norm_of_nonneg (hb control).1]
    exact (hb control).2
  refine ⟨integral_nonneg (fun control => (hb control).1), ?_⟩
  calc
    _ ≤ ∫ _ : TimeControl p, (1 : ℝ) ∂ContinuousLearningRows.timeControlLaw p :=
      integral_mono hint (integrable_const _) (fun control => (hb control).2)
    _ = 1 := by simp only [integral_const, Measure.real, measure_univ,
        ENNReal.toReal_one, one_smul]

theorem indicatedProbability_integrable (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) :
    Integrable ((firstCell rate rewards C_star C_h u t).indicator
      (markerProbability rate rewards C_star C_h t o)) (sourceInputLaw p) := by
  have hm := (indicatedProbability_stronglyMeasurable
    rate rewards C_star C_h control0 u t o).mono
      ((sourcePrefixFiltration control0).le' (t.val + 1))
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  obtain ⟨h0, h1⟩ := indicatedProbability_bounds rate rewards C_star C_h control0 u t o z
  rw [Real.norm_of_nonneg h0]
  exact h1

/-- Conditional recording law under the original source measure. The event
remains unnormalized and all three optional outcomes remain separate. -/
theorem firstCell_marker_condExp (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
          rate rewards C_star C_h t z = o then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
    (firstCell rate rewards C_star C_h u t).indicator
      (markerProbability rate rewards C_star C_h t o) := by
  have hcond := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t (markerControlSet rate rewards C_star C_h u t o)
      (markerControlSet_measurable rate rewards C_star C_h control0 u t o)
  have htest := funext (markerControl_test rate rewards C_star C_h control0 u t o)
  have hsection := funext (markerControl_section rate rewards C_star C_h control0 u t o)
  rw [htest, hsection] at hcond
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t] using hcond

/-- The arbitrary strict-past set-integral form uses the same original
source law, without division by the probability of the first invocation. -/
theorem firstCell_marker_setIntegral (control0 : TimeControl p) (u t : Fin p.T)
    (o : Option (Option (Fin p.K))) (A0 : Set (SourceInput p))
    (hA0 : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A0) :
    (∫ z in A0, (firstCell rate rewards C_star C_h u t).indicator
      (fun y => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
        rate rewards C_star C_h t y = o then (1 : ℝ) else 0) z ∂sourceInputLaw p) =
    ∫ z in A0, (firstCell rate rewards C_star C_h u t).indicator
      (markerProbability rate rewards C_star C_h t o) z ∂sourceInputLaw p := by
  have hle := (sourcePrefixFiltration control0).le' (t.val + 1)
  have hcell : MeasurableSet (firstCell rate rewards C_star C_h u t) :=
    hle _ (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t)
  have hm : Measurable (fun z : SourceInput p =>
      if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
        rate rewards C_star C_h t z = o then (1 : ℝ) else 0) := by
    simpa only [Function.comp_def] using
      (measurable_of_countable (fun y : Option (Option (Fin p.K)) =>
        if y = o then (1 : ℝ) else 0)).comp
          (currentMarker_measurable rate rewards C_star C_h t)
  have hint : Integrable ((firstCell rate rewards C_star C_h u t).indicator
      (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
        rate rewards C_star C_h t z = o then (1 : ℝ) else 0)) (sourceInputLaw p) := by
    apply (integrable_const (1 : ℝ)).mono' (hm.indicator hcell).aestronglyMeasurable
    filter_upwards [] with z
    by_cases hz : z ∈ firstCell rate rewards C_star C_h u t
    · rw [Set.indicator_of_mem hz]
      split_ifs <;> norm_num
    · rw [Set.indicator_of_notMem hz]
      norm_num
  calc
    _ = ∫ z in A0, (sourceInputLaw p)[
        (firstCell rate rewards C_star C_h u t).indicator
          (fun y => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
            rate rewards C_star C_h t y = o then (1 : ℝ) else 0) |
        sourcePrefixFiltration control0 (t.val + 1)] z ∂sourceInputLaw p :=
      (setIntegral_condExp hle hint hA0).symm
    _ = _ := integral_congr_ae (ae_restrict_of_ae
      (firstCell_marker_condExp rate rewards C_star C_h control0 u t o))

/-- The original index, selected view and present numerical cell refer to
the same physical record. Ownership, feedback and saved logging are retained
even when the recorded arm's quantized arrival is zero. -/
theorem firstCell_physical (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (n : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (theta : Theta p) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[n]? = some r ∧
      r.input.time = t ∧ actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.rows = z.1.2 ∧ r.input.selected = selectedRowIndex p z ∧ r.input.rewards = rewards ∧
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some cell.input ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t z =
        some (ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
          r cell.selected.view.payload true) ∧
      cell.input.recordedArm =
        ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r cell.selected.view.payload true ∧
      cell.selected.view.payload.anchor = theta.2 ∧
      cell.selected.view.pendingAtChoice = Finset.univ ∧
      (∀ i, (cell.states i).status = .unoccupied ∧
        r.input.state.followers i = .ordinary (cell.states i) (cell.memories i)) ∧
      (∀ a, cell.input.recordedArm = some a → ∃ owner : Fin p.m,
        SnapshotRecordingKernel.owns p
          (.live cell.selected.view.payload.assignment
            (ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot
              cell.selected.view.payload.assignment)) owner a ∧
        (∀ other, SnapshotRecordingKernel.owns p
          (.live cell.selected.view.payload.assignment
            (ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot
              cell.selected.view.payload.assignment)) other a → other = owner) ∧
        r.output.preparation.arms.actions owner = a ∧ r.gridFeedback owner = rewards t a ∧
        (r.output.ownEntries owner).2.val.val = ((rewards t a).val : ℝ) / (ConstructorDimensions.D p : ℝ)) ∧
      (∀ i, PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.dataSlot →
        ∃ logged, ActiveFollowerLogging.checkedLogging i r.input.row
          (r.input.state.activations i) r.input.time
          (r.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          (cell.states i) = .ok logged ∧
          (r.output.followers i).downInput = some logged ∧
          logged.buffer = (cell.states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i r ∧
          ∀ saved ∈ ReferenceFollowerBufferProvenance.logEmission i r, saved ∈ logged.buffer) := by
  obtain ⟨n, r, theta, selected, c, hn, ht, hr, hrows, hj, hrewards,
    hp, hs, hchosen, hc, hread, ha, _hpos⟩ :=
    firstCell_selected rate rewards C_star C_h u t z hz
  obtain ⟨hnlt, hindex⟩ := List.getElem?_eq_some_iff.mp hn
  let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length := ⟨n, hnlt⟩
  have hget : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get k = r := hindex
  have hread' : ReferenceLaterLiveNumericalReadout.laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get k) = some c := by
    rw [hget]
    exact hread
  have physical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_physical
    rate rewards C_star C_h z k c hread'
  dsimp only at physical
  rw [hget] at physical
  obtain ⟨cell, hcell, _henabled, _hlive, _hlearning, _hrows, _hj, _hrewards,
    hphysical, _hdown, howner, _hgate, _hsaved, hlogging, _hrecording, _hcollection⟩ := physical
  have hsel : cell.selected = selected := Option.some.inj (cell.selection_actual.symm.trans hs)
  obtain ⟨theta', hcall⟩ := ReferenceFirstCollectionCurrentRemainderLaw.firstCell_call
    rate rewards C_star C_h u t z hz
  obtain ⟨ho, _hdomain, hpending, hstates⟩ :=
    ReferenceFirstCollectionCurrentRemainderLaw.firstCall_selected_domain
      rate rewards C_star C_h u t z theta' hcall r hr selected hs
  have hcanonical (i : Fin (p.m - 1)) :
      cell.states i = ReferenceLaterLiveNumericalReadout.preparedStates r ho i ∧
      cell.memories i = ReferenceLaterLiveNumericalReadout.preparedMemories r ho i := by
    have h := congrArg ReferenceLaterLiveNumericalReadout.ordinaryData
      ((cell.ordinary i).symm.trans
        (ReferenceLaterLiveNumericalReadout.prepared_configuration r ho i))
    simpa only [ReferenceLaterLiveNumericalReadout.ordinaryData,
      Option.some.injEq, Prod.mk.injEq] using h
  have hstatus (i : Fin (p.m - 1)) : (cell.states i).status = .unoccupied := by
    rw [(hcanonical i).1]
    exact (hstates i).1
  have hsnapshot : ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states =
      ReferenceFirstCollectionCurrentRemainderLaw.firstSnapshot cell.selected.view.payload.assignment := by
    apply congrArg₂ (fun missing status => (ActiveRoundActions.Snapshot.mk missing status :
      ActiveRoundActions.Snapshot cell.selected.view.payload.assignment))
    · rw [← cell.selected.pending_eq, hsel]
      exact hpending
    · exact funext hstatus
  have hc' : ReferenceFirstCollectionCurrentNumericalCell.currentCell
      rate rewards C_star C_h t z = some cell.input := hc.trans (congrArg some hcell.symm)
  have hphysical' : cell.input.recordedArm =
      ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r cell.selected.view.payload true := by
    rw [hcell]
    exact hphysical
  refine ⟨n, r, theta, cell, hn, ht, hr, hrows, hj, hrewards, hp, hchosen, hc', ?_,
    hphysical', ?_, ?_, ?_, ?_, ?_⟩
  · rw [ReferenceFirstCollectionCurrentNumericalCell.currentMarker, hc', Option.map_some, hphysical']
  · rw [hsel]
    exact ha
  · rw [hsel]
    exact hpending
  · intro i
    refine ⟨hstatus i, ?_⟩
    rw [(hcanonical i).1, (hcanonical i).2]
    exact (hstates i).2
  · rw [hsnapshot] at howner
    intro a hamark
    obtain ⟨owner, hown, huniq, haction, hfeedback, hownEntry⟩ :=
      howner a (by rw [← hcell]; exact hamark)
    exact ⟨owner, hown, huniq, haction, by simpa only [ht] using hfeedback,
      by simpa only [ht] using hownEntry⟩
  · intro i hslot
    obtain ⟨logged, hlog, hdown, hbuffer⟩ := hlogging i (hstatus i) hslot
    refine ⟨logged, hlog, hdown, hbuffer, ?_⟩
    intro saved hsaved
    rw [hbuffer]
    exact List.mem_append_right _ hsaved

/-- Explicit atoms of the fixed-vector law: no cell absence, a present
bottom, and each actual arm, irrespective of its rounded reward. -/
theorem firstCell_fixedVector_atoms (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (theta : Theta p) (_hpos : ∀ a, 0 < theta.2 a),
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      ∀ v : AssignmentVector p,
        let μ := (controlRemainderLaw p).map
          (ReferenceFirstCollectionCurrentRemainderLaw.currentMarker
            rate rewards C_star C_h control0 t z v)
        μ {none} = 0 ∧
        μ {some none} = ENNReal.ofReal
          (1 - ∑ a, CanonicalRecordingRates.xi p rate.eta.val theta.2 a) ∧
        ∀ a, μ {some (some a)} = ENNReal.ofReal
          (CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
  obtain ⟨theta, hpos, hp, hlaw⟩ :=
    firstCell_fixedVector_law rate rewards C_star C_h control0 u t z hz
  refine ⟨theta, hpos, hp, ?_⟩
  intro v
  dsimp only
  rw [hlaw v]
  have hsome : Measurable (some : Option (Fin p.K) → Option (Option (Fin p.K))) :=
    measurable_of_countable _
  constructor
  · rw [Measure.map_apply hsome (measurableSet_singleton none)]
    simp only [Set.preimage, Set.mem_singleton_iff, reduceCtorEq, Set.ofPred_false, measure_empty]
  · constructor
    · rw [Measure.map_apply hsome (measurableSet_singleton (some none))]
      simp only [Set.preimage, Set.mem_singleton_iff, Option.some.injEq]
      exact RecordedRoundMoments.recordingOutcomePMF_toMeasure_none _
    · intro a
      rw [Measure.map_apply hsome (measurableSet_singleton (some (some a)))]
      simp only [Set.preimage, Set.mem_singleton_iff, Option.some.injEq]
      exact RecordedRoundMoments.recordingOutcomePMF_toMeasure_some _ a

/-- Absence of a numerical cell is impossible at the original first call. -/
theorem firstCell_outerAbsence (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ReferenceFirstCollectionCurrentNumericalCell.currentMarker rate rewards C_star C_h t z ≠ none := by
  obtain ⟨_n, _r, _theta, _selected, c, _hn, _ht, _hr, _hrows, _hj, _hrewards,
    _hp, _hs, _hchosen, hc, _hread, _ha, _hpos⟩ :=
    firstCell_selected rate rewards C_star C_h u t z hz
  rw [ReferenceFirstCollectionCurrentNumericalCell.currentMarker, hc, Option.map_some]
  exact Option.some_ne_none _

/-- The outer-absence conditional mass is zero on the original source law. -/
theorem firstCell_outerAbsence_condExp (control0 : TimeControl p) (u t : Fin p.T) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
          rate rewards C_star C_h t z = none then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p] fun _ => 0 := by
  have hzero : markerProbability rate rewards C_star C_h t none = fun _ => 0 := by
    funext z
    unfold markerProbability
    cases calendarParameters rate rewards C_star C_h t z <;> rfl
  simpa only [hzero, Set.indicator_zero] using
    firstCell_marker_condExp rate rewards C_star C_h control0 u t none

/-- The same produced calendar anchor is retained on every actual whole-vector
and remainder replacement. Admissibility is applied anew on each original
replacement source to produce its indexed record, selection and present cell. -/
theorem firstCell_replacement_realization (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ∃ (theta : Theta p) (_hpos : ∀ a, 0 < theta.2 a),
      calendarParameters rate rewards C_star C_h t z = some theta ∧
      ∀ (v : AssignmentVector p) (w : ControlRemainder p),
        let source := ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w
        source ∈ firstCell rate rewards C_star C_h u t ∧
        calendarParameters rate rewards C_star C_h t source = some theta ∧
        ∃ (n : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r),
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[n]? = some r ∧
          r.input.time = t ∧ actualRecord rate rewards C_star C_h t source = some r ∧
          r.input.rows = source.1.2 ∧ r.input.selected = selectedRowIndex p source ∧
          r.input.rewards = rewards ∧
          ReferenceCollectionPhaseHistory.laterChosen r.input = true ∧
          ReferenceFirstCollectionCurrentNumericalCell.currentCell
            rate rewards C_star C_h t source = some cell.input ∧
          ReferenceFirstCollectionCurrentRemainderLaw.currentParameters
            rate rewards C_star C_h control0 t z v w = some (cell.selected.view, cell.selected.started) ∧
          cell.selected.view.payload.anchor = theta.2 ∧
          ReferenceFirstCollectionCurrentNumericalCell.currentMarker
            rate rewards C_star C_h t source =
            some (ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
              r cell.selected.view.payload true) := by
  obtain ⟨theta, hcall⟩ := ReferenceFirstCollectionCurrentRemainderLaw.firstCell_call
    rate rewards C_star C_h u t z hz
  have hp := ReferenceFirstCollectionCurrentRemainderLaw.firstCall_calendarParameters
    rate rewards C_star C_h u t z theta hcall
  obtain ⟨_n, _r, theta0, selected0, _c, _hn, _ht, _hr, _hrows, _hj, _hrewards,
    hp0, _hs, _hchosen, _hc, _hread, _ha, hpos0⟩ :=
    firstCell_selected rate rewards C_star C_h u t z hz
  have htheta : theta0 = theta := Option.some.inj (hp0.symm.trans hp)
  subst theta0
  refine ⟨theta, hpos0, hp, ?_⟩
  intro v w
  dsimp only
  have hz' := ReferenceFirstCollectionCurrentRemainderLaw.currentSource_firstCell
    rate rewards C_star C_h control0 u t z hz v w
  have hcall' := ReferenceFirstCollectionCurrentRemainderLaw.currentSource_firstCall
    rate rewards C_star C_h control0 u t z theta hcall v w
  have hp' := ReferenceFirstCollectionCurrentRemainderLaw.firstCall_calendarParameters
    rate rewards C_star C_h u t _ theta hcall'
  obtain ⟨n, r, theta', cell, hn, ht, hr, hrows, hj, hrewards, hparameters,
    hchosen, hc, hm, _hphysical, ha, _hpending, _hstates, _howner, _hlogging⟩ :=
    firstCell_physical rate rewards C_star C_h u t
      (ReferenceFirstCollectionCurrentRemainderLaw.currentSource control0 t z v w) hz'
  have htheta' : theta' = theta := Option.some.inj (hparameters.symm.trans hp')
  subst theta'
  refine ⟨hz', hp', n, r, cell, hn, ht, hr, hrows, hj, hrewards, hchosen, hc, ?_, ha, hm⟩
  simp only [ReferenceFirstCollectionCurrentRemainderLaw.currentParameters,
    hr, Option.bind_some, cell.selection_actual, Option.map_some]

/-- Present bottom has the complementary canonical recording mass. -/
theorem firstCell_bottom_condExp (control0 : TimeControl p) (u t : Fin p.T) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
          rate rewards C_star C_h t z = some none then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
    (firstCell rate rewards C_star C_h u t).indicator
      (fun z => match calendarParameters rate rewards C_star C_h t z with
        | none => 0
        | some theta => 1 - ∑ a, CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
  have hformula : markerProbability rate rewards C_star C_h t (some none) =
      fun z => match calendarParameters rate rewards C_star C_h t z with
      | none => 0
      | some theta => 1 - ∑ a, CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
    funext z
    unfold markerProbability
    cases calendarParameters rate rewards C_star C_h t z <;> rfl
  simpa only [hformula] using
    firstCell_marker_condExp rate rewards C_star C_h control0 u t (some none)

/-- An actual arm marker has its canonical rate, including zero rewards. -/
theorem firstCell_arm_condExp (control0 : TimeControl p) (u t : Fin p.T) (a : Fin p.K) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => if ReferenceFirstCollectionCurrentNumericalCell.currentMarker
          rate rewards C_star C_h t z = some (some a) then (1 : ℝ) else 0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
    (firstCell rate rewards C_star C_h u t).indicator
      (fun z => match calendarParameters rate rewards C_star C_h t z with
        | none => 0
        | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a) := by
  have hformula : markerProbability rate rewards C_star C_h t (some (some a)) =
      fun z => match calendarParameters rate rewards C_star C_h t z with
      | none => 0
      | some theta => CanonicalRecordingRates.xi p rate.eta.val theta.2 a := by
    funext z
    unfold markerProbability
    cases calendarParameters rate rewards C_star C_h t z <;> rfl
  simpa only [hformula] using
    firstCell_marker_condExp rate rewards C_star C_h control0 u t (some (some a))

end Bandits.Support.ReferenceFirstCollectionCurrentRecordedCell
