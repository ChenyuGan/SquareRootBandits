/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

import Mathlib.Tactic

/-!
# Actual DATA release sections on later-installation local gates

For a follower in the actual pending readout at a later-installation local
release gate, the original-source DATA control section is the assigned-arm
positive-reward mass. The source gate and pending membership are local
selectors; no predictable version of either selector is asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferencePhysicalReleaseQuota
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceOriginalInstallationReleaseDataSection

variable {p : ConstructorDimensions.Parameters}

/-- The source's actual DATA flag has its exact assigned-arm mass on every
later-installation local release gate and for every follower in that gate's
actual pending readout. The conditional-expectation identity remains the
global fixed-follower, fixed-time source-prefix identity; the local selectors
are not asserted predictable. -/
theorem actual_later_local_release_data_control_section
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (z : SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (t : Fin p.T)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z).map Prod.fst = some true)
    (i : Fin (p.m - 1))
    (hpending : i ∈ ReferenceSourcePrefixHistoryFiltration.pending
      rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source =>
            if ReferenceSourcePrefixHistoryFiltration.actualData
                rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
              control0 (t.val + 1)] =ᵐ[
                BootstrapPrivateRoundStreams.sourceInputLaw p]
          ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t ∧
        ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t z =
          ReleaseRoundKernel.chi
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i) / (2 * (p.K : ℝ)) := by
  classical
  obtain ⟨r, hr, htime, registers, owned, base, selected, originalStates,
    originalMemories, hstate, hpayload, hpendingChoice, hselection, hempty,
    hcutoff, hlive, hvalid, horiginal, hfields, _hcarried, _hnextCarried,
    _hweights, _hfast, _hactions, _hfeedback, _hcost, _hcontinuation⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame
      rate rewards C_star C_h control0 z b t hb hg
  obtain ⟨allRecord, allSelected, states, memories, hallRecord,
    hallSelection, hcontrols⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame_all_controls
      rate rewards C_star C_h control0 z b t hb hg
  have hrecordEq : allRecord = r := Option.some.inj (hallRecord.symm.trans hr)
  cases hrecordEq
  have hselectedEq : allSelected = selected :=
    Option.some.inj (hallSelection.symm.trans hselection)
  cases hselectedEq
  have hrecordRewards : r.input.rewards = rewards := by
    let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    have hstart : start ≤ t.val := by
      by_contra hnot
      have hnot' : ¬ start ≤ t.val := by omega
      simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, start, hnot'] at hr
    have hlaunch : ∃ active,
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
          some active := by
      by_cases hnone :
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none
      · have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h = [] := by
          simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
        simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, start, hstart,
          hrecords] at hr
      · cases hc : ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate z rewards C_star C_h with
        | none => exact False.elim (hnone hc)
        | some active => exact ⟨active, rfl⟩
    obtain ⟨active, hl⟩ := hlaunch
    have hget : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[t.val - start]? = some r := by
      simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, start,
        ite_eq_left hstart] using hr
    have hmem := List.mem_of_getElem? hget
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hl] at hmem
    have hspan : start + (p.T - start) ≤ p.T := by omega
    exact (ReferenceActivePhysicalHorizon.run_record_inputs active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start (p.T - start)
      hspan (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate z rewards C_star C_h active hl) r hmem).2.2
  let birth := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
  have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birth t
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    apply Option.some.inj
    simpa only [birth, ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hr,
      Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry] using hg
  have hstored : ReferenceRetainedReleasePhaseObservation.localStoredPayload
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
        some selected.view.payload := by
    rw [ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hstate,
      ReferenceAssignmentPayloadPersistence.storedPayload_live, hpayload]
  have hpendingReadout :
      ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h birth t z =
        ReferencePhysicalReleaseQuota.pendingAtStart selected.view.payload t r.input.state := by
    unfold ReferenceSourcePrefixHistoryFiltration.pending
      ReferenceSourcePrefixHistoryFiltration.entry
      ReferenceSourcePrefixHistoryFiltration.incoming
    rw [hr]
    simp [ReferenceRetainedReleasePhaseObservation.localReleaseEntry, hgate,
      hstored, ReferenceRetainedReleasePhaseObservation.localReleasePending,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
  have hpendingOriginal : i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r := by
    unfold ReferencePhysicalReleaseQuota.pendingSet
    rw [htime, ← hpendingReadout]
    exact hpending
  have hnotUnoccupied : ∀ j : Fin (p.m - 1), (states j).status ≠ .unoccupied := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfieldsBase, _, _, _, _, _, _⟩ :=
      hcontrols control0
    exact fun j => (hfieldsBase j).1
  have hpendingStatus (u : TimeControl p) : (states i).status = .pending := by
    obtain ⟨ru, vu, _hru, _hinput, hstateU, htimeU, _hselectionU, hviewU,
      _hweightsU, _hemptyU, _hcutoffU, _hliveU, horiginalU, _hfieldsU,
      hpendingU, _hfastU, _hactionsU, _hfeedbackU, _hownFeedbackU, _hcostU,
      _hcostEmptyU⟩ := hcontrols u
    have hpayloadU : registers.payload = vu.view.payload :=
      hpayload.trans (congrArg (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
        view.payload) hviewU.symm)
    have hstateCurrent : ru.input.state.coordinator = .live registers owned base := by
      rw [hstateU, hstate]
    have hpendingU' : i ∈ ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru := by
      rw [hpendingU]
      exact hpendingOriginal
    have hstart : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart vu.view.payload
        ru.input.time ru.input.state := hpendingU'
    exact (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      vu.view.payload ru.input registers owned base hstateCurrent hpayloadU
      hpendingChoice i (states i) (memories i) (horiginalU i)).mp hstart
  have hstatus : ∀ j : Fin (p.m - 1),
      (states j).status = .pending ∨ (states j).status = .released := by
    intro j
    cases hstatus : (states j).status with
    | unoccupied => exact False.elim (hnotUnoccupied j hstatus)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let E : Set (ContinuousControlSlice.Slice p.m p.K) := {slice |
    PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.dataSlot ∧
      PublicDiscreteDraws.pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) slice =
          selected.view.payload.assignment.assigned i ∧
      0 < row.val (selected.view.payload.assignment.assigned i)}
  have hE : MeasurableSet E := by
    exact (measurableSet_eq_fun PublicDiscreteDraws.measurable_slotDraw measurable_const).inter
      ((measurableSet_eq_fun
        (PublicDiscreteDraws.measurable_pilotDraw (K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m)) measurable_const).inter
        (MeasurableSet.const _))
  let kernelInputAt (slice : ContinuousControlSlice.Slice p.m p.K) :=
    ReleaseRoundKernel.releaseRoundInput p selected.view.payload.assignment
      selected.view.payload.slowSet selected.view.payload.assignment_image.symm
      rate.eta rate.eta.property selected.view.payload.eta_le_source_cap
      selected.view.payload.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      selected.view.payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).2.2) slice
  have hcontrolDataGeometry (u : ContinuousLearningRows.TimeControl p) :
      (ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) = true ↔
        u.1 ∈ E) ∧
      (ActiveRoundActions.releaseObservation p.two_le_m
          (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
          (kernelInputAt u.1) row i ∧ (kernelInputAt u.1).slot =
            PublicDiscreteDraws.dataSlot ↔ u.1 ∈ E) := by
    obtain ⟨ru, vu, hru, hinput, hstateU, htimeU, hselectionU, hviewU,
      hweightsU, hemptyU, _hcutoffU, hliveU, horiginalU, hfieldsU,
      hpendingU, _hfastU, _hactionsU, _hfeedbackU, hownFeedbackU, _hcostU,
      _hcostEmptyU⟩ := hcontrols u
    have hpayloadEq : vu.view.payload = selected.view.payload :=
      congrArg (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
        view.payload) hviewU
    have hpayloadU : registers.payload = vu.view.payload := hpayload.trans hpayloadEq.symm
    have hstateCurrent : ru.input.state.coordinator = .live registers owned base := by
      rw [hstateU, hstate]
    have hpendingU' : i ∈ ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru := by
      rw [hpendingU]
      exact hpendingOriginal
    have hstart : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart vu.view.payload
        ru.input.time ru.input.state := hpendingU'
    have hiState : (states i).status = .pending :=
      (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
        vu.view.payload ru.input registers owned base hstateCurrent hpayloadU
        hpendingChoice i (states i) (memories i) (horiginalU i)).mp hstart
    have hpreparedSelection :
        (ReferenceActivePhysicalStep.prepare ru.input).coordinator.selection = some vu := by
      simpa only [ru.output_eq, ReferenceActivePhysicalStep.step] using hselectionU
    have hvalidU : CoordinatorLocalArmChoice.ChoiceInputsValid vu.view.payload
        vu.view.cutoff ru.input.time vu.view.complementWeights :=
      ReferenceLaterLiveNumericalReadout.selection_choiceValid vu
    -- `dataFlag` tests this record's literal `ownEntries` observation. The
    -- checked geometry uses `own_observation_eq` to pass to prepared feedback.
    have hframeFlags := ReferenceFirstLiveReleaseSliceMass.actual_release_flags_and_kernel_events_iff
      ru vu hpreparedSelection states memories horiginalU hfieldsU hvalidU hliveU
      hemptyU i hiState
    have hcurrentSlice : (ru.input.row.2 ru.input.time).1 = u.1 := by
      rw [hinput]
      rw [ReferenceLaterOptionalControlResampling.withControl_time,
        ReferenceLaterOptionalControlResampling.withControl_currentControl]
    have hrow : ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
        ru.input.rewards ru.input.time = row := by
      rw [hinput, ReferenceLaterOptionalControlResampling.withControl_rewards,
        ReferenceLaterOptionalControlResampling.withControl_time,
        hrecordRewards, htime]
    have hkernelEvent :
        ReferenceFirstLiveReleaseSliceMass.dataKernelEvent vu hvalidU states
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
              ru.input.rewards ru.input.time) i (ru.input.row.2 ru.input.time).1 ↔
          (ActiveRoundActions.releaseObservation p.two_le_m
            (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
            (kernelInputAt u.1) row i ∧
              (kernelInputAt u.1).slot = PublicDiscreteDraws.dataSlot) := by
      rw [hcurrentSlice, hrow]
      let event (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
          (bounds : ∀ a,
            0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
              view.payload view.complementWeights a ∧
            view.payload.anchor a ≤
              ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
                view.payload view.complementWeights a ∧
            ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
                view.payload view.complementWeights a ≤ 2 * view.payload.anchor a) : Prop :=
        ActiveRoundActions.releaseObservation p.two_le_m
          (ReferenceFirstLiveReleaseSliceMass.payloadSnapshot
            view.payload view.pendingAtChoice states)
          (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData
            view.payload view.complementWeights bounds u.1) row i ∧
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData
          view.payload view.complementWeights bounds u.1).slot = PublicDiscreteDraws.dataSlot
      have htransport (view₁ view₂ : ReferenceDownReception.ChoiceTimeView p rate.eta)
          (heq : view₁ = view₂) (bounds₁ bounds₂) :
          event view₁ bounds₁ ↔ event view₂ bounds₂ := by
        cases heq
        rfl
      exact htransport vu.view selected.view hviewU
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds vu hvalidU)
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid)
    have hconditions :
        ReferenceFirstLiveReleaseSliceMass.dataKernelConditions vu hvalidU i
            (ru.input.row.2 ru.input.time).1
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
              ru.input.rewards ru.input.time) ↔ u.1 ∈ E := by
      rw [hcurrentSlice, hrow]
      change (PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot ∧
        PublicDiscreteDraws.pilotDraw (K_pos p)
            (ActiveRoundActions.coordinator p.two_le_m) u.1 =
          vu.view.payload.assignment.assigned i ∧
        0 < row.val (vu.view.payload.assignment.assigned i)) ↔ u.1 ∈ E
      rw [hpayloadEq]
      rfl
    have hactualFlag :
        ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) = true ↔
        ReferencePhysicalReleaseQuota.dataFlag vu.view.payload ru i = true := by
      let sourceC := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
      let sourceA := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t sourceC u
      let sourceB := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
      have hprefix : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
          (t.val + 1) sourceA =
            ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) sourceB := by
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · funext q
            by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
            · subst q
              simp only [sourceA, sourceB, sourceC,
                ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
                ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
                ReferenceSourceCurrentControlFreshness.c_t,
                ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
                ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
                ActualInitializationPhysicalStep.selectedRowIndex,
                Function.update_self]
              refine Prod.ext rfl ?_
              funext v
              by_cases hv : v = t
              · subst v
                simp only [Function.update_self]
              · have hv' : v.val ≠ t.val := fun h => hv (Fin.ext h)
                by_cases hbefore : v.val < t.val
                · simp only [Function.update_of_ne hv, hbefore, ite_true]
                · have hafter : ¬ v.val < t.val + 1 := by omega
                  simp only [hafter, ite_false]
            · have hq' : q ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 := hq
              simp only [sourceA, sourceB, sourceC,
                ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
                ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
                ReferenceSourceCurrentControlFreshness.c_t,
                ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
                ActualInitializationPhysicalStep.selectedRowIndex,
                ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
                Function.update_of_ne hq']
        · rfl
      have hfactorA := ReferenceSourcePrefixHistoryFiltration.flags_factor
        rate rewards C_star C_h control0 i t sourceA
      have hfactorB := ReferenceSourcePrefixHistoryFiltration.flags_factor
        rate rewards C_star C_h control0 i t sourceB
      have hdataSource : ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t sourceA =
          ReferenceSourcePrefixHistoryFiltration.actualData
            rate rewards C_star C_h i t sourceB := by
        rw [hfactorA.2.1, hfactorB.2.1, hprefix]
      have hactualFlagOnB :
          ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t sourceB = true ↔
            ReferencePhysicalReleaseQuota.dataFlag vu.view.payload ru i = true := by
        unfold ReferenceSourcePrefixHistoryFiltration.actualData
        rw [hru]
        simp only [Option.bind_some, hstateCurrent,
          ReferenceAssignmentPayloadPersistence.storedPayload_live, hpayloadU,
          Option.map_some, Option.getD_some]
      change ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t sourceA = true ↔ _
      rw [hdataSource]
      exact hactualFlagOnB
    have hflagEvent := hframeFlags.2.1
    have heventCondition := hframeFlags.2.2.2
    exact ⟨hactualFlag.trans (hflagEvent.trans (heventCondition.trans hconditions)),
      hkernelEvent.symm.trans (heventCondition.trans hconditions)⟩
  have hkernelSet :
      {slice : ContinuousControlSlice.Slice p.m p.K |
        ActiveRoundActions.releaseObservation p.two_le_m
          (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
          (kernelInputAt slice) row i ∧
        (kernelInputAt slice).slot = PublicDiscreteDraws.dataSlot} = E := by
    ext slice
    let u : ContinuousLearningRows.TimeControl p :=
      (slice, fun _ : ContinuousLearningRows.Channel p =>
        (fun _ : Fin (ContinuousLearningRows.B p) => (0 : AffineChannelLaw.Bit),
          (0 : AffineChannelLaw.Bit)))
    simpa only [u, Set.mem_ofPred_eq] using (hcontrolDataGeometry u).2
  have hprob := ReleaseRoundKernel.actual_data_release_probability p
    selected.view.payload.assignment
    (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states) row
    rate.eta rate.eta.property selected.view.payload.eta_le_source_cap
    selected.view.payload.anchor
    (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
    selected.view.payload.anchor_pos
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
      selected hvalid a).1)
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
      selected hvalid a).2.1)
    (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
      selected hvalid a).2.2)
    selected.view.payload.slowSet selected.view.payload.assignment_image.symm
    hempty hstatus i (hpendingStatus control0)
  have hmass : (ContinuousControlSlice.sliceLaw p.m p.K) E =
      ENNReal.ofReal (ReleaseRoundKernel.chi row
        (selected.view.payload.assignment.assigned i) / (2 * (p.K : ℝ))) := by
    rw [← hkernelSet]
    simpa only [kernelInputAt] using hprob
  have hwhole : ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' E) =
      ContinuousControlSlice.sliceLaw p.m p.K E :=
    (ContinuousLearningRows.measurePreserving_slice p).measure_preimage hE.nullMeasurableSet
  have hintegral :
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z =
          (ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' E)).toReal := by
    unfold ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSectionIntegrand
    have hfun :
        (fun control : TimeControl p =>
          if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control)
          then (1 : ℝ) else 0) =
        (Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
      funext control
      simp only [Set.indicator, Set.mem_preimage]
      exact if_congr (hcontrolDataGeometry control).1 rfl rfl
    rw [hfun]
    exact integral_indicator_one (hE.preimage measurable_fst)
  have hnonneg :
      0 ≤ ReleaseRoundKernel.chi row (selected.view.payload.assignment.assigned i) /
        (2 * (p.K : ℝ)) := by
    unfold ReleaseRoundKernel.chi
    split_ifs <;> positivity
  have hsection :
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z =
        ReleaseRoundKernel.chi row
          (selected.view.payload.assignment.assigned i) / (2 * (p.K : ℝ)) := by
    rw [hintegral, hwhole, hmass, ENNReal.toReal_ofReal hnonneg]
  exact ⟨r, selected, hr, hselection,
    ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
      rate rewards C_star C_h control0 i t,
    hsection⟩

/-- Specialize the global fixed-follower, fixed-time conditional identity only
on its almost-everywhere set. The dependent installation index and the actual
release/pending selectors are introduced afterwards, so no predictability of
these selectors or random conditional-expectation label is used. -/
theorem actual_later_local_release_data_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length),
      ReferenceCollectionPhaseHistory.laterChosen
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input = true →
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t z).map Prod.fst = some true →
      i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t z →
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
          ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t z = some r ∧
          r.output.preparation.coordinator.selection = some selected ∧
          ((BootstrapPrivateRoundStreams.sourceInputLaw p)[
            (fun source =>
              if ReferenceSourcePrefixHistoryFiltration.actualData
                  rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
              ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
                control0 (t.val + 1)]) z =
            ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i) / (2 * (p.K : ℝ)) := by
  filter_upwards [ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
    rate rewards C_star C_h control0 i t] with z hz
  intro b hb hg hpending
  obtain ⟨r, selected, hr, hselection, _hglobal, hsection⟩ :=
    actual_later_local_release_data_control_section
      rate rewards C_star C_h control0 z b t hb hg i hpending
  exact ⟨r, selected, hr, hselection, hz.trans hsection⟩

end Bandits.Support.ReferenceOriginalInstallationReleaseDataSection

end
