/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

import Mathlib.Tactic

/-!
# Actual UP section on an original local release gate

Sources: `sources/zip4/manuscript/05_binary_transport.tex:293-349` and
`sources/zip4/manuscript/06_interruptions.tex:489-490`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical ENNReal

namespace Bandits.Support.ReferenceOriginalInstallationReleaseUpSection

variable {p : Parameters}

private theorem actualRecord_input_rewards
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rewards = rewards := by
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
    by_cases hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val
    · exact hs
    · simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hs] at hr
  have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
    cases hx : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing with
    | none =>
        have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_no_crossing
          rate rewards C_star C_h t z hx
        rw [hnone] at hr
        cases hr
    | some c => rfl
  let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active := by
    simpa only [active] using
      ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hcross
  have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z active hlaunch hstart
  have heq := Option.some.inj (hr.symm.trans hrecord)
  subst r
  rfl

private theorem choiceView_complementWeights_heq
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (view₁ view₂ : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : view₁ = view₂) : HEq view₁.complementWeights view₂.complementWeights := by
  cases hview
  rfl

private theorem upKernelEventData_congr
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (pending₁ pending₂ : Finset (ActiveRoundActions.Follower p.m))
    (hpending : pending₁ = pending₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (bounds₁ : ∀ a, 0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
      payload₁ weights₁ a ∧ payload₁.anchor a ≤
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload₁ weights₁ a ∧
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload₁ weights₁ a ≤
        2 * payload₁.anchor a)
    (bounds₂ : ∀ a, 0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
      payload₂ weights₂ a ∧ payload₂.anchor a ≤
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload₂ weights₂ a ∧
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload₂ weights₂ a ≤
        2 * payload₂.anchor a)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (row₁ row₂ : ActiveRoundActions.RewardRow p.K) (hrow : row₁ = row₂)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K) :
    (ActiveRoundActions.releaseObservation p.two_le_m
        (ReferenceFirstLiveReleaseSliceMass.payloadSnapshot payload₁ pending₁ states)
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData payload₁ weights₁ bounds₁ slice)
        row₁ i ∧
      (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData payload₁ weights₁ bounds₁ slice).slot =
        PublicDiscreteDraws.upSlot) ↔
    (ActiveRoundActions.releaseObservation p.two_le_m
        (ReferenceFirstLiveReleaseSliceMass.payloadSnapshot payload₂ pending₂ states)
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData payload₂ weights₂ bounds₂ slice)
        row₂ i ∧
      (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData payload₂ weights₂ bounds₂ slice).slot =
        PublicDiscreteDraws.upSlot) := by
  cases hpayload
  cases hpending
  cases hweights
  cases hrow
  rfl

/-- On every actual later-installation local-release gate, the literal UP
section for a locally pending follower is the exact current-weight release
mass and satisfies the source lower bound. The selected record and follower
frame are constructed from the original source; only `i`'s local pending
membership is a caller selector. -/
theorem actualUpControlSection_on_later_local_release
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (t : Fin p.T)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z).map Prod.fst = some true)
    (i : Fin (p.m - 1))
    (hi : i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val) t z) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z =
        ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) ∧
      ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          selected.view.payload.assignment.auxiliary /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := by
  classical
  let birth := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
  obtain ⟨r, hr, htime, registers, owned, base, selected, states, memories,
    hstate, hpayload, hregisterPending, hselection, hempty, hcutoff, hlive, hvalid,
    hord, hfields, hcarried, hnextCarried, hweights, hfast, hactions, hfeedback,
    hcost, dispatched, hstart, continuation, arm, hcoord⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame
      rate rewards C_star C_h control0 z b t hb hg
  obtain ⟨rAll, selectedAll, statesAll, memoriesAll, hrAll, hselectionAll, hcontrols⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame_all_controls
      rate rewards C_star C_h control0 z b t hb hg
  have hrecordEq : rAll = r := Option.some.inj (hrAll.symm.trans hr)
  subst rAll
  have hselectedEq : selectedAll = selected :=
    Option.some.inj (hselectionAll.symm.trans hselection)
  subst selectedAll

  let originalControl :=
    (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t
  have hreplaceOriginal :
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z originalControl = z := by
    dsimp only [originalControl]
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex p z]
    exact ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p t z
  obtain ⟨r0, _selected0, hr0, _hinput0, _hstate0, _htime0, _hsel0, _hview0, _hw0,
    _hempty0, _hcut0, _hlive0, hord0, _hfields0, _hpending0, _hfast0, _hactions0,
    _hfeedback0, _hown0, _hcost0, _hnone0⟩ := hcontrols originalControl
  have hr0' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r0 := by
    simpa only [hreplaceOriginal] using hr0
  have hr0Eq : r0 = r := Option.some.inj (hr0'.symm.trans hr)
  subst r0
  have hstatesEq : statesAll = states := by
    funext j
    have hconfig :=
      (hord j).symm.trans (hord0 j)
    injection hconfig with hstateEq _
    exact hstateEq.symm
  have hmemoriesEq : memoriesAll = memories := by
    funext j
    have hconfig :=
      (hord j).symm.trans (hord0 j)
    injection hconfig with _ hmemoryEq
    exact hmemoryEq.symm
  subst statesAll
  subst memoriesAll

  have hgate : ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birth t
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = true := by
    have h := hg
    unfold ReferenceSourcePrefixHistoryFiltration.entry
      ReferenceSourcePrefixHistoryFiltration.incoming at h
    rw [hr] at h
    simpa [ReferenceRetainedReleasePhaseObservation.localReleaseEntry] using h
  have hstored : ReferenceRetainedReleasePhaseObservation.localStoredPayload
      (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) = some selected.view.payload := by
    rw [ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded]
    simp [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState,
      ReferenceAssignmentPayloadPersistence.storedPayload, hstate, hpayload]
  have hentry : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birth t z =
      some (true, some (ReferencePhysicalReleaseQuota.pendingAtStart
        selected.view.payload t r.input.state)) := by
    unfold ReferenceSourcePrefixHistoryFiltration.entry
      ReferenceSourcePrefixHistoryFiltration.incoming
    rw [hr]
    simp only [Option.map_some]
    unfold ReferenceRetainedReleasePhaseObservation.localReleaseEntry
    simp [hgate, hstored, ReferenceRetainedReleasePhaseObservation.localReleasePending,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
  have hipendingAtStart : i ∈ ReferencePhysicalReleaseQuota.pendingAtStart
      selected.view.payload t r.input.state := by
    have h := hi
    unfold ReferenceSourcePrefixHistoryFiltration.pending at h
    rw [hentry] at h
    exact h
  have hipendingState : (states i).status = .pending := by
    apply (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      selected.view.payload r.input registers owned base hstate hpayload hregisterPending
      i (states i) (memories i) (hord i)).mp
    simpa [htime] using hipendingAtStart

  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let payload := selected.view.payload
  let weights := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected
  let bounds := fun a => ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid a
  let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states
  have hmissing : snapshot.missing = ∅ := by
    change selected.view.pendingAtChoice = ∅
    exact hempty
  have hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released := by
    intro j
    change (states j).status = .pending ∨ (states j).status = .released
    cases hs : (states j).status with
    | unoccupied => exact False.elim ((hfields j).1 hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hm : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
  have hcompleteDef : ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected =
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        selected.view.payload selected.view.complementWeights := rfl
  let event : Set (ContinuousControlSlice.Slice p.m p.K) :=
    {x | ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected hvalid states row i x}
  have hkernelMass := ReleaseRoundKernel.actual_up_release_probability p
    payload.assignment snapshot row rate.eta rate.eta.property payload.eta_le_source_cap
    payload.anchor weights payload.anchor_pos (fun a => (bounds a).1)
    (fun a => (bounds a).2.1) (fun a => (bounds a).2.2) payload.slowSet
    payload.assignment_image.symm hmissing hstatus i hipendingState
  have hprob : ContinuousControlSlice.sliceLaw p.m p.K event =
      ENNReal.ofReal (ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
        selected hvalid row) := by
    simpa [event, snapshot, weights, bounds, payload, row,
      ReferenceFirstLiveReleaseSliceMass.upKernelEvent,
      ReferenceFirstLiveReleaseSliceMass.releaseKernelInput,
      ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData,
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula,
      hcompleteDef, PublicDiscreteDraws.followerCount, Nat.cast_sub hm] using hkernelMass

  let actualEvent : Set (ContinuousLearningRows.TimeControl p) :=
    {u | ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) = true}
  have hflag_at_control : ∀ u : ContinuousLearningRows.TimeControl p,
      u ∈ actualEvent ↔ u.1 ∈ event := by
    intro u
    let replaced := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
    obtain ⟨ru, vu, hru, hinput, hstateU, htimeU, hselectionU, hviewU,
      hweightsU, hemptyU, hcutoffU, hliveU, hordU, hfieldsU, hpendingU,
      hfastU, hactionsU, hfeedbackU, hownU, hcostU, hnoneU⟩ := hcontrols u
    have hruRewards : ru.input.rewards = rewards :=
      actualRecord_input_rewards rate rewards C_star C_h t replaced ru hru
    have hrowU : ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow ru.input.rewards ru.input.time = row := by
      simp [row, hruRewards, htimeU]
    have hstateU' : ru.input.state.coordinator = .live registers owned base := by
      rw [hstateU, hstate]
    have hstoredU : ReferenceAssignmentPayloadPersistence.storedPayload
        ru.input.state.coordinator = some payload := by
      simp [ReferenceAssignmentPayloadPersistence.storedPayload, hstateU', hpayload, payload]
    have hflag : ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t replaced =
        ReferencePhysicalReleaseQuota.upFlag payload ru i := by
      unfold ReferenceSourcePrefixHistoryFiltration.actualUp
      rw [hru]
      simp [hstoredU, payload]
    have hvalidU : CoordinatorLocalArmChoice.ChoiceInputsValid vu.view.payload
        vu.view.cutoff ru.input.time vu.view.complementWeights := by
      rw [hviewU, htimeU, ← htime]
      exact hvalid
    have hselectionPrepared : (ReferenceActivePhysicalStep.prepare ru.input).coordinator.selection =
        some vu := by
      simpa only [ru.output_eq, ReferenceActivePhysicalStep.step] using hselectionU
    have hflags := ReferenceFirstLiveReleaseSliceMass.actual_release_flags_and_kernel_events_iff
      ru vu hselectionPrepared states memories hordU hfieldsU hvalidU hliveU hemptyU i hipendingState
    let slice := (ru.input.row.2 ru.input.time).1
    have hslice : slice = u.1 := by
      dsimp only [slice]
      rw [hinput, ReferenceLaterOptionalControlResampling.withControl_row,
        ReferenceLaterOptionalControlResampling.withControl_time]
      simp [Function.update_self]
    have hpayloadU : vu.view.payload = selected.view.payload := congrArg
      (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.payload) hviewU
    have hpendingView : vu.view.pendingAtChoice = selected.view.pendingAtChoice := congrArg
      (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta => view.pendingAtChoice) hviewU
    have hboundsU : ∀ a,
        0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
          vu.view.payload vu.view.complementWeights a ∧
        vu.view.payload.anchor a ≤
          ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
            vu.view.payload vu.view.complementWeights a ∧
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
          vu.view.payload vu.view.complementWeights a ≤ 2 * vu.view.payload.anchor a := by
      intro a
      change 0 < ReferenceFirstLiveReleaseGeometry.completeCurrentWeights vu a ∧
        vu.view.payload.anchor a ≤ ReferenceFirstLiveReleaseGeometry.completeCurrentWeights vu a ∧
        ReferenceFirstLiveReleaseGeometry.completeCurrentWeights vu a ≤ 2 * vu.view.payload.anchor a
      rw [hweightsU]
      simpa only [hpayloadU] using bounds a
    have hcomplementWeightsHEq := choiceView_complementWeights_heq vu.view selected.view hviewU
    have hflagsU : ReferencePhysicalReleaseQuota.upFlag payload ru i = true ↔
        ReferenceFirstLiveReleaseSliceMass.upKernelEvent vu hvalidU states row i slice := by
      have h := hflags.1
      rw [hrowU] at h
      simpa [payload, ← hpayloadU] using h
    have hevent : ReferenceFirstLiveReleaseSliceMass.upKernelEvent vu hvalidU states row i slice ↔
        ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected hvalid states row i slice := by
      change (ActiveRoundActions.releaseObservation p.two_le_m
          (ReferenceFirstLiveReleaseSliceMass.payloadSnapshot vu.view.payload
            vu.view.pendingAtChoice states)
          (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData vu.view.payload
            vu.view.complementWeights
            (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds vu hvalidU) slice)
          row i ∧
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData vu.view.payload
          vu.view.complementWeights
          (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds vu hvalidU) slice).slot =
          PublicDiscreteDraws.upSlot) ↔
        (ActiveRoundActions.releaseObservation p.two_le_m
          (ReferenceFirstLiveReleaseSliceMass.payloadSnapshot selected.view.payload
            selected.view.pendingAtChoice states)
          (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData selected.view.payload
            selected.view.complementWeights bounds slice)
          row i ∧
        (ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData selected.view.payload
          selected.view.complementWeights bounds slice).slot = PublicDiscreteDraws.upSlot)
      exact upKernelEventData_congr vu.view.payload selected.view.payload hpayloadU
        vu.view.pendingAtChoice selected.view.pendingAtChoice hpendingView
        vu.view.complementWeights selected.view.complementWeights hcomplementWeightsHEq
        hboundsU
        bounds states row row rfl i slice
    have hflagToEvent : ReferencePhysicalReleaseQuota.upFlag payload ru i = true ↔
        ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected hvalid states row i slice := by
      exact hflagsU.trans hevent
    have hprefix := ReferenceFirstLiveActualFlagSections.actual_flags_after_prefix_restore
      rate rewards C_star C_h control0 i t z u
    have hrestore : ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) =
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t replaced := by
      simpa only [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
        replaced] using hprefix.1.symm
    change ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) = true ↔ _
    rw [hrestore, hflag]
    change ReferencePhysicalReleaseQuota.upFlag payload ru i = true ↔
      ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected hvalid states row i u.1
    simpa only [hslice] using hflagToEvent

  have hmeasActual : MeasurableSet actualEvent := by
    have hf : Measurable (fun u : ContinuousLearningRows.TimeControl p =>
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand
          rate rewards C_star C_h i t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, u)) :=
      (ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand_measurable
        rate rewards C_star C_h control0 i t).comp (measurable_const.prodMk measurable_id)
    have heq : actualEvent = (fun u : ContinuousLearningRows.TimeControl p =>
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand
          rate rewards C_star C_h i t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, u)) ⁻¹' ({1} : Set ℝ) := by
      ext u
      simp [actualEvent, ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand]
    rw [heq]
    exact (measurableSet_singleton (1 : ℝ)).preimage hf
  have hpreimage : actualEvent =
      (Prod.fst : ContinuousLearningRows.TimeControl p → ContinuousControlSlice.Slice p.m p.K) ⁻¹' event := by
    ext u
    exact hflag_at_control u
  have heventMeas : MeasurableSet event := by
    let affine : ContinuousLearningRows.AffineSamples p :=
      fun _ => ((fun _ => (0 : AffineChannelLaw.Bit)), 0)
    have hsection := hmeasActual.preimage
      (measurable_id.prodMk (measurable_const : Measurable fun _ : ContinuousLearningRows.Slice p => affine))
    simpa [hpreimage, event, affine] using hsection

  have hsection : ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z =
      (ContinuousLearningRows.timeControlLaw p
        ((Prod.fst : ContinuousLearningRows.TimeControl p →
          ContinuousControlSlice.Slice p.m p.K) ⁻¹' event)).toReal := by
    unfold ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
    calc
      (∫ control, ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand
          rate rewards C_star C_h i t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, control)
          ∂ContinuousLearningRows.timeControlLaw p) =
        ∫ control, if control.1 ∈ event then (1 : ℝ) else 0
          ∂ContinuousLearningRows.timeControlLaw p := by
            apply integral_congr_ae
            filter_upwards [] with control
            have heq := hflag_at_control control
            by_cases hf : ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
                (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                  (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control) = true
            · have hmem : control ∈ actualEvent := by
                simpa [actualEvent] using hf
              have hevent' := heq.mp hmem
              simp [ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand, hf, hevent']
            · have hnot : control.1 ∉ event := fun he =>
                hf (by simpa [actualEvent] using heq.mpr he)
              have hfalse : ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
                  (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                    (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control) = false :=
                Bool.eq_false_iff.mpr hf
              simp [ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand,
                hfalse, hnot]
      _ = (ContinuousLearningRows.timeControlLaw p
          ((Prod.fst : ContinuousLearningRows.TimeControl p →
            ContinuousControlSlice.Slice p.m p.K) ⁻¹' event)).toReal := by
            have hindicator : (fun control : ContinuousLearningRows.TimeControl p =>
                if control.1 ∈ event then (1 : ℝ) else 0) =
                ((Prod.fst : ContinuousLearningRows.TimeControl p →
                  ContinuousControlSlice.Slice p.m p.K) ⁻¹' event).indicator (fun _ => (1 : ℝ)) := by
              funext control
              simp [Set.indicator]
            rw [hindicator]
            exact integral_indicator_one (heventMeas.preimage measurable_fst)

  have hmap : ContinuousLearningRows.timeControlLaw p
      ((Prod.fst : ContinuousLearningRows.TimeControl p →
        ContinuousControlSlice.Slice p.m p.K) ⁻¹' event) =
      ContinuousControlSlice.sliceLaw p.m p.K event := by
    rw [← Measure.map_apply measurable_fst heventMeas,
      ContinuousLearningRows.map_slice p]

  have hchi : 0 ≤ ReleaseRoundKernel.chi row payload.assignment.auxiliary := by
    unfold ReleaseRoundKernel.chi
    split <;> norm_num
  have hd : 0 < (p.m - 1 : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt
      (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m))
  have hK : 0 < (p.K : ℝ) := by exact_mod_cast ConstructorDimensions.K_pos p
  let denominator := ((p.m : ℝ) - 1) * (p.K : ℝ)
  have hden : 0 < denominator := mul_pos hd hK
  let e := ReleaseRoundKernel.auxiliaryFastArm payload.assignment payload.slowSet
    payload.assignment_image.symm
  have he : e.1 = payload.auxiliaryArm := by
    change payload.assignment.auxiliary = payload.auxiliaryArm
    rfl
  have hmin : ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
      payload.anchor e.1 ≤ payload.anchor j.1 := by
    intro j
    rw [he]
    exact payload.auxiliaryArm_anchor_minimum j.1 j.property
  have hq := CanonicalFastSampling.qGamma_auxiliary_arm_le_two_thirds
    p rate.eta.property payload.eta_le_source_cap payload.anchor weights
    payload.anchor_pos (fun a => (bounds a).1) (fun a => (bounds a).2.1)
    (fun a => (bounds a).2.2) payload.slowSet e hmin
  have hthird : (1 : ℝ) / 3 ≤ 1 - CanonicalFastSampling.qGamma p rate.eta
      rate.eta.property payload.eta_le_source_cap payload.anchor weights
      payload.anchor_pos (fun a => (bounds a).1) (fun a => (bounds a).2.1)
      (fun a => (bounds a).2.2) payload.slowSet e := by
    linarith
  have hfrac : 1 / (12 * denominator) ≤
      (1 - CanonicalFastSampling.qGamma p rate.eta rate.eta.property
        payload.eta_le_source_cap payload.anchor weights payload.anchor_pos
        (fun a => (bounds a).1) (fun a => (bounds a).2.1)
        (fun a => (bounds a).2.2) payload.slowSet e) / (4 * denominator) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 12 * denominator)
      (by positivity : (0 : ℝ) < 4 * denominator)).2
    have hscaled := mul_le_mul_of_nonneg_right hthird (by positivity : (0 : ℝ) ≤ 12 * denominator)
    nlinarith
  have hformulaLower : ReleaseRoundKernel.chi row payload.assignment.auxiliary /
        (12 * denominator) ≤
      ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected hvalid row := by
    rw [ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula]
    have hmassTarget : ReleaseRoundKernel.chi row payload.assignment.auxiliary /
        (12 * denominator) ≤
      ReleaseRoundKernel.chi row payload.assignment.auxiliary *
        (1 - CanonicalFastSampling.qGamma p rate.eta rate.eta.property
          payload.eta_le_source_cap payload.anchor weights payload.anchor_pos
          (fun a => (bounds a).1) (fun a => (bounds a).2.1)
          (fun a => (bounds a).2.2) payload.slowSet e) / (4 * denominator)
        := by
      have hmul := mul_le_mul_of_nonneg_left hfrac hchi
      calc
        _ = ReleaseRoundKernel.chi row payload.assignment.auxiliary *
            (1 / (12 * denominator)) := by ring
        _ ≤ ReleaseRoundKernel.chi row payload.assignment.auxiliary *
            ((1 - CanonicalFastSampling.qGamma p rate.eta rate.eta.property
              payload.eta_le_source_cap payload.anchor weights payload.anchor_pos
              (fun a => (bounds a).1) (fun a => (bounds a).2.1)
              (fun a => (bounds a).2.2) payload.slowSet e) / (4 * denominator)) := hmul
        _ = _ := by ring
    convert hmassTarget using 1
    simp [payload, weights, denominator, e]
    ring
  have hmassNonneg : 0 ≤ ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected hvalid row :=
    le_trans (div_nonneg hchi (by positivity)) hformulaLower
  have hsectionExact :
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z =
      ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected hvalid row := by
    rw [hsection, hmap, hprob, ENNReal.toReal_ofReal hmassNonneg]
  have hlowerReal : ReleaseRoundKernel.chi row payload.assignment.auxiliary /
        (12 * denominator) ≤
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z := by
    rw [hsectionExact]
    exact hformulaLower
  refine ⟨r, selected, hr, hselection, ?_, ?_⟩
  · simpa [row, hvalid] using hsectionExact
  · convert hlowerReal using 1
    simp [row, payload, denominator]
    ring

/-- The fixed-time conditional expectation of the actual UP flag is the
literal UP section almost everywhere. At every source in that same
almost-everywhere set, any actual later-installation local-release selector
and pending follower recover the original record, selected payload, current
weights, exact release mass, and its source lower bound. -/
theorem actualUpControlSection_condExp_on_later_local_release
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun source =>
          if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] z =
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z ∧
      ∀ (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).length)
        (_hb : ReferenceCollectionPhaseHistory.laterChosen
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[b.val].input = true)
        (_hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t z).map Prod.fst = some true)
        (_hi : i ∈ ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
          t z),
        ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (selected : ReferenceActivePhysicalStep.Selection r.input),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
            some r ∧
          r.output.preparation.coordinator.selection = some selected ∧
          (∀ a,
            0 < ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
            selected.view.payload.anchor a ≤
              ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
            ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ≤
              2 * selected.view.payload.anchor a) ∧
          (BootstrapPrivateRoundStreams.sourceInputLaw p)[
            (fun source =>
              if ReferenceSourcePrefixHistoryFiltration.actualUp
                rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
              ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
                control0 (t.val + 1)] z =
            ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected
              (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) ∧
          ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              selected.view.payload.assignment.auxiliary /
                (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
            (BootstrapPrivateRoundStreams.sourceInputLaw p)[
              (fun source =>
                if ReferenceSourcePrefixHistoryFiltration.actualUp
                  rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
                ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
                  control0 (t.val + 1)] z := by
  have hcond := ReferenceSourcePhysicalFlagConditionalLaw.actual_up_condExp
    rate rewards C_star C_h control0 i t
  filter_upwards [hcond] with z hcondz
  refine ⟨hcondz, ?_⟩
  intro b _hb _hg _hi
  obtain ⟨r, selected, hr, hselection, hsection, hlower⟩ :=
    actualUpControlSection_on_later_local_release
      rate rewards C_star C_h control0 z b t _hb _hg i _hi
  have hweights : ∀ a,
      0 < ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
      selected.view.payload.anchor a ≤
        ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ≤
        2 * selected.view.payload.anchor a := by
    intro a
    exact ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) a
  have hmass :
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun source =>
          if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
            control0 (t.val + 1)] z =
        ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) := by
    exact hcondz.trans hsection
  have hconditionalLower :
      ReleaseRoundKernel.chi
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          selected.view.payload.assignment.auxiliary /
            (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source =>
            if ReferenceSourcePrefixHistoryFiltration.actualUp
              rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
              control0 (t.val + 1)] z := by
    rw [hcondz]
    exact hlower
  exact ⟨r, selected, hr, hselection, hweights, hmass, hconditionalLower⟩

end Bandits.Support.ReferenceOriginalInstallationReleaseUpSection

end
