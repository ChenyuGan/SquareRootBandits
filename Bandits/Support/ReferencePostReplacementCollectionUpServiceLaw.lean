/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionReleaseResamplingData

import Mathlib.Tactic

/-!
# Actual UP release sections after post-rawK replacement collection

The literal stopped pending UP flag is integrated over the complete current
control using the retained payload and its actual whole current weights.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ActiveRoundActions
open Bandits.Support.FiniteBanditModel
open scoped Classical BigOperators

namespace Bandits.Support.ReferencePostReplacementCollectionUpServiceLaw

variable {p : ConstructorDimensions.Parameters}

private theorem sourcePrefix_replace_current
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hne : v ≠ t := by
          intro heq
          subst v
          omega
        simp only [hv, ite_true, Function.update_of_ne hne]
      · simp only [hv, ite_false]
    · have hq' : q ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 := hq
      dsimp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_of_ne hq']
  · rfl

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

private theorem pending_up_other_action_assigned {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (j : Follower m)
    (hj : s.status j = .pending) (hslot : r.slot = PublicDiscreteDraws.upSlot)
    (hselected : r.selected ≠ j)
    (htuple : r.tuple.val (coordinator hm) = a.auxiliary) :
    followerAction hm s r j = a.assigned j := by
  have haux : a.assigned j ≠ a.auxiliary := fun h => a.auxiliary_outside j h.symm
  have hnotdata : r.slot ≠ PublicDiscreteDraws.dataSlot := by rw [hslot]; decide
  have hnotdown : r.slot ≠ PublicDiscreteDraws.downSlot := by rw [hslot]; decide
  simp [followerAction, PublicDiscreteDraws.dataSlot, PublicDiscreteDraws.downSlot,
    PublicDiscreteDraws.upSlot, hj, hslot, hselected, htuple, haux]

private theorem pending_up_feedback_eq_auxiliary {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower m) (hi : s.status i = .pending)
    (hslot : r.slot = PublicDiscreteDraws.upSlot) (hselected : r.selected = i)
    (htuple : r.tuple.val (coordinator hm) = a.auxiliary)
    (hfast : r.fast ≠ a.auxiliary) :
    feedback hm s r row (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) = row.val a.auxiliary := by
  have htarget : followerAction hm s r i = a.auxiliary := by
    rw [← hselected]
    have hselectedStatus : s.status r.selected = .pending := by rw [hselected]; exact hi
    exact followerAction_pending_up_test hm s r hselectedStatus hslot htuple
  have hfree : collisionFreeFor (actions hm s r) (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) := by
    intro q hq hsame
    rcases player_cases hm q with hcoord | ⟨j, hj⟩
    · rw [hcoord, actions_coordinator,
        coordinatorAction_fast hm s r hmissing, actions_follower, htarget] at hsame
      exact hfast hsame
    · have hji : j ≠ i := by
        intro heq
        subst j
        exact hq hj
      have hselectedNe : r.selected ≠ j := by rw [hselected]; exact hji.symm
      have hother : followerAction hm s r j = a.assigned j := by
        rcases hstatus j with hjp | hjr
        · exact pending_up_other_action_assigned hm s r j hjp hslot hselectedNe htuple
        · exact followerAction_released hm s r j hjr
      rw [hj, actions_follower, actions_follower, hother, htarget] at hsame
      exact a.auxiliary_outside j hsame.symm
  rw [feedback_eq_reward_of_collision_free hm s r row _ hfree,
    actions_follower, htarget]

private theorem pending_up_release_iff {m K B : ℕ}
    {a : Assignment m K} (hm : 2 ≤ m) (s : Snapshot a)
    (r : RoundInput a B) (row : RewardRow K)
    (hmissing : s.missing = ∅)
    (hstatus : ∀ j, s.status j = .pending ∨ s.status j = .released)
    (i : Follower m) (hi : s.status i = .pending) :
    (releaseObservation hm s r row i ∧ r.slot = PublicDiscreteDraws.upSlot) ↔
      r.slot = PublicDiscreteDraws.upSlot ∧ r.selected = i ∧
        r.tuple.val (coordinator hm) = a.auxiliary ∧
        r.fast ≠ a.auxiliary ∧ 0 < row.val a.auxiliary := by
  constructor
  · rintro ⟨⟨hpos, htest⟩, houter⟩
    rcases htest with ⟨hslot, hselected, htuple⟩ | ⟨hdata, _⟩
    · have hfast : r.fast ≠ a.auxiliary := by
        intro heq
        have htarget : followerAction hm s r i = a.auxiliary := by
          rw [← hselected]
          have hselectedStatus : s.status r.selected = .pending := by rw [hselected]; exact hi
          exact followerAction_pending_up_test hm s r hselectedStatus hslot htuple
        have hzero : feedback hm s r row (Bandits.Support.PublicDiscreteDraws.followerPlayer hm i) = 0 :=
          feedback_eq_zero_of_collision hm s r row _ (coordinator hm)
            (Bandits.Support.ActiveRoundActions.followerPlayer_ne_coordinator hm i).symm (by
              rw [actions_coordinator, coordinatorAction_fast hm s r hmissing,
                actions_follower, htarget, heq])
        rw [hzero] at hpos
        exact (lt_irrefl 0) hpos
      have hreward := pending_up_feedback_eq_auxiliary hm s r row hmissing
        hstatus i hi hslot hselected htuple hfast
      rw [hreward] at hpos
      exact ⟨houter, hselected, htuple, hfast, hpos⟩
    · exact False.elim ((by decide : PublicDiscreteDraws.dataSlot ≠
        PublicDiscreteDraws.upSlot) (hdata.symm.trans houter))
  · rintro ⟨hslot, hselected, htuple, hfast, hreward⟩
    refine ⟨⟨?_, Or.inl ⟨hslot, hselected, htuple⟩⟩, hslot⟩
    rw [pending_up_feedback_eq_auxiliary hm s r row hmissing hstatus i hi
      hslot hselected htuple hfast]
    exact hreward

private theorem completeCurrentWeights_eq_payload
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection (p := p) (rate := rate) x) :
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected =
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        selected.view.payload selected.view.complementWeights := rfl

private theorem complementWeights_heq_of_complete
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hpayload : payload₁ = payload₂)
    (hcomplete : ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
      payload₁ weights₁ =
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
          payload₂ weights₂) :
    HEq weights₁ weights₂ := by
  cases hpayload
  apply heq_of_eq
  funext a
  have hpoint := congrFun hcomplete a.val
  have hnot : a.val ∉ payload₁.slowSet.val :=
    (Finset.mem_sdiff.mp a.property).2
  simpa [ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights, hnot] using hpoint

private theorem upKernelConditionsData_congr
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload₁ payload₂ : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : payload₁ = payload₂)
    (weights₁ : CanonicalFastSampling.FastArm payload₁.slowSet → ℝ)
    (weights₂ : CanonicalFastSampling.FastArm payload₂.slowSet → ℝ)
    (hweights : HEq weights₁ weights₂)
    (bounds₁ : ∀ a, 0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        payload₁ weights₁ a ∧
      payload₁.anchor a ≤ ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        payload₁ weights₁ a ∧
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload₁ weights₁ a ≤
        2 * payload₁.anchor a)
    (bounds₂ : ∀ a, 0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        payload₂ weights₂ a ∧
      payload₂.anchor a ≤ ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        payload₂ weights₂ a ∧
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload₂ weights₂ a ≤
        2 * payload₂.anchor a)
    (i : Fin (p.m - 1)) (slice : ContinuousControlSlice.Slice p.m p.K)
    (row₁ row₂ : ActiveRoundActions.RewardRow p.K) (hrow : row₁ = row₂) :
    ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData payload₁ weights₁ bounds₁ i slice row₁ ↔
      ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData payload₂ weights₂ bounds₂ i slice row₂ := by
  cases hpayload
  cases hweights
  cases hrow
  rfl

private theorem upKernelEventData_iff
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection
      (p := p) (rate := rate) x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (row : ActiveRoundActions.RewardRow p.K) (i : Fin (p.m - 1))
    (slice : ContinuousControlSlice.Slice p.m p.K)
    (hmissing : (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states).missing = ∅)
    (hstatus : ∀ j : ActiveRoundActions.Follower p.m,
      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states).status j = .pending ∨
      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states).status j = .released)
    (hi : (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states).status
      (⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩ :
        ActiveRoundActions.Follower p.m) = .pending) :
    ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected hvalid states row i slice ↔
      ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData selected.view.payload
        selected.view.complementWeights
        (fun a => by
          rw [← completeCurrentWeights_eq_payload selected]
          exact ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid a)
        i slice row := by
  have hiff := pending_up_release_iff p.two_le_m
    (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
    (ReferenceFirstLiveReleaseSliceMass.releaseKernelInput selected hvalid slice)
    row hmissing hstatus
    (⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩ :
      ActiveRoundActions.Follower p.m) hi
  have hcast : (⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩ :
      ActiveRoundActions.Follower p.m) = i := by
    apply Fin.ext
    rfl
  simpa [ReferenceFirstLiveReleaseSliceMass.upKernelEvent,
    ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData,
    ReferenceFirstLiveReleaseSliceMass.releaseKernelInput,
    ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData,
    ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights,
    ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
    completeCurrentWeights_eq_payload, hcast] using hiff

private theorem actualUp_prefix_restore
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (control : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) control) =
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) := by
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control
  have hcurrent : (z'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z')).2 t = control := by
    simp only [z', ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  have hprefix := ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t z'
  rw [sourcePrefix_replace_current control0 t z control, hcurrent] at hprefix
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  exact ((ReferenceSourcePrefixHistoryFiltration.flags_factor rate rewards C_star C_h
    control0 i t z').1.trans (congrArg
      (ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t)
      hprefix)).symm

private theorem upKernelConditionsData_measurable
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (bounds : ∀ a, 0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        payload weights a ∧
      payload.anchor a ≤ ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        payload weights a ∧
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload weights a ≤
        2 * payload.anchor a)
    (i : Fin (p.m - 1)) (row : ActiveRoundActions.RewardRow p.K) :
    MeasurableSet {slice : ContinuousControlSlice.Slice p.m p.K |
      ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData payload weights bounds i slice row} := by
  let inputAt := fun slice : ContinuousControlSlice.Slice p.m p.K =>
    ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData payload weights bounds slice
  have hslot : Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
      (inputAt slice).slot) := by
    change Measurable (PublicDiscreteDraws.slotDraw :
      ContinuousControlSlice.Slice p.m p.K → PublicDiscreteDraws.Slot)
    exact PublicDiscreteDraws.measurable_slotDraw
  have hselected : Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
      (inputAt slice).selected) := by
    change Measurable (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K)
    exact PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K
  have htuple : Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
      (inputAt slice).tuple.val (ActiveRoundActions.coordinator p.two_le_m)) := by
    change Measurable (fun slice =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K slice).val
        (ActiveRoundActions.coordinator p.two_le_m))
    exact (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp
        (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))
  have hfast : Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
      (inputAt slice).fast) := by
    change Measurable (fun slice : ContinuousControlSlice.Slice p.m p.K =>
      (CanonicalFastSampling.sampleFast p rate.eta rate.eta.property
        payload.eta_le_source_cap payload.anchor
        (ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload weights)
        payload.anchor_pos
        (fun a => (bounds a).1) (fun a => (bounds a).2.1) (fun a => (bounds a).2.2)
        payload.slowSet (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast slice)).1)
    exact measurable_subtype_coe.comp
      ((CanonicalFastSampling.measurable_sampleFast p rate.eta rate.eta.property
        payload.eta_le_source_cap payload.anchor
        (ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights payload weights)
        payload.anchor_pos
        (fun a => (bounds a).1) (fun a => (bounds a).2.1) (fun a => (bounds a).2.2)
        payload.slowSet).comp
        (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast))
  let e := payload.assignment.auxiliary
  have hslotSet : MeasurableSet {slice | (inputAt slice).slot = PublicDiscreteDraws.upSlot} :=
    (measurableSet_singleton PublicDiscreteDraws.upSlot).preimage hslot
  have hselectedSet : MeasurableSet {slice | (inputAt slice).selected = i} :=
    (measurableSet_singleton i).preimage hselected
  have htupleSet : MeasurableSet {slice |
      (inputAt slice).tuple.val (ActiveRoundActions.coordinator p.two_le_m) = e} :=
    (measurableSet_singleton e).preimage htuple
  have hfastSet : MeasurableSet {slice | (inputAt slice).fast ≠ e} :=
    ((measurableSet_singleton e).preimage hfast).compl
  by_cases hpos : 0 < row.val e
  · have hset : {slice : ContinuousControlSlice.Slice p.m p.K |
        ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData payload weights bounds i slice row} =
      {slice | (inputAt slice).slot = PublicDiscreteDraws.upSlot} ∩
        ({slice | (inputAt slice).selected = i} ∩
          ({slice | (inputAt slice).tuple.val
              (ActiveRoundActions.coordinator p.two_le_m) = e} ∩
            {slice | (inputAt slice).fast ≠ e})) := by
      ext slice
      simp [ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData, inputAt,
        e, hpos, ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData,
        ReleaseRoundKernel.releaseRoundInput]
    rw [hset]
    exact hslotSet.inter (hselectedSet.inter (htupleSet.inter hfastSet))
  · have hempty : {slice : ContinuousControlSlice.Slice p.m p.K |
        ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData payload weights bounds i slice row} = ∅ := by
      ext slice
      constructor
      · intro h
        exact hpos h.2.2.2.2
      · intro h
        cases h
    rw [hempty]
    exact MeasurableSet.empty

/- The displayed section has the exact UP mass of the one-round kernel. -/
theorem stoppedPending_actualUpControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hpending : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z) :
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
  have hkeep :=
    (ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_iff
      rate rewards C_star C_h t z i).mp hpending |>.1
  obtain ⟨r0, hr0, hactual0, _ht0, hread0⟩ :=
    ReferencePostReplacementCollectionReleaseResamplingData.stoppedDate_record_readouts
      rate rewards C_star C_h control0 t z hkeep
  obtain ⟨r, selected0, hactual, hselection, hpayload, hweightBounds,
      hauxMinimum, hreplace⟩ :=
    ReferencePostReplacementCollectionReleaseResamplingData.stoppedDate_actualWeights_replace_current
      rate rewards C_star C_h control0 t z hkeep
  have hrEq : r = r0 := Option.some.inj (hactual.symm.trans hactual0)
  subst r0
  obtain ⟨selectedBase, registers, owned, base, states, memories,
      hstate, hregisterPayload, hemptyRegisters, hselectionBase, hempty,
      hlive, hchoices, hfields, _hfast, _hup, _hdata, _hcost⟩ :=
    ReferencePostReplacementCollectionReleaseResamplingData.rawReleaseRecord_actualGeometry
      rate rewards C_star C_h z r hr0
  have hselectedBase : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
      some selectedBase := by
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselectionBase
  have hselected0 : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
      some selected0 := by
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselection
  have hselectedEq : selectedBase = selected0 := Option.some.inj (hselectedBase.symm.trans hselected0)
  subst selectedBase
  have hP0 := (hread0 selected0.view.payload hpayload).2
  have hpending0 : i ∈ ReferencePhysicalReleaseQuota.pendingSet selected0.view.payload r :=
    hP0 ▸ hpending
  have hi : (states i).status = .pending := by
    have hchoice : ((ReferenceActivePhysicalStep.prepare r.input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
      simpa only [ReferenceFollowerFixedReply.actualChoice, r.output_eq,
        ReferenceActivePhysicalStep.step] using hchoices i
    exact (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      selected0.view.payload r.input registers owned base hstate hregisterPayload
      hemptyRegisters i
      (states i) (memories i) hchoice).mp hpending0
  have hstatus : ∀ j, (states j).status = .pending ∨ (states j).status = .released := by
    intro j
    cases hs : (states j).status with
    | unoccupied => exact False.elim ((hfields j).1 hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hvalid := ReferenceLaterLiveNumericalReadout.selection_choiceValid selected0
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let weights := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0
  let bounds := fun a =>
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid a
  let boundsData : ∀ a,
      0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
          selected0.view.payload selected0.view.complementWeights a ∧
        selected0.view.payload.anchor a ≤
          ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
            selected0.view.payload selected0.view.complementWeights a ∧
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
            selected0.view.payload selected0.view.complementWeights a ≤
          2 * selected0.view.payload.anchor a := fun a => by
    rw [← completeCurrentWeights_eq_payload selected0]
    exact bounds a
  let E : Set (ContinuousControlSlice.Slice p.m p.K) :=
    {slice | ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData
      selected0.view.payload selected0.view.complementWeights
      boundsData
      i slice row}
  have hE : MeasurableSet E := by
    exact upKernelConditionsData_measurable selected0.view.payload
      selected0.view.complementWeights
      boundsData i row
  have hgeom : ∀ control : ContinuousLearningRows.TimeControl p,
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control) = true ↔
      control.1 ∈ E := by
    intro control
    obtain ⟨r', selected', hactual', hselection', hpayload', hweights'⟩ := hreplace control
    let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control
    have hkeep' : ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedDate
        rate rewards C_star C_h t z' := by
      rw [ReferencePostReplacementCollectionReleaseResamplingData.postRawKStoppedDate_replace_current
        rate rewards C_star C_h control0]
      exact hkeep
    obtain ⟨rRead, hrRead, hactualRead, _htRead, hread⟩ :=
      ReferencePostReplacementCollectionReleaseResamplingData.stoppedDate_record_readouts
        rate rewards C_star C_h control0 t z' hkeep'
    have hrEq' : r' = rRead := Option.some.inj (hactual'.symm.trans hactualRead)
    subst rRead
    obtain ⟨selectedGeom, registers', owned', base', states', memories',
        hstate', hregisterPayload', hemptyRegisters', hselectionGeom, hempty',
        hlive', hchoices', hfields', _hfast', hupGeom', _hdata', _hcost'⟩ :=
      ReferencePostReplacementCollectionReleaseResamplingData.rawReleaseRecord_actualGeometry
        rate rewards C_star C_h z' r' hrRead
    have hselectedGeom : (ReferenceActivePhysicalStep.prepare r'.input).coordinator.selection =
        some selectedGeom := by
      simpa only [r'.output_eq, ReferenceActivePhysicalStep.step] using hselectionGeom
    have hselectedHall : (ReferenceActivePhysicalStep.prepare r'.input).coordinator.selection =
        some selected' := by
      simpa only [r'.output_eq, ReferenceActivePhysicalStep.step] using hselection'
    have hselectedEq' : selectedGeom = selected' :=
      Option.some.inj (hselectedGeom.symm.trans hselectedHall)
    subst selectedGeom
    have hM' : ReferencePostReplacementCollectionReleaseResamplingData.incomingStoredPayload
        rate rewards C_star C_h t z' = some (some selected0.view.payload) := by
      rw [ReferencePostReplacementCollectionReleaseResamplingData.incomingStoredPayload_replace_current
        rate rewards C_star C_h control0]
      exact hpayload
    obtain ⟨hstored, hP⟩ := hread selected0.view.payload hM'
    have hi' : (states' i).status = .pending := by
      have hpending' : i ∈
          ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
            rate rewards C_star C_h t z' := by
        rw [ReferencePostReplacementCollectionReleaseResamplingData.postRawKStoppedPendingSet_replace_current
          rate rewards C_star C_h control0 t z control]
        exact hpending
      have hpend' : i ∈ ReferencePhysicalReleaseQuota.pendingSet selected0.view.payload r' :=
        hP ▸ hpending'
      have hchoice : ((ReferenceActivePhysicalStep.prepare r'.input).followers.followers i).configuration =
          .ordinary (states' i) (memories' i) := by
        simpa only [ReferenceFollowerFixedReply.actualChoice, r'.output_eq,
          ReferenceActivePhysicalStep.step] using hchoices' i
      have hselectedPayload' : selected'.view.payload = selected0.view.payload := hpayload'
      exact (ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
        selected0.view.payload r'.input registers' owned' base' hstate'
        (hregisterPayload'.trans hselectedPayload') hemptyRegisters' i
        (states' i) (memories' i) hchoice).mp hpend'
    have hstatus' : ∀ j, (states' j).status = .pending ∨ (states' j).status = .released := by
      intro j
      cases hs : (states' j).status with
      | unoccupied => exact False.elim ((hfields' j).1 hs)
      | pending => exact Or.inl rfl
      | released => exact Or.inr rfl
    have hordinary' : ∀ j,
        ((ReferenceActivePhysicalStep.prepare r'.input).followers.followers j).configuration =
          .ordinary (states' j) (memories' j) := by
      intro j
      simpa only [ReferenceFollowerFixedReply.actualChoice, r'.output_eq,
        ReferenceActivePhysicalStep.step] using hchoices' j
    have hvalid' := ReferenceLaterLiveNumericalReadout.selection_choiceValid selected'
    have hprep' : (ReferenceActivePhysicalStep.prepare r'.input).coordinator.selection =
        some selected' := hselectedHall
    have hfieldsInput := actualRecord_input_fields rate rewards C_star C_h t z' r' hactual'
    have hcontrol : r'.input.row.2 r'.input.time = control := by
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hfieldsInput.1,
        hfieldsInput.2.1, _htRead, z', ActualInitializationPhysicalStep.selectedRowIndex,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        Function.update_self]
    have hcontrolT : r'.input.row.2 t = control := by
      simpa only [_htRead] using hcontrol
    let follower : ActiveRoundActions.Follower p.m :=
      ⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩
    have hfollower : ReferenceFirstLiveReleaseGeometry.followerToFin follower = i := by
      apply Fin.ext
      rfl
    have hfollowerIndex : (follower : Fin (p.m - 1)) = i := by
      apply Fin.ext
      rfl
    have hupCoordinates := hupGeom' follower (by
      simpa only [hfollower] using hi')
    have boundsData' : ∀ a,
        0 < ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
            selected'.view.payload selected'.view.complementWeights a ∧
          selected'.view.payload.anchor a ≤
            ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
              selected'.view.payload selected'.view.complementWeights a ∧
          ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
              selected'.view.payload selected'.view.complementWeights a ≤
            2 * selected'.view.payload.anchor a := by
      intro a
      rw [← completeCurrentWeights_eq_payload selected']
      exact ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected' hvalid' a
    have hupData' :
        ReferencePhysicalReleaseQuota.upFlag selected'.view.payload r' i = true ↔
          ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData
            selected'.view.payload selected'.view.complementWeights boundsData'
            i control.1 row := by
      simpa [ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput,
        ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData,
        ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData,
        ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights,
        completeCurrentWeights_eq_payload,
        ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow, row, hcontrolT,
        _htRead, follower, hfollower, hfollowerIndex,
        ReferenceFirstLiveReleaseGeometry.followerToFin,
        ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using hupCoordinates
    have hcomplete' := hweights'
    change ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        selected'.view.payload selected'.view.complementWeights =
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
        selected0.view.payload selected0.view.complementWeights at hcomplete'
    have hcomplementHEq := complementWeights_heq_of_complete selected'.view.payload
      selected0.view.payload selected'.view.complementWeights
      selected0.view.complementWeights hpayload' hcomplete'
    have hupDataEq := upKernelConditionsData_congr selected'.view.payload
      selected0.view.payload hpayload' selected'.view.complementWeights
      selected0.view.complementWeights hcomplementHEq boundsData' boundsData i
      control.1 row row rfl
    have hactualUp : ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z' = true ↔
        ReferenceFirstLiveReleaseSliceMass.upKernelConditionsData
          selected0.view.payload selected0.view.complementWeights
          boundsData
          i control.1 row := by
      rw [ReferenceSourcePrefixHistoryFiltration.actualUp, hactual', Option.bind_some,
        hstored, Option.map_some, Option.getD_some]
      have hflagPayload :
          ReferencePhysicalReleaseQuota.upFlag selected0.view.payload r' i = true ↔
            ReferencePhysicalReleaseQuota.upFlag selected'.view.payload r' i = true := by
        rw [← hpayload']
      exact hflagPayload.trans (hupData'.trans hupDataEq)
    exact hactualUp
  have hfun : (fun control : ContinuousLearningRows.TimeControl p =>
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand
        rate rewards C_star C_h i t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, control)) =
      (Prod.fst ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext control
    rw [ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSectionIntegrand,
      actualUp_prefix_restore rate rewards C_star C_h control0 t i z control]
    simp only [Set.indicator, Set.mem_preimage]
    exact if_congr (hgeom control) rfl rfl
  have hintegral : ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z =
        (ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' E)).toReal := by
    unfold ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
    rw [hfun]
    exact integral_indicator_one (hE.preimage measurable_fst)
  have hwhole : ContinuousLearningRows.timeControlLaw p (Prod.fst ⁻¹' E) =
      ContinuousControlSlice.sliceLaw p.m p.K E :=
    (ContinuousLearningRows.measurePreserving_slice p).measure_preimage hE.nullMeasurableSet
  let payload := selected0.view.payload
  let a := payload.assignment
  let U := payload.slowSet
  let hU := payload.assignment_image.symm
  have hmissing : (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states).missing = ∅ := by
    change selected0.view.pendingAtChoice = ∅
    exact hempty
  have hstatusSnapshot : ∀ j : ActiveRoundActions.Follower p.m,
      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states).status j =
        .pending ∨ (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states).status j = .released := by
    intro j
    change (states (ReferenceFirstLiveReleaseGeometry.followerToFin j)).status = .pending ∨
      (states (ReferenceFirstLiveReleaseGeometry.followerToFin j)).status = .released
    simpa only [ReferenceFirstLiveReleaseGeometry.followerToFin] using hstatus
      (ReferenceFirstLiveReleaseGeometry.followerToFin j)
  have hiSnapshot :
      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states).status
        (⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩ :
          ActiveRoundActions.Follower p.m) =
          .pending := by
    change (states i).status = .pending
    exact hi
  have hprobKernel := ReleaseRoundKernel.actual_up_release_probability p a
    (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states)
    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
    rate.eta rate.eta.property payload.eta_le_source_cap payload.anchor weights
    payload.anchor_pos (fun a => (bounds a).1) (fun a => (bounds a).2.1)
    (fun a => (bounds a).2.2) U hU hmissing hstatusSnapshot
    (⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩ :
      ActiveRoundActions.Follower p.m)
    hiSnapshot
  have hkernelSet : {slice : ContinuousControlSlice.Slice p.m p.K |
      ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected0 hvalid states row i slice} = E := by
    ext slice
    simpa [E, boundsData, completeCurrentWeights_eq_payload] using
      upKernelEventData_iff selected0 hvalid states row i slice
        hmissing hstatusSnapshot hiSnapshot
  have hprobEvent : ContinuousControlSlice.sliceLaw p.m p.K
      {slice : ContinuousControlSlice.Slice p.m p.K |
        ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected0 hvalid states row i slice} =
      ENNReal.ofReal (ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
        selected0 hvalid row) := by
    simpa [ReferenceFirstLiveReleaseSliceMass.upKernelEvent,
      ReferenceFirstLiveReleaseSliceMass.releaseKernelInput,
      ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData,
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula,
      PublicDiscreteDraws.followerCount, payload, a, U, hU, row, weights, bounds,
      Nat.cast_sub (show 1 ≤ p.m from Nat.le_trans (by decide) p.two_le_m)] using hprobKernel
  have hprob : ContinuousControlSlice.sliceLaw p.m p.K E =
      ENNReal.ofReal (ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
        selected0 hvalid row) := by
    rw [← hkernelSet]
    exact hprobEvent
  have haux : (ReleaseRoundKernel.auxiliaryFastArm a U hU).val = payload.assignment.auxiliary := rfl
  have hminimum : ∀ j : CanonicalFastSampling.FastArm U,
      payload.anchor (ReleaseRoundKernel.auxiliaryFastArm a U hU).val ≤ payload.anchor j.val := by
    intro j
    rw [haux]
    exact payload.auxiliaryArm_anchor_minimum j.val j.property
  have hlowerKernel := ReleaseRoundKernel.actual_up_release_probability_lower_bound
    p a (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected0 states)
    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
    rate.eta rate.eta.property payload.eta_le_source_cap payload.anchor weights
    payload.anchor_pos (fun a => (bounds a).1) (fun a => (bounds a).2.1)
    (fun a => (bounds a).2.2) U hU hmissing hstatusSnapshot
    (⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩ :
      ActiveRoundActions.Follower p.m)
    hiSnapshot hminimum
  have hlowerEvent : ENNReal.ofReal
      (ReleaseRoundKernel.chi row payload.assignment.auxiliary /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
      ContinuousControlSlice.sliceLaw p.m p.K
        {slice : ContinuousControlSlice.Slice p.m p.K |
          ReferenceFirstLiveReleaseSliceMass.upKernelEvent selected0 hvalid states row i slice} := by
    simpa [ReferenceFirstLiveReleaseSliceMass.upKernelEvent,
      ReferenceFirstLiveReleaseSliceMass.releaseKernelInput,
      ReferenceFirstLiveReleaseSliceMass.releaseKernelInputData,
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights,
      ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot,
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
      completeCurrentWeights_eq_payload,
      PublicDiscreteDraws.followerCount, payload, a, U, hU, row, weights, bounds,
      Nat.cast_sub (show 1 ≤ p.m from Nat.le_trans (by decide) p.two_le_m)] using hlowerKernel
  have hlower : ENNReal.ofReal
      (ReleaseRoundKernel.chi row payload.assignment.auxiliary /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ))) ≤
      ContinuousControlSlice.sliceLaw p.m p.K E := by
    rw [← hkernelSet]
    exact hlowerEvent
  have hm : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
  have hd : (0 : ℝ) ≤ (p.m - 1 : ℝ) := by
    exact_mod_cast (show 0 ≤ p.m - 1 by omega)
  have hden : (0 : ℝ) ≤ 4 * (p.m - 1 : ℝ) * (p.K : ℝ) := by
    positivity
  have hchi : 0 ≤ ReleaseRoundKernel.chi row payload.assignment.auxiliary := by
    unfold ReleaseRoundKernel.chi
    split_ifs <;> norm_num
  have hq := CanonicalFastSampling.qGamma_auxiliary_arm_le_two_thirds
    p rate.eta.property payload.eta_le_source_cap payload.anchor weights payload.anchor_pos
    (fun a => (bounds a).1) (fun a => (bounds a).2.1) (fun a => (bounds a).2.2)
    U (ReleaseRoundKernel.auxiliaryFastArm a U hU) hminimum
  have hmassNonneg : 0 ≤ ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row := by
    unfold ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
    exact div_nonneg
      (mul_nonneg hchi (sub_nonneg.mpr (hq.trans (by norm_num)))) hden
  have hfinite : ContinuousControlSlice.sliceLaw p.m p.K E ≠ ⊤ := by
    rw [hprob]
    exact ENNReal.ofReal_ne_top
  have hsection : ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z =
        ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row := by
    rw [hintegral, hwhole, hprob]
    exact ENNReal.toReal_ofReal hmassNonneg
  have hlowerReal : ReleaseRoundKernel.chi row payload.assignment.auxiliary /
      (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := by
    rw [hintegral, hwhole]
    have hden12 : 0 ≤ 12 * (p.m - 1 : ℝ) * (p.K : ℝ) := by positivity
    have hnonneg : 0 ≤ ReleaseRoundKernel.chi row payload.assignment.auxiliary /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) := div_nonneg hchi hden12
    have hreal := ENNReal.toReal_mono hfinite hlower
    rw [ENNReal.toReal_ofReal hnonneg] at hreal
    exact hreal
  exact ⟨r, selected0, hactual, hselection, hsection, hlowerReal⟩

/- The masked law and its auxiliary-arm lower bound hold together for all
followers and dates outside one null set of the original source law. -/
theorem stoppedPending_actualUp_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p),
      ∀ (i : Fin (p.m - 1)) (t : Fin p.T),
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          ({source | i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
            rate rewards C_star C_h t source}.indicator
            (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
              rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
            (t.val + 1)] z =
          (if i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
              rate rewards C_star C_h t z then
            ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
              rate rewards C_star C_h control0 i t z else 0) ∧
        (if i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
              rate rewards C_star C_h t z then
          ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
            (selected : ReferenceActivePhysicalStep.Selection r.input),
            ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
            r.output.preparation.coordinator.selection = some selected ∧
            (BootstrapPrivateRoundStreams.sourceInputLaw p)[
              ({source | i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
                rate rewards C_star C_h t source}.indicator
                (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
                  rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
              ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
                (t.val + 1)] z =
              ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected
                (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) ∧
            ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              selected.view.payload.assignment.auxiliary /
              (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
              (BootstrapPrivateRoundStreams.sourceInputLaw p)[
                ({source | i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
                  rate rewards C_star C_h t source}.indicator
                  (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
                    rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
                ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
                  (t.val + 1)] z
        else True) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro t
  have hmask :=
    ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet_mem_measurable_preRound
      rate rewards C_star C_h control0 t i
  have hpull := condExp_indicator
    (ReferenceSourcePhysicalFlagConditionalLaw.actualUp_observation_integrable
      rate rewards C_star C_h control0 i t) hmask
  filter_upwards [hpull, ReferenceSourcePhysicalFlagConditionalLaw.actual_up_condExp
    rate rewards C_star C_h control0 i t] with z hpull hup
  rw [hpull]
  by_cases hp : i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
      rate rewards C_star C_h t z
  · have hsection := stoppedPending_actualUpControlSection
      rate rewards C_star C_h control0 t i z hp
    simp only [hp]
    have hcond : (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] z =
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := by
      exact hup
    have hmasked :
        ({source | i ∈ ReferencePostReplacementCollectionStoppedReleaseAdaptation.postRawKStoppedPendingSet
          rate rewards C_star C_h t source}.indicator
          ((BootstrapPrivateRoundStreams.sourceInputLaw p)[
            (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
              rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
              (t.val + 1)])) z =
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
            (t.val + 1)] z := by
      simp [Set.indicator, Set.mem_ofPred_eq, hp]
    constructor
    · simp only [Set.indicator, Set.mem_ofPred_eq, hp, ↓reduceIte, hcond]
    · obtain ⟨r, selected, hactual, hselection, hformula, hlower⟩ := hsection
      exact ⟨r, selected, hactual, hselection, hmasked.trans (hcond.trans hformula),
        by rw [hmasked, hcond]; exact hlower⟩
  · simp only [hp, Set.indicator, Set.mem_ofPred_eq, ↓reduceIte]
    trivial

end Bandits.Support.ReferencePostReplacementCollectionUpServiceLaw

end
