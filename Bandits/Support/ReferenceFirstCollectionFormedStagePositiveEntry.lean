/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionStoppedOldDownQuota

import Lean.Elab.Tactic.Omega

/-!
# Pointwise formed-UP support and retained physical positive entry

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-481`,
`sources/zip4/manuscript/05_binary_transport.tex:27-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionFormedStagePositiveEntry

variable {p : ConstructorDimensions.Parameters}

private theorem actualRecord_input_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val source
  · have hseed := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hlaunch.1
    have hactual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t source _ hseed hlaunch.2
    have heq := Option.some.inj (hrecord.symm.trans hactual)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hstart := hlaunch.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t source hlaunch] at hrecord
    cases hrecord

private theorem acceptedStart_pos_lastDown_ne
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (haccepted : 1 ≤ ReferencePrelaunchFollower.acceptedStart old) :
    old.lastDown ≠ none := by
  intro hnone
  simp [ReferencePrelaunchFollower.acceptedStart, hnone] at haccepted

private theorem formed_support_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (hformed : source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
        some r ∧
      ∃ old : ReferencePrelaunchFollower.State p rate.eta,
        ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
          r.input.state.followers i = .ordinary old memory ∧
          1 ≤ ReferencePrelaunchFollower.acceptedStart old := by
  change source ∈
    (ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t ∪
      ⋃ U : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
          (p := p) (rate := rate) rewards C_star C_h i t U) at hformed
  rcases hformed with hcut | hcontinuing
  · obtain ⟨U, hcut⟩ := Set.mem_iUnion.mp hcut
    rcases hcut with ⟨r, hrecord, registers, owned, base, hlive, hcutoff,
      hallOrdinary, old, memory, hfocus, haccepted, hfields⟩
    exact ⟨r, hrecord, old, memory, hfocus, haccepted⟩
  · obtain ⟨U, hcontinuing⟩ := Set.mem_iUnion.mp hcontinuing
    rcases hcontinuing with ⟨r, hrecord, payload, ledger, saved, old, memory,
      hready, hpending, hfocus, haccepted, hfields, hallOrdinary⟩
    exact ⟨r, hrecord, old, memory, hfocus, haccepted⟩

/-- A true pointwise FORMED-stage test identifies the actual retained positive
UP entry on the same original source and physical record. -/
theorem actual_formed_stage_positive_entry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (hformed : source ∈ ReferenceFirstCollectionStagedConditionalService.FORMED
      (p := p) (rate := rate) rewards C_star C_h i t)
    (hx : ReferenceFirstCollectionRoundEndObservation.x
      (rate := rate) rewards C_star C_h i t.val source = true) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source =
        some r ∧
      r.input.time = t ∧
      r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.rewards = rewards ∧
      ∃ old : ReferencePrelaunchFollower.State p rate.eta,
        ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
          r.input.state.followers i = .ordinary old memory ∧
          1 ≤ ReferencePrelaunchFollower.acceptedStart old ∧
          old.lastDown ≠ none ∧
          ReferenceSelectedAffinePairLaw.selectedChannel p
            ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 =
              some (1, i) ∧
          ReferenceActiveAffinePositiveTest.upPositive r.input = true ∧
          ∃ e : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p),
            ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i = [e] ∧
            e.time = t ∧
            e.sample = ((source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).2 (1, i) := by
  obtain ⟨r, hrecord, old, memory, hfocus, haccepted⟩ := formed_support_record
    rate rewards C_star C_h source i t hformed
  obtain ⟨hrows, hselected, htime, hrewards⟩ := actualRecord_input_fields
    rate rewards C_star C_h t source r hrecord
  have hlast := acceptedStart_pos_lastDown_ne old haccepted
  have hnotOld : source ∉ ReferenceFirstCollectionStagedConditionalService.OLD
      (p := p) (rate := rate) rewards C_star C_h i t := by
    intro hold
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionStagedConditionalService.disjoint_OLD_FORMED
        (p := p) (rate := rate) rewards C_star C_h i t)) hold hformed
  have hobs : PhaseServiceWaiting.observation
      (ReferenceFirstCollectionRoundEndObservation.x
        (rate := rate) rewards C_star C_h) i t.val source = 1 := by
    simp [PhaseServiceWaiting.observation, hx]
  rw [ReferenceFirstCollectionRoundEndObservation.observation_eq_X
    (rate := rate) rewards C_star C_h i t.val t.isLt] at hobs
  have hreadout : ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t source = 1 := by
    simpa only [ReferenceFirstCollectionStagedConditionalService.X,
      Set.indicator_of_notMem hnotOld, Set.indicator_of_mem hformed,
      add_zero, zero_add] using hobs
  have htest : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 t).1 = ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
      ReferenceActiveAffinePositiveTest.upPositive r.input = true := by
    simp only [ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout,
      hrecord] at hreadout
    split_ifs at hreadout with h
    · exact h
    · norm_num at hreadout
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1) = i := by
    simpa [ReferenceFirstCollectionUpConditionalService.followerIndex,
      ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected, htime] using htest.1
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive r.input = true := htest.2
  have hdpositive : ReferenceActiveAffinePositiveTest.upDiagnosticPositive
      r.output.coordinator.up = true := by
    rw [← ReferenceActiveAffinePositiveTest.record_upPositive r]
    exact hpositive
  have hchannel : ReferenceSelectedAffinePairLaw.selectedChannel p
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1 =
        some (1, i) := by
    cases hd : r.output.coordinator.up with
    | none => simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hd] at hdpositive
    | some diagnostic =>
      have hdiagEligible : AffineBatchDecoder.eligible
          (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic) := by
        simpa [ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hd,
          ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using hdpositive
      have hgate : CoordinatorUpReception.receptionGate diagnostic.input :=
        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput_eligible_iff
          diagnostic).mp hdiagEligible |>.1
      obtain ⟨_, _, _, _, _, _, _, _, hdiagSlot, _, _, _, _, _⟩ :=
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hd
      have hslotUp : diagnostic.input.slot = PublicDiscreteDraws.upSlot := hgate.2.1
      have hsourceSlot : PublicDiscreteDraws.slotDraw
          (((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).1) =
            PublicDiscreteDraws.upSlot := by
        have hrecordSlot := hdiagSlot.symm.trans hslotUp
        simpa [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected, htime] using
          hrecordSlot
      rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hsourceSlot]
      exact congrArg (fun j => some (1, j)) hdraw
  refine ⟨r, hrecord, htime, hrows, hselected, hrewards,
    old, memory, hfocus, haccepted, hlast, hchannel, hpositive, ?_⟩
  cases hd : r.output.coordinator.up with
  | none =>
      rw [ReferenceActiveAffinePositiveTest.record_upPositive r, hd] at hpositive
      simp [ReferenceActiveAffinePositiveTest.upDiagnosticPositive] at hpositive
  | some diagnostic =>
      have hdiagEligible : AffineBatchDecoder.eligible
          (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic) := by
        rw [hd] at hdpositive
        simpa [ReferenceActiveAffinePositiveTest.upDiagnosticPositive,
          ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using hdpositive
      obtain ⟨_, _, _, _, hdiagTime, _, hdiagFollower, hsample, _, _, _, hroundSample,
        _, _⟩ :=
        ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields r diagnostic hd
      have htimeDiag : ReferenceCoordinatorUpDecoderReplay.retainedUpTime diagnostic = t := by
        unfold ReferenceCoordinatorUpDecoderReplay.retainedUpTime
        exact hdiagTime.trans htime
      have hfollowerDiag :
          ReferenceCoordinatorUpDecoderReplay.retainedUpFollower diagnostic = i := by
        unfold ReferenceCoordinatorUpDecoderReplay.retainedUpFollower
        rw [hdiagFollower]
        apply Fin.ext
        simpa [CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw,
          ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected, htime] using
          congrArg Fin.val hdraw
      have hselectedChannelFollower : CoordinatorUpMeasurability.selectedChannelFollower
          ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) = i := by
        apply Fin.ext
        simpa [CoordinatorUpMeasurability.selectedChannelFollower_val] using
          congrArg Fin.val hdraw
      have hcontrol : (r.input.rows r.input.selected).2 r.input.time =
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t := by
        simp [hrows, hselected, htime]
      have hsampleNorm : diagnostic.input.affineSample =
          ((r.input.rows r.input.selected).2 r.input.time).2
            (1, CoordinatorUpMeasurability.selectedChannelFollower
              ((r.input.rows r.input.selected).2 r.input.time)) := by
        simpa only [AffineBatchDecoder.width, ContinuousLearningRows.B] using hsample
      have hsampleSource : diagnostic.input.affineSample =
          ((source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).2 (1, i) := by
        rw [hsampleNorm, hcontrol]
        rw [hselectedChannelFollower]
      have hentry : ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i =
          [⟨t, ((source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).2 (1, i)⟩] := by
        have hEligible : AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput diagnostic.input) := by
          simpa [ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput] using hdiagEligible
        have hdiagTime' : diagnostic.input.time = t := hdiagTime.trans htime
        have hdiagSelected : diagnostic.input.selectedFollower = i := by
          simpa [ReferenceCoordinatorUpDecoderReplay.retainedUpFollower] using hfollowerDiag
        simp [ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries, hd,
          hdiagSelected, ReferenceCoordinatorUpDecoderReplay.retainedUpFollower,
          ReferenceCoordinatorUpDecoderReplay.retainedUpTime, hdiagTime',
          ReferenceCoordinatorUpDecoderReplay.constantInputTrace,
          AffineBatchDecoder.positiveAt, hEligible, AffineBatchDecoder.entry,
          hroundSample, hsampleSource]
      exact ⟨⟨t, ((source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t).2 (1, i)⟩,
        hentry, rfl, rfl⟩

end Bandits.Support.ReferenceFirstCollectionFormedStagePositiveEntry
