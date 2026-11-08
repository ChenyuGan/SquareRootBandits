/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteHistoryOrdinarySuffixIdentification
public import Bandits.Support.ActualInitializationLaunchMemory
public import Bandits.Support.ReferenceCompleteRewardMeasurability

/-!
# Actual complete reward and the canonical corrected reference

Mathematical evidence: `sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/06_interruptions.tex:240-295`, and
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`.

The actual initialization handoff and its retained proposal memory identify
the same active state used by the actual ordinary suffix with the literal
corrected reference launch. Initialization rewards are identified from the
produced own histories, and the existing ordinary/reference prefix comparison
then applies to the canonical complete suffix records.

These are internal deterministic comparisons. The initialization and virtual
false-forward exclusions remain explicit. The additional saved-record good
condition is local to the computed reference records; it is not identified
with a manuscript exceptional-event complement. No event coverage, domain
safety, probability, expectation, or manuscript regret conclusion is claimed.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ActualCompleteRewardPrefixComparison

variable {p : ConstructorDimensions.Parameters} {rate : ActualPostlaunchPhysicalStep.RateInput p}

/-- A related physical prefix has exactly the reward of its stored reference
own histories. The sole local hypothesis is the explicit existing prefix
relation; the source-root results below produce that relation. -/
theorem physicalRewardSum_eq_boundaryReward_of_past_related
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (boundary : ReferenceInitializationRun.Boundary p)
    (hpast : ActualReferenceInitializationBlock.past_related past boundary) :
    (past.map ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward).sum =
      ReferenceInitializationPhysicalRewards.boundaryReward p boundary := by
  obtain ⟨hlength, _hcalendar, hhistory⟩ := hpast
  have hsum :
      (past.map ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward).sum =
        ∑ u : Fin past.length,
          ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward past[u.val] := by
    rw [← List.ofFn_getElem_eq_map past
      ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward, List.sum_ofFn]
  rw [hsum]
  calc
    _ = ∑ u : Fin (ReferenceInitializationRun.elapsed p boundary.completed),
        ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward
          past[(Fin.cast hlength.symm u).val] :=
      Fintype.sum_equiv (finCongr hlength) _ _ (by intro u; rfl)
    _ = ReferenceInitializationPhysicalRewards.boundaryReward p boundary := by
      unfold ReferenceInitializationPhysicalRewards.boundaryReward
      apply Finset.sum_congr rfl
      intro u _hu
      unfold ActualInitializationPhysicalRewards.physicalRoundRecordObservedReward
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hhistory i u]
      rfl

/-- One actual launched branch supplies one canonical launch state for every
prefix. Its full configuration comes from the actual handoff; only the real
initialization memory invariant is used to identify proposal memory. The
prefix condition concerns the canonical complete suffix's retained records.
A terminal launch at `T` is included, with a zero-length suffix. -/
theorem sourceInitializedRun_launched_canonical_comparison
    (p : ConstructorDimensions.Parameters) (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed) :
    let u := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    let start := launch.monitor.launchPosition
    let count := p.T - start
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let projected := (ActualCompletePhysicalHistory.postlaunchRecords
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards
        C_star C_h)).map ActualCompleteHistoryOrdinarySuffixIdentification.mixedPhysicalProjection
    let canonical := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∃ active : ReferenceActivePhysicalStep.State p rate,
      ∃ (hspan : start + count ≤ p.T)
        (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start),
      (∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate
        (u.terminalHandoff.followers i) = .declared J (active.activations i)
          (active.followers i)) ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some active ∧
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = start ∧
      ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
        ReferenceInitializationPhysicalRewards.boundaryReward p
          (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) ∧
      canonical = (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
        start count hspan hmode).records ∧
      (∀ k, k ≤ count →
        (∀ record ∈ canonical.take k,
          ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record) →
        projected.take k =
          (canonical.map ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k ∧
        ActualInitializationPhysicalRewards.sourceInitializationReward
          (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source +
            ((projected.take k).map
              ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum =
          ReferenceInitializationPhysicalRewards.boundaryReward p
            (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) +
            ((canonical.take k).map ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum) ∧
      ((∀ record ∈ canonical,
          ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record) →
        ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
          (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
          ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  obtain ⟨_actual, active, hspan, hmode, _hrelated, _hfold, _hCstar, _hCh,
    hcoordinator, hbank, hhandoff, hstartRelated, hordinary, _hpreserve, _hfirst,
    hcross, _hlaunchRound, _hlength, hpast, helapsed, _hcalendar, _hcanonical,
    _htrace, _hactualReward, hprefix, hfull, _hbad⟩ :=
    ActualCompleteHistoryOrdinarySuffixIdentification.sourceInitializedRun_launched_ordinary_suffix_eq
      p rate source rewards C_star C_h hinit hfalse launch seed hlaunch
  have hmemory := (ActualInitializationLaunchMemory.source_declared_memory_initial
    p rate source rewards C_star C_h hinit hfalse).2.1
  have hconfiguration : ∀ i, active.followers i = .ordinary
      (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
        (ActualReferenceInitializationBlock.refFollower i))
      (ActiveFollowerLifecycle.initialMemory p) := by
    intro i
    obtain ⟨state, memory, hf, hstate, _hregisters⟩ := hordinary i
    have hm : memory = ActiveFollowerLifecycle.initialMemory p :=
      hmemory i (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (active.activations i) state memory (by simpa only [hf] using hhandoff i)
    rw [hf, hstate, hm]
  have hactivation : ∀ i, (ReferenceInitializationRun.output x).activation
      (ActualReferenceInitializationBlock.refFollower i) = some (active.activations i) := by
    intro i
    have hi := hstartRelated i
    rw [hconfiguration i] at hi
    exact hi.2.1
  have hc : (ReferenceInitializationRun.output x).crossing.isSome = true := by
    rw [hcross]
    rfl
  have hcorrected : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active := by
    unfold ReferenceCorrectedInitializationLaunch.correctedLaunch
    dsimp only
    rw [dite_eq_left hc]
    apply congrArg some
    cases active with
    | mk coordinator bank activations followers =>
        have ha : (fun i => ((ReferenceInitializationRun.output x).activation
            (ActualReferenceInitializationBlock.refFollower i)).get
              (ReferenceInitializationRun.run_all_activated_at_crossing x
                (BootstrapDimensions.n_boot p) hc (ActualReferenceInitializationBlock.refFollower i))) =
            activations := by
          funext i
          simp only [hactivation i, Option.get_some]
        have hf : followers = fun i => .ordinary
            (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (ActualReferenceInitializationBlock.refFollower i))
            (ActiveFollowerLifecycle.initialMemory p) := funext hconfiguration
        cases hcoordinator
        cases hbank
        cases ha
        cases hf
        rfl
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h = launch.monitor.launchPosition := helapsed
  have hinitReward : ActualInitializationPhysicalRewards.sourceInitializationReward
      (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
      ReferenceInitializationPhysicalRewards.boundaryReward p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) :=
    physicalRewardSum_eq_boundaryReward_of_past_related _ _ hpast
  have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h =
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        launch.monitor.launchPosition (p.T - launch.monitor.launchPosition) hspan hmode).records := by
    have h := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate source rewards C_star C_h active hcorrected
    simpa only [hstart] using h
  refine ⟨active, hspan, hmode, hhandoff, hcorrected, hstart, hinitReward, hrecords, ?_, ?_⟩
  · intro k hk hgood
    have hg : ∀ record ∈
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          launch.monitor.launchPosition (p.T - launch.monitor.launchPosition) hspan hmode).records.take k,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
      simpa only [hrecords] using hgood
    have hphysical := (hprefix k hk hg).2.1
    rw [← hrecords] at hphysical
    refine ⟨hphysical, ?_⟩
    rw [hinitReward, hphysical, ← List.map_take, List.map_map]
    rfl
  · intro hgood
    have hg : ∀ record ∈
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          launch.monitor.launchPosition (p.T - launch.monitor.launchPosition) hspan hmode).records,
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
      simpa only [hrecords] using hgood
    have hsuffix := (ReferenceCompletePhysicalRewards.completeSuffixReward_eq_run_totalReward
      rate source rewards C_star C_h active hcorrected).2
    have hsuffixAt : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h |>.map
          ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          launch.monitor.launchPosition (p.T - launch.monitor.launchPosition) hspan hmode).totalReward := by
      simpa only [hstart] using hsuffix
    rw [hfull hg, hinitReward,
      ReferenceCompletePhysicalRewards.completeReward_calendar_split, hsuffixAt]

/-- Complete actual and canonical corrected-reference rewards agree under the
two explicit initialization exclusions and the visible local saved-record
condition. All players and all physical rounds through `T` are counted.
Exhaustion and a real terminal crossing are both retained. -/
theorem sourceInitializedActualCompleteTotalReward_eq_completeReward
    (p : ConstructorDimensions.Parameters) (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (hgood : ∀ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h,
      ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record) :
    ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
      ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h := by
  cases hd : (ActualInitializationHorizon.sourceInitializedRun
      p rate source rewards C_star C_h).terminalDisposition with
  | continueNext next carry =>
      have hstopped := (ActualInitializationHorizon.sourceInitializedRun
        p rate source rewards C_star C_h).terminal_stopped
      rw! [hd] at hstopped
      exact hstopped.elim
  | launched launch seed =>
      obtain ⟨_active, _hspan, _hmode, _hhandoff, _hcorrected, _hstart,
        _hinitReward, _hrecords, _hprefix, hfull⟩ :=
        sourceInitializedRun_launched_canonical_comparison p rate source rewards C_star C_h
          hinit hfalse launch seed hd
      exact hfull hgood
  | exhausted live =>
      obtain ⟨hcross, _hlaunchRound, _hblock, _hstop, _hlength, hpast,
        _hcalendar, _hrecords, hactual⟩ :=
        ActualCompleteHistoryOrdinarySuffixIdentification.sourceInitializedRun_exhausted_no_postlaunch
          p rate source rewards C_star C_h hinit hfalse live hd
      have hnone := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
        rate source rewards C_star C_h).2 hcross
      rw [hactual, ReferenceCompletePhysicalRewards.completeReward_eq_prefix_of_no_launch
        rate source rewards C_star C_h hnone]
      exact physicalRewardSum_eq_boundaryReward_of_past_related _ _ hpast

end Bandits.Support.ActualCompleteRewardPrefixComparison

end
