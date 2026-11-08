/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualSourceInitializedLaunchMeasurability
public import Bandits.Support.ActualPostlaunchSuffixMeasurability

/-!
# The actual source-initialized complete suffix observation

The observation pairs the existing initialization observation with the existing
postlaunch suffix core. The left `Unit` tag means that there is no suffix:
exhaustion and launch after the horizon both retain that absence. No execution,
state, or terminal record is synthesized by this observation.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.

All results are internal deterministic observation and measurability results.
Whole action/feedback lists, real reward readouts, bounds, integrability,
locality, actual/reference coupling, and regret remain later consumers.
`ActualCompleteHistoryRewardReadouts` is the intended next consumer, after
independent acceptance of these exact observation declarations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions

namespace Bandits.Support.ActualSourceCompleteSuffixObservation

abbrev Parameters := ActualSourceInitializedLaunchMeasurability.Parameters
abbrev RateInput := ActualSourceInitializedLaunchMeasurability.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev GridRewardTable := ActualSourceInitializedLaunchMeasurability.GridRewardTable

abbrev InitializationObservation (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) :=
  ActualInitializationHorizonMeasurability.RunFromObservation
    (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
    (ActualInitializationRun.firstBlock p)

abbrev SuffixCoreObservation := ActualPostlaunchSuffixMeasurability.SuffixCoreObservation

/-- The existing initialization observation and the optionally present suffix.
The canonical product and sum spaces retain all continuous code coordinates. -/
abbrev CompleteHistoryObservation (p : Parameters) (rate : RateInput p)
    (C_star C_h : ℝ) :=
  InitializationObservation p rate C_star C_h × (Unit ⊕ SuffixCoreObservation p rate)

variable {p : Parameters} {rate : RateInput p} {C_star C_h : ℝ}
  {rewards : GridRewardTable p}

/-- Read H's actual suffix without adding any record to either absent case. -/
def suffixObservationOfCompleteHistory {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) : Unit ⊕ SuffixCoreObservation p rate :=
  match history with
  | .launchedBefore _ _ _ _ suffix =>
      Sum.inr (ActualPostlaunchSuffixMeasurability.postlaunchSuffixCoreObservation suffix)
  | .launchedAtHorizon _ _ _ _ => Sum.inl ()
  | .exhausted _ _ => Sum.inl ()

theorem suffixObservationOfCompleteHistory_launchedBefore {source : SourceInput p}
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T)
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
        rewards C_star C_h launch learnerSeed hlaunch hbefore)
      (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
        rewards C_star C_h launch learnerSeed hlaunch hbefore).state) :
    suffixObservationOfCompleteHistory
        (.launchedBefore launch learnerSeed hlaunch hbefore suffix) =
      Sum.inr (ActualPostlaunchSuffixMeasurability.postlaunchSuffixCoreObservation suffix) := rfl

theorem suffixObservationOfCompleteHistory_launchedAtHorizon {source : SourceInput p}
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hat : launch.monitor.launchPosition = p.T) :
    suffixObservationOfCompleteHistory
      (.launchedAtHorizon launch learnerSeed hlaunch hat) = Sum.inl () := rfl

theorem suffixObservationOfCompleteHistory_exhausted {source : SourceInput p}
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h).terminalDisposition = .exhausted live) :
    suffixObservationOfCompleteHistory (.exhausted live hexhausted) = Sum.inl () := rfl

/-- The literal observation of the existing source-initialized complete history. -/
def sourceInitializedActualCompleteHistoryObservation (source : SourceInput p) :
    CompleteHistoryObservation p rate C_star C_h :=
  (ActualInitializationSourceObservation.sourceInitializedRunObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source,
    suffixObservationOfCompleteHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
        p rate source rewards C_star C_h))

/-- Convert one physical input using its literal full source, rewards and state. -/
def blockInputOfPhysicalInput {block : Fin (n_boot p)}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0) :
    ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 :=
  (input.source, (input.rewards, input.state))

/-- The conversion uses the existing input encoding's measurable projections. -/
theorem measurable_blockInputOfPhysicalInput {block : Fin (n_boot p)} :
    Measurable (blockInputOfPhysicalInput (p := p) (rate := rate) (block := block)) :=
  ActualPostlaunchPreparationMeasurability.measurable_inputSource.prodMk
    (ActualPostlaunchPreparationMeasurability.measurable_inputRewards.prodMk
      ActualPostlaunchPreparationMeasurability.measurable_inputState)

/-- Retain the actual dependent block index when converting a launch input. -/
def blockInputOfLaunchInput
    (input : Sigma fun block : Fin (n_boot p) =>
      ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) block 0) :
    Sigma fun block : Fin (n_boot p) =>
      ActualPostlaunchBlockMeasurability.BlockInput p rate block 0 :=
  ⟨input.1, blockInputOfPhysicalInput input.2⟩

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[(⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_sigmaMk {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (Sigma.mk a : β a → Sigma β) := by
  rw [measurable_iff_le_map]
  change (⨅ i, (inferInstance : MeasurableSpace (β i)).map (Sigma.mk i)) ≤ _
  exact iInf_le _ a

theorem measurable_blockInputOfLaunchInput :
    Measurable (blockInputOfLaunchInput (p := p) (rate := rate)) := by
  apply measurable_of_sigma_sections
  intro block
  exact (measurable_sigmaMk (β := fun block : Fin (n_boot p) =>
    ActualPostlaunchBlockMeasurability.BlockInput p rate block 0) block).comp
      measurable_blockInputOfPhysicalInput

/-- S's existing suffix core, evaluated at a converted dependent launch input. -/
def runSuffixCoreOfLaunchInput
    (input : Sigma fun block : Fin (n_boot p) =>
      ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) block 0) : SuffixCoreObservation p rate :=
  let converted := blockInputOfLaunchInput input
  ActualPostlaunchSuffixMeasurability.postlaunchSuffixCoreObservation
    (ActualCompletePhysicalHistory.runPostlaunchSuffix p rate
      converted.2.1 converted.2.2.1 converted.1 converted.2.2.2)

theorem measurable_runSuffixCoreOfLaunchInput :
    Measurable (runSuffixCoreOfLaunchInput (p := p) (rate := rate)) := by
  apply measurable_of_sigma_sections
  intro block
  exact (ActualPostlaunchSuffixMeasurability.measurable_runPostlaunchSuffixCoreObservation
    (p := p) (rate := rate) (block := block)).comp
      measurable_blockInputOfPhysicalInput

abbrev LaunchDomain := ActualSourceInitializedLaunchMeasurability.LaunchDomain
  (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)

/-- The actual suffix core on the strict pre-horizon launch event subtype. -/
def sourceInitializedSuffixCoreOnLaunch
    (source : LaunchDomain (p := p) (rate := rate) (C_star := C_star)
      (C_h := C_h) (rewards := rewards)) : SuffixCoreObservation p rate :=
  runSuffixCoreOfLaunchInput
    (ActualSourceInitializedLaunchMeasurability.sourceInitializedLaunchInput
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) source)

theorem measurable_sourceInitializedSuffixCoreOnLaunch :
    Measurable (sourceInitializedSuffixCoreOnLaunch (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) :=
  measurable_runSuffixCoreOfLaunchInput.comp
    (ActualSourceInitializedLaunchMeasurability.measurable_sourceInitializedLaunchInput
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))

/-- Gluing uses only the actual launch event; its complement has no suffix. -/
def sourceInitializedSuffixObservation (source : SourceInput p) :
    Unit ⊕ SuffixCoreObservation p rate := by
  classical
  exact if h : source ∈
      ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) then
    Sum.inr (sourceInitializedSuffixCoreOnLaunch (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) ⟨source, h⟩)
  else Sum.inl ()

theorem measurable_sourceInitializedSuffixObservation :
    Measurable (sourceInitializedSuffixObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  classical
  exact Measurable.dite
    (measurable_inr.comp (measurable_sourceInitializedSuffixCoreOnLaunch
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)))
    measurable_const
    (ActualInitializationTerminalReadout.measurable_sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards))

/-- Unfold the existing actual construction, retaining its exact first trace. -/
private theorem sourceInitializedActualCompleteHistory_launch_constructor
    (source : SourceInput p)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source
      rewards C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
        p rate source rewards C_star C_h =
      .launchedBefore launch learnerSeed hlaunch hbefore
        (ActualCompletePhysicalHistory.runPostlaunchSuffixFromTrace p rate source rewards
          (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
            rewards C_star C_h launch learnerSeed hlaunch hbefore)
          (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
            rewards C_star C_h launch learnerSeed hlaunch hbefore).state
          (ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate source rewards
            (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
              rewards C_star C_h launch learnerSeed hlaunch hbefore)
            (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
              rewards C_star C_h launch learnerSeed hlaunch hbefore)
            (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_source
              p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore)
            (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_rewards
              p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore))) := by
  unfold ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
  dsimp only
  rw! [hlaunch]
  simp [hbefore]

/-- The glued observation equals the suffix of H's actual history on every
source. The first input/trace equalities are proved here, never supplied. -/
theorem sourceInitializedActualCompleteHistory_suffixObservation_eq
    (source : SourceInput p) :
    suffixObservationOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h) =
      sourceInitializedSuffixObservation (p := p) (rate := rate)
        (C_star := C_star) (C_h := C_h) (rewards := rewards) source := by
  classical
  by_cases hE : source ∈
    ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
  · rcases (ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) source).mp hE with
      ⟨launch, learnerSeed, hlaunch, hbefore⟩
    let next := ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock
      p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore
    let input := ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput
      p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore
    have hinput : ActualSourceInitializedLaunchMeasurability.sourceInitializedLaunchInput
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
        ⟨source, hE⟩ = ⟨next, input⟩ :=
      ActualSourceInitializedLaunchMeasurability.sourceInitializedLaunchInput_eq_actual
        source launch learnerSeed hlaunch hbefore
    have htrace : ActualCompletePhysicalHistory.foldMixedBlockFromInput p rate source rewards
        next input
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_source
          p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore)
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_rewards
          p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore) =
      ActualCompletePhysicalHistory.foldMixedBlock p rate source rewards next input.state := by
      have hsource : input.source = source :=
        ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_source
          p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore
      have hrewards : input.rewards = rewards :=
        ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_rewards
          p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore
      have h := ActualPostlaunchBlockMeasurability.foldMixedBlockFromInput_eq_foldMixedBlock input
      cases hsource
      cases hrewards
      exact h
    rw [sourceInitializedActualCompleteHistory_launch_constructor source launch
      learnerSeed hlaunch hbefore]
    simp only [suffixObservationOfCompleteHistory]
    unfold sourceInitializedSuffixObservation
    rw [dite_eq_left hE]
    unfold sourceInitializedSuffixCoreOnLaunch
    rw [hinput]
    dsimp only [runSuffixCoreOfLaunchInput, blockInputOfLaunchInput, blockInputOfPhysicalInput]
    rw [htrace]
    rfl
  · have hnone : suffixObservationOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h) = Sum.inl () := by
      cases ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h with
      | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
          exact (hE ((ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent_iff_actual_constructor
            (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
            (rewards := rewards) source).mpr
            ⟨launch, learnerSeed, hlaunch, hbefore⟩)).elim
      | launchedAtHorizon launch learnerSeed hlaunch hat => rfl
      | exhausted live hexhausted => rfl
    rw [hnone]
    unfold sourceInitializedSuffixObservation
    rw [dite_eq_right hE]

/-- The literal suffix projection of H's actual construction is measurable
on the entire original source, including both absent constructors. -/
theorem measurable_sourceInitializedActualCompleteHistory_suffixObservation :
    Measurable (fun source : SourceInput p =>
      suffixObservationOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h)) := by
  rw [funext sourceInitializedActualCompleteHistory_suffixObservation_eq]
  exact measurable_sourceInitializedSuffixObservation

/-- Whole-source measurability, with unrestricted shared constants and rewards. -/
theorem measurable_sourceInitializedActualCompleteHistoryObservation :
    Measurable (sourceInitializedActualCompleteHistoryObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)) := by
  exact ActualInitializationSourceObservation.measurable_sourceInitializedRunObservation.prodMk
    measurable_sourceInitializedActualCompleteHistory_suffixObservation

/-- The initialization part keeps the whole original source and the exact
initial carry, including the same two unrestricted constants. -/
theorem sourceInitializedActualCompleteHistoryObservation_input_coordinates
    (source : SourceInput p) :
    let observation := sourceInitializedActualCompleteHistoryObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) source
    observation.1.originalSource = source ∧
      observation.1.initialCarry =
        ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩ :=
  ActualInitializationSourceObservation.sourceInitializedRunObservation_input_coordinates source

/-- Suffix absence is exactly the complement of the actual strict-launch event. -/
theorem sourceInitializedActualCompleteHistoryObservation_suffix_absent_iff
    (source : SourceInput p) :
    (sourceInitializedActualCompleteHistoryObservation (p := p) (rate := rate)
      (C_star := C_star) (C_h := C_h) (rewards := rewards) source).2 = Sum.inl () ↔
      source ∉
        ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
  classical
  change suffixObservationOfCompleteHistory _ = Sum.inl () ↔ _
  rw [sourceInitializedActualCompleteHistory_suffixObservation_eq]
  unfold sourceInitializedSuffixObservation
  by_cases hE : source ∈
    ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
  · rw [dite_eq_left hE]
    exact iff_of_false Sum.inr_ne_inl (fun h => h hE)
  · rw [dite_eq_right hE]
    exact iff_of_true rfl hE

/-- A present suffix is equivalent to the actual strict pre-horizon launch. -/
theorem sourceInitializedActualCompleteHistoryObservation_suffix_present_iff
    (source : SourceInput p) :
    (∃ core, (sourceInitializedActualCompleteHistoryObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
      source).2 = Sum.inr core) ↔
      source ∈
        ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
          (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards) := by
  classical
  change (∃ core, suffixObservationOfCompleteHistory _ = Sum.inr core) ↔ _
  rw [sourceInitializedActualCompleteHistory_suffixObservation_eq]
  unfold sourceInitializedSuffixObservation
  by_cases hE : source ∈
    ActualInitializationTerminalReadout.sourceInitializedPreHorizonTerminalLaunchEvent
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
  · rw [dite_eq_left hE]
    exact ⟨fun _ => hE, fun _ => ⟨_, rfl⟩⟩
  · rw [dite_eq_right hE]
    exact ⟨fun ⟨_, h⟩ => (Sum.inl_ne_inr h).elim, fun h => (hE h).elim⟩

/-- The optional chronological step-code coordinates; absence stays absent. -/
def suffixStepCodeCoordinatesOfCompleteHistory {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    Unit ⊕ ActualPostlaunchSuffixMeasurability.LengthIndexObservation
      (ActualPostlaunchSuffixMeasurability.StepCodeObservation p rate) :=
  Sum.map id Prod.fst (suffixObservationOfCompleteHistory history)

/-- The optional boundary coordinates, retaining each actual boundary carry. -/
def suffixBoundaryCoordinatesOfCompleteHistory {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    Unit ⊕ ActualPostlaunchSuffixMeasurability.LengthIndexObservation
      (ActualPostlaunchSuffixMeasurability.BoundaryObservation p rate) :=
  Sum.map id (fun core => core.2.1) (suffixObservationOfCompleteHistory history)

/-- The optional cross-boundary coordinates retain the actual successor state. -/
def suffixCrossBoundaryCoordinatesOfCompleteHistory {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    Unit ⊕ ActualPostlaunchSuffixMeasurability.LengthIndexObservation
      (ActualPostlaunchSuffixMeasurability.CrossBoundaryObservation p rate) :=
  Sum.map id (fun core => core.2.2.1) (suffixObservationOfCompleteHistory history)

/-- The optional terminal code keeps the shortened final block's real state
and carry; neither absent constructor creates a terminal suffix record. -/
def suffixTerminalObservationOfCompleteHistory {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    Unit ⊕ ActualPostlaunchSuffixMeasurability.TerminalObservation p rate :=
  Sum.map id (fun core => core.2.2.2) (suffixObservationOfCompleteHistory history)

/-- Exact step-code reconstruction in all three H constructors. S's public
record decoder reconstructs the complete retained step from each listed code. -/
theorem suffixStepCodeCoordinatesOfCompleteHistory_eq_records {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    suffixStepCodeCoordinatesOfCompleteHistory history =
      match history with
      | .launchedBefore _ _ _ _ suffix =>
          Sum.inr (ActualPostlaunchBlockMeasurability.roundListCoordinates
            (suffix.records.map ActualPostlaunchSuffixMeasurability.recordStepCodeObservation))
      | .launchedAtHorizon _ _ _ _ => Sum.inl ()
      | .exhausted _ _ => Sum.inl () := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      exact congrArg Sum.inr
        (ActualPostlaunchSuffixMeasurability.postlaunchSuffix_stepCodeCoordinates_eq_records suffix)
  | launchedAtHorizon launch learnerSeed hlaunch hat => rfl
  | exhausted live hexhausted => rfl

/-- Exact boundary reconstruction; the S decoder returns H's actual outputs
and follower carry codes for every entry in the present branch. -/
theorem suffixBoundaryCoordinatesOfCompleteHistory_eq_records {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    suffixBoundaryCoordinatesOfCompleteHistory history =
      match history with
      | .launchedBefore _ _ _ _ suffix =>
          Sum.inr (ActualPostlaunchBlockMeasurability.roundListCoordinates
            (suffix.boundaries.map
              (ActualPostlaunchSuffixMeasurability.boundaryRecordObservation source)))
      | .launchedAtHorizon _ _ _ _ => Sum.inl ()
      | .exhausted _ _ => Sum.inl () := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      exact congrArg Sum.inr
        (ActualPostlaunchSuffixMeasurability.postlaunchSuffix_boundaryCoordinates_eq_records suffix)
  | launchedAtHorizon launch learnerSeed hlaunch hat => rfl
  | exhausted live hexhausted => rfl

/-- Exact cross-boundary reconstruction in the original source. S's decoder
identifies the stored state with H's existing cross-successor adapter. -/
theorem suffixCrossBoundaryCoordinatesOfCompleteHistory_eq_records {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    suffixCrossBoundaryCoordinatesOfCompleteHistory history =
      match history with
      | .launchedBefore _ _ _ _ suffix =>
          Sum.inr (ActualPostlaunchBlockMeasurability.roundListCoordinates
            (suffix.crossBoundaryRecords.map
              ActualPostlaunchSuffixMeasurability.crossBoundaryRecordObservation))
      | .launchedAtHorizon _ _ _ _ => Sum.inl ()
      | .exhausted _ _ => Sum.inl () := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      exact congrArg Sum.inr
        (ActualPostlaunchSuffixMeasurability.postlaunchSuffix_crossBoundaryCoordinates_eq_records
          suffix)
  | launchedAtHorizon launch learnerSeed hlaunch hat => rfl
  | exhausted live hexhausted => rfl

/-- Exact terminal reconstruction, including H's original final state and
boundary carry. Launch at the horizon has no post-horizon observation. -/
theorem suffixTerminalObservationOfCompleteHistory_eq_record {source : SourceInput p}
    (history : ActualCompletePhysicalHistory.CompleteHistory
      p rate source rewards C_star C_h) :
    suffixTerminalObservationOfCompleteHistory history =
      match history with
      | .launchedBefore _ _ _ _ suffix =>
          Sum.inr (ActualPostlaunchSuffixMeasurability.terminalBoundaryRecordObservation source
            (ActualPostlaunchSuffixMeasurability.postlaunchSuffixTerminalBoundaryRecord suffix))
      | .launchedAtHorizon _ _ _ _ => Sum.inl ()
      | .exhausted _ _ => Sum.inl () := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      exact congrArg Sum.inr
        (ActualPostlaunchSuffixMeasurability.postlaunchSuffix_terminalObservation_eq_record suffix)
  | launchedAtHorizon launch learnerSeed hlaunch hat => rfl
  | exhausted live hexhausted => rfl

theorem measurable_sourceInitializedActualCompleteHistory_stepCodeCoordinates :
    Measurable (fun source : SourceInput p =>
      suffixStepCodeCoordinatesOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h)) :=
  (measurable_id.sumMap measurable_fst).comp
    measurable_sourceInitializedActualCompleteHistoryObservation.snd

theorem measurable_sourceInitializedActualCompleteHistory_boundaryCoordinates :
    Measurable (fun source : SourceInput p =>
      suffixBoundaryCoordinatesOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h)) :=
  (measurable_id.sumMap measurable_snd.fst).comp
    measurable_sourceInitializedActualCompleteHistoryObservation.snd

theorem measurable_sourceInitializedActualCompleteHistory_crossBoundaryCoordinates :
    Measurable (fun source : SourceInput p =>
      suffixCrossBoundaryCoordinatesOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h)) :=
  (measurable_id.sumMap measurable_snd.snd.fst).comp
    measurable_sourceInitializedActualCompleteHistoryObservation.snd

theorem measurable_sourceInitializedActualCompleteHistory_terminalObservation :
    Measurable (fun source : SourceInput p =>
      suffixTerminalObservationOfCompleteHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
          p rate source rewards C_star C_h)) :=
  (measurable_id.sumMap measurable_snd.snd.snd).comp
    measurable_sourceInitializedActualCompleteHistoryObservation.snd

/-- Fix only the public output, retaining `J` and every original private array. -/
def fixedPublicPrivateSourceInitializedActualCompleteHistoryObservation
    (published : CompletePublicTable.PublishedOutput p)
    (privateCoordinates : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :=
  sourceInitializedActualCompleteHistoryObservation (p := p) (rate := rate)
    (C_star := C_star) (C_h := C_h) (rewards := rewards) (published, privateCoordinates)

theorem measurable_fixedPublicPrivateSourceInitializedActualCompleteHistoryObservation
    (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fixedPublicPrivateSourceInitializedActualCompleteHistoryObservation
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h) (rewards := rewards)
      published) :=
  measurable_sourceInitializedActualCompleteHistoryObservation.comp
    (measurable_const.prodMk measurable_id)

end Bandits.Support.ActualSourceCompleteSuffixObservation

end
