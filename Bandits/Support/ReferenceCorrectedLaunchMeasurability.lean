/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchCarriedMeasurability
public import Bandits.Support.ReferenceCorrectedInitializationLaunch
public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# Measurability of the original-source corrected launch

For the original complete source input, whole grid reward table, fixed shared
constants and accepted rate, this module proves Borel measurability of the
literal corrected launch and of its exact canonical state code. The crossing
state is taken from `ReferenceCorrectedInitializationLaunch.correctedLaunch`;
its crossing characterization supplies the generated ordinary follower
states and the initialized proposal memory. The actual terminal ordinary
carried-state producer supplies the complete ordered buffers and their real
saved-scalar fibres.

Sources: `sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/06_interruptions.tex:192-209,235-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The three direct project imports were independently reviewed and admitted at
the exact bytes recorded in
`private-audit-archive/turn-00170-publication-corrected-launch-borel.json`:
`ReferencePrelaunchCarriedMeasurability` (SHA-256
`61d7584d043f035ecf751d3ba7d593a08ab9af25c066cbcd7792dce4a86e96a3`),
`ReferenceCorrectedInitializationLaunch` (SHA-256
`949c9d72f63b83ed18e6824e61aaae7247bf787d71e0cdedba72c10ed80abe77`), and
`ReferenceActivePhysicalStepMeasurability` (SHA-256
`11b431bc05c6971b331016537f4e67f457e80a9c45d76940874cb30d37c6b314`).

These are deterministic internal measurability and reconstruction results.
They do not prove a horizon fold, stochastic law, regret assertion, or
manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceCorrectedLaunchMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceCorrectedInitializationLaunch.RateInput

private def generatedOutput {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : ReferenceInitializationRun.Boundary p :=
  ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)

private def generatedCrossing {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Prop :=
  (generatedOutput rate source rewards C_star C_h).crossing.isSome = true

private theorem measurable_generatedOutput {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (generatedOutput rate (p := p) · rewards C_star C_h) := by
  have hcoordinates : Measurable
      (ReferencePrelaunchCarriedMeasurability.sourceCoordinates (p := p)) :=
    ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
  have hinputOutput :=
    (ReferenceInitializationMeasurability.measurable_output p C_star C_h rate.eta rewards).comp
      hcoordinates
  have hsameInput :
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceInitializationRun.output
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h
            rate.eta rewards
            (ReferencePrelaunchCarriedMeasurability.sourceCoordinates source))) =
      (fun source => generatedOutput rate source rewards C_star C_h) := by
    funext source
    change ReferenceInitializationRun.output
        (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h
          rate.eta rewards
          (ReferencePrelaunchCarriedMeasurability.sourceCoordinates source)) =
      ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    exact congrArg ReferenceInitializationRun.output
      (ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput
        source rewards C_star C_h rate)
  rw [← hsameInput]
  exact hinputOutput

theorem measurableSet_generated_crossing {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    MeasurableSet {source : BootstrapPrivateRoundStreams.SourceInput p |
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true} := by
  change MeasurableSet
    ((fun source => generatedOutput rate source rewards C_star C_h) ⁻¹'
      {b : ReferenceInitializationRun.Boundary p | b.crossing.isSome = true})
  exact measurable_generatedOutput rate rewards C_star C_h
    (MeasurableSpace.measurableSet_top :
      MeasurableSet {b : ReferenceInitializationRun.Boundary p | b.crossing.isSome = true})

theorem measurableSet_generated_no_crossing {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    MeasurableSet {source : BootstrapPrivateRoundStreams.SourceInput p |
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing = none} := by
  change MeasurableSet
    ((fun source => generatedOutput rate source rewards C_star C_h) ⁻¹'
      {b : ReferenceInitializationRun.Boundary p | b.crossing = none})
  exact measurable_generatedOutput rate rewards C_star C_h
    (MeasurableSpace.measurableSet_top :
      MeasurableSet {b : ReferenceInitializationRun.Boundary p | b.crossing = none})

/-- The launch-start fibre includes a crossing at the terminal elapsed time. -/
theorem measurableSet_generated_launch_start_fiber {p : Parameters}
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) :
    MeasurableSet {source : BootstrapPrivateRoundStreams.SourceInput p |
      (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s} := by
  change MeasurableSet
    ((fun source => generatedOutput rate source rewards C_star C_h) ⁻¹'
      {b : ReferenceInitializationRun.Boundary p |
        b.crossing.isSome = true ∧ ReferenceInitializationRun.elapsed p b.completed = s})
  exact measurable_generatedOutput rate rewards C_star C_h
    (MeasurableSpace.measurableSet_top :
      MeasurableSet {b : ReferenceInitializationRun.Boundary p |
        b.crossing.isSome = true ∧ ReferenceInitializationRun.elapsed p b.completed = s})

private abbrev CrossingSource {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  {source : BootstrapPrivateRoundStreams.SourceInput p //
    generatedCrossing rate source rewards C_star C_h}

private def crossingState {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : generatedCrossing rate source rewards C_star C_h) :
    ReferenceActivePhysicalStep.State p rate :=
  (ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h).get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hc)

private theorem crossingState_correctedLaunch {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : generatedCrossing rate source rewards C_star C_h) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some (crossingState rate source rewards C_star C_h hc) := by
  have hsome :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hc
  cases hlaunch :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h with
  | none => simp [hlaunch] at hsome
  | some active => simp [crossingState, hlaunch]

private theorem crossingState_spec {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : generatedCrossing rate source rewards C_star C_h) :
    (crossingState rate source rewards C_star C_h hc).coordinator = .first ∧
    (crossingState rate source rewards C_star C_h hc).upDecoderBank =
      CoordinatorUpReception.initialUpDecoderBank p ∧
    (∀ i, some ((crossingState rate source rewards C_star C_h hc).activations i) =
      (generatedOutput rate source rewards C_star C_h).activation
        (ActualReferenceInitializationBlock.refFollower i)) ∧
    (∀ i, (crossingState rate source rewards C_star C_h hc).followers i =
      .ordinary
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (generatedOutput rate source rewards C_star C_h)
          (ActualReferenceInitializationBlock.refFollower i))
        (ActiveFollowerLifecycle.initialMemory p)) := by
  obtain ⟨active, ⟨hlaunch, hcoordinator, hbank, hactivations, hfollower⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hc
  have hstate : crossingState rate source rewards C_star C_h hc = active := by
    simp [crossingState, hlaunch]
  exact ⟨by simpa [hstate] using hcoordinator,
    by simpa [hstate] using hbank,
    by intro i; simpa only [hstate, generatedOutput] using hactivations i,
    by intro i; simpa only [hstate, generatedOutput] using hfollower i⟩

private theorem crossingState_activation_iff {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : generatedCrossing rate source rewards C_star C_h)
    (i : Fin (p.m - 1)) (a : ReferencePrelaunchFollower.Activation p) :
    (crossingState rate source rewards C_star C_h hc).activations i = a ↔
      (generatedOutput rate source rewards C_star C_h).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a := by
  rw [← (crossingState_spec rate source rewards C_star C_h hc).2.2.1 i]
  simp

private theorem measurable_sum_dite_subtype {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (s : Set Ω) (hs : MeasurableSet s)
    (f : {x : Ω // x ∈ s} → A) (hf : Measurable f) :
    Measurable (fun x : Ω =>
      if h : x ∈ s then Sum.inl (f ⟨x, h⟩) else Sum.inr PUnit.unit) := by
  intro u hu
  have hsub : MeasurableSet
      {z : {x : Ω // x ∈ s} | Sum.inl (f z) ∈ u} :=
    (measurable_inl.comp hf) hu
  obtain ⟨v, hv, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hsub
  have hpreimage :
      (fun x : Ω => if h : x ∈ s then Sum.inl (f ⟨x, h⟩) else Sum.inr PUnit.unit) ⁻¹' u =
        (s ∩ v) ∪ (if Sum.inr PUnit.unit ∈ u then sᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ s
    · have hmem : Sum.inl (f ⟨x, hx⟩) ∈ u ↔ x ∈ v := by
        have heval := congrArg (fun t : Set {z : Ω // z ∈ s} => (⟨x, hx⟩ : {z : Ω // z ∈ s}) ∈ t) hpre
        simpa using heval.symm
      simp [hx, hmem]
    · simp [hx]
  rw [hpreimage]
  by_cases hnone : Sum.inr PUnit.unit ∈ u
  · simpa [hnone] using (hs.inter hv).union hs.compl
  · simpa [hnone] using (hs.inter hv).union MeasurableSet.empty

private theorem measurable_option_dite_subtype {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (s : Set Ω) (hs : MeasurableSet s)
    (f : {x : Ω // x ∈ s} → A) (hf : Measurable f) :
    Measurable (fun x : Ω => if h : x ∈ s then some (f ⟨x, h⟩) else none) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x : Ω =>
    Equiv.optionEquivSumPUnit A
      (if h : x ∈ s then some (f ⟨x, h⟩) else none))
  have hsum := measurable_sum_dite_subtype s hs f hf
  have heq :
      (fun x : Ω => Equiv.optionEquivSumPUnit A
        (if h : x ∈ s then some (f ⟨x, h⟩) else none)) =
      (fun x : Ω => if h : x ∈ s then Sum.inl (f ⟨x, h⟩) else Sum.inr PUnit.unit) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx, Equiv.optionEquivSumPUnit]
  rw [heq]
  exact hsum

private theorem measurable_sourceOrdinaryInitialMemoryIncoming {p : Parameters}
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        (.ordinary
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p))) := by
  change Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
    some
      (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
          (ActualReferenceInitializationBlock.refFollower i)),
        FollowerLifecycleMeasurability.localMemoryCode
          (ActiveFollowerLifecycle.initialMemory p)))
  have hcarry :=
    ReferencePrelaunchCarriedMeasurability.measurable_sourceTerminalOrdinaryCarriedState
      rate C_star C_h rewards (ActualReferenceInitializationBlock.refFollower i)
  have hpair := hcarry.prodMk
    (measurable_const : Measurable (fun _ : BootstrapPrivateRoundStreams.SourceInput p =>
      FollowerLifecycleMeasurability.localMemoryCode
        (ActiveFollowerLifecycle.initialMemory p)))
  apply (measurable_comap_iff).2
  change Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
    FollowerPrepareJointMeasurability.incomingConfigurationToSum
      (some
        (FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i)),
          FollowerLifecycleMeasurability.localMemoryCode
            (ActiveFollowerLifecycle.initialMemory p))))
  simp only [FollowerPrepareJointMeasurability.incomingConfigurationToSum]
  exact measurable_inr.comp hpair

private theorem measurable_crossingState_encodeState {p : Parameters}
    (rate : RateInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      ReferenceActivePhysicalStepMeasurability.encodeState
        (crossingState rate z.1 rewards C_star C_h z.2)) := by
  let state := fun z : CrossingSource rate rewards C_star C_h =>
    crossingState rate z.1 rewards C_star C_h z.2
  have hcoordinatorEq :
      (fun z => ReferenceActivePhysicalStepMeasurability.encodeCoordinator
        (state z).coordinator) =
        fun _ : CrossingSource rate rewards C_star C_h =>
          (Sum.inl () : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate) := by
    funext z
    simp [state, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      (crossingState_spec rate z.1 rewards C_star C_h z.2).1]
  have hbankEq : (fun z : CrossingSource rate rewards C_star C_h => (state z).upDecoderBank) =
      fun _ => CoordinatorUpReception.initialUpDecoderBank p := by
    funext z
    exact (crossingState_spec rate z.1 rewards C_star C_h z.2).2.1
  have hactivation (i : Fin (p.m - 1)) :
      Measurable (fun z : CrossingSource rate rewards C_star C_h => (state z).activations i) := by
    apply FollowerDownMeasurability.measurable_of_countable_fibers
    intro a
    have houtput : Measurable
        (fun z : CrossingSource rate rewards C_star C_h =>
          generatedOutput rate z.1 rewards C_star C_h) :=
      (measurable_generatedOutput rate rewards C_star C_h).comp measurable_subtype_coe
    have hsourceFiber : MeasurableSet
        {z : CrossingSource rate rewards C_star C_h |
          (generatedOutput rate z.1 rewards C_star C_h).activation
            (ActualReferenceInitializationBlock.refFollower i) = some a} :=
      houtput (MeasurableSpace.measurableSet_top :
        MeasurableSet {b : ReferenceInitializationRun.Boundary p |
          b.activation (ActualReferenceInitializationBlock.refFollower i) = some a})
    have heq :
        {z : CrossingSource rate rewards C_star C_h | (state z).activations i = a} =
          {z | (generatedOutput rate z.1 rewards C_star C_h).activation
            (ActualReferenceInitializationBlock.refFollower i) = some a} := by
      ext z
      exact crossingState_activation_iff rate z.1 rewards C_star C_h z.2 i a
    rw [heq]
    exact hsourceFiber
  have hactivations : Measurable
      (fun z : CrossingSource rate rewards C_star C_h => (state z).activations) :=
    measurable_pi_iff.mpr hactivation
  have hfollower (i : Fin (p.m - 1)) :
      Measurable (fun z : CrossingSource rate rewards C_star C_h =>
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
          ((state z).followers i)) := by
    have hsource : Measurable (fun z : CrossingSource rate rewards C_star C_h =>
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
          (.ordinary
            (ReferenceInitializationRun.ordinary
              (ActualReferenceInitializationBlock.referenceInput z.1 rewards C_star C_h rate)
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput z.1 rewards C_star C_h rate))
              (ActualReferenceInitializationBlock.refFollower i))
            (ActiveFollowerLifecycle.initialMemory p))) :=
      (measurable_sourceOrdinaryInitialMemoryIncoming rate rewards C_star C_h i).comp
        (measurable_subtype_coe :
          Measurable (fun z : CrossingSource rate rewards C_star C_h => z.1))
    have heq :
        (fun z : CrossingSource rate rewards C_star C_h =>
          FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
            ((state z).followers i)) =
          (fun z =>
            FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
              (.ordinary
                (ReferenceInitializationRun.ordinary
                  (ActualReferenceInitializationBlock.referenceInput z.1 rewards C_star C_h rate)
                  (ReferenceInitializationRun.output
                    (ActualReferenceInitializationBlock.referenceInput z.1 rewards C_star C_h rate))
                  (ActualReferenceInitializationBlock.refFollower i))
                (ActiveFollowerLifecycle.initialMemory p))) := by
      funext z
      rw [(crossingState_spec rate z.1 rewards C_star C_h z.2).2.2.2 i]
      rfl
    rw [heq]
    exact hsource
  have hfollowerCodes : Measurable
      (fun z : CrossingSource rate rewards C_star C_h => fun i =>
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
          ((state z).followers i)) :=
    measurable_pi_iff.mpr hfollower
  change Measurable (fun z : CrossingSource rate rewards C_star C_h =>
    (ReferenceActivePhysicalStepMeasurability.encodeCoordinator (state z).coordinator,
      ((state z).upDecoderBank,
        ((state z).activations,
          fun i => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
            ((state z).followers i)))))
  have hcoordinator : Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      ReferenceActivePhysicalStepMeasurability.encodeCoordinator (state z).coordinator) := by
    rw [hcoordinatorEq]
    exact measurable_const
  have hbank : Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      (state z).upDecoderBank) := by
    rw [hbankEq]
    exact measurable_const
  exact hcoordinator.prodMk (hbank.prodMk (hactivations.prodMk hfollowerCodes))

private theorem measurable_crossingState {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      crossingState rate z.1 rewards C_star C_h z.2) := by
  apply measurable_comap_iff.mpr
  exact measurable_crossingState_encodeState rate rewards C_star C_h

/-- The actual corrected state is Borel in the existing canonical comap
measurable space. The option branch is glued only after proving the generated
crossing subtype map measurable. -/
theorem measurable_correctedLaunch {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h) := by
  let crossingSet : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
    {source | generatedCrossing rate source rewards C_star C_h}
  have hcrossingSet : MeasurableSet crossingSet :=
    measurableSet_generated_crossing rate rewards C_star C_h
  have hglued := measurable_option_dite_subtype crossingSet hcrossingSet
    (fun z : CrossingSource rate rewards C_star C_h =>
      crossingState rate z.1 rewards C_star C_h z.2)
    (measurable_crossingState rate rewards C_star C_h)
  have heq :
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h) =
      (fun source => if h : source ∈ crossingSet then
        some (crossingState rate source rewards C_star C_h h) else none) := by
    funext source
    by_cases hc : generatedCrossing rate source rewards C_star C_h
    · simp only [crossingSet, Set.mem_ofPred_eq, dite_eq_left hc]
      exact crossingState_correctedLaunch rate source rewards C_star C_h hc
    · have hnone : (generatedOutput rate source rewards C_star C_h).crossing = none := by
        cases h : (generatedOutput rate source rewards C_star C_h).crossing with
        | none => rfl
        | some crossing => exact (hc (by simp [generatedCrossing, h])).elim
      have hlaunch :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
          rate source rewards C_star C_h).2 hnone
      simp only [crossingSet, Set.mem_ofPred_eq, dite_eq_right hc, hlaunch]
  rw [heq]
  exact hglued

/-- The literal `Option.map encodeState` code of the same corrected launch is
Borel on every original complete source input. -/
theorem measurable_correctedLaunch_encodeState {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      (ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h).map
        (ReferenceActivePhysicalStepMeasurability.encodeState (p := p) (rate := rate))) := by
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap
    (ReferenceActivePhysicalStepMeasurability.encodeState (p := p) (rate := rate))
    ReferenceActivePhysicalStepMeasurability.measurable_encodeState
      (fun source => ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h)
    (measurable_correctedLaunch rate rewards C_star C_h)

/-- Encoding and then decoding preserves the exact same actual corrected
constructor, including its none exhaustion branch. -/
theorem correctedLaunch_decode_encode {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Option.map (ReferenceActivePhysicalStepMeasurability.decodeState (p := p) (rate := rate))
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h).map
        (ReferenceActivePhysicalStepMeasurability.encodeState (p := p) (rate := rate))) =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h := by
  cases ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h <;>
    simp [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]

end Bandits.Support.ReferenceCorrectedLaunchMeasurability

end
