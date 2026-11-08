/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompletePhysicalRewards
public import Bandits.Support.ReferenceCorrectedLaunchMeasurability
public import Bandits.Support.ReferenceActiveHorizonMeasurability

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Measurability and expectation of complete reference reward

Sources: `sources/zip4/manuscript/01_introduction.tex:20-36`,
`sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/08_main_theorem.tex:26-48,67-75`, and
`sources/zip4/manuscript/06_interruptions.tex:355-362`.

The complete computed reward is Borel on the original source product. Its
literal fixed-public expectation integrates the same reward over every
extended private coordinate, including the original coordinator index.
These are internal measurable and integrable observables, not a regret or
manuscript-closure theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Bandits.Support.ReferenceCompleteRewardMeasurability

variable {p : ReferenceCompletePhysicalRewards.Parameters}

private abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput p
private abbrev PublishedOutput := CompletePublicTable.PublishedOutput p
private abbrev ExtendedPrivateCoordinates :=
  BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p

private def generatedCrossingSet (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Set (SourceInput (p := p)) :=
  {source | (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true}

private abbrev CrossingSource (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :=
  {source : SourceInput // source ∈ generatedCrossingSet rate rewards C_star C_h}

private def generatedActiveState (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : CrossingSource rate rewards C_star C_h) :
    ReferenceActivePhysicalStep.State p rate :=
  (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.1 rewards C_star C_h).get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z.1 rewards C_star C_h).2 z.2)

private theorem option_get_mem_iff_sum_inl
    {α : Type*} (o : Option α) (ho : o.isSome = true) (u : Set α) :
    o.get ho ∈ u ↔ Equiv.optionEquivSumPUnit α o ∈ Sum.inl '' u := by
  cases o with
  | none => simp at ho
  | some a => simp [Equiv.optionEquivSumPUnit]

private theorem measurable_option_get_of_isSome
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → Option α) (hf : Measurable f)
    (hsome : ∀ x, (f x).isSome = true) :
    Measurable (fun x => (f x).get (hsome x)) := by
  let optionSumEquiv : Option α ≃ α ⊕ PUnit := Equiv.optionEquivSumPUnit α
  have hsum : Measurable (fun x => optionSumEquiv (f x)) := by
    change Measurable (fun x => Equiv.optionEquivSumPUnit α (f x))
    exact measurable_comap_iff.mp hf
  intro u hu
  have hsumset : MeasurableSet ((Sum.inl : α → α ⊕ PUnit) '' u) :=
    MeasurableSet.inl_image hu
  have hpre := hsum hsumset
  have hpreEq : (fun x => (f x).get (hsome x)) ⁻¹' u =
      (fun x => optionSumEquiv (f x)) ⁻¹' (Sum.inl '' u) := by
    ext x
    exact option_get_mem_iff_sum_inl (f x) (hsome x) u
  rw [hpreEq]
  exact hpre

private theorem measurable_generatedActiveState
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      generatedActiveState rate rewards C_star C_h z) := by
  let launchCode := fun z : CrossingSource rate rewards C_star C_h =>
    (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.1 rewards C_star C_h).map
      (ReferenceActivePhysicalStepMeasurability.encodeState (p := p) (rate := rate))
  have hlaunchCode : Measurable launchCode :=
    (ReferenceCorrectedLaunchMeasurability.measurable_correctedLaunch_encodeState
      rate rewards C_star C_h).comp measurable_subtype_coe
  have hsome : ∀ z : CrossingSource rate rewards C_star C_h,
      (launchCode z).isSome = true := by
    intro z
    have hsomeActual :=
      (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z.1 rewards C_star C_h).2 z.2
    simp [launchCode, hsomeActual]
  have hget := measurable_option_get_of_isSome launchCode hlaunchCode hsome
  have hgetEq : (fun z : CrossingSource rate rewards C_star C_h =>
      (launchCode z).get (hsome z)) =
      fun z => ReferenceActivePhysicalStepMeasurability.encodeState
        (generatedActiveState rate rewards C_star C_h z) := by
    funext z
    cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z.1 rewards C_star C_h with
    | none =>
        have hsomeActual :=
          (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
            rate z.1 rewards C_star C_h).2 z.2
        simp [hlaunch] at hsomeActual
    | some active =>
        simp [launchCode, generatedActiveState, hlaunch]
  apply measurable_comap_iff.mpr
  change Measurable (fun z : CrossingSource rate rewards C_star C_h =>
    ReferenceActivePhysicalStepMeasurability.encodeState
      (generatedActiveState rate rewards C_star C_h z))
  rw [← hgetEq]
  exact hget

private theorem measurable_generatedCrossingStart
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h) := by
  apply measurable_to_nat
  intro z
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h
  have hfiber := ReferenceCorrectedLaunchMeasurability.measurableSet_generated_launch_start_fiber
    rate rewards C_star C_h start
  have hpull := hfiber.preimage
    (measurable_subtype_coe : Measurable (fun z : CrossingSource rate rewards C_star C_h => z.1))
  have hset : MeasurableSet
      {z' : CrossingSource rate rewards C_star C_h |
        ReferenceCompletePhysicalHistory.physicalStart rate z'.1 rewards C_star C_h = start} := by
    have hEq : {z' : CrossingSource rate rewards C_star C_h |
          ReferenceCompletePhysicalHistory.physicalStart rate z'.1 rewards C_star C_h = start} =
        (fun z' : CrossingSource rate rewards C_star C_h => z'.1) ⁻¹'
          {source : SourceInput |
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
            ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = start} := by
      ext z'
      constructor
      · intro hstart
        refine ⟨z'.property, ?_⟩
        simpa [ReferenceCompletePhysicalHistory.physicalStart,
          ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hstart
      · rintro ⟨_, hstart⟩
        simpa [ReferenceCompletePhysicalHistory.physicalStart,
          ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using hstart
    rw [hEq]
    exact hpull
  exact hset

private theorem measurable_completeSuffixReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun source : SourceInput =>
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
        ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum) := by
  classical
  let crossingSet := generatedCrossingSet rate rewards C_star C_h
  have hcrossingSet : MeasurableSet crossingSet := by
    change MeasurableSet {source : SourceInput |
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true}
    exact ReferenceCorrectedLaunchMeasurability.measurableSet_generated_crossing
      rate rewards C_star C_h
  let state := fun z : CrossingSource rate rewards C_star C_h =>
    generatedActiveState rate rewards C_star C_h z
  let launch := fun z : CrossingSource rate rewards C_star C_h =>
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate z.1 rewards C_star C_h
  have hlaunch : ∀ z : CrossingSource rate rewards C_star C_h,
      launch z = some (state z) := by
    intro z
    cases h : launch z with
    | none =>
        have hs := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z.1 rewards C_star C_h).2 z.2
        simp [launch, h] at hs
    | some active =>
        simp [launch, state, generatedActiveState, h]
  let start := fun z : CrossingSource rate rewards C_star C_h =>
    ReferenceCompletePhysicalHistory.physicalStart rate z.1 rewards C_star C_h
  let runInput : CrossingSource rate rewards C_star C_h →
      ReferenceActiveHorizonMeasurability.CalendarRunInput (p := p) (rate := rate) :=
    fun z =>
      ⟨(start z, (p.T - start z,
        (state z, (z.1.1.2,
          (ActualInitializationPhysicalStep.selectedRowIndex p z.1, rewards))))),
        ⟨by
          have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate z.1 rewards C_star C_h
          have hstart' : start z ≤ p.T := by simpa [start] using hstart
          exact Nat.le_of_eq (Nat.add_sub_of_le hstart'),
         ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
           rate z.1 rewards C_star C_h (state z) (hlaunch z)⟩⟩
  have hstart := measurable_generatedCrossingStart rate rewards C_star C_h
  have hstate := measurable_generatedActiveState rate rewards C_star C_h
  have hrows : Measurable (fun z : CrossingSource rate rewards C_star C_h => z.1.1.2) :=
    (measurable_snd.comp (measurable_fst.comp measurable_subtype_coe))
  have hselected : Measurable
      (fun z : CrossingSource rate rewards C_star C_h =>
        ActualInitializationPhysicalStep.selectedRowIndex p z.1) := by
    change Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z.1)
    exact (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp
      measurable_subtype_coe
  have hdata : Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      (state z, (z.1.1.2,
        (ActualInitializationPhysicalStep.selectedRowIndex p z.1, rewards)))) :=
    hstate.prodMk (hrows.prodMk (hselected.prodMk measurable_const))
  have hsub : Measurable (fun z : ℕ × ℕ => z.1 - z.2) :=
    measurable_of_countable _
  have hcount : Measurable (fun z : CrossingSource rate rewards C_star C_h => p.T - start z) :=
    hsub.comp (measurable_const.prodMk hstart)
  have hcalendar : Measurable (fun z : CrossingSource rate rewards C_star C_h =>
      (start z, (p.T - start z,
        (state z, (z.1.1.2,
          (ActualInitializationPhysicalStep.selectedRowIndex p z.1, rewards)))))) :=
    hstart.prodMk (hcount.prodMk hdata)
  have hrunInput : Measurable runInput := by
    exact hcalendar.subtype_mk (h := fun z => by
      constructor
      · have hstartLe := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z.1 rewards C_star C_h
        have hstartLe' : start z ≤ p.T := by simpa [start] using hstartLe
        exact Nat.le_of_eq (Nat.add_sub_of_le hstartLe')
      · exact ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z.1 rewards C_star C_h (state z) (hlaunch z))
  have hrunReward :=
    (ReferenceActiveHorizonMeasurability.measurable_calendarRunTotalReward
      (p := p) (rate := rate)).comp hrunInput
  let runReward := fun z : CrossingSource rate rewards C_star C_h =>
    ReferenceActiveHorizonMeasurability.calendarRunTotalReward (runInput z)
  have hpiecewise : Measurable (fun source : SourceInput =>
      if h : source ∈ crossingSet then runReward ⟨source, h⟩ else 0) :=
    hrunReward.dite measurable_const hcrossingSet
  let suffix := fun source : SourceInput =>
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
      ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum
  have hEq : suffix = fun source =>
      if h : source ∈ crossingSet then runReward ⟨source, h⟩ else 0 := by
    funext source
    by_cases hc : source ∈ crossingSet
    · let z : CrossingSource rate rewards C_star C_h := ⟨source, hc⟩
      have hsum := (ReferenceCompletePhysicalRewards.completeSuffixReward_eq_run_totalReward
        rate source rewards C_star C_h (state z) (hlaunch z)).2
      have hcalendar : runReward z =
          (ReferenceActivePhysicalHorizon.run (state z) source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (by
              have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                rate source rewards C_star C_h
              omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate source rewards C_star C_h (state z) (hlaunch z))).totalReward := by
        rfl
      rw [dite_eq_left hc]
      change suffix source = runReward z
      exact hsum.trans hcalendar.symm
    · have hnoCross : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing = none := by
        cases hcross : (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing with
        | none => rfl
        | some crossing =>
            have hmem : source ∈ crossingSet := by
              change (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true
              simp [hcross]
            exact (hc hmem).elim
      have hnone := (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
        rate source rewards C_star C_h).2 hnoCross
      have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h = [] := by
        simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
      simp only [suffix, hrecords, List.map_nil, List.sum_nil]
      rw [dite_eq_right hc]
  change Measurable suffix
  rw [hEq]
  exact hpiecewise

/-- The complete physical received reward is Borel on the original joint
source input, for the fixed original grid reward table and shared constants. -/
theorem measurable_completeReward_source
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h) := by
  let suffix := fun source : SourceInput =>
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
      ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum
  have hprefix := ReferenceInitializationPhysicalRewards.measurable_source_reference_outputBoundaryReward
    rewards C_star C_h rate
  have hsuffix := measurable_completeSuffixReward rate rewards C_star C_h
  have hsplit : (fun source : SourceInput =>
      ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h) =
      fun source =>
        ReferenceInitializationPhysicalRewards.outputBoundaryReward p
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) +
        suffix source := by
    funext source
    rw [ReferenceCompletePhysicalRewards.completeReward_calendar_split]
    rfl
  rw [hsplit]
  exact hprefix.add hsuffix

private theorem completeReward_norm_le
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (source : SourceInput)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ‖ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h‖ ≤
      (p.m : ℝ) * (p.T : ℝ) := by
  have h := ReferenceCompletePhysicalRewards.completeReward_bounds
    rate source rewards C_star C_h
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- The complete reward is integrable under the existing joint source law. -/
theorem integrable_completeReward_source
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Integrable (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let f := fun source : SourceInput =>
    ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
  have hf : Measurable f := measurable_completeReward_source rate rewards C_star C_h
  refine (integrable_const ((p.m : ℝ) * (p.T : ℝ))).mono' hf.aestronglyMeasurable ?_
  filter_upwards with source
  exact completeReward_norm_le rate source rewards C_star C_h

/-- Every fixed public output has a Borel source section on the full extended
private carrier. -/
theorem measurable_completeReward_privateSection
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p) :
    Measurable (fun privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
        rewards C_star C_h) := by
  exact (measurable_completeReward_source rate rewards C_star C_h).comp
    (measurable_const.prodMk measurable_id)

/-- Every fixed public output has an integrable complete reward section over
the entire extended private law, with the original index coordinate retained.
-/
theorem integrable_completeReward_privateSection
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p) :
    Integrable (fun privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p =>
      ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
        rewards C_star C_h)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  let f := fun privateCoords : ExtendedPrivateCoordinates =>
    ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
      rewards C_star C_h
  have hf : Measurable f := measurable_completeReward_privateSection
    rate rewards C_star C_h published
  refine (integrable_const ((p.m : ℝ) * (p.T : ℝ))).mono' hf.aestronglyMeasurable ?_
  filter_upwards with privateCoords
  exact completeReward_norm_le rate (published, privateCoords) rewards C_star C_h

/-- Every fixed extended private coordinate has a Borel public section on the
whole published-output space. -/
theorem measurable_completeReward_publicSection
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    Measurable (fun published : CompletePublicTable.PublishedOutput p =>
      ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
        rewards C_star C_h) := by
  exact (measurable_completeReward_source rate rewards C_star C_h).comp
    (measurable_id.prodMk measurable_const)

/-- Every fixed extended private coordinate has an integrable complete reward
section over the full published-output law. -/
theorem integrable_completeReward_publicSection
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p) :
    Integrable (fun published : CompletePublicTable.PublishedOutput p =>
      ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
        rewards C_star C_h)
      (CompletePublicTable.publishedOutputMeasure p) := by
  let f := fun published : CompletePublicTable.PublishedOutput p =>
    ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
      rewards C_star C_h
  have hf : Measurable f := measurable_completeReward_publicSection
    rate rewards C_star C_h privateCoords
  refine (integrable_const ((p.m : ℝ) * (p.T : ℝ))).mono' hf.aestronglyMeasurable ?_
  filter_upwards with published
  exact completeReward_norm_le rate (published, privateCoords) rewards C_star C_h

/-- The literal fixed-public private expectation of the same complete
computed reference reward, integrated over all extended private coordinates.
-/
noncomputable def completePrivateExpectedReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p) : ℝ :=
  ∫ privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
    ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
      rewards C_star C_h ∂ BootstrapPrivateRoundStreams.extendedPrivateLaw p

/-- The fixed-public law is the existing extended-private law, independently
of the fixed published output and reward value. -/
theorem completePrivateExpectedReward_eq_fixedPublicPrivateLaw
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p)
    (rewardMatrix : FiniteBanditModel.RewardMatrix p.T p.K) :
    completePrivateExpectedReward rate rewards C_star C_h published =
      ∫ privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
        ReferenceCompletePhysicalRewards.completeReward rate (published, privateCoords)
          rewards C_star C_h ∂
            BootstrapPrivateRoundStreams.fixedPublicPrivateLaw p published rewardMatrix := rfl

/-- The literal private expected reward is Borel in every published output. -/
theorem measurable_completePrivateExpectedReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Measurable (fun published : CompletePublicTable.PublishedOutput p =>
      completePrivateExpectedReward rate rewards C_star C_h published) := by
  let f : CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p → ℝ :=
    fun source => ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
  have hf : Measurable f := measurable_completeReward_source rate rewards C_star C_h
  change Measurable (fun published : CompletePublicTable.PublishedOutput p =>
    ∫ privateCoords : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
      f (published, privateCoords)
      ∂ BootstrapPrivateRoundStreams.extendedPrivateLaw p)
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := BootstrapPrivateRoundStreams.extendedPrivateLaw p)).measurable

/-- The literal private expectation retains the complete reward's pointwise
`[0,mT]` bound for every published output. -/
theorem completePrivateExpectedReward_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : CompletePublicTable.PublishedOutput p) :
    completePrivateExpectedReward rate rewards C_star C_h published ∈
      Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
  have hf := integrable_completeReward_privateSection rate rewards C_star C_h published
  have hnonneg := integral_mono (integrable_const (0 : ℝ)) hf (by
    intro privateCoords
    exact (ReferenceCompletePhysicalRewards.completeReward_bounds rate
      (published, privateCoords) rewards C_star C_h).1)
  have hupper := integral_mono hf
    (integrable_const ((p.m : ℝ) * (p.T : ℝ))) (by
      intro privateCoords
      exact (ReferenceCompletePhysicalRewards.completeReward_bounds rate
        (published, privateCoords) rewards C_star C_h).2)
  constructor
  · simpa [completePrivateExpectedReward] using hnonneg
  · simpa [completePrivateExpectedReward] using hupper

/-- The fixed-public private expected reward is integrable over the original
published-output measure. -/
theorem integrable_completePrivateExpectedReward
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    Integrable (fun published : CompletePublicTable.PublishedOutput p =>
      completePrivateExpectedReward rate rewards C_star C_h published)
      (CompletePublicTable.publishedOutputMeasure p) := by
  have hf := measurable_completePrivateExpectedReward rate rewards C_star C_h
  refine (integrable_const ((p.m : ℝ) * (p.T : ℝ))).mono' hf.aestronglyMeasurable ?_
  filter_upwards with published
  have h := completePrivateExpectedReward_bounds rate rewards C_star C_h published
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- Fubini's identity for the actual joint source product law and the literal
fixed-public private expected reward. -/
theorem integral_completeReward_eq_publicExpectation
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ∫ source : BootstrapPrivateRoundStreams.SourceInput p,
      ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
        ∂ BootstrapPrivateRoundStreams.sourceInputLaw p =
      ∫ published : CompletePublicTable.PublishedOutput p,
        completePrivateExpectedReward rate rewards C_star C_h published
          ∂ CompletePublicTable.publishedOutputMeasure p := by
  let f := fun source : SourceInput =>
    ReferenceCompletePhysicalRewards.completeReward rate source rewards C_star C_h
  change (∫ source : CompletePublicTable.PublishedOutput p ×
        BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p, f source
      ∂ (CompletePublicTable.publishedOutputMeasure p).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) =
    ∫ published : CompletePublicTable.PublishedOutput p,
      completePrivateExpectedReward rate rewards C_star C_h published
        ∂ CompletePublicTable.publishedOutputMeasure p
  rw [MeasureTheory.integral_prod f (integrable_completeReward_source rate rewards C_star C_h)]
  rfl

end Bandits.Support.ReferenceCompleteRewardMeasurability

end
