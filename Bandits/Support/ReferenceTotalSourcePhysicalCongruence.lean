/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceTotalSourcePairCoupling
public import Bandits.Support.ReferenceCompleteRewardMeasurability

/-!
# Physical congruence for fixed-time original-source resampling

Sources: `sources/zip4/manuscript/06_interruptions.tex:376-426`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-46`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

All computations below are projections of the existing corrected reference.
The retained source includes every original private coordinate, including J.
This is internal fixed-time physical congruence, not a chronological logical
coupling, an exceptional-event probability bound, or a regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceTotalSourcePhysicalCongruence

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceRetainedSourceCoupling.RateInput
abbrev SourceInput := ReferenceRetainedSourceCoupling.SourceInput
abbrev TimeControl := ReferenceRetainedSourceCoupling.TimeControl

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance controlPairMeasurableSpace (p : Parameters) :
    MeasurableSpace (ReferenceRetainedSourceCoupling.ControlPair p) :=
  inferInstanceAs (MeasurableSpace (TimeControl p × TimeControl p))

private instance scalarMeasurableEq : MeasurableEq ContinuousLearningRows.Scalar where
  measurableSet_diagonal := by
    have h : MeasurableSet {z : ContinuousLearningRows.Scalar × ContinuousLearningRows.Scalar |
        (z.1 : ℝ) = (z.2 : ℝ)} := measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have he : Set.diagonal ContinuousLearningRows.Scalar =
        {z : ContinuousLearningRows.Scalar × ContinuousLearningRows.Scalar |
          (z.1 : ℝ) = (z.2 : ℝ)} := by
      ext z
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [he]
    exact h

private instance prodMeasurableEq {α β : Type*} [MeasurableSpace α] [MeasurableEq α]
    [MeasurableSpace β] [MeasurableEq β] : MeasurableEq (α × β) where
  measurableSet_diagonal := by
    have hleft : MeasurableSet {z : (α × β) × (α × β) | z.1.1 = z.2.1} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have hright : MeasurableSet {z : (α × β) × (α × β) | z.1.2 = z.2.2} :=
      measurableSet_eq_fun (by fun_prop) (by fun_prop)
    have he : Set.diagonal (α × β) =
        {z : (α × β) × (α × β) | z.1.1 = z.2.1} ∩ {z | z.1.2 = z.2.2} := by
      ext z
      simp only [Set.mem_diagonal_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Prod.ext_iff]
    rw [he]
    exact hleft.inter hright

private instance piMeasurableEq {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableEq (α i)] : MeasurableEq (∀ i, α i) where
  measurableSet_diagonal := by
    have he : Set.diagonal (∀ i, α i) =
        ⋂ i, {z : (∀ i, α i) × (∀ i, α i) | z.1 i = z.2 i} := by
      ext z
      simp only [Set.mem_diagonal_iff, Set.mem_iInter, Set.mem_ofPred_eq, funext_iff]
    rw [he]
    exact MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) (by fun_prop)

private instance sourceMeasurableEq (p : Parameters) : MeasurableEq (SourceInput p) := by
  exact prodMeasurableEq

private instance publishedRemainderMeasurableEq (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    MeasurableEq (ReferenceFixedTimeSourceControlCoupling.FixedControlPublishedRemainder p q t) := by
  let : MeasurableEq (ReferenceSelectedAffinePairLaw.Other t → TimeControl p) :=
    piMeasurableEq
  let : MeasurableEq (ReferenceSelectedAffinePairLaw.Other q → CompletePublicTable.CompleteRow p) :=
    piMeasurableEq
  let : MeasurableEq (CompletePublicTable.ForwardRow p ×
      (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) := prodMeasurableEq
  let : MeasurableEq ((CompletePublicTable.ForwardRow p ×
      (ReferenceSelectedAffinePairLaw.Other t → TimeControl p)) ×
      (ReferenceSelectedAffinePairLaw.Other q → CompletePublicTable.CompleteRow p)) := prodMeasurableEq
  exact prodMeasurableEq

private instance remainderMeasurableEq (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :
    MeasurableEq (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) := by
  exact prodMeasurableEq

variable {p : Parameters} (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "X" => ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart rate rewards C_star C_h q t s hs control0
local notation "src" => ReferenceGeneratedActivePrefixFactor.splitSource q t

/-- The crossing and elapsed facts are generated on every reconstruction. -/
theorem retained_source_facts (x : X) (u : TimeControl p) :
    (ReferenceCompletePhysicalHistory.generatedBoundary rate (src u x.1)
      rewards C_star C_h).crossing.isSome = true ∧
    ReferenceCompletePhysicalHistory.physicalStart rate (src u x.1) rewards C_star C_h = s := by
  exact ReferenceGeneratedActivePrefixFactor.launchStart_source_facts rate rewards C_star C_h
    q t u x.1 x.2.1 s hs
    ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s x.1 x.2.1 control0 u).mp x.2.2)

/-- On an actual active stratum, changing the removed control preserves the
produced initialization boundary and all ordinary follower states. No matched
initialization history is assumed. -/
theorem retained_initialization_eq (x : X) (u v : TimeControl p) :
    ReferenceCompletePhysicalHistory.generatedBoundary rate (src u x.1) rewards C_star C_h =
      ReferenceCompletePhysicalHistory.generatedBoundary rate (src v x.1) rewards C_star C_h ∧
    (fun i => ReferenceInitializationRun.ordinary
      (ReferenceCompletePhysicalHistory.generatedInput rate (src u x.1) rewards C_star C_h)
      (ReferenceCompletePhysicalHistory.generatedBoundary rate (src u x.1) rewards C_star C_h) i) =
    (fun i => ReferenceInitializationRun.ordinary
      (ReferenceCompletePhysicalHistory.generatedInput rate (src v x.1) rewards C_star C_h)
      (ReferenceCompletePhysicalHistory.generatedBoundary rate (src v x.1) rewards C_star C_h) i) := by
  have hu := retained_source_facts rate rewards C_star C_h q t s hs control0 x u
  have hv := retained_source_facts rate rewards C_star C_h q t s hs control0 x v
  have hobs := (ReferenceInitializationControlRemainder.stoppedObservationFactor_control_independent rate rewards C_star C_h q t
    x.1 x.2.1 u v s hs).2
  have hcu : ReferenceInitializationControlRemainder.stoppedCrossedBy rate rewards C_star C_h (src u x.1) s := by
    exact ⟨hu.1, hu.2.le⟩
  have hcv : ReferenceInitializationControlRemainder.stoppedCrossedBy rate rewards C_star C_h (src v x.1) s := by
    exact ⟨hv.1, hv.2.le⟩
  dsimp only [ReferenceGeneratedActivePrefixFactor.splitSource] at hcu hcv
  simp only [ReferenceInitializationControlRemainder.stoppedObservationFactor,
    ReferenceInitializationControlRemainder.stoppedObservation,
    ite_eq_left hcu, ite_eq_left hcv] at hobs
  have hp := Option.some.inj hobs
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- Both reconstructed sources have the actual elapsed start `s`, including
the zero-prefix case `s=t`. -/
theorem retained_physicalStart (x : X) (u : TimeControl p) :
    ReferenceCompletePhysicalHistory.physicalStart rate (src u x.1) rewards C_star C_h = s :=
  (retained_source_facts rate rewards C_star C_h q t s hs control0 x u).2

/-- The initialization part of literal physical reward is produced equally. -/
theorem retained_boundaryReward_eq (x : X) (u v : TimeControl p) :
    ReferenceInitializationPhysicalRewards.boundaryReward p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate (src u x.1) rewards C_star C_h) =
      ReferenceInitializationPhysicalRewards.boundaryReward p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate (src v x.1) rewards C_star C_h) :=
  congrArg (ReferenceInitializationPhysicalRewards.boundaryReward p)
    (retained_initialization_eq rate rewards C_star C_h q t s hs control0 x u v).1

/-- Actual selected index on every reconstruction, with the original J. -/
theorem retained_selected (x : X) (u : TimeControl p) :
    ActualInitializationPhysicalStep.selectedRowIndex p (src u x.1) = q := by
  rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
    p q t u x.1 x.2.1

private theorem run_projections_congr
    {a b : ReferenceActivePhysicalStep.State p rate} (hab : a = b)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (ha : ReferenceActivePhysicalHorizon.allActiveAtStart a start)
    (hb : ReferenceActivePhysicalHorizon.allActiveAtStart b start) :
    (ReferenceActivePhysicalHorizon.run a rows selected rewards start count hspan ha).finalState =
      (ReferenceActivePhysicalHorizon.run b rows selected rewards start count hspan hb).finalState ∧
    (ReferenceActivePhysicalHorizon.run a rows selected rewards start count hspan ha).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run b rows selected rewards start count hspan hb).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  subst b
  exact ⟨rfl, rfl⟩

/-- The existing generated prefix gives a common corrected launch and the
same actual state and chronological evidence before the resampled round. -/
theorem retained_launch_prefix (x : X) (u v : TimeControl p) :
    ∃ active : ReferenceActivePhysicalStep.State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate (src u x.1)
        rewards C_star C_h = some active ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate (src v x.1)
        rewards C_star C_h = some active ∧
      ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s,
        (ReferenceActivePhysicalHorizon.run active (src u x.1).1.2 q rewards s
          (t.val - s) (by omega) hmode).finalState =
        (ReferenceActivePhysicalHorizon.run active (src v x.1).1.2 q rewards s
          (t.val - s) (by omega) hmode).finalState ∧
        (ReferenceActivePhysicalHorizon.run active (src u x.1).1.2 q rewards s
          (t.val - s) (by omega) hmode).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        (ReferenceActivePhysicalHorizon.run active (src v x.1).1.2 q rewards s
          (t.val - s) (by omega) hmode).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  let hu := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 u).mp x.2.2
  let hv := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 v).mp x.2.2
  obtain ⟨active, _, hlu, hlv, hm, _, hstate, hev⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h q t x.1 x.2.1 control0 s (t.val - s) hs
      (by omega) x.2.2 u v
  have hsu : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t u x.1 x.2.1 s hs hu = active :=
    Option.some.inj ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t u x.1 x.2.1 s hs hu).1.symm.trans hlu)
  have hsv : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t v x.1 x.2.1 s hs hv = active :=
    Option.some.inj ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t v x.1 x.2.1 s hs hv).1.symm.trans hlv)
  have hqu := retained_selected rate rewards C_star C_h q t s hs control0 x u
  have hqv := retained_selected rate rewards C_star C_h q t s hs control0 x v
  have hpu := run_projections_congr rate rewards hsu (src u x.1).1.2 q s (t.val - s)
    (by omega) (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t u x.1 x.2.1 s hs hu).2.1 hm
  have hpv := run_projections_congr rate rewards hsv (src v x.1).1.2 q s (t.val - s)
    (by omega) (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t v x.1 x.2.1 s hs hv).2.1 hm
  refine ⟨active, hlu, hlv, hm, hpu.1.symm.trans (Eq.trans ?_ hpv.1),
    hpu.2.symm.trans (Eq.trans ?_ hpv.2)⟩
  · simpa only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor, hqu, hqv]
      using hstate
  · simpa only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor, hqu, hqv]
      using hev

private theorem retained_currentInput (x : X) (u : TimeControl p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate (src u x.1)
      rewards C_star C_h = some active)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s) :
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput rate rewards C_star C_h
      q t s hs control0 x u =
    ReferenceActivePhysicalHorizon.roundInputAt active (src u x.1).1.2 q rewards s hmode
      (ReferenceActivePhysicalHorizon.run active (src u x.1).1.2 q rewards s
        (t.val - s) (by omega) hmode) ⟨s + (t.val - s), by constructor <;> omega⟩ := by
  let hu := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 u).mp x.2.2
  have hseed : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
      q t u x.1 x.2.1 s hs hu = active :=
    Option.some.inj ((ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards
      C_star C_h q t u x.1 x.2.1 s hs hu).1.symm.trans hlaunch)
  subst active
  unfold ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
  dsimp only
  rw [retained_selected rate rewards C_star C_h q t s hs control0 x u]
  congr 1
  apply Subtype.ext
  change t.val = s + (t.val - s)
  omega

private theorem foldCalendar_eq_of_temporal_reads
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (origin start count : ℕ)
    (horigin : origin ≤ start) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial origin)
    (left right : ReferenceActivePhysicalHorizon.Run initial)
    (hacc : left.finalState = right.finalState ∧
      left.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        right.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hprops : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards origin start count
      horigin hspan hmode left).finalState =
    (ReferenceActivePhysicalHorizon.foldCalendar initial otherRows selected rewards origin start count
      horigin hspan hmode right).finalState ∧
    (ReferenceActivePhysicalHorizon.foldCalendar initial rows selected rewards origin start count
      horigin hspan hmode left).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
    (ReferenceActivePhysicalHorizon.foldCalendar initial otherRows selected rewards origin start count
      horigin hspan hmode right).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  unfold ReferenceActivePhysicalHorizon.foldCalendar
  refine List.foldl_rel
    (r := fun a b : ReferenceActivePhysicalHorizon.Run initial =>
      a.finalState = b.finalState ∧
      a.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        b.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) hacc ?_
  intro entry hentry a b hab
  have hmem : entry.val ∈
      (ReferenceActivePhysicalHorizon.calendarEntries origin start count horigin hspan).unattach :=
    List.mem_map.mpr ⟨entry, hentry, rfl⟩
  rw [ReferenceActivePhysicalHorizon.calendarEntries_time_values] at hmem
  obtain ⟨offset, hoffset, heq⟩ := List.mem_range'.mp hmem
  have hb : start ≤ entry.val ∧ entry.val < start + count := by
    constructor <;> omega
  let time : Fin p.T := ⟨entry.val, entry.property.2⟩
  let input := ReferenceActivePhysicalHorizon.roundInputAt initial rows selected rewards
    origin hmode a entry
  let other := ReferenceActivePhysicalHorizon.roundInputAt initial otherRows selected rewards
    origin hmode b entry
  have hpast : ∀ j : Fin p.T, j.val < time.val →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop := by
    intro j hj
    by_cases hstart : j.val < start
    · exact hprops j hstart
    · exact congrArg (fun c : TimeControl p => c.1 ContinuousControlSlice.Label.prop)
        (hcontrols j (by omega) (by dsimp [time] at hj; omega))
  have hlocal := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    input.state rows otherRows selected input.time input.active rewards rewards
    (hcontrols time hb.1 hb.2) hpast rfl
  have hcarry := ReferenceActivePhysicalHorizon.computedEvidence_congr
    ⟨input.state, otherRows, selected, input.time, input.active, rewards⟩ other
    hab.1 rfl rfl rfl rfl
  have he : ReferenceActivePhysicalHorizon.computedEvidence input =
      ReferenceActivePhysicalHorizon.computedEvidence other := hlocal.trans hcarry
  constructor
  · exact congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after he
  · change (a.records ++ [ReferenceActivePhysicalHorizon.RoundRecord.mk input
        (ReferenceActivePhysicalStep.step input) rfl]).map _ =
      (b.records ++ [ReferenceActivePhysicalHorizon.RoundRecord.mk other
        (ReferenceActivePhysicalStep.step other) rfl]).map _
    simp only [List.map_append, List.map_singleton]
    exact congrArg₂ (fun x y : List (ReferenceActivePhysicalHorizon.RoundEvidence
      (p := p) (rate := rate)) => x ++ y) hab.2 (congrArg (fun e => [e]) he)

private theorem reconstructed_otherTime (x : X) (u v : TimeControl p)
    (j : Fin p.T) (hj : j ≠ t) :
    ((src u x.1).1.2 q).2 j = ((src v x.1).1.2 q).2 j := by
  exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
    p q t u x.1 ⟨j, hj⟩).trans
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_otherTime
      p q t v x.1 ⟨j, hj⟩).symm

private theorem reward_sum_eq_of_evidence
    (left right : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (he : left.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      right.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) :
    (left.map ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
      (right.map ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum := by
  let reward := fun e : ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate) =>
    ∑ player : Fin p.m, ReferenceActivePhysicalHorizon.observationValue (e.ownEntries player).2
  have h := congrArg (fun es => (es.map reward).sum) he
  change (left.map (fun r => ∑ player : Fin p.m,
      ReferenceActivePhysicalHorizon.observationValue (r.ownEntries player).2)).sum =
    (right.map (fun r => ∑ player : Fin p.m,
      ReferenceActivePhysicalHorizon.observationValue (r.ownEntries player).2)).sum
  simpa only [List.map_map, Function.comp_def, reward, ReferenceActivePhysicalHorizon.RoundRecord.evidence,
    ReferenceActivePhysicalHorizon.RoundRecord.totalReward] using h

/-- The complete existing execution agrees under the retained lifted law.
The current-round certificate is used on this very law, before pushforward.
All later rounds, including a zero-length terminal suffix, are retained. -/
theorem ae_retained_complete :
    ∀ᵐ z ∂ReferenceRetainedSourceCoupling.retainedCoupling rate rewards C_star C_h
        q t s hs control0,
      let pair := ReferenceRetainedSourceCoupling.retainedSourcePairMap rate rewards C_star C_h
        q t s hs control0 z
      ReferenceCompletePhysicalHistory.completeTerminalState rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeTerminalState rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalRewards.completeReward rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalRewards.completeReward rate pair.2 rewards C_star C_h := by
  filter_upwards [ReferenceRetainedSourceCoupling.ae_retained_generated_effects
      rate rewards C_star C_h q t s hs control0,
    ReferenceRetainedSourceCoupling.ae_retained_frames rate rewards C_star C_h q t s hs control0]
    with z he hf
  obtain ⟨active, hlu, hlv, hm, hpreState, hpreEvidence⟩ :=
    retained_launch_prefix rate rewards C_star C_h q t s hs control0 z.1 z.2.1 z.2.2
  let left := src z.2.1 z.1.1
  let right := src z.2.2 z.1.1
  have hqu := retained_selected rate rewards C_star C_h q t s hs control0 z.1 z.2.1
  have hqv := retained_selected rate rewards C_star C_h q t s hs control0 z.1 z.2.2
  have hsu := retained_physicalStart rate rewards C_star C_h q t s hs control0 z.1 z.2.1
  have hsv := retained_physicalStart rate rewards C_star C_h q t s hs control0 z.1 z.2.2
  let preU := ReferenceActivePhysicalHorizon.run active left.1.2 q rewards s (t.val - s)
    (by omega) hm
  let preV := ReferenceActivePhysicalHorizon.run active right.1.2 q rewards s (t.val - s)
    (by omega) hm
  let entry : ReferenceActivePhysicalHorizon.CalendarEntry p s :=
    ⟨s + (t.val - s), by constructor <;> omega⟩
  let inputU := ReferenceActivePhysicalHorizon.roundInputAt active left.1.2 q rewards s hm preU entry
  let inputV := ReferenceActivePhysicalHorizon.roundInputAt active right.1.2 q rewards s hm preV entry
  have hinputU := retained_currentInput rate rewards C_star C_h q t s hs control0
    z.1 z.2.1 active hlu hm
  have hinputV := retained_currentInput rate rewards C_star C_h q t s hs control0
    z.1 z.2.2 active hlv hm
  have hstep : ReferenceActivePhysicalHorizon.computedEvidence inputU =
      ReferenceActivePhysicalHorizon.computedEvidence inputV :=
    (congrArg ReferenceActivePhysicalHorizon.computedEvidence hinputU).symm.trans
      (he.1.trans (congrArg ReferenceActivePhysicalHorizon.computedEvidence hinputV))
  let cut := (t.val - s) + 1
  have hcut : s + cut = t.val + 1 := by dsimp [cut]; omega
  have hcutSpan : s + cut ≤ p.T := by rw [hcut]; exact t.isLt
  let accU := ReferenceActivePhysicalHorizon.run active left.1.2 q rewards s cut hcutSpan hm
  let accV := ReferenceActivePhysicalHorizon.run active right.1.2 q rewards s cut hcutSpan hm
  have hacc : accU.finalState = accV.finalState ∧
      accU.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        accV.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    dsimp only [accU, accV, cut]
    rw [ReferenceActivePhysicalHorizon.run_successor_step,
      ReferenceActivePhysicalHorizon.run_successor_step]
    constructor
    · exact congrArg ReferenceActivePhysicalHorizon.RoundEvidence.after hstep
    · change (preU.records ++ [ReferenceActivePhysicalHorizon.RoundRecord.mk inputU
          (ReferenceActivePhysicalStep.step inputU) rfl]).map _ =
        (preV.records ++ [ReferenceActivePhysicalHorizon.RoundRecord.mk inputV
          (ReferenceActivePhysicalStep.step inputV) rfl]).map _
      simp only [List.map_append, List.map_singleton]
      exact congrArg₂ (fun a b : List (ReferenceActivePhysicalHorizon.RoundEvidence
        (p := p) (rate := rate)) => a ++ b) hpreEvidence
        (congrArg (fun e => [e]) hstep)
  have hprop : z.2.1.1 ContinuousControlSlice.Label.prop =
      z.2.2.1 ContinuousControlSlice.Label.prop := by
    exact hf.2.2.2.2.2.2.2.2.2.1
      ⟨ContinuousControlSlice.Label.prop, by rintro ⟨r, h⟩; cases h⟩
  have hprops : ∀ j : Fin p.T, j.val < s + cut →
      ((left.1.2 q).2 j).1 ContinuousControlSlice.Label.prop =
        ((right.1.2 q).2 j).1 ContinuousControlSlice.Label.prop := by
    intro j _hj
    by_cases htime : j = t
    · subst j
      change ((((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (z.2.1, z.1.1)).1.2 q).2 t).1 ContinuousControlSlice.Label.prop =
        ((((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (z.2.2, z.1.1)).1.2 q).2 t).1 ContinuousControlSlice.Label.prop
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control,
        ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control]
      exact hprop
    · exact congrArg (fun c : TimeControl p => c.1 ContinuousControlSlice.Label.prop)
        (reconstructed_otherTime rate rewards C_star C_h q t s hs control0 z.1 z.2.1 z.2.2 j htime)
  have htail := foldCalendar_eq_of_temporal_reads rate rewards active left.1.2 right.1.2 q
    s (s + cut) (p.T - (s + cut)) (by omega) (by omega) hm accU accV hacc
    (fun j hj _ => reconstructed_otherTime rate rewards C_star C_h q t s hs control0
      z.1 z.2.1 z.2.2 j (by intro h; subst j; omega)) hprops
  have hlength : p.T - s = cut + (p.T - (s + cut)) := by omega
  have hrun :
      (ReferenceActivePhysicalHorizon.run active left.1.2 q rewards s (p.T - s)
        (by omega) hm).finalState =
      (ReferenceActivePhysicalHorizon.run active right.1.2 q rewards s (p.T - s)
        (by omega) hm).finalState ∧
      (ReferenceActivePhysicalHorizon.run active left.1.2 q rewards s (p.T - s)
        (by omega) hm).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run active right.1.2 q rewards s (p.T - s)
        (by omega) hm).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
    have htail' := htail
    rw [← ReferenceActivePhysicalHorizon.run_append active left.1.2 q rewards s cut
        (p.T - (s + cut)) (by omega) hm,
      ← ReferenceActivePhysicalHorizon.run_append active right.1.2 q rewards s cut
        (p.T - (s + cut)) (by omega) hm] at htail'
    simpa only [← hlength] using htail'
  have hterminalU := ReferenceCompletePhysicalHistory.completeTerminalState_on_launch
    rate left rewards C_star C_h active hlu
  have hterminalV := ReferenceCompletePhysicalHistory.completeTerminalState_on_launch
    rate right rewards C_star C_h active hlv
  have hevidenceU := ReferenceCompletePhysicalHistory.completeSuffixEvidence_on_launch
    rate left rewards C_star C_h active hlu
  have hevidenceV := ReferenceCompletePhysicalHistory.completeSuffixEvidence_on_launch
    rate right rewards C_star C_h active hlv
  have hterminal : ReferenceCompletePhysicalHistory.completeTerminalState rate left rewards C_star C_h =
      ReferenceCompletePhysicalHistory.completeTerminalState rate right rewards C_star C_h := by
    rw [hterminalU, hterminalV]
    simpa only [left, right, hqu, hqv, hsu, hsv] using congrArg some hrun.1
  have hevidence : ReferenceCompletePhysicalHistory.completeSuffixEvidence rate left rewards C_star C_h =
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate right rewards C_star C_h := by
    rw [hevidenceU, hevidenceV]
    simpa only [left, right, hqu, hqv, hsu, hsv] using hrun.2
  refine ⟨hterminal, hevidence, ?_⟩
  change ReferenceCompletePhysicalRewards.completeReward rate left rewards C_star C_h =
    ReferenceCompletePhysicalRewards.completeReward rate right rewards C_star C_h
  have hboundary := retained_boundaryReward_eq rate rewards C_star C_h q t s hs control0
    z.1 z.2.1 z.2.2
  change ReferenceInitializationPhysicalRewards.boundaryReward p
    (ReferenceCompletePhysicalHistory.generatedBoundary rate left rewards C_star C_h) =
    ReferenceInitializationPhysicalRewards.boundaryReward p
    (ReferenceCompletePhysicalHistory.generatedBoundary rate right rewards C_star C_h) at hboundary
  rw [ReferenceCompletePhysicalRewards.completeReward_calendar_split,
    ReferenceCompletePhysicalRewards.completeReward_calendar_split,
    hboundary]
  exact congrArg (fun r => ReferenceInitializationPhysicalRewards.boundaryReward p
    (ReferenceCompletePhysicalHistory.generatedBoundary rate right rewards C_star C_h) + r)
    (reward_sum_eq_of_evidence rate _ _ hevidence)

/-- The actual state after the resampled round is active at the successor
boundary. Activation preservation supplies the proof even at the horizon. -/
theorem retained_activeAtSuccessor (x : X) (u : TimeControl p) :
    ∃ active : ReferenceActivePhysicalStep.State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate (src u x.1)
        rewards C_star C_h = some active ∧
      ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s,
        ReferenceActivePhysicalHorizon.allActiveAtStart
          (ReferenceActivePhysicalHorizon.run active (src u x.1).1.2 q rewards s
            ((t.val - s) + 1) (by omega) hmode).finalState (t.val + 1) := by
  obtain ⟨active, hl, _, hm, _, _⟩ :=
    retained_launch_prefix rate rewards C_star C_h q t s hs control0 x u u
  refine ⟨active, hl, hm, ?_⟩
  have h := ReferenceActivePhysicalHorizon.run_allActiveAtEnd active (src u x.1).1.2
    q rewards s ((t.val - s) + 1) (by omega) hm
  have he : s + ((t.val - s) + 1) = t.val + 1 := by omega
  simpa only [he] using h

/-- Reconstruction is a Borel embedding, not merely a measurable map.
Its exact range is the Borel set of equal original remainders in the retained
stratum. The inverse reads the two original controls and that same remainder;
it supplies no default source or operational state. -/
theorem measurableEmbedding_retainedSourcePairMap :
    MeasurableEmbedding (ReferenceRetainedSourceCoupling.retainedSourcePairMap
      rate rewards C_star C_h q t s hs control0) := by
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let cell := ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
    rate rewards C_star C_h q t s control0
  let f := ReferenceRetainedSourceCoupling.retainedSourcePairMap
    rate rewards C_star C_h q t s hs control0
  have hrange : Set.range f = {pair : SourceInput p × SourceInput p |
      (e pair.1).2 ∈ cell ∧ (e pair.1).2 = (e pair.2).2} := by
    ext pair
    constructor
    · rintro ⟨z, rfl⟩
      have hsplit := ReferenceRetainedSourceCoupling.retainedSourcePairMap_split
        rate rewards C_star C_h q t s hs control0 z
      exact ⟨by rw [hsplit.1]; exact z.1.2,
        (congrArg Prod.snd hsplit.1).trans (congrArg Prod.snd hsplit.2).symm⟩
    · rintro ⟨hm, he⟩
      refine ⟨(⟨(e pair.1).2, hm⟩, ((e pair.1).1, (e pair.2).1)), ?_⟩
      apply Prod.ext
      · exact e.symm_apply_apply pair.1
      · change e.symm ((e pair.2).1, (e pair.1).2) = pair.2
        rw [he]
        exact e.symm_apply_apply pair.2
  have hcell : MeasurableSet cell :=
    ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
      rate rewards C_star C_h q t s hs control0
  have hrangeMeasurable : MeasurableSet (Set.range f) := by
    rw [hrange, Set.ofPred_and]
    exact (hcell.preimage (measurable_snd.comp (e.measurable.comp measurable_fst))).inter
      (measurableSet_eq_fun
        (measurable_snd.comp (e.measurable.comp measurable_fst))
        (measurable_snd.comp (e.measurable.comp measurable_snd)))
  let inverse : Set.range f → X × ReferenceRetainedSourceCoupling.ControlPair p := fun pair =>
    (⟨(e pair.1.1).2, by
      exact ((Set.ext_iff.mp hrange pair.val).mp pair.property).1⟩, ((e pair.1.1).1, (e pair.1.2).1))
  have hinverse : Measurable inverse := by
    have hleft : Measurable (fun pair : Set.range f => e pair.val.1) :=
      e.measurable.comp (measurable_fst.comp measurable_subtype_coe)
    have hright : Measurable (fun pair : Set.range f => e pair.val.2) :=
      e.measurable.comp (measurable_snd.comp measurable_subtype_coe)
    exact ((measurable_snd.comp hleft).subtype_mk).prodMk
      ((measurable_fst.comp hleft).prodMk (measurable_fst.comp hright))
  apply MeasurableEmbedding.of_measurable_inverse_on_range
    (ReferenceRetainedSourceCoupling.measurable_retainedSourcePairMap
      rate rewards C_star C_h q t s hs control0) hrangeMeasurable hinverse
  intro z
  have hsplit := ReferenceRetainedSourceCoupling.retainedSourcePairMap_split
    rate rewards C_star C_h q t s hs control0 z
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.snd hsplit.1
  · change ((e (f z).1).1, (e (f z).2).1) = z.2
    have hfst : (e (f z).1).1 = z.2.1 := congrArg Prod.fst hsplit.1
    have hsnd : (e (f z).2).1 = z.2.2 := congrArg Prod.fst hsplit.2
    exact Prod.ext hfst hsnd

/-- The complete physical certificate on the actual original-source stratum.
The proved Borel embedding transports null sets for arbitrary predicates, so
no measurable-equality premise on the canonical execution state is required. -/
theorem ae_sourceStratum_complete (i : ReferenceTotalSourcePairCoupling.StratumIndex t) :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.sourceStratumPairLaw rate rewards C_star C_h
        t control0 i,
      ReferenceCompletePhysicalHistory.completeTerminalState rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeTerminalState rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalRewards.completeReward rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalRewards.completeReward rate pair.2 rewards C_star C_h := by
  rw [ReferenceTotalSourcePairCoupling.sourceStratumPairLaw,
    ReferenceRetainedSourceCoupling.retainedSourcePairLaw]
  apply (measurableEmbedding_retainedSourcePairMap rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0).ae_map_iff.mpr
  exact ae_retained_complete rate rewards C_star C_h i.1 t i.2.val
    (Nat.lt_succ_iff.mp i.2.isLt) control0

/-- Supporting launch and initialization identities on each original-source
active stratum, obtained from generated retained observations and seeds. -/
theorem ae_sourceStratum_launch_boundary
    (i : ReferenceTotalSourcePairCoupling.StratumIndex t) :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.sourceStratumPairLaw rate rewards C_star C_h
        t control0 i,
      ReferenceCompletePhysicalHistory.generatedBoundary rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.generatedBoundary rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.physicalStart rate pair.1 rewards C_star C_h = i.2.val ∧
      ReferenceCompletePhysicalHistory.physicalStart rate pair.2 rewards C_star C_h = i.2.val ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate pair.1 rewards C_star C_h =
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate pair.2 rewards C_star C_h := by
  rw [ReferenceTotalSourcePairCoupling.sourceStratumPairLaw,
    ReferenceRetainedSourceCoupling.retainedSourcePairLaw,
    (measurableEmbedding_retainedSourcePairMap rate rewards C_star C_h i.1 t i.2.val
      (Nat.lt_succ_iff.mp i.2.isLt) control0).ae_map_iff]
  apply Filter.Eventually.of_forall
  intro z
  obtain ⟨active, hlu, hlv, _, _, _⟩ := retained_launch_prefix rate rewards C_star C_h
    i.1 t i.2.val (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.1 z.2.2
  exact ⟨(retained_initialization_eq rate rewards C_star C_h i.1 t i.2.val
      (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.1 z.2.2).1,
    retained_physicalStart rate rewards C_star C_h i.1 t i.2.val
      (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.1,
    retained_physicalStart rate rewards C_star C_h i.1 t i.2.val
      (Nat.lt_succ_iff.mp i.2.isLt) control0 z.1 z.2.2,
    hlu.trans hlv.symm⟩

private theorem measurableEmbedding_sourceDiagonalMap :
    MeasurableEmbedding (ReferenceTotalSourcePairCoupling.sourceDiagonalMap (p := p)) := by
  apply MeasurableEmbedding.of_measurable_inverse
    ReferenceTotalSourcePairCoupling.measurable_sourceDiagonalMap
  · have hrange : Set.range (ReferenceTotalSourcePairCoupling.sourceDiagonalMap (p := p)) =
        Set.diagonal (SourceInput p) := by
      ext pair
      change (∃ z, (z, z) = pair) ↔ pair.1 = pair.2
      constructor
      · rintro ⟨z, rfl⟩
        rfl
      · intro h
        exact ⟨pair.1, Prod.ext rfl h⟩
    rw [hrange]
    exact measurableSet_diagonal
  · exact measurable_fst
  · exact fun _ => rfl

/-- One fixed-time total original-source resampling preserves the complete
corrected physical terminal state, chronological suffix evidence, and literal
received reward. No crossing, success, matched trace, or no-overflow premise
is imposed on either original source. -/
theorem ae_totalSourcePairLaw_complete :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
        t control0,
      ReferenceCompletePhysicalHistory.completeTerminalState rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeTerminalState rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalRewards.completeReward rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalRewards.completeReward rate pair.2 rewards C_star C_h := by
  rw [ReferenceTotalSourcePairCoupling.totalSourcePairLaw, ae_add_measure_iff]
  constructor
  · rw [ae_finsetSum_measure_iff]
    intro i _hi
    exact ae_sourceStratum_complete rate rewards C_star C_h t control0 i
  · rw [ReferenceTotalSourcePairCoupling.complementDiagonalSourcePairLaw,
      measurableEmbedding_sourceDiagonalMap.ae_map_iff]
    exact Filter.Eventually.of_forall fun _ => ⟨rfl, rfl, rfl⟩

/-- At the natural terminal boundary there is no current control: the
separate source law is diagonal and preserves the same complete outputs. -/
theorem ae_terminalSourcePairLaw_complete :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.terminalSourcePairLaw p,
      ReferenceCompletePhysicalHistory.completeTerminalState rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeTerminalState rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.2 rewards C_star C_h ∧
      ReferenceCompletePhysicalRewards.completeReward rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalRewards.completeReward rate pair.2 rewards C_star C_h := by
  rw [ReferenceTotalSourcePairCoupling.terminalSourcePairLaw,
    measurableEmbedding_sourceDiagonalMap.ae_map_iff]
  exact Filter.Eventually.of_forall fun _ => ⟨rfl, rfl, rfl⟩

/-- The literal reward equality predicate is Borel on the actual source
product, using the admitted complete-execution reward measurability. -/
theorem measurableSet_completeReward_eq :
    MeasurableSet {pair : SourceInput p × SourceInput p |
      ReferenceCompletePhysicalRewards.completeReward rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalRewards.completeReward rate pair.2 rewards C_star C_h} :=
  measurableSet_eq_fun
    ((ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h).comp measurable_fst)
    ((ReferenceCompleteRewardMeasurability.measurable_completeReward_source
      rate rewards C_star C_h).comp measurable_snd)

/-- Terminal-state projection of the joint complete physical certificate. -/
theorem ae_totalSourcePairLaw_completeTerminalState :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
        t control0,
      ReferenceCompletePhysicalHistory.completeTerminalState rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeTerminalState rate pair.2 rewards C_star C_h := by
  filter_upwards [ae_totalSourcePairLaw_complete rate rewards C_star C_h t control0] with pair h
  exact h.1

/-- Full chronological evidence projection, including actual feedback and
all coordinator and follower diagnostics. -/
theorem ae_totalSourcePairLaw_completeSuffixEvidence :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
        t control0,
      ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalHistory.completeSuffixEvidence rate pair.2 rewards C_star C_h := by
  filter_upwards [ae_totalSourcePairLaw_complete rate rewards C_star C_h t control0] with pair h
  exact h.2.1

/-- Literal received reward over all physical rounds and players. -/
theorem ae_totalSourcePairLaw_completeReward :
    ∀ᵐ pair ∂ReferenceTotalSourcePairCoupling.totalSourcePairLaw rate rewards C_star C_h
        t control0,
      ReferenceCompletePhysicalRewards.completeReward rate pair.1 rewards C_star C_h =
        ReferenceCompletePhysicalRewards.completeReward rate pair.2 rewards C_star C_h := by
  filter_upwards [ae_totalSourcePairLaw_complete rate rewards C_star C_h t control0] with pair h
  exact h.2.2

end Bandits.Support.ReferenceTotalSourcePhysicalCongruence

end
