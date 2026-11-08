/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompletePhysicalHistory
public import Bandits.Support.ReferenceInitializationPhysicalRewards

/-!
# Complete physical rewards of the original-source reference execution

Sources: `sources/zip4/manuscript/01_introduction.tex:20-36`,
`sources/zip4/manuscript/07_public_setup.tex:93-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-48,67-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

The definitions below project actions and observations from the existing full
reference history on the original source, selected complete row, whole reward
table, shared constants, and admitted rate.  Their physical reward laws and
calendar decomposition are deterministic identities for that computed
execution.  No probability, expectation, measurability, regret, coupling, or
source theorem is asserted here.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceInitializationPhysicalRewards
open Bandits.Support.FiniteBanditModel
open Bandits.Support.RealRewardGridCount

namespace Bandits.Support.ReferenceCompletePhysicalRewards

abbrev Parameters := ReferenceCompletePhysicalHistory.Parameters
abbrev RateInput := ReferenceCompletePhysicalHistory.RateInput

variable {p : Parameters}

/-- The literal simultaneous action profile stored in the complete computed
reference history at this physical round. -/
def completeActions (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (time : Fin p.T) : Fin p.m → Fin p.K :=
  fun player =>
    (ReferenceCompletePhysicalHistory.completeOwnHistory
      rate source rewards C_star C_h player time).1

/-- A player's literal stored scalar feedback in the complete computed
reference history. -/
def completeFeedback (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (player : Fin p.m) (time : Fin p.T) : ℝ :=
  (((ReferenceCompletePhysicalHistory.completeOwnHistory
    rate source rewards C_star C_h player time).2).val).val

/-- The total own-observation reward computed on one complete physical round.
-/
def completeRoundReward (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (time : Fin p.T) : ℝ :=
  ∑ player : Fin p.m, completeFeedback rate source rewards C_star C_h player time

/-- The total observed reward over every one of the `T` physical rounds of the
complete computed reference execution. -/
def completeReward (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : ℝ :=
  ∑ time : Fin p.T, completeRoundReward rate source rewards C_star C_h time

private theorem completeSuffixRecords_eq_run (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    (ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h
      (by rw [hlaunch]; simp)).records =
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h
          omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate source rewards C_star C_h active hlaunch)).records := by
  let hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by
    rw [hlaunch]
    simp
  have hleft : ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h =
      (ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h
        hnone).records := by
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
  have hright := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
    rate source rewards C_star C_h active hlaunch
  exact hleft.symm.trans hright

private theorem completeOwnHistory_suffix_run (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (player : Fin p.m)
    (offset : Fin (p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h)) :
    ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h player
      ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset.val,
        by
          have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
            rate source rewards C_star C_h
          omega⟩ =
    ((ReferenceActivePhysicalHorizon.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega)
      (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch)).records.get
        ⟨offset.val, by
          rw [ReferenceActivePhysicalHorizon.run_record_count active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
            (by
              have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                rate source rewards C_star C_h
              omega)
            (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
              rate source rewards C_star C_h active hlaunch)]
          exact offset.isLt⟩).ownEntries player := by
  let hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by
    rw [hlaunch]
    simp
  let execution := ReferenceActivePhysicalHorizon.run active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate source rewards C_star C_h
      omega)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate source rewards C_star C_h active hlaunch)
  have hhistory := ReferenceCompletePhysicalHistory.completeOwnHistory_suffix
    rate source rewards C_star C_h player active hlaunch offset
  have hrecords := completeSuffixRecords_eq_run rate source rewards C_star C_h active hlaunch
  have hcorrectedIndex : offset.val <
      (ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h hnone).records.length := by
    rw [ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count
      rate source rewards C_star C_h hnone]
    exact offset.isLt
  have hexecutionIndex : offset.val < execution.records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega)
      (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch)]
    exact offset.isLt
  have hget? := congrArg
    (fun records : List (ReferenceCompletePhysicalHistory.RoundRecord p rate) => records[offset.val]?) hrecords
  rw [List.getElem?_eq_getElem hcorrectedIndex,
    List.getElem?_eq_getElem hexecutionIndex] at hget?
  have hget :
      (ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h hnone).records[offset.val]'hcorrectedIndex =
        execution.records[offset.val]'hexecutionIndex := Option.some.inj hget?
  have hhistory' :
      ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h player
        ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset.val,
          by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h
            omega⟩ =
        ((ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h hnone).records[offset.val]'hcorrectedIndex).ownEntries player := by
    simpa only [List.get_eq_getElem] using hhistory
  rw [hget] at hhistory'
  simpa [execution] using hhistory'

/-- Every player's complete-history feedback equals the collision-filtered
real grid reward for the very same complete simultaneous action profile and
the original whole reward table.  Collision-free play is not assumed.
Sources: `01_introduction.tex:22-26` and `07_public_setup.tex:123-140`.
-/
theorem completeFeedback_collisionFiltered (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ∀ (time : Fin p.T) (player : Fin p.m),
      completeFeedback rate source rewards C_star C_h player time =
        if FiniteBanditModel.collisionFreeFor (completeActions rate source rewards C_star C_h time) player then
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards time (completeActions rate source rewards C_star C_h time player))
        else 0 := by
  intro time player
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  by_cases hprefix : time.val < start
  · let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    let u : Fin (ReferenceInitializationRun.elapsed p b.completed) :=
      ⟨time.val, by
        simpa [start, ReferenceCompletePhysicalHistory.physicalStart,
          ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput, b, x] using hprefix⟩
    have hown (j : Fin p.m) :
        ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h j time =
          b.history j u := by
      have h := ReferenceCompletePhysicalHistory.completeOwnHistory_prefix
        rate source rewards C_star C_h j time (by simpa [start] using hprefix)
      simpa [u, b, x, ReferenceCompletePhysicalHistory.generatedBoundary,
        ReferenceCompletePhysicalHistory.generatedInput,
        ActualReferenceInitializationBlock.referenceInput] using h
    have hprofile : completeActions rate source rewards C_star C_h time =
        fun j => (b.history j u).1 := by
      funext j
      change (ReferenceCompletePhysicalHistory.completeOwnHistory
        rate source rewards C_star C_h j time).1 = (b.history j u).1
      exact congrArg Prod.fst (hown j)
    have hindex :
        (⟨u.val, Nat.lt_of_lt_of_le u.isLt
          (ReferenceInitializationRun.elapsed_le_T p b.completed)⟩ : Fin p.T) = time := by
      apply Fin.ext
      rfl
    have hphysics := ReferenceInitializationPhysicalRewards.source_reference_output_physicalFeedback
      source rewards C_star C_h rate u player
    have hphysics' : (b.history player u).2.val.val =
        if FiniteBanditModel.collisionFreeFor (fun j => (b.history j u).1) player then
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            ((ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate).rewards
              (⟨u.val, Nat.lt_of_lt_of_le u.isLt
                (ReferenceInitializationRun.elapsed_le_T p b.completed)⟩ : Fin p.T)
              ((b.history player u).1))
        else 0 := by
      simpa [x, b, ActualReferenceInitializationBlock.referenceInput] using hphysics
    rw [hindex] at hphysics'
    rw [← hprofile] at hphysics'
    have hplayer :
        completeActions rate source rewards C_star C_h time player =
          (b.history player u).1 := congrFun hprofile player
    rw [← hplayer] at hphysics'
    change (b.history player u).2.val.val =
      if FiniteBanditModel.collisionFreeFor
          (completeActions rate source rewards C_star C_h time) player then
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards time (completeActions rate source rewards C_star C_h time player))
      else 0 at hphysics'
    have hleft : completeFeedback rate source rewards C_star C_h player time =
        (b.history player u).2.val.val := by
      change ((ReferenceCompletePhysicalHistory.completeOwnHistory
        rate source rewards C_star C_h player time).2).val.val = _
      rw [hown player]
    exact hleft.trans hphysics'
  · have hnotNone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h ≠ none := by
      intro hnone
      have hstart := ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate source rewards C_star C_h hnone
      have htime := time.isLt
      omega
    cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h with
    | none => exact False.elim (hnotNone hlaunch)
    | some active =>
      let offset : Fin (p.T - start) := ⟨time.val - start, by
        have htime := time.isLt
        omega⟩
      let hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      let mode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let execution := ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
        (p.T - start) hspan mode
      have hrecords := completeSuffixRecords_eq_run rate source rewards C_star C_h active hlaunch
      have hidx : offset.val < execution.records.length := by
        rw [ReferenceActivePhysicalHorizon.run_record_count active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
          (p.T - start) hspan mode]
        exact offset.isLt
      have htimes : execution.records.map (fun record => record.input.time.val) =
          ReferenceActivePhysicalHorizon.calendar start (p.T - start) := by
        have h := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
          rate source rewards C_star C_h
        rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
          rate source rewards C_star C_h active hlaunch] at h
        simpa [execution, start, hspan, mode] using h
      have hcalIdx : offset.val <
          (ReferenceActivePhysicalHorizon.calendar start (p.T - start)).length := by
        rw [← htimes, List.length_map]
        exact hidx
      have htimeOption := congrArg
        (fun times : List ℕ => times[offset.val]?) htimes
      rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hidx),
        List.getElem?_eq_getElem hcalIdx] at htimeOption
      have hcalendar :
          (ReferenceActivePhysicalHorizon.calendar start (p.T - start))[offset.val] =
            start + offset.val := by
        simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range', Nat.one_mul]
      have htimeVal :
          (execution.records[offset.val]'hidx).input.time.val = start + offset.val :=
        Option.some.inj (by
          simpa only [List.getElem_map, hcalendar] using htimeOption)
      have htimeCoord : start + offset.val = time.val := by
        dsimp [offset]
        omega
      have hrecordTime : (execution.records[offset.val]'hidx).input.time = time := by
        apply Fin.ext
        exact htimeVal.trans htimeCoord
      have hfields := ReferenceActivePhysicalHorizon.run_record_inputs
        active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start (p.T - start) hspan mode
        (execution.records[offset.val]'hidx) (List.getElem_mem hidx)
      have hrecordRewards : (execution.records[offset.val]'hidx).input.rewards = rewards := by
        simpa [execution] using hfields.2.2
      have hentry (j : Fin p.m) :
          ReferenceCompletePhysicalHistory.completeOwnHistory rate source rewards C_star C_h j time =
            ((execution.records[offset.val]'hidx).ownEntries j) := by
        have h := completeOwnHistory_suffix_run rate source rewards C_star C_h
          active hlaunch j offset
        have hcoordinate :
            (⟨start + offset.val,
              by have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                    rate source rewards C_star C_h; omega⟩ : Fin p.T) = time := by
          apply Fin.ext
          exact htimeCoord
        rw [hcoordinate] at h
        simpa [execution] using h
      have hprofile : completeActions rate source rewards C_star C_h time =
          (execution.records[offset.val]'hidx).actions := by
        funext j
        change (ReferenceCompletePhysicalHistory.completeOwnHistory
          rate source rewards C_star C_h j time).1 = _
        rw [hentry j, ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula]
      have hrecordFeedback : completeFeedback rate source rewards C_star C_h player time =
          if FiniteBanditModel.collisionFreeFor
              (execution.records[offset.val]'hidx).actions player then
            RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
              ((execution.records[offset.val]'hidx).input.rewards
                (execution.records[offset.val]'hidx).input.time
                ((execution.records[offset.val]'hidx).actions player))
          else 0 := by
        change ((ReferenceCompletePhysicalHistory.completeOwnHistory
          rate source rewards C_star C_h player time).2).val.val = _
        rw [hentry player, ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula]
        by_cases hcollision : FiniteBanditModel.collisionFreeFor
            (execution.records[offset.val]'hidx).actions player
        · simp [hcollision, ActualInitializationPhysicalStep.observationOfGrid_value,
            RealRewardGridCount.realRewardGridValue]
        · simp [hcollision, ActualInitializationPhysicalStep.observationOfGrid_value]
      rw [← hprofile, hrecordTime, hrecordRewards] at hrecordFeedback
      simpa [completeFeedback, completeActions] using hrecordFeedback

/-- The per-round total observed reward is between zero and one per player.
-/
theorem completeRoundReward_bounds (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (time : Fin p.T) :
    completeRoundReward rate source rewards C_star C_h time ∈
      Set.Icc (0 : ℝ) (p.m : ℝ) := by
  constructor
  · unfold completeRoundReward
    apply Finset.sum_nonneg
    intro player _
    exact ((ReferenceCompletePhysicalHistory.completeOwnHistory
      rate source rewards C_star C_h player time).2).val.property.1
  · unfold completeRoundReward
    calc
      (∑ player : Fin p.m,
          completeFeedback rate source rewards C_star C_h player time) ≤
        ∑ _player : Fin p.m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro player _
          exact ((ReferenceCompletePhysicalHistory.completeOwnHistory
            rate source rewards C_star C_h player time).2).val.property.2
      _ = (p.m : ℝ) := by simp

/-- The total observed reward on all `T` rounds lies in `[0,mT]` on every
computed execution, including every failure and terminal branch. -/
theorem completeReward_bounds (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    completeReward rate source rewards C_star C_h ∈
      Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
  constructor
  · unfold completeReward
    apply Finset.sum_nonneg
    intro time _
    exact (completeRoundReward_bounds rate source rewards C_star C_h time).1
  · unfold completeReward
    calc
      (∑ time : Fin p.T, completeRoundReward rate source rewards C_star C_h time) ≤
        ∑ _time : Fin p.T, (p.m : ℝ) := by
          apply Finset.sum_le_sum
          intro time _
          exact (completeRoundReward_bounds rate source rewards C_star C_h time).2
      _ = (p.T : ℝ) * (p.m : ℝ) := by simp
      _ = (p.m : ℝ) * (p.T : ℝ) := mul_comm _ _

/-- The action projection depends on the selected complete row alone once the
original IDs and entire private tuple agree.  The original private `J` is
retained and its equality is consumed by the existing full-history theorem.
-/
theorem completeActions_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) (time : Fin p.T) :
    completeActions rate source rewards C_star C_h time =
      completeActions rate source' rewards C_star C_h time := by
  funext player
  exact congrArg Prod.fst
    (congrArg (fun history => history time)
      (ReferenceCompletePhysicalHistory.completeOwnHistory_eq_of_source_data
        rate source source' rewards C_star C_h q hids hprivate hq hrow player))

/-- Own scalar feedback has selected-row dependence under equality of the
original IDs, entire original private tuple, and selected complete row. -/
theorem completeFeedback_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) (player : Fin p.m) :
    completeFeedback rate source rewards C_star C_h player =
      completeFeedback rate source' rewards C_star C_h player := by
  funext time
  exact congrArg (fun entry : Fin p.K × ReferencePrelaunchFollower.Observation p =>
      entry.2.val.val)
    (congrArg (fun history => history time)
      (ReferenceCompletePhysicalHistory.completeOwnHistory_eq_of_source_data
        rate source source' rewards C_star C_h q hids hprivate hq hrow player))

/-- Per-round received reward has selected-row dependence under the same
original-source equality conditions. -/
theorem completeRoundReward_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) (time : Fin p.T) :
    completeRoundReward rate source rewards C_star C_h time =
      completeRoundReward rate source' rewards C_star C_h time := by
  unfold completeRoundReward
  apply Finset.sum_congr rfl
  intro player _
  have hhistory := ReferenceCompletePhysicalHistory.completeOwnHistory_eq_of_source_data
    rate source source' rewards C_star C_h q hids hprivate hq hrow player
  exact congrArg (fun entry : Fin p.K × ReferencePrelaunchFollower.Observation p =>
      entry.2.val.val) (congrArg (fun history => history time) hhistory)

/-- Total received reward over all rounds has selected-row dependence under
equality of IDs, the entire original private tuple, and the selected row. -/
theorem completeReward_eq_of_source_data (rate : RateInput p)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p))
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (hrow : source.1.2 q = source'.1.2 q) :
    completeReward rate source rewards C_star C_h =
      completeReward rate source' rewards C_star C_h := by
  unfold completeReward
  apply Finset.sum_congr rfl
  intro time _
  exact completeRoundReward_eq_of_source_data rate source source' rewards C_star C_h
    q hids hprivate hq hrow time

private theorem completeRoundReward_prefix_eq_boundaryEntry (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (time : Fin p.T)
    (htime : time.val < ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h) :
    completeRoundReward rate source rewards C_star C_h time =
      ∑ player : Fin p.m,
        ((ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).history
          player ⟨time.val, by simpa [ReferenceCompletePhysicalHistory.physicalStart] using htime⟩).2.val.val := by
  unfold completeRoundReward
  apply Finset.sum_congr rfl
  intro player _
  change ((ReferenceCompletePhysicalHistory.completeOwnHistory
      rate source rewards C_star C_h player time).2).val.val = _
  rw [ReferenceCompletePhysicalHistory.completeOwnHistory_prefix
    rate source rewards C_star C_h player time htime]

private theorem listMapSum_eq_finSum {α : Type*} (records : List α) (f : α → ℝ) :
    (records.map f).sum = ∑ i : Fin records.length, f (records.get i) := by
  induction records with
  | nil => simp
  | cons record rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.get_cons_succ', ih]

/-- On a present launch, the complete per-round reward at suffix offset `k`
is exactly the total reward of the corresponding record in the existing
corrected suffix run. -/
theorem completeRoundReward_eq_suffixRecord_totalReward (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (offset : Fin (p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h)) :
    completeRoundReward rate source rewards C_star C_h
        ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset.val,
          by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h
            omega⟩ =
      ReferenceActivePhysicalHorizon.RoundRecord.totalReward
        ((ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h
          (by rw [hlaunch]; simp)).records.get
        ⟨offset.val, by
          rw [ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count
            rate source rewards C_star C_h (by rw [hlaunch]; simp)]
          exact offset.isLt⟩) := by
  unfold completeRoundReward
  rw [ReferenceActivePhysicalHorizon.RoundRecord.totalReward]
  apply Finset.sum_congr rfl
  intro player _
  change ((ReferenceCompletePhysicalHistory.completeOwnHistory
      rate source rewards C_star C_h player
        ⟨ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + offset.val,
          by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h
            omega⟩).2).val.val = _
  rw [ReferenceCompletePhysicalHistory.completeOwnHistory_suffix
    rate source rewards C_star C_h player active hlaunch offset]
  rfl

/-- The complete suffix reward is the total reward of the literal corrected
suffix run, and also the `totalReward` of the existing active-horizon run on
the same `some` launch. -/
theorem completeSuffixReward_eq_run_totalReward (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
      ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
        (ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h
          (by rw [hlaunch]; simp)).totalReward ∧
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
        ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum =
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          (by
            have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate source rewards C_star C_h
            omega)
          (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
            rate source rewards C_star C_h active hlaunch)).totalReward := by
  let hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h ≠ none := by
    rw [hlaunch]
    simp
  constructor
  · have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h =
          (ReferenceCompletePhysicalHistory.correctedSuffixRun rate source rewards C_star C_h
            hnone).records := by
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
    rw [hrecords]
    rfl
  · rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate source rewards C_star C_h active hlaunch]
    rfl

/-- Exact split of the complete physical reward at the generated
initialization boundary: the prefix reward plus every record of the actual
calendar suffix. -/
theorem completeReward_calendar_split (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    completeReward rate source rewards C_star C_h =
      ReferenceInitializationPhysicalRewards.boundaryReward p
          (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) +
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
          ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let count := p.T - start
  have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  have hlength : p.T = start + count := by
    dsimp [count]
    omega
  let f : Fin p.T → ℝ := fun time =>
    completeRoundReward rate source rewards C_star C_h time
  let g : Fin (start + count) → ℝ := fun time => f (Fin.cast hlength.symm time)
  have hsumReindex : (∑ time : Fin p.T, f time) =
      ∑ time : Fin (start + count), g time :=
    Fintype.sum_equiv (finCongr hlength) f g (by intro time; rfl)
  have hprefix :
      (∑ time : Fin start, g (Fin.castAdd count time)) =
        ReferenceInitializationPhysicalRewards.boundaryReward p
          (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) := by
    unfold ReferenceInitializationPhysicalRewards.boundaryReward
    apply Finset.sum_congr rfl
    intro time _
    let rootTime := Fin.cast hlength.symm (Fin.castAdd count time)
    have hval : rootTime.val = time.val := by simp [rootTime]
    have hbefore : rootTime.val < start := by omega
    have hbeforePhysical : rootTime.val <
        ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
      simpa [start] using hbefore
    have hindex :
        (⟨rootTime.val, by
          simpa [ReferenceCompletePhysicalHistory.physicalStart] using hbeforePhysical⟩ :
            Fin (ReferenceInitializationRun.elapsed p
              (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h).completed)) =
          time := by
      apply Fin.ext
      exact hval
    change completeRoundReward rate source rewards C_star C_h rootTime = _
    rw [completeRoundReward_prefix_eq_boundaryEntry
      rate source rewards C_star C_h rootTime hbeforePhysical]
    rw [hindex]
  have hsuffix :
      (∑ offset : Fin count, g (Fin.natAdd start offset)) =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
          ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum := by
    by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = none
    · have hcomplete := ReferenceCompletePhysicalHistory.no_launch_complete_history
        rate source rewards C_star C_h hnone
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone,
        start, count, hcomplete.1]
    · cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate source rewards C_star C_h with
      | none => exact False.elim (hnone hlaunch)
      | some active =>
        let hrunNone : ReferenceCorrectedInitializationLaunch.correctedLaunch
            rate source rewards C_star C_h ≠ none := by
          rw [hlaunch]
          simp
        let records := (ReferenceCompletePhysicalHistory.correctedSuffixRun
          rate source rewards C_star C_h hrunNone).records
        have hrecordsLength : records.length = count := by
          dsimp [records, count, start]
          exact ReferenceCompletePhysicalHistory.correctedSuffixRun_record_count
            rate source rewards C_star C_h hrunNone
        have hlist := listMapSum_eq_finSum records
          ReferenceActivePhysicalHorizon.RoundRecord.totalReward
        have hreindex :
            (∑ i : Fin records.length,
              ReferenceActivePhysicalHorizon.RoundRecord.totalReward (records.get i)) =
              ∑ offset : Fin count,
                ReferenceActivePhysicalHorizon.RoundRecord.totalReward
                  (records.get (Fin.cast hrecordsLength.symm offset)) :=
          Fintype.sum_equiv (finCongr hrecordsLength)
            (fun i => ReferenceActivePhysicalHorizon.RoundRecord.totalReward (records.get i))
            (fun offset => ReferenceActivePhysicalHorizon.RoundRecord.totalReward
              (records.get (Fin.cast hrecordsLength.symm offset))) (by intro i; rfl)
        have hrounds :
            (∑ offset : Fin count, g (Fin.natAdd start offset)) =
              ∑ offset : Fin count,
                ReferenceActivePhysicalHorizon.RoundRecord.totalReward
                  (records.get (Fin.cast hrecordsLength.symm offset)) := by
          apply Finset.sum_congr rfl
          intro offset _
          have htime :
              Fin.cast hlength.symm (Fin.natAdd start offset) =
                ⟨start + offset.val, by
                  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
                    rate source rewards C_star C_h
                  omega⟩ := by
            apply Fin.ext
            simp only [Fin.val_cast, Fin.val_natAdd]
          change completeRoundReward rate source rewards C_star C_h
              (Fin.cast hlength.symm (Fin.natAdd start offset)) = _
          rw [htime]
          have hterm := completeRoundReward_eq_suffixRecord_totalReward
            rate source rewards C_star C_h active hlaunch offset
          simpa [records, hrunNone, hrecordsLength] using hterm
        have hrecords :
            ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h =
              records := by
          simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hrunNone, records]
        calc
          (∑ offset : Fin count, g (Fin.natAdd start offset)) =
              ∑ offset : Fin count,
                ReferenceActivePhysicalHorizon.RoundRecord.totalReward
                  (records.get (Fin.cast hrecordsLength.symm offset)) := hrounds
          _ = (records.map ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum :=
            (hlist.trans hreindex).symm
          _ = (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h |>.map
              ReferenceActivePhysicalHorizon.RoundRecord.totalReward).sum := by rw [← hrecords]
  unfold completeReward
  change (∑ time : Fin p.T, f time) = _
  rw [hsumReindex, Fin.sum_univ_add, hprefix, hsuffix]

/-- If the actual corrected launch option is absent, all `T` observed rounds
are the generated initialization prefix. This retains the no-launch option as
distinct from a terminal crossing. -/
theorem completeReward_eq_prefix_of_no_launch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = none) :
    completeReward rate source rewards C_star C_h =
      ReferenceInitializationPhysicalRewards.boundaryReward p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) := by
  rw [completeReward_calendar_split rate source rewards C_star C_h]
  have hcomplete := ReferenceCompletePhysicalHistory.no_launch_complete_history
    rate source rewards C_star C_h hlaunch
  rw [hcomplete.2.1]
  simp

/-- At a launch crossing exactly at `T`, the launch remains `some active` but
the physical suffix is empty, so total reward is again the full generated
prefix. The terminal state and launch option are preserved. -/
theorem completeReward_eq_prefix_of_terminal_crossing (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (active : ReferenceCompletePhysicalHistory.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hterminal : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = p.T) :
    completeReward rate source rewards C_star C_h =
      ReferenceInitializationPhysicalRewards.boundaryReward p
        (ReferenceCompletePhysicalHistory.generatedBoundary rate source rewards C_star C_h) := by
  rw [completeReward_calendar_split rate source rewards C_star C_h]
  have hcomplete := ReferenceCompletePhysicalHistory.terminal_crossing_complete_history
    rate source rewards C_star C_h active hlaunch hterminal
  rw [hcomplete.1]
  simp

end Bandits.Support.ReferenceCompletePhysicalRewards

end
