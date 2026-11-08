/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix

import Lean.Elab.Tactic.Omega

/-!
# The first-renewal queue readout at the next prior boundary

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-290`,
`sources/zip4/manuscript/06_interruptions.tex:9-70,246-295,355-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

The proof observer keeps the original renewal source and changes only the
selected control suffix after the current date. Its complete stopped readout
is determined by the whole accepted numerical prefix, including inherited
queues, overflow, and every accepted history.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextPriorReadout

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Source {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalSourceCurrentPrefix.Source
    rate rewards C_star C_h u t

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : TimeControl p)

local notation "Z" => Source rate rewards C_star C_h u t

/-- The same renewal source with the complete selected control suffix after
the current date replaced by `control0`. Membership is supplied by the
existing first-renewal suffix-locality constructor. -/
def nextPriorObserver (z : Z) : Z :=
  ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
    rate rewards C_star C_h u t z (fun v =>
      if v = t then
        (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 t
      else control0)

/-- The observer's source coordinate is exactly the existing prefix map;
the subtype proof comes from `renewalSourceWithSuffix`. -/
theorem nextPriorObserver_val (z : Z) :
    (nextPriorObserver rate rewards C_star C_h u t control0 z).val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z.val := by
  change ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
      z.val t
        (fun v => if v = t then
          (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 t
        else control0) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z.val
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext row
      by_cases hrow : row = ActualInitializationPhysicalStep.selectedRowIndex p z.val
      · subst row
        simp only [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix, Function.update_self]
        apply Prod.ext
        · rfl
        · funext v
          change (if v.val < t.val then
              (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 v
            else if v = t then
              (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 t
            else control0) =
            (if v.val < t.val + 1 then
              (z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)).2 v
            else control0)
          by_cases hbefore : v.val < t.val
          · have hbeforeNext : v.val < t.val + 1 := by omega
            simp [hbefore, hbeforeNext]
          · by_cases heq : v = t
            · subst v
              simp
            · have hprefix : ¬ v.val < t.val + 1 := by omega
              simp [hbefore, heq, hprefix]
      · simp [ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix,
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix, hrow]
  · rfl

private theorem nextPriorObserver_prefix_idempotent (z : Z) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1)
        (nextPriorObserver rate rewards C_star C_h u t control0 z).val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z.val := by
  rw [nextPriorObserver_val]
  exact ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 (t.val + 1) (t.val + 1) le_rfl z.val

private theorem nextPriorObserver_prefixObservation_eq (z : Z) :
    ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z) =
      ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t
          (nextPriorObserver rate rewards C_star C_h u t control0 z)) := by
  have hn : t.val + 1 ≤ p.T := by omega
  calc
    _ = ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
            (t.val + 1) z.val)) :=
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservationPrefix_factor
        rate rewards C_star C_h u t control0 (t.val + 1) hn z
    _ = ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
        (ReferenceCompleteNumericalBranchObservation.completeBranchObservation
          rate rewards C_star C_h
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
            (t.val + 1)
            (nextPriorObserver rate rewards C_star C_h u t control0 z))) := by
      rw [nextPriorObserver_prefix_idempotent rate rewards C_star C_h u t control0 z]
    _ = ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t
          (nextPriorObserver rate rewards C_star C_h u t control0 z)) :=
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservationPrefix_factor
        rate rewards C_star C_h u t control0 (t.val + 1) hn
        (nextPriorObserver rate rewards C_star C_h u t control0 z)).symm

private theorem encodeNumerical_some_injective :
    Function.Injective (fun cell : RecordedQueueRun.RoundInput p.K =>
      some (ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) := by
  intro a b hab
  cases a with
  | mk aEnabled aArm aReward aRate _ _ _ =>
    cases b with
    | mk bEnabled bArm bReward bRate _ _ _ =>
      have h := Option.some.inj hab
      change (aEnabled, (aArm, (aReward, aRate))) =
        (bEnabled, (bArm, (bReward, bRate))) at h
      rcases Prod.mk.inj h with ⟨hEnabled, hRest⟩
      rcases Prod.mk.inj hRest with ⟨hArm, hRest⟩
      rcases Prod.mk.inj hRest with ⟨hReward, hRate⟩
      subst bEnabled
      subst bArm
      subst bReward
      subst bRate
      rfl

private theorem nextPriorObserver_appendedCells_eq (z : Z) :
    ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z ++
        [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t z] =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t
        (nextPriorObserver rate rewards C_star C_h u t control0 z) ++
        [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t
          (nextPriorObserver rate rewards C_star C_h u t control0 z)] := by
  have hobs := nextPriorObserver_prefixObservation_eq
    rate rewards C_star C_h u t control0 z
  have hlive := congrArg
    (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate) hobs
  have hcollection := congrArg
    (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate) hobs
  have hjoin :
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z ++
        [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t z]).map
          (fun cell => some (ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) =
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t
        (nextPriorObserver rate rewards C_star C_h u t control0 z) ++
        [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t
          (nextPriorObserver rate rewards C_star C_h u t control0 z)]).map
          (fun cell => some (ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) := by
    calc
      _ = List.zipWith (fun a b => a.2.or b.2)
          (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
            (ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
              (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
                rate rewards C_star C_h u t z)))
          (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
            (ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
              (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
                rate rewards C_star C_h u t z))) :=
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.appendedCells_rawPrefix_join
          rate rewards C_star C_h u t z).symm
      _ = List.zipWith (fun a b => a.2.or b.2)
          (ReferenceCompleteFirstPhaseObservationRecovery.rawLiveNumericalDecoder rate
            (ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
              (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
                rate rewards C_star C_h u t
                (nextPriorObserver rate rewards C_star C_h u t control0 z))))
          (ReferenceCompleteFirstPhaseObservationRecovery.rawCollectionNumericalDecoder rate
            (ReferenceCompleteObservationPrefixInformation.datePrefix rate (t.val + 1)
              (ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
                rate rewards C_star C_h u t
                (nextPriorObserver rate rewards C_star C_h u t control0 z)))) := by
        rw [hlive, hcollection]
      _ = _ :=
        ReferenceFirstCollectionRenewalSourceCurrentPrefix.appendedCells_rawPrefix_join
          rate rewards C_star C_h u t
          (nextPriorObserver rate rewards C_star C_h u t control0 z)
  exact (List.map_injective_iff.mpr encodeNumerical_some_injective) hjoin

/-- The complete stopped output is unchanged by replacing the selected
control suffix after the current renewal date with the fixed control. -/
theorem wholePostReadout_nextPrefix_factor (z : Z) :
    ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t
        (nextPriorObserver rate rewards C_star C_h u t control0 z) := by
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_fullPrefix
      rate rewards C_star C_h u t z,
    ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_fullPrefix
      rate rewards C_star C_h u t
      (nextPriorObserver rate rewards C_star C_h u t control0 z)]
  exact congrArg
    (fun cells => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) cells))
    (nextPriorObserver_appendedCells_eq rate rewards C_star C_h u t control0 z)

/-- The complete stopped readout is measurable in the existing source-prefix
field at offset `t.val + 2`, including at the terminal date. -/
theorem measurable_wholePostReadout_nextPrior :
    Measurable[MeasurableSpace.comap (fun z : Z => z.val)
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
        (t.val + 2))]
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t) := by
  let observer : Z → Z := nextPriorObserver rate rewards C_star C_h u t control0
  have hfield :
      MeasurableSpace.comap (fun z : Z => z.val)
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
            (t.val + 2)) =
        MeasurableSpace.comap
          (fun z : Z => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
            (t.val + 1) z.val)
          (inferInstance : MeasurableSpace
            (ReferenceSourcePrefixHistoryFiltration.SourceInput p)) := by
    rw [show t.val + 2 = (t.val + 1) + 1 by omega,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
      MeasurableSpace.comap_comp]
    rfl
  have hprefix : Measurable[
      MeasurableSpace.comap (fun z : Z => z.val)
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (t.val + 2))]
      (fun z : Z => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
        (t.val + 1) z.val) := by
    rw [hfield]
    exact comap_measurable _
  have hobserver_val : Measurable[
      MeasurableSpace.comap (fun z : Z => z.val)
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (t.val + 2))]
      (fun z : Z => (observer z).val) := by
    have hfun : (fun z : Z => (observer z).val) =
        (fun z : Z => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0
          (t.val + 1) z.val) := by
      funext z
      exact nextPriorObserver_val rate rewards C_star C_h u t control0 z
    rw [hfun]
    exact hprefix
  have hobserver : Measurable[
      MeasurableSpace.comap (fun z : Z => z.val)
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
          (t.val + 2))] observer :=
    hobserver_val.subtype_mk
  have hfactor :
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t =
        fun z => ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t (observer z) := by
    funext z
    exact wholePostReadout_nextPrefix_factor rate rewards C_star C_h u t control0 z
  rw [hfactor]
  exact (ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholePostReadout
    rate rewards C_star C_h u t).comp hobserver

end Bandits.Support.ReferenceFirstCollectionRenewalNextPriorReadout

end
