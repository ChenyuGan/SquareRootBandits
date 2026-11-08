/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceSavedMoments
public import Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw

/-!
# Actual strict-prefix branch and parameter invariance

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:142-156,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-408`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`.

These internal deterministic results use the original source, including all
private coordinates and the whole reward table. The analysis field is the
literal strict-prefix field; no identification with manuscript histories or
conditional moment assertion is made here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceContinuingRecordingPhysicalReward
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionPhaseHistory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveSourcePrefixBranchInvariance

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
variable (i : Fin (p.m - 1))

local notation "X" => ReferenceFirstLiveRecordingReadoutMeasurability.SourceX rate rewards C_star C_h q t s hs control0
local notation "Xi" => ReferenceFirstLiveRecordingReadoutMeasurability.XFollower rate rewards C_star C_h q t s hs control0 i
local notation "Zi" => Bandits.Support.ReferenceFirstLiveSourceSavedMoments.SourceFollower rate rewards C_star C_h q t s hs control0 i
local notation "μZi" => Bandits.Support.ReferenceFirstLiveSourceSavedMoments.followerSourceMeasure rate rewards C_star C_h q t s hs control0 i

local notation "ret" => ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
  rate rewards C_star C_h q t s hs control0

/-- The original launch stratum after replacing the selected control suffix
starting at the focal round by the fixed baseline. -/
def prefixZ (z : Z) : Z := by
  refine ⟨Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val, ?_⟩
  have hz := z.property
  change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val = q ∧
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s at hz
  rcases hz with ⟨hq, hcross, helapsed⟩
  refine ⟨?_, ?_⟩
  · rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hq
  · exact (Bandits.Support.ReferenceSourcePrefixHistoryFiltration.actualLaunchStratum_factor rate rewards C_star C_h control0 t.val
      (Nat.le_of_lt t.isLt) s hs z.val).mp ⟨hcross, helapsed⟩

@[simp] theorem prefixZ_val (z : Z) : (prefixZ rate rewards C_star C_h q t s hs control0 z).val =
    Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val := rfl

/-- Prefixing twice at the same calendar boundary has no further effect. -/
theorem prefixZ_idempotent (z : Z) :
    prefixZ rate rewards C_star C_h q t s hs control0
      (prefixZ rate rewards C_star C_h q t s hs control0 z) =
        prefixZ rate rewards C_star C_h q t s hs control0 z := by
  apply Subtype.ext
  exact Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 t.val t.val le_rfl z.val

local notation "pre" => prefixZ rate rewards C_star C_h q t s hs control0
local notation "inp" => ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
  rate rewards C_star C_h q t s hs control0
local notation "gen" => ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
  rate rewards C_star C_h q t s hs control0

private def liveCutoffTag
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) : Bool :=
  match out with
  | .cutoffChosen .. => true
  | _ => false

private theorem liveCutoffTag_eq_projection
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) :
    liveCutoffTag (rate := rate) r owned base row out =
      (match (Bandits.Support.ReferenceActiveDispatchTemporal.liveOutcomeData
        r owned base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (input : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    cutoffChosen input =
      liveCutoffTag (rate := rate) (liveRegistersAt r input.time)
        (liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base)) := by
  dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

/-- Actual earlier PREPARE cutoff tags are compared through their dispatcher
projections. The retained row itself is not identified. -/
private theorem cutoffChosen_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : RewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows otherSelected).2 time) :
    cutoffChosen ⟨state, rows, selected, time, active, rewards⟩ =
      cutoffChosen ⟨state, otherRows, otherSelected, time, active, otherRewards⟩ := by
  classical
  cases hphase : state.coordinator with
  | first =>
      dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase, CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      have hdata := Bandits.Support.ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
        (ReferenceActivePhysicalStep.liveRegistersAt r time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned time) base
        (rows selected) (otherRows otherSelected) hcurrent
      have htag := congrArg (fun data =>
        match data.2.2 with
        | .inr (.inr (.inr _)) => true
        | _ => false) hdata
      rw [← liveCutoffTag_eq_projection, ← liveCutoffTag_eq_projection] at htag
      rw [cutoffChosen_live rate _ r owned base hphase,
        cutoffChosen_live rate _ r owned base hphase]
      simpa only [ReferenceActivePhysicalStep.liveInput, RoundInput.row,
        liveCutoffTag] using htag
  | collection payload ledger proposal =>
      dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [cutoffChosen, prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]

private abbrev LiveOutcomeData :=
  Fin p.K × Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
    (Unit ⊕ (Unit ⊕ (ReferenceActiveDispatchTemporal.LiveArgs p rate ⊕
      ReferenceActiveDispatchTemporal.CollectionArgs p rate)))

private def liveDataStart (data : LiveOutcomeData (p := p) (rate := rate)) :
    Option (CoordinatorPhaseClock.StartRoundResult p) :=
  match data.2.2 with
  | .inr (.inr (.inl args)) => some args.2.2.2
  | _ => none

private theorem liveDataStart_eq_of_current
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (row otherRow : CompletePublicTable.CompleteRow p)
    (hcurrent : row.2 r.time = otherRow.2 r.time) :
    liveDataStart rate (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base row
      (CoordinatorRoundDispatch.dispatchLive
        { eta := rate.eta, registers := r, ownedRegisters := owned,
          followerBaseScore := base, row := row })) =
    liveDataStart rate (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base otherRow
      (CoordinatorRoundDispatch.dispatchLive
        { eta := rate.eta, registers := r, ownedRegisters := owned,
          followerBaseScore := base, row := otherRow })) := by
  exact congrArg (liveDataStart rate)
    (ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
      r owned base row otherRow hcurrent)

private theorem cutoffChosen_eq_of_inputs
    (left right : RoundInput p rate)
    (hstate : left.state = right.state)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    cutoffChosen left = cutoffChosen right := by
  cases left with
  | mk ls lrows lselected ltime lact lrewards =>
    cases right with
    | mk rs rrows rselected rtime ractive rrewards =>
      dsimp only at hstate htime hcurrent
      subst rs
      subst rtime
      exact cutoffChosen_eq_of_current rate ls lrows rrows lselected rselected ltime
        lact lrewards rrewards hcurrent

/-- The physical strict-past run preserves the actual dispatch cutoff tags
when all selected current controls in its interval agree. -/
theorem run_cutoffTags_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (M p)) (rewards : RewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (run initial rows selected rewards start count hspan hmode).records.map
        (fun record => cutoffChosen record.input) =
      (run initial otherRows selected rewards start count hspan hmode).records.map
        (fun record => cutoffChosen record.input) := by
  induction count with
  | zero =>
      rw [ReferenceActivePhysicalHorizon.run_zero_records,
        ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      have hprefix : start + count ≤ p.T := by omega
      have hcontrolsPrefix : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
          (rows selected).2 j = (otherRows selected).2 j := by
        intro j hj hk
        exact hcontrols j hj (by omega)
      have htags := ih hprefix hcontrolsPrefix
      have hstate := (Bandits.Support.ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
        initial rows otherRows selected rewards rewards start count hprefix hmode
        hcontrolsPrefix (fun _ _ _ => rfl) (fun _ => hbefore)).1
      rw [ReferenceActivePhysicalHorizon.run_successor_step,
        ReferenceActivePhysicalHorizon.run_successor_step]
      simp only [ReferenceActivePhysicalHorizon.foldRound, List.map_append,
        List.map_singleton]
      rw [htags]
      congr 1
      apply congrArg List.singleton
      apply cutoffChosen_eq_of_inputs
      · exact hstate
      · rfl
      · exact hcontrols ⟨start + count, by omega⟩ (by dsimp; omega)
          (by dsimp; omega)

private theorem suffix_after_current_replacement (z : SourceInput p) :
    Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control0)
        t (fun _ => control0) =
      Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  rw [Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_suffix
    control0 t.val t.isLt z]
  dsimp only [Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix]
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z control0) =
      ActualInitializationPhysicalStep.selectedRowIndex p z := rfl
  rw [hselected]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p z
      · subst j
        simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
          Function.update_self]
        apply Prod.ext
        · rfl
        · funext v
          by_cases hv : v.val < t.val
          · have hvt : v ≠ t := by intro h; subst v; omega
            simp [hv, hvt]
          · simp [hv]
      · simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
          hj]
  · rfl

/-- Reconstructing the retained source changes only its original current control. -/
theorem splitSource_sourceRetained (z : Z) :
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 (ret z).val =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.val control0 := by
  have hselected : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val = q := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact z.property.1
  unfold ReferenceGeneratedActivePrefixFactor.splitSource
  have hret :
      (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z).val =
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.val).2 := by
    change (ReferenceTotalSourceDisintegration.sourceRetainedInput rate rewards C_star C_h
      t control0 (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z).val = _
    exact ReferenceTotalSourceDisintegration.sourceRetainedInput_val rate rewards C_star C_h
      t control0 (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z
  change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
    (control0, (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
      rate rewards C_star C_h q t s hs control0 z).val) = _
  rw [hret]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t z.val control0 hselected

private theorem splitSource_sourcePrefix (z : Z) :
    let x := ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
      rate rewards C_star C_h q t s hs control0 z
    Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val)
        t (fun _ => control0) =
      Bandits.Support.ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val := by
  dsimp only
  rw [splitSource_sourceRetained]
  exact suffix_after_current_replacement t control0 z.val

theorem sourceRetained_prefix_val (z : Z) :
    (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
      rate rewards C_star C_h q t s hs control0
      (prefixZ rate rewards C_star C_h q t s hs control0 z)).val =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
        (Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix
          (ReferenceGeneratedActivePrefixFactor.splitSource q t control0
            (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
              rate rewards C_star C_h q t s hs control0 z).val)
          t (fun _ => control0))).2 := by
  unfold ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
  rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val rate rewards C_star C_h t control0
    (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
    (prefixZ rate rewards C_star C_h q t s hs control0 z)]
  simp only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex]
  rw [prefixZ_val]
  have hsplit := splitSource_sourcePrefix rate rewards C_star C_h q t s hs control0 z
  exact congrArg (fun w => (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t w).2)
    hsplit.symm

private theorem retainedBranch_parts
    (x : Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.RetainedBranch
      rate rewards C_star C_h q t s hs control0) :
    x.val ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∧
      x.val ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0 := by
  have hx := x.property
  change x.val ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
    rate rewards C_star C_h q t s control0 at hx
  simpa [ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet,
    Set.mem_inter_iff] using hx

theorem source_prefix_retained (z : Z) :
    ∃ x' : Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.RetainedBranch
        rate rewards C_star C_h q t s hs control0,
      ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0
          (prefixZ rate rewards C_star C_h q t s hs control0 z) = x' ∧
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          control0
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hs control0 z).val
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hs control0 z).property.1 s hs
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hs control0 z).property.2 =
        ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          control0 x'.val x'.property.1 s hs x'.property.2 ∧
      ∀ k : Fin (t.val - s + 1),
        (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hs control0 z) control0
          k.val (by have hk := k.isLt; omega)).finalState =
        (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0 x' control0
          k.val (by have hk := k.isLt; omega)).finalState ∧
        (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0
          (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
            rate rewards C_star C_h q t s hs control0 z) control0
          k.val (by have hk := k.isLt; omega)).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence =
        (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
          rate rewards C_star C_h q t s hs control0 x' control0
          k.val (by have hk := k.isLt; omega)).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  let x := ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
    rate rewards C_star C_h q t s hs control0 z
  obtain ⟨x', hxval, hseed, hprefix⟩ :=
    Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance.retainedGeneratedPrefix_suffix_invariant
      (rate := rate) rewards C_star C_h q t s hs control0 x (fun _ => control0)
  have hval :
      (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0
        (prefixZ rate rewards C_star C_h q t s hs control0 z)).val = x'.val := by
    rw [sourceRetained_prefix_val]
    exact hxval.symm
  have hsub : ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0
        (prefixZ rate rewards C_star C_h q t s hs control0 z) = x' := by
    apply Subtype.ext
    exact hval
  refine ⟨x', hsub, ?_, ?_⟩
  · simpa only [x] using hseed
  · simpa only [x] using hprefix

private theorem generatedSeed_eq_launchState
    (x : Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.RetainedBranch
      rate rewards C_star C_h q t s hs control0) :
    ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
        control0 x.val x.property.1 s hs x.property.2 =
      ReferenceFirstLaunchNumericalCell.launchState rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val)
        rewards C_star C_h
        (Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
          rate rewards C_star C_h q t s hs control0 x).1 := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  have hparts := retainedBranch_parts
    rate rewards C_star C_h q t s hs control0 x
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val hparts.1 s hs hparts.2
  have hlaunch := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
    rate source rewards C_star C_h
    (Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
      rate rewards C_star C_h q t s hs control0 x).1
  apply Option.some.inj
  exact hspec.1.symm.trans hlaunch

private theorem run_records_eq_of_initial_eq
    (left right : ReferenceActivePhysicalStep.State p rate)
    (hstate : left = right)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (hleft : allActiveAtStart left start) (hright : allActiveAtStart right start) :
    (run left rows selected rewards start count hspan hleft).records =
      (run right rows selected rewards start count hspan hright).records := by
  cases hstate
  have hmode : hleft = hright := Subsingleton.elim _ _
  cases hmode
  rfl

theorem retainedGeneratedPrefix_cutoffTags_eq
    (x x' : Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.RetainedBranch
      rate rewards C_star C_h q t s hs control0)
    (hseed : ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
        q t control0 x.val x.property.1 s hs x.property.2 =
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
        q t control0 x'.val x'.property.1 s hs x'.property.2)
    (hcontrols : ∀ j : Fin p.T, s ≤ j.val → j.val < t.val →
      ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2 q).2 j =
        ((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x'.val).1.2 q).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < s →
      (((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2 q).2 j).1
          ContinuousControlSlice.Label.prop =
        (((ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x'.val).1.2 q).2 j).1
          ContinuousControlSlice.Label.prop) :
    (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
      rate rewards C_star C_h q t s hs control0 x control0 (t.val - s) (by omega)).records.map
        (fun record => cutoffChosen record.input) =
    (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
      rate rewards C_star C_h q t s hs control0 x' control0 (t.val - s) (by omega)).records.map
        (fun record => cutoffChosen record.input) := by
  let sourceL := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let sourceR := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x'.val
  have hpartsL := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x
  have hpartsR := retainedBranch_parts rate rewards C_star C_h q t s hs control0 x'
  have hselectedL : ActualInitializationPhysicalStep.selectedRowIndex p sourceL = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p sourceL =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p sourceL :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p sourceL).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.val hpartsL.1
  have hselectedR : ActualInitializationPhysicalStep.selectedRowIndex p sourceR = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p sourceR =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p sourceR :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p sourceR).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x'.val hpartsR.1
  have hspecL := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val hpartsL.1 s hs hpartsL.2
  have hspecR := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x'.val hpartsR.1 s hs hpartsR.2
  have hspan : s + (t.val - s) ≤ p.T := by omega
  have htags := run_cutoffTags_eq rate
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
      control0 x.val x.property.1 s hs x.property.2)
    sourceL.1.2 sourceR.1.2 q rewards s (t.val - s) hspan hspecL.2.1
    (by
      intro j hjS hjT
      exact hcontrols j hjS (by omega))
    (by
      intro j hjS
      exact hbefore j (by omega))
  have hrecordsR := run_records_eq_of_initial_eq rate
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
      control0 x'.val x'.property.1 s hs x'.property.2)
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
      control0 x.val x.property.1 s hs x.property.2)
    hseed.symm sourceR.1.2 q rewards s (t.val - s) hspan hspecR.2.1 hspecL.2.1
  unfold Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
  dsimp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
  rw [hselectedL, hselectedR]
  calc
    _ = (run (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          control0 x.val x.property.1 s hs x.property.2)
        sourceL.1.2 q rewards s (t.val - s) hspan hspecL.2.1).records.map
          (fun record => cutoffChosen record.input) := by
      simp only [sourceL]
    _ = (run (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          control0 x.val x.property.1 s hs x.property.2)
        sourceR.1.2 q rewards s (t.val - s) hspan hspecL.2.1).records.map
          (fun record => cutoffChosen record.input) := by
      exact htags
    _ = (run (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
          control0 x'.val x'.property.1 s hs x'.property.2)
        sourceR.1.2 q rewards s (t.val - s) hspan hspecR.2.1).records.map
          (fun record => cutoffChosen record.input) := by
      exact congrArg (fun records => records.map (fun record => cutoffChosen record.input)) hrecordsR.symm

theorem actualRetainedPrefixRun_take_prefix
    (x : Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.RetainedBranch
      rate rewards C_star C_h q t s hs control0) :
    (Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control0 x).records.take (t.val - s) =
    (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
      rate rewards C_star C_h q t s hs control0 x control0 (t.val - s)
      (by omega)).records := by
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
    (Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
      rate rewards C_star C_h q t s hs control0 x).1
  have hparts := retainedBranch_parts
    rate rewards C_star C_h q t s hs control0 x
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p source =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p source).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.val hparts.1
  have hmode : allActiveAtStart initial s := by
    rcases Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
        rate rewards C_star C_h q t s hs control0 x with ⟨_, helapsed⟩
    simpa [initial, helapsed] using
      (Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
        rate rewards C_star C_h q t s hs control0 x).activeAtStart
  have hfull :
      Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x =
      run initial source.1.2 q rewards s (t.val - s + 1) (by omega) hmode := by
    rcases Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
        rate rewards C_star C_h q t s hs control0 x with ⟨_, helapsed⟩
    simp [Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, source, initial,
      helapsed, hselected]
  have happend : ∃ record,
      (run initial source.1.2 q rewards s (t.val - s + 1) (by omega) hmode).records =
        (run initial source.1.2 q rewards s (t.val - s) (by omega) hmode).records ++ [record] := by
    refine ⟨RoundRecord.mk
      (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s hmode
        (run initial source.1.2 q rewards s (t.val - s) (by omega) hmode)
        ⟨s + (t.val - s), by omega, by omega⟩)
      (ReferenceActivePhysicalStep.step
        (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s hmode
          (run initial source.1.2 q rewards s (t.val - s) (by omega) hmode)
          ⟨s + (t.val - s), by omega, by omega⟩)) rfl, ?_⟩
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    exact (ReferenceActivePhysicalHorizon.foldRound_equations initial source.1.2 q rewards
      s hmode (run initial source.1.2 q rewards s (t.val - s) (by omega) hmode)
      ⟨s + (t.val - s), by omega, by omega⟩).2
  rcases happend with ⟨record, happend⟩
  have hseed := generatedSeed_eq_launchState rate rewards C_star C_h q t s hs control0 x
  have hgenMode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val hparts.1 s hs hparts.2).2.1
  have hpriorRecords :
      (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control0 (t.val - s) (by omega)).records =
      (run initial source.1.2 q rewards s (t.val - s) (by omega) hmode).records := by
    unfold Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
    dsimp only [ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor]
    simpa [source, hselected] using run_records_eq_of_initial_eq rate
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
        control0 x.val x.property.1 s hs x.property.2)
      initial hseed.symm (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val))
      rewards s (t.val - s) (by omega) hgenMode hmode
  have htakeRun :
      (Bandits.Support.ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x).records.take (t.val - s) =
      (run initial source.1.2 q rewards s (t.val - s + 1) (by omega) hmode).records.take
        (t.val - s) :=
    congrArg (fun u : ReferenceActivePhysicalHorizon.Run initial =>
      u.records.take (t.val - s)) hfull
  calc
    _ = (run initial source.1.2 q rewards s (t.val - s + 1) (by omega) hmode).records.take
        (t.val - s) := htakeRun
    _ = (run initial source.1.2 q rewards s (t.val - s) (by omega) hmode).records := by
      rw [happend]
      rw [List.take_append_of_le_length (by
        simp [ReferenceActivePhysicalHorizon.run_record_count])]
      simp [ReferenceActivePhysicalHorizon.run_record_count]
    _ = (Bandits.Support.ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
        rate rewards C_star C_h q t s hs control0 x control0 (t.val - s) (by omega)).records :=
      hpriorRecords.symm

/-- The prefixed remainder reconstructs the literal prefixed original source. -/
theorem splitSource_sourceRetained_prefix (z : Z) :
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 (ret (pre z)).val =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val := by
  rw [splitSource_sourceRetained, prefixZ_val]
  have hc : ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val).1.2
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val))).2 t =
        control0 := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control]
    exact ite_eq_right (Nat.lt_irrefl _)
  calc
    _ = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)
        (((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val).1.2
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val))).2 t) :=
      congrArg (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val)) hc.symm
    _ = _ := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original _ _ _

/-- Every actual retained endpoint and chronological evidence list through
the strict-past boundary agrees. The prefix index includes zero and `t.val-s`. -/
theorem source_prefix_states_evidence (z : Z) (k : Fin (t.val - s + 1)) :
    (gen (ret z) control0 k.val (by have hk := k.isLt; omega)).finalState =
        (gen (ret (pre z)) control0 k.val (by have hk := k.isLt; omega)).finalState ∧
      (gen (ret z) control0 k.val (by have hk := k.isLt; omega)).records.map RoundRecord.evidence =
        (gen (ret (pre z)) control0 k.val (by have hk := k.isLt; omega)).records.map RoundRecord.evidence := by
  obtain ⟨x', hx, _, hprior⟩ := source_prefix_retained rate rewards C_star C_h q t s hs control0 z
  rw [hx]
  exact hprior k

/-- Actual strict-past incoming states agree; no equality of retained rows is asserted. -/
theorem source_prefix_incoming (z : Z) : (inp (ret z)).state = (inp (ret (pre z))).state := by
  obtain ⟨x', hx, _, hprior⟩ := source_prefix_retained rate rewards C_star C_h q t s hs control0 z
  have hstate := (hprior ⟨t.val - s, by omega⟩).1
  rw [← hx] at hstate
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary,
    ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  exact hstate

/-- The actual baseline input reads precisely the fixed whole current control. -/
theorem actualCurrentInput_baseline (x : X) : (inp x).row.2 (inp x).time = control0 := by
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  rw [RoundInput.row, ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time,
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_rows,
    ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_selected_eq_q]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control p q t control0 x.val

private theorem actualCurrentInput_time (x : X) : (inp x).time = t := by
  rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
  rfl

/-- Every actual earlier cutoff tag agrees after strict-prefix projection. -/
theorem source_prefix_cutoffTags (z : Z) :
    ((ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control0 (ret z)).records.take (t.val - s)).map
        (fun record => cutoffChosen record.input) =
    ((ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control0 (ret (pre z))).records.take (t.val - s)).map
        (fun record => cutoffChosen record.input) := by
  rw [actualRetainedPrefixRun_take_prefix, actualRetainedPrefixRun_take_prefix]
  obtain ⟨x', hx, hseed, _⟩ := source_prefix_retained rate rewards C_star C_h q t s hs control0 z
  rw [← hx] at hseed
  apply retainedGeneratedPrefix_cutoffTags_eq rate rewards C_star C_h q t s hs control0
    (ret z) (ret (pre z)) hseed
  · intro j _ hj
    rw [splitSource_sourceRetained_prefix rate rewards C_star C_h q t s hs control0 z,
      ← splitSource_sourcePrefix rate rewards C_star C_h q t s hs control0 z]
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 (ret z).val) = q :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 (ret z).val (ret z).property.1
    simpa only [hselected] using
      (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 (ret z).val)
        t j (fun _ => control0) hj).symm
  · intro j hj
    have hjt : j.val < t.val := lt_of_lt_of_le hj hs
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 (ret z).val) = q :=
      ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 (ret z).val (ret z).property.1
    have hcontrol := ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_before
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 (ret z).val)
      t j (fun _ => control0) hjt
    rw [hselected, splitSource_sourcePrefix,
      ← splitSource_sourceRetained_prefix] at hcontrol
    exact congrArg (fun u : TimeControl p => u.1 ContinuousControlSlice.Label.prop) hcontrol.symm

/-- Literal continuing start-result projection of the actual PREPARE. -/
def preparedContinuingStart (input : RoundInput p rate) :
    Option (CoordinatorPhaseClock.StartRoundResult p) :=
  match (prepare input).coordinator with
  | .live _ _ _ (.continuingChosen dispatched _ _ _) => some dispatched.startResult
  | _ => none

private theorem preparedContinuingStart_live
    (input : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    preparedContinuingStart rate input = liveDataStart rate
      (ReferenceActiveDispatchTemporal.liveOutcomeData
        (liveRegistersAt r input.time) (liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base))) := by
  dsimp only [preparedContinuingStart, prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

/-- All dispatch exceptions are retained in this comparison. Its only inputs
are equality of the actual incoming state, time, and whole current control. -/
theorem preparedContinuingStart_eq_of_inputs
    (left right : RoundInput p rate) (hstate : left.state = right.state)
    (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    preparedContinuingStart rate left = preparedContinuingStart rate right := by
  cases left with
  | mk state rows selected time active rewardsL =>
    cases right with
    | mk stateR rowsR selectedR timeR activeR rewardsR =>
      dsimp only at hstate htime hcurrent
      subst stateR
      subst timeR
      cases hphase : state.coordinator with
      | first =>
          simp only [preparedContinuingStart, prepare, ReferenceActivePhysicalStep.dispatch,
            hphase, CoordinatorRoundDispatch.dispatch]
          rfl
      | live r owned base =>
          rw [preparedContinuingStart_live rate _ r owned base hphase,
            preparedContinuingStart_live rate _ r owned base hphase]
          exact liveDataStart_eq_of_current rate _ _ _ _ _ hcurrent
      | collection payload ledger proposal =>
          dsimp only [preparedContinuingStart, prepare, ReferenceActivePhysicalStep.dispatch]
          simp only [hphase]
          by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
          · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
            rfl
          · simp only [dite_eq_right hc]
      | dagger =>
          simp only [preparedContinuingStart, prepare, ReferenceActivePhysicalStep.dispatch, hphase]

/-- The current continuing dispatch and its start data agree at the SAME baseline. -/
theorem source_prefix_preparedStart (z : Z) :
    preparedContinuingStart rate (inp (ret z)) =
      preparedContinuingStart rate (inp (ret (pre z))) := by
  apply preparedContinuingStart_eq_of_inputs
  · exact source_prefix_incoming rate rewards C_star C_h q t s hs control0 z
  · rw [actualCurrentInput_time, actualCurrentInput_time]
  · rw [actualCurrentInput_baseline, actualCurrentInput_baseline]

/-- The actual local prepared configuration agrees, including dagger and every
ordinary status. This does not equate the retained prepared row. -/
theorem source_prefix_preparedConfiguration (z : Z) :
    ((prepare (inp (ret z))).followers.followers i).configuration =
      ((prepare (inp (ret (pre z)))).followers.followers i).configuration := by
  have hstate := source_prefix_incoming rate rewards C_star C_h q t s hs control0 z
  have htime : (inp (ret z)).time = (inp (ret (pre z))).time := by
    rw [actualCurrentInput_time, actualCurrentInput_time]
  have hcurrent : (inp (ret z)).row.2 (inp (ret z)).time =
      (inp (ret (pre z))).row.2 (inp (ret (pre z))).time := by
    rw [actualCurrentInput_baseline, actualCurrentInput_baseline]
  generalize inp (ret z) = left at *
  generalize inp (ret (pre z)) = right at *
  cases left with
  | mk state rows selected time active rewardsL =>
    cases right with
    | mk stateR rowsR selectedR timeR activeR rewardsR =>
      dsimp only at hstate htime hcurrent
      subst stateR
      subst timeR
      exact congrArg Prod.snd
        (ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
          i (state.activations i) (active i) (state.followers i) hcurrent)

private theorem continuingRecordingBranch_iff_start (x : X) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
      rate rewards C_star C_h q t s hs control0 x ↔
    t.val - s > 0 ∧
      (∀ record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x).records.take (t.val - s),
        cutoffChosen record.input = false) ∧
      (match preparedContinuingStart rate (inp x) with
      | some started => started.pending.Nonempty ∧ t.val + 1 < started.clock.g
      | none => False) := by
  dsimp only [ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch,
    preparedContinuingStart]
  cases (prepare (inp x)).coordinator with
  | live r owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- Actual continuing recording is invariant under the produced original-source prefix. -/
theorem continuingRecordingBranch_prefix_iff (z : Z) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
        rate rewards C_star C_h q t s hs control0 (ret (pre z)) ↔
      ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
        rate rewards C_star C_h q t s hs control0 (ret z) := by
  rw [continuingRecordingBranch_iff_start, continuingRecordingBranch_iff_start,
    ← source_prefix_preparedStart]
  apply and_congr_right
  intro _
  apply and_congr_left
  intro _
  have htags := source_prefix_cutoffTags rate rewards C_star C_h q t s hs control0 z
  have hall (records : List (RoundRecord (p := p) (rate := rate))) :
      (∀ record ∈ records, cutoffChosen record.input = false) ↔
        ∀ tag ∈ records.map (fun record => cutoffChosen record.input), tag = false := by
    simp only [List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro h tag record hr heq
      exact heq ▸ h record hr
    · intro h record hr
      exact h _ record hr rfl
  rw [hall, hall, htags]

/-- The same iff includes the actual prepared follower's unoccupied test. -/
theorem continuingRecordingFollowerBranch_prefix_iff (z : Z) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch
        rate rewards C_star C_h q t s hs control0 i (ret (pre z)) ↔
      ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch
        rate rewards C_star C_h q t s hs control0 i (ret z) := by
  unfold ReferenceFirstLiveRecordingSourceBranch.continuingRecordingFollowerBranch
  rw [continuingRecordingBranch_prefix_iff, ← source_prefix_preparedConfiguration]

/-- A continuing PREPARE selects the payload of its actual incoming live registers. -/
theorem incoming_payload_of_continuing (input : RoundInput p rate) :
    ∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) owned base d hsStart c arm,
      (prepare input).coordinator = .live r owned base (.continuingChosen d hsStart c arm) →
      (match input.state.coordinator with
      | .live registers _ _ => some registers.payload
      | _ => none) = some r.payload := by
  intro r owned base d hsStart c arm hcoord
  have hp := congrArg (fun cut : DispatchCut input =>
    match cut with
    | .live registers _ _ _ => some registers.payload
    | _ => none) hcoord
  cases hphase : input.state.coordinator with
  | first =>
      dsimp only [prepare, ReferenceActivePhysicalStep.dispatch] at hp
      simp only [hphase, CoordinatorRoundDispatch.dispatch] at hp
      change (none : Option (Payload rate)) = some r.payload at hp
      contradiction
  | live registers ownedR baseR =>
      simp only [prepare, ReferenceActivePhysicalStep.dispatch, hphase,
        CoordinatorRoundDispatch.dispatch] at hp
      change some registers.payload = some r.payload at hp
      exact hp
  | collection payload ledger proposal =>
      dsimp only [prepare, ReferenceActivePhysicalStep.dispatch] at hp
      simp only [hphase] at hp
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch] at hp
        change (none : Option (Payload rate)) = some r.payload at hp
        contradiction
      · simp only [dite_eq_right hc] at hp
        contradiction
  | dagger =>
      simp only [prepare, ReferenceActivePhysicalStep.dispatch, hphase] at hp
      contradiction

/-- The produced prefix on the literal actual follower subtype. -/
def prefixZi (z : Zi) : Zi :=
  ⟨pre z.val,
    (continuingRecordingFollowerBranch_prefix_iff
      rate rewards C_star C_h q t s hs control0 i z.val).mpr z.property⟩

@[simp] theorem prefixZi_val (z : Zi) :
    (prefixZi rate rewards C_star C_h q t s hs control0 i z).val = pre z.val := rfl

theorem prefixZi_idempotent (z : Zi) :
    prefixZi rate rewards C_star C_h q t s hs control0 i
      (prefixZi rate rewards C_star C_h q t s hs control0 i z) =
        prefixZi rate rewards C_star C_h q t s hs control0 i z := by
  apply Subtype.ext
  exact prefixZ_idempotent rate rewards C_star C_h q t s hs control0 z.val

/-- The remainder is exactly the first projection of M's original-source split. -/
def sourceFollowerRetained (z : Zi) : Xi :=
  (ReferenceFirstLiveSourceSavedMoments.followerSourceSplit
    rate rewards C_star C_h q t s hs control0 i z).1

local notation "xof" => sourceFollowerRetained rate rewards C_star C_h q t s hs control0 i
local notation "prei" => prefixZi rate rewards C_star C_h q t s hs control0 i

/-- The selected baseline payload of the actual follower source. -/
def selectedBaselinePayloadZ (z : Zi) : Payload rate :=
  ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
    rate rewards C_star C_h q t s hs control0 i (xof z)

/-- The same actual assigned arm as in M. -/
def assignedArmZ (z : Zi) : Fin p.K :=
  ReferenceFirstLiveSourceSavedMoments.assignedArm
    rate rewards C_star C_h q t s hs control0 i (xof z)

/-- The varying recording rate on the actual source follower fibre. -/
def xiZ (z : Zi) : ℝ := ReferenceFirstLiveSourceSavedMoments.xi
  rate rewards C_star C_h q t s hs control0 i (xof z)

/-- The current rounded reward from the unchanged whole reward table. -/
def rhoZ (z : Zi) : ℝ := ReferenceFirstLiveSourceSavedMoments.rho
  rate rewards C_star C_h q t s hs control0 i (xof z)

/-- The literal quantized value, with the same rate and reward. -/
def vZ (z : Zi) : ℝ := ReferenceFirstLiveSourceSavedMoments.value
  rate rewards C_star C_h q t s hs control0 i (xof z)

/-- The selected payload agrees after prefixing the actual original source. -/
theorem selectedBaselinePayloadZ_prefix (z : Zi) :
    selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i (prei z) =
      selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i z := by
  let xp := ReferenceFirstLiveRecordingReadoutMeasurability.followerAsPlus
    (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) (q := q) (t := t)
    (s := s) (hs := hs) (control0 := control0) i
  obtain ⟨r, owned, base, d, hd, c, arm, hcoord, hpayload⟩ :=
    ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_actual (xp (xof z))
  obtain ⟨r', owned', base', d', hd', c', arm', hcoord', hpayload'⟩ :=
    ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload_eq_actual (xp (xof (prei z)))
  have hleft := incoming_payload_of_continuing rate _ r owned base d hd c arm hcoord
  have hright := incoming_payload_of_continuing rate _ r' owned' base' d' hd' c' arm' hcoord'
  change (match (inp (ret z.val)).state.coordinator with
    | .live registers _ _ => some registers.payload | _ => none) = some r.payload at hleft
  change (match (inp (ret (pre z.val))).state.coordinator with
    | .live registers _ _ => some registers.payload | _ => none) = some r'.payload at hright
  rw [source_prefix_incoming] at hleft
  have heq : r'.payload = r.payload := Option.some.inj (hright.symm.trans hleft)
  change ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload (xp (xof (prei z))) =
    ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload (xp (xof z))
  exact hpayload'.trans (heq.trans hpayload.symm)

theorem assignedArmZ_prefix (z : Zi) :
    assignedArmZ rate rewards C_star C_h q t s hs control0 i (prei z) =
      assignedArmZ rate rewards C_star C_h q t s hs control0 i z := by
  change (selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i (prei z)).assignment.assigned
      (bufferFollowerIndex i) =
    (selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i z).assignment.assigned
      (bufferFollowerIndex i)
  rw [selectedBaselinePayloadZ_prefix]

theorem xiZ_prefix (z : Zi) :
    xiZ rate rewards C_star C_h q t s hs control0 i (prei z) =
      xiZ rate rewards C_star C_h q t s hs control0 i z := by
  change CanonicalRecordingRates.xi p rate.eta.val
      (selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i (prei z)).anchor
      (assignedArmZ rate rewards C_star C_h q t s hs control0 i (prei z)) = _
  rw [selectedBaselinePayloadZ_prefix, assignedArmZ_prefix]
  rfl

theorem rhoZ_prefix (z : Zi) :
    rhoZ rate rewards C_star C_h q t s hs control0 i (prei z) =
      rhoZ rate rewards C_star C_h q t s hs control0 i z := by
  change ((rewards t (assignedArmZ rate rewards C_star C_h q t s hs control0 i (prei z))).val : ℝ) /
    (D p : ℝ) = _
  rw [assignedArmZ_prefix]
  rfl

theorem vZ_prefix (z : Zi) :
    vZ rate rewards C_star C_h q t s hs control0 i (prei z) =
      vZ rate rewards C_star C_h q t s hs control0 i z := by
  change QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
    (xiZ rate rewards C_star C_h q t s hs control0 i (prei z))
    (rhoZ rate rewards C_star C_h q t s hs control0 i (prei z)) = _
  rw [xiZ_prefix, rhoZ_prefix]
  rfl

/-- The exact analysis field on the literal follower source subtype. -/
abbrev sourceFollowerPrefixField : MeasurableSpace Zi :=
  (inferInstance : MeasurableSpace (SourceInput p)).comap
    (fun z : Zi => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val)

local notation "Fi" => sourceFollowerPrefixField rate rewards C_star C_h q t s hs control0 i

theorem sourceFollowerPrefixField_eq_trace :
    Fi = (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)).comap
      (fun z : Zi => z.val.val) := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ, MeasurableSpace.comap_comp]
  exact congrArg (fun f : Zi → SourceInput p =>
    (inferInstance : MeasurableSpace (SourceInput p)).comap f)
      (funext fun z => ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z.val.val)

/-- The produced prefix is measurable FROM the exact smaller field Fi into
Zi's inherited Borel space. This supplies the required factorization. -/
theorem prefixZi_adapted : Measurable[Fi] prei := by
  apply Measurable.subtype_mk
  apply Measurable.subtype_mk
  change Measurable[Fi] (fun z : Zi =>
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val)
  have heq : (fun z : Zi => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z.val.val) =
      fun z => ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val := by
    funext z
    exact (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z.val.val).symm
  rw [heq]
  exact comap_measurable _

private theorem measurable_sourceFollowerRetained : Measurable xof :=
  measurable_fst.comp (ReferenceFirstLiveSourceSavedMoments.measurable_followerSourceSplit
    rate rewards C_star C_h q t s hs control0 i)

theorem selectedBaselinePayloadZ_adapted :
    Measurable[Fi] (selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i) := by
  have h : Measurable (selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i) :=
    (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselinePayload.comp
      (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_followerAsPlus i)).comp
        (measurable_sourceFollowerRetained rate rewards C_star C_h q t s hs control0 i)
  have hpre : Measurable[Fi] (fun z : Zi =>
      selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i (prei z)) :=
    h.comp (prefixZi_adapted rate rewards C_star C_h q t s hs control0 i)
  have heq : (fun z : Zi => selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i (prei z)) =
      selectedBaselinePayloadZ rate rewards C_star C_h q t s hs control0 i :=
    funext (fun z => selectedBaselinePayloadZ_prefix rate rewards C_star C_h q t s hs control0 i z)
  rwa [heq] at hpre

theorem assignedArmZ_adapted :
    Measurable[Fi] (assignedArmZ rate rewards C_star C_h q t s hs control0 i) := by
  have h : Measurable (assignedArmZ rate rewards C_star C_h q t s hs control0 i) :=
    ((ReferenceFirstLiveRecordingReadoutMeasurability.measurable_selectedBaselineAssignedArm i).comp
      (ReferenceFirstLiveRecordingReadoutMeasurability.measurable_followerAsPlus i)).comp
        (measurable_sourceFollowerRetained rate rewards C_star C_h q t s hs control0 i)
  have hpre : Measurable[Fi] (fun z : Zi =>
      assignedArmZ rate rewards C_star C_h q t s hs control0 i (prei z)) :=
    h.comp (prefixZi_adapted rate rewards C_star C_h q t s hs control0 i)
  have heq : (fun z : Zi => assignedArmZ rate rewards C_star C_h q t s hs control0 i (prei z)) =
      assignedArmZ rate rewards C_star C_h q t s hs control0 i :=
    funext (fun z => assignedArmZ_prefix rate rewards C_star C_h q t s hs control0 i z)
  rwa [heq] at hpre

/-- Adapted measurability of the actual rate, obtained by factoring through
prefixZi rather than inferring it from ordinary Borel measurability. -/
theorem xiZ_adapted : Measurable[Fi] (xiZ rate rewards C_star C_h q t s hs control0 i) := by
  have h : Measurable[Fi] (fun z : Zi => xiZ rate rewards C_star C_h q t s hs control0 i (prei z)) :=
    ((ReferenceFirstLiveSourceSavedMoments.measurable_xi
    rate rewards C_star C_h q t s hs control0 i).comp
      (measurable_sourceFollowerRetained rate rewards C_star C_h q t s hs control0 i)).comp
        (prefixZi_adapted rate rewards C_star C_h q t s hs control0 i)
  have heq : (fun z : Zi => xiZ rate rewards C_star C_h q t s hs control0 i (prei z)) =
      xiZ rate rewards C_star C_h q t s hs control0 i :=
    funext (fun z => xiZ_prefix rate rewards C_star C_h q t s hs control0 i z)
  rw [heq] at h
  exact h

theorem rhoZ_adapted : Measurable[Fi] (rhoZ rate rewards C_star C_h q t s hs control0 i) := by
  have h : Measurable[Fi] (fun z : Zi => rhoZ rate rewards C_star C_h q t s hs control0 i (prei z)) :=
    ((ReferenceFirstLiveSourceSavedMoments.measurable_rho
    rate rewards C_star C_h q t s hs control0 i).comp
      (measurable_sourceFollowerRetained rate rewards C_star C_h q t s hs control0 i)).comp
        (prefixZi_adapted rate rewards C_star C_h q t s hs control0 i)
  have heq : (fun z : Zi => rhoZ rate rewards C_star C_h q t s hs control0 i (prei z)) =
      rhoZ rate rewards C_star C_h q t s hs control0 i :=
    funext (fun z => rhoZ_prefix rate rewards C_star C_h q t s hs control0 i z)
  rw [heq] at h
  exact h

theorem vZ_adapted : Measurable[Fi] (vZ rate rewards C_star C_h q t s hs control0 i) := by
  have h : Measurable[Fi] (fun z : Zi => vZ rate rewards C_star C_h q t s hs control0 i (prei z)) :=
    ((ReferenceFirstLiveSourceSavedMoments.measurable_value
    rate rewards C_star C_h q t s hs control0 i).comp
      (measurable_sourceFollowerRetained rate rewards C_star C_h q t s hs control0 i)).comp
        (prefixZi_adapted rate rewards C_star C_h q t s hs control0 i)
  have heq : (fun z : Zi => vZ rate rewards C_star C_h q t s hs control0 i (prei z)) =
      vZ rate rewards C_star C_h q t s hs control0 i :=
    funext (fun z => vZ_prefix rate rewards C_star C_h q t s hs control0 i z)
  rw [heq] at h
  exact h

end Bandits.Support.ReferenceFirstLiveSourcePrefixBranchInvariance

end
