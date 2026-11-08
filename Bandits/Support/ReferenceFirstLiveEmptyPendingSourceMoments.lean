/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-!
# Actual empty-pending first-live raw numerical moments

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module reads the current numerical cell from the existing original-source
first-live window. It proves raw first and square moment identities on the
inherited finite, unnormalized empty-pending measures. It does not establish
strict-past adaptation, accepted-record conditional laws, queue drift, or a
calendar estimate. The next consumer is
`ReferenceFirstLiveEmptyPendingAcceptedMoments`, followed by separate empty
queue drift, exponential, and calendar producers.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingSourceMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Ze" =>
  Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
    rate rewards C_star C_h q t s hs control0
local notation "Xe" =>
  Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.Xempty
    rate rewards C_star C_h q t s hs control0
local notation "n" => t.val - s
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "scale" => rate.eta.val * (ConstructorDimensions.D p : ℝ)
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "muE" =>
  Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
local notation "nuE" =>
  Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.nuEmpty
    rate rewards C_star C_h q t s hs control0

theorem actualSpan (z : Ze) :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed +
        (n + 1) ≤ p.T := by
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed = s := by
    simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  rw [helapsed]
  omega

def actualCells (z : Ze) : List (RecordedQueueRun.RoundInput p.K) :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
    z.val.property.2.1 (n + 1) (actualSpan rate rewards C_star C_h q t s hs control0 z)

private theorem physicalRun_records_eq_of_initial_eq
    (left right : ReferenceActivePhysicalStep.State p rate) (h : left = right)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
    (rewards : RewardTable p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (hl : ReferenceActivePhysicalHorizon.allActiveAtStart left start)
    (hr : ReferenceActivePhysicalHorizon.allActiveAtStart right start) :
    (ReferenceActivePhysicalHorizon.run left rows selected rewards start count hspan hl).records =
      (ReferenceActivePhysicalHorizon.run right rows selected rewards start count hspan hr).records := by
  cases h
  rfl

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
    liveCutoffTag rate r owned base row out =
      (match (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (input : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    ReferenceCollectionPhaseHistory.cutoffChosen input =
      liveCutoffTag rate (ReferenceActivePhysicalStep.liveRegistersAt r input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base)) := by
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
    ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

private theorem cutoffChosen_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (ConstructorDimensions.M p)) (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : RewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows otherSelected).2 time) :
    ReferenceCollectionPhaseHistory.cutoffChosen ⟨state, rows, selected, time, active, rewards⟩ =
      ReferenceCollectionPhaseHistory.cutoffChosen
        ⟨state, otherRows, otherSelected, time, active, otherRewards⟩ := by
  classical
  cases hphase : state.coordinator with
  | first =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase, CoordinatorRoundDispatch.dispatch]
      rfl
  | live r owned base =>
      have hdata := ReferenceActiveDispatchTemporal.liveOutcomeData_eq_of_current
        (ReferenceActivePhysicalStep.liveRegistersAt r time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned time) base
        (rows selected) (otherRows otherSelected) hcurrent
      have htag := congrArg (fun data =>
        match data.2.2 with
        | .inr (.inr (.inr _)) => true
        | _ => false) hdata
      rw [← liveCutoffTag_eq_projection rate, ← liveCutoffTag_eq_projection rate] at htag
      rw [cutoffChosen_live rate _ r owned base hphase,
        cutoffChosen_live rate _ r owned base hphase]
      simpa only [ReferenceActivePhysicalStep.liveInput,
        ReferenceActivePhysicalStep.RoundInput.row, liveCutoffTag] using htag
  | collection payload ledger proposal =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · simp only [dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      · simp only [dite_eq_right hc]
  | dagger =>
      dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
        ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
      simp only [hphase]

private theorem cutoffChosen_congr (left right : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : left.state = right.state) (htime : left.time = right.time)
    (hcurrent : left.row.2 left.time = right.row.2 right.time) :
    ReferenceCollectionPhaseHistory.cutoffChosen left =
      ReferenceCollectionPhaseHistory.cutoffChosen right := by
  cases left
  cases right
  dsimp only at hstate htime hcurrent
  cases hstate
  cases htime
  exact cutoffChosen_eq_of_current rate _ _ _ _ _ _ _ _ _ hcurrent

private theorem run_cutoffTags_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p)) (rewards : RewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hcontrols : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
      (rows selected).2 j = (otherRows selected).2 j)
    (hbefore : ∀ j : Fin p.T, j.val < start →
      ((rows selected).2 j).1 ContinuousControlSlice.Label.prop =
        ((otherRows selected).2 j).1 ContinuousControlSlice.Label.prop) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
      (ReferenceActivePhysicalHorizon.run initial otherRows selected rewards start count hspan hmode).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
  induction count with
  | zero => simp [ReferenceActivePhysicalHorizon.run_zero_records]
  | succ count ih =>
      have hprefix : start + count ≤ p.T := by omega
      have hcontrolsPrefix : ∀ j : Fin p.T, start ≤ j.val → j.val < start + count →
          (rows selected).2 j = (otherRows selected).2 j := by
        intro j hj hk
        exact hcontrols j hj (by omega)
      have htags := ih hprefix hcontrolsPrefix
      have hstate := (ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
        initial rows otherRows selected rewards rewards start count hprefix hmode
        hcontrolsPrefix (fun _ _ _ => rfl) (fun _ => hbefore)).1
      rw [ReferenceActivePhysicalHorizon.run_successor_step,
        ReferenceActivePhysicalHorizon.run_successor_step]
      simp only [ReferenceActivePhysicalHorizon.foldRound, List.map_append,
        List.map_singleton]
      rw [htags]
      congr 1
      apply congrArg List.singleton
      apply cutoffChosen_congr
      · exact hstate
      · rfl
      · let j : Fin p.T := ⟨start + count, by omega⟩
        have hjval : j.val = start + count := rfl
        exact hcontrols j (by rw [hjval]; omega) (by rw [hjval]; omega)

theorem currentOriginalWindowIndex (z : Ze) :
    ∃ hn : n < (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate z.val.val rewards C_star C_h z.val.property.2.1 (n + 1)
      (actualSpan rate rewards C_star C_h q t s hs control0 z)).length,
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val.val rewards C_star C_h z.val.property.2.1 (n + 1)
        (actualSpan rate rewards C_star C_h q t s hs control0 z))[n]'hn =
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val := by
  classical
  let x := Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty
    rate rewards C_star C_h q t s hs control0 z
  let source := z.val.val
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let hc := z.val.property.2.1
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
    simpa only [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  have hspanS : s + (n + 1) ≤ p.T := by
    omega
  have hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        (n + 1) ≤ p.T := by rw [helapsed]; exact hspanS
  have hx := x.property
  have hbaselineIndex := Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.actualRetainedPrefixRun_current_in_firstLiveWindow
    rate rewards C_star C_h q t s hs control0 x.val hx
  let split := Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0 z
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source0
    rewards C_star C_h (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
      rate rewards C_star C_h q t s hs control0 x.val).1
  let prefix0 := ReferenceActivePhysicalHorizon.run initial source0.1.2 q rewards s n
    (by omega) (by
      have hseed := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source0 rewards C_star C_h
        (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
          rate rewards C_star C_h q t s hs control0 x.val).1).activeAtStart
      have helapsed0 := (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
        rate rewards C_star C_h q t s hs control0 x.val).2
      rw [← helapsed0]
      exact hseed)
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    have hseed := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source0 rewards C_star C_h
      (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
        rate rewards C_star C_h q t s hs control0 x.val).1).activeAtStart
    rw [← (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
      rate rewards C_star C_h q t s hs control0 x.val).2]
    exact hseed
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact z.val.property.1
  have hsource0 : source0 = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t source control0 := by
    have hretained : x.val.val =
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 := by
      change (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
          rate rewards C_star C_h q t s hs control0 z.val).val = _
      exact ReferenceTotalSourceDisintegration.sourceRetainedInput_val rate rewards C_star C_h
        t control0 (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z.val
    dsimp [source0, ReferenceGeneratedActivePrefixFactor.splitSource]
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control0, x.val.val) = _
    rw [hretained]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t source control0 hindex
  have hprivate : source.2 = source0.2 := by rw [hsource0]; rfl
  have hcoordIndex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source0 =
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source := by
    unfold ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex
    exact congrArg (fun v => PrivateSourceStreams.coordinatorIndex p v.1.2) hprivate.symm
  have hselected0 : ActualInitializationPhysicalStep.selectedRowIndex p source0 = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p source0 =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source0 :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p source0).symm
      _ = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source := hcoordIndex
      _ = q := hindex
  have hc0 := (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
    rate rewards C_star C_h q t s hs control0 x.val).1
  have elapsed0 := (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
    rate rewards C_star C_h q t s hs control0 x.val).2
  have hids : source.1.1 = source0.1.1 := by rw [hsource0]; rfl
  have hforward : ∀ j : Fin p.T, j.val < t.val →
      ∀ v : Fin (BootstrapDimensions.A_id p),
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 v j =
        (source0.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 v j := by
    intro j hj v
    rw [hsource0]
    have hjt : j ≠ t := by intro h; subst j; omega
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p source).symm.trans hindex
    simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
      hselected]
  have hcontrol : ∀ j : Fin p.T, j.val < t.val →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 j =
        (source0.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 j := by
    intro j hj
    rw [hsource0]
    have hjt : j ≠ t := by intro h; subst j; omega
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p source).symm.trans hindex
    simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
      hselected, Function.update_of_ne hjt]
  have hinit := ReferenceInitializationStoppedLocality.source_calendar_stopped_output_eq_of_event
    rate rewards C_star C_h source source0 t.val (by omega) hids hprivate hforward hcontrol
    (Or.inl ⟨hc, by rw [helapsed]; omega⟩)
  have hlaunchEq : ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc =
      initial := by
    have hcorrected :
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate source0 rewards C_star C_h := by
      rcases hinit with ⟨_, houtput, _, _, hord, _, _, _, _⟩
      have hc0' : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source0 rewards C_star C_h rate)).crossing.isSome = true := by
        rw [← houtput]
        exact hc
      dsimp only [ReferenceCorrectedInitializationLaunch.correctedLaunch]
      rw [dite_eq_left hc, dite_eq_left hc0']
      apply congrArg some
      rw [ReferenceActivePhysicalStep.State.mk.injEq]
      exact ⟨rfl, rfl,
        funext (fun i => by
          let follower := ActualReferenceInitializationBlock.refFollower i
          let inputSource := ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate
          let inputSource0 := ActualReferenceInitializationBlock.referenceInput
            source0 rewards C_star C_h rate
          have hactivation := congrArg (fun b => b.activation follower) houtput
          have hsome : ((ReferenceInitializationRun.output inputSource).activation follower).isSome = true := by
            change ((ReferenceInitializationRun.run inputSource (BootstrapDimensions.n_boot p)).activation follower).isSome = true
            exact ReferenceInitializationRun.run_all_activated_at_crossing inputSource
              (BootstrapDimensions.n_boot p) hc follower
          have hsome0 : ((ReferenceInitializationRun.output inputSource0).activation follower).isSome = true := by
            change ((ReferenceInitializationRun.run inputSource0 (BootstrapDimensions.n_boot p)).activation follower).isSome = true
            exact ReferenceInitializationRun.run_all_activated_at_crossing inputSource0
              (BootstrapDimensions.n_boot p) hc0' follower
          apply Option.some.inj
          calc
            some (Option.get _ hsome) =
                (ReferenceInitializationRun.output inputSource).activation follower :=
              Option.coe_get hsome
            _ = (ReferenceInitializationRun.output inputSource0).activation follower := hactivation
            _ = some (Option.get _ hsome0) := (Option.coe_get hsome0).symm),
        funext (fun i => congrArg (fun state =>
          DeclaredFollowerLocalRound.LocalConfiguration.ordinary state
            (ActiveFollowerLifecycle.initialMemory p))
          (hord (ActualReferenceInitializationBlock.refFollower i)))⟩
    have hleft := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hc
    have hright := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source0 rewards C_star C_h hc0
    exact Option.some.inj (hleft.symm.trans (hcorrected.trans hright))
  have hcontrols : ∀ j : Fin p.T, s ≤ j.val → j.val < s + n →
      (source0.1.2 q).2 j = (source.1.2 q).2 j := by
    intro j hj hjend
    have hjt : j.val < t.val := by omega
    rw [hsource0]
    simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
      Function.update_of_ne (show j ≠ t from Fin.ne_of_val_ne (by omega))]
  have hbefore : ∀ j : Fin p.T, j.val < s →
      ((source0.1.2 q).2 j).1 ContinuousControlSlice.Label.prop =
        ((source.1.2 q).2 j).1 ContinuousControlSlice.Label.prop := by
    intro j hj
    have hsame : (source0.1.2 q).2 j = (source.1.2 q).2 j := by
      rw [hsource0]
      simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
        Function.update_of_ne (show j ≠ t from by intro h; subst j; omega)]
    exact congrArg (fun u : TimeControl p => u.1 ContinuousControlSlice.Label.prop) hsame
  have hprefixEq := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
    initial source0.1.2 source.1.2 q rewards rewards s n (by omega) hmode
    hcontrols (fun _ _ _ => rfl) (fun _ => hbefore)
  have htags := run_cutoffTags_eq rate initial source0.1.2 source.1.2 q rewards s n
    (by omega) hmode hcontrols hbefore
  have hselectedSplit : ActualInitializationPhysicalStep.selectedRowIndex p
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) = q := hselected0
  have hbaseRun :
      ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x.val =
      ReferenceActivePhysicalHorizon.run initial source0.1.2 q rewards s (n + 1)
        hspanS hmode := by
    simp only [ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, elapsed0, hselectedSplit]
    rfl
  have hbaseFull : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x.val).records =
      (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x.val).records := by
    apply (List.takeWhile_prefix _).eq_of_length_le
    have hlen : (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x.val).records.length = n + 1 := by
      rw [hbaseRun]
      exact ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
    rw [hlen]
    exact Nat.succ_le_of_lt hbaselineIndex.1
  have hbaseAll : ∀ record ∈ prefix0.records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hrecord
    have hmem : record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x.val).records := by
      rw [hbaseRun, ReferenceActivePhysicalHorizon.run_successor_step]
      exact List.mem_append_left _ hrecord
    rw [← hbaseFull] at hmem
    simpa using List.mem_takeWhile_imp hmem
  have hsourceAll : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode).records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hrecord
    have hmem : ReferenceCollectionPhaseHistory.cutoffChosen record.input ∈
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode).records.map
          (fun r => ReferenceCollectionPhaseHistory.cutoffChosen r.input) :=
      List.mem_map.mpr ⟨record, hrecord, rfl⟩
    rw [← htags] at hmem
    obtain ⟨record0, hrecord0, hcut⟩ := List.mem_map.mp hmem
    rw [← hcut]
    exact hbaseAll record0 hrecord0
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hfirst, hseed, hunoccupied, hvalid, hpairwise, htime⟩ :=
    Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw.actual_empty_recording_inputs
      rate rewards C_star C_h q t s hs control0 x.val hx
  let u := split.2
  have hcontrolRecovered : u = ReferenceFirstLiveRecordingSourceCylinder.originalControl
      rate rewards C_star C_h q t s hs z.val := by
    rfl
  obtain ⟨c_u, arm_u, hcoord_u⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
    (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
      rate rewards C_star C_h q t s hs control0 x.val)
    r owned base d hsStart c arm hcoord u
  have hcontrolInput := ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original
    rate rewards C_star C_h q t s hs control0 z.val
  change ReferenceContinuingLiveSlicePreparation.inputAtControl
    (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
      rate rewards C_star C_h q t s hs control0 x.val)
    (ReferenceFirstLiveRecordingSourceCylinder.originalControl
      rate rewards C_star C_h q t s hs z.val) = _ at hcontrolInput
  rw [← hcontrolRecovered] at hcontrolInput
  have hcurrentCutoff :
      ReferenceCollectionPhaseHistory.cutoffChosen
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).input = false := by
    rw [← hcontrolInput]
    unfold ReferenceCollectionPhaseHistory.cutoffChosen
    rw [hcoord_u]
  have hboundary :
      ReferenceTotalSourceDisintegration.sourceIncomingBoundary
          rate rewards C_star C_h t control0
            (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z.val =
        ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
          rate rewards C_star C_h q t s hs control0 x.val := by
    rw [ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput_eq_retainedIncomingBoundary]
    rfl
  have hstate : prefix0.finalState =
      (ReferenceTotalSourceDisintegration.sourceIncomingBoundary
        rate rewards C_star C_h t control0
          (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z.val).state := by
    rw [hboundary]
    change (ReferenceActivePhysicalHorizon.run initial source0.1.2 q rewards s n
      (by omega) hmode).finalState =
        (ReferenceContinuingDataCandidateLogging.candidateInput initial source0.1.2 q rewards
          s n hspanS hmode).state
    rfl
  have hstateFinal :
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode).finalState =
        (ReferenceTotalSourceDisintegration.sourceIncomingBoundary
          rate rewards C_star C_h t control0
            (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z.val).state :=
    hprefixEq.1.symm.trans hstate
  have hcurInput :
      ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s hmode
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode)
        ⟨s + n, by omega, by omega⟩ =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input := by
    let leftInput := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s hmode
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode)
      ⟨s + n, by omega, by omega⟩
    let rightInput := (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val).input
    have hleftState : leftInput.state = rightInput.state := hstateFinal
    have hrows : leftInput.rows = rightInput.rows := rfl
    have hselected : leftInput.selected = rightInput.selected := z.val.property.1.symm
    have htime' : leftInput.time = rightInput.time := by
      change (⟨s + n, by omega⟩ : Fin p.T) = t
      apply Fin.ext
      simp
      omega
    have hrewards : leftInput.rewards = rightInput.rewards := rfl
    cases leftInput with
    | mk ls lrows lselected ltime lact lrewards =>
      cases rightInput with
      | mk rs rrows rselected rtime ractive rrewards =>
        simp_all [leftInput, rightInput, ReferenceActivePhysicalHorizon.roundInputAt,
          ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord,
          ReferenceTotalSourceDisintegration.sourceIncomingBoundary,
          ReferenceFixedTimeSourceControlCoupling.roundInputAtSource]
  have hsourceAppend :
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
        hspanS hmode).records =
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode).records ++
          [ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val] := by
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    simp only [ReferenceActivePhysicalHorizon.foldRound]
    have hlast :
        ({ input := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s
              hmode (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode)
              ⟨s + n, by omega, by omega⟩,
            output := ReferenceActivePhysicalStep.step
              (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s
                hmode (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode)
                ⟨s + n, by omega, by omega⟩), output_eq := rfl } :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =
          ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val :=
      congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
        (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) hcurInput
    rw [hlast]
  have hsourceFull : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode).records ++
        [ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val],
      (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true := by
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprefix | hlast
    · simp [hsourceAll record hprefix]
    · simp only [List.mem_singleton] at hlast
      rcases hlast with rfl
      simp [hcurrentCutoff]
  have hallTags : ∀ record ∈
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
        hspanS hmode).records,
      (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true := by
    intro record hrecord
    rw [hsourceAppend] at hrecord
    exact hsourceFull record hrecord
  have hwindow : ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
        hspanS hmode).records =
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
          hspanS hmode).records := by
    rw [ReferenceFirstLiveConfirmationHistory.firstLiveWindow]
    exact List.takeWhile_eq_self_iff.mpr hallTags
  have hmodeSource : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc) s := by
    simpa only [helapsed] using
      (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc).activeAtStart
  have hrunRecords :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate source rewards C_star C_h hc
        (n + 1) hspan).records =
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
          hspanS hmode).records := by
    dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveRun]
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p source).symm.trans hindex
    simpa only [helapsed, hselected] using
      physicalRun_records_eq_of_initial_eq rate
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        initial hlaunchEq source.1.2 q rewards s (n + 1) hspanS hmodeSource hmode
  have hwindowRun :
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h hc
          (n + 1) hspan =
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
          hspanS hmode).records := by
    dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow]
    rw [hrunRecords, hwindow]
  have hlength :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h hc
        (n + 1) hspan).length = n + 1 := by
    rw [hwindowRun]
    exact ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 q rewards s
      (n + 1) hspanS hmode
  have hprefixLen :
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n (by omega) hmode).records.length = n :=
    ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 q rewards s n (by omega) hmode
  have hcurrentOpt :
      ((ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
        hspanS hmode).records)[n]? =
        some (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val) := by
    rw [hsourceAppend]
    simp [hprefixLen]
  have hcurrentAt :
      ((ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h hc
        (n + 1) hspan)[n]'(by rw [hlength]; omega)) =
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val := by
    have hwindowOpt :
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate source rewards C_star C_h hc
          (n + 1) hspan)[n]? =
          some (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val) := by
      rw [hwindowRun]
      exact hcurrentOpt
    rw [List.getElem?_eq_getElem (by rw [hlength]; omega)] at hwindowOpt
    exact Option.some.inj hwindowOpt
  refine ⟨by rw [hlength]; omega, ?_⟩
  exact hcurrentAt

/-- The current original source cell is present without a caller premise. -/
theorem currentCellIndex (z : Ze) :
    n < (actualCells rate rewards C_star C_h q t s hs control0 z).length := by
  simpa only [actualCells, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length] using
    (currentOriginalWindowIndex rate rewards C_star C_h q t s hs control0 z).choose

def cell (z : Ze) : RecordedQueueRun.RoundInput p.K :=
  (actualCells rate rewards C_star C_h q t s hs control0 z)[n]'
    (currentCellIndex rate rewards C_star C_h q t s hs control0 z)

/-- Literal count-`n` numerical list on the same original complete source. -/
def actualPastCells (z : Ze) : List (RecordedQueueRun.RoundInput p.K) :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
    z.val.property.2.1 n (by
      have hspan := actualSpan rate rewards C_star C_h q t s hs control0 z
      omega)

theorem actualCells_length (z : Ze) :
    (actualCells rate rewards C_star C_h q t s hs control0 z).length = n + 1 := by
  have hindex := currentCellIndex rate rewards C_star C_h q t s hs control0 z
  have hrun : (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val.val rewards
      C_star C_h z.val.property.2.1 (n + 1)
      (actualSpan rate rewards C_star C_h q t s hs control0 z)).records.length = n + 1 :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hprefix := (List.takeWhile_prefix
    (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      !ReferenceCollectionPhaseHistory.cutoffChosen record.input)
    (l := (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val.val rewards
      C_star C_h z.val.property.2.1 (n + 1)
      (actualSpan rate rewards C_star C_h q t s hs control0 z)).records)).length_le
  have hle : (actualCells rate rewards C_star C_h q t s hs control0 z).length ≤ n + 1 := by
    rw [actualCells, ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length]
    exact hprefix.trans hrun.le
  omega

theorem actualCells_take_successor (z : Ze) :
    (actualCells rate rewards C_star C_h q t s hs control0 z).take n =
      actualPastCells rate rewards C_star C_h q t s hs control0 z :=
  ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor
    rate rewards C_star C_h q t s hs control0 z.val

/-- The successor appends precisely the current actual cell to its own past. -/
theorem actualCells_eq_past_append_cell (z : Ze) :
    actualCells rate rewards C_star C_h q t s hs control0 z =
      actualPastCells rate rewards C_star C_h q t s hs control0 z ++
        [cell rate rewards C_star C_h q t s hs control0 z] := by
  have htake := List.take_succ_eq_append_getElem
    (currentCellIndex rate rewards C_star C_h q t s hs control0 z)
  rw [actualCells_take_successor, ← actualCells_length, List.take_length] at htake
  exact htake

local notation "xofE" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0
local notation "xiE" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control0
local notation "markerE" =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker rate rewards C_star C_h q t s hs control0

def rho {p : Parameters} (_rate : RateInput p) (rewards : RewardTable p)
    (_C_star _C_h : ℝ) (_q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (_hs : s ≤ t.val) (_control0 : TimeControl p) (j : Fin p.K) : ℝ :=
  ((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ)

def v (x : Xe) (j : Fin p.K) : ℝ :=
  (Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
    xiE x j) : ℝ) / scale

def a (z : Ze) (j : Fin p.K) : ℝ :=
  (RecordedQueueRun.quantizedArrival queue (cell rate rewards C_star C_h q t s hs control0 z) j : ℝ) /
    scale

private theorem sourceArm_congr_view
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (view₁ view₂ : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      view₁.payload view₁.cutoff record.input.time view₁.complementWeights)
    (hview : view₁ = view₂) :
    ReferenceFirstWindowNumericalStream.sourceArm record view₁.payload
      view₁.pendingAtChoice states view₁.complementWeights view₁.cutoff hvalid =
    ReferenceFirstWindowNumericalStream.sourceArm record view₂.payload
      view₂.pendingAtChoice states view₂.complementWeights view₂.cutoff (hview ▸ hvalid) := by
  cases hview
  rfl

private theorem actualMarker_eq_cellSourceArm (z : Ze)
    {record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (sourceCell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hrecord : record = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val) :
    markerE z = ReferenceFirstWindowNumericalStream.sourceArm record
      sourceCell.selected.view.payload sourceCell.selected.view.pendingAtChoice
      sourceCell.states sourceCell.selected.view.complementWeights
      sourceCell.selected.view.cutoff sourceCell.choiceInputsValid := by
  classical
  cases hrecord
  let x := xofE z
  let source := x.val
  let source0 := ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit source
  let initial := ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial source
  let seed := ReferenceFirstLiveRecordingSourceBranch.actualRetainedSeed
    rate rewards C_star C_h q t s hs control0 x.val
  let hspan := ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan hs
  let hmode := ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode x.val
  let candidate := ReferenceContinuingDataCandidateLogging.candidateInput
    initial source0.1.2 q rewards s n hspan hmode
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord0,
      henabled0, hfirst, hseed, hunoccupied, hvalidSeed, hpairwise, htime⟩ :=
      ReferenceFirstLiveEmptyPendingMarkerLaw.actual_empty_recording_inputs
      rate rewards C_star C_h q t s hs control0 source x.property
  have hcandidateTime : candidate.time.val = t.val := by
    change s + (t.val - s) = t.val
    omega
  have hcoord :
      (ReferenceActivePhysicalStep.prepare
        (ReferenceContinuingDataCandidateLogging.candidateInput initial source0.1.2 q
          rewards s n hspan hmode)).coordinator =
        .live r owned base (.continuingChosen d hsStart c arm) := by
    simpa [candidate, initial, source0,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentCount,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan,
      ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput] using hcoord0
  have henabled :
      (ReferenceContinuingDataCandidateLogging.candidateInput initial source0.1.2 q
        rewards s n hspan hmode).time.val + 1 < d.startResult.clock.g := by
    simpa [candidate, initial, source0,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentCount,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan,
      ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput, hcandidateTime] using henabled0
  have hpair := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
    initial source0.1.2 q rewards s n hspan hmode seed.followers seed.memory
    hfirst hseed hunoccupied hvalidSeed hpairwise htime
    r owned base d hsStart c arm hcoord states memories ho henabled
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl
    rate rewards C_star C_h q t s hs z.val
  obtain ⟨c_u, arm_u, hcoord_u⟩ :=
    ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control candidate
      r owned base d hsStart c arm hcoord u
  let selectedU := ReferenceContinuingLiveSlicePreparation.continuingSelection
    (ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u)
    r owned base d hsStart c_u arm_u
  have hselectedU := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
    (ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u)
    r owned base d hsStart c_u arm_u hcoord_u
  have hcandidateInput :
      ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput
        source = candidate := by
    simpa only [candidate, initial, source0,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentCount,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan] using
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput_eq_candidateInput source)
  have hinputU : ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input := by
    rw [← hcandidateInput]
    change ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl source u = _
    exact ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original
      rate rewards C_star C_h q t s hs control0 z.val
  have hselectedCell :
      (ReferenceActivePhysicalStep.prepare
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection =
        some sourceCell.selected := by
    exact sourceCell.selection_actual
  have hviews := congrArg
    (fun inp : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare inp).coordinator.selection.map
        (fun chosen => chosen.view)) hinputU.symm
  have hviewsCell :
      (ReferenceActivePhysicalStep.prepare
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection.map
        (fun chosen => chosen.view) = some sourceCell.selected.view := by
    simpa using congrArg (Option.map (fun chosen => chosen.view)) hselectedCell
  have hviewsCandidate :
      (ReferenceActivePhysicalStep.prepare
        (ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u)).coordinator.selection.map
        (fun chosen => chosen.view) = some selectedU.view := by
    simpa using congrArg (Option.map (fun chosen => chosen.view)) hselectedU
  rw [hviewsCell, hviewsCandidate] at hviews
  have hview : sourceCell.selected.view = selectedU.view := Option.some.inj hviews
  have hviewU : selectedU.view = {
      payload := r.payload
      pendingAtChoice := d.startResult.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
      complementWeights :=
        (ReferenceActivePhysicalStep.liveRegistersAt r candidate.time).complementWeights } := rfl
  have hphysical : markerE z =
      ReferenceContinuingRecordingFastPair.candidatePhysicalMarker
        initial source0.1.2 q rewards s n hspan hmode r.payload true u := by
    rw [ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker_eq_control]
    unfold ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
    rw [ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty_payload_eq
      rate rewards C_star C_h q t s hs control0 x r owned base d hsStart c arm hcoord0]
    simpa [candidate, initial, source0,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitial,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceSplit,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceInitialMode,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentCount,
      ReferenceFirstLiveRecordingReadoutMeasurability.retainedSourceCurrentSpan] using
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourcePhysicalMarker_eq_candidatePhysicalMarker
        source u r.payload true)
  have hmap := congrArg Prod.fst (hpair u)
  simp only [ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair,
    FastRewardSliceLaw.liveRecordingFastPair] at hmap
  have hslice :
      ((ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input.row.2
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).input.time).1 = u.1 := by
    have h := congrArg (fun inp : ReferenceActivePhysicalStep.RoundInput p rate =>
      (inp.row.2 inp.time).1) hinputU.symm
    simpa [ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
      ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using h
  have hstates : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
      sourceCell.states = states := by
    intro hdata
    have hordinary :=
      ReferenceContinuingLiveSlicePreparation.data_preparation_at_control
        candidate states memories ho u hdata
    have hordinaryOriginal : ∀ i,
        ((ReferenceActivePhysicalStep.prepare
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val).input).followers.followers i).configuration =
          .ordinary (states i) (memories i) := by
      intro i
      have hprep :
          ((ReferenceActivePhysicalStep.prepare
            (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
              rate rewards C_star C_h q t s hs control0 z.val).input).followers.followers i).configuration =
          ((ReferenceActivePhysicalStep.prepare
            (ReferenceContinuingLiveSlicePreparation.inputAtControl candidate u)).followers.followers i).configuration :=
        congrArg (fun inp : ReferenceActivePhysicalStep.RoundInput p rate =>
          ((ReferenceActivePhysicalStep.prepare inp).followers.followers i).configuration) hinputU.symm
      exact hprep.trans (hordinary i)
    funext i
    have h := (sourceCell.ordinary i).symm.trans (hordinaryOriginal i)
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj h).1
  have hsourceArm : ReferenceFirstWindowNumericalStream.sourceArm
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val)
      sourceCell.selected.view.payload sourceCell.selected.view.pendingAtChoice
      sourceCell.states sourceCell.selected.view.complementWeights
      sourceCell.selected.view.cutoff sourceCell.choiceInputsValid =
      SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment
        (ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
          r owned base candidate.time d states)) true rate.eta.val rate.eta.property
        rate.sourceCap r.payload.anchor
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights r candidate.time)
        r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r candidate.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm_u.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r candidate.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm_u.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r candidate.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          arm_u.choiceInputsValid) u.1 := by
    let view₂ : ReferenceDownReception.ChoiceTimeView p rate.eta := {
      payload := r.payload
      pendingAtChoice := d.startResult.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
      complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r candidate.time).complementWeights }
    have hfull : sourceCell.selected.view = view₂ := by
      calc
        sourceCell.selected.view = selectedU.view := hview
        _ = view₂ := hviewU
    have hcongr := sourceArm_congr_view rate
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val)
      sourceCell.selected.view view₂ sourceCell.states sourceCell.choiceInputsValid hfull
    have htargetWeights : ReferenceFirstWindowNumericalStream.sourceWeights view₂.payload
        view₂.complementWeights =
        ReferenceContinuingLiveSlicePreparation.liveSliceWeights r candidate.time := by
      funext j
      by_cases hj : j ∈ r.payload.slowSet.1
      · simp [view₂, ReferenceFirstWindowNumericalStream.sourceWeights,
          ReferenceContinuingLiveSlicePreparation.liveSliceWeights,
          ReferenceActivePhysicalStep.liveRegistersAt, hj]
      · simp [view₂, ReferenceFirstWindowNumericalStream.sourceWeights,
          ReferenceContinuingLiveSlicePreparation.liveSliceWeights,
          ReferenceActivePhysicalStep.liveRegistersAt, hj]
    rw [hcongr]
    by_cases hdata : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot
    · rw [hstates hdata]
      simp [ReferenceFirstWindowNumericalStream.sourceArm,
        ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot,
        SnapshotRecordingKernel.recordingMap, view₂, htargetWeights, hslice, hdata]
      rfl
    · simp [ReferenceFirstWindowNumericalStream.sourceArm,
        SnapshotRecordingKernel.recordingMap, hslice, hdata]
  exact hphysical.trans (hmap.trans hsourceArm.symm)

/-- The canonical indexed queue input is the current original record's
actual source cell. Its selection and recorder readouts are inherited from
the original PREPARE and the actual first-live cell producer. -/
theorem cell_actual_facts (z : Ze) :
    (cell rate rewards C_star C_h q t s hs control0 z).enabled = true ∧
    (cell rate rewards C_star C_h q t s hs control0 z).reward =
      (fun j : Fin p.K => rho rate rewards C_star C_h q t s hs control0 j) ∧
    (cell rate rewards C_star C_h q t s hs control0 z).rate =
      (fun j : Fin p.K => xiE (xofE z) j) ∧
    (cell rate rewards C_star C_h q t s hs control0 z).recordedArm = markerE z ∧
    (∀ j : Fin p.K,
      RecordedQueueRun.quantizedArrival queue
        (cell rate rewards C_star C_h q t s hs control0 z) j =
        if markerE z = some j then
          Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
            xiE (xofE z) j)
        else 0) ∧
    ∃ actualRecord : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      actualRecord = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val ∧
    ∃ sourceCell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell actualRecord,
      sourceCell.input = cell rate rewards C_star C_h q t s hs control0 z ∧
      actualRecord.output.preparation.coordinator.selection = some sourceCell.selected := by
  classical
  let window := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val.val rewards
    C_star C_h z.val.property.2.1 (n + 1) (actualSpan rate rewards C_star C_h q t s hs control0 z)
  let hidx := (currentOriginalWindowIndex rate rewards C_star C_h q t s hs control0 z).choose
  let index : Fin window.length := ⟨n, hidx⟩
  let record := window[n]'hidx
  let sourceCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val.val
    rewards C_star C_h z.val.property.2.1 (n + 1)
    (actualSpan rate rewards C_star C_h q t s hs control0 z) index
  have hrecord : record = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val := by
    exact (currentOriginalWindowIndex rate rewards C_star C_h q t s hs control0 z).choose_spec
  have hrecordInput := congrArg
    (fun rr : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => rr.input)
    hrecord
  have hcell : cell rate rewards C_star C_h q t s hs control0 z = sourceCell.input := by
    dsimp only [cell, actualCells, sourceCell, index, window]
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get rate z.val.val rewards
      C_star C_h z.val.property.2.1 (n + 1)
      (actualSpan rate rewards C_star C_h q t s hs control0 z)
      ⟨n, hidx⟩
  have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
    rate z.val.val rewards C_star C_h z.val.property.2.1 (n + 1)
    (actualSpan rate rewards C_star C_h q t s hs control0 z) index
  dsimp only at hfacts
  rcases hfacts with ⟨_hrows, _hselected, hrewards, _htime, henabled, hreward,
    hrate, harm, harr⟩
  change record.input.rewards = rewards at hrewards
  have hrecordRewards : record.input.rewards = rewards := hrewards
  have hrecordTime : record.input.time = t := by
    apply Fin.ext
    calc
      record.input.time.val =
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val).input.time.val :=
        congrArg (fun inp : ReferenceActivePhysicalStep.RoundInput p rate => inp.time.val)
          hrecordInput
      _ = t.val := congrArg Fin.val
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time
          rate rewards C_star C_h q t s hs control0 z.val)
  have hpayload : sourceCell.selected.view.payload =
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs
        control0 (xofE z)).view.payload := by
    have hselection := ReferenceFirstLiveEmptyPendingMarkerLaw.original_selection_data
      rate rewards C_star C_h q t s hs control0 z
    have hselectionBridge := congrArg
      (fun inp : ReferenceActivePhysicalStep.RoundInput p rate =>
        (ReferenceActivePhysicalStep.prepare inp).coordinator.selection.map
          (fun selected => (selected.view.payload, selected.started))) hrecordInput.symm
    have hselectionRecord :
        ((ReferenceActivePhysicalStep.prepare record.input).coordinator.selection).map
          (fun selected => (selected.view.payload, selected.started)) =
        some (sourceCell.selected.view.payload, sourceCell.selected.started) := by
      have hsel :
          (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
            some sourceCell.selected := by
        have hsel' := sourceCell.selection_actual
        rw [record.output_eq] at hsel'
        change (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
          some sourceCell.selected at hsel'
        exact hsel'
      simpa only [Option.map_some] using
        congrArg (Option.map (fun selected => (selected.view.payload, selected.started))) hsel
    have hpair :
        some ((ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs
          control0 (xofE z)).view.payload,
          (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs
            control0 (xofE z)).started) =
        some (sourceCell.selected.view.payload, sourceCell.selected.started) := by
      calc
        _ = ((ReferenceActivePhysicalStep.prepare
            (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
              rate rewards C_star C_h q t s hs control0 z.val).input).coordinator.selection).map
              (fun selected => (selected.view.payload, selected.started)) := hselection.symm
        _ = ((ReferenceActivePhysicalStep.prepare record.input).coordinator.selection).map
              (fun selected => (selected.view.payload, selected.started)) := hselectionBridge
        _ = _ := hselectionRecord
    exact congrArg Prod.fst (Option.some.inj hpair).symm
  have hrateXi : sourceCell.selected.view.payload.rate =
      (fun j : Fin p.K => xiE (xofE z) j) := by
    funext j
    change sourceCell.selected.view.payload.rate j =
      CanonicalRecordingRates.xi p rate.eta.val
        (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs
          control0 (xofE z)).view.payload.anchor j
    rw [hpayload]
    rfl
  have hreward' : sourceCell.input.reward =
      (fun j : Fin p.K => rho rate rewards C_star C_h q t s hs control0 j) := by
    rw [hrecordRewards, hrecordTime] at hreward
    simpa [rho] using hreward
  have hmarker := actualMarker_eq_cellSourceArm rate rewards C_star C_h q t s hs control0
    z sourceCell hrecord
  have hrecorded : sourceCell.input.recordedArm = markerE z :=
    harm.trans hmarker.symm
  constructor
  · rw [hcell]
    exact henabled
  constructor
  · rw [hcell]
    exact hreward'
  constructor
  · rw [hcell, hrate]
    exact hrateXi
  constructor
  · rw [hcell]
    exact hrecorded
  constructor
  · intro j
    have harr' := harr j
    rw [hrecordRewards, hrecordTime] at harr'
    rw [hcell, harr', hmarker.symm, hrateXi]
    simp [rho]
  · exact ⟨record, hrecord, sourceCell, hcell.symm, sourceCell.selection_actual⟩

/-- The indexed cell uses the ORIGINAL PREPARE selection getter, whose payload
and entire start-result transport are already proved by the marker module. -/
theorem cell_original_selection (z : Ze) :
    ∃ sourceCell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val),
      sourceCell.input = cell rate rewards C_star C_h q t s hs control0 z ∧
      sourceCell.selected = ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty
        rate rewards C_star C_h q t s hs control0 z := by
  obtain ⟨record, rfl, sourceCell, hcell, hsel⟩ :=
    (cell_actual_facts rate rewards C_star C_h q t s hs control0 z).2.2.2.2.2
  refine ⟨sourceCell, hcell, ?_⟩
  have hget := Option.some_get
    (ReferenceFirstLiveEmptyPendingMarkerLaw.original_selection_present
      rate rewards C_star C_h q t s hs control0 z)
  exact Option.some.inj (hsel.symm.trans hget.symm)

theorem map_xofEmpty : (muE).map xofE = nuE := by
  change (muE).map (Prod.fst ∘
    (ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
      rate rewards C_star C_h q t s hs control0)) = nuE
  rw [← Measure.map_map measurable_fst
      (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
        rate rewards C_star C_h q t s hs control0),
    ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_product,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The actual empty-pending arm rate is positive and dominates beta. -/
theorem xi_bounds (x : Xe) (j : Fin p.K) :
    0 < xiE x j ∧ beta ≤ xiE x j := by
  change 0 < CanonicalRecordingRates.xi p rate.eta.val
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
        rate rewards C_star C_h q t s hs control0 x).view.payload.anchor j ∧
    CanonicalRecordingRates.beta p rate.eta.val ≤ CanonicalRecordingRates.xi p rate.eta.val
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty
        rate rewards C_star C_h q t s hs control0 x).view.payload.anchor j
  exact ⟨CanonicalRecordingRates.xi_pos p rate.eta.property _ _,
    CanonicalRecordingRates.beta_le_xi p rate.eta.property _ _⟩

theorem rho_bounds (j : Fin p.K) : 0 ≤ rho rate rewards C_star C_h q t s hs control0 j ∧
    rho rate rewards C_star C_h q t s hs control0 j ≤ 1 := by
  have hD : 0 < (ConstructorDimensions.D p : ℝ) :=
    Nat.cast_pos.mpr (ConstructorDimensions.D_pos p)
  have hreward0 : 0 ≤ ((rewards t j).val : ℝ) := Nat.cast_nonneg _
  have hrewardD : ((rewards t j).val : ℝ) ≤ (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ (rewards t j).isLt
  constructor
  · exact div_nonneg hreward0 hD.le
  · unfold rho
    exact (div_le_one hD).2 hrewardD

private theorem v_eq_quantizedValue (x : Xe) (j : Fin p.K) :
    v rate rewards C_star C_h q t s hs control0 x j =
      QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p) rate.eta.val
        (xiE x j) (rho rate rewards C_star C_h q t s hs control0 j) := by
  have harg : (rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
      xiE x j = ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        rho rate rewards C_star C_h q t s hs control0 j) / xiE x j := by
    rw [rate.n_scale]
    ring
  unfold v QuantizedRecordingMoments.quantizedValue QuantizedRecordingMoments.quantizedIndex
  rw [harg]

theorem v_bounds (x : Xe) (j : Fin p.K) :
    0 ≤ v rate rewards C_star C_h q t s hs control0 x j ∧
    v rate rewards C_star C_h q t s hs control0 x j ≤ 1 / beta := by
  have hxi := xi_bounds rate rewards C_star C_h q t s hs control0 x j
  have hrho := rho_bounds rate rewards C_star C_h q t s hs control0 j
  have hq0 := QuantizedRecordingMoments.quantizedValue_nonneg
    (ConstructorDimensions.D p) rate.eta.val (xiE x j)
    (rho rate rewards C_star C_h q t s hs control0 j) rate.eta.property
  have hqle := QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
    (ConstructorDimensions.D p) rate.eta.val (xiE x j)
    (rho rate rewards C_star C_h q t s hs control0 j) beta
    (ConstructorDimensions.D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
    (CanonicalRecordingRates.beta_pos p rate.eta.property) hxi.2
  rw [v_eq_quantizedValue rate rewards C_star C_h q t s hs control0 x j]
  exact ⟨hq0, hqle⟩

/-- The actual first-moment coefficient differs from rho by less than one
quantization step and never exceeds rho. -/
theorem xi_mul_v_bounds (x : Xe) (j : Fin p.K) :
    rho rate rewards C_star C_h q t s hs control0 j - xiE x j / scale ≤
        xiE x j * v rate rewards C_star C_h q t s hs control0 x j ∧
    0 ≤ xiE x j * v rate rewards C_star C_h q t s hs control0 x j ∧
    xiE x j * v rate rewards C_star C_h q t s hs control0 x j ≤
        rho rate rewards C_star C_h q t s hs control0 j ∧
    rho rate rewards C_star C_h q t s hs control0 j ≤ 1 := by
  have hxi := xi_bounds rate rewards C_star C_h q t s hs control0 x j
  have hrho := rho_bounds rate rewards C_star C_h q t s hs control0 j
  have hlow := QuantizedRecordingMoments.quantizedValue_roundingError
    (ConstructorDimensions.D p) rate.eta.val (xiE x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (ConstructorDimensions.D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
  have hup := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (ConstructorDimensions.D p) rate.eta.val (xiE x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (ConstructorDimensions.D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
  have hlow' := hlow
  have hup' := hup
  rw [← v_eq_quantizedValue rate rewards C_star C_h q t s hs control0 x j] at hlow' hup'
  exact ⟨hlow', mul_nonneg hxi.1.le
    (v_bounds rate rewards C_star C_h q t s hs control0 x j).1, hup', hrho.2⟩

/-- The correct square coefficient is `xi * v^2`; its envelope is
`rho^2 / xi`, then `1 / xi`, then `1 / beta`. -/
theorem xi_mul_v_sq_bounds (x : Xe) (j : Fin p.K) :
    0 ≤ xiE x j * (v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∧
    xiE x j * (v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ≤
      (rho rate rewards C_star C_h q t s hs control0 j) ^ 2 / xiE x j ∧
    (rho rate rewards C_star C_h q t s hs control0 j) ^ 2 / xiE x j ≤ 1 / xiE x j ∧
    1 / xiE x j ≤ 1 / beta := by
  have hxi := xi_bounds rate rewards C_star C_h q t s hs control0 x j
  have hrho := rho_bounds rate rewards C_star C_h q t s hs control0 j
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (ConstructorDimensions.D p) rate.eta.val (xiE x j)
    (rho rate rewards C_star C_h q t s hs control0 j)
    (ConstructorDimensions.D_pos p) rate.eta.property hxi.1 ⟨hrho.1, hrho.2⟩
  have hrhoSq : (rho rate rewards C_star C_h q t s hs control0 j) ^ 2 ≤ 1 := by
    nlinarith [hrho.1, hrho.2]
  have hratio := div_le_div_of_nonneg_right hrhoSq hxi.1.le
  have hbeta := one_div_le_one_div_of_le
    (CanonicalRecordingRates.beta_pos p rate.eta.property) hxi.2
  rw [← v_eq_quantizedValue rate rewards C_star C_h q t s hs control0 x j] at hsecond
  exact ⟨mul_nonneg hxi.1.le (sq_nonneg _), hsecond, hratio, hbeta⟩

theorem a_eq_actual_marker (z : Ze) (j : Fin p.K) :
    a rate rewards C_star C_h q t s hs control0 z j =
      if markerE z = some j then v rate rewards C_star C_h q t s hs control0
        (xofE z) j else 0 := by
  have h := (cell_actual_facts rate rewards C_star C_h q t s hs control0 z).2.2.2.2.1 j
  unfold a
  rw [h]
  by_cases hm : markerE z = some j <;> simp [hm, v]

theorem measurable_v (j : Fin p.K) :
    Measurable (fun x : Xe => v rate rewards C_star C_h q t s hs control0 x j) := by
  have hxi := ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty
    rate rewards C_star C_h q t s hs control0 j
  have harg : Measurable (fun x : Xe =>
      (rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j / xiE x j) :=
    (measurable_const.mul measurable_const).div hxi
  have hfloor := Nat.measurable_floor.comp harg
  have hcast : Measurable (fun x : Xe =>
      (Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
        xiE x j) : ℝ)) := (measurable_of_countable _).comp hfloor
  change Measurable (fun x : Xe =>
    (Nat.floor ((rate.n : ℝ) * rho rate rewards C_star C_h q t s hs control0 j /
      xiE x j) : ℝ) / scale)
  exact hcast.div_const _

theorem integrable_v (j : Fin p.K) :
    Integrable (fun x : Xe => v rate rewards C_star C_h q t s hs control0 x j) nuE := by
  apply Integrable.of_bound (measurable_v rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable (1 / beta)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (v_bounds rate rewards C_star C_h q t s hs control0 x j).1]
  exact (v_bounds rate rewards C_star C_h q t s hs control0 x j).2

theorem measurable_a (j : Fin p.K) :
    Measurable (fun z : Ze => a rate rewards C_star C_h q t s hs control0 z j) := by
  rw [show (fun z : Ze => a rate rewards C_star C_h q t s hs control0 z j) =
      (fun z => if markerE z = some j then
        v rate rewards C_star C_h q t s hs control0 (xofE z) j else 0) from by
        funext z
        exact a_eq_actual_marker rate rewards C_star C_h q t s hs control0 z j]
  exact Measurable.ite
    (measurableSet_eq_fun
      (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_actualEmptyMarker
        rate rewards C_star C_h q t s hs control0) measurable_const)
    ((measurable_v rate rewards C_star C_h q t s hs control0 j).comp
      (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
        rate rewards C_star C_h q t s hs control0)) measurable_const

theorem a_bounds (z : Ze) (j : Fin p.K) :
    0 ≤ a rate rewards C_star C_h q t s hs control0 z j ∧
      a rate rewards C_star C_h q t s hs control0 z j ≤ 1 / beta := by
  rw [a_eq_actual_marker rate rewards C_star C_h q t s hs control0 z j]
  by_cases hm : markerE z = some j
  · simp only [ite_eq_left hm]
    exact v_bounds rate rewards C_star C_h q t s hs control0 (xofE z) j
  · constructor
    · simp [hm]
    · simpa [hm] using div_nonneg (by norm_num : (0 : ℝ) ≤ 1)
        (CanonicalRecordingRates.beta_pos p rate.eta.property).le

theorem measurable_a_sq (j : Fin p.K) :
    Measurable (fun z : Ze => (a rate rewards C_star C_h q t s hs control0 z j) ^ 2) :=
  (measurable_a rate rewards C_star C_h q t s hs control0 j).pow_const 2

/-- Uniform arrival domination gives integrability under the unnormalized
inherited finite source measure, including zero mass. -/
theorem integrable_a (j : Fin p.K) :
    Integrable (fun z : Ze => a rate rewards C_star C_h q t s hs control0 z j) muE := by
  apply Integrable.of_bound (measurable_a rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    (1 / beta)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (a_bounds rate rewards C_star C_h q t s hs control0 z j).1]
  exact (a_bounds rate rewards C_star C_h q t s hs control0 z j).2

theorem integrable_a_sq (j : Fin p.K) :
    Integrable (fun z : Ze => (a rate rewards C_star C_h q t s hs control0 z j) ^ 2) muE := by
  have hm := measurable_a_sq rate rewards C_star C_h q t s hs control0 j
  apply Integrable.of_bound hm.aestronglyMeasurable ((1 / beta) ^ 2)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := a_bounds rate rewards C_star C_h q t s hs control0 z j
  have hb0 : 0 ≤ 1 / beta :=
    (div_pos (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
  nlinarith

theorem measurable_xi_mul_v (j : Fin p.K) :
    Measurable (fun x : Xe => xiE x j * v rate rewards C_star C_h q t s hs control0 x j) :=
  (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty
    rate rewards C_star C_h q t s hs control0 j).mul
    (measurable_v rate rewards C_star C_h q t s hs control0 j)

theorem measurable_xi_mul_v_sq (j : Fin p.K) :
    Measurable (fun x : Xe => xiE x j * (v rate rewards C_star C_h q t s hs control0 x j) ^ 2) :=
  (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xiEmpty
    rate rewards C_star C_h q t s hs control0 j).mul
    ((measurable_v rate rewards C_star C_h q t s hs control0 j).pow_const 2)

theorem integrable_xi_mul_v (j : Fin p.K) :
    Integrable (fun x : Xe => xiE x j * v rate rewards C_star C_h q t s hs control0 x j) nuE := by
  apply Integrable.of_bound (measurable_xi_mul_v rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable 1
  filter_upwards [] with x
  have hp := xi_mul_v_bounds rate rewards C_star C_h q t s hs control0 x j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (xi_bounds rate rewards C_star C_h q t s hs control0 x j).1.le
    (v_bounds rate rewards C_star C_h q t s hs control0 x j).1)]
  exact hp.2.2.1.trans hp.2.2.2

theorem integrable_xi_mul_v_sq (j : Fin p.K) :
    Integrable (fun x : Xe => xiE x j * (v rate rewards C_star C_h q t s hs control0 x j) ^ 2) nuE := by
  apply Integrable.of_bound (measurable_xi_mul_v_sq rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable
    (1 / beta)
  filter_upwards [] with x
  have hp := xi_mul_v_sq_bounds rate rewards C_star C_h q t s hs control0 x j
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2.1.trans (hp.2.2.1.trans hp.2.2.2)

private theorem marker_weight_cell_integral
    (Aset : Set Xe) (hAset : MeasurableSet Aset) (j : Fin p.K)
    (w : Xe → ℝ) (hw : Measurable w) (B : ℝ) (hB : 0 ≤ B)
    (hw_bound : ∀ x, ‖w x‖ ≤ B) :
    (∫ z in {z : Ze | xofE z ∈ Aset},
      (if markerE z = some j then w (xofE z) else 0) ∂muE) =
      ∫ x in Aset, xiE x j * w x ∂nuE := by
  classical
  let split := ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit
    rate rewards C_star C_h q t s hs control0
  let sourceSet : Set Ze := {z | xofE z ∈ Aset}
  let cellControl : Set (Xe × TimeControl p) := Aset ×ˢ Set.univ
  let H : Xe × TimeControl p → ℝ := cellControl.indicator (fun y =>
    if ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
      rate rewards C_star C_h q t s hs control0 y = some j then w y.1 else 0)
  have hsourceSet : MeasurableSet sourceSet :=
    hAset.preimage (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
      rate rewards C_star C_h q t s hs control0)
  have hmarkerEvent : MeasurableSet {y : Xe × TimeControl p |
      ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
        rate rewards C_star C_h q t s hs control0 y = some j} :=
    measurableSet_eq_fun
      ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_currentEmptyMarker measurable_const
  have hconditional : Measurable (fun y : Xe × TimeControl p =>
      if ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
        rate rewards C_star C_h q t s hs control0 y = some j then w y.1 else 0) :=
    Measurable.ite hmarkerEvent (hw.comp measurable_fst) measurable_const
  have hcellControl : MeasurableSet cellControl := hAset.prod MeasurableSet.univ
  have hH : Measurable H := hconditional.indicator hcellControl
  have hHbound : ∀ y, ‖H y‖ ≤ B := by
    intro y
    by_cases hy : y ∈ cellControl
    · by_cases hm : ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
          rate rewards C_star C_h q t s hs control0 y = some j
      · simpa [H, hy, hm] using hw_bound y.1
      · simp [H, hy, hm, hB]
    · simp [H, hy, hB]
  have hHint : Integrable H ((nuE).prod (timeControlLaw p)) :=
    Integrable.of_bound hH.aestronglyMeasurable B
      (Filter.Eventually.of_forall hHbound)
  have hsplit : Measurable split :=
    ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_emptySourceSplit
      rate rewards C_star C_h q t s hs control0
  have hcellPreimage (z : Ze) : split z ∈ cellControl ↔ z ∈ sourceSet := by
    simp [cellControl, sourceSet, split,
      ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit]
  have hsourceIndicator : sourceSet.indicator
      (fun z => if markerE z = some j then w (xofE z) else 0) = H ∘ split := by
    funext z
    by_cases hz : z ∈ sourceSet
    · have hspl : split z ∈ cellControl := (hcellPreimage z).2 hz
      change sourceSet.indicator _ z = H (split z)
      rw [Set.indicator_of_mem hz]
      unfold H
      rw [Set.indicator_of_mem hspl]
      simp [split, ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit,
        ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker_eq_control]
    · have hspl : split z ∉ cellControl := fun h => hz ((hcellPreimage z).1 h)
      change sourceSet.indicator _ z = H (split z)
      rw [Set.indicator_of_notMem hz]
      unfold H
      rw [Set.indicator_of_notMem hspl]
  have hfiber : ∀ x : Xe, (∫ u, H (x, u) ∂timeControlLaw p) =
      Aset.indicator (fun x => xiE x j * w x) x := by
    intro x
    by_cases hx : x ∈ Aset
    · let Eset : Set (TimeControl p) := {u |
        ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
          rate rewards C_star C_h q t s hs control0 (x, u) = some j}
      have hEset : MeasurableSet Eset := by
        exact measurableSet_eq_fun
          (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_currentEmptyMarker.comp
            (measurable_const.prodMk measurable_id)) measurable_const
      have hfun : (fun u => H (x, u)) = Eset.indicator (fun _ => w x) := by
        funext u
        by_cases hu : ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker
            rate rewards C_star C_h q t s hs control0 (x, u) = some j
        · simp [H, cellControl, hx, Eset, hu]
        · simp [H, cellControl, hx, Eset, hu]
      rw [hfun, integral_indicator_const, smul_eq_mul]
      · have hmass := (ReferenceFirstLiveEmptyPendingMarkerLaw.currentEmptyMarker_masses
            rate rewards C_star C_h q t s hs control0 x).1 j
        change timeControlLaw p Eset = ENNReal.ofReal (xiE x j) at hmass
        rw [measureReal_def, hmass,
          ENNReal.toReal_ofReal (xi_bounds rate rewards C_star C_h q t s hs control0 x j).1.le]
        simp [Set.indicator_of_mem hx]
      · exact hEset
    · have hfun : (fun u => H (x, u)) = fun _ => (0 : ℝ) := by
        funext u
        simp [H, cellControl, hx]
      rw [hfun]
      simp [Set.indicator_of_notMem hx]
  calc
    _ = ∫ z, sourceSet.indicator
        (fun z => if markerE z = some j then w (xofE z) else 0) z ∂muE := by
      rw [← integral_indicator hsourceSet]
    _ = ∫ z, H (split z) ∂muE := by
      rw [hsourceIndicator]
      simp only [Function.comp_apply]
    _ = ∫ y, H y ∂((muE).map split) :=
      (MeasureTheory.integral_map hsplit.aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ y, H y ∂((nuE).prod (timeControlLaw p)) := by
      rw [ReferenceFirstLiveEmptyPendingMarkerLaw.emptySourceSplit_product
        rate rewards C_star C_h q t s hs control0]
    _ = ∫ x, ∫ u, H (x, u) ∂timeControlLaw p ∂nuE := integral_prod H hHint
    _ = ∫ x, Aset.indicator (fun x => xiE x j * w x) x ∂nuE := by
      congr 1
      funext x
      exact hfiber x
    _ = ∫ x in Aset, xiE x j * w x ∂nuE := by rw [integral_indicator hAset]

theorem source_firstMoment_cell_integral (Aset : Set Xe)
    (hAset : MeasurableSet Aset) (j : Fin p.K) :
    (∫ z in {z : Ze | xofE z ∈ Aset}, a rate rewards C_star C_h q t s hs control0 z j ∂muE) =
      ∫ x in Aset, xiE x j * v rate rewards C_star C_h q t s hs control0 x j ∂nuE := by
  have hset : MeasurableSet {z : Ze | xofE z ∈ Aset} :=
    hAset.preimage (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
      rate rewards C_star C_h q t s hs control0)
  calc
    _ = ∫ z in {z : Ze | xofE z ∈ Aset},
        (if markerE z = some j then v rate rewards C_star C_h q t s hs control0 (xofE z) j
          else 0) ∂muE := by
      apply setIntegral_congr_fun hset
      intro z _
      exact a_eq_actual_marker rate rewards C_star C_h q t s hs control0 z j
    _ = _ := marker_weight_cell_integral rate rewards C_star C_h q t s hs control0
      Aset hAset j (fun x => v rate rewards C_star C_h q t s hs control0 x j)
      (measurable_v rate rewards C_star C_h q t s hs control0 j) (1 / beta)
      (div_nonneg (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property).le)
      (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg
          (v_bounds rate rewards C_star C_h q t s hs control0 x j).1]
        exact (v_bounds rate rewards C_star C_h q t s hs control0 x j).2)

theorem source_secondMoment_cell_integral (Aset : Set Xe)
    (hAset : MeasurableSet Aset) (j : Fin p.K) :
    (∫ z in {z : Ze | xofE z ∈ Aset},
      (a rate rewards C_star C_h q t s hs control0 z j) ^ 2 ∂muE) =
      ∫ x in Aset, xiE x j * (v rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∂nuE := by
  have hset : MeasurableSet {z : Ze | xofE z ∈ Aset} :=
    hAset.preimage (ReferenceFirstLiveEmptyPendingMarkerLaw.measurable_xofEmpty
      rate rewards C_star C_h q t s hs control0)
  calc
    _ = ∫ z in {z : Ze | xofE z ∈ Aset},
        (if markerE z = some j then (v rate rewards C_star C_h q t s hs control0
          (xofE z) j) ^ 2 else 0) ∂muE := by
      apply setIntegral_congr_fun hset
      intro z _
      change (a rate rewards C_star C_h q t s hs control0 z j) ^ 2 = _
      rw [a_eq_actual_marker rate rewards C_star C_h q t s hs control0 z j]
      by_cases hm : markerE z = some j <;> simp [hm]
    _ = _ := marker_weight_cell_integral rate rewards C_star C_h q t s hs control0
      Aset hAset j (fun x => (v rate rewards C_star C_h q t s hs control0 x j) ^ 2)
      ((measurable_v rate rewards C_star C_h q t s hs control0 j).pow_const 2)
      ((1 / beta) ^ 2) (sq_nonneg _)
      (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hv := v_bounds rate rewards C_star C_h q t s hs control0 x j
        have hB : 0 ≤ 1 / beta :=
          (div_pos (by norm_num) (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
        nlinarith [sq_nonneg (1 / beta - v rate rewards C_star C_h q t s hs control0 x j)])

end Bandits.Support.ReferenceFirstLiveEmptyPendingSourceMoments
end
