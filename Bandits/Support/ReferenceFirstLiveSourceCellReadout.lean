/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveSourceSavedMoments

import Mathlib.Data.List.TakeWhile

/-!
# Actual chronological first-live source readout

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module identifies the current original-source record in its actual
first-live window and reads the existing numerical cell and saved arrival at
that same calendar coordinate. The source, whole reward table, private arrays,
initialization path, and physical run are unchanged. No conditional law or
manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceFirstLiveSourceCellReadout

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
  (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs)
local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0

private def liveCutoffTag
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) : Bool :=
  match out with
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
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
    (selected otherSelected : Fin (M p)) (time : Fin p.T)
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
      simpa only [ReferenceActivePhysicalStep.liveInput, ReferenceActivePhysicalStep.RoundInput.row,
        liveCutoffTag] using htag
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
    (selected : Fin (M p)) (rewards : RewardTable p)
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
      · exact hcontrols ⟨start + count, by omega⟩ (by dsimp; omega) (by dsimp; omega)

private theorem physicalRun_eq_of_initial_eq
    (initial initial' : ReferenceActivePhysicalStep.State p rate)
    (hinitial : initial = initial')
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : RewardTable p) (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart initial' start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run initial' rows selected rewards start count hspan hmode').records := by
  cases hinitial
  rfl

/-- The original current record occurs at the end of the actual first-live
window, and the current window is the entire `n + 1` physical run. -/
theorem source_current_window (z : Zplus) :
    let source := z.val.val
    let hc := z.val.property.2.1
    let hspan : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          ((t.val - s) + 1) ≤ p.T := by
      have helapsed : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
        simpa [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
      rw [helapsed]
      omega
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc (t.val - s + 1) hspan
    let W := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc (t.val - s + 1) hspan
    W = E.records ∧ W.length = t.val - s + 1 ∧
      ∃ hn : t.val - s < W.length,
        W[t.val - s]'hn = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val := by
  classical
  dsimp only
  let source := z.val.val
  let x := ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
    rate rewards C_star C_h q t s hs control0 z.val
  let n := t.val - s
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let hc := z.val.property.2.1
  let elapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
    simpa [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using z.val.property.2.2
  let hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        (n + 1) ≤ p.T := by
    rw [elapsed]
    dsimp [n]
    omega
  have hspanS : s + (n + 1) ≤ p.T := by
    rw [← elapsed]
    exact hspan
  let hc0 := (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
    rate rewards C_star C_h q t s hs control0 x).1
  let elapsed0 := (ReferenceFirstLiveRecordingSourceBranch.retainedSourceFacts
    rate rewards C_star C_h q t s hs control0 x).2
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source0
    rewards C_star C_h hc0
  let hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    have hseed := (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate source0 rewards C_star C_h hc0).activeAtStart
    change ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate source0 rewards C_star C_h hc0) s
    rw [← elapsed0]
    exact hseed
  let prefix0 := ReferenceActivePhysicalHorizon.run initial source0.1.2 q rewards s n
    (by omega) hmode
  let sourcePrefix := ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s n
    (by omega) hmode
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q := by
    exact (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
      p source).trans z.val.property.1
  have hretained : x.val =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 := by
    exact ReferenceTotalSourceDisintegration.sourceRetainedInput_val
      rate rewards C_star C_h t control0 (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex
        q t s hs) z.val
  have hsource0 : source0 = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t source control0 := by
    dsimp [source0, ReferenceGeneratedActivePrefixFactor.splitSource]
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
    (Or.inl ⟨hc, by rw [elapsed]; omega⟩)
  have hlaunchEq : ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc =
      initial := by
    have hcorrected :
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate source0 rewards C_star C_h := by
      rcases hinit with ⟨_, houtput, _, _, hordinary, _, _, _, _⟩
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
            _ = some (Option.get _ hsome0) :=
              (Option.coe_get hsome0).symm),
        funext (fun i => congrArg (fun state =>
          DeclaredFollowerLocalRound.LocalConfiguration.ordinary state
            (ActiveFollowerLifecycle.initialMemory p))
          (hordinary (ActualReferenceInitializationBlock.refFollower i)))⟩
    have hleft := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hc
    have hright := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source0 rewards C_star C_h hc0
    exact Option.some.inj (hleft.symm.trans (hcorrected.trans hright))
  have hcontrols : ∀ j : Fin p.T, s ≤ j.val → j.val < s + n →
      (source0.1.2 q).2 j = (source.1.2 q).2 j := by
    intro j hj hjend
    have hjt : j.val < t.val := by dsimp [n] at hjend; omega
    rw [hsource0]
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p source).symm.trans hindex
    simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
      Function.update_of_ne (show j ≠ t from Fin.ne_of_val_ne (by omega))]
  have hbefore : ∀ j : Fin p.T, j.val < s →
      ((source0.1.2 q).2 j).1 ContinuousControlSlice.Label.prop =
        ((source.1.2 q).2 j).1 ContinuousControlSlice.Label.prop := by
    intro j hj
    have hjt : j.val < t.val := by omega
    have hsame : (source0.1.2 q).2 j = (source.1.2 q).2 j := by
      rw [hsource0]
      have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p source).symm.trans hindex
      simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
        Function.update_of_ne (show j ≠ t from by intro h; subst j; omega)]
    exact congrArg (fun u : TimeControl p => u.1 ContinuousControlSlice.Label.prop) hsame
  have hprefixEq := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
    initial source0.1.2 source.1.2 q rewards rewards s n (by omega) hmode
    hcontrols (fun _ _ _ => rfl) (fun _ => hbefore)
  have htags := run_cutoffTags_eq rate initial source0.1.2 source.1.2 q rewards s n
    (by omega) hmode hcontrols hbefore
  have hbaseRun :
      ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x =
      ReferenceActivePhysicalHorizon.run initial source0.1.2 q rewards s (n + 1)
        hspanS hmode := by
    have hselectedSplit : ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val) = q := by
      change ActualInitializationPhysicalStep.selectedRowIndex p source0 = q
      exact hselected0
    simp only [ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun,
      ReferenceFirstWindowNumericalStream.actualFirstLiveRun, elapsed0, hselectedSplit]
    rfl
  have hbaseTake :
      (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 x).records.take n = prefix0.records := by
    rw [hbaseRun, ReferenceActivePhysicalHorizon.run_successor_step]
    simp only [ReferenceActivePhysicalHorizon.foldRound]
    have hlen : prefix0.records.length = n := by
      exact ReferenceActivePhysicalHorizon.run_record_count initial source0.1.2 q rewards s n
        (by omega) hmode
    rw [List.take_append_of_le_length (by omega : n ≤ prefix0.records.length)]
    exact List.take_of_length_le (by rw [hlen])
  have hbaseAll : ∀ record ∈ prefix0.records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hrecord
    have h := z.property.2.1 record (by rw [hbaseTake]; exact hrecord)
    exact h
  have hsourceAll : ∀ record ∈ sourcePrefix.records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
    intro record hrecord
    have hmem : ReferenceCollectionPhaseHistory.cutoffChosen record.input ∈
        sourcePrefix.records.map (fun r => ReferenceCollectionPhaseHistory.cutoffChosen r.input) :=
      List.mem_map.mpr ⟨record, hrecord, rfl⟩
    rw [← htags] at hmem
    obtain ⟨record0, hrecord0, hcut⟩ := List.mem_map.mp hmem
    rw [← hcut]
    simpa [prefix0] using hbaseAll record0 hrecord0
  obtain ⟨states, memories, ho, r, owned, base, d, hsStart, c, arm, hcoord,
      henabled, hpending, hcontrolsAll, hdata, hfirst, hseed, haccepted,
      hS, hdelta, hbacklog, hlastDown, hunoccupied, hlocal, hvalid,
      hpairwise, htime, hdecoder, hmodeActual⟩ :=
    ReferenceFirstLiveRecordingSourceBranch.actual_continuing_recording_inputs
      rate rewards C_star C_h q t s hs control0 x z.property
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl
    rate rewards C_star C_h q t s hs z.val
  obtain ⟨c_u, arm_u, hcoord_u⟩ := hcontrolsAll u
  have hcontrolInput :
      ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (q := q) (t := t) (s := s) (hs := hs) (control0 := control0) x u =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input :=
    ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original
      rate rewards C_star C_h q t s hs control0 z.val
  have hcurrentCutoff :
      ReferenceCollectionPhaseHistory.cutoffChosen
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).input = false := by
    rw [← hcontrolInput]
    change ReferenceCollectionPhaseHistory.cutoffChosen
      (ReferenceContinuingLiveSlicePreparation.inputAtControl
        (ReferenceContinuingDataCandidateLogging.candidateInput initial source0.1.2 q rewards
          s n hspanS hmode) u) = false
    unfold ReferenceCollectionPhaseHistory.cutoffChosen
    rw [hcoord_u]
  have hcurInput :
      ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s hmode
        sourcePrefix ⟨s + n, by omega, by omega⟩ =
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input := by
    have hboundary :
        ReferenceTotalSourceDisintegration.sourceIncomingBoundary
          rate rewards C_star C_h t control0
            (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z.val =
        ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
          rate rewards C_star C_h q t s hs control0 x := by
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
    have hstate' := hprefixEq.1
    have hstateFinal : sourcePrefix.finalState =
        (ReferenceTotalSourceDisintegration.sourceIncomingBoundary
          rate rewards C_star C_h t control0
            (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs) z.val).state :=
      hstate'.symm.trans hstate
    let leftInput := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s
      hmode sourcePrefix ⟨s + n, by omega, by omega⟩
    let rightInput := (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val).input
    have hleftState : leftInput.state = rightInput.state := hstateFinal
    have hrows : leftInput.rows = rightInput.rows := rfl
    have hselected : leftInput.selected = rightInput.selected := by
      exact z.val.property.1.symm
    have htime : leftInput.time = rightInput.time := by
      rw [show leftInput.time = ⟨s + n, by omega⟩ by rfl,
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time]
      apply Fin.ext
      dsimp [n]
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
        (by omega) hmode).records = sourcePrefix.records ++
          [ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val] := by
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    simp only [ReferenceActivePhysicalHorizon.foldRound]
    have hlast :
        ({ input := ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s
              hmode sourcePrefix ⟨s + n, by omega, by omega⟩,
            output := ReferenceActivePhysicalStep.step
              (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2 q rewards s
                hmode sourcePrefix ⟨s + n, by omega, by omega⟩),
            output_eq := rfl } : ReferenceActivePhysicalHorizon.RoundRecord) =
          ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val := by
      exact congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
        (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
          ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))) hcurInput
    rw [hlast]
  have hsourceFull : ∀ record ∈ sourcePrefix.records ++
      [ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val],
      (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true := by
    intro record hrecord
    rcases List.mem_append.mp hrecord with hprefix | hlast
    · simp [hsourceAll record hprefix]
    · simp only [List.mem_singleton] at hlast
      rcases hlast with rfl
      simp [hcurrentCutoff]
  have hwindow :
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
            hspanS hmode).records =
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
            hspanS hmode).records := by
    rw [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, hsourceAppend]
    exact List.takeWhile_eq_self_iff.mpr hsourceFull
  have hrunRecords :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hc (n + 1) hspan).records =
      (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
        hspanS hmode).records := by
    dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveRun]
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p source).symm.trans hindex
    have hmodeSource : ReferenceActivePhysicalHorizon.allActiveAtStart
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc) s := by
      simpa only [elapsed] using
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate source rewards C_star C_h hc).activeAtStart
    simpa only [elapsed, hselected] using
      physicalRun_eq_of_initial_eq rate
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
        initial hlaunchEq source.1.2 q rewards s (n + 1) hspanS
        hmodeSource hmode
  let sourceRun := ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s
    (n + 1) hspanS hmode
  have hwindowRun :
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc (n + 1) hspan = sourceRun.records := by
    dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow, sourceRun]
    rw [hrunRecords, hwindow]
  have hprefixLen : sourcePrefix.records.length = n := by
    exact ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 q rewards s n
      (by omega) hmode
  have hfullIndex : n < sourceRun.records.length := by
      dsimp [sourceRun]
      rw [ReferenceActivePhysicalHorizon.run_record_count]
      omega
  have hcurrentOpt : sourceRun.records[n]? =
      some (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val) := by
    dsimp only [sourceRun]
    rw [hsourceAppend]
    simp [hprefixLen]
  have hcurrentAt : sourceRun.records[n]'hfullIndex =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val := by
    have h := hcurrentOpt
    rw [List.getElem?_eq_getElem hfullIndex] at h
    exact Option.some.inj h
  have hwindowLength :
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc (n + 1) hspan).length = n + 1 := by
    rw [hwindowRun]
    dsimp [sourceRun]
    exact ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 q rewards s
      (n + 1) hspanS hmode
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow]
    rw [hrunRecords, hwindow]
  · rw [show ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc (n + 1) hspan =
        (ReferenceActivePhysicalHorizon.run initial source.1.2 q rewards s (n + 1)
          hspanS hmode).records from ?_]
    · exact ReferenceActivePhysicalHorizon.run_record_count initial source.1.2 q rewards s
        (n + 1) hspanS hmode
    · dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow]
      rw [hrunRecords, hwindow]
  · refine ⟨?_, ?_⟩
    · rw [hwindowLength]
      omega
    · have hwindowOpt :
          (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
            rate source rewards C_star C_h hc (n + 1) hspan)[n]? =
            some (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
              rate rewards C_star C_h q t s hs control0 z.val) := by
        rw [hwindowRun]
        exact hcurrentOpt
      have h := hwindowOpt
      rw [List.getElem?_eq_getElem (by rw [hwindowLength]; omega)] at h
      exact Option.some.inj h

/-- The full calendar count through the current round. -/
def sourceCurrentCount : ℕ := t.val - s + 1

/-- Initialization elapsed time on the unchanged original source. -/
def sourceCurrentElapsed (z : Zplus) : ℕ :=
  ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val.val rewards C_star C_h rate)).completed

theorem source_current_elapsed_eq (z : Zplus) : sourceCurrentElapsed rate rewards C_star C_h
    q t s hs control0 z = s := by
  simpa [sourceCurrentElapsed, ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] using
    z.val.property.2.2

theorem source_current_span (z : Zplus) :
    sourceCurrentElapsed rate rewards C_star C_h q t s hs control0 z +
      sourceCurrentCount t s ≤ p.T := by
  rw [source_current_elapsed_eq]
  dsimp [sourceCurrentCount]
  omega

/-- N's existing first-live window on the unchanged original source. -/
def sourceCurrentWindow (z : Zplus) :=
  ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate z.val.val rewards C_star C_h
    z.val.property.2.1 (sourceCurrentCount t s)
    (source_current_span rate rewards C_star C_h q t s hs control0 z)

/-- The current calendar offset, certified to lie in the actual window. -/
noncomputable def sourceCurrentIndex (z : Zplus) :
    Fin (sourceCurrentWindow rate rewards C_star C_h q t s hs control0 z).length := by
  have hwindow := source_current_window rate rewards C_star C_h q t s hs control0 z
  have hlength : (sourceCurrentWindow rate rewards C_star C_h q t s hs control0 z).length =
      sourceCurrentCount t s := by
    simpa [sourceCurrentWindow, sourceCurrentCount] using hwindow.2.1
  exact ⟨t.val - s, by rw [hlength]; dsimp [sourceCurrentCount]; omega⟩

/-- The literal numerical input list on the original source and its full
first-live calendar window. -/
def cells (z : Zplus) : List (RecordedQueueRun.RoundInput p.K) :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
    z.val.property.2.1 (sourceCurrentCount t s)
    (source_current_span rate rewards C_star C_h q t s hs control0 z)

/-- The existing numerical cell at the proved current index of the original
first-live window. -/
noncomputable def cell (z : Zplus) :
    ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
      ((sourceCurrentWindow rate rewards C_star C_h q t s hs control0 z)[
        (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z).val]) :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt rate z.val.val rewards C_star C_h
    z.val.property.2.1 (sourceCurrentCount t s)
    (source_current_span rate rewards C_star C_h q t s hs control0 z)
    (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z)

/-- The current window has every original calendar record through `t`. -/
theorem source_current_window_length (z : Zplus) :
    (sourceCurrentWindow rate rewards C_star C_h q t s hs control0 z).length =
      sourceCurrentCount t s :=
  (source_current_window rate rewards C_star C_h q t s hs control0 z).2.1

/-- The selected index is the original calendar offset, not a filtered count. -/
theorem source_current_index_val (z : Zplus) :
    (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z).val = t.val - s := rfl

/-- The record at the proved index is the original source's physical step. -/
theorem source_current_record (z : Zplus) :
    (sourceCurrentWindow rate rewards C_star C_h q t s hs control0 z)[
      (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z).val] =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val := by
  obtain ⟨_, _, _, hrecord⟩ :=
    source_current_window rate rewards C_star C_h q t s hs control0 z
  exact hrecord

/-- The numerical input list has the same complete calendar length. -/
theorem cells_length (z : Zplus) :
    (cells rate rewards C_star C_h q t s hs control0 z).length = sourceCurrentCount t s := by
  exact (ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
    rate z.val.val rewards C_star C_h z.val.property.2.1 (sourceCurrentCount t s)
    (source_current_span rate rewards C_star C_h q t s hs control0 z)).trans
      (source_current_window_length rate rewards C_star C_h q t s hs control0 z)

/-- The proved current index selects precisely the existing actual cell input. -/
theorem cells_current (z : Zplus) :
    (cells rate rewards C_star C_h q t s hs control0 z)[t.val - s]'(by
      rw [cells_length]; dsimp [sourceCurrentCount]; omega) =
      (cell rate rewards C_star C_h q t s hs control0 z).input :=
  ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get rate z.val.val rewards C_star C_h
    z.val.property.2.1 (sourceCurrentCount t s)
    (source_current_span rate rewards C_star C_h q t s hs control0 z)
    (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z)

private theorem actualCell_selected_view
    {record1 record2 : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : record1 = record2)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record1)
    (selected : ReferenceActivePhysicalStep.Selection record2.input)
    (hselected : (ReferenceActivePhysicalStep.prepare record2.input).coordinator.selection =
      some selected) :
    c.selected.view = selected.view := by
  cases hrecord
  have hcellSelection : (ReferenceActivePhysicalStep.prepare record1.input).coordinator.selection =
      some c.selected := by
    simpa [record1.output_eq, ReferenceActivePhysicalStep.step] using c.selection_actual
  exact congrArg (fun chosen => chosen.view)
    (Option.some.inj (hcellSelection.symm.trans hselected))

/-- The numerical cell selects the same actual payload as the source readout. -/
theorem source_current_cell_payload (z : Zplus) :
    (cell rate rewards C_star C_h q t s hs control0 z).selected.view.payload =
      ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 z).1 := by
  obtain ⟨states, memories, r, owned, base, d, hsStart, continuation, arm,
      hcoord, hordinary, hpayload, hselectedRecord, hvalid, hsourceMarker⟩ :=
    ReferenceFirstLiveRecordingSourceCylinder.sourceMarker_eq_sourceArm
      rate rewards C_star C_h q t s hs control0 z
  obtain ⟨selected, hselected, hview, _⟩ := hselectedRecord
  have hviewCell := actualCell_selected_view rate
    (source_current_record rate rewards C_star C_h q t s hs control0 z)
    (cell rate rewards C_star C_h q t s hs control0 z) selected hselected
  exact (congrArg ReferenceDownReception.ChoiceTimeView.payload
    (hviewCell.trans hview)).trans hpayload.symm

private theorem actualCell_recordedArm_eq_none_of_not_data
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hdata : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
      PublicDiscreteDraws.dataSlot) : c.input.recordedArm = none := by
  rw [c.recordedArm_eq]
  simp [ReferenceFirstWindowNumericalStream.sourceArm,
    SnapshotRecordingKernel.recordingMap,
    CanonicalRecordingSlice.slotFromScalar_coordinate, hdata]

private theorem actualCellSourceAlignment
    (z : Zplus)
    {record1 record2 : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : record1 = record2)
    (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record1)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (selected : ReferenceActivePhysicalStep.Selection record2.input)
    (hselected : (ReferenceActivePhysicalStep.prepare record2.input).coordinator.selection =
      some selected)
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (hview : selected.view = view)
    (hdata : PublicDiscreteDraws.slotDraw
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val).1 = PublicDiscreteDraws.dataSlot →
      ∀ i, (record2.output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hslotData : PublicDiscreteDraws.slotDraw
        (record1.input.row.2 record1.input.time).1 = PublicDiscreteDraws.dataSlot ↔
      PublicDiscreteDraws.slotDraw
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val).1 = PublicDiscreteDraws.dataSlot)
    (marker : Option (Fin p.K))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
      record2.input.time view.complementWeights)
    (hsource : marker = ReferenceFirstWindowNumericalStream.sourceArm record2
      view.payload view.pendingAtChoice states view.complementWeights view.cutoff hvalid)
    (hmarkerNone : PublicDiscreteDraws.slotDraw
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val).1 ≠ PublicDiscreteDraws.dataSlot →
      marker = none) :
    c.selected.view = view ∧
    (PublicDiscreteDraws.slotDraw (record1.input.row.2 record1.input.time).1 =
        PublicDiscreteDraws.dataSlot → c.states = states) ∧
    ReferenceFirstWindowNumericalStream.sourceArm record1 c.selected.view.payload
      c.selected.view.pendingAtChoice c.states c.selected.view.complementWeights
      c.selected.view.cutoff c.choiceInputsValid = marker := by
  cases hrecord
  have hcellSelection : (ReferenceActivePhysicalStep.prepare record1.input).coordinator.selection =
      some c.selected := by
    simpa [record1.output_eq, ReferenceActivePhysicalStep.step] using c.selection_actual
  have hselectedCell : c.selected = selected :=
    Option.some.inj (hcellSelection.symm.trans hselected)
  have hviewCell : c.selected.view = view := by
    rw [hselectedCell]
    exact hview
  have hstatesCell : PublicDiscreteDraws.slotDraw
      (record1.input.row.2 record1.input.time).1 = PublicDiscreteDraws.dataSlot →
      c.states = states := by
    intro hslot
    have hcontrol := hslotData.mp hslot
    funext i
    have hordinary := hdata hcontrol i
    rw [c.ordinary i] at hordinary
    injection hordinary
  constructor
  · exact hviewCell
  constructor
  · exact hstatesCell
  · by_cases hslot : PublicDiscreteDraws.slotDraw
        (record1.input.row.2 record1.input.time).1 = PublicDiscreteDraws.dataSlot
    · have hsource' : marker = ReferenceFirstWindowNumericalStream.sourceArm record1
          c.selected.view.payload c.selected.view.pendingAtChoice c.states
          c.selected.view.complementWeights c.selected.view.cutoff c.choiceInputsValid := by
        have hstates := hstatesCell hslot
        cases hviewCell
        cases hstates
        exact hsource
      exact hsource'.symm
    · have hcontrol : PublicDiscreteDraws.slotDraw
          (ReferenceFirstLiveRecordingSourceCylinder.originalControl
            rate rewards C_star C_h q t s hs z.val).1 ≠ PublicDiscreteDraws.dataSlot := by
        intro hc
        exact hslot (hslotData.mpr hc)
      have hcellNone : c.input.recordedArm = none := by
        rw [c.recordedArm_eq]
        simp [ReferenceFirstWindowNumericalStream.sourceArm,
          SnapshotRecordingKernel.recordingMap,
          CanonicalRecordingSlice.slotFromScalar_coordinate, hslot]
      calc
        ReferenceFirstWindowNumericalStream.sourceArm record1 c.selected.view.payload
            c.selected.view.pendingAtChoice c.states c.selected.view.complementWeights
            c.selected.view.cutoff c.choiceInputsValid = c.input.recordedArm :=
          c.recordedArm_eq.symm
        _ = none := hcellNone
        _ = marker := (hmarkerNone hcontrol).symm

/-- The source's current cell keeps N's whole numerical input and the source's
own original marker. Its queue arrival is the stated all-arm floor formula. -/
theorem source_current_cell_fields (z : Zplus) :
    let c := cell rate rewards C_star C_h q t s hs control0 z
    c.input.enabled = true ∧
    (∀ j : Fin p.K,
      c.input.reward j = ((rewards t j).val : ℝ) / (D p : ℝ)) ∧
    (∀ j : Fin p.K,
      c.input.rate j = ReferenceFirstLiveRecordingSourceCylinder.markerRate
        rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 z).1 j) ∧
    c.input.recordedArm = ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
      rate rewards C_star C_h q t s hs control0 z ∧
    (∀ j : Fin p.K,
      RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.input j =
        if ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
            rate rewards C_star C_h q t s hs control0 z = some j then
          Nat.floor ((rate.n : ℝ) * (((rewards t j).val : ℝ) / (D p : ℝ)) /
            ReferenceFirstLiveRecordingSourceCylinder.markerRate
              rate rewards C_star C_h q t s hs control0
              (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
                rate rewards C_star C_h q t s hs control0 z).1 j)
        else 0) := by
  classical
  dsimp only
  let current := (sourceCurrentWindow rate rewards C_star C_h q t s hs control0 z)[
    (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z).val]
  let c := cell rate rewards C_star C_h q t s hs control0 z
  have hrecord : current =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val :=
    source_current_record rate rewards C_star C_h q t s hs control0 z
  have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
    rate z.val.val rewards C_star C_h z.val.property.2.1 (sourceCurrentCount t s)
    (source_current_span rate rewards C_star C_h q t s hs control0 z)
    (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 z)
  dsimp only at hfacts
  rcases hfacts with ⟨_, _, _, _, henabled, hreward, hcellRate, _, _⟩
  change c.input.enabled = true at henabled
  change c.input.reward =
    (fun j => ((current.input.rewards current.input.time j).val : ℝ) / (D p : ℝ)) at hreward
  change c.input.rate = c.selected.view.payload.rate at hcellRate
  obtain ⟨states, memories, r, owned, base, d, hsStart, continuation, arm,
      hcoord, hordinary, hselectedPayload, hselectedRecord, hvalid, hsourceMarker⟩ :=
    ReferenceFirstLiveRecordingSourceCylinder.sourceMarker_eq_sourceArm
      rate rewards C_star C_h q t s hs control0 z
  rcases hselectedRecord with ⟨selected, hselected, hview, hdata⟩
  let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
      payload := r.payload
      pendingAtChoice := d.startResult.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
      complementWeights :=
        (ReferenceActivePhysicalStep.liveRegistersAt r
          (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput
            (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
              rate rewards C_star C_h q t s hs control0 z).1.val).time).complementWeights }
  have hview' : selected.view = view := by simpa [view] using hview
  have hbaseline : ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
      (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
        rate rewards C_star C_h q t s hs control0 z).1 = r.payload := hselectedPayload
  have hrecordRewards : current.input.rewards = rewards := by
    rw [hrecord]
    exact ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_rewards
      rate rewards C_star C_h q t s hs control0 z.val
  have hrecordTime : current.input.time = t := by
    rw [hrecord]
    exact ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time
      rate rewards C_star C_h q t s hs control0 z.val
  have hrowOriginal :
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input.row.2 t =
      ReferenceFirstLiveRecordingSourceCylinder.originalControl
        rate rewards C_star C_h q t s hs z.val := by
    simp only [ReferenceActivePhysicalStep.RoundInput.row,
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_rows,
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_selected,
      ReferenceFirstLiveRecordingSourceCylinder.originalControl]
  have hslotData :
      PublicDiscreteDraws.slotDraw (current.input.row.2 current.input.time).1 =
        PublicDiscreteDraws.dataSlot ↔
      PublicDiscreteDraws.slotDraw
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val).1 = PublicDiscreteDraws.dataSlot := by
    rw [hrecordTime, hrecord, hrowOriginal]
  have hmarkerNone :
      PublicDiscreteDraws.slotDraw
          (ReferenceFirstLiveRecordingSourceCylinder.originalControl
            rate rewards C_star C_h q t s hs z.val).1 ≠ PublicDiscreteDraws.dataSlot →
      ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
        rate rewards C_star C_h q t s hs control0 z = none := by
    intro hslot
    rw [ReferenceFirstLiveRecordingSourceCylinder.sourceMarker_eq_original
      rate rewards C_star C_h q t s hs control0 z]
    have hrecordSlot : PublicDiscreteDraws.slotDraw
        ((ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val).input.row.2
            (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
              rate rewards C_star C_h q t s hs control0 z.val).input.time).1 ≠
          PublicDiscreteDraws.dataSlot := by
      rw [ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time,
        hrowOriginal]
      exact hslot
    simp [ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord, hrecordSlot]
  have hvalid' : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z.val).input.time
      view.complementWeights := by
    simpa [view] using hvalid
  have halignment := actualCellSourceAlignment rate rewards C_star C_h q t s hs control0 z
    hrecord c states memories selected hselected view hview' hdata hslotData
    (ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
      rate rewards C_star C_h q t s hs control0 z) hvalid' (by
        simpa [view] using hsourceMarker) hmarkerNone
  rcases halignment with ⟨hviewCell, _, hsourceArm⟩
  have hpayload : c.selected.view.payload =
      ReferenceFirstLiveRecordingReadoutMeasurability.selectedBaselinePayload
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 z).1 := by
    rw [hviewCell, hbaseline]
  have hmarkerRate (j : Fin p.K) :
      c.selected.view.payload.rate j =
        ReferenceFirstLiveRecordingSourceCylinder.markerRate rate rewards C_star C_h q t s hs
          control0 (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
            rate rewards C_star C_h q t s hs control0 z).1 j := by
    rw [hpayload, ReferenceFirstLiveRecordingSourceCylinder.markerRate]
    exact AssignmentStartPayload.Input.rate_eq_canonical _ j
  have hcellMarker (j : Fin p.K) : c.input.rate j =
      ReferenceFirstLiveRecordingSourceCylinder.markerRate rate rewards C_star C_h q t s hs
        control0 (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 z).1 j := by
    exact (congrFun hcellRate j).trans (hmarkerRate j)
  have hrecorded : c.input.recordedArm =
      ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
        rate rewards C_star C_h q t s hs control0 z := by
    calc
      c.input.recordedArm =
          ReferenceFirstWindowNumericalStream.sourceArm current c.selected.view.payload
            c.selected.view.pendingAtChoice c.states c.selected.view.complementWeights
            c.selected.view.cutoff c.choiceInputsValid := c.recordedArm_eq
      _ = ReferenceFirstLiveRecordingSourceCylinder.sourceMarker
          rate rewards C_star C_h q t s hs control0 z := hsourceArm
  refine ⟨henabled, ?_, ?_, hrecorded, ?_⟩
  · intro j
    change c.input.reward j = _
    rw [congrFun hreward j, hrecordRewards, hrecordTime]
  · exact hcellMarker
  · intro j
    change RecordedQueueRun.quantizedArrival _ c.input j = _
    unfold RecordedQueueRun.quantizedArrival
    rw [hrecorded]
    rw [hcellMarker j, congrFun hreward j, hrecordRewards, hrecordTime]
    rfl

/-- The focal original source, on C's literal continuing subtype. -/
def followerAsSourcePlus (i : Fin (p.m - 1))
    (z : ReferenceFirstLiveSourceSavedMoments.SourceFollower
      rate rewards C_star C_h q t s hs control0 i) : Zplus :=
  ⟨z.val, z.property.1⟩

/-- On DATA, the actual cell's focal follower is unoccupied. The status is
produced from the source branch; no current-state premise is assumed. -/
theorem source_current_cell_unoccupied_on_data (i : Fin (p.m - 1))
    (z : ReferenceFirstLiveSourceSavedMoments.SourceFollower
      rate rewards C_star C_h q t s hs control0 i)
    (hdata : PublicDiscreteDraws.slotDraw
      (ReferenceFirstLiveRecordingSourceCylinder.originalControl
        rate rewards C_star C_h q t s hs z.val).1 = PublicDiscreteDraws.dataSlot) :
    ((cell rate rewards C_star C_h q t s hs control0
      (followerAsSourcePlus rate rewards C_star C_h q t s hs control0 i z)).states i).status =
        .unoccupied := by
  let zp := followerAsSourcePlus rate rewards C_star C_h q t s hs control0 i z
  let c := cell rate rewards C_star C_h q t s hs control0 zp
  obtain ⟨states, memories, r, owned, base, d, hsStart, continuation, arm,
      hcoord, hordinary, hpayload, hselectedRecord, hvalid, hsourceMarker⟩ :=
    ReferenceFirstLiveRecordingSourceCylinder.sourceMarker_eq_sourceArm
      rate rewards C_star C_h q t s hs control0 zp
  obtain ⟨selected, hselected, hview, hdataStates⟩ := hselectedRecord
  have hunoccupied : (states i).status = .unoccupied := by
    have hstatus := z.property.2
    change (match ((ReferenceActivePhysicalStep.prepare
      (ReferenceFirstLiveRecordingReadoutMeasurability.sourceCurrentInput
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceSplit
          rate rewards C_star C_h q t s hs control0 zp).1.val)).followers.followers i).configuration with
      | .ordinary state _ => state.status = .unoccupied
      | .dagger => False) at hstatus
    rw [hordinary i] at hstatus
    exact hstatus
  have hrecord := source_current_record rate rewards C_star C_h q t s hs control0 zp
  have hconfigurationEq := congrArg
    (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
      (record.output.preparation.followers.followers i).configuration) hrecord
  have hconfiguration := hconfigurationEq.symm.trans (c.ordinary i)
  have hsame := (hdataStates hdata i).symm.trans hconfiguration
  have hstate : states i = c.states i := by injection hsame
  rw [← hstate]
  exact hunoccupied

private theorem logEmission_eq_nil_of_not_data
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hdata : PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 ≠
      PublicDiscreteDraws.dataSlot) :
    ReferenceFollowerBufferProvenance.logEmission i record = [] := by
  classical
  have htests : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := by
    intro hpass
    exact hdata ((ReferencePrelaunchFollower.loggingTestsPass_iff i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))).mp hpass).2.1
  unfold ReferenceFollowerBufferProvenance.logEmission
  dsimp only
  cases (record.output.preparation.followers.followers i).configuration with
  | dagger => rfl
  | ordinary state memory =>
      simp only
      split
      · exact ActiveFollowerLogging.logAt_eq_nil_of_not_tests i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)) htests
      · rfl

/-- The actual current numerical arrival is the integer contribution of the
original record's current log, including off-DATA and failed-thinning paths. -/
theorem source_current_arrival_eq_saved_contribution (i : Fin (p.m - 1))
    (z : ReferenceFirstLiveSourceSavedMoments.SourceFollower
      rate rewards C_star C_h q t s hs control0 i) :
    let zp := followerAsSourcePlus rate rewards C_star C_h q t s hs control0 i z
    let x := (ReferenceFirstLiveSourceSavedMoments.followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i z).1
    let payload := ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
      rate rewards C_star C_h q t s hs control0 i x
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (cell rate rewards C_star C_h q t s hs control0 zp).input
      (ReferenceFirstLiveSourceSavedMoments.assignedArm
        rate rewards C_star C_h q t s hs control0 i x) =
      ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z.val) payload i := by
  classical
  intro zp x payload
  let current := (sourceCurrentWindow rate rewards C_star C_h q t s hs control0 zp)[
    (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 zp).val]
  let c := cell rate rewards C_star C_h q t s hs control0 zp
  have hrecord : current = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z.val :=
    source_current_record rate rewards C_star C_h q t s hs control0 zp
  have hpayload : c.selected.view.payload = payload :=
    source_current_cell_payload rate rewards C_star C_h q t s hs control0 zp
  have harm : ReferenceFirstLiveSourceSavedMoments.assignedArm
      rate rewards C_star C_h q t s hs control0 i x = payload.assignment.assigned i := rfl
  rw [harm]
  by_cases hdata : PublicDiscreteDraws.slotDraw
      (current.input.row.2 current.input.time).1 = PublicDiscreteDraws.dataSlot
  · have hdataOriginal : PublicDiscreteDraws.slotDraw
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val).1 = PublicDiscreteDraws.dataSlot := by
      rw [hrecord, ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time,
        ReferenceActivePhysicalStep.RoundInput.row,
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_rows,
        ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_selected] at hdata
      exact hdata
    have hunoccupied := source_current_cell_unoccupied_on_data
      rate rewards C_star C_h q t s hs control0 i z hdataOriginal
    have hem := ReferenceFirstLiveUnoccupiedEmission.actual_first_live_unoccupied_emission
      rate z.val.val rewards C_star C_h z.val.property.2.1 (sourceCurrentCount t s)
      (source_current_span rate rewards C_star C_h q t s hs control0 zp)
      (sourceCurrentIndex rate rewards C_star C_h q t s hs control0 zp) i hunoccupied
    have h : RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.input
        (c.selected.view.payload.assignment.assigned i) =
        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
          current c.selected.view.payload i := (hem.1.trans hem.2).symm
    rw [hpayload, hrecord] at h
    exact h
  · have hnone : c.input.recordedArm = none := by
      exact actualCell_recordedArm_eq_none_of_not_data rate current c hdata
    have hzero : RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.input
        (payload.assignment.assigned i) = 0 := by
      simp only [RecordedQueueRun.quantizedArrival, hnone, reduceCtorEq, ↓reduceIte]
    change RecordedQueueRun.quantizedArrival _ c.input _ = _
    rw [hzero, ← hrecord]
    unfold ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
    rw [logEmission_eq_nil_of_not_data rate current i hdata]
    rfl

/-- Literal integer equality with the original physical record's `logEmission`
sum, before normalization. No older buffer entries are included. -/
theorem source_current_arrival_eq_log_emission (i : Fin (p.m - 1))
    (z : ReferenceFirstLiveSourceSavedMoments.SourceFollower
      rate rewards C_star C_h q t s hs control0 i) :
    let zp := followerAsSourcePlus rate rewards C_star C_h q t s hs control0 i z
    let x := (ReferenceFirstLiveSourceSavedMoments.followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i z).1
    let payload := ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
      rate rewards C_star C_h q t s hs control0 i x
    let a := ReferenceFirstLiveSourceSavedMoments.assignedArm
      rate rewards C_star C_h q t s hs control0 i x
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (cell rate rewards C_star C_h q t s hs control0 zp).input a =
      SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
        (payload.exponent a) a (t.val + 1)
        (ReferenceFollowerBufferProvenance.logEmission i
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val)) := by
  intro zp x payload a
  have h := source_current_arrival_eq_saved_contribution
    rate rewards C_star C_h q t s hs control0 i z
  dsimp only at h
  rw [ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution,
    ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord_time] at h
  exact h

/-- The actual current-cell arrival, normalized by the same `eta * D`, is
exactly M's original-source saved readout on its unnormalized follower fibre. -/
theorem source_current_normalized_arrival_eq_source_saved (i : Fin (p.m - 1))
    (z : ReferenceFirstLiveSourceSavedMoments.SourceFollower
      rate rewards C_star C_h q t s hs control0 i) :
    let zp := followerAsSourcePlus rate rewards C_star C_h q t s hs control0 i z
    let x := (ReferenceFirstLiveSourceSavedMoments.followerSourceSplit
      rate rewards C_star C_h q t s hs control0 i z).1
    (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (cell rate rewards C_star C_h q t s hs control0 zp).input
      (ReferenceFirstLiveSourceSavedMoments.assignedArm
        rate rewards C_star C_h q t s hs control0 i x) : ℝ) /
        (rate.eta.val * (D p : ℝ)) =
      ReferenceFirstLiveSourceSavedMoments.sourceSaved
        rate rewards C_star C_h q t s hs control0 i z := by
  dsimp only
  rw [ReferenceFirstLiveSourceSavedMoments.sourceSaved_eq_originalCurrentRecord]
  exact congrArg (fun value : ℕ => (value : ℝ) / (rate.eta.val * (D p : ℝ)))
    (source_current_arrival_eq_saved_contribution rate rewards C_star C_h q t s hs control0 i z)

end Bandits.Support.ReferenceFirstLiveSourceCellReadout

end
