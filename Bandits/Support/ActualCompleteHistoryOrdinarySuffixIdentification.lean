/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteHistoryRewardReadouts
public import Bandits.Support.ActualReferenceStoppedPrefixSplice

/-!
# Identification of the actual complete history's ordinary suffix

Mathematical evidence: `sources/zip4/manuscript/08_main_theorem.tex:29-42,67-75`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/06_interruptions.tex:240-295`, and
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`.

The actual mixed steps and their real block-boundary adapters preserve the
selected-row ordinary state produced by the initialization splice. Saved-record
exclusions are needed only for the subsequent comparison with the reference.
This is a deterministic internal identification, not an exceptional-event or
manuscript regret theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions BootstrapDimensions BootstrapObservedFollower
open ActualPostlaunchPhysicalStep ActualCompletePhysicalHistory

namespace Bandits.Support.ActualCompleteHistoryOrdinarySuffixIdentification

variable {p : ConstructorDimensions.Parameters} {rate : ActualPostlaunchPhysicalStep.RateInput p}

/-- Literal physical projection of a retained actual mixed round. -/
def mixedPhysicalProjection {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : MixedRoundRecord p rate source rewards) :
    ReferenceActiveStoppedPrefixCoupling.PhysicalRound p :=
  ⟨record.time, record.actions, record.feedback,
    fun i => (record.actions i, ActualInitializationPhysicalStep.observationOfGrid p
      (record.feedback i))⟩

private theorem canonical_state_eq {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hcoordinator : input.state.coordinator = active.coordinator)
    (hbank : input.state.upDecoderBank = active.upDecoderBank)
    (hfollowers : ∀ i, input.state.followers i = .declared
      (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
      (active.activations i) (active.followers i)) :
    (canonicalRoundInput input hdeclared).state = active := by
  have hdata : ∀ i, canonicalFollowerData input hdeclared i =
      (active.activations i, active.followers i) := by
    intro i
    simp only [canonicalFollowerData, hfollowers i]
  cases active with
  | mk coordinator bank activations followers =>
      change ReferenceActivePhysicalStep.State.mk _ _ _ _ =
        ReferenceActivePhysicalStep.State.mk coordinator bank activations followers
      congr 1
      · exact funext (fun i => congrArg Prod.fst (hdata i))
      · exact funext (fun i => congrArg Prod.snd (hdata i))

private theorem step_next_eq_canonical {block : Fin (n_boot p)} {cursor : Nat}
    (input : PhysicalInput (p := p) (rate := rate) block cursor)
    (hdeclared : AllDeclaredSelectedRow input) :
    let next := (OrdinaryActivePhysicalStep.step (canonicalRoundInput input hdeclared)).next
    (step input).nextState.coordinator = next.coordinator ∧
      (step input).nextState.upDecoderBank = next.upDecoderBank ∧
      ∀ i, (step input).nextState.followers i = .declared
        (ActualInitializationPhysicalStep.selectedRowIndex p input.source)
        (next.activations i) (next.followers i) := by
  have hc := coordinatorFields_eq_canonical_step input hdeclared
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro i
  rw [OrdinaryActivePhysicalStep.step_activation_preserved]
  exact followerNext_eq_canonical_step input hdeclared i

private theorem mixed_physical_eq_canonical
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : MixedRoundRecord p rate source rewards)
    (hdeclared : AllDeclaredSelectedRow record.input) :
    mixedPhysicalProjection record =
      (ReferenceActiveStoppedPrefixCoupling.RoundRecord.mk
        (canonicalRoundInput record.input hdeclared)).physical := by
  have ha := actionProfile_eq_canonical record.input hdeclared
  have hf := funext (gridFeedback_eq_canonical record.input hdeclared)
  have he := funext (OrdinaryActivePhysicalStep.step_own_entry
    (canonicalRoundInput record.input hdeclared))
  change ReferenceActiveStoppedPrefixCoupling.PhysicalRound.mk _ _ _ _ =
    ReferenceActiveStoppedPrefixCoupling.PhysicalRound.mk _ _ _ _
  congr 1
  · exact (congrArg (fun result => actionProfile result.prepared) record.result_eq).trans ha
  · exact (congrArg (fun result : RoundResult record.input =>
      physicalFeedback result.prepared) record.result_eq).trans hf
  · change _ = (OrdinaryActivePhysicalStep.step
      (canonicalRoundInput record.input hdeclared)).ownEntries
    rw [he]
    funext i
    change (record.actions i, ActualInitializationPhysicalStep.observationOfGrid p
      (record.feedback i)) = _
    have ha' : record.actions =
        (ReferenceActivePhysicalStep.prepare
          (canonicalRoundInput record.input hdeclared)).arms.actions := by
      exact (congrArg (fun result => actionProfile result.prepared) record.result_eq).trans ha
    have hf' : record.feedback =
        (ReferenceActivePhysicalStep.prepare
          (canonicalRoundInput record.input hdeclared)).feedback.feedback := by
      exact (congrArg (fun result : RoundResult record.input =>
        physicalFeedback result.prepared) record.result_eq).trans hf
    rw [ha', hf']
    rfl

/-- A real declared follower crosses an artificial postlaunch block boundary
with its row, activation, and complete ordinary/dagger configuration intact. -/
theorem crossSuccessorBoundary_declared_eq {block next : Fin (n_boot p)}
    (hnext : block.val + 1 < n_boot p)
    (next_eq : next = ActualInitializationRun.successorBlock p block hnext)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (state : PostlaunchState (p := p) (rate := rate) block (blockLength p block))
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (hdeclared : state.followers i = .declared row activation configuration) :
    (crossSuccessorBoundary hnext next_eq source state).followers i =
      .declared row activation configuration := by
  subst next
  change ActualInitializationRun.beginFollowerBlock p rate _ source i
    (boundaryCarry state i) = _
  rw [boundaryCarry_eq_actual_boundary, hdeclared,
    ActualInitializationHorizon.followerCarryAtBlockBoundary_declared_eq]
  rfl

private theorem roundInput_eq (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time = y.time)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  cases hstate
  cases hrows
  cases hselected
  cases htime
  cases hrewards
  rfl

private theorem mixedBlockTrace_eq_ordinary
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (active : ReferenceActivePhysicalStep.State p rate) (start finish : Nat)
    (hspan : start + finish ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start)
    {block : Fin (n_boot p)} {cursor stop : Nat}
    {state : PostlaunchState (p := p) (rate := rate) block cursor}
    (trace : MixedBlockTrace p rate source rewards block cursor state stop)
    (offset : Nat) (hoffset : start + offset ≤ p.T)
    (htime : blockStart p block + cursor = start + offset)
    (hstop : blockStart p block + stop = start + finish)
    (hcoordinator : state.coordinator =
      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.coordinator)
    (hbank : state.upDecoderBank =
      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.upDecoderBank)
    (hfollowers : ∀ i, state.followers i = .declared
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      ((ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.activations i)
      ((ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.followers i)) :
    let final := ReferenceActiveStoppedPrefixCoupling.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start finish hspan hmode
    trace.finalState.coordinator = final.finalState.coordinator ∧
      trace.finalState.upDecoderBank = final.finalState.upDecoderBank ∧
      (∀ i, trace.finalState.followers i = .declared
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (final.finalState.activations i) (final.finalState.followers i)) ∧
      final.physicalTrace =
        (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start offset hoffset hmode).physicalTrace ++
            trace.records.map mixedPhysicalProjection := by
  induction trace generalizing offset with
  | done state =>
      have heq : offset = finish := by omega
      subst offset
      exact ⟨hcoordinator, hbank, hfollowers, (List.append_nil _).symm⟩
  | @step cursor stop state input hstate hsource hrewards result hresult tail hlt ih =>
      have hnext : start + (offset + 1) ≤ p.T := by omega
      let previous := ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode
      have hdeclared : AllDeclaredSelectedRow input := by
        intro i
        refine ⟨(previous.finalState.activations i, previous.finalState.followers i), ?_⟩
        rw [hstate, hsource]
        exact hfollowers i
      have hcanonical := canonical_state_eq input hdeclared previous.finalState
        (hstate ▸ hcoordinator) (hstate ▸ hbank) (by
          intro i
          rw [hstate, hsource]
          exact hfollowers i)
      have hinput : canonicalRoundInput input hdeclared =
          (ReferenceActiveStoppedPrefixCoupling.ordinaryRecordAt active source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
            start offset hnext hmode).input := by
        apply roundInput_eq
        · exact hcanonical
        · change input.source.1.2 = source.1.2
          rw [hsource]
        · change ActualInitializationPhysicalStep.selectedRowIndex p input.source = _
          rw [hsource]
          rfl
        · apply Fin.ext
          exact htime
        · exact hrewards
      have hsuccessor := ReferenceActiveStoppedPrefixCoupling.run_successor_equations
        active source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start offset hnext hmode
      have hfields := step_next_eq_canonical input hdeclared
      dsimp only at hfields
      rw [hinput] at hfields
      have htail := ih (offset + 1) hnext (by omega) hstop
        (by rw [hresult, hsuccessor.1]; exact hfields.1)
        (by rw [hresult, hsuccessor.1]; exact hfields.2.1)
        (by
          intro i
          rw [hresult, hsuccessor.1]
          simpa only [hsource, ReferenceActiveStoppedPrefixCoupling.RoundRecord.output]
            using hfields.2.2 i)
      refine ⟨htail.1, htail.2.1, htail.2.2.1, ?_⟩
      have hphysical := mixed_physical_eq_canonical
        (MixedRoundRecord.mk block cursor input hsource hrewards result hresult) hdeclared
      rw [hinput] at hphysical
      rw [htail.2.2.2]
      change _ ++ _ = _ ++ (_ :: _)
      rw [ReferenceActiveStoppedPrefixCoupling.Run.physicalTrace, hsuccessor.2,
        List.map_append, List.map_singleton, ← hphysical, List.append_assoc]
      rfl

private theorem postlaunchSuffix_eq_ordinary
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (active : ReferenceActivePhysicalStep.State p rate) (start : Nat)
    (hstartT : start ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start)
    {block : Fin (n_boot p)}
    {state : PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state)
    (offset : Nat) (hoffset : start + offset ≤ p.T)
    (hstart : blockStart p block = start + offset)
    (hcoordinator : state.coordinator =
      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.coordinator)
    (hbank : state.upDecoderBank =
      (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.upDecoderBank)
    (hfollowers : ∀ i, state.followers i = .declared
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      ((ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.activations i)
      ((ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start offset hoffset hmode).finalState.followers i)) :
    (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      start (p.T - start) (by omega) hmode).physicalTrace =
        (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start offset hoffset hmode).physicalTrace ++
            suffix.records.map mixedPhysicalProjection := by
  induction suffix generalizing offset with
  | @final block state trace hlast =>
      have hstop := finalBlock_endpoint_eq_T p block hlast
      have hlength := ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hb := mixedBlockTrace_eq_ordinary source rewards active start (p.T - start)
        (by omega) hmode trace offset hoffset (by omega) (by omega)
        hcoordinator hbank hfollowers
      exact hb.2.2.2
  | @successor block state trace hnext next heq tail ih =>
      have hlength := ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hpositive := blockStart_lt_blockStop p block
      have hstopT : blockStop p block ≤ p.T := by simp only [blockStop, Nat.min_le_left]
      let middle := blockStop p block - start
      have hmiddle : start + middle = blockStop p block := by omega
      have hnextval : next.val = block.val + 1 := by
        rw [heq]
        rfl
      have hnextstart : blockStart p next = blockStop p block := by
        have ha := ActualInitializationHorizon.nextActivationRound_eq_successor_start
          block next hnextval
        change blockStop p block + 1 = blockStart p next + 1 at ha
        omega
      have hb := mixedBlockTrace_eq_ordinary source rewards active start middle
        (by omega) hmode trace offset hoffset (by omega) (by omega)
        hcoordinator hbank hfollowers
      have ht := ih middle (by omega) (by omega)
        (by rw [crossSuccessorBoundary_coordinator]; exact hb.1)
        (by rw [crossSuccessorBoundary_bank]; exact hb.2.1)
        (by
          intro i
          exact crossSuccessorBoundary_declared_eq hnext heq source trace.finalState i
            _ _ _ (hb.2.2.1 i))
      rw [ht, hb.2.2.2, List.append_assoc]
      simp only [PostlaunchSuffix.records, List.map_append]

private theorem postlaunchRecords_eq_ordinary_of_handoff
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hstartT : launch.monitor.launchPosition ≤ p.T)
    (hspan : launch.monitor.launchPosition + (p.T - launch.monitor.launchPosition) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active launch.monitor.launchPosition)
    (hcoordinator : active.coordinator = .first)
    (hbank : active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p)
    (hhandoff : ∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate
      ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalHandoff.followers i) = .declared
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (active.activations i) (active.followers i)) :
    (postlaunchRecords (sourceInitializedActualCompleteHistory p rate source rewards
      C_star C_h)).map mixedPhysicalProjection =
        (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          launch.monitor.launchPosition (p.T - launch.monitor.launchPosition)
          hspan hmode).physicalTrace := by
  by_cases hbefore : launch.monitor.launchPosition < p.T
  · let block := sourceInitializedLaunchSuccessorBlock p rate source rewards C_star C_h
      launch seed hlaunch hbefore
    let input := sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch seed hlaunch hbefore
    have hstart : blockStart p block = launch.monitor.launchPosition := by
      have ht := sourceInitializedLaunchSuccessorInput_time_val p rate source rewards
        C_star C_h launch seed hlaunch hbefore
      simpa only [PhysicalInput.time, ActualInitializationRun.blockTime, Nat.add_zero]
        using ht
    have hfollowers : ∀ i, input.state.followers i = .declared
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (active.activations i) (active.followers i) := by
      intro i
      change ActualInitializationRun.beginFollowerBlock p rate block source i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate
          ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
            C_star C_h).terminalHandoff.followers i)) = _
      rw [hhandoff i]
      rfl
    have hfold : foldMixedBlockFromInput p rate source rewards block input
        (sourceInitializedLaunchSuccessorInput_source p rate source rewards C_star C_h
          launch seed hlaunch hbefore)
        (sourceInitializedLaunchSuccessorInput_rewards p rate source rewards C_star C_h
          launch seed hlaunch hbefore) =
        foldMixedBlock p rate source rewards block input.state :=
      ActualPostlaunchBlockMeasurability.foldMixedBlockFromInput_eq_foldMixedBlock input
    have hconstructor : sourceInitializedActualCompleteHistory p rate source rewards
        C_star C_h = .launchedBefore launch seed hlaunch hbefore
          (runPostlaunchSuffix p rate source rewards block input.state) := by
      unfold sourceInitializedActualCompleteHistory
      dsimp only
      rw! [hlaunch]
      simp only [dite_eq_left hbefore]
      rw [hfold]
      rfl
    rw [hconstructor]
    have hzero := ReferenceActiveStoppedPrefixCoupling.run_zero active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      launch.monitor.launchPosition (by omega) hmode
    have hs := postlaunchSuffix_eq_ordinary source rewards active launch.monitor.launchPosition
      hstartT hmode (runPostlaunchSuffix p rate source rewards block input.state)
      0 (by omega) (by omega)
      (by rw [hzero.1]; exact hcoordinator.symm)
      (by rw [hzero.1]; exact hbank.symm)
      (by rw [hzero.1]; exact hfollowers)
    have hempty : (ReferenceActiveStoppedPrefixCoupling.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        launch.monitor.launchPosition 0 (by omega) hmode).physicalTrace = [] := by
      simp only [ReferenceActiveStoppedPrefixCoupling.Run.physicalTrace, hzero.2, List.map_nil]
    rw [hempty, List.nil_append] at hs
    exact hs.symm
  · have hat : launch.monitor.launchPosition = p.T := by omega
    have hconstructor : sourceInitializedActualCompleteHistory p rate source rewards
        C_star C_h = .launchedAtHorizon launch seed hlaunch hat := by
      unfold sourceInitializedActualCompleteHistory
      dsimp only
      rw! [hlaunch]
      simp only [dite_eq_right hbefore]
    rw [hconstructor]
    have hzero := ReferenceActiveStoppedPrefixCoupling.run_zero active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      launch.monitor.launchPosition (by omega) hmode
    have hn : p.T - launch.monitor.launchPosition = 0 := by omega
    simp only [postlaunchRecords, List.map_nil,
      ReferenceActiveStoppedPrefixCoupling.Run.physicalTrace, hn, hzero.2]

private theorem launch_canonical_state_eq
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hcoordinator : active.coordinator = .first)
    (hbank : active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p)
    (hhandoff : ∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate
      ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalHandoff.followers i) = .declared
          (ActualInitializationPhysicalStep.selectedRowIndex p source)
          (active.activations i) (active.followers i))
    (hbefore : launch.monitor.launchPosition < p.T) :
    let input := sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
      launch seed hlaunch hbefore
    ∃ hdeclared : AllDeclaredSelectedRow input,
      (canonicalRoundInput input hdeclared).state = active := by
  let input := sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
    launch seed hlaunch hbefore
  have hfollowers : ∀ i, input.state.followers i = .declared
      (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (active.activations i) (active.followers i) := by
    intro i
    change ActualInitializationRun.beginFollowerBlock p rate _ source i
      (ActualInitializationRun.followerCarryOfBoundaryOutput rate
        ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards
          C_star C_h).terminalHandoff.followers i)) = _
    rw [hhandoff i]
    rfl
  have hdeclared : AllDeclaredSelectedRow input := fun i =>
    ⟨(active.activations i, active.followers i), hfollowers i⟩
  refine ⟨hdeclared, canonical_state_eq input hdeclared active
    hcoordinator.symm hbank.symm hfollowers⟩

/-- The projected round reads precisely the actual whole feedback-vector
reward, without any collision-free or successful-decoding premise. -/
theorem mixedPhysicalProjection_totalReward
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : MixedRoundRecord p rate source rewards) :
    (mixedPhysicalProjection record).totalReward =
      ActualCompleteHistoryRewardReadouts.actualFeedbackVectorReward record.feedback := by
  rfl

/-- Direct consumption of the accepted complete actual reward readout. -/
theorem sourceInitializedActualCompleteTotalReward_eq_initialization_add_projected
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
      ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source +
      (((postlaunchRecords (sourceInitializedActualCompleteHistory p rate source rewards
        C_star C_h)).map mixedPhysicalProjection).map
        ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum := by
  rw [ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward_eq_initialization_add_postlaunch]
  simp only [List.map_map, Function.comp_def, mixedPhysicalProjection_totalReward]

/-- One actual launched history determines one ordinary suffix and one active
state for every stopped-prefix query. The two root exclusions are precisely
the initialization and false-forward complements of the admitted splice.
The ordinary trace equality is constructed from actual mixed steps; the
reference comparison consumes the splice's already proved local coupling.

The retained carry/fold, activation, memory, and initialization relations are
outputs of that same splice. No corrected-launch memory identification or
source exceptional-event identification is asserted. -/
theorem sourceInitializedRun_launched_ordinary_suffix_eq
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
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let u := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    let hist := sourceInitializedActualCompleteHistory p rate source rewards C_star C_h
    let start := launch.monitor.launchPosition
    let count := p.T - start
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let initializedTrace := u.records.map ActualReferenceStoppedPrefixSplice.initializationPhysicalProjection
    let projected := (postlaunchRecords hist).map mixedPhysicalProjection
    ∃ actual : ActualInitializationRun.BlockCarry p rate u.terminalBlock,
      ∃ active : ReferenceActivePhysicalStep.State p rate,
        ∃ (hspan : start + count ≤ p.T)
          (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active start),
        let ordinary := ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
          start count hspan hmode
        let reference := ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
          start count hspan hmode
        ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
          u.terminalBlock actual (ReferenceInitializationRun.run x u.terminalBlock.val)
          (u.records.take (blockStart p u.terminalBlock)) ∧
        HEq u.terminalFold
          (ActualInitializationRun.foldBlock p rate u.terminalBlock source rewards actual) ∧
        actual.C_star = C_star ∧ actual.C_h = C_h ∧
        active.coordinator = .first ∧
        active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
        (∀ i, ActualInitializationRun.followerCarryOfBoundaryOutput rate
          (u.terminalHandoff.followers i) = .declared J (active.activations i)
            (active.followers i)) ∧
        (∀ i, ActualReferenceInitializationBlock.follower_start_related x source rate rfl
          (ReferenceInitializationRun.output x) i
          (.declared J (active.activations i) (active.followers i))) ∧
        (∀ i, ∃ state memory,
          active.followers i = .ordinary state memory ∧
          state = ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
            (ActualReferenceInitializationBlock.refFollower i) ∧
          state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
          state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
          state.status = .unoccupied ∧ state.initializationFailure = false) ∧
        (∀ i row activation state memory,
          actual.followers i = .declared row activation (.ordinary state memory) →
          u.terminalHandoff.followers i = .preserveDeclared J activation
            (.ordinary (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (ActualReferenceInitializationBlock.refFollower i)) memory) ∧
          active.followers i = .ordinary
            (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x)
              (ActualReferenceInitializationBlock.refFollower i)) memory) ∧
        (∀ i row activation state memory,
          u.terminalHandoff.followers i = .firstDeclaration row activation state memory →
          state = ReferencePrelaunchFollower.initial p rate.eta ∧
            memory = ActiveFollowerLifecycle.initialMemory p) ∧
        (ReferenceInitializationRun.output x).crossing = some u.terminalBlock ∧
        ReferenceInitializationRun.launchRound x = start + 1 ∧
        u.records.length = start ∧
        ActualReferenceInitializationBlock.past_related u.records
          (ReferenceInitializationRun.output x) ∧
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed = start ∧
        (ActualInitializationRun.PhysicalRoundRecord.times u.records).map Fin.val =
          ActualInitializationHorizon.consecutiveNat 0 start ∧
        (∀ hbefore : start < p.T,
          let input := sourceInitializedLaunchSuccessorInput p rate source rewards C_star C_h
            launch seed hlaunch hbefore
          ∃ hdeclared : AllDeclaredSelectedRow input,
            (canonicalRoundInput input hdeclared).state = active) ∧
        projected = ordinary.physicalTrace ∧
        ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
          (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
          ActualInitializationPhysicalRewards.sourceInitializationReward
            (p := p) (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) source + ordinary.totalReward ∧
        (∀ k (hk : k ≤ count),
          (∀ record ∈ reference.records.take k,
            ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record) →
          (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
            start k (by omega) hmode).finalState =
            (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
              start k (by omega) hmode).finalState ∧
          projected.take k = (reference.records.map
            ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k ∧
          initializedTrace ++ projected.take k = initializedTrace ++ (reference.records.map
            ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k ∧
          ((initializedTrace ++ projected.take k).map
            ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum =
            ((initializedTrace ++ (reference.records.map
              ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k).map
                ReferenceActiveStoppedPrefixCoupling.PhysicalRound.totalReward).sum) ∧
        ((∀ record ∈ reference.records,
            ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record) →
          ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
            (p := p) (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) source =
          ActualInitializationPhysicalRewards.sourceInitializationReward
            (p := p) (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) source + reference.totalReward) ∧
        (∀ index (hindex : index < count)
          (_hearlier : ∀ record ∈ reference.records.take index,
            ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record)
          (_hbad : ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted
            (ReferenceActiveStoppedPrefixCoupling.referenceRecordAt active source.1.2 J rewards
              start index (by omega) hmode)),
          (∃ record ∈ reference.records, record.input.time.val = start + index ∧
            ReferenceActiveStoppedPrefixCoupling.saved_wrong_unique_accepted record) ∧
          (∀ k (_hk : k ≤ index),
            (ReferenceActiveStoppedPrefixCoupling.run active source.1.2 J rewards
              start k (by omega) hmode).finalState =
              (ReferenceActivePhysicalHorizon.run active source.1.2 J rewards
                start k (by omega) hmode).finalState) ∧
          (∀ k, k ≤ index + 1 → projected.take k =
            (reference.records.map ReferenceActiveStoppedPrefixCoupling.referencePhysical).take k)) := by
  dsimp only
  obtain ⟨actual, active, hrelated, hfold, hCstar, hCh, hcoordinator, hbank, hhandoff,
    hstartRelated, hordinary, _hactive, _hactiveTime, hpreserve, hfirst,
    hstartT, hspan, hmode, hcross, hlaunchRound, hlength, _ha, _hf,
    hpast, helapsed, hcalendar, _suffix, _hsuffix, _reference, _hreference,
    hrest⟩ := ActualReferenceStoppedPrefixSplice.sourceInitializedRun_launched_suffix_splice
      p rate source rewards C_star C_h hinit hfalse launch seed hlaunch
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hprefix, hbad⟩ := hrest
  have htrace := postlaunchRecords_eq_ordinary_of_handoff source rewards C_star C_h
    launch seed hlaunch active hstartT hspan hmode hcoordinator hbank hhandoff
  have hreward := sourceInitializedActualCompleteTotalReward_eq_initialization_add_projected
    (rate := rate) source rewards C_star C_h
  rw [htrace] at hreward
  refine ⟨actual, active, hspan, hmode, hrelated, hfold, hCstar, hCh,
    hcoordinator, hbank, hhandoff, hstartRelated, hordinary, hpreserve, hfirst,
    hcross, hlaunchRound, hlength, hpast, helapsed, hcalendar,
    launch_canonical_state_eq source rewards C_star C_h launch seed hlaunch active
      hcoordinator hbank hhandoff,
    htrace, hreward, ?_, ?_, ?_⟩
  · intro k hk hgood
    obtain ⟨⟨hstate, hphysical, _hprefixReward⟩, happend, _, _, _, _, _, hsum⟩ :=
      hprefix k hk hgood
    rw [← htrace] at hphysical happend hsum
    exact ⟨hstate, hphysical, happend, hsum⟩
  · intro hgood
    have hcount := ReferenceActivePhysicalHorizon.run_record_count active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      launch.monitor.launchPosition (p.T - launch.monitor.launchPosition) hspan hmode
    have hgoodTake : ∀ record ∈
        (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          launch.monitor.launchPosition (p.T - launch.monitor.launchPosition)
          hspan hmode).records.take (p.T - launch.monitor.launchPosition),
        ReferenceActiveStoppedPrefixCoupling.no_wrong_unique_accepted record := by
      simpa only [List.take_of_length_le (le_of_eq hcount)] using hgood
    have heq := (hprefix (p.T - launch.monitor.launchPosition) le_rfl hgoodTake).1.2.2
    exact hreward.trans (congrArg
      (fun reward => ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) source + reward) heq)
  · intro index hindex hearlier hbadRecord
    have h := (hbad index hindex hearlier hbadRecord).1
    refine ⟨h.1, h.2.1, ?_⟩
    intro k hk
    rw [htrace]
    exact h.2.2.1 k hk

/-- A real launch at the terminal boundary has no postlaunch physical record.
It is still a launch; this statement introduces no `Fin T` sentinel. -/
theorem sourceInitializedRun_launchedAtHorizon_no_postlaunch
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch seed)
    (hat : launch.monitor.launchPosition = p.T) :
    postlaunchRecords (sourceInitializedActualCompleteHistory p rate source rewards
      C_star C_h) = [] ∧
    ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
      ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source := by
  have hconstructor : sourceInitializedActualCompleteHistory p rate source rewards C_star C_h =
      .launchedAtHorizon launch seed hlaunch hat := by
    unfold sourceInitializedActualCompleteHistory
    dsimp only
    rw! [hlaunch]
    simp only [dite_eq_right (by omega : ¬ launch.monitor.launchPosition < p.T)]
  have hrecords : postlaunchRecords (sourceInitializedActualCompleteHistory
      p rate source rewards C_star C_h) = [] := by
    rw [hconstructor]
    rfl
  refine ⟨hrecords, ?_⟩
  rw [sourceInitializedActualCompleteTotalReward_eq_initialization_add_projected,
    hrecords, List.map_nil, List.map_nil, List.sum_nil, add_zero]

/-- The actual exhausted branch retains all `T` initialization records, has
no reference crossing, and has no actual suffix. This uses the admitted
exhausted splice, rather than manufacturing a launched active state. -/
theorem sourceInitializedRun_exhausted_no_postlaunch
    (p : ConstructorDimensions.Parameters) (rate : ActualPostlaunchPhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
    (hfalse : source ∉ GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards (ActualInitializationPhysicalStep.selectedRowIndex p source))
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .exhausted live) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let u := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (ReferenceInitializationRun.output x).crossing = none ∧
    ReferenceInitializationRun.launchRound x = p.T + 1 ∧
    u.terminalBlock.val + 1 = n_boot p ∧
    blockStop p u.terminalBlock = p.T ∧
    u.records.length = p.T ∧
    ActualReferenceInitializationBlock.past_related u.records (ReferenceInitializationRun.output x) ∧
    (ActualInitializationRun.PhysicalRoundRecord.times u.records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat 0 p.T ∧
    postlaunchRecords (sourceInitializedActualCompleteHistory p rate source rewards C_star C_h) = [] ∧
    ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source =
      ActualInitializationPhysicalRewards.sourceInitializationReward
        (p := p) (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h) source := by
  dsimp only
  obtain ⟨hcross, hlaunchRound, hblock, hstop, hlength, _, _, hpast, _, _, _, _, _, _,
    hcalendar, _, _, _⟩ := ActualReferenceStoppedPrefixSplice.sourceInitializedRun_exhausted_splice
      p rate source rewards C_star C_h hinit hfalse live hexhausted
  have hconstructor : sourceInitializedActualCompleteHistory p rate source rewards C_star C_h =
      .exhausted live hexhausted := by
    unfold sourceInitializedActualCompleteHistory
    dsimp only
    rw! [hexhausted]
    simp only
  have hrecords : postlaunchRecords (sourceInitializedActualCompleteHistory
      p rate source rewards C_star C_h) = [] := by
    rw [hconstructor]
    rfl
  refine ⟨hcross, hlaunchRound, hblock, hstop, hlength, hpast, hcalendar, hrecords, ?_⟩
  rw [sourceInitializedActualCompleteTotalReward_eq_initialization_add_projected,
    hrecords, List.map_nil, List.map_nil, List.sum_nil, add_zero]

end Bandits.Support.ActualCompleteHistoryOrdinarySuffixIdentification

end
