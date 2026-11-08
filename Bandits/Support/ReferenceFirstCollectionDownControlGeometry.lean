/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionControlGeometry

import Lean.Elab.Tactic.Omega

/-!
# First-collection DOWN control geometry

Sources: `sources/zip4/manuscript/06_interruptions.tex:476-480`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

This module proves a local current-control identity on an actual first-
collection ready input. The follower boundary is reconstructed from the
public same-run prefix producer. No service law, probability bound, quota,
or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceCollectionPhaseHistory
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActiveRoundActions
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.AffineChannelLaw

namespace Bandits.Support.ReferenceFirstCollectionDownControlGeometry

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev Payload {p : Parameters} (rate : RateInput p) := ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) := ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem actual_first_collection_prefix_follower_domains
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (hspan : s + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)).records).length).length)
    (hn : 0 < n.val)
    (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)).records).length)[n.val].input
      payload l saved) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ j : Fin (p.m - 1),
      ∃ state memory,
        B[n.val].input.state.followers j = .ordinary state memory ∧
        state.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧
        ActiveFollowerLifecycle.localBufferValid state ∧
        ActiveFollowerLifecycle.downDecoderStateValid state ∧
        state.S + state.backlog ≤ w * D p ∧
        ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
          state.lastDown = some (payload.downRecord j)) := by
  classical
  cases hsElapsed
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records).length
  let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records w
  let x := window[n.val].input
  have hrunCount : epoch.records.length = count := by
    simpa [epoch, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  have hw : w < count := by simpa [epoch, w] using hshort
  have hwRecords : w < epoch.records.length := by rw [hrunCount]; exact hw
  let tail := (epoch.records.drop (w + 1)).takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
  let launch := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
    hcross
  let active := ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
    rate source rewards C_star C_h hcross start rfl
  have htailLength : window.length = tail.length + 1 := by
    dsimp [window, tail, ReferenceCollectionPhaseHistory.collectionWindow]
    rw [List.length_append]
    have hfirst : ((epoch.records.drop w).take 1).length = 1 := by
      simp only [List.length_take, List.length_drop]
      omega
    rw [hfirst]
    exact Nat.add_comm 1 tail.length
  have hjTail : n.val - 1 < tail.length := by
    have hnlt : n.val < window.length := n.isLt
    omega
  have hrunAlignment :
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross start rfl count hspan = epoch := by
    have hgenerated := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hcross
    have hactual : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h =
          some (ReferenceFirstCollectionEpochAlignment.actualLaunchState
            rate source rewards C_star C_h hcross) := by
      unfold ReferenceFirstCollectionEpochAlignment.actualLaunchState
      exact (Option.some_get _).symm
    have hlaunch : ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross =
          ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h
            hcross := Option.some.inj (hactual.symm.trans hgenerated)
    change ReferenceActivePhysicalHorizon.run launch source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active =
      ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
        rewards start count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
    cases hlaunch
    rfl
  have hshortGenerated : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross start rfl count hspan).records).length < count := by
    simpa [hrunAlignment] using hshort
  have hprefixRaw :=
    ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
      rate source rewards C_star C_h hcross start rfl count hspan hshortGenerated
  have hprefix := hprefixRaw
  simp only [hrunAlignment] at hprefix
  rcases hprefix with
    ⟨cutoffRegisters, cutoffOwned, cutoffBase, _hcutCoordinator, _hcutStart,
      _hcutQueue,
      ⟨_dispatched, _hstart, _ledger, _hinit, _hledger, _hdomain, _hclock,
        _hpending, _hnoAssignment, _selected, _hpreparedCoordinator,
        _hu, _huT, _huGrid, _hsigma, _hcutoff, _hscan,
        _hsuccessor, _hmoving, hboundaries, _hrecords⟩⟩
  have htailBound : w + 1 + tail.length ≤ count := by
    have hprefix : tail <+: epoch.records.drop (w + 1) := List.takeWhile_prefix _
    have hlength := hprefix.length_le
    have hdrop : (epoch.records.drop (w + 1)).length = count - (w + 1) := by
      simp [hrunCount]
    have htail : tail.length ≤ count - (w + 1) := by simpa [hdrop] using hlength
    omega
  let prefixAt := fun (j : ℕ) (hj : j ≤ tail.length) =>
    ReferenceActivePhysicalHorizon.run launch source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start
      (w + 1 + j) (by have := hj; omega) active
  have hnOne : 1 ≤ n.val := by omega
  have hwindowState : x.state =
      (prefixAt (n.val - 1) (Nat.le_of_lt hjTail)).finalState := by
    have hendpoints := ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
      rate source rewards C_star C_h count hcross hspan hshort n
    have hgenerated := ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate source rewards C_star C_h hcross
    have hstate := hendpoints.1
    have hindex : w + 1 + (n.val - 1) = w + n.val := by omega
    simpa [start, epoch, window, w, x, prefixAt, launch, hindex,
      ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState, hgenerated] using hstate
  have hboundaryAt := hboundaries (n.val - 1) (Nat.le_of_lt hjTail)
  have hboundaryLocal :
      (prefixAt (n.val - 1) (Nat.le_of_lt hjTail)).finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          (prefixAt (n.val - 1) (Nat.le_of_lt hjTail)).finalState.coordinator =
            .collection cutoffRegisters.payload movingLedger movingSaved := by
    simpa [prefixAt, launch, Nat.sub_add_cancel hnOne] using hboundaryAt.1
  have hcoord : (prefixAt (n.val - 1) (Nat.le_of_lt hjTail)).finalState.coordinator =
      .collection payload l saved := by
    rw [← hwindowState]
    exact hReady.1
  have hrootPayload : cutoffRegisters.payload = payload := by
    rcases hboundaryLocal with hdagger | ⟨_movingLedger, _movingSaved, hcollection⟩
    · rw [hcoord] at hdagger
      cases hdagger
    · have heq := hcollection.symm.trans hcoord
      injection heq with hpayload _ _
  change ∀ j : Fin (p.m - 1),
    ∃ state memory,
      window[n.val].input.state.followers j = .ordinary state memory ∧
      state.status = .unoccupied ∧
      ActiveFollowerLifecycle.localStateDomainValid state ∧
      ActiveFollowerLifecycle.localBufferValid state ∧
      ActiveFollowerLifecycle.downDecoderStateValid state ∧
      state.S + state.backlog ≤ w * D p ∧
      ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
        state.lastDown = some (payload.downRecord j))
  intro j
  rcases hboundaryAt.2 j with
    ⟨state, memory, hstate, hstatus, hdomain, hbuffer, hdecoder,
      _hS, _hdelta, _hbacklog, hmass, _hstamps, _hnodup, _hquantized,
      _hpairwise, _hcalendar, _hpending, _hcompleted, hlast⟩
  refine ⟨state, memory, ?_, hstatus, hdomain, hbuffer, hdecoder, ?_, ?_⟩
  · exact (congrArg (fun current => current.followers j) hwindowState).trans hstate
  · simpa [w] using hmass
  · rcases hlast with hnone | hsome
    · exact Or.inl hnone
    · exact Or.inr (by simpa [hrootPayload] using hsome)

private theorem follower_stateInputDomain_of_localStateDomainValid
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerQueueOperation.stateInputDomain state := by
  rcases hvalid with ⟨hregisters, hbuffer, _hdecoder⟩
  change state.S ≤ p.T * D p ∧ state.delta ≤ D p ∧ state.backlog ≤ p.T * D p at hregisters
  rcases (Bandits.Support.FollowerLifecycleMeasurability.localBufferValid_iff_bufferInputDomain
    state).mp hbuffer with ⟨hstamps, hkeys⟩
  refine ⟨hregisters.1, hregisters.2.1, hregisters.2.2, ?_, ?_⟩
  · intro record hrecord
    exact ⟨(hstamps record hrecord).1, (hstamps record hrecord).2.1⟩
  · exact hkeys

private def followerIndexOfFin (i : Fin (p.m - 1)) : ActiveRoundActions.Follower p.m :=
  ⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩

/-- The action-profile player associated to the API's `Fin (m - 1)` index. -/
def followerPlayerAt (i : Fin (p.m - 1)) : Fin p.m :=
  PublicDiscreteDraws.followerPlayer p.two_le_m
    ⟨i.val, by simp [PublicDiscreteDraws.followerCount]⟩

private theorem followerPlayerAt_eq (i : Fin (p.m - 1)) :
    PublicDiscreteDraws.followerPlayer p.two_le_m i = followerPlayerAt i := by
  apply Fin.ext
  rfl

private theorem tuple_profile_collisionFree
    (actions : Fin p.m → Fin p.K) (tuple : OrderedTupleSampler.Tuple p.m p.K)
    (i : Fin (p.m - 1))
    (hcoordinator : actions (ActiveRoundActions.coordinator p.two_le_m) =
      tuple.val (ActiveRoundActions.coordinator p.two_le_m))
    (hfollowers : ∀ j : Fin (p.m - 1),
      actions (followerPlayerAt j) = tuple.val (followerPlayerAt j)) :
    FiniteBanditModel.collisionFreeFor actions (followerPlayerAt i) := by
  intro player hne
  rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨j, hplayer⟩
  · rw [hcoord, hcoordinator, hfollowers i]
    intro heq
    exact ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m
      (followerIndexOfFin i) (tuple.property heq).symm
  · let jFin : Fin (p.m - 1) :=
      ⟨j.val, by simpa [PublicDiscreteDraws.followerCount] using j.isLt⟩
    have hplayerJ : followerPlayerAt jFin =
        PublicDiscreteDraws.followerPlayer p.two_le_m j := by
      apply Fin.ext
      rfl
    have hjiFin : jFin ≠ i := by
      intro heq
      apply hne
      rw [hplayer, ← hplayerJ]
      exact congrArg followerPlayerAt heq
    rw [hplayer, ← hplayerJ, hfollowers jFin, hfollowers i]
    intro heq
    have hval := congrArg Fin.val (tuple.property heq)
    have hval' : jFin.val + 1 = i.val + 1 := by
      simpa [followerPlayerAt, PublicDiscreteDraws.followerPlayer_val] using hval
    have hindex : jFin.val = i.val := by
      omega
    exact hjiFin (Fin.ext hindex)

private theorem physical_prepare_unoccupied_other
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstate : x.state.followers i = .ordinary old memory)
    (hstatus : old.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid old)
    (hnotdata : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠
      PublicDiscreteDraws.dataSlot)
    (hnotselected : ¬ (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 =
        PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1 = i)) :
    ∃ followerPrepared : DeclaredFollowerLocalRound.PreparedRound p rate,
      (ReferenceActivePhysicalStep.prepare x).followers.followers i = followerPrepared ∧
      followerPrepared.configuration = .ordinary old memory ∧
      followerPrepared.arm = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        (x.row.2 x.time).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  let followerPrepared := DeclaredFollowerLocalRound.prepare rate i x.row
    (x.state.activations i)
    x.time (x.active i) (.ordinary old memory)
  have hstateInput := follower_stateInputDomain_of_localStateDomainValid old hvalid
  have hstart : ActiveFollowerLifecycle.startRound rate.eta x.time old memory =
      .ok (old, memory) :=
    ActiveFollowerLifecycle.startRound_unoccupied rate.eta x.time old memory hvalid hstatus
  have hnotUp : ¬ (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 =
      PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1 = i) := hnotselected
  have hnoOffer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
      (x.state.activations i) x.time old = ActiveFollowerQueueOperation.UpOfferResult.noOffer := by
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i x.row
      (x.state.activations i) x.time old hstateInput
    intro hselected
    exact hnotUp ⟨hselected.1.2.1, hselected.1.2.2⟩
  have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
    old (x.row.2 x.time) i none hstatus hnotdata hnotselected
  have hchoice' : ActiveFollowerArmChoice.followerArmChoice old x.row x.time i none =
      some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
    simpa only [ActiveFollowerArmChoice.followerArmChoice] using hchoice
  have hlocal := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation rate i x.row
    (x.state.activations i) x.time (x.active i) old old memory memory hstart hnoOffer).2 _ hchoice'
  have hphysical : (ReferenceActivePhysicalStep.prepare x).followers.followers i =
      followerPrepared := by
    rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq i]
    change DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i) x.time
      (x.active i) (x.state.followers i) = followerPrepared
    rw [hstate]
  exact ⟨followerPrepared, hphysical, hlocal.2, hlocal.1⟩

private theorem ordinaryParse_stored_down_word
    (payload : Payload rate) (i : Fin (p.m - 1)) :
    ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
      some (payload.downRecord i) := by
  unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
  change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
    (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
      ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
        (payload.downWord i))).trans (payload.parseDown_downWord i)

private theorem referenceDownCut_expectedWord
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (own : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row t own rate state).expectedWord =
      ReferenceDownReception.expectedDownFlatWord view i row t := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  dsimp only
  split_ifs <;> rfl

private theorem finishFollower_down_eq_recordFollower
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).down =
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).down := by
  classical
  simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration]
  cases hrecord : ReferenceActivePhysicalStep.recordFollower view prepared.follower
      prepared.row prepared.activation prepared.time prepared.active prepared.arm
      observation state with
  | mk result downInput down =>
      cases result with
      | error failure => rfl
      | ok postRecord =>
          dsimp only
          cases DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
              prepared.time observation state memory postRecord with
          | error failure => rfl
          | ok next => cases next; rfl

/-- On the canonical first-collection run, an actual continuing READY input
with the focal follower still uninitialized at DOWN has a fixed outgoing word
before the current `TimeControl` is varied. The physical positivity event is
exactly the selected old-word hash-one and positive original grid reward
event. Every follower arm, the checked coordinator selection, receiver call,
and retained expected/raw diagnostic remain those of the actual operations.
Sources: `sources/zip4/manuscript/06_interruptions.tex:476-480`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`. -/
theorem actual_first_collection_down_current_control_geometry
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
        + count ≤ p.T) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (_hshort : w < count)
      (n : Fin B.length) (_hn : 0 < n.val)
      (payload : Payload rate) (l : Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (_hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        B[n.val].input payload l saved)
      (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (_hfi : B[n.val].input.state.followers i = .ordinary old memory)
      (_hip : i ∈ l.pending) (_hnone : old.lastDown = none),
    ∃ wD : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      wD = CoordinatorLocalArmChoice.storedDownFlatWord payload i ∧
      ∀ c : ContinuousLearningRows.TimeControl p,
        let x := B[n.val].input
        let xc := ReferenceLaterOptionalControlResampling.withControl x c
        let slot := PublicDiscreteDraws.slotDraw c.1
        let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1
        let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
        let prepared := ReferenceActivePhysicalStep.prepare xc
        ((selected = i ∧ ReferenceActiveAffinePositiveTest.downPositive xc = true) ↔
          slot = PublicDiscreteDraws.downSlot ∧ selected = i ∧
            affineHash (c.2 (0, i)) wD = 1 ∧
            0 < rewards x.time (tuple.val (followerPlayerAt i))) ∧
        (slot = PublicDiscreteDraws.downSlot ∧ selected = i →
          prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
            ActiveRoundActions.sendArm
            (affineHash (c.2 (0, i)) wD)
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
            (tuple.val (followerPlayerAt i)) ∧
          prepared.arms.actions (followerPlayerAt i) =
            tuple.val (followerPlayerAt i) ∧
          (∀ j : Fin (p.m - 1), j ≠ i →
            ∃ state memory',
              xc.state.followers j = .ordinary state memory' ∧
              state.status = .unoccupied ∧
              (prepared.followers.followers j).arm =
                tuple.val (followerPlayerAt j)) ∧
          (affineHash (c.2 (0, i)) wD = 0 →
            (ReferenceActiveFeedbackCut.collisionFeedbackVector prepared.arms.actions
              xc.time xc.rewards (followerPlayerAt i)).val = 0) ∧
          ReferenceActiveAffinePositiveTest.downSent xc = some wD ∧
          ∃ actualSelection : ReferenceActivePhysicalStep.Selection xc,
            prepared.coordinator.selection = some actualSelection ∧
            actualSelection.view.payload = payload ∧
            actualSelection.view.pendingAtChoice = l.pending ∧
          ReferenceActiveAffinePositiveTest.downGate xc = true ∧
          ReferenceActiveAffinePositiveTest.downDiagnosticCall
            (prepared.observeFollower i) = true ∧
          (ReferenceDownReception.ordinaryParse p rate (some wD) =
            some (payload.downRecord i)) ∧
          ReferenceDownReception.ordinaryLocalAcceptanceTest p rate xc.time old
            (some (payload.downRecord i)) ∧
          ∃ logged cut,
            ActiveFollowerLogging.checkedLogging i xc.row (xc.state.activations i) xc.time
              ((prepared.followers.followers i).arm,
                prepared.feedback.observations
                  (followerPlayerAt i)) old = .ok logged ∧
            (prepared.observeFollower i).down = some cut ∧
            cut.expectedWord = some wD ∧
            cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i xc.row xc.time
              (prepared.feedback.observations
                (followerPlayerAt i)) rate logged).2 ∧
            cut.rawComparison.isSome = true) := by
  classical
  intro E w B hshort n hn payload l saved hReady i old memory hfi hip hnone
  let x := B[n.val].input
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  have hlookup := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort n
  have hmem : B[n.val] ∈ E.records := List.mem_of_getElem? hlookup.1
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross) source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1 B[n.val] hmem
  have hrewardTable : x.rewards = rewards := hinputs.2.2
  let hReadyProof := hReady
  rcases hReady with ⟨_hReadyCoord, _hReadyPhase, _hReadySigmaPos, _hReadySigmaBound,
    hReadySigmaCutoff, hReadySigmaPayload, _hReadyCutoffPos, _hReadyCutoffBound,
    _hReadyCutoffFreeze, _hReadyFreezeBound, _hReadyFreezeGrid, hReadyCursor,
    hReadyCutoffCursor, _hReadyCursorBound, _hReadyAssignment, _hReadyBase,
    _hReadyAnchor, _hReadyPayloadN, _hReadyPending, _hReadyRegisters, _hReadyZero,
    _hReadyCutRegisters, _hReadyCurrent, _hReadyCap, _hReadyRaw, _hReadyHistory,
    _hReadyBank⟩
  have hprefixRaw := actual_first_collection_prefix_follower_domains rate source rewards
    C_star C_h count hcross s rfl hspan hshort n hn payload l saved hReadyProof
  have hprefix : ∀ j : Fin (p.m - 1),
      ∃ state memory',
        x.state.followers j = .ordinary state memory' ∧
        state.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧
        ActiveFollowerLifecycle.localBufferValid state ∧
        ActiveFollowerLifecycle.downDecoderStateValid state ∧
        state.S + state.backlog ≤ w * D p ∧
        ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
          state.lastDown = some (payload.downRecord j)) := by
    simpa [E, w, B, x] using hprefixRaw
  rcases hprefix i with ⟨rootOld, rootMemory, hrootFocal, _hrootStatus,
    _hrootValid, _hrootBuffer, _hrootDecoder, _hrootMass, _hrootLast⟩
  have hfocalEq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary rootOld rootMemory =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary old memory :=
    hrootFocal.symm.trans hfi
  injection hfocalEq with hfocalState hfocalMemory
  subst rootOld
  subst rootMemory
  let wD := CoordinatorLocalArmChoice.storedDownFlatWord payload i
  refine ⟨wD, rfl, ?_⟩
  intro c
  let xc := ReferenceLaterOptionalControlResampling.withControl x c
  let slot := PublicDiscreteDraws.slotDraw c.1
  let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
  let prepared := ReferenceActivePhysicalStep.prepare xc
  have hReadyC : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      xc payload l saved := by
    simpa [ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain,
      xc, ReferenceLaterOptionalControlResampling.withControl] using hReadyProof
  have hcurrent : xc.row.2 xc.time = c :=
    ReferenceLaterOptionalControlResampling.withControl_currentControl x c
  rcases ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
      xc payload l saved hReadyC with
    ⟨cutoff, _hcutoffStart, core, snap, _hb, _hs, hcoord, _harm, _rest⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput xc payload l clock cutoff
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  have hcutoffView : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
      snap.clockStarted.clock.u = some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
    rw [snap.clockStarted_frame.1]
    change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clock.u = _
    have hclockCutoff : clock.u = some cutoff := by
      simpa [input, ReferenceActivePhysicalStep.collectionInput] using
        snap.inputsValid.clock_cutoff_eq
    rw [hclockCutoff]
    rfl
  have hframePending : snap.clockStarted.pending = l.pending := by
    simpa [ReferenceActivePhysicalStep.collectionInput] using
      snap.clockStarted_frame.2.1
  let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
    payload := payload
    pendingAtChoice := snap.clockStarted.pending
    cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snap.clockStarted.clock.u
    complementWeights := weights }
  let actualSelection : ReferenceActivePhysicalStep.Selection xc := {
    view := view
    started := snap.clockStarted
    pending_eq := rfl
    cutoff_eq := rfl
    arm := snap.arm
    choice_eq := by
      change CoordinatorLocalArmChoice.coordinatorArmChoice payload
        snap.clockStarted.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snap.clockStarted.clock.u)
        xc.time weights xc.row = some snap.arm
      rw [hcutoffView]
      exact snap.armChoice_eq }
  have hselection : prepared.coordinator.selection = some actualSelection := by
    rw [hcoord]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection, actualSelection, view,
      clock, input, weights, hcutoffView]
  have hview : prepared.coordinator.downView = some view := by
    simp [ReferenceActivePhysicalStep.DispatchCut.downView, hselection, actualSelection]
  have hactualSelected :
      ReferenceActivePhysicalStep.upSenderIndex xc = selected := by
    simpa only [selected, hcurrent] using
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw xc
  have hframeView : actualSelection.view.payload = payload ∧
      actualSelection.view.pendingAtChoice = l.pending := by
    exact ⟨rfl, hframePending⟩
  have hlocalData : ∀ j : Fin (p.m - 1),
      ∃ state memory',
        xc.state.followers j = .ordinary state memory' ∧
        state.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid state ∧
        ActiveFollowerLifecycle.localBufferValid state ∧
        ActiveFollowerLifecycle.downDecoderStateValid state ∧
        state.S + state.backlog ≤ w * D p ∧
        ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
          state.lastDown = some (payload.downRecord j)) := by
    intro j
    rcases hprefix j with ⟨state, memory', hstate, hstatus, hvalid, hbuffer,
      hdecoder, hmass, hlastJ⟩
    have hstateC : xc.state.followers j = .ordinary state memory' := by
      simpa [xc, ReferenceLaterOptionalControlResampling.withControl] using hstate
    exact ⟨state, memory', hstateC, hstatus, hvalid, hbuffer, hdecoder, hmass, hlastJ⟩
  have hbranchGeometry :
      slot = PublicDiscreteDraws.downSlot → selected = i →
        prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
          ActiveRoundActions.sendArm
            (affineHash (c.2 (0, i)) wD)
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
            (tuple.val (followerPlayerAt i)) ∧
        prepared.arms.actions (followerPlayerAt i) =
          tuple.val (followerPlayerAt i) ∧
        (∀ j : Fin (p.m - 1), j ≠ i →
          ∃ state memory',
            xc.state.followers j = .ordinary state memory' ∧
            state.status = .unoccupied ∧
            (prepared.followers.followers j).arm =
              tuple.val (followerPlayerAt j)) ∧
        ReferenceActiveAffinePositiveTest.downSent xc = some wD ∧
        actualSelection.view.payload = payload ∧
        actualSelection.view.pendingAtChoice = l.pending ∧
        ReferenceActiveAffinePositiveTest.downGate xc = true ∧
        ReferenceActiveAffinePositiveTest.downDiagnosticCall
          (prepared.observeFollower i) = true ∧
        ReferenceDownReception.ordinaryParse p rate (some wD) =
          some (payload.downRecord i) ∧
        ReferenceDownReception.ordinaryLocalAcceptanceTest p rate xc.time old
          (some (payload.downRecord i)) ∧
        ∃ logged cut,
          ActiveFollowerLogging.checkedLogging i xc.row (xc.state.activations i) xc.time
            ((prepared.followers.followers i).arm,
              prepared.feedback.observations
                (followerPlayerAt i)) old = .ok logged ∧
          (prepared.observeFollower i).down = some cut ∧
          cut.expectedWord = some wD ∧
          cut.raw = (ActiveFollowerDownAcceptance.currentDecodeStep p i xc.row xc.time
            (prepared.feedback.observations
              (followerPlayerAt i)) rate logged).2 ∧
          cut.rawComparison.isSome = true := by
    intro hslot hselected
    have hslotRow : PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 =
        PublicDiscreteDraws.downSlot := by
      simpa [slot, hcurrent] using hslot
    have hselectedRow : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (xc.row.2 xc.time).1 = i := by
      simpa only [hcurrent] using hselected
    have hbranch : ReferenceDownReception.selectedDownSenderBranch view i xc.row xc.time := by
      refine ⟨hslotRow, hselectedRow, ?_⟩
      change i ∈ snap.clockStarted.pending
      rw [hframePending]
      exact hip
    have hsent : ReferenceActiveAffinePositiveTest.downSent xc = some wD := by
      unfold ReferenceActiveAffinePositiveTest.downSent
      rw [← prepared.coordinator_eq, hview, hactualSelected]
      simpa [wD, actualSelection, view, hselected] using
        actualSelection.expected_down_word i hbranch
    have hcoordAction : prepared.arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
          ActiveRoundActions.sendArm (affineHash (c.2 (0, i)) wD)
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
            (tuple.val (followerPlayerAt i)) := by
      have h := ReferenceActivePhysicalStep.action_eq_down_sendArm
        prepared actualSelection hselection i hbranch
      simpa [CoordinatorLocalArmChoice.currentDownHash, actualSelection, view,
        CoordinatorLocalArmChoice.downChannel, tuple, wD, hcurrent, hselected,
        followerPlayerAt_eq] using h
    have hnotdataRow : PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 ≠
        PublicDiscreteDraws.dataSlot := by
      intro h
      have hne : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot := by decide
      exact hne (hslotRow.symm.trans h)
    have hfocalSource := hlocalData i
    rcases hfocalSource with ⟨focalState, focalMemory, hfiC, hstatus, hvalid, hbuffer, hdecoder,
      _hmass, _hlastFocal⟩
    have hfocalConfiguration :
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary focalState focalMemory =
          DeclaredFollowerLocalRound.LocalConfiguration.ordinary old memory :=
      hfiC.symm.trans (by
        simpa [xc, ReferenceLaterOptionalControlResampling.withControl] using hfi)
    injection hfocalConfiguration with hfocalState hfocalMemory
    subst focalState
    subst focalMemory
    have hfocalPrep := physical_prepare_unoccupied_other xc i old memory
      (by simpa [xc, ReferenceLaterOptionalControlResampling.withControl] using hfi)
      hstatus hvalid hnotdataRow (by
        intro ⟨hup, _⟩
        have hne : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot := by decide
        exact hne (hslotRow.symm.trans hup))
    rcases hfocalPrep with ⟨focalPrepared, hfocalEq, hfocalConfig, hfocalArm⟩
    have hfocusAlignment := prepared.follower_alignment i
    rw [hfocalEq] at hfocusAlignment
    rcases hfocusAlignment with ⟨hfocalRow, hfocalIndex, hfocalTime, hfocalActivation⟩
    have hrecvAction : prepared.arms.actions
        (followerPlayerAt i) =
          tuple.val (followerPlayerAt i) := by
      calc
        prepared.arms.actions (followerPlayerAt i) =
            prepared.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
          rw [← followerPlayerAt_eq i]
        _ = (DeclaredFollowerLocalRound.prepare rate i xc.row
            (xc.state.activations i) xc.time (xc.active i) (xc.state.followers i)).arm :=
              prepared.action_follower i
        _ = (prepared.followers.followers i).arm := by
          rw [prepared.followers.followers_eq i,
            ReferenceActiveFeedbackCut.prepareFollowers_apply]
          simp [ReferenceActivePhysicalStep.followerInput,
            ReferenceActivePhysicalStep.RoundInput.row]
        _ = focalPrepared.arm := congrArg DeclaredFollowerLocalRound.PreparedRound.arm hfocalEq
        _ = tuple.val (followerPlayerAt i) := by
          rw [← followerPlayerAt_eq i]
          simpa [tuple, hcurrent] using hfocalArm
    have hotherArms : ∀ j : Fin (p.m - 1), j ≠ i →
        ∃ state memory',
          xc.state.followers j = .ordinary state memory' ∧
          state.status = .unoccupied ∧
          (prepared.followers.followers j).arm =
            tuple.val (followerPlayerAt j) := by
      intro j hji
      rcases hlocalData j with ⟨state, memory', hstate, hstatusJ, hvalidJ,
        _hbufferJ, _hdecoderJ, _hmassJ, hlastJ⟩
      have hnotselectedJ : ¬ (PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 =
          PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (xc.row.2 xc.time).1 = j) := by
        intro ⟨hup, _⟩
        have hne : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot := by decide
        exact hne (hslotRow.symm.trans hup)
      have hotherPrep := physical_prepare_unoccupied_other xc j state memory'
        hstate hstatusJ hvalidJ hnotdataRow hnotselectedJ
      rcases hotherPrep with ⟨followerPrepared, hfollowerEq, _hconfig, harm⟩
      refine ⟨state, memory', hstate, hstatusJ, ?_⟩
      have hfollowerEq' : prepared.followers.followers j = followerPrepared := by
        simpa [prepared] using hfollowerEq
      rw [hfollowerEq', ← followerPlayerAt_eq j]
      simpa [tuple, hcurrent] using harm
    have hreceiver : ReferenceActiveAffinePositiveTest.downReceiverGate i xc.row xc.time old := by
      have hregisters := hvalid.1
      change old.S ≤ p.T * D p ∧ old.delta ≤ D p ∧ old.backlog ≤ p.T * D p at hregisters
      have hdecoderDomain : ActiveFollowerDownAcceptance.decoderInputDomain p old.downBatch := by
        simpa [ActiveFollowerLifecycle.downDecoderStateValid,
          ActiveFollowerDownAcceptance.decoderInputDomain] using hdecoder
      have hbufferDomain : ActiveFollowerDownAcceptance.bufferInputDomain p old.buffer :=
        (Bandits.Support.FollowerLifecycleMeasurability.localBufferValid_iff_bufferInputDomain
          old).mp hbuffer
      refine ⟨?_, hstatus, hregisters, hdecoderDomain, hbufferDomain⟩
      unfold ActiveFollowerDownAcceptance.downSelected
      exact ⟨hslotRow, hselectedRow⟩
    have hgate : ReferenceActiveAffinePositiveTest.downGate xc = true := by
      unfold ReferenceActiveAffinePositiveTest.downGate
      dsimp only
      rw [hactualSelected, hselected]
      have hfocalEq' : prepared.followers.followers i = focalPrepared := by
        simpa [prepared] using hfocalEq
      rw [hfocalEq']
      simp [ReferenceActiveAffinePositiveTest.downPrefixGate, hfocalConfig,
        hbuffer, hreceiver]
    let own := prepared.feedback.observations
      (followerPlayerAt i)
    have hcall : ReferenceActiveAffinePositiveTest.downCallGate focalPrepared own = true := by
      rw [ReferenceActiveAffinePositiveTest.downCallGate_eq_prefix]
      rw [hfocalIndex, hfocalRow, hfocalTime, hfocalConfig]
      simp [ReferenceActiveAffinePositiveTest.downPrefixGate, hbuffer, hreceiver]
    have hdiagnostic : ReferenceActiveAffinePositiveTest.downDiagnosticCall
        (prepared.observeFollower i) = true := by
      change ReferenceActiveAffinePositiveTest.downDiagnosticCall
        (ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
          (prepared.followers.followers i) own) = true
      rw [ReferenceActiveAffinePositiveTest.finishFollower_down_call, hfocalEq]
      exact hcall
    have hlogging : ActiveFollowerLogging.checkedLogging focalPrepared.follower
        focalPrepared.row focalPrepared.activation focalPrepared.time
        (focalPrepared.arm, own) old = .ok old := by
      simpa [hfocalIndex, hfocalRow, hfocalActivation, hfocalTime, hbuffer] using
        (ReferenceActiveAffinePositiveTest.checkedLogging_eq_of_down
          i xc.row (xc.state.activations i) xc.time (focalPrepared.arm, own) old hslotRow)
    let logged := old
    have hreceiverLogged :
        ReferenceActiveAffinePositiveTest.downReceiverGate i xc.row xc.time logged := by
      exact hreceiver
    let cut := ReferenceDownReception.referenceDownCut p (some view)
      focalPrepared.follower focalPrepared.row focalPrepared.time own rate logged
    have hcutCall : cut.rawComparison.isSome = true := by
      have hcallAtCut := ReferenceActiveAffinePositiveTest.referenceDownCut_has_call
        (some view) focalPrepared.follower focalPrepared.row focalPrepared.time own logged
      simpa [cut, hfocalIndex, hfocalRow, hfocalTime, hreceiverLogged] using hcallAtCut
    have hcutCompared : cut.rawComparison ≠ none := by
      intro hnoneRaw
      rw [hnoneRaw] at hcutCall
      cases hcutCall
    have hcutExpectedBase : cut.expectedWord =
        ReferenceDownReception.expectedDownFlatWord
          (some view) focalPrepared.follower focalPrepared.row focalPrepared.time := by
      change (ReferenceDownReception.referenceDownCut p (some view)
        focalPrepared.follower focalPrepared.row focalPrepared.time own rate logged).expectedWord = _
      exact referenceDownCut_expectedWord (some view) focalPrepared.follower
        focalPrepared.row focalPrepared.time own logged
    have hcutExpected : cut.expectedWord = some wD := by
      rw [hcutExpectedBase]
      simpa [hfocalIndex, hfocalRow, hfocalTime, wD] using
        actualSelection.expected_down_word i hbranch
    have hcutRaw := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
      (some view) focalPrepared.follower focalPrepared.row focalPrepared.time own rate logged
      hcutCompared
    have hcutRaw' : cut.raw =
        (ActiveFollowerDownAcceptance.currentDecodeStep p i xc.row xc.time own rate logged).2 := by
      simpa [cut, hfocalIndex, hfocalRow, hfocalTime] using hcutRaw
    have hobsEq : prepared.observeFollower i =
        ReferenceActivePhysicalStep.finishFollower (some view) focalPrepared own := by
      change ReferenceActivePhysicalStep.finishFollower prepared.coordinator.downView
        (prepared.followers.followers i) own = _
      rw [hview]
      have hfocalEq' : prepared.followers.followers i = focalPrepared := by
        simpa [prepared] using hfocalEq
      rw [hfocalEq']
    have hfocalEq'' : prepared.followers.followers i = focalPrepared := by
      simpa [prepared] using hfocalEq
    have hrecordedDown :
        (ReferenceActivePhysicalStep.recordFollower (some view) focalPrepared.follower
          focalPrepared.row focalPrepared.activation focalPrepared.time focalPrepared.active
          focalPrepared.arm own old).down =
            some cut := by
      have h := (ReferenceActivePhysicalStep.recordFollower_logged (some view)
        focalPrepared.follower focalPrepared.row focalPrepared.activation focalPrepared.time
        focalPrepared.active focalPrepared.arm own old old hstatus hlogging).2
      simpa [cut, logged] using h
    have hobsDown : (prepared.observeFollower i).down = some cut := by
      rw [hobsEq]
      rw [finishFollower_down_eq_recordFollower (some view) focalPrepared own old memory
        hfocalConfig]
      exact hrecordedDown
    have hparse := ordinaryParse_stored_down_word payload i
    have hrecordFields := payload.downRecord_fields i
    have hdownSigma : (payload.downRecord i).val.sigma = payload.sigma.val + 1 := by
      rw [hrecordFields]
    have hdownSigmaLower := (payload.downRecord i).property
    unfold OrdinaryMessageCodec.downAdmissible at hdownSigmaLower
    rcases hdownSigmaLower with ⟨hdownSigmaLower, _hdownSigmaUpper, _⟩
    have hdownAccept : OrdinaryMessageCodec.acceptDown
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ReferencePrelaunchFollower.acceptedStart old) (xc.time.val + 1)
        (payload.downRecord i) := by
      unfold OrdinaryMessageCodec.acceptDown
      simp only [ReferencePrelaunchFollower.acceptedStart, hnone]
      constructor
      · omega
      · rw [hdownSigma]
        have hcursorX : l.cursor = xc.time.val + 1 := by
          simpa [xc, ReferenceLaterOptionalControlResampling.withControl] using hReadyCursor
        rw [← hReadySigmaPayload]
        omega
    refine ⟨hcoordAction, hrecvAction, hotherArms, hsent,
      hframeView.1, hframeView.2, hgate, hdiagnostic, ?_, ?_, ?_⟩
    · simpa [wD] using hparse
    · exact hdownAccept
    · refine ⟨logged, cut, ?_, hobsDown, hcutExpected, hcutRaw', hcutCall⟩
      simpa [own, hfocalIndex, hfocalRow, hfocalActivation, hfocalTime,
        logged, hfocalEq''] using hlogging
  constructor
  · constructor
    · intro hleft
      rcases hleft with ⟨hselected, hpositive⟩
      have hdownPositiveOriginal := hpositive
      have hformula := ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback xc
      rw [hformula] at hpositive
      have hgateBool : ReferenceActiveAffinePositiveTest.downGate xc = true :=
        (Bool.and_eq_true_iff.mp hpositive).1
      have hdownSelected :=
        ReferenceDownPhysicalHashRule.downGate_true_receiver_prepared xc hgateBool
      have hslot : slot = PublicDiscreteDraws.downSlot := by
        rcases hdownSelected with ⟨_state, _memory, _hconfiguration, _hstatus, hselectedDown⟩
        simpa [slot, hcurrent] using hselectedDown.1
      rcases hbranchGeometry hslot hselected with
        ⟨_hcoordAction, hrecvAction, _hotherArms, hsent,
          _hselectedPayload, _hpending, _hgate, _hcall, _hparse,
          _haccept, _hdiagnostic⟩
      have hpositiveFeedback : 0 <
          (ReferenceActiveFeedbackCut.collisionFeedbackVector prepared.arms.actions
            xc.time xc.rewards (followerPlayerAt i)).val := by
        have h := of_decide_eq_true (Bool.and_eq_true_iff.mp hpositive).2
        have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex xc = i :=
          hactualSelected.trans hselected
        simpa [prepared, hsenderIndex, followerPlayerAt_eq] using h
      have hcollisionFree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
          (followerPlayerAt i) := by
        by_contra hnot
        have h := hpositiveFeedback
        rw [ReferenceActiveFeedbackCut.collisionFeedbackVector_apply] at h
        simp [hnot] at h
      have hrewardVal : 0 <
          (rewards x.time (tuple.val (followerPlayerAt i))).val := by
        have h := hpositiveFeedback
        simp [ReferenceActiveFeedbackCut.collisionFeedbackVector_apply,
          hcollisionFree] at h
        rw [hrecvAction] at h
        simpa [xc, ReferenceLaterOptionalControlResampling.withControl,
          ReferenceLaterOptionalControlResampling.withControl_rewards,
          hrewardTable] using h
      have hreward : 0 <
          rewards x.time (tuple.val (followerPlayerAt i)) := by
        change 0 < (rewards x.time
          (tuple.val (followerPlayerAt i))).val
        exact hrewardVal
      have hhashRaw := ReferenceDownPhysicalHashRule.downPositive_sent_hash_one
        xc wD hsent hdownPositiveOriginal
      have hsample : ReferenceDownPhysicalHashRule.originalDownSample xc = c.2 (0, i) := by
        have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex xc = i :=
          hactualSelected.trans hselected
        unfold ReferenceDownPhysicalHashRule.originalDownSample
        rw [hcurrent]
        exact congrArg (fun j : Fin (p.m - 1) => c.2 (0, j)) hsenderIndex
      have hhash : affineHash (c.2 (0, i)) wD = 1 := by
        rw [← hsample]
        exact hhashRaw
      exact ⟨hslot, hselected, hhash, hreward⟩
    · rintro ⟨hslot, hselected, hhash, hreward⟩
      rcases hbranchGeometry hslot hselected with
        ⟨hcoordAction, hrecvAction, hotherArms, _hsent,
          _hselectedPayload, _hpending, hgate, _hcall, _hparse,
          _haccept, _hdiagnostic⟩
      have hcoordArmOne : prepared.arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) =
            tuple.val (ActiveRoundActions.coordinator p.two_le_m) := by
        rw [hcoordAction, hhash, ActiveRoundActions.sendArm_one]
      have htupleArms : ∀ j : Fin (p.m - 1),
          prepared.arms.actions (followerPlayerAt j) = tuple.val (followerPlayerAt j) := by
        intro j
        by_cases hji : j = i
        · subst j
          exact hrecvAction
        · rcases hotherArms j hji with ⟨_state, _memory, _hstate, _hstatus, harm⟩
          exact harm
      have hcollisionFree := tuple_profile_collisionFree prepared.arms.actions tuple i
        hcoordArmOne htupleArms
      have hrewardVal : 0 <
          (xc.rewards xc.time (prepared.arms.actions
            (followerPlayerAt i))).val := by
        have hrewardFin : 0 <
            xc.rewards xc.time (tuple.val (followerPlayerAt i)) := by
          simpa [xc, ReferenceLaterOptionalControlResampling.withControl_rewards,
            hrewardTable] using hreward
        change 0 < (xc.rewards xc.time
          (prepared.arms.actions (followerPlayerAt i))).val
        rw [hrecvAction]
        exact hrewardFin
      have hfeedback : 0 <
          (ReferenceActiveFeedbackCut.collisionFeedbackVector prepared.arms.actions
            xc.time xc.rewards (followerPlayerAt i)).val := by
        simpa [ReferenceActiveFeedbackCut.collisionFeedbackVector_apply,
          hcollisionFree] using hrewardVal
      have hdownPositive : ReferenceActiveAffinePositiveTest.downPositive xc = true := by
        have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex xc = i :=
          hactualSelected.trans hselected
        rw [ReferenceActiveAffinePositiveTest.downPositive_eq_gate_feedback, hgate]
        simp only [Bool.true_and]
        simpa [hsenderIndex, followerPlayerAt_eq] using decide_eq_true hfeedback
      exact ⟨hselected, hdownPositive⟩
  · rintro ⟨hslot, hselected⟩
    rcases hbranchGeometry hslot hselected with
      ⟨hcoordAction, hrecvAction, hotherArms, hsent, hpayload, hpending,
        hgate, hcall, hparse, haccept, hdiagnostic⟩
    have hzero : affineHash (c.2 (0, i)) wD = 0 →
        (ReferenceActiveFeedbackCut.collisionFeedbackVector prepared.arms.actions
          xc.time xc.rewards (followerPlayerAt i)).val = 0 := by
      intro hhash
      have hcoordZero : prepared.arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) =
            tuple.val (followerPlayerAt i) := by
        rw [hcoordAction, hhash, ActiveRoundActions.sendArm_zero]
      have hcollision : ¬ FiniteBanditModel.collisionFreeFor prepared.arms.actions
          (followerPlayerAt i) := by
        intro hfree
        have hne : ActiveRoundActions.coordinator p.two_le_m ≠ followerPlayerAt i := by
          rw [← followerPlayerAt_eq i]
          exact (ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m
            (followerIndexOfFin i)).symm
        exact (hfree _ hne) (hcoordZero.trans hrecvAction.symm)
      rw [ReferenceActiveFeedbackCut.collisionFeedbackVector_apply]
      simp only [hcollision, ite_false, Fin.val_zero]
    exact ⟨hcoordAction, hrecvAction, hotherArms, hzero, hsent, actualSelection, hselection,
      hpayload, hpending, hgate, hcall, hparse, haccept, hdiagnostic⟩

end Bandits.Support.ReferenceFirstCollectionDownControlGeometry

end
