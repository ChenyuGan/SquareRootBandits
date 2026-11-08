/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionReadyStep
public import Bandits.Support.ReferenceContinuingCollectionFollowerPreparation
public import Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw
public import Bandits.Support.ReferenceGeneratedFirstCollectionFollowerPrefix

import Lean.Elab.Tactic.Omega

/-!
# First-collection control geometry

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124,193-240`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-296,327-348,459-490`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

This module uses the actual first-collection run and the proved original-prefix
follower boundary. Its control conclusions are local operation identities for
an explicit ready branch. It introduces no service law, probability bound, or
manuscript closure.
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

namespace Bandits.Support.ReferenceFirstCollectionControlGeometry

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
  let launch := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
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
          ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross :=
      Option.some.inj (hactual.symm.trans hgenerated)
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
  have hprefixRaw := ReferenceGeneratedFirstCollectionFollowerPrefix.actual_first_collection_follower_prefix_boundary
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
  have hwindowState : x.state = (prefixAt (n.val - 1) (Nat.le_of_lt hjTail)).finalState := by
    have hendpoints := ReferenceFirstCollectionReadyStep.actual_collection_window_prefix_endpoints
      rate source rewards C_star C_h count hcross
      (by simpa [start] using hspan) hshort n
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
      state.S + state.backlog ≤ w * D p ∧
      ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
        state.lastDown = some (payload.downRecord j))
  intro j
  rcases hboundaryAt.2 j with
    ⟨state, memory, hstate, hstatus, hdomain, _hbuffer, _hdecoder,
      _hS, _hdelta, _hbacklog, hmass, _hstamps, _hnodup, _hquantized,
      _hpairwise, _hcalendar, _hpending, _hcompleted, hlast⟩
  refine ⟨state, memory, ?_, hstatus, hdomain, ?_, ?_⟩
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
  rcases hregisters with ⟨hS, hdelta, hbacklog⟩
  rcases (Bandits.Support.FollowerLifecycleMeasurability.localBufferValid_iff_bufferInputDomain
    state).mp hbuffer with
    ⟨hstamps, hkeys⟩
  refine ⟨hS, hdelta, hbacklog, ?_, ?_⟩
  · intro record hrecord
    exact ⟨(hstamps record hrecord).1, (hstamps record hrecord).2.1⟩
  · exact hkeys

private theorem actual_upOfferFields_admissible
    (payload : Payload rate) (j : Fin (p.m - 1))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid old)
    (hlast : (old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
      old.lastDown = some (payload.downRecord j)) :
    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields old) := by
  rcases hvalid with ⟨hregisters, _hbuffer, _hdecoder⟩
  change old.S ≤ p.T * D p ∧ old.delta ≤ D p ∧ old.backlog ≤ p.T * D p at hregisters
  rcases hlast with ⟨hnone, hS, hdelta, hbacklog⟩ | hsome
  · simp [OrdinaryMessageCodec.upAdmissible, OrdinaryMessageCodec.upPlaceholder,
      ActiveFollowerQueueOperation.upOfferFields, ReferencePrelaunchFollower.acceptedStart,
      hnone, hS, hdelta, hbacklog]
  · have hrecord := (payload.downRecord j).property
    unfold OrdinaryMessageCodec.downAdmissible at hrecord
    rcases hrecord with ⟨hsigmaLo, hsigmaHi, _⟩
    unfold OrdinaryMessageCodec.upAdmissible ActiveFollowerQueueOperation.upOfferFields
    simp only [ReferencePrelaunchFollower.acceptedStart, hsome]
    exact Or.inr ⟨hsigmaLo, hsigmaHi, hregisters.1, hregisters.2.1, hregisters.2.2⟩

private theorem follower_prepare_local_control_cases
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstatus : old.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid old)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields old)) :
    let prepared := DeclaredFollowerLocalRound.prepare rate i row activation t hactive
      (.ordinary old memory)
    prepared.configuration = .ordinary old memory ∧
    (∀ _hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t,
      ∃ offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old =
          .offer offered ∧ offered.val = ActiveFollowerQueueOperation.upOfferFields old ∧
        prepared.arm = ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 t) i offered)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
            (ActiveRoundActions.coordinator p.two_le_m))) ∧
    (¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old = .noOffer ∧
      ActiveFollowerArmChoice.followerArmChoice old row t i none = some prepared.arm) ∧
    (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot →
      prepared.arm = PublicDiscreteDraws.pilotDraw (K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 t).1) ∧
    (PublicDiscreteDraws.slotDraw (row.2 t).1 ≠ PublicDiscreteDraws.dataSlot →
      ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t →
      prepared.arm = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  classical
  let prepared := DeclaredFollowerLocalRound.prepare rate i row activation t hactive
    (.ordinary old memory)
  have hstateInput := follower_stateInputDomain_of_localStateDomainValid old hvalid
  have hstart : ActiveFollowerLifecycle.startRound rate.eta t old memory = .ok (old, memory) :=
    ActiveFollowerLifecycle.startRound_unoccupied rate.eta t old memory hvalid hstatus
  let offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields old, hadmissible⟩
  have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t →
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old = .noOffer := by
    intro hnot
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row activation t old
      hstateInput
    intro hselected
    exact hnot hselected.1
  have hselectedOffer : ∀ hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t,
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t old = .offer offered := by
    intro hselected
    simp [ActiveFollowerQueueOperation.checkedUpOffer, hstateInput, hselected, hstatus,
      hadmissible, offered]
  have hconfig : prepared.configuration = .ordinary old memory := by
    by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot
    · have hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t := by
        intro hselected
        have hne : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by decide
        exact hne (hdata.symm.trans hselected.2.1)
      have hoff := hnotSelected hnot
      have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data old
        (row.2 t) i none hstatus hdata
      have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i none =
          some (PublicDiscreteDraws.pilotDraw (K_pos p)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) (row.2 t).1) := by
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
        rate i row activation t hactive old old memory memory hstart hoff).2 _ hchoice
      exact hpreparedArm.2
    · by_cases hup : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i
      · have hselected : ActiveFollowerQueueOperation.selectedUpRound i row activation t :=
          ⟨hactive, hup.1, hup.2⟩
        have hoff := hselectedOffer hselected
        have hvalidChoice : ActiveFollowerArmChoice.upStateDomain old ∧
            ActiveFollowerArmChoice.offeredUpMatchesState old offered := by
          constructor
          · exact ⟨hstateInput.1, hstateInput.2.1, hstateInput.2.2.1⟩
          · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
              ActiveFollowerQueueOperation.upOfferFields]
        have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
          old (row.2 t) i offered hstatus hup.1 hup.2 hvalidChoice
        have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i (some offered) =
            some (ActiveRoundActions.sendArm
              (ActiveFollowerArmChoice.offeredUpBit rate.eta (row.2 t) i offered)
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
                (ActiveRoundActions.coordinator p.two_le_m))) := by
          rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
          exact hcore
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_offer_arm_equation
          rate i row activation t hactive old old memory memory hstart offered hoff).2 _ hchoice
        exact hpreparedArm.2
      · have hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t := by
          intro hselected
          exact hup ⟨hselected.2.1, hselected.2.2⟩
        have hoff := hnotSelected hnot
        have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other old
          (row.2 t) i none hstatus (by simp [hdata]) hup
        have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i none =
            some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
          rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
          exact hcore
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
          rate i row activation t hactive old old memory memory hstart hoff).2 _ hchoice
        exact hpreparedArm.2
  refine ⟨hconfig, ?_, ?_, ?_, ?_⟩
  · intro hselected
    have hoff := hselectedOffer hselected
    have hvalidChoice : ActiveFollowerArmChoice.upStateDomain old ∧
        ActiveFollowerArmChoice.offeredUpMatchesState old offered := by
      constructor
      · exact ⟨hstateInput.1, hstateInput.2.1, hstateInput.2.2.1⟩
      · simp [ActiveFollowerArmChoice.offeredUpMatchesState, offered,
          ActiveFollowerQueueOperation.upOfferFields]
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
      old (row.2 t) i offered hstatus hselected.2.1 hselected.2.2 hvalidChoice
    have hchoice := (ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i
      (some offered)).trans hcore
    have hpreparedArm := (DeclaredFollowerLocalRound.prepare_offer_arm_equation
      rate i row activation t hactive old old memory memory hstart offered hoff).2 _ hchoice
    exact ⟨offered, hoff, rfl, hpreparedArm.1⟩
  · intro hnot
    have hoff := hnotSelected hnot
    have hchoice : ActiveFollowerArmChoice.followerArmChoice old row t i none =
        some prepared.arm := by
      by_cases hdata : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.dataSlot
      · have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data old
          (row.2 t) i none hstatus hdata
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
          rate i row activation t hactive old old memory memory hstart hoff).2 _ hcore
        rw [hpreparedArm.1]
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
      · have hup : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) := by
          intro h
          exact hnot ⟨hactive, h.1, h.2⟩
        have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other old
          (row.2 t) i none hstatus hdata hup
        have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
          rate i row activation t hactive old old memory memory hstart hoff).2 _ hcore
        rw [hpreparedArm.1]
        rw [ActiveFollowerArmChoice.followerArmChoice_eq_core]
        exact hcore
    exact ⟨hoff, hchoice⟩
  · intro hdata
    have hnot : ¬ ActiveFollowerQueueOperation.selectedUpRound i row activation t := by
      intro hselected
      have hne : PublicDiscreteDraws.dataSlot ≠ PublicDiscreteDraws.upSlot := by decide
      exact hne (hdata.symm.trans hselected.2.1)
    have hoff := hnotSelected hnot
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data old
      (row.2 t) i none hstatus hdata
    have hchoice := (ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i none).trans hcore
    have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
      rate i row activation t hactive old old memory memory hstart hoff).2 _ hchoice
    exact hpreparedArm.1
  · intro hnotData hnotSelectedRound
    have hoff := hnotSelected hnotSelectedRound
    have hnotUp : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 =
        PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) := by
      intro hup
      exact hnotSelectedRound ⟨hactive, hup.1, hup.2⟩
    have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other old
      (row.2 t) i none hstatus hnotData hnotUp
    have hchoice := (ActiveFollowerArmChoice.followerArmChoice_eq_core old row t i none).trans hcore
    have hpreparedArm := (DeclaredFollowerLocalRound.prepare_no_offer_arm_equation
      rate i row activation t hactive old old memory memory hstart hoff).2 _ hchoice
    exact hpreparedArm.1

/-- Lift the accepted local PREPARE equations to the one actual physical
preparation. The ordinary state, unoccupied status, full local domain, and
codec admissibility are explicit conditional inputs; the actual root below
produces them from G. No statement is made about arbitrary dagger inputs. -/
private theorem physical_prepare_unoccupied
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hstate : x.state.followers i = .ordinary old memory)
    (hstatus : old.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localStateDomainValid old)
    (hadmissible : OrdinaryMessageCodec.upAdmissible
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ActiveFollowerQueueOperation.upOfferFields old)) :
    let prepared := ReferenceActivePhysicalStep.prepare x
    (prepared.followers.followers i).configuration = .ordinary old memory ∧
    (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 x.time).1 = i →
      ∃ offered : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
        ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
          (x.state.activations i) x.time old = .offer offered ∧
        offered.val = ActiveFollowerQueueOperation.upOfferFields old ∧
        (prepared.followers.followers i).arm = ActiveRoundActions.sendArm
          (ActiveFollowerArmChoice.offeredUpBit rate.eta (x.row.2 x.time) i offered)
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (PublicDiscreteDraws.followerPlayer p.two_le_m i))
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
            (ActiveRoundActions.coordinator p.two_le_m))) ∧
    (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠ PublicDiscreteDraws.dataSlot →
      ¬ ActiveFollowerQueueOperation.selectedUpRound i x.row (x.state.activations i) x.time →
      (prepared.followers.followers i).arm =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := by
  have hc := follower_prepare_local_control_cases i x.row
    (x.state.activations i) x.time (x.active i) old memory hstatus hvalid hadmissible
  have hp : (ReferenceActivePhysicalStep.prepare x).followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
        x.time (x.active i) (.ordinary old memory) := by
    rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq i]
    change DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
      x.time (x.active i) (x.state.followers i) = _
    rw [hstate]
  dsimp only
  rw [hp]
  exact ⟨hc.1, fun h => hc.2.1 ⟨x.active i, h.1, h.2⟩, hc.2.2.2.2⟩

private theorem upSent_of_checked_offer
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (i : Fin (p.m - 1))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = i)
    (hconfig : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary old memory)
    (hchecked : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row
      (x.state.activations i) x.time old = .offer U) :
    ReferenceActiveAffinePositiveTest.upSent x =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  have halign := prepared.follower_alignment i
  have hlocal : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
      (prepared.followers.followers i).follower (prepared.followers.followers i).row
      (prepared.followers.followers i).activation (prepared.followers.followers i).time
      old = .offer U := by
    rw [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2]
    exact hchecked
  have hw := ReferenceUpReception.currentOfferWord_eq_encoded_offer rate
    x.row i x.time (prepared.followers.followers i)
    halign.1 halign.2.1 halign.2.2.1 old memory hconfig U hlocal
  have hi : ReferenceActivePhysicalStep.upSenderIndex x = i :=
    (ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw x).trans hselected
  cases hi
  exact hw

private theorem actual_coordinator_arm_tuple_on_up
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (snap : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (hb : snap.clockStarted.clock.g ≤ p.T + 1)
    (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) = true)
    (hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock cutoff (.continuing core snap hb hs))
    (hslot : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.upSlot) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.arm =
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 x.time).1).val
        (ActiveRoundActions.coordinator p.two_le_m) := by
  have harm : (ReferenceActivePhysicalStep.prepare x).coordinator.arm = snap.arm := by
    rw [hcoord]
    exact ReferenceActivePhysicalStep.collection_arm_equation payload ledger clock cutoff
      (.continuing core snap hb hs)
  have hpendingNe : snap.clockStarted.pending ≠ ∅ := by
    intro h
    have hframePending : snap.clockStarted.pending = ledger.pending := by
      simpa [ReferenceActivePhysicalStep.collectionInput] using
        snap.clockStarted_frame.2.1
    have hpending : snap.clockStarted.pending.Nonempty := by
      rw [hframePending]
      exact snap.inputsValid.pending_nonempty
    rw [h] at hpending
    simp at hpending
  have hnotFast :
      ¬ (CoordinatorLocalArmChoice.assignmentIsLive payload
          (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) x.time ∧
        snap.clockStarted.pending = ∅) := by
    intro h
    exact hpendingNe h.2
  have hnotData : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 ≠
      PublicDiscreteDraws.dataSlot := by
    intro h
    have hne : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.dataSlot := by decide
    exact hne (hslot.symm.trans h)
  have hnotDown : ¬ (PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 =
      PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1 ∈ snap.clockStarted.pending) := by
    intro h
    have hne : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.downSlot := by decide
    exact hne (hslot.symm.trans h.1)
  have hcore := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_other
    payload snap.clockStarted.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) x.time
    (CoordinatorCollectionInteractive.PreObservationInputs.weights
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
      snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq)
    (x.row.2 x.time) snap.inputsValid.choice_valid hnotFast hnotData hnotDown
  have hchoice := snap.armChoice_eq
  have hchoiceCore : CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload
      snap.clockStarted.pending
      (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) x.time
      (CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
        snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq)
      (x.row.2 x.time) = some snap.arm := by
    simpa [CoordinatorLocalArmChoice.coordinatorArmChoice,
      ReferenceActivePhysicalStep.collectionInput] using hchoice
  rw [hcore] at hchoiceCore
  exact harm.trans (Option.some.inj hchoiceCore).symm

private theorem coordinator_observation_positive_iff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (arm : Fin p.K)
    (ha : prepared.arms.actions (ActiveRoundActions.coordinator p.two_le_m) = arm) :
    (0 < CoordinatorUpReception.roundedObservationValue p prepared.coordinatorObservation) ↔
      FiniteBanditModel.collisionFreeFor prepared.arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) ∧ 0 < x.rewards x.time arm := by
  classical
  have hD : (0 : ℝ) < (D p : ℝ) := by exact_mod_cast D_pos p
  have hpos : (0 < CoordinatorUpReception.roundedObservationValue p
      prepared.coordinatorObservation) ↔
      0 < (prepared.feedback.feedback (ActiveRoundActions.coordinator p.two_le_m)).val := by
    rw [CoordinatorUpReception.roundedObservationValue,
      ReferenceActivePhysicalStep.PreparedRound.coordinatorObservation,
      div_pos_iff_of_pos_right hD]
    exact Nat.cast_pos
  rw [hpos, prepared.feedback_rule]
  by_cases hfree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
      (ActiveRoundActions.coordinator p.two_le_m)
  · rw [ite_eq_left hfree, ha]
    simp only [hfree, true_and]
    rfl
  · rw [ite_eq_right hfree]
    simp only [Fin.val_zero, Nat.lt_irrefl, hfree, false_and]

private theorem continuing_siteLedger
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (snap : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (hb : snap.clockStarted.clock.g ≤ p.T + 1)
    (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) = true)
    (hcoord : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock cutoff (.continuing core snap hb hs))
    (o : CoordinatorRecordingOperation.Output p) (lc : Ledger rate)
    (hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) payload snap.clockStarted
        (CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
          snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq)) = some o)
    (hstart : CoordinatorCollectionLedger.startRound ledger
      (CoordinatorCollectionLedger.sourceRound x.time)
      (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success lc) :
    ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := x) = some lc := by
  classical
  have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection ≠ none := by
    rw [hcoord]
    dsimp only [ReferenceActivePhysicalStep.DispatchCut.selection]
    intro h
    cases h
  dsimp only [ReferenceCoordinatorUpPhysicalCall.siteLedger?]
  rw [dite_eq_right hselection]
  simp only [hcoord]
  unfold ReferenceCoordinatorUpPhysicalCall.tailLedger?
  rw [hrecord]
  change (match CoordinatorCollectionLedger.startRound ledger
    (CoordinatorCollectionLedger.sourceRound x.time)
    (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) with
    | .success l => some l
    | .invalid => none
    | .rejected _ => none) = some lc
  rw [hstart]

/-- On the actual first-collection run, every optional resampling of the
current time control has the literal continuing collection call and the
coordinator UP positivity event is exactly the selected sender's hash-one,
positive-reward event. The follower facts come from the original generated
prefix, and the local ready input is unchanged by resampling.
Sources: 05_binary_transport.tex:20-53,70-124,193-240;
06_interruptions.tex:164-177,246-296,327-348,459-490;
07_public_setup.tex:127-164; appendix_a_local_protocol.tex:92-157. -/
theorem actual_first_collection_control_geometry
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (hspan : s + count ≤ p.T)
    :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count
      (by simpa only [hsElapsed] using hspan)
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
      (_hip : i ∈ l.pending)
      (_hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart old),
    let x := B[n.val].input
    let t := x.time
    ∃ U : OrdinaryMessageCodec.UpRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta),
      U.val = ActiveFollowerQueueOperation.upOfferFields old ∧
      1 ≤ U.val.sigma ∧
      ∀ c : ContinuousLearningRows.TimeControl p,
        let xc := ReferenceLaterOptionalControlResampling.withControl x c
        let slot := PublicDiscreteDraws.slotDraw c.1
        let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1
        let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
        let prepared := ReferenceActivePhysicalStep.prepare xc
        ((selected = i ∧ ReferenceActiveAffinePositiveTest.upPositive xc = true) ↔
          slot = PublicDiscreteDraws.upSlot ∧ selected = i ∧
            affineHash (c.2 (1, i)) (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
            0 < rewards t (tuple.val (ActiveRoundActions.coordinator p.two_le_m))) ∧
        (∀ j : Fin (p.m - 1),
          ∃ state memory',
            xc.state.followers j = .ordinary state memory' ∧
            state.status = .unoccupied ∧
            ActiveFollowerLifecycle.localStateDomainValid state ∧
            state.S + state.backlog ≤ w * D p ∧
            ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
              state.lastDown = some (payload.downRecord j)) ∧
            (prepared.followers.followers j).configuration = .ordinary state memory') ∧
        (slot = PublicDiscreteDraws.upSlot ∧ selected = i →
          prepared.coordinator.arm = tuple.val (ActiveRoundActions.coordinator p.two_le_m) ∧
          (prepared.followers.followers i).configuration = .ordinary old memory ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xc.row
            (xc.state.activations i) xc.time old = .offer U ∧
          (prepared.followers.followers i).arm = ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
            (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) ∧
          ∀ j : Fin (p.m - 1), j ≠ i →
            ∃ state memory',
              xc.state.followers j = .ordinary state memory' ∧
              state.status = .unoccupied ∧
              (prepared.followers.followers j).configuration = .ordinary state memory' ∧
              (prepared.followers.followers j).arm =
                tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j)) ∧
        (∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
          let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
          let input := ReferenceActivePhysicalStep.collectionInput xc payload l clock cutoff
          ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
            (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
            (hb : snap.clockStarted.clock.g ≤ p.T + 1)
            (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true),
          let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
            snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
          let recordingInput := ReferenceActivePhysicalStep.collectionRecordingInput prepared
            payload snap.clockStarted weights
          prepared.coordinator =
              .collection payload l clock cutoff (.continuing core snap hb hs) ∧
          prepared.coordinator.arm = snap.arm ∧
          CoordinatorRecorderComplementBridge.LocalInputsValid recordingInput ∧
          CoordinatorRecordingOperation.InputsValid
            (CoordinatorRecorderComplementBridge.recorderInput recordingInput) ∧
          ∃ (o : CoordinatorRecordingOperation.Output p) (lc : Ledger rate),
            CoordinatorRecorderComplementBridge.run recordingInput = some o ∧
            let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o
            CoordinatorCollectionLedger.startRound l
                (CoordinatorCollectionLedger.sourceRound xc.time)
                (ReferenceActivePhysicalStep.collectionEnabled l xc.time) raw =
              .success lc ∧
            CoordinatorCollectionLedger.validLedgerCheck lc = true ∧
            lc.phase = .started ∧
            lc.cursor = xc.time.val + 1 ∧
            lc.pending = l.pending ∧
            prepared.observeCoordinator =
              ReferenceActivePhysicalStep.collectionFinish (x := xc) payload
                snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared lc) ∧
            prepared.observeCoordinator.up =
              (ReferenceActivePhysicalStep.receiveUp prepared lc).diagnostic) ∧
        (∃ lc : Ledger rate,
          let receptionInput := ReferenceUpReception.receptionInputAtRow rate xc.row
            (ReferenceActivePhysicalStep.upInputs prepared lc) xc.time
          CoordinatorUpReception.receptionInputDomain receptionInput ∧
          CoordinatorUpReception.receptionInputCheck receptionInput = true ∧
          ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := xc) = some lc) ∧
        Function.Injective tuple.val := by
  classical
  intro E w B hshort n hn payload l saved hReady i old memory hfi hip hpositive
  let x := B[n.val].input
  let t := x.time
  have hlookup := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross
    (by simpa only [hsElapsed] using hspan) hshort n
  have hmem : B[n.val] ∈ E.records := List.mem_of_getElem? hlookup.1
  have hinputs := ReferenceActivePhysicalHorizon.run_record_inputs
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross) source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    count (by simpa only [hsElapsed] using hspan)
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1 B[n.val] hmem
  have hrewardTable : x.rewards = rewards := hinputs.2.2
  let hReadyProof := hReady
  rcases hReady with ⟨_hReadyCoord, _hReadyPhase, hReadySigmaPos, _hReadySigmaBound,
    _hReadySigmaCutoff, _hReadySigmaPayload, hReadyCutoffPos, _hReadyCutoffBound,
    _hReadyCutoffFreeze, _hReadyFreezeBound, _hReadyFreezeGrid, hReadyCursor,
    hReadyCutoffCursor, _hReadyCursorBound, _hReadyAssignment, _hReadyBase,
    _hReadyAnchor, _hReadyPayloadN, _hReadyPending, _hReadyRegisters, _hReadyZero,
    _hReadyCutRegisters, _hReadyCurrent, _hReadyCap, _hReadyRaw, _hReadyHistory, hReadyBank⟩
  have hprefix := actual_first_collection_prefix_follower_domains rate source rewards
    C_star C_h count hcross s hsElapsed hspan hshort n hn payload l saved hReadyProof
  rcases hprefix i with ⟨rootOld, rootMemory, hrootFocal, hrootStatus,
    hrootValid, _hrootMass, hrootLast⟩
  have hfocalEq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary rootOld rootMemory =
      DeclaredFollowerLocalRound.LocalConfiguration.ordinary old memory :=
    hrootFocal.symm.trans hfi
  injection hfocalEq with hfocalState hfocalMemory
  subst rootOld
  subst rootMemory
  have hadmissible := actual_upOfferFields_admissible payload i old hrootValid hrootLast
  let U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta) :=
    ⟨ActiveFollowerQueueOperation.upOfferFields old, hadmissible⟩
  have hUval : U.val = ActiveFollowerQueueOperation.upOfferFields old := rfl
  refine ⟨U, hUval, ?_, ?_⟩
  · simpa [U, ActiveFollowerQueueOperation.upOfferFields] using hpositive
  · intro c
    let xc := ReferenceLaterOptionalControlResampling.withControl x c
    let slot := PublicDiscreteDraws.slotDraw c.1
    let selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1
    let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1
    let prepared := ReferenceActivePhysicalStep.prepare xc
    have hReadyC : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        xc payload l saved := by
      simpa [ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain,
        xc, ReferenceLaterOptionalControlResampling.withControl] using hReadyProof
    have hcurrent : xc.row.2 xc.time = c := by
      exact ReferenceLaterOptionalControlResampling.withControl_currentControl x c
    have hdrawControl : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (xc.row.2 xc.time).1 = selected := by
      rw [hcurrent]
    have hfollowers : ∀ j : Fin (p.m - 1),
        ∃ state memory',
          xc.state.followers j = .ordinary state memory' ∧
          state.status = .unoccupied ∧
          ActiveFollowerLifecycle.localStateDomainValid state ∧
          state.S + state.backlog ≤ w * D p ∧
          ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
            state.lastDown = some (payload.downRecord j)) ∧
          (prepared.followers.followers j).configuration = .ordinary state memory' := by
      intro j
      rcases hprefix j with ⟨state, memory', hstate, hstatus, hvalid, hmass, hlast⟩
      have hstateC : xc.state.followers j = .ordinary state memory' := by
        simpa [xc] using hstate
      have hadm := actual_upOfferFields_admissible payload j state hvalid hlast
      have hprepLocal := physical_prepare_unoccupied xc j state memory'
        hstateC hstatus hvalid hadm
      refine ⟨state, memory', hstateC, hstatus, hvalid, ?_, hlast, hprepLocal.1⟩
      simpa [w] using hmass
    have hstateI : xc.state.followers i = .ordinary old memory := hfi
    have hcasesI := physical_prepare_unoccupied xc i old memory hstateI
      hrootStatus hrootValid hadmissible
    have hclockAndInput := ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
      xc payload l saved hReadyC
    rcases hclockAndInput with ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm,
      hlocal, hrecorderInputs, o, lc, hrecord, hstart, hcand, hvalid, hphase,
      hcursor, hσ, hcutoffStart, hfreeze, hpendingStart, hassignmentStart,
      hbaseStart, hcutRegisters, hincrement, htransition, hconservation, hfrozen,
      hrawNone, hunknown, hmass, hcurrentBound, hcutBounds, hpendingZero,
      hgammaBounds, hcutScoreBounds, hrawBounds, hhistory, hrawBufferEq,
      hrawOther, hfresh, hfutureFresh, hobserve, hrecorded, hdiagnostic⟩
    let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
      (ReferenceActivePhysicalStep.collectionInput xc payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
      snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
    have hdiag : prepared.observeCoordinator.up =
        (ReferenceActivePhysicalStep.receiveUp prepared lc).diagnostic := by
      calc
        prepared.observeCoordinator.up =
            (ReferenceActivePhysicalStep.collectionFinish (x := xc) payload
              snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared lc)).up := by
          rw [hobserve]
        _ = (ReferenceActivePhysicalStep.receiveUp prepared lc).diagnostic :=
          ReferenceActiveAffinePositiveTest.collectionFinish_up xc payload
            snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp prepared lc)
    let receptionInput := ReferenceUpReception.receptionInputAtRow rate xc.row
      (ReferenceActivePhysicalStep.upInputs prepared lc) xc.time
    have hbankCheck : CoordinatorUpReception.decoderBankCheck p xc.state.upDecoderBank = true := by
      apply (CoordinatorUpReception.decoderBankCheck_eq_true_iff p xc.state.upDecoderBank).2
      intro j
      exact ⟨(hReadyBank j).1, (hReadyBank j).2.1⟩
    have hsigmaPositive : 1 ≤ lc.sigma := by rw [hσ]; exact hReadySigmaPos
    have hcutoffPositive : 1 ≤ lc.cutoff := by
      rw [hcutoffStart]
      exact hReadyCutoffPos
    have hcursorLedger : lc.cursor =
        CoordinatorCollectionLedger.sourceRound xc.time := by
      simpa [CoordinatorCollectionLedger.sourceRound] using hcursor
    have hcutoffCursor : lc.cutoff ≤ lc.cursor := by
      calc
        lc.cutoff = l.cutoff := hcutoffStart
        _ ≤ l.cursor := Nat.le_of_lt hReadyCutoffCursor
        _ = CoordinatorCollectionLedger.sourceRound xc.time := by
          simpa [CoordinatorCollectionLedger.sourceRound, xc] using hReadyCursor
        _ = lc.cursor := hcursorLedger.symm
    have hcursorBound : lc.cursor ≤ p.T := by
      rw [hcursorLedger]
      exact Nat.succ_le_of_lt xc.time.isLt
    have hcursorReception : lc.cursor =
        CoordinatorCollectionLedger.sourceRound receptionInput.time := by
      simpa [receptionInput, ReferenceUpReception.receptionInputAtRow,
        CoordinatorUpMeasurability.receptionInputAtRow,
        ReferenceActivePhysicalStep.upInputs,
        CoordinatorCollectionLedger.sourceRound] using hcursorLedger
    have hreceptionDomain : CoordinatorUpReception.receptionInputDomain receptionInput :=
      ⟨hvalid, hsigmaPositive, hphase, hcutoffPositive, hcutoffCursor,
        hcursorBound, hcursorReception, hbankCheck⟩
    have hcheck : CoordinatorUpReception.receptionInputCheck receptionInput = true :=
      (CoordinatorUpReception.receptionInputCheck_eq_true_iff receptionInput).2 hreceptionDomain
    have hgate_of_up : slot = PublicDiscreteDraws.upSlot ∧ selected = i →
        CoordinatorUpReception.receptionGate receptionInput := by
      rintro ⟨hslot, hselected⟩
      have hslotInput : receptionInput.slot = PublicDiscreteDraws.upSlot := by
        change PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 =
          PublicDiscreteDraws.upSlot
        rw [hcurrent]
        exact hslot
      have hselectedInput : receptionInput.selectedFollower = i := by
        change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (xc.row.2 xc.time).1 = i
        rw [hcurrent]
        exact hselected
      have hmember : i ∈ lc.pending := by rw [hpendingStart]; exact hip
      refine ⟨?_, hslotInput, hselectedInput ▸ hmember⟩
      calc
        lc.cutoff ≤ lc.cursor := hcutoffCursor
        _ = CoordinatorCollectionLedger.sourceRound receptionInput.time := hcursorReception
    have hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := xc) = some lc :=
      continuing_siteLedger xc payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
        core snap hb hs hcoord o lc hrecord hstart
    have hUpFormula : ReferenceActiveAffinePositiveTest.upPositive xc =
        (CoordinatorUpReception.receptionInputCheck receptionInput &&
          decide (AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput receptionInput))) := by
      unfold ReferenceActiveAffinePositiveTest.upPositive
      rw [hdiag]
      exact ReferenceActiveAffinePositiveTest.receiveUp_positive prepared lc
    have hcoordArmOnUp := actual_coordinator_arm_tuple_on_up xc payload l
      (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff
      core snap hb hs hcoord
    have hpreparedUpFacts :
        (slot = PublicDiscreteDraws.upSlot ∧ selected = i) →
          prepared.coordinator.arm = tuple.val (ActiveRoundActions.coordinator p.two_le_m) ∧
          (prepared.followers.followers i).configuration = .ordinary old memory ∧
          ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xc.row
            (xc.state.activations i) xc.time old = .offer U ∧
          (prepared.followers.followers i).arm = ActiveRoundActions.sendArm
            (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
            (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) ∧
          ∀ j : Fin (p.m - 1), j ≠ i →
            ∃ state memory',
              xc.state.followers j = .ordinary state memory' ∧
              state.status = .unoccupied ∧
              (prepared.followers.followers j).configuration = .ordinary state memory' ∧
              (prepared.followers.followers j).arm =
                tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j) := by
      rintro ⟨hslot, hselected⟩
      obtain ⟨offered, hchecked, hfields, hlocalArm⟩ := hcasesI.2.1
        ⟨by simpa only [hcurrent] using hslot, by simpa only [hcurrent] using hselected⟩
      have hU : offered = U := Subtype.ext (hfields.trans hUval.symm)
      have hcheckedU : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i xc.row
          (xc.state.activations i) xc.time old = .offer U := hU ▸ hchecked
      have hfocalConfig := hcasesI.1
      have hfocalArm : (prepared.followers.followers i).arm =
          ActiveRoundActions.sendArm (ActiveFollowerArmChoice.offeredUpBit rate.eta c i U)
            (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) := by
        simpa only [hcurrent, hU] using hlocalArm
      have hcoordArm : prepared.coordinator.arm =
          tuple.val (ActiveRoundActions.coordinator p.two_le_m) := by
        simpa only [hcurrent] using hcoordArmOnUp (by simpa only [hcurrent] using hslot)
      refine ⟨hcoordArm, hfocalConfig, hcheckedU, hfocalArm, ?_⟩
      intro j hji
      rcases hprefix j with ⟨state, memory', hstate, hstatus, hvalidJ, _hmass, hlastJ⟩
      have hstateC : xc.state.followers j = .ordinary state memory' := by
        simpa [xc] using hstate
      have hadmJ := actual_upOfferFields_admissible payload j state hvalidJ hlastJ
      have hcasesJ := physical_prepare_unoccupied xc j state memory'
        hstateC hstatus hvalidJ hadmJ
      have hnotSelected : ¬ ActiveFollowerQueueOperation.selectedUpRound j xc.row
          (xc.state.activations j) xc.time := by
        intro hsJ
        have hdrawEq : i = j := (hdrawControl.trans hselected).symm.trans hsJ.2.2
        exact hji hdrawEq.symm
      have hnotData : PublicDiscreteDraws.slotDraw (xc.row.2 xc.time).1 ≠
          PublicDiscreteDraws.dataSlot := by
        rw [hcurrent]
        intro heq
        have hne : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.dataSlot := by decide
        exact hne (hslot.symm.trans heq)
      have hotherArm := hcasesJ.2.2 hnotData hnotSelected
      refine ⟨state, memory', hstateC, hstatus, hcasesJ.1, ?_⟩
      simpa only [hcurrent] using hotherArm
    have hrewardPositive_of_observation
        (hslot : slot = PublicDiscreteDraws.upSlot)
        (hobs : 0 < CoordinatorUpReception.roundedObservationValue p
          prepared.coordinatorObservation) :
        0 < rewards t (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) := by
      have hcoordArm : prepared.coordinator.arm =
          tuple.val (ActiveRoundActions.coordinator p.two_le_m) := by
        simpa only [hcurrent] using hcoordArmOnUp (by simpa only [hcurrent] using hslot)
      have ha := prepared.action_coordinator.trans hcoordArm
      have hreward := (coordinator_observation_positive_iff xc prepared _ ha).mp hobs |>.2
      simpa only [xc, ReferenceLaterOptionalControlResampling.withControl,
        hrewardTable] using hreward
    have hUpEvent :
        (selected = i ∧ ReferenceActiveAffinePositiveTest.upPositive xc = true) ↔
          slot = PublicDiscreteDraws.upSlot ∧ selected = i ∧
            affineHash (c.2 (1, i)) (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
            0 < rewards t (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) := by
      constructor
      · rintro ⟨hselected, hup⟩
        have heligible : AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput receptionInput) := by
          have hbool : decide (AffineBatchDecoder.eligible
              (CoordinatorUpReception.roundInput receptionInput)) = true := by
            have hformula := hUpFormula
            rw [hcheck] at hformula
            simpa using (hup.symm.trans hformula)
          exact of_decide_eq_true hbool
        obtain ⟨hslotActual, hobs⟩ :=
          ReferenceUpPhysicalHashRule.receiver_eligible_observation prepared lc heligible
        have hslot : slot = PublicDiscreteDraws.upSlot := by
          simpa [slot, hcurrent] using hslotActual
        obtain ⟨_, hconfig, hchecked, _, _⟩ := hpreparedUpFacts ⟨hslot, hselected⟩
        have hsent := upSent_of_checked_offer xc i old memory U
          (hdrawControl.trans hselected) hconfig hchecked
        have hhash0 := ReferenceUpPhysicalHashRule.upPositive_hash_one xc
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hsent hup
        have hhash : affineHash (c.2 (1, i))
            (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 := by
          rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdrawControl,
            hselected, hcurrent] at hhash0
          exact hhash0
        have hreward := hrewardPositive_of_observation hslot hobs
        exact ⟨hslot, hselected, hhash, hreward⟩
      · rintro ⟨hslot, hselected, hhash, hreward⟩
        have hpreparedArms := hpreparedUpFacts ⟨hslot, hselected⟩
        obtain ⟨hcoordArm, _hfocalConfig, _hchecked, hfocalArm, hotherArms⟩ := hpreparedArms
        have hcollisionFree : FiniteBanditModel.collisionFreeFor prepared.arms.actions
            (ActiveRoundActions.coordinator p.two_le_m) := by
          intro player hne
          rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨j, hplayer⟩
          · exact (hne hcoord).elim
          · have hact : prepared.arms.actions player = (prepared.followers.followers j).arm := by
              rw [hplayer]
              exact prepared.arms.actions_follower j
            rw [hact]
            by_cases hji : j = i
            · subst j
              rw [hfocalArm, prepared.action_coordinator, hcoordArm,
                ActiveFollowerArmChoice.offeredUpBit, hhash,
                ActiveRoundActions.sendArm_one]
              exact fun heq => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
                (tuple.property heq)
            · obtain ⟨_, _, _, _, _, harmJ⟩ := hotherArms j hji
              rw [harmJ, prepared.action_coordinator, hcoordArm]
              exact fun heq => ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m j
                (tuple.property heq)
        have haction := prepared.action_coordinator.trans hcoordArm
        have hrewardC : 0 < xc.rewards xc.time
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) := by
          simpa only [xc, ReferenceLaterOptionalControlResampling.withControl,
            hrewardTable] using hreward
        have hobsPositive := (coordinator_observation_positive_iff xc prepared _ haction).mpr
          ⟨hcollisionFree, hrewardC⟩
        have hgate := hgate_of_up ⟨hslot, hselected⟩
        have hselectedRound : (CoordinatorUpReception.roundInput receptionInput).selected = true :=
          (CoordinatorUpReception.roundInput_selected_iff_gate receptionInput).2 hgate
        have heligible : AffineBatchDecoder.eligible
            (CoordinatorUpReception.roundInput receptionInput) := by
          unfold AffineBatchDecoder.eligible
          exact ⟨hselectedRound, rfl, hobsPositive⟩
        have hpositiveBool : ReferenceActiveAffinePositiveTest.upPositive xc = true := by
          rw [hUpFormula, hcheck]
          simp [heligible]
        exact ⟨hselected, hpositiveBool⟩
    refine ⟨hUpEvent, hfollowers, hpreparedUpFacts, ?_, ?_, tuple.property⟩
    · refine ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, harm, hlocal,
        hrecorderInputs, o, lc, hrecord, hstart, hvalid, hphase, ?_, hpendingStart,
        hobserve, hdiagnostic⟩
      exact hcursor
    · refine ⟨lc, ?_, hcheck, hsite⟩
      exact hreceptionDomain

end Bandits.Support.ReferenceFirstCollectionControlGeometry

end
