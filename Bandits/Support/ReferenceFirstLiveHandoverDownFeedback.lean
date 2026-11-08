/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveStoppedReleaseSignedCost

/-!
# First-live mixed DOWN feedback

Sources: `sources/zip4/manuscript/05_binary_transport.tex:180-289`,
`sources/zip4/manuscript/06_interruptions.tex:246-299,431-490`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:100-108,141-157`.

The actual selected DOWN query has two physical service branches. Before an
unoccupied follower accepts its word, its PREPARE observation is the receiver
reward exactly for hash one. A pending follower avoids that receiver arm and
the coordinator observes the same rounded reward for hash zero. Both identities
are derived on the original source, rows and rewards.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ActiveRoundActions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveHandoverDownFeedback

variable {p : ConstructorDimensions.Parameters}

/-- Conditional arm calculation on the actual preparation. Every premise is
supplied by the source-derived frame in the public producer below. -/
private theorem prepared_mixed_down_actions
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : ∀ j,
      ((ReferenceActivePhysicalStep.prepare x).followers.followers j).configuration =
        .ordinary (states j) (memories j))
    (hfields : ∀ j, (states j).status ≠ .unoccupied →
      (states j).lastDown = some (selected.view.payload.downRecord j))
    (hnotReleased : ∀ j, (states j).status ≠ .released)
    (i : Fin (p.m - 1)) (hi : i ∈ selected.view.pendingAtChoice)
    (hdown : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = PublicDiscreteDraws.downSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = i) :
    let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
    let u := x.row.2 x.time
    let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1
    let hash := CoordinatorLocalArmChoice.currentDownHash selected.view.payload u i
    let selectedDraw := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1
    let projected : ActiveRoundActions.RoundInput selected.view.payload.assignment 0 :=
      { slot := PublicDiscreteDraws.slotDraw u.1
        selected := selectedDraw
        tuple := tuple
        pilots := fun player => PublicDiscreteDraws.pilotDraw (K_pos p) player u.1
        down := ⟨(fun j => Fin.elim0 j, hash), fun j => Fin.elim0 j⟩
        up := ⟨(fun j => Fin.elim0 j, hash), fun j => Fin.elim0 j⟩
        fast := selected.view.payload.assignment.auxiliary
        fast_outside := selected.view.payload.assignment.auxiliary_outside }
    (ReferenceActivePhysicalStep.prepare x).arms.actions =
      ActiveRoundActions.actions p.two_le_m snapshot projected := by
  intro snapshot u tuple hash selectedDraw projected
  have hdownNotData : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot := by decide
  have hdownNotUp : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot := by decide
  have hslot : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.downSlot := hdown
  have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1 = i := hdraw
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1 = tuple := rfl
  have hhash : projected.down.bit = hash := by
    simp [projected, ActiveRoundActions.HashedWord.bit,
      AffineChannelLaw.affineHash_zero_width]
  have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time :=
    ⟨hslot, hselectedDraw, hi⟩
  have hslotProjected : projected.slot = PublicDiscreteDraws.downSlot := hslot
  let iF : Fin (PublicDiscreteDraws.followerCount p.m) :=
    ⟨i.val, by simpa only [PublicDiscreteDraws.followerCount] using i.isLt⟩
  have hiF : iF = i := by apply Fin.ext; rfl
  have hselectedDrawF : selectedDraw = iF := hselectedDraw.trans hiF.symm
  have hprojectedSelected : projected.selected = iF := hselectedDrawF
  have hmissingProjected : projected.selected ∈ snapshot.missing := by
    change selectedDraw ∈ selected.view.pendingAtChoice
    rw [hselectedDrawF, hiF]
    exact hi
  classical
  funext player
  rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨j, hplayer⟩
  · subst player
    rw [ReferenceActivePhysicalStep.action_eq_down_sendArm
      (ReferenceActivePhysicalStep.prepare (x))
      selected hselection i hbranch]
    rw [ActiveRoundActions.actions_coordinator,
      ActiveRoundActions.coordinatorAction_down p.two_le_m snapshot projected
        hslotProjected hmissingProjected]
    change ActiveRoundActions.sendArm hash
        (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
        (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m iF)) = _
    rw [← hhash]
    rw [show projected.tuple = tuple by rfl, hprojectedSelected]
  · subst player
    let jIndex : Fin (p.m - 1) :=
      ⟨j.val, by simpa only [PublicDiscreteDraws.followerCount] using j.isLt⟩
    have hindex : jIndex = j := by
      apply Fin.ext
      rfl
    rw [ActiveRoundActions.actions_follower]
    rw [← hindex]
    have hlocalOrdinary :
        (DeclaredFollowerLocalRound.prepare rate jIndex x.row
          (x.state.activations jIndex) x.time
          (x.active jIndex) (x.state.followers jIndex)).configuration =
            .ordinary (states jIndex) (memories jIndex) := by
      have h := hprepared jIndex
      rw [(ReferenceActivePhysicalStep.prepare (x)).followers.followers_eq jIndex,
        ReferenceActiveFeedbackCut.prepareFollowers_apply] at h
      exact h
    obtain ⟨before, beforeMemory, offered, hinput, hstart, hchoiceArm⟩ :=
      ReferenceActiveDataOwnership.prepare_ordinary_choice jIndex
        x.row
        (x.state.activations jIndex)
        x.time (x.active jIndex)
        (x.state.followers jIndex) (states jIndex) (memories jIndex)
        hlocalOrdinary
    have hcore : ActiveFollowerArmChoice.followerArmChoiceCore (states jIndex) u jIndex offered =
        some (ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex) := by
      cases hstatus : (states jIndex).status with
      | unoccupied =>
          have hnotdata : PublicDiscreteDraws.slotDraw u.1 ≠ PublicDiscreteDraws.dataSlot := by
            rw [hslot]; decide
          have hnotSelected : ¬ (PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.upSlot ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1 = jIndex) := by
            rintro ⟨hup, _⟩
            rw [hslot] at hup
            exact (by decide : PublicDiscreteDraws.downSlot ≠
              PublicDiscreteDraws.upSlot) hup
          have hother := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
            (states jIndex) u jIndex offered hstatus hnotdata hnotSelected
          have hkernel := ActiveRoundActions.followerAction_unoccupied_down
            p.two_le_m snapshot projected jIndex hstatus hslotProjected
          rw [hkernel]
          simpa only [htuple] using hother
      | pending =>
          have hlast := hfields jIndex (by rw [hstatus]; decide)
          have harm := ReferenceActiveDataOwnership.downRecord_arm selected.view.payload jIndex
          have haux : ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
              (selected.view.payload.downRecord jIndex) = selected.view.payload.assignment.auxiliary := by
            apply Fin.ext
            have hone := ActiveFollowerArmChoice.down_auxiliary_arm_one_based rate.eta
              (selected.view.payload.downRecord jIndex)
            have hfield : (selected.view.payload.downRecord jIndex).val.e =
                (selected.view.payload.assignment.auxiliary).val + 1 := by
              rw [selected.view.payload.downRecord_fields jIndex]
            rw [hfield] at hone
            omega
          have hnotdata : PublicDiscreteDraws.slotDraw u.1 ≠ PublicDiscreteDraws.dataSlot := by
            rw [hslot]; decide
          have hnotfirst : ¬ (PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.upSlot ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1 = jIndex ∧
              (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                (ActiveRoundActions.coordinator p.two_le_m) =
                  ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
                    (selected.view.payload.downRecord jIndex)) := by
            rintro ⟨hup, _, _⟩
            rw [hslot] at hup
            exact (by decide : PublicDiscreteDraws.downSlot ≠
              PublicDiscreteDraws.upSlot) hup
          by_cases hcollision : PrelaunchBufferRecovery.downArm rate.eta
              (selected.view.payload.downRecord jIndex) =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m selectedDraw)
          · have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_pending_collision_escape
              (states jIndex) u jIndex offered (selected.view.payload.downRecord jIndex)
              hstatus hlast (Or.inl ⟨hslot, hcollision⟩)
            have hassignedCollision : selected.view.payload.assignment.assigned jIndex =
                (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m selectedDraw)) :=
              harm.symm.trans hcollision
            have hkernel : ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex =
                ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
                  (selected.view.payload.downRecord jIndex) := by
              simp [ActiveRoundActions.followerAction, snapshot, projected, selectedDraw,
                hstatus, hslot, hassignedCollision, haux, hdownNotData]
            rw [hkernel]
            simpa only [haux] using hcore
          · have hnotcollision : ¬ ((PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.downSlot ∧
                PrelaunchBufferRecovery.downArm rate.eta (selected.view.payload.downRecord jIndex) =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                    (PublicDiscreteDraws.followerPlayer p.two_le_m
                      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1))) ∨
              (PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.upSlot ∧
                PrelaunchBufferRecovery.downArm rate.eta (selected.view.payload.downRecord jIndex) =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                    (ActiveRoundActions.coordinator p.two_le_m))) := by
              rintro (⟨_, hcoll⟩ | ⟨hup, _⟩)
              · exact hcollision (by simpa only [selectedDraw, hselectedDraw] using hcoll)
              · rw [hslot] at hup
                exact (by decide : PublicDiscreteDraws.downSlot ≠
                  PublicDiscreteDraws.upSlot) hup
            have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_pending_own_arm
              (states jIndex) u jIndex offered (selected.view.payload.downRecord jIndex)
              hstatus hlast hnotdata hnotfirst hnotcollision
            have hnotActionCollision :
                selected.view.payload.assignment.assigned jIndex ≠
                  tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m selectedDraw) := by
              intro hsame
              exact hcollision (harm.trans hsame)
            have hselectedEqIndex : selectedDraw = i := by
              simpa only [selectedDraw] using hselectedDraw
            have hnotActionCollisionAtI :
                selected.view.payload.assignment.assigned jIndex ≠
                  tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
              intro hsame
              exact hnotActionCollision (by simpa only [hselectedEqIndex] using hsame)
            have hkernel : ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex =
                PrelaunchBufferRecovery.downArm rate.eta
                  (selected.view.payload.downRecord jIndex) := by
              simp [ActiveRoundActions.followerAction, snapshot, projected, selectedDraw,
                hstatus, hslot, hselectedDraw,
                hnotActionCollisionAtI, harm, hdownNotData, hdownNotUp]
            rw [hkernel]
            exact hcore
      | released => exact False.elim (hnotReleased jIndex hstatus)
    have hcoreChoice : ActiveFollowerArmChoice.followerArmChoice (states jIndex)
        x.row x.time jIndex offered =
        some (ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex) := by
      simpa only [ActiveFollowerArmChoice.followerArmChoice] using hcore
    have harm :
        (DeclaredFollowerLocalRound.prepare rate jIndex x.row
          (x.state.activations jIndex) x.time
          (x.active jIndex)
          (x.state.followers jIndex)).arm =
          ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex :=
      Option.some.inj (hchoiceArm.symm.trans hcoreChoice)
    change (ReferenceActivePhysicalStep.prepare (x)).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m jIndex) =
      ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex
    exact (ReferenceActivePhysicalStep.PreparedRound.action_follower
      (ReferenceActivePhysicalStep.prepare (x)) jIndex).trans harm

/-- Conditional chronology on the computed first window. The public producer
supplies ordinary preparations from actual corrected-seed safety. -/
private theorem first_live_prior_down_of_ordinary_choices
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial) :
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records
    (∀ (k : Fin W.length) (j : Fin (p.m - 1)), ∃ choice memory,
      (W[k.val].output.preparation.followers.followers j).configuration = .ordinary choice memory) →
    ∀ (k : Fin W.length) (selected : ReferenceActivePhysicalStep.Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      ∀ j, j ∉ selected.view.pendingAtChoice →
        ∃ prior ∈ W, prior.input.time.val < W[k.val].input.time.val ∧
          ∃ priorSelected : ReferenceActivePhysicalStep.Selection prior.input,
            prior.output.preparation.coordinator.selection = some priorSelected ∧
            priorSelected.view.payload = selected.view.payload ∧
            ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent prior priorSelected ∧
            PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (prior.input.row.2 prior.input.time).1 = j ∧
            ∃ accepted ∈ W, accepted.input.time.val < prior.input.time.val ∧
              ReferenceFirstLiveConfirmationHistory.AcceptedDown accepted j
                (selected.view.payload.downRecord j) := by
  intro W hordinary k selected hselectionOutput j hj
  have hround : W[k.val].input.time.val = start + k.val :=
    (ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
      initial rows J rewards start count hspan active hfirst k selected hselectionOutput).2.1
  have hmissingProvenance := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    initial rows J rewards start count hspan
    active hfirst
  have hnonzeroRoot : W.length ≠ 0 := by omega
  have hdata := hmissingProvenance.resolve_left hnonzeroRoot
  rcases hdata with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrows⟩
  obtain ⟨provenanceRecord, hprovenanceRecord, provenanceSelected, hprovenanceSelected,
    _, _, _, _, _, _, _, _, hpriorHistory⟩ := hrows k
  cases hprovenanceRecord
  have hselectedEq : provenanceSelected = selected :=
    Option.some.inj (hprovenanceSelected.symm.trans hselectionOutput)
  subst provenanceSelected
  obtain ⟨ell, hell, prior, hprior, priorSelected, hpriorSelected, hpayload,
    hevent, hindex⟩ := hpriorHistory j hj
  cases hprior
  change ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
    W[ell] priorSelected at hevent
  have hellWindow : ell < W.length := hell.trans k.isLt
  have hpriorSelectedOutput : W[ell].output.preparation.coordinator.selection =
      some priorSelected := hpriorSelected
  have hpriorTime := (ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
    initial rows J rewards start count hspan
    active hfirst ⟨ell, hellWindow⟩ priorSelected hpriorSelectedOutput).2.1
  change W[ell].input.time.val = start + ell at hpriorTime
  have hpriorSelectedPrepared :
      (ReferenceActivePhysicalStep.prepare W[ell].input).coordinator.selection =
        some priorSelected := by
    simpa only [W[ell].output_eq, ReferenceActivePhysicalStep.step] using hpriorSelectedOutput
  refine ⟨W[ell], ?_, ?_, priorSelected, hpriorSelectedOutput, hpayload,
    hevent, hindex, ?_⟩
  · exact List.getElem_mem hellWindow
  · omega
  · obtain ⟨priorChoice, priorMemory, hpriorPrepared⟩ := hordinary ⟨ell, hellWindow⟩ j
    change (W[ell].output.preparation.followers.followers j).configuration =
      .ordinary priorChoice priorMemory at hpriorPrepared
    have hpriorPrepared' :
        ((ReferenceActivePhysicalStep.prepare W[ell].input).followers.followers j).configuration =
          .ordinary priorChoice priorMemory := by
      simpa only [W[ell].output_eq, ReferenceActivePhysicalStep.step] using hpriorPrepared
    have hpriorIndex : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[ell].input.row.2 W[ell].input.time).1 = j := hindex
    obtain ⟨a, ha, haccepted⟩ :=
      ReferenceFirstLiveConfirmationHistory.run_firstLive_confirmation_prior_down
        initial rows J rewards start count hspan
        active hfirst hseed ⟨ell, hellWindow⟩ priorSelected hpriorSelectedPrepared
        priorChoice priorMemory (by rw [hpriorIndex]; exact hpriorPrepared')
        (by simpa only [ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent,
          W[ell].output_eq, ReferenceActivePhysicalStep.step] using hevent)
    change a < ell at ha
    change ReferenceFirstLiveConfirmationHistory.AcceptedDown W[a]
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[ell].input.row.2 W[ell].input.time).1)
      (priorSelected.view.payload.downRecord
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (W[ell].input.row.2 W[ell].input.time).1)) at haccepted
    rw [hpriorIndex, hpayload] at haccepted
    have haWindow : a < W.length := ha.trans hellWindow
    obtain ⟨_, hactualAccepted, _⟩ :=
      ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
        initial rows J rewards start count hspan
        active ⟨a, haWindow⟩
    have hacceptedTime : W[a].input.time.val = start + a := by
      rw [hactualAccepted]
      rfl
    refine ⟨W[a], ?_, ?_, ?_⟩
    · exact List.getElem_mem haWindow
    · omega
    · exact haccepted


/-- Deterministic actual mixed-unoccupied/pending DOWN feedback at the first
live selected query. The source's first installation and every follower that
has already left the pending set are retained as actual prior-DOWN evidence.
The two feedback identities are conditional only on the inline local stage
predicates and the actual hash branch. -/
theorem actual_first_live_mixed_down_feedback
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hrW : r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
        rate rewards C_star C_h z))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (hi : i ∈ selected.view.pendingAtChoice)
    (hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 t).1 = i) :
    let followerIndex : Fin (PublicDiscreteDraws.followerCount p.m) :=
      ⟨i.val, by simpa only [PublicDiscreteDraws.followerCount] using i.isLt⟩
    let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K (r.input.row.2 t).1
    let receiver := tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m followerIndex)
    r.input.time = t ∧
      r.output.coordinator.failure = none ∧
      ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
        (∀ j, r.input.state.followers j = .ordinary (states j) (memories j)) ∧
        (∀ j, (r.output.preparation.followers.followers j).configuration =
          .ordinary (states j) (memories j)) ∧
        (∀ j, (states j).status ≠ .released) ∧
        (∀ j, (states j).status = .unoccupied ↔ (states j).lastDown = none) ∧
        (∀ j, (states j).status ≠ .unoccupied →
          (states j).lastDown = some (selected.view.payload.downRecord j)) ∧
        (r.output.preparation.arms.actions (ActiveRoundActions.coordinator p.two_le_m) =
          ActiveRoundActions.sendArm
            (CoordinatorLocalArmChoice.currentDownHash selected.view.payload (r.input.row.2 t) i)
            (tuple.val (ActiveRoundActions.coordinator p.two_le_m)) receiver) ∧
        (∀ j, (states j).status = .unoccupied →
          r.output.preparation.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
            tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m j)) ∧
        (∀ j, (states j).status = .pending →
          r.output.preparation.arms.actions (PublicDiscreteDraws.followerPlayer p.two_le_m j) =
            if selected.view.payload.assignment.assigned j = receiver then
              selected.view.payload.assignment.auxiliary
            else selected.view.payload.assignment.assigned j) ∧
        (∀ j, (states j).status = .pending →
          r.output.preparation.arms.actions
            (PublicDiscreteDraws.followerPlayer p.two_le_m j) ≠ receiver) ∧
        (∀ j, j ≠ i → r.output.preparation.arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m j) ≠ receiver) ∧
        tuple.val (ActiveRoundActions.coordinator p.two_le_m) ≠ receiver ∧
        (∀ j, j ∉ selected.view.pendingAtChoice →
          ∃ prior ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
              (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
                rate rewards C_star C_h z),
            prior.input.time.val < t.val ∧
            ∃ priorSelected : ReferenceActivePhysicalStep.Selection prior.input,
              prior.output.preparation.coordinator.selection = some priorSelected ∧
              priorSelected.view.payload = selected.view.payload ∧
              ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
                prior priorSelected ∧
              PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (prior.input.row.2 prior.input.time).1 = j ∧
              ∃ accepted ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
                  (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
                    rate rewards C_star C_h z),
                accepted.input.time.val < prior.input.time.val ∧
                ReferenceFirstLiveConfirmationHistory.AcceptedDown accepted j
                  (selected.view.payload.downRecord j)) ∧
        (∀ incoming incomingMemory,
          r.input.state.followers i = .ordinary incoming incomingMemory →
          incoming.lastDown = none →
          (r.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m followerIndex)).val.val =
            if CoordinatorLocalArmChoice.currentDownHash selected.view.payload
                (r.input.row.2 t) i = 1 then
              RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t receiver)
            else 0) ∧
        ((∃ incoming incomingMemory,
          r.input.state.followers i = .ordinary incoming incomingMemory ∧
          incoming.lastDown = some (selected.view.payload.downRecord i)) →
          (states i).status = .pending ∧
            (CoordinatorLocalArmChoice.currentDownHash selected.view.payload
                (r.input.row.2 t) i = 0 →
              (r.output.preparation.feedback.observations
                  (ActiveRoundActions.coordinator p.two_le_m)).val.val =
                RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (rewards t receiver))) := by
  classical
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let count := p.T - s
  have hsElapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s := by
    dsimp [s, ReferenceCompletePhysicalHistory.physicalStart,
      ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput]
  have hsBound : s ≤ p.T := by
    simpa only [s] using ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  have hspan : s + count ≤ p.T := by dsimp [count]; omega
  have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hactualNone :
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = none := by
      rw [ReferenceSourcePrefixHistoryFiltration.actualRecord]
      by_cases hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val
      · simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
      · simp [hs]
    rw [hactualNone] at hr
    cases hr
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true := by
    by_contra hnot
    have hfalse : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = false :=
      Bool.eq_false_of_not_eq_true hnot
    have hcrossNone : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing = none := by
      cases hvalue : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing with
      | none => rfl
      | some value => simp [hvalue] at hfalse
    exact hlaunchNe ((ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
      rate z rewards C_star C_h).mpr hcrossNone)
  let initial := ReferenceLocalReleaseGateChronology.sourceSeed rate z rewards C_star C_h hcross
  have hlaunch := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z rewards C_star C_h hcross
  have hcanonical := ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
    rate z rewards C_star C_h hcross
  have hcellLaunch := ReferenceFirstLaunchNumericalCell.actual_launch_seed
    rate z rewards C_star C_h hcross
  let actualSeed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z rewards C_star C_h hcross
  have hinitialEq : initial = ReferenceFirstLaunchNumericalCell.launchState
      rate z rewards C_star C_h hcross :=
    Option.some.inj (hlaunch.symm.trans hcellLaunch.1)
  have hdecoderSeed := ReferenceFirstLiveDownCompletionReadout.actual_corrected_decoder_seed
    rate z rewards C_star C_h hcross
  have hseedLastDown : ∀ j, (actualSeed.followers j).lastDown = none := by
    intro j
    obtain ⟨state, memory, hstate, hnone, _, _, _, _⟩ := hdecoderSeed j
    have hstateSeed : initial.followers j = .ordinary (actualSeed.followers j)
        (actualSeed.memory j) := by
      simpa only [initial, hinitialEq, actualSeed] using actualSeed.configuration j
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hstate.symm.trans hstateSeed)
    rw [← heq.1]
    exact hnone
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
    simpa only [initial, hinitialEq, s, actualSeed, hsElapsed] using hcanonical.2.1
  have hfirst : initial.coordinator = .first := by simpa only [initial] using hcanonical.1
  have hinitialFollowers : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    simpa only [initial] using hcanonical.2.2
  have hseedConfiguration : ∀ j,
      initial.followers j = .ordinary (actualSeed.followers j) (actualSeed.memory j) := by
    intro j
    simpa only [initial, hinitialEq, actualSeed] using actualSeed.configuration j
  let sourceRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hmode
  let sourceWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow sourceRun.records
  have hrunRecords : sourceRun.records =
      ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords rate rewards C_star C_h z := by
    exact (ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch).symm
  have hwindow :
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
          rate rewards C_star C_h z) = sourceWindow := by
    simp only [sourceWindow, ← hrunRecords]
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp (by simpa only [hwindow] using hrW)
  let k : Fin sourceWindow.length := ⟨n, by simpa only [hwindow] using hn⟩
  have hrEq : r = sourceWindow[k.val] := by
    change r = sourceWindow[n]
    exact hget.symm
  subst r
  have hstartLe : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
    by_contra hfuture
    have hnone := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_future_start
      rate rewards C_star C_h t z (Nat.lt_of_not_ge hfuture)
    rw [hnone] at hr
    cases hr
  have hactualRecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h t z initial hlaunch hstartLe
  have hrecordIdentity : sourceWindow[k.val] =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (t.val - s)
        (by
          have ht := t.isLt
          omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h initial hlaunch) := by
    exact Option.some.inj (hr.symm.trans hactualRecord)
  have htime : sourceWindow[k.val].input.time = t := by
    rw [hrecordIdentity]
    apply Fin.ext
    have hsle : s ≤ t.val := by
      simpa only [s] using hstartLe
    simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    omega
  have hselection :
      (ReferenceActivePhysicalStep.prepare sourceWindow[k.val].input).coordinator.selection =
        some selected := by
    simpa only [k, sourceWindow[n].output_eq, ReferenceActivePhysicalStep.step] using hsel
  have hrunSafety := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode hfirst actualSeed.followers actualSeed.memory hseedConfiguration
    actualSeed.S_zero actualSeed.delta_zero actualSeed.backlog_zero hseedLastDown
    actualSeed.unoccupied actualSeed.bufferValid actualSeed.chronologicalBuffer
    actualSeed.bufferStamps actualSeed.decoderValid
  have hchoices : ∀ j : Fin (p.m - 1),
      ∃ choice choiceMemory next nextMemory,
        (sourceWindow[k.val].output.preparation.followers.followers j).configuration =
          .ordinary choice choiceMemory ∧
        (sourceWindow[k.val].output.followers j).configuration = .ordinary next nextMemory ∧
        (sourceWindow[k.val].output.followers j).failure = none ∧
        ∀ selected' : ReferenceActivePhysicalStep.Selection sourceWindow[k.val].input,
          sourceWindow[k.val].output.preparation.coordinator.selection = some selected' →
          choice.status ≠ .unoccupied →
            choice.lastDown = some (selected'.view.payload.downRecord j) := by
    intro j
    exact hrunSafety.2 k j
  choose states memories nextStates nextMemories hprepared hnext hfailure hcarried using hchoices
  have hselectionOutput :
      sourceWindow[k.val].output.preparation.coordinator.selection = some selected := by
    simpa only [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselection
  obtain ⟨hsigma, hround, hgrid, hbits⟩ :=
    ReferenceFirstLiveDownNumericalRecovery.first_live_geometry
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
      hmode hfirst k selected hselectionOutput
  change selected.view.payload.sigma.val = s at hsigma
  change sourceWindow[k.val].input.time.val = s + k.val at hround
  change sourceWindow[k.val].input.time.val + 2 ≤
    FollowerCutoffScan.gridBoundary p rate.eta.val selected.view.payload.sigma at hgrid
  change ∀ j : Fin p.T, s ≤ j.val → j.val < sourceWindow[k.val].input.time.val →
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) j = false at hbits
  obtain ⟨hstep, hactualWindow, _⟩ :=
    ReferenceFirstLiveUnoccupiedEmission.window_record_eq_candidate
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
      hmode k
  have hchoiceIncoming : ∀ j,
      sourceWindow[k.val].input.state.followers j = .ordinary (states j) (memories j) ∧
      ((states j).status = .unoccupied → (states j).lastDown = none) := by
    intro j
    obtain ⟨hprefix, hprefixStates⟩ := hrunSafety.1 k.val k.isLt.le
    obtain ⟨before, beforeMemory, hbefore, hlocal, _, _, _, hzero, hoccupied⟩ :=
      hprefixStates j
    have hinputState : sourceWindow[k.val].input.state =
        (ReferenceActivePhysicalHorizon.run initial z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k.val hprefix hmode).finalState := by
      rw [hactualWindow]
      rfl
    have hinput : sourceWindow[k.val].input.state.followers j =
        .ordinary before beforeMemory := by
      rw [hinputState]
      exact hbefore
    have hstartUnchanged : ActiveFollowerLifecycle.startRound rate.eta
        sourceWindow[k.val].input.time before beforeMemory = .ok (before, beforeMemory) := by
      by_cases hu : before.status = .unoccupied
      · exact ActiveFollowerLifecycle.startRound_unoccupied rate.eta
          sourceWindow[k.val].input.time before beforeMemory hlocal hu
      · obtain ⟨hkpos, M, token, hM, hMsigma, hread, hstamp, hbit⟩ := hoccupied hu
        have hcoordinate : ActiveFollowerLifecycle.acceptedStartCoordinate M =
            selected.view.payload.sigma := by
          apply Fin.ext
          have hone := ActiveFollowerLifecycle.accepted_start_coordinate_one_based M
          omega
        have hrecordTime : M.val.sigma ≤ sourceWindow[k.val].input.time.val := by omega
        have hrecordGrid : sourceWindow[k.val].input.time.val + 2 ≤
            FollowerCutoffScan.gridBoundary p rate.eta.val
              (ActiveFollowerLifecycle.acceptedStartCoordinate M) := by
          rw [hcoordinate]
          exact hgrid
        have hbitFalse : token.bit = false := by
          rw [hbit]
          apply hbits token.timestamp <;> omega
        have hgridNe : FollowerCutoffScan.gridBoundary p rate.eta.val
            (ActiveFollowerLifecycle.acceptedStartCoordinate M) ≠
              sourceWindow[k.val].input.time.val + 1 := by omega
        have hbranch := ActiveFollowerLifecycle.startRound_occupied_branch rate.eta
          sourceWindow[k.val].input.time before beforeMemory hu hlocal M hM hrecordTime
          (by omega) token hread
          (by change token.timestamp.val + 1 = sourceWindow[k.val].input.time.val; omega)
        simpa only [hgridNe, decide_false, hbitFalse, Bool.false_or,
          Bool.false_eq_true, ite_false] using hbranch
    have hlocalPrepared :
        (DeclaredFollowerLocalRound.prepare rate j sourceWindow[k.val].input.row
          (sourceWindow[k.val].input.state.activations j) sourceWindow[k.val].input.time
          (sourceWindow[k.val].input.active j)
          (sourceWindow[k.val].input.state.followers j)).configuration =
            .ordinary (states j) (memories j) := by
      have h := hprepared j
      rw [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step,
        (ReferenceActivePhysicalStep.prepare sourceWindow[k.val].input).followers.followers_eq j,
        ReferenceActiveFeedbackCut.prepareFollowers_apply] at h
      exact h
    obtain ⟨actualBefore, actualMemory, _offered, hactualBefore, hstart, _harm⟩ :=
      ReferenceActiveDataOwnership.prepare_ordinary_choice j sourceWindow[k.val].input.row
        (sourceWindow[k.val].input.state.activations j) sourceWindow[k.val].input.time
        (sourceWindow[k.val].input.active j) (sourceWindow[k.val].input.state.followers j)
        (states j) (memories j) hlocalPrepared
    have hbeforeEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hinput.symm.trans hactualBefore)
    rcases hbeforeEq with ⟨rfl, rfl⟩
    have hchoiceEq := Prod.mk.inj (Except.ok.inj (hstartUnchanged.symm.trans hstart))
    rw [← hchoiceEq.1, ← hchoiceEq.2]
    exact ⟨hinput, fun hu => (hzero hu).1⟩
  have hfirstLiveNoReleased := ReferenceFirstLiveConfirmationHistory.run_firstLive_no_released
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode hfirst hinitialFollowers
  have hcoordSafety := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    hmode hfirst
  have hcoordFailure : sourceWindow[k.val].output.coordinator.failure = none := by
    exact (hcoordSafety.1 k).1
  have hnoReleasedFields : ∀ j,
      (states j).status ≠ .unoccupied →
        (states j).lastDown = some (selected.view.payload.downRecord j) := by
    intro j hoccupied
    have hprep : ((ReferenceActivePhysicalStep.prepare (sourceWindow[k.val].input)).followers.followers j).configuration =
        .ordinary (states j) (memories j) := by
      have h := hprepared j
      rw [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] at h
      exact h
    exact (hfirstLiveNoReleased k selected hselection j (states j) (memories j) hprep).1 hoccupied
  have hpendingNonempty : selected.view.pendingAtChoice.Nonempty := ⟨i, hi⟩
  have hnotReleased : ∀ j, (states j).status ≠ .released := by
    intro j
    have hprep : ((ReferenceActivePhysicalStep.prepare (sourceWindow[k.val].input)).followers.followers j).configuration =
        .ordinary (states j) (memories j) := by
      have h := hprepared j
      rw [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] at h
      exact h
    exact (hfirstLiveNoReleased k selected hselection j (states j) (memories j) hprep).2 hpendingNonempty
  let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
    ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
  have hnoReleased : ActiveRoundActions.no_released_while_missing snapshot := by
    intro hmissing j
    exact hnotReleased j
  have hdownNotData : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot := by
    decide
  have hdownNotUp : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot := by
    decide
  let u := sourceWindow[k.val].input.row.2 sourceWindow[k.val].input.time
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1
  let hash := CoordinatorLocalArmChoice.currentDownHash selected.view.payload u i
  let selectedDraw := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1
  let projected : ActiveRoundActions.RoundInput selected.view.payload.assignment 0 :=
    { slot := PublicDiscreteDraws.slotDraw u.1
      selected := selectedDraw
      tuple := tuple
      pilots := fun player => PublicDiscreteDraws.pilotDraw (K_pos p) player u.1
      down := ⟨(fun j => Fin.elim0 j, hash), fun j => Fin.elim0 j⟩
      up := ⟨(fun j => Fin.elim0 j, hash), fun j => Fin.elim0 j⟩
      fast := selected.view.payload.assignment.auxiliary
      fast_outside := selected.view.payload.assignment.auxiliary_outside }
  have hslot : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.downSlot := by
    simpa only [u, htime] using hdown
  have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1 = i := by
    simpa only [u, htime] using hdraw
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1 = tuple := rfl
  have hhash : projected.down.bit = hash := by
    simp [projected, ActiveRoundActions.HashedWord.bit,
      AffineChannelLaw.affineHash_zero_width]
  have hbranch : ReferenceDownReception.selectedDownSenderBranch selected.view i
      sourceWindow[k.val].input.row sourceWindow[k.val].input.time := by
    exact ⟨hslot, hselectedDraw, hi⟩
  have hslotProjected : projected.slot = PublicDiscreteDraws.downSlot := by
    simpa only [projected] using hslot
  let iF : Fin (PublicDiscreteDraws.followerCount p.m) :=
    ⟨i.val, by simpa only [PublicDiscreteDraws.followerCount] using i.isLt⟩
  have hiF : iF = i := by
    apply Fin.ext
    rfl
  have hselectedDrawF : selectedDraw = iF := hselectedDraw.trans hiF.symm
  have hprojectedSelected : projected.selected = iF := by
    change selectedDraw = iF
    exact hselectedDrawF
  have hiFmem : iF ∈ selected.view.pendingAtChoice := by
    simpa only [iF, PublicDiscreteDraws.followerCount] using hi
  have hmissingProjected : projected.selected ∈ snapshot.missing := by
    change selectedDraw ∈ selected.view.pendingAtChoice
    rw [hselectedDrawF]
    exact hiFmem
  have hhashAtTime : CoordinatorLocalArmChoice.currentDownHash selected.view.payload
      (sourceWindow[k.val].input.row.2 t) i = hash := by
    simp [hash, u, htime]
  have htupleAtTime : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (sourceWindow[k.val].input.row.2 t).1 = tuple := by
    simp [tuple, u, htime]
  have hactions :
      (ReferenceActivePhysicalStep.prepare sourceWindow[k.val].input).arms.actions =
        ActiveRoundActions.actions p.two_le_m snapshot projected := by
    apply prepared_mixed_down_actions sourceWindow[k.val].input selected hselection
      states memories (fun j => ?_) hnoReleasedFields hnotReleased i hi hslot hselectedDraw
    simpa only [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] using hprepared j
  have hactualActions : sourceWindow[k.val].output.preparation.arms.actions =
      ActiveRoundActions.actions p.two_le_m snapshot projected := by
    simpa only [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] using hactions
  have hprojectedObservation (player : Fin p.m) :
      (sourceWindow[k.val].output.preparation.feedback.observations player).val.val =
        ActiveRoundActions.feedback p.two_le_m snapshot projected
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) player := by
    have hinputRewards : sourceWindow[k.val].input.rewards = rewards := by
      rw [hrecordIdentity]
      rfl
    calc
      (sourceWindow[k.val].output.preparation.feedback.observations player).val.val =
          ((ReferenceActivePhysicalStep.prepare (sourceWindow[k.val].input)).feedback.observations player).val.val := by
        rw [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step]
      _ = ActiveRoundActions.feedback p.two_le_m snapshot projected
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) player := by
        simpa only [k, htime, hinputRewards] using
          ReferenceFirstLiveReleaseGeometry.prepared_observation_eq_projected selected snapshot
            projected player hactions
  have hpreparationChoice := hprepared i
  have hactualPrep :
      ((ReferenceActivePhysicalStep.prepare (sourceWindow[k.val].input)).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    simpa only [sourceWindow[k.val].output_eq, ReferenceActivePhysicalStep.step] using hprepared i
  have hactualLocalPrep :
      (DeclaredFollowerLocalRound.prepare rate i sourceWindow[k.val].input.row
        (sourceWindow[k.val].input.state.activations i) sourceWindow[k.val].input.time
        (sourceWindow[k.val].input.active i) (sourceWindow[k.val].input.state.followers i)).configuration =
          .ordinary (states i) (memories i) := by
    have h := hactualPrep
    rw [(ReferenceActivePhysicalStep.prepare (sourceWindow[k.val].input)).followers.followers_eq i,
      ReferenceActiveFeedbackCut.prepareFollowers_apply] at h
    exact h
  obtain ⟨incoming, incomingMemory, offered, hincoming, hstartRound, hchoiceArm⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i sourceWindow[k.val].input.row
      (sourceWindow[k.val].input.state.activations i) sourceWindow[k.val].input.time
      (sourceWindow[k.val].input.active i) (sourceWindow[k.val].input.state.followers i)
      (states i) (memories i) hactualLocalPrep
  have hframe := ActiveFollowerLifecycle.startRound_frame rate.eta
    sourceWindow[k.val].input.time incoming (states i) incomingMemory (memories i) hstartRound
  have hchoiceLastDown :
      (states i).status ≠ .unoccupied →
        (states i).lastDown = some (selected.view.payload.downRecord i) :=
    hnoReleasedFields i
  have hbeforeFormula : ∀ before beforeMemory,
      sourceWindow[k.val].input.state.followers i = .ordinary before beforeMemory →
      before.lastDown = none →
      (sourceWindow[k.val].output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m iF)).val.val =
        if CoordinatorLocalArmChoice.currentDownHash selected.view.payload
            (sourceWindow[k.val].input.row.2 t) i = 1 then
          RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
            (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (sourceWindow[k.val].input.row.2 t).1).val
              (PublicDiscreteDraws.followerPlayer p.two_le_m iF)))
        else 0 := by
    intro before beforeMemory hin hnone
    have hsame : before = incoming ∧ beforeMemory = incomingMemory := by
      have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hin.symm.trans hincoming)
      exact heq
    rcases hsame with ⟨rfl, rfl⟩
    have hchoiceNone : (states i).lastDown = none := hframe.1.trans hnone
    have hstatusUnoccupied : (states i).status = .unoccupied := by
      by_contra hstatus
      have hsome := hchoiceLastDown hstatus
      rw [hchoiceNone] at hsome
      cases hsome
    have hprojectedStatus : snapshot.status projected.selected = .unoccupied := by
      change (states projected.selected).status = .unoccupied
      rw [hprojectedSelected, hiF]
      exact hstatusUnoccupied
    have hgeneric := ActiveRoundActions.unoccupied_down_feedback p.two_le_m snapshot projected
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
      hslotProjected hmissingProjected hnoReleased hprojectedStatus
    have hgeneric' : ActiveRoundActions.feedback p.two_le_m snapshot projected
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (PublicDiscreteDraws.followerPlayer p.two_le_m iF) =
          if projected.down.bit = 1 then
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
              (projected.tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m iF))
          else 0 := by
      simpa only [projected, hselectedDrawF] using hgeneric
    rw [hprojectedObservation (PublicDiscreteDraws.followerPlayer p.two_le_m iF), hgeneric']
    rw [hhash, hhashAtTime]
    simp [projected, tuple, u, htime,
      ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow]
  have hafter : (states i).status = .pending →
      ∃ incoming incomingMemory,
        sourceWindow[k.val].input.state.followers i = .ordinary incoming incomingMemory ∧
        incoming.lastDown = some (selected.view.payload.downRecord i) ∧
        (CoordinatorLocalArmChoice.currentDownHash selected.view.payload
            (sourceWindow[k.val].input.row.2 t) i = 0 →
          (sourceWindow[k.val].output.preparation.feedback.observations
              (ActiveRoundActions.coordinator p.two_le_m)).val.val =
            RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
              (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (sourceWindow[k.val].input.row.2 t).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m iF)))) := by
    intro hpending
    refine ⟨incoming, incomingMemory, hincoming, ?_, ?_⟩
    · rw [← hframe.1]
      exact hchoiceLastDown (by rw [hpending]; decide)
    · intro hzero
      have hbit : projected.down.bit = 0 := by
        rw [hhash, ← hhashAtTime]
        exact hzero
      have hprojectedPending : snapshot.status projected.selected = .pending := by
        change (states projected.selected).status = .pending
        rw [hprojectedSelected, hiF]
        exact hpending
      have hgeneric := ActiveRoundActions.pending_down_coordinator_feedback p.two_le_m
        snapshot projected (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        hslotProjected hmissingProjected hnoReleased hprojectedPending hbit
      have hgenericCoord : ActiveRoundActions.feedback p.two_le_m snapshot projected
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (ActiveRoundActions.coordinator p.two_le_m) =
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
              (projected.tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m iF)) := by
        simpa only [hprojectedSelected] using hgeneric
      rw [hprojectedObservation (ActiveRoundActions.coordinator p.two_le_m), hgenericCoord]
      simp [projected, tuple, u, htime,
        ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow]
  have hafterFormula :
      (∃ before beforeMemory,
        sourceWindow[k.val].input.state.followers i = .ordinary before beforeMemory ∧
        before.lastDown = some (selected.view.payload.downRecord i)) →
      (states i).status = .pending ∧
        (CoordinatorLocalArmChoice.currentDownHash selected.view.payload
            (sourceWindow[k.val].input.row.2 t) i = 0 →
          (sourceWindow[k.val].output.preparation.feedback.observations
              (ActiveRoundActions.coordinator p.two_le_m)).val.val =
            RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
              (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                (sourceWindow[k.val].input.row.2 t).1).val
                (PublicDiscreteDraws.followerPlayer p.two_le_m iF)))) := by
    rintro ⟨before, beforeMemory, hbefore, hlast⟩
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hbefore.symm.trans (hchoiceIncoming i).1)
    have hchoiceSome : (states i).lastDown = some (selected.view.payload.downRecord i) := by
      rw [← heq.1]
      exact hlast
    have hoccupied : (states i).status ≠ .unoccupied := by
      intro hu
      rw [(hchoiceIncoming i).2 hu] at hchoiceSome
      cases hchoiceSome
    have hpending : (states i).status = .pending := by
      cases hstatus : (states i).status with
      | unoccupied => exact False.elim (hoccupied hstatus)
      | pending => rfl
      | released => exact False.elim (hnotReleased i hstatus)
    obtain ⟨_, _, _, _, hformula⟩ := hafter hpending
    exact ⟨hpending, hformula⟩
  dsimp only
  refine ⟨htime, hcoordFailure, states, memories, ?_, hprepared, hnotReleased,
    ?_, hnoReleasedFields, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbeforeFormula, hafterFormula⟩
  · exact fun j => (hchoiceIncoming j).1
  · intro j
    refine ⟨(hchoiceIncoming j).2, ?_⟩
    intro hnone
    by_contra hoccupied
    have hsome := hnoReleasedFields j hoccupied
    rw [hnone] at hsome
    cases hsome
  · rw [hactualActions, ActiveRoundActions.actions_coordinator,
      ActiveRoundActions.coordinatorAction_down p.two_le_m snapshot projected
        hslotProjected hmissingProjected]
    change ActiveRoundActions.sendArm projected.down.bit
        (tuple.val (ActiveRoundActions.coordinator p.two_le_m))
        (tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m projected.selected)) =
      ActiveRoundActions.sendArm
        (CoordinatorLocalArmChoice.currentDownHash selected.view.payload
          (sourceWindow[k.val].input.row.2 t) i)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (sourceWindow[k.val].input.row.2 t).1).val
          (ActiveRoundActions.coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (sourceWindow[k.val].input.row.2 t).1).val
          (PublicDiscreteDraws.followerPlayer p.two_le_m iF))
    rw [hprojectedSelected, hhash, hhashAtTime, htupleAtTime]
  · intro j hu
    rw [hactualActions, ActiveRoundActions.actions_follower p.two_le_m snapshot projected j,
      ActiveRoundActions.followerAction_unoccupied_down p.two_le_m snapshot projected j
        hu hslotProjected]
    exact congrArg (fun a => a.val (PublicDiscreteDraws.followerPlayer p.two_le_m j))
      htupleAtTime.symm
  · intro j hpending
    rw [hactualActions, ActiveRoundActions.actions_follower p.two_le_m snapshot projected j,
      ActiveRoundActions.followerAction_pending_down p.two_le_m snapshot projected j
        hpending hslotProjected]
    change (if selected.view.payload.assignment.assigned j =
        tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m projected.selected) then
      selected.view.payload.assignment.auxiliary else selected.view.payload.assignment.assigned j) = _
    rw [hprojectedSelected, htupleAtTime]
  · intro j hpending
    rw [hactualActions, ActiveRoundActions.actions_follower p.two_le_m snapshot projected j]
    rw [htupleAtTime]
    have havoid := ActiveRoundActions.pending_avoids_down p.two_le_m snapshot projected j
      hpending hslotProjected
    rw [hprojectedSelected] at havoid
    exact havoid
  · intro j hji
    rw [hactualActions, ActiveRoundActions.actions_follower p.two_le_m snapshot projected j]
    have hjiProjected : j ≠ projected.selected := by simpa only [hprojectedSelected, hiF] using hji
    rw [htupleAtTime]
    have havoid := ActiveRoundActions.other_follower_avoids_down_target p.two_le_m snapshot projected
      hslotProjected hmissingProjected hnoReleased j hjiProjected
    rw [hprojectedSelected] at havoid
    exact havoid
  · rw [htupleAtTime]
    exact ActiveRoundActions.tuple_coordinator_ne_follower p.two_le_m projected iF
  · intro j hj
    have hordinary : ∀ (a : Fin sourceWindow.length) (j : Fin (p.m - 1)), ∃ choice memory,
        (sourceWindow[a.val].output.preparation.followers.followers j).configuration =
          .ordinary choice memory := by
      intro a j
      obtain ⟨choice, memory, _, _, hchoice, _⟩ := hrunSafety.2 a j
      exact ⟨choice, memory, hchoice⟩
    obtain ⟨prior, hprior, hpriorTime, priorSelected, hpriorSelected, hpayload,
      hevent, hindex, accepted, haccepted, hacceptedTime, hacceptedDown⟩ :=
      first_live_prior_down_of_ordinary_choices initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan hmode
        hfirst hinitialFollowers hordinary k selected hselectionOutput j hj
    refine ⟨prior, ?_, hpriorTime.trans_eq (congrArg Fin.val htime), priorSelected,
      hpriorSelected, hpayload, hevent, hindex, accepted, ?_, hacceptedTime, hacceptedDown⟩
    · rw [hwindow]
      exact hprior
    · rw [hwindow]
      exact haccepted

/-- Before acceptance, the actual selected follower receives the rounded
receiver reward exactly on hash one. The selector concerns the incoming
state, so acceptance at this round's end does not change this branch. -/
theorem actual_first_live_before_down_feedback
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hrW : r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
        rate rewards C_star C_h z))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (hi : i ∈ selected.view.pendingAtChoice)
    (hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 t).1 = i)
    (hbefore : ∃ incoming memory,
      r.input.state.followers i = .ordinary incoming memory ∧ incoming.lastDown = none) :
    (r.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val =
      if CoordinatorLocalArmChoice.currentDownHash selected.view.payload (r.input.row.2 t) i = 1 then
        RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
            (r.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
      else 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hformula, _⟩ :=
    actual_first_live_mixed_down_feedback rate rewards C_star C_h z t r hr hrW
      selected hsel i hi hdown hdraw
  obtain ⟨incoming, memory, hinput, hnone⟩ := hbefore
  exact hformula incoming memory hinput hnone

/-- After acceptance, the same actual receiver reward reaches the coordinator
on hash zero. CHOICE pending status is produced inside the mixed-frame
theorem from this inline incoming-state selector. -/
theorem actual_first_live_after_down_feedback
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hrW : r ∈ ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstLiveSourceStoppedReleaseEndpoint.completeRecords
        rate rewards C_star C_h z))
    (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (i : Fin (p.m - 1))
    (hi : i ∈ selected.view.pendingAtChoice)
    (hdown : PublicDiscreteDraws.slotDraw (r.input.row.2 t).1 = PublicDiscreteDraws.downSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 t).1 = i)
    (hafter : ∃ incoming memory,
      r.input.state.followers i = .ordinary incoming memory ∧
        incoming.lastDown = some (selected.view.payload.downRecord i))
    (hzero : CoordinatorLocalArmChoice.currentDownHash selected.view.payload (r.input.row.2 t) i = 0) :
    (r.output.preparation.feedback.observations
        (ActiveRoundActions.coordinator p.two_le_m)).val.val =
      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          (r.input.row.2 t).1).val (PublicDiscreteDraws.followerPlayer p.two_le_m i))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hformula⟩ :=
    actual_first_live_mixed_down_feedback rate rewards C_star C_h z t r hr hrW
      selected hsel i hi hdown hdraw
  exact (hformula hafter).2 hzero

end Bandits.Support.ReferenceFirstLiveHandoverDownFeedback

end
