/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionHandoverReplay

import Mathlib.Tactic

/-!
# Physical later-handover decoder correspondence

The calendar in this module is an analytical replay of one actual later
installation.  Its retained dates use the selected payload, complete actual
round rows, whole reward tables, and actual acceptance flags.  Dates outside
the handover prefix are zero-reward padding and are used only through their
inert live-round transition.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions BootstrapPrivateRoundStreams
open ActiveRoundActions
open HandoverStoppedDecoderReplay

namespace Bandits.Support.ReferencePostReplacementCollectionHandoverDecoderCorrespondence

private local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-! The action input is made from the retained record's entire current row.
The DOWN word is the selected payload's literal stored word; the DOWN sample,
UP sample, slot, follower, tuple, pilots, and fast-arm fields are the actual
current row controls. -/

public def handoverRoundInput (payload : ReferenceActivePhysicalStep.Payload rate)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) :
    ActiveRoundActions.RoundInput payload.assignment (AffineBatchDecoder.width p) :=
  let u := row.2 t
  { slot := PublicDiscreteDraws.slotDraw u.1
    selected := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1
    tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1
    pilots := fun player => PublicDiscreteDraws.pilotDraw (K_pos p) player u.1
    down := ⟨u.2 (0, PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1),
      CoordinatorLocalArmChoice.storedDownFlatWord payload
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1)⟩
    up := ⟨u.2 (1, PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1),
      fun _ => 0⟩
    fast := payload.assignment.auxiliary
    fast_outside := payload.assignment.auxiliary_outside }

public theorem handoverRoundInput_down_bit
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) :
    (handoverRoundInput payload row t).down.bit =
      CoordinatorLocalArmChoice.currentDownHash payload (row.2 t)
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1) := rfl

/-! The actual action frame is needed for complete feedback, including zero
observations.  In a DOWN round, it follows from the actual choice states and
the retained current payload word for every occupied follower. -/

public theorem actual_handover_down_actions
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
    (ReferenceActivePhysicalStep.prepare x).arms.actions =
      ActiveRoundActions.actions p.two_le_m snapshot
        (handoverRoundInput selected.view.payload x.row x.time) := by
  classical
  let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
    ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
  let u := x.row.2 x.time
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1
  let hash := CoordinatorLocalArmChoice.currentDownHash selected.view.payload u i
  let selectedDraw := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1
  let projected := handoverRoundInput selected.view.payload x.row x.time
  have hdownNotData : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot := by decide
  have hdownNotUp : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot := by decide
  have hslot : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.downSlot := hdown
  have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K u.1 = i := hdraw
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1 = tuple := rfl
  have hhash : projected.down.bit = hash := by
    change (handoverRoundInput selected.view.payload x.row x.time).down.bit = hash
    rw [handoverRoundInput_down_bit]
    dsimp [hash, u]
    rw [hdraw]
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
  funext player
  rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨j, hplayer⟩
  · subst player
    rw [ReferenceActivePhysicalStep.action_eq_down_sendArm
      (ReferenceActivePhysicalStep.prepare x)
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
    have hindex : jIndex = j := by apply Fin.ext; rfl
    rw [ActiveRoundActions.actions_follower]
    rw [← hindex]
    have hlocalOrdinary :
        (DeclaredFollowerLocalRound.prepare rate jIndex x.row
          (x.state.activations jIndex) x.time
          (x.active jIndex) (x.state.followers jIndex)).configuration =
            .ordinary (states jIndex) (memories jIndex) := by
      have h := hprepared jIndex
      rw [(ReferenceActivePhysicalStep.prepare x).followers.followers_eq jIndex,
        ReferenceActiveFeedbackCut.prepareFollowers_apply] at h
      exact h
    obtain ⟨before, beforeMemory, offered, hinput, hstart, hchoiceArm⟩ :=
      ReferenceActiveDataOwnership.prepare_ordinary_choice jIndex x.row
        (x.state.activations jIndex) x.time (x.active jIndex)
        (x.state.followers jIndex) (states jIndex) (memories jIndex) hlocalOrdinary
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
            exact (by decide : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot) hup
          have hother := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_other
            (states jIndex) u jIndex offered hstatus hnotdata hnotSelected
          have hkernel := ActiveRoundActions.followerAction_unoccupied_down
            p.two_le_m snapshot projected jIndex hstatus hslotProjected
          rw [hkernel]
          simpa [projected, handoverRoundInput, htuple] using hother
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
            exact (by decide : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot) hup
          by_cases hcollision : PrelaunchBufferRecovery.downArm rate.eta
              (selected.view.payload.downRecord jIndex) =
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K u.1).val
                  (PublicDiscreteDraws.followerPlayer p.two_le_m selectedDraw)
          · have hcore := ActiveFollowerArmChoice.followerArmChoiceCore_pending_collision_escape
              (states jIndex) u jIndex offered (selected.view.payload.downRecord jIndex)
              hstatus hlast (Or.inl ⟨hslot, hcollision⟩)
            have hassignedCollision : selected.view.payload.assignment.assigned jIndex =
                tuple.val (PublicDiscreteDraws.followerPlayer p.two_le_m selectedDraw) :=
              harm.symm.trans hcollision
            have hkernel : ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex =
                ActiveFollowerArmChoice.downAuxiliaryArm rate.eta
                  (selected.view.payload.downRecord jIndex) := by
              simp [ActiveRoundActions.followerAction, snapshot, projected,
                handoverRoundInput, u, tuple, selectedDraw, hstatus, hslot, hselectedDraw,
                hassignedCollision, haux]
              intro hbad
              exact False.elim
                ((by decide : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.dataSlot) hbad)
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
                exact (by decide : PublicDiscreteDraws.downSlot ≠ PublicDiscreteDraws.upSlot) hup
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
              simp [ActiveRoundActions.followerAction, snapshot, projected,
                handoverRoundInput, u, tuple, hstatus, hslot, hselectedDraw,
                hnotActionCollisionAtI, harm, hdownNotUp]
            rw [hkernel]
            exact hcore
      | released => exact False.elim (hnotReleased jIndex hstatus)
    have hcoreChoice : ActiveFollowerArmChoice.followerArmChoice (states jIndex)
        x.row x.time jIndex offered =
        some (ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex) := by
      simpa only [ActiveFollowerArmChoice.followerArmChoice] using hcore
    have harmChoice :
        (DeclaredFollowerLocalRound.prepare rate jIndex x.row
          (x.state.activations jIndex) x.time (x.active jIndex)
          (x.state.followers jIndex)).arm =
          ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex :=
      Option.some.inj (hchoiceArm.symm.trans hcoreChoice)
    change (ReferenceActivePhysicalStep.prepare x).arms.actions
        (PublicDiscreteDraws.followerPlayer p.two_le_m jIndex) =
      ActiveRoundActions.followerAction p.two_le_m snapshot projected jIndex
    exact (ReferenceActivePhysicalStep.PreparedRound.action_follower
      (ReferenceActivePhysicalStep.prepare x) jIndex).trans harmChoice

public def handoverWholeRewardRowAt
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (t : Fin p.T) : ActiveRoundActions.RewardRow p.K :=
  ⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (record.input.rewards t a),
    fun a => RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p)
      (record.input.rewards t a)⟩

public def handoverWholeRewardRow
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ActiveRoundActions.RewardRow p.K :=
  handoverWholeRewardRowAt record record.input.time

public def handoverZeroRow : ActiveRoundActions.RewardRow p.K :=
  ReferenceFirstLiveHandoverSnapshotPrefix.zeroRow

public def handoverPadding (payload : ReferenceActivePhysicalStep.Payload rate)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (t : Fin p.T) :
    ActiveRoundActions.LiveRoundData payload.assignment (AffineBatchDecoder.width p) :=
  ⟨handoverRoundInput payload
      (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) t,
    handoverZeroRow, fun _ => false⟩

public def actualLaterHandoverLive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (handover : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (t : Fin p.T) :
    ActiveRoundActions.LiveRoundData payload.assignment (AffineBatchDecoder.width p) := by
  classical
  if hwindow : payload.sigma.val ≤ t.val ∧
      t.val < payload.sigma.val + handover.length then
    exact match ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z with
      | none => handoverPadding payload z t
      | some record =>
          ⟨handoverRoundInput payload record.input.row t,
            handoverWholeRewardRow record,
            ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload record⟩
  else
    exact handoverPadding payload z t

public theorem completeSuffixRecord_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  exact ReferenceAssignmentFollowerMassSteps.complete_record_time rate rewards C_star C_h z k

public theorem actualRecord_time_eq
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record) :
    record.input.time = t := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  by_cases hs : s ≤ t.val
  · have hlookup : R[t.val - s]? = some record := by
      change (if s ≤ t.val then R[t.val - s]? else none) = some record at hrecord
      rw [ite_eq_left hs] at hrecord
      exact hrecord
    obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
    have htime := completeSuffixRecord_time rate rewards C_star C_h z ⟨t.val - s, hk⟩
    have hvalue : record.input.time.val = s + (t.val - s) := by
      rw [← heq]
      exact htime
    apply Fin.ext
    rw [hvalue]
    omega
  · have hnone : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t z = none := by
      simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, s, hs]
    rw [hnone] at hrecord
    cases hrecord

public theorem actualLaterHandoverLive_of_actual_record
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (handover : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (t : Fin p.T)
    (hwindow : payload.sigma.val ≤ t.val ∧
      t.val < payload.sigma.val + handover.length)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some record) :
    actualLaterHandoverLive rate rewards C_star C_h z payload handover t =
      ⟨handoverRoundInput payload record.input.row t,
        handoverWholeRewardRowAt record t,
        ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload record⟩ := by
  have htime := actualRecord_time_eq
    rate rewards C_star C_h z t record hrecord
  simp [actualLaterHandoverLive, hwindow, hrecord, handoverWholeRewardRow, htime]

/-- Before the actual birth time, this analytical calendar consists only of
zero-reward, nonaccepting padding.  Its strict-past live snapshot therefore
remains the all-unoccupied birth snapshot. -/
public theorem actualLaterHandoverLive_prebirth_snapshot
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (handover : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (t : Fin p.T) (ht : t.val ≤ payload.sigma.val) :
    ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (actualLaterHandoverLive rate rewards C_star C_h z payload handover) t =
      ActiveRoundActions.initialSnapshot payload.assignment := by
  unfold ActiveObservationBridge.liveSnapshotBefore
  have hfold (k : ℕ) (hk : k ≤ t.val) :
      ActiveRoundActions.liveSegment p.two_le_m
        ((List.ofFn (fun s : Fin p.T =>
          actualLaterHandoverLive rate rewards C_star C_h z payload handover s)).take k) =
        ActiveRoundActions.initialSnapshot payload.assignment := by
    induction k with
    | zero => rfl
    | succ k ih =>
        have hkT : k < p.T := by omega
        have hkBirth : k < payload.sigma.val := by omega
        have hpad : actualLaterHandoverLive rate rewards C_star C_h z payload handover
            ⟨k, hkT⟩ = handoverPadding payload z ⟨k, hkT⟩ := by
          simp [actualLaterHandoverLive, hkBirth]
        rw [List.take_succ_eq_append_getElem
          (by simpa only [List.length_ofFn] using hkT)]
        simp only [List.getElem_ofFn, ActiveRoundActions.liveSegment,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
        rw [hpad]
        simp only [handoverPadding, handoverZeroRow]
        rw [ReferenceFirstLiveHandoverSnapshotPrefix.finish_zero]
        exact ih (by omega)
  exact hfold t.val le_rfl

private theorem installationBirth_time
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record payload) :
    payload.sigma.val = record.input.time.val := by
  unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hbirth
  split at hbirth
  · exact hbirth.2
  · exact hbirth.2
  · contradiction

/-- The accepted later-installation birth API supplies the selected payload,
the complete current selection, and each follower's actual unoccupied choice
state. The source's retained occupied-field condition is kept for later
handover rounds. -/
public theorem actual_later_handover_birth_choice_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hlater : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      ∃ selected : ReferenceActivePhysicalStep.Selection R[b.val].input,
        ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
          ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
            ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
            R[b.val].output.preparation.coordinator.selection = some selected ∧
            selected.view.payload = payload ∧
            selected.view.pendingAtChoice = Finset.univ ∧
            (∀ i, (R[b.val].output.preparation.followers.followers i).configuration =
              .ordinary (states i) (memories i)) ∧
            (∀ i, (states i).status = .unoccupied) ∧
            (∀ i, (states i).status ≠ .unoccupied →
              (states i).lastDown = some (payload.downRecord i)) := by
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  have hbirthData :=
    ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_birth_data
      rate rewards C_star C_h z b
  rw [ite_eq_left hlater] at hbirthData
  obtain ⟨registers, _owned, _base, birthSelected, _hnext, hbirth,
    hbirthSelection, hbirthPayload, hbirthPending, _hfollowing,
    hfollowers, _hpartition, _hnoReleased, _hframes⟩ := hbirthData
  have hchoiceData :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h z b birthSelected hbirthSelection
  obtain ⟨states, memories, hchoices, hfields, _⟩ := hchoiceData
  have hunoccupied : ∀ i, (states i).status = .unoccupied := by
    intro i
    obtain ⟨_before, _beforeMemory, choice, choiceMemory, _hinput,
      _hbeforeUnoccupied, hchoice, hchoiceUnoccupied, _⟩ := hfollowers i
    have heq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hchoices i).symm.trans hchoice)
    rw [heq.1]
    exact hchoiceUnoccupied
  refine ⟨registers.payload, birthSelected, states, memories, hbirth,
    hbirthSelection, hbirthPayload, hbirthPending, ?_, hunoccupied, ?_⟩
  · intro i
    exact hchoices i
  · intro i hi
    simpa only [hbirthPayload] using hfields i hi

public def handoverRoundData (payload : ReferenceActivePhysicalStep.Payload rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (snapshot : ActiveRoundActions.Snapshot payload.assignment)
    (cutoffBefore overflowAfter : Bool) (t : Fin p.T) : RoundData p payload.assignment :=
  ⟨snapshot, handoverRoundInput payload record.input.row t,
    handoverWholeRewardRowAt record t, cutoffBefore, overflowAfter⟩

private theorem decoderRoundInput_eq {B : ℕ}
    {left right : AffineBatchDecoder.RoundInput B}
    (hselected : left.selected = right.selected)
    (hreceiver : left.receiverEnabled = right.receiverEnabled)
    (hsample : left.sample = right.sample)
    (hreward : left.roundedReward = right.roundedReward) : left = right := by
  cases left
  cases right
  simp_all

/-! This one-round identity compares every field used by the literal decoder
input, including zero feedback.  It is conditional only on the actual choice,
prepared follower states, the current selected DOWN case, and the selected
follower's actual unoccupied status.  The calendar snapshot theorem supplies
these fields from the actual later-installation stages. -/

public theorem actual_handover_decoder_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselection : record.output.preparation.coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hprepared : ∀ j,
      (record.output.preparation.followers.followers j).configuration =
        .ordinary (states j) (memories j))
    (hfields : ∀ j, (states j).status ≠ .unoccupied →
      (states j).lastDown = some (selected.view.payload.downRecord j))
    (hnotReleased : ∀ j, (states j).status ≠ .released)
    (i : Fin (p.m - 1)) (hi : i ∈ selected.view.pendingAtChoice)
    (hdown : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.downSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i)
    (hunoccupied : (states i).status = .unoccupied)
    (cutoffBefore overflowAfter : Bool) :
    HandoverStoppedDecoderReplay.observationTrace p selected.view.payload.assignment
        (handoverRoundData selected.view.payload record
          ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
          cutoffBefore overflowAfter) i record.input.time =
      ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate (states i) := by
  classical
  let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
    ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
  let input := handoverRoundInput selected.view.payload record.input.row record.input.time
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hselection' :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    rw [← hprep]
    exact hselection
  have hprepared' : ∀ j,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers j).configuration =
        .ordinary (states j) (memories j) := by
    intro j
    rw [← hprep]
    exact hprepared j
  have hactions := actual_handover_down_actions record.input selected hselection'
    states memories hprepared' hfields hnotReleased i hi hdown hdraw
  have hactions' : record.output.preparation.arms.actions =
      ActiveRoundActions.actions p.two_le_m snapshot input := by
    rw [hprep]
    exact hactions
  have hrounded :
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)).val.val =
      ActiveRoundActions.feedback p.two_le_m snapshot input (handoverWholeRewardRow record)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
    calc
      _ = FiniteBanditModel.playerFeedback record.output.preparation.arms.actions
          (fun a => ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ))
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) :=
        record.output.preparation.feedback.feedback_scalar_eq_playerFeedback _
      _ = ActiveRoundActions.feedback p.two_le_m snapshot input (handoverWholeRewardRow record)
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
        rw [hactions']
        rfl
  have hsample : input.down.sample =
      (record.input.row.2 record.input.time).2 (0, i) := by
    dsimp [input, handoverRoundInput]
    rw [hdraw]
  have hselectedObs : input.slot = PublicDiscreteDraws.downSlot ∧
      input.selected = i ∧ i ∈ snapshot.missing := by
    refine ⟨?_, ?_⟩
    · simpa [input, handoverRoundInput] using hdown
    · constructor
      · simpa [input, handoverRoundInput] using hdraw
      · simpa [snapshot] using hi
  have hselectedPhysical :
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.downSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i := ⟨hdown, hdraw⟩
  apply decoderRoundInput_eq
  · simp [HandoverStoppedDecoderReplay.observationTrace, handoverRoundData,
      ActiveFollowerDownAcceptance.currentRoundInput, handoverRoundInput,
      hselectedPhysical]
    intro _
    exact hselectedObs.2.2
  · simp [HandoverStoppedDecoderReplay.observationTrace, handoverRoundData,
      ActiveFollowerDownAcceptance.currentRoundInput, hunoccupied]
  · simpa [HandoverStoppedDecoderReplay.observationTrace, handoverRoundData,
      ActiveFollowerDownAcceptance.currentRoundInput, input, handoverRoundInput] using hsample
  · simpa [HandoverStoppedDecoderReplay.observationTrace, handoverRoundData,
      ActiveFollowerDownAcceptance.currentRoundInput, handoverWholeRewardRowAt,
      handoverWholeRewardRow, input, snapshot] using hrounded.symm

private theorem handover_status_step
    (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (states next : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories nextMemories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hc : ∀ i, (r.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hn : ∀ i, (r.output.followers i).configuration = .ordinary (next i) (nextMemories i))
    (hold : ∀ i, (states i).status = .unoccupied →
      ReferencePrelaunchFollower.acceptedStart (states i) <
        (selected.view.payload.downRecord i).val.sigma)
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hnextFields : ∀ i, (next i).status = .pending →
      (next i).lastDown = some (selected.view.payload.downRecord i))
    (hno : ∀ i, (states i).status ≠ .released)
    (hnextNo : ∀ i, (next i).status ≠ .released)
    (hne : selected.view.pendingAtChoice.Nonempty) (i : Fin (p.m - 1)) :
    (ActiveRoundActions.finishLiveRound p.two_le_m
      ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
      (handoverRoundInput selected.view.payload r.input.row r.input.time)
      (handoverWholeRewardRow r)
      (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag selected.view.payload r)).status i =
        (next i).status := by
  classical
  have hfinish := ReferenceFirstLiveHandoverSnapshotPrefix.finish_status_while_missing
    (⟨selected.view.pendingAtChoice, fun j => (states j).status⟩ :
      ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (handoverRoundInput selected.view.payload r.input.row r.input.time)
    (handoverWholeRewardRow r)
    (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag selected.view.payload r) hne i
  refine hfinish.trans ?_
  by_cases hu : (states i).status = .unoccupied
  · by_cases hn0 : (next i).status = .unoccupied
    · have hf : ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag
          selected.view.payload r i = false := by
        simp only [ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag,
          hc i, hn i, hn0, reduceCtorEq, and_false, decide_false]
      simp only [ActiveRoundActions.statusAfterAcceptance, hu, hf,
        Bool.false_eq_true, and_false, ite_false, hn0]
    · have hp : (next i).status = .pending := by
        cases h : (next i).status <;> simp_all
      have hf := (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag_ordinary_iff
        selected.view.payload r i _ _ _ _ (hc i) (hn i)).mpr
          ⟨hu, hnextFields i hp, hp⟩
      have hn' : r.output.next.followers i = .ordinary (next i) (nextMemories i) := by
        rw [r.output_eq] at hn ⊢
        exact hn i
      obtain ⟨choice, memory, hc', _, _, hchange⟩ :=
        ReferenceFollowerReplyChronology.record_choice_chronology r i _ _ hn'
      have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hc'.symm.trans (hc i))
      obtain ⟨heq, hmemory⟩ := he
      subst choice
      have hstart : ReferencePrelaunchFollower.acceptedStart (next i) =
          (selected.view.payload.downRecord i).val.sigma := by
        simp only [ReferencePrelaunchFollower.acceptedStart, hnextFields i hp]
      have hneStart : ReferencePrelaunchFollower.acceptedStart (states i) ≠
          ReferencePrelaunchFollower.acceptedStart (next i) := by
        rw [hstart]
        exact Nat.ne_of_lt (hold i hu)
      obtain ⟨logged, cut, after, raw, M, scan, registers, lastService,
        hi, hd, ho, _⟩ := hchange hneStart
      have hs := ReferenceFirstLiveHandoverSnapshotPrefix.acceptedDown_selected r i M
        ⟨logged, cut, after, raw, scan, registers, lastService, hi, hd, ho⟩
      rw [hp]
      apply ite_eq_left
      exact ⟨hu, hs.1, hs.2, hf⟩
  · have hp : (states i).status = .pending := by
      cases h : (states i).status <;> simp_all
    have hout := hn i
    rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r] at hout
    obtain ⟨choice, memory, post, hc', hr, hf, _, _⟩ :=
      ReferenceFollowerReplyChronology.finishFollower_ordinary_inversion _ _ _ _ _ hout
    have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hc'.symm.trans (hc i))
    obtain ⟨heq, hmemory⟩ := he
    subst choice
    subst memory
    have hs := (ReferenceActiveConfirmationRelease.pending_choice_successful_finish_preserves_status
      r.output.preparation selected hsel i (states i) (memories i) hne (hc i)
      hp (hfields i hu) post hr (next i) (nextMemories i) hf).2.1
    simp only [ActiveRoundActions.statusAfterAcceptance, hp, reduceCtorEq,
      false_and, ite_false, hs]

private theorem handover_confirmation_iff
    (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive
      selected.view.payload selected.view.cutoff r.input.time)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hc : ∀ i, (r.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hno : ∀ i, (states i).status ≠ .released)
    (hne : selected.view.pendingAtChoice.Nonempty) :
    ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected ↔
      ActiveRoundActions.confirmation p.two_le_m
        ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
        (handoverRoundInput selected.view.payload r.input.row r.input.time)
        (handoverWholeRewardRow r)
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 r.input.time).1) := by
  let input := handoverRoundInput selected.view.payload r.input.row r.input.time
  let snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment :=
    ⟨selected.view.pendingAtChoice, fun j => (states j).status⟩
  let i := input.selected
  have hinvariant : ActiveRoundActions.no_released_while_missing snapshot := fun _ j => hno j
  have hobs (hd : input.slot = PublicDiscreteDraws.downSlot)
      (hi : i ∈ selected.view.pendingAtChoice) :
      CoordinatorLocalArmChoice.ownGridObservationValue r.output.preparation.coordinatorObservation =
        ActiveRoundActions.feedback p.two_le_m snapshot input (handoverWholeRewardRow r)
          (ActiveRoundActions.coordinator p.two_le_m) := by
    have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
      rw [r.output_eq]
      rfl
    have ha := actual_handover_down_actions r.input selected (hp ▸ hsel)
      states memories (fun j => hp ▸ hc j) hfields hno i hi hd rfl
    have ha' : r.output.preparation.arms.actions =
        ActiveRoundActions.actions p.two_le_m snapshot input := by
      rw [hp]
      exact ha
    have hnormalized :
        (r.output.preparation.feedback.observations
          (ActiveRoundActions.coordinator p.two_le_m)).val.val =
        CoordinatorLocalArmChoice.ownGridObservationValue
          r.output.preparation.coordinatorObservation :=
      r.output.preparation.feedback.observation_grid_value _
    rw [← hnormalized]
    calc
      _ = FiniteBanditModel.playerFeedback r.output.preparation.arms.actions
          (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ))
          (ActiveRoundActions.coordinator p.two_le_m) :=
        r.output.preparation.feedback.feedback_scalar_eq_playerFeedback _
      _ = _ := by rw [ha']; rfl
  constructor
  · rintro ⟨_, _, hd, hi, hz, hpositive⟩
    refine ⟨hd, rfl, hi, hz, ?_⟩
    rw [← hobs hd hi]
    exact hpositive
  · intro hconfirm
    have _hpending := ActiveRoundActions.confirmation_implies_pending p.two_le_m
      snapshot input (handoverWholeRewardRow r) i hinvariant hconfirm
    obtain ⟨hd, _, hi, hz, hpositive⟩ := hconfirm
    refine ⟨hlive, hne, hd, hi, hz, ?_⟩
    rw [hobs hd hi]
    exact hpositive

private theorem installationBirth_unique (r : Record rate)
    (P Q : ReferenceActivePhysicalStep.Payload rate)
    (hP : ReferenceAssignmentPayloadPersistence.InstallationBirth r P)
    (hQ : ReferenceAssignmentPayloadPersistence.InstallationBirth r Q) : P = Q := by
  unfold ReferenceAssignmentPayloadPersistence.InstallationBirth at hP hQ
  split at hP <;> simp_all <;> rfl

private theorem selectionAt_cutoff
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hs : ReferenceActivePhysicalStep.selectionAt x payload started time weights arm = some selected) :
    selected.view.cutoff = CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u := by
  unfold ReferenceActivePhysicalStep.selectionAt at hs
  split at hs
  · cases hs
    rfl
  · cases hs

private theorem laterBirth_cutoff
    (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hb : ReferenceCollectionPhaseHistory.laterChosen r.input = true) :
    selected.view.cutoff = none := by
  have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  unfold ReferenceCollectionPhaseHistory.laterChosen at hb
  rw [← hp] at hb
  cases hcoord : r.output.preparation.coordinator
    <;> try simp only [hcoord, Bool.false_eq_true] at hb
  rename_i payload ledger clock cutoff outcome
  cases outcome <;> try simp only [Bool.false_eq_true] at hb
  rename_i core consistent started hstart instruction hinstruction output hlocal clockData installed arm
  have hcut := selectionAt_cutoff r.input installed.registers.payload started instruction.time
    installed.registers.complementWeights arm selected
    (by simpa only [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection] using hs)
  have heffect := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val r.input.time
    clock ledger.pending started instruction core.clock_parameter_valid core.clock_registers_valid
    core.clock_start_time_valid hstart hinstruction
  rw [hcut, heffect.2.2.2.1]
  rfl

/-- Across adjacent actual rounds, an awaiting choice retains the old reply;
its predecessor cannot already be occupied with the new word. -/
private theorem adjacent_choice_status
    (r nextRecord : Record rate) (payload : ReferenceActivePhysicalStep.Payload rate)
    (hadj : nextRecord.input.state = r.output.next)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hc : ∀ i, (nextRecord.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ReferenceActiveDataOwnership.carriedOccupiedFields payload r.output.next)
    (hold : ∀ i, (states i).status = .unoccupied →
      ReferencePrelaunchFollower.acceptedStart (states i) < (payload.downRecord i).val.sigma) :
    ∃ (next : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (nextMemories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      (∀ i, (r.output.followers i).configuration = .ordinary (next i) (nextMemories i)) ∧
      (∀ i, r.output.next.followers i = .ordinary (next i) (nextMemories i)) ∧
      (∀ i, (next i).status = (states i).status) := by
  have hprepare (i : Fin (p.m - 1)) := hc i
  simp only [nextRecord.output.preparation.followers.followers_eq] at hprepare
  have hinversion (i : Fin (p.m - 1)) :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i nextRecord.input.row
      (nextRecord.input.state.activations i) nextRecord.input.time (nextRecord.input.active i)
      (nextRecord.input.state.followers i) (states i) (memories i) (hprepare i)
  choose next nextMemories hin hstart hreply _hzero using hinversion
  have hout (i : Fin (p.m - 1)) :
      r.output.next.followers i = .ordinary (next i) (nextMemories i) := by
    rw [← hadj]
    exact hin i
  refine ⟨next, nextMemories, ?_, hout, ?_⟩
  · intro i
    have h := hout i
    rw [r.output_eq] at h ⊢
    exact h
  · intro i
    by_cases hu : (states i).status = .unoccupied
    · have hn : (next i).status = .unoccupied := by
        by_contra hn
        have hf := hfields i
        simp only [ReferenceActiveDataOwnership.occupiedFields, hout i] at hf
        have hlast := hf hn
        have hs := ReferenceFollowerReplyChronology.acceptedStart_eq_of_reply_eq (hreply i)
        have hstrict := hold i hu
        rw [hs, ReferencePrelaunchFollower.acceptedStart, hlast] at hstrict
        exact (Nat.lt_irrefl _) hstrict
      exact hn.trans hu.symm
    · have hs := ReferenceActiveDataOwnership.startRound_status
        nextRecord.input.time (next i) (states i) (nextMemories i) (memories i) (hstart i)
      exact (hs.resolve_left hu).symm

private theorem handover_choice_step
    (r nextRecord : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hsel : r.output.preparation.coordinator.selection = some selected)
    (pendingNext : Finset (Fin (p.m - 1)))
    (states nextStates : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories nextMemories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hc : ∀ i, (r.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hcNext : ∀ i, (nextRecord.output.preparation.followers.followers i).configuration =
      .ordinary (nextStates i) (nextMemories i))
    (hold : ∀ i, (states i).status = .unoccupied →
      ReferencePrelaunchFollower.acceptedStart (states i) < (selected.view.payload.downRecord i).val.sigma)
    (holdNext : ∀ i, (nextStates i).status = .unoccupied →
      ReferencePrelaunchFollower.acceptedStart (nextStates i) < (selected.view.payload.downRecord i).val.sigma)
    (hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hout : ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload r.output.next)
    (hno : ∀ i, (states i).status ≠ .released)
    (hnoNext : ∀ i, (nextStates i).status ≠ .released)
    (hne : selected.view.pendingAtChoice.Nonempty)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time)
    (hadj : nextRecord.input.state = r.output.next)
    (hpend : pendingNext =
      if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent r selected then
        selected.view.pendingAtChoice.erase
          (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1)
      else selected.view.pendingAtChoice) :
    ActiveRoundActions.finishLiveRound p.two_le_m
      ⟨selected.view.pendingAtChoice, fun i => (states i).status⟩
      (handoverRoundInput selected.view.payload r.input.row r.input.time)
      (handoverWholeRewardRow r)
      (ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag selected.view.payload r) =
        ⟨pendingNext, fun i => (nextStates i).status⟩ := by
  obtain ⟨next, nextMemory, hnConfig, hnNext, hnStatus⟩ := adjacent_choice_status
    r nextRecord selected.view.payload hadj nextStates nextMemories hcNext hout holdNext
  have hnextFields (i : Fin (p.m - 1)) (hi : (next i).status = .pending) :
      (next i).lastDown = some (selected.view.payload.downRecord i) := by
    have h := hout i
    simp only [ReferenceActiveDataOwnership.occupiedFields, hnNext i] at h
    exact h (by rw [hi]; decide)
  have hs := handover_status_step r selected hsel states next memories nextMemory hc hnConfig
    hold hf hnextFields hno (fun i => (hnStatus i) ▸ hnoNext i) hne
  have hconfirm := handover_confirmation_iff r selected hsel hlive states memories hc hf hno hne
  apply congrArg₂ ActiveRoundActions.Snapshot.mk
  · change (if ActiveRoundActions.confirmation p.two_le_m
        ⟨selected.view.pendingAtChoice, fun i => (states i).status⟩
        (handoverRoundInput selected.view.payload r.input.row r.input.time) (handoverWholeRewardRow r)
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1)
      then selected.view.pendingAtChoice.erase
        (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 r.input.time).1)
      else selected.view.pendingAtChoice) = pendingNext
    rw [← hconfirm]
    exact hpend.symm
  · funext i
    exact (hs i).trans (hnStatus i)

private theorem calendar_snapshot_induction
    {a : ActiveRoundActions.Assignment p.m p.K} {N : ℕ}
    (live : Fin p.T → ActiveRoundActions.LiveRoundData a (AffineBatchDecoder.width p))
    (times : Fin N → Fin p.T) (snapshots : Fin N → ActiveRoundActions.Snapshot a)
    (hzero : ∀ h : 0 < N,
      ActiveObservationBridge.liveSnapshotBefore p a live (times ⟨0, h⟩) = snapshots ⟨0, h⟩)
    (hdates : ∀ j : Fin N, ∀ h : j.val + 1 < N,
      (times ⟨j.val + 1, h⟩).val = (times j).val + 1)
    (hstep : ∀ j : Fin N, ∀ h : j.val + 1 < N,
      ActiveRoundActions.finishLiveRound p.two_le_m (snapshots j) (live (times j)).input
        (live (times j)).rewards (live (times j)).acceptCurrent = snapshots ⟨j.val + 1, h⟩) :
    ∀ j : Fin N, ActiveObservationBridge.liveSnapshotBefore p a live (times j) = snapshots j := by
  have h (n : ℕ) : ∀ hn : n < N,
      ActiveObservationBridge.liveSnapshotBefore p a live (times ⟨n, hn⟩) = snapshots ⟨n, hn⟩ := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
        intro hn
        let j : Fin N := ⟨n, by omega⟩
        rw [ReferenceFirstLiveHandoverSnapshotPrefix.snapshot_successor live
          (times j) (times ⟨n + 1, hn⟩) (hdates j hn), ih j.isLt]
        exact hstep j hn
  intro j
  exact h j.val j.isLt

/-- The original birth record followed by its complete continuing suffix,
retained through the actual missing-confirmation choices. -/
public def actualHandoverRecords
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length) :
    List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[b.val] ::
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix rate rewards C_star C_h z (b.val + 1)).takeWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice

section ActualCalendar

variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h

variable (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
  rate z rewards C_star C_h).length)

local notation "W" => ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
  rate rewards C_star C_h z (b.val + 1)
local notation "V" => R[b.val] :: W
local notation "H" => actualHandoverRecords rate rewards C_star C_h z b

private theorem handover_index (j : Fin (H).length) :
    ∃ hk : b.val + j.val < (R).length, H[j.val] = R[b.val + j.val]'hk := by
  have hV : (V).IsPrefix ((R).drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hH : (H).IsPrefix ((R).drop b.val) := (List.takeWhile_prefix _).trans hV
  have hlen := hH.length_le
  simp only [List.length_drop] at hlen
  refine ⟨by omega, ?_⟩
  rw [hH.getElem j.isLt, List.getElem_drop]

private theorem handover_time (j : Fin (H).length) :
    H[j.val].input.time.val = R[b.val].input.time.val + j.val := by
  obtain ⟨hk, heq⟩ := handover_index rewards C_star C_h z b j
  rw [heq, completeSuffixRecord_time rate rewards C_star C_h z ⟨_, hk⟩,
    completeSuffixRecord_time rate rewards C_star C_h z b]
  simp only [Nat.add_assoc]

private theorem handover_lookup (j : Fin (H).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      H[j.val].input.time z = some H[j.val] := by
  obtain ⟨hk, heq⟩ := handover_index rewards C_star C_h z b j
  have ht := completeSuffixRecord_time rate rewards C_star C_h z ⟨_, hk⟩
  rw [heq]
  simp only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ht,
    Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hk]

private theorem handover_adjacent (j : Fin (H).length) (hj : j.val + 1 < (H).length) :
    H[j.val + 1].input.state = H[j.val].output.next := by
  obtain ⟨hk, heq⟩ := handover_index rewards C_star C_h z b j
  obtain ⟨hk', heq'⟩ := handover_index rewards C_star C_h z b ⟨j.val + 1, hj⟩
  rw [heq, heq']
  exact ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    rewards C_star C_h z (b.val + j.val) (by simpa only [Nat.add_assoc] using hk')

private theorem handover_choice_data
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true) :
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      ∀ j : Fin (H).length,
        ∃ (selected : ReferenceActivePhysicalStep.Selection H[j.val].input)
          (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          H[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (∀ i, (H[j.val].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied →
            (states i).lastDown = some (payload.downRecord i)) ∧
          (∀ i, (states i).status ≠ .released) ∧
          (∀ i, (states i).status = .unoccupied →
            i ∈ selected.view.pendingAtChoice ∧
            ReferencePrelaunchFollower.acceptedStart (states i) < (payload.downRecord i).val.sigma) ∧
          selected.view.pendingAtChoice.Nonempty ∧
          ReferenceActiveDataOwnership.carriedOccupiedFields payload H[j.val].output.next := by
  classical
  have hs := ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_choice_stages
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hs
  obtain ⟨payload, hbirth, hstages⟩ := hs
  refine ⟨payload, hbirth, ?_⟩
  intro j
  let i0 : Fin (p.m - 1) := ⟨0, by have := p.two_le_m; omega⟩
  obtain ⟨_, _, _, _, _, hchoices0⟩ := hstages i0
  obtain ⟨selected, _choice, _memory, hsel, hpayload, _⟩ := hchoices0 j
  obtain ⟨hk, heq⟩ := handover_index rewards C_star C_h z b j
  have hfields := ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
    (rate := rate) rewards C_star C_h z ⟨_, hk⟩
  rw [← heq] at hfields
  obtain ⟨states, memories, hc, hf, _, hout⟩ := hfields selected hsel
  have hst (i : Fin (p.m - 1)) :
      ((states i).status = .unoccupied ∧ i ∈ selected.view.pendingAtChoice ∧
        ReferencePrelaunchFollower.acceptedStart (states i) < (payload.downRecord i).val.sigma) ∨
      (states i).status = .pending := by
    obtain ⟨before, beforeMemory, _, _, hstrict, hchoices⟩ := hstages i
    obtain ⟨sel, choice, memory, hs, hp, hchoice, hstage⟩ := hchoices j
    have heSel := Option.some.inj (hs.symm.trans hsel)
    subst sel
    have heChoice := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hchoice.symm.trans (hc i))
    obtain ⟨rfl, _⟩ := heChoice
    rcases hstage with ⟨hi, hu, _, hstart⟩ | ⟨_, hstatus, _⟩ | ⟨_, hstatus, _⟩
    · exact Or.inl ⟨hu, hi, hstart ▸ hstrict⟩
    · exact Or.inr hstatus
    · exact Or.inr hstatus
  refine ⟨selected, states, memories, hsel, hpayload, hc, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hpayload] using hf
  · intro i
    rcases hst i with ⟨hu, _⟩ | hp
    · rw [hu]
      decide
    · rw [hp]
      decide
  · intro i hu
    rcases hst i with ⟨_, hi, hstrict⟩ | hp
    · exact ⟨hi, hstrict⟩
    · simp only [hu, reduceCtorEq] at hp
  · have hm : ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice H[j.val] = true :=
      List.mem_takeWhile_imp (List.getElem_mem j.isLt)
    have hsel' : H[j.val].output.preparation.coordinator.selection = some selected := hsel
    rw [ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice, hsel'] at hm
    exact of_decide_eq_true hm
  · simpa only [hpayload] using hout

private theorem handover_pending_adjacent
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H).length) (hj : j.val + 1 < (H).length) :
    ∀ (selected : ReferenceActivePhysicalStep.Selection H[j.val].input)
      (selectedNext : ReferenceActivePhysicalStep.Selection H[j.val + 1].input),
      H[j.val].output.preparation.coordinator.selection = some selected →
      H[j.val + 1].output.preparation.coordinator.selection = some selectedNext →
      selectedNext.view.pendingAtChoice =
        if ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent H[j.val] selected then
          selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (H[j.val].input.row.2 H[j.val].input.time).1)
        else selected.view.pendingAtChoice := by
  rcases j with ⟨nval, hbound⟩
  change nval + 1 < (H).length at hj
  dsimp only [Fin.val_mk] at hj ⊢
  classical
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨rb, qb, beta, birthSelected, hbirthNext, _, _, hbirthSel,
    _, hfull, hrbFull, hnoEvent, _, _, _, hframes⟩ := hh
  have hV : (V).IsPrefix ((R).drop b.val) := by
    rw [List.drop_eq_getElem_cons b.isLt]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hadj (n : ℕ) (hn : n + 1 < (V).length) :
      V[n + 1].input.state = V[n].output.next := by
    have hlen := hV.length_le
    simp only [List.length_drop] at hlen
    rw [hV.getElem hn, hV.getElem (by omega), List.getElem_drop, List.getElem_drop]
    exact ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      rewards C_star C_h z (b.val + n) (by omega)
  have hVlength : (H).length ≤ (V).length := (List.takeWhile_prefix _).length_le
  have hv0 : nval < (V).length := lt_of_lt_of_le hbound hVlength
  have hv1 : nval + 1 < (V).length := lt_of_lt_of_le hj hVlength
  have hcurrent : H[nval] = V[nval]'hv0 := (List.takeWhile_prefix _).getElem hbound
  have hfollowing : H[nval + 1] = V[nval + 1]'hv1 := (List.takeWhile_prefix _).getElem hj
  simp only [List.length_cons] at hVlength hv0 hv1
  rw [hcurrent, hfollowing]
  cases nval with
  | zero =>
      simp only [Nat.zero_add, List.getElem_cons_zero, List.getElem_cons_succ] at hj hbound ⊢
      intro selected selectedNext hs hsNext
      have he := Option.some.inj (hbirthSel.symm.trans hs)
      subst selected
      obtain ⟨r1, q1, sel1, out1, own1, _states1, _memories1, hin1, _, hs1, _, hp1, _⟩ :=
        hframes ⟨0, by omega⟩
      have he := Option.some.inj (hs1.symm.trans hsNext)
      subst sel1
      have hconnect : W[0].input.state = R[b.val].output.next :=
        hadj 0 (by change 1 < (W).length + 1; omega)
      have hr := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
        (hin1.symm.trans ((congrArg (fun st : ReferenceActivePhysicalStep.State p rate =>
          st.coordinator) hconnect).trans hbirthNext))).1
      rw [ite_eq_right hnoEvent, hp1, hr, hrbFull, hfull]
  | succ n =>
      simp only [List.getElem_cons_succ] at hj hbound ⊢
      intro selected selectedNext hs hsNext
      obtain ⟨r0, q0, sel0, out0, own0, _states0, _memories0, _, _, hs0, _, _, hout0, _, hu0, _⟩ :=
        hframes ⟨n, by omega⟩
      obtain ⟨r1, q1, sel1, out1, own1, _states1, _memories1, hin1, _, hs1, _, hp1, _⟩ :=
        hframes ⟨n + 1, by omega⟩
      have he0 := Option.some.inj (hs0.symm.trans hs)
      have he1 := Option.some.inj (hs1.symm.trans hsNext)
      subst sel0
      subst sel1
      have hc : W[n + 1].input.state = W[n].output.next :=
        hadj (n + 1) (by change n + 1 + 1 < (W).length + 1; omega)
      have hr := (ReferenceActivePhysicalStep.CoordinatorConfiguration.live.inj
        (hin1.symm.trans ((congrArg (fun s : ReferenceActivePhysicalStep.State p rate =>
          s.coordinator) hc).trans hout0))).1
      rw [hp1, hr, hu0]

private theorem handover_cutoff
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (j : Fin (H).length) :
    ∀ selected : ReferenceActivePhysicalStep.Selection H[j.val].input,
      H[j.val].output.preparation.coordinator.selection = some selected →
      selected.view.cutoff = none := by
  rcases j with ⟨nval, hbound⟩
  have hh := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hh
  obtain ⟨_, _, beta, _, _, _, _, _, _, _, _, _, _, _, _, hframes⟩ := hh
  have hjV := lt_of_lt_of_le hbound
    (List.takeWhile_prefix ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice).length_le
  have hHj : H[nval] = V[nval] := (List.takeWhile_prefix _).getElem hbound
  have hindex := handover_index rewards C_star C_h z b ⟨nval, hbound⟩
  rw [hHj]
  cases nval with
  | zero =>
      simp only [List.getElem_cons_zero]
      intro selected hs
      exact laterBirth_cutoff _ selected hs hb
  | succ n =>
      have hnW : n < (W).length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hjV
      simp only [List.getElem_cons_succ]
      intro selected hs
      obtain ⟨r, q, sel, next, owned, _states, _memories, hin, _, _, _, _, _⟩ := hframes ⟨n, hnW⟩
      obtain ⟨hk, heq⟩ := hindex
      dsimp only at heq
      have hdomain := ReferenceCompleteLiveChoiceDomains.complete_live_dispatch_choice_exists
        rate rewards C_star C_h z ⟨_, hk⟩ r q beta
      dsimp only at hdomain
      rw [← heq, hHj, List.getElem_cons_succ] at hdomain
      obtain ⟨hd, hbranch⟩ := hdomain hin
      have hp : W[n].output.preparation = ReferenceActivePhysicalStep.prepare W[n].input := by
        rw [(W[n]).output_eq]
        rfl
      have ht : ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest W[n] = true :=
        List.mem_takeWhile_imp (List.getElem_mem hnW)
      unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at ht
      rw [hp, hd] at ht
      cases hchosen : CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput W[n].input r q beta)
        <;> simp only [hchosen, Bool.false_eq_true] at ht
      rename_i dispatched hstart continuation arm
      rw [hchosen] at hbranch
      have hcut := selectionAt_cutoff W[n].input r.payload dispatched.startResult W[n].input.time
        (ReferenceActivePhysicalStep.liveRegistersAt r W[n].input.time).complementWeights arm selected
        (by simpa only [hp, hd, hchosen, ReferenceActivePhysicalStep.DispatchCut.selection] using hs)
      rw [hcut, hbranch.2.1]
      rfl

private theorem handover_birth_snapshot
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload)
    (hk : 0 < (H).length) :
    ∀ (selected : ReferenceActivePhysicalStep.Selection H[0].input)
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      H[0].output.preparation.coordinator.selection = some selected →
      (∀ i, (H[0].output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i)) →
      ActiveObservationBridge.liveSnapshotBefore p payload.assignment
        (actualLaterHandoverLive rate rewards C_star C_h z payload H) H[0].input.time =
          ⟨selected.view.pendingAtChoice, fun i => (states i).status⟩ := by
  have hzero : H[0] = R[b.val] := by
    change (List.takeWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice V)[0] = R[b.val]
    rw [(List.takeWhile_prefix _).getElem hk]
    rfl
  rw [hzero]
  intro selected states memories hs hc
  obtain ⟨_, birthSel, birthStates, birthMemories, _, hs0, _, hfull, hc0, hu0, _⟩ :=
    actual_later_handover_birth_choice_data rate rewards C_star C_h z b hb
  have he := Option.some.inj (hs0.symm.trans hs)
  subst birthSel
  have hu (i : Fin (p.m - 1)) : (states i).status = .unoccupied := by
    have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((hc0 i).symm.trans (hc i))
    exact he.1 ▸ hu0 i
  calc
    _ = ActiveRoundActions.initialSnapshot payload.assignment :=
      actualLaterHandoverLive_prebirth_snapshot rate rewards C_star C_h z payload H
        R[b.val].input.time (by rw [installationBirth_time _ payload hbirth])
    _ = _ := by
      apply congrArg₂ ActiveRoundActions.Snapshot.mk
      · exact hfull.symm
      · funext i
        exact (hu i).symm

/-- Every actual later-handover CHOICE is the strict-past live calendar
snapshot. The states and all branch facts are produced from the original run. -/
public theorem actual_later_handover_snapshot
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true) :
    ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      ∀ j : Fin (H).length,
        ∃ (selected : ReferenceActivePhysicalStep.Selection H[j.val].input)
          (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
          H[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (∀ i, (H[j.val].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          ActiveObservationBridge.liveSnapshotBefore p payload.assignment
            (actualLaterHandoverLive rate rewards C_star C_h z payload H) H[j.val].input.time =
              ⟨selected.view.pendingAtChoice, fun i => (states i).status⟩ ∧
          (∀ i, (states i).status ≠ .unoccupied →
            (states i).lastDown = some (payload.downRecord i)) ∧
          (∀ i, (states i).status ≠ .released) ∧
          (∀ i, (states i).status = .unoccupied → i ∈ selected.view.pendingAtChoice) := by
  obtain ⟨payload, hbirth, hframe⟩ := handover_choice_data rewards C_star C_h z b hb
  have htimes := handover_time rewards C_star C_h z b
  have hlookups := handover_lookup rewards C_star C_h z b
  have hadjacents := handover_adjacent rewards C_star C_h z b
  have hpendings := handover_pending_adjacent rewards C_star C_h z b hb
  have hcutoffs := handover_cutoff rewards C_star C_h z b hb
  choose selected states memories hs hp hc hf hn ho hne hout using hframe
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
  have hbirthTime := installationBirth_time R[b.val] payload hbirth
  have htime (j : Fin (H).length) : H[j.val].input.time.val = payload.sigma.val + j.val := by
    rw [htimes j, ← hbirthTime]
  have hcalendar (j : Fin (H).length) : live H[j.val].input.time =
      ⟨handoverRoundInput payload H[j.val].input.row H[j.val].input.time,
        handoverWholeRewardRow H[j.val],
        ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload H[j.val]⟩ := by
    apply actualLaterHandoverLive_of_actual_record
      rate rewards C_star C_h z payload H H[j.val].input.time
    · constructor <;> rw [htime j] <;> omega
    · exact hlookups j
  have hzeroSnapshot (hk : 0 < (H).length) :
      ActiveObservationBridge.liveSnapshotBefore p payload.assignment live H[0].input.time =
        ⟨(selected ⟨0, hk⟩).view.pendingAtChoice, fun i => (states ⟨0, hk⟩ i).status⟩ :=
    handover_birth_snapshot rewards C_star C_h z b hb payload hbirth hk
      (selected ⟨0, hk⟩) (states ⟨0, hk⟩) (memories ⟨0, hk⟩) (hs ⟨0, hk⟩) (hc ⟨0, hk⟩)
  have hstepSnapshot (j : Fin (H).length) (hk : j.val + 1 < (H).length) :
      ActiveRoundActions.finishLiveRound p.two_le_m
        ⟨(selected j).view.pendingAtChoice, fun i => (states j i).status⟩
        (live H[j.val].input.time).input (live H[j.val].input.time).rewards
        (live H[j.val].input.time).acceptCurrent =
          ⟨(selected ⟨j.val + 1, hk⟩).view.pendingAtChoice,
            fun i => (states ⟨j.val + 1, hk⟩ i).status⟩ := by
    let k : Fin (H).length := ⟨j.val + 1, hk⟩
    rw [hcalendar j]
    have hlive : CoordinatorLocalArmChoice.assignmentIsLive (selected j).view.payload
        (selected j).view.cutoff H[j.val].input.time := by
      rw [hp j, hcutoffs j (selected j) (hs j)]
      constructor
      · change payload.sigma.val + 1 ≤ H[j.val].input.time.val + 1
        rw [htime j]
        omega
      · change H[j.val].input.time.val + 1 < p.T + 1
        have := H[j.val].input.time.isLt
        omega
    have hstep := handover_choice_step H[j.val] H[k.val] (selected j) (hs j)
      (selected k).view.pendingAtChoice (states j) (states k) (memories j) (memories k)
      (hc j) (hc k)
      (by simpa only [hp j] using (fun i hu => (ho j i hu).2))
      (by simpa only [hp j] using (fun i hu => (ho k i hu).2))
      (by simpa only [hp j] using hf j) (by simpa only [hp j] using hout j)
      (hn j) (hn k) (hne j) hlive (hadjacents j hk)
      (hpendings j hk
        (selected j) (selected k) (hs j) (hs k))
    rw [hp j] at hstep
    exact hstep
  have hsn := calendar_snapshot_induction live
    (fun j : Fin (H).length => H[j.val].input.time)
    (fun j => (⟨(selected j).view.pendingAtChoice, fun i => (states j i).status⟩ :
      ActiveRoundActions.Snapshot payload.assignment)) hzeroSnapshot
    (fun j hk => by rw [htime, htime]; simp only [Nat.add_assoc]) hstepSnapshot
  refine ⟨payload, hbirth, ?_⟩
  intro j
  exact ⟨selected j, states j, memories j, hs j, hp j, hc j,
    hsn j, hf j, hn j, fun i hu => (ho j i hu).1⟩

/-- The same live snapshot and inherited bank give the whole current decoder
call and its compared raw diagnostic. The two endpoint flags in `fromLive` are
unused by observationTrace; no stopped-local-state identification is asserted. -/
public theorem actual_later_handover_decoder_correspondence
    (hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true)
    (i : Fin (p.m - 1)) :
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (before : ReferencePrelaunchFollower.State p rate.eta)
      (beforeMemory : ActiveFollowerLifecycle.LocalMemory p),
      ReferenceAssignmentPayloadPersistence.InstallationBirth R[b.val] payload ∧
      R[b.val].input.state.followers i = .ordinary before beforeMemory ∧
      before.status = .unoccupied ∧
      ReferencePrelaunchFollower.acceptedStart before < (payload.downRecord i).val.sigma ∧
      let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
      let trace := HandoverStoppedDecoderReplay.observationTrace p payload.assignment
        (HandoverStoppedDecoderReplay.fromLive p payload.assignment live (fun _ => false) (fun _ => false)) i
      ∀ j : Fin (H).length,
        ∃ (selected : ReferenceActivePhysicalStep.Selection H[j.val].input)
          (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
          (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
          (inputState : ReferencePrelaunchFollower.State p rate.eta)
          (inputMemory : ActiveFollowerLifecycle.LocalMemory p),
          H[j.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.payload = payload ∧
          (∀ k, (H[j.val].output.preparation.followers.followers k).configuration =
            .ordinary (states k) (memories k)) ∧
          H[j.val].input.state.followers i = .ordinary inputState inputMemory ∧
          inputState.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
            ((H).take j.val) before.downBatch ∧
          (states i).downBatch = inputState.downBatch ∧
          ActiveObservationBridge.liveSnapshotBefore p payload.assignment live H[j.val].input.time =
            ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩ ∧
          ((states i).status ≠ .unoccupied →
            (H[j.val].output.followers i).downInput = none ∧ (H[j.val].output.followers i).down = none) ∧
          (¬ ActiveFollowerDownAcceptance.downSelected p i H[j.val].input.row H[j.val].input.time →
            ∀ cut, (H[j.val].output.followers i).down = some cut →
              ∃ logged, (H[j.val].output.followers i).downInput = some logged ∧
                cut.outcome = .skipped logged .notSelectedDown ∧ cut.raw = none ∧
                cut.rawComparison = none) ∧
          (ActiveFollowerDownAcceptance.downSelected p i H[j.val].input.row H[j.val].input.time →
            (states i).status = .unoccupied →
            trace H[j.val].input.time = ActiveFollowerDownAcceptance.currentRoundInput p i
              H[j.val].input.row H[j.val].input.time
              (H[j.val].output.preparation.feedback.observations
                (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate (states i) ∧
            AffineBatchDecoder.decodeStep p trace
              (ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H).take j.val) before.downBatch)
              H[j.val].input.time = ActiveFollowerDownAcceptance.currentDecodeStep p i
                H[j.val].input.row H[j.val].input.time
                (H[j.val].output.preparation.feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate (states i)) ∧
          (∀ cut, (H[j.val].output.followers i).down = some cut →
            cut.rawComparison = none ∨ ∃ logged,
              (H[j.val].output.followers i).downInput = some logged ∧
              logged.downBatch = ReferenceFollowerDownDecoderReplay.replayDownCalls i
                ((H).take j.val) before.downBatch ∧
              AffineBatchDecoder.decodeStep p trace
                (ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H).take j.val) before.downBatch)
                H[j.val].input.time =
                ActiveFollowerDownAcceptance.currentDecodeStep p i H[j.val].input.row H[j.val].input.time
                  (H[j.val].output.preparation.feedback.observations
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
              cut.raw = (AffineBatchDecoder.decodeStep p trace
                (ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H).take j.val) before.downBatch)
                H[j.val].input.time).2) := by
  obtain ⟨payload, hbirth, hsnapshots⟩ := actual_later_handover_snapshot rewards C_star C_h z b hb
  have hstages := ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_choice_stages
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hstages
  obtain ⟨birthPayload, hbirth', hstages⟩ := hstages
  have hpayload := installationBirth_unique R[b.val] birthPayload payload hbirth' hbirth
  subst birthPayload
  obtain ⟨before, beforeMemory, hbefore, huBefore, hstrict, _⟩ := hstages i
  have hbanks := ReferencePostReplacementCollectionHandoverReplay.actual_later_installation_handover_bank_replay
    rate rewards C_star C_h z b
  rw [ite_eq_left hb] at hbanks
  refine ⟨payload, before, beforeMemory, hbirth, hbefore, huBefore, hstrict, ?_⟩
  dsimp only
  let live := actualLaterHandoverLive rate rewards C_star C_h z payload H
  let trace := HandoverStoppedDecoderReplay.observationTrace p payload.assignment
    (HandoverStoppedDecoderReplay.fromLive p payload.assignment live (fun _ => false) (fun _ => false)) i
  intro j
  obtain ⟨selected, states, memories, hs, hp, hc, hsnapshot, hf, hno, hmissing⟩ := hsnapshots j
  let r := H[j.val]
  let prep := r.output.preparation.followers.followers i
  let observation := r.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hprepare := hc i
  rw [r.output.preparation.followers.followers_eq i] at hprepare
  obtain ⟨inputState, inputMemory, hin, hstart, _, _⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i r.input.row
      (r.input.state.activations i) r.input.time (r.input.active i)
      (r.input.state.followers i) (states i) (memories i) hprepare
  obtain ⟨_, _, _, _, hchoiceBank, _, _, _⟩ := ActiveFollowerLifecycle.startRound_frame
    rate.eta r.input.time inputState (states i) inputMemory (memories i) hstart
  have hbank := hbanks i before beforeMemory hbefore j inputState inputMemory hin
  have htime := handover_time rewards C_star C_h z b j
  have hbirthTime := installationBirth_time R[b.val] payload hbirth
  have hcalendar := actualLaterHandoverLive_of_actual_record rate rewards C_star C_h z payload H
    r.input.time (by dsimp only [r]; rw [htime, ← hbirthTime]; constructor <;> omega)
    r (handover_lookup rewards C_star C_h z b j)
  have hinput (hd : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time)
      (hu : (states i).status = .unoccupied) :
      trace r.input.time = ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row
        r.input.time observation rate (states i) := by
    have h := actual_handover_decoder_input r selected hs states memories hc
      (by simpa only [hp] using hf) hno i (hmissing i hu) hd.1 hd.2 hu false false
    rw [hp] at h
    have hsnapshot' : ActiveObservationBridge.liveSnapshotBefore p payload.assignment live r.input.time =
        ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩ := hsnapshot
    have hcalendar' : live r.input.time =
        ⟨handoverRoundInput payload r.input.row r.input.time, handoverWholeRewardRow r,
          ReferenceFirstLiveHandoverSnapshotPrefix.installationFlag payload r⟩ := hcalendar
    have hdata : HandoverStoppedDecoderReplay.fromLive p payload.assignment live
        (fun _ => false) (fun _ => false) r.input.time =
        handoverRoundData payload r ⟨selected.view.pendingAtChoice, fun k => (states k).status⟩
          false false r.input.time := by
      unfold HandoverStoppedDecoderReplay.fromLive handoverRoundData
      rw [hsnapshot', hcalendar']
      rfl
    change HandoverStoppedDecoderReplay.observationTrace p payload.assignment
      (HandoverStoppedDecoderReplay.fromLive p payload.assignment live
        (fun _ => false) (fun _ => false)) i r.input.time = _
    unfold HandoverStoppedDecoderReplay.observationTrace
    rw [hdata]
    exact h
  have hdiagnostic (cut : ReferenceDownReception.ReferenceDownCutOutput p rate)
      (hd : (r.output.followers i).down = some cut) :
      ∃ logged, (states i).status = .unoccupied ∧ (r.output.followers i).downInput = some logged ∧
        logged.status = (states i).status ∧ logged.downBatch = (states i).downBatch ∧
        cut = ReferenceDownReception.referenceDownCut p r.output.preparation.coordinator.downView
          i r.input.row r.input.time observation rate logged := by
    obtain ⟨choice, memory, logged, hc', hu, hl, hi, hcut⟩ :=
      ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice r i cut hd
    obtain ⟨he, hm⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      (hc'.symm.trans (hc i))
    subst choice
    obtain ⟨_, _, _, _, hstatus, hbatch, _⟩ := ActiveFollowerLogging.checkedLogging_success_frame
      prep.follower prep.row prep.activation prep.time (prep.arm, observation) (states i) logged hl
    have ha := r.output.preparation.follower_alignment i
    exact ⟨logged, hu, hi, hstatus, hbatch, by simpa only [ha.1, ha.2.1, ha.2.2.1] using hcut⟩
  refine ⟨selected, states, memories, inputState, inputMemory, hs, hp, hc, hin, hbank,
    hchoiceBank, hsnapshot, ?_, ?_, ?_, ?_⟩
  · intro ho
    rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r]
    have hd := ReferenceFollowerSparseEmissionRecovery.finishFollower_diagnostics
      r.output.preparation.coordinator.downView prep observation (states i) (memories i) (hc i)
    rw [hd.1, hd.2]
    simp only [ReferenceActivePhysicalStep.recordFollower, ho, ↓reduceDIte]
    exact ⟨trivial, trivial⟩
  · intro hn cut hd
    change ¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time at hn
    obtain ⟨logged, _, hdownInput, _, _, hcut⟩ := hdiagnostic cut hd
    refine ⟨logged, hdownInput, ?_, ?_, ?_⟩
    all_goals rw [hcut, ReferenceDownReception.referenceDownCut, dite_eq_right hn]
  · intro hd hu
    refine ⟨hinput hd hu, ?_⟩
    unfold ActiveFollowerDownAcceptance.currentDecodeStep
    rw [hchoiceBank, hbank]
    exact ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p trace _ _ r.input.time (hinput hd hu)
  · intro cut hd
    by_cases hn : cut.rawComparison = none
    · exact Or.inl hn
    right
    obtain ⟨logged, hu, hi, hstatus, hbatch, hcut⟩ := hdiagnostic cut hd
    have hdown : ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time := by
      by_contra hnot
      simp only [hcut, ReferenceDownReception.referenceDownCut, hnot, ↓reduceDIte] at hn
      exact hn trivial
    have hcurrent : trace r.input.time = ActiveFollowerDownAcceptance.currentRoundInput p i
        r.input.row r.input.time observation rate logged := by
      simpa only [ActiveFollowerDownAcceptance.currentRoundInput, hstatus] using hinput hdown hu
    have hloggedBank : logged.downBatch =
        ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H).take j.val) before.downBatch :=
      hbatch.trans (hchoiceBank.trans hbank)
    have hdecode := ActiveFollowerDownAcceptance.decodeStep_depends_on_current_input p trace
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i r.input.row r.input.time observation rate logged))
      (ReferenceFollowerDownDecoderReplay.replayDownCalls i ((H).take j.val) before.downBatch)
      r.input.time hcurrent
    rw [← hloggedBank] at hdecode
    have hraw := ReferenceDownReception.referenceDownCut_raw_eq_currentDecodeStep_of_compared
      r.output.preparation.coordinator.downView i r.input.row r.input.time observation rate logged
      (by rw [← hcut]; exact hn)
    change AffineBatchDecoder.decodeStep p trace logged.downBatch r.input.time =
      ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row r.input.time observation rate logged at hdecode
    rw [hloggedBank] at hdecode
    refine ⟨logged, hi, hloggedBank, hdecode, ?_⟩
    exact (congrArg ReferenceDownReception.ReferenceDownCutOutput.raw hcut).trans
      (hraw.trans (congrArg Prod.snd hdecode).symm)

end ActualCalendar

end Bandits.Support.ReferencePostReplacementCollectionHandoverDecoderCorrespondence

end
