/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveAllFollowerOccupancy
public import Bandits.Support.ReferenceActiveDataOwnership
public import Bandits.Support.ReleaseRoundKernel

import Mathlib.Data.List.TakeWhile

/-!
# First-live release geometry

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,128-175,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:246-260,270-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module keeps the original fixed-boundary physical execution and its
whole-record DOWN fields. Its occupancy projection is derived only from the
integrated all-follower result. It introduces no new execution or feedback
model.

The original-source export jointly retains the all-player action and feedback
identities and the exact physical UP/DATA flags. The next consumer is the
first-live release slice/sampler coupling with `ReleaseRoundKernel`'s existing
UP/DATA probability exports. No current-control conditional law, mass formula,
service/quota, queue/score truth, cost, or manuscript closure is proved here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveReleaseGeometry

open ConstructorDimensions
open ReferenceActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)

/-- Convert the accepted ActiveRoundActions follower carrier to the literal
`Fin (m - 1)` carrier of the physical follower arrays. -/
def followerToFin (i : ActiveRoundActions.Follower p.m) : Fin (p.m - 1) :=
  ⟨i.val, by
    simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using i.isLt⟩

/-- Extend the actual live complement weights to all arms by the source anchor
on the payload's assigned image. -/
def completeCurrentWeights {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x) : Fin p.K → ℝ :=
  fun a => if ha : a ∈ selected.view.payload.slowSet.val then
    selected.view.payload.anchor a
  else selected.view.complementWeights
    ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩

/-- The whole selected reward row, at its original denominator `D`. -/
def wholeGridRewardRow (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) : ActiveRoundActions.RewardRow p.K :=
  ⟨fun a => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a),
    fun a => RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p)
      (rewards t a)⟩

/-- The literal common-action snapshot of the actual choices. -/
def actualChoiceSnapshot {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) :
    ActiveRoundActions.Snapshot selected.view.payload.assignment :=
  ⟨selected.view.pendingAtChoice, fun i => (states i).status⟩

private theorem downAuxiliaryArm_eq_assignment
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) :
    ActiveFollowerArmChoice.downAuxiliaryArm rate.eta (payload.downRecord i) =
      payload.assignment.auxiliary := by
  apply Fin.ext
  have haux := ActiveFollowerArmChoice.down_auxiliary_arm_one_based rate.eta
    (payload.downRecord i)
  have hfield : (payload.downRecord i).val.e =
      (payload.assignment.auxiliary).val + 1 := by
    rw [payload.downRecord_fields i]
  omega

/-- An occupied actual local choice agrees with the common follower action on
the same physical controls. The proof follows the pending UP sentinel, DATA,
DOWN collision-escape, and assigned-arm branches directly; its two DOWN arms
are the fields of this selected payload. -/
private theorem occupied_choice_eq_projected_action
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0)
    (i : Fin (p.m - 1))
    (offered : Option (OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)))
    (hstatus : state.status = snapshot.status i)
    (hoccupied : state.status ≠ .unoccupied)
    (hrecord : state.lastDown = some (selected.view.payload.downRecord i))
    (hslot : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = input.slot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = input.selected)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = input.tuple) :
    ActiveFollowerArmChoice.followerArmChoiceCore state (x.row.2 x.time) i offered =
      some (ActiveRoundActions.followerAction p.two_le_m snapshot input i) := by
  cases hs : state.status with
  | unoccupied => exact (hoccupied hs).elim
  | released =>
      have hsnap : snapshot.status i = .released := hstatus.symm.trans hs
      rw [ActiveFollowerArmChoice.followerArmChoiceCore.eq_def, hs, hrecord]
      have harm := ReferenceActiveDataOwnership.downRecord_arm selected.view.payload i
      simp [ActiveRoundActions.followerAction, hsnap, harm]
  | pending =>
      have hsnap : snapshot.status i = .pending := hstatus.symm.trans hs
      have harm := ReferenceActiveDataOwnership.downRecord_arm selected.view.payload i
      have haux := downAuxiliaryArm_eq_assignment selected.view.payload i
      rw [ActiveFollowerArmChoice.followerArmChoiceCore.eq_def, hs, hrecord]
      simp only [hsnap, hslot, hselected, htuple, harm, haux,
        ActiveRoundActions.followerAction]
      split_ifs <;> simp_all

/-- The actual simultaneous action profile equals the common-action profile
on a projected width-zero round input. The only state and DOWN-record fields
are those extracted for this same record from the integrated occupancy root. -/
theorem prepared_actions_eq_projected
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied ∧
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0)
    (hmissing : (actualChoiceSnapshot selected states).missing = ∅)
    (hslot : PublicDiscreteDraws.slotDraw (x.row.2 x.time).1 = input.slot)
    (hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = input.selected)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (x.row.2 x.time).1 = input.tuple)
    (hfast : input.fast = selected.arm) :
    (ReferenceActivePhysicalStep.prepare x).arms.actions =
      ActiveRoundActions.actions p.two_le_m (actualChoiceSnapshot selected states) input := by
  classical
  funext player
  rcases ActiveRoundActions.player_cases p.two_le_m player with hcoord | ⟨i, hplayer⟩
  · subst player
    have hactual :
        (ReferenceActivePhysicalStep.prepare x).arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) = selected.arm := by
      rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
      simp [ReferenceActivePhysicalStep.DispatchCut.arm, hselection]
    calc
      (ReferenceActivePhysicalStep.prepare x).arms.actions
          (ActiveRoundActions.coordinator p.two_le_m) = selected.arm := hactual
      _ = input.fast := hfast.symm
      _ = ActiveRoundActions.actions p.two_le_m
          (actualChoiceSnapshot selected states) input
          (ActiveRoundActions.coordinator p.two_le_m) := by
            rw [ActiveRoundActions.actions_coordinator,
              ActiveRoundActions.coordinatorAction_fast p.two_le_m
                (actualChoiceSnapshot selected states) input hmissing]
  · subst player
    have hi := hfields i
    obtain ⟨_, _, offered, _, _, hchoice⟩ :=
      ReferenceActiveDataOwnership.prepare_ordinary_choice i x.row
        (x.state.activations i) x.time (x.active i) (x.state.followers i)
        (states i) (memories i) (hordinary i)
    have hcore := occupied_choice_eq_projected_action selected (states i)
      (actualChoiceSnapshot selected states) input i offered rfl hi.1 hi.2
      hslot hselected htuple
    have hcore' : ActiveFollowerArmChoice.followerArmChoice
        (states i) x.row x.time i offered =
          some (ActiveRoundActions.followerAction p.two_le_m
            (actualChoiceSnapshot selected states) input i) := by
      simpa only [ActiveFollowerArmChoice.followerArmChoice] using hcore
    have hpreparedArm :
        (DeclaredFollowerLocalRound.prepare rate i x.row (x.state.activations i)
          x.time (x.active i) (x.state.followers i)).arm =
          ActiveRoundActions.followerAction p.two_le_m
            (actualChoiceSnapshot selected states) input i :=
      Option.some.inj (hchoice.symm.trans hcore')
    have harm :
        (ReferenceActivePhysicalStep.prepare x).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        ActiveRoundActions.followerAction p.two_le_m
          (actualChoiceSnapshot selected states) input i :=
      (ReferenceActivePhysicalStep.PreparedRound.action_follower
        (ReferenceActivePhysicalStep.prepare x) i).trans hpreparedArm
    calc
      (ReferenceActivePhysicalStep.prepare x).arms.actions
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
        ActiveRoundActions.followerAction p.two_le_m
          (actualChoiceSnapshot selected states) input i := harm
      _ = ActiveRoundActions.actions p.two_le_m
          (actualChoiceSnapshot selected states) input
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
            rw [ActiveRoundActions.actions_follower]

/-- The typed observation produced by the physical feedback cut has the
projected row's finite-bandit scalar value on the same all-player profile. -/
theorem prepared_observation_eq_projected
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0)
    (player : Fin p.m)
    (hactions : (ReferenceActivePhysicalStep.prepare x).arms.actions =
      ActiveRoundActions.actions p.two_le_m snapshot input) :
    ((ReferenceActivePhysicalStep.prepare x).feedback.observations player).val.val =
      ActiveRoundActions.feedback p.two_le_m snapshot input
        (wholeGridRewardRow x.rewards x.time) player := by
  have hscalar := ReferenceActiveFeedbackCut.FeedbackCut.feedback_scalar_eq_playerFeedback
    (ReferenceActivePhysicalStep.prepare x).feedback player
  have hrow : (fun a : Fin p.K =>
      ((x.rewards x.time a).val : ℝ) / (D p : ℝ)) =
      (wholeGridRewardRow x.rewards x.time).val := by
    funext a
    rfl
  calc
    ((ReferenceActivePhysicalStep.prepare x).feedback.observations player).val.val =
        ((ReferenceActivePhysicalStep.prepare x).feedback.feedback player).val / (D p : ℝ) :=
      ReferenceActiveFeedbackCut.FeedbackCut.observation_grid_value
        (ReferenceActivePhysicalStep.prepare x).feedback player
    _ = FiniteBanditModel.playerFeedback
        (ReferenceActivePhysicalStep.prepare x).arms.actions
        (fun a => ((x.rewards x.time a).val : ℝ) / (D p : ℝ)) player := hscalar
    _ = ActiveRoundActions.feedback p.two_le_m snapshot input
        (wholeGridRewardRow x.rewards x.time) player := by
      rw [hactions, hrow]
      rfl

/-- The physical local release test is the common action kernel's release
observation on the same complete row and actual typed own observation. -/
theorem prepared_releaseCondition_eq_projected
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0)
    (i : Fin (p.m - 1))
    (hactions : (ReferenceActivePhysicalStep.prepare x).arms.actions =
      ActiveRoundActions.actions p.two_le_m snapshot input)
    (hslot : input.slot = PublicDiscreteDraws.slotDraw (x.row.2 x.time).1)
    (hselected : input.selected = PublicDiscreteDraws.selectedFollowerDraw
      p.two_le_m p.m_lt_K (x.row.2 x.time).1)
    (htuple : input.tuple = OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (x.row.2 x.time).1)
    (hpilots : input.pilots = fun q => PublicDiscreteDraws.pilotDraw
      (K_pos p) q (x.row.2 x.time).1) :
    ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) =
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input
        (wholeGridRewardRow x.rewards x.time) i := by
  have hassigned : selected.view.payload.assignment.assigned i =
      PrelaunchBufferRecovery.downArm rate.eta (selected.view.payload.downRecord i) :=
    (ReferenceActiveDataOwnership.downRecord_arm selected.view.payload i).symm
  have hauxiliary : selected.view.payload.assignment.auxiliary =
      ActiveFollowerLifecycle.acceptedEscapeArm (selected.view.payload.downRecord i) := by
    apply Fin.ext
    let follower : ActiveRoundActions.Follower p.m := i
    have he : (selected.view.payload.downRecord follower).val.e =
        (selected.view.payload.assignment.auxiliary).val + 1 := by
      have hh := congrArg (fun d : OrdinaryMessageCodec.DownFields => d.e)
        (selected.view.payload.downRecord_fields follower)
      exact hh
    have hescape := ActiveFollowerLifecycle.accepted_escape_arm_one_based
      (selected.view.payload.downRecord follower)
    change (selected.view.payload.assignment.auxiliary).val =
      (ActiveFollowerLifecycle.acceptedEscapeArm
        (selected.view.payload.downRecord follower)).val
    have hsum :
        (ActiveFollowerLifecycle.acceptedEscapeArm
          (selected.view.payload.downRecord follower)).val + 1 =
          (selected.view.payload.assignment.auxiliary).val + 1 :=
      hescape.trans he
    omega
  have hrow : ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time =
      ActiveFollowerLifecycle.publicRowOfActionInput input := by
    cases input with
    | mk slot selectedFollower tuple pilots down up fast hfast =>
        simp only [ActiveFollowerLifecycle.publicRowOfCompleteRow,
          ActiveFollowerLifecycle.publicRowOfActionInput]
        simp_all
  have hfeedback := prepared_observation_eq_projected selected snapshot input
    (PublicDiscreteDraws.followerPlayer p.two_le_m i) hactions
  rw [hrow]
  exact ActiveFollowerLifecycle.releaseCondition_eq_activeRoundActions rate.eta
    selected.view.payload.assignment snapshot input
    (wholeGridRewardRow x.rewards x.time) i
    (selected.view.payload.downRecord i)
    ((ReferenceActivePhysicalStep.prepare x).feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    hassigned hauxiliary hfeedback

/-- Extending the actual complement weights by the payload anchor on the
assigned image preserves positivity and the source factor-two envelope. -/
theorem completeCurrentWeights_bounds
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (a : Fin p.K) :
    0 < completeCurrentWeights selected a ∧
      selected.view.payload.anchor a ≤ completeCurrentWeights selected a ∧
      completeCurrentWeights selected a ≤ 2 * selected.view.payload.anchor a := by
  by_cases ha : a ∈ selected.view.payload.slowSet.val
  · have hweight : completeCurrentWeights selected a = selected.view.payload.anchor a := by
      unfold completeCurrentWeights
      rw [dite_eq_left ha]
    rw [hweight]
    exact ⟨selected.view.payload.anchor_pos a, le_rfl,
      by nlinarith [selected.view.payload.anchor_pos a]⟩
  · let j : CanonicalFastSampling.FastArm selected.view.payload.slowSet :=
      ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
    have hweight : completeCurrentWeights selected a = selected.view.complementWeights j := by
      unfold completeCurrentWeights
      rw [dite_eq_right ha]
    rw [hweight]
    exact ⟨hvalid.current_weight_pos j, hvalid.anchor_le_current j,
      hvalid.current_le_twice_anchor j⟩

/-- The existing kernel input formed from this record's literal continuous
control slice, the actual complement weights, and the payload anchor on the
assigned image. The width-zero hash fields are precisely the kernel's inert
coordinates. -/
def actualReleaseKernelInput
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights) :
    ActiveRoundActions.RoundInput selected.view.payload.assignment 0 :=
  ReleaseRoundKernel.releaseRoundInput p selected.view.payload.assignment
    selected.view.payload.slowSet selected.view.payload.assignment_image.symm
    rate.eta rate.eta.property selected.view.payload.eta_le_source_cap
    selected.view.payload.anchor (completeCurrentWeights selected)
    selected.view.payload.anchor_pos
    (fun a => (completeCurrentWeights_bounds selected hvalid a).1)
    (fun a => (completeCurrentWeights_bounds selected hvalid a).2.1)
    (fun a => (completeCurrentWeights_bounds selected hvalid a).2.2)
    ((x.row.2 x.time).1)

theorem actual_releaseRoundInput_fast_eq_selected
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff x.time)
    (hempty : selected.view.pendingAtChoice = ∅)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights) :
    let input := ReleaseRoundKernel.releaseRoundInput p
      selected.view.payload.assignment selected.view.payload.slowSet
      selected.view.payload.assignment_image.symm rate.eta rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor
      (completeCurrentWeights selected) selected.view.payload.anchor_pos
      (fun a => (completeCurrentWeights_bounds selected hvalid a).1)
      (fun a => (completeCurrentWeights_bounds selected hvalid a).2.1)
      (fun a => (completeCurrentWeights_bounds selected hvalid a).2.2)
      ((x.row.2 x.time).1)
    input.fast = selected.arm ∧ selected.arm ∉ selected.view.payload.slowSet.val := by
  let weights := completeCurrentWeights selected
  have hbounds (a : Fin p.K) := completeCurrentWeights_bounds selected hvalid a
  have hrestrict : selected.view.complementWeights =
      fun j : CanonicalFastSampling.FastArm selected.view.payload.slowSet => weights j.1 := by
    funext j
    have hj := (Finset.mem_sdiff.mp j.property).2
    change selected.view.complementWeights j =
      completeCurrentWeights selected j.1
    unfold completeCurrentWeights
    rw [dite_eq_right hj]
  have hdraw := CoordinatorLocalArmChoice.localFastDraw_eq_canonical
    selected.view.payload selected.view.cutoff x.time selected.view.complementWeights
    hvalid weights (fun a => (hbounds a).1) (fun a => (hbounds a).2.1)
    (fun a => (hbounds a).2.2) hrestrict (x.row.2 x.time)
  have hchoice := selected.choice_eq
  rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core] at hchoice
  have hlocal := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty
    selected.view.payload selected.view.pendingAtChoice selected.view.cutoff x.time
    selected.view.complementWeights (x.row.2 x.time) hvalid hlive hempty
  rw [hlocal] at hchoice
  have harm : selected.arm =
      (CoordinatorLocalArmChoice.localFastDraw selected.view.payload
        selected.view.cutoff x.time selected.view.complementWeights hvalid
        (x.row.2 x.time)).1 := (Option.some.inj hchoice).symm
  dsimp only
  constructor
  · change (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
      selected.view.payload.eta_le_source_cap selected.view.payload.anchor weights
      selected.view.payload.anchor_pos (fun a => (hbounds a).1)
      (fun a => (hbounds a).2.1) (fun a => (hbounds a).2.2)
      selected.view.payload.slowSet
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
        ((x.row.2 x.time).1))).1 = selected.arm
    rw [harm, hdraw]
  · have hnotImage : selected.arm ∉
        Finset.univ.image selected.view.payload.assignment.assigned := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
      have hfast := (ReleaseRoundKernel.releaseRoundInput p
        selected.view.payload.assignment selected.view.payload.slowSet
        selected.view.payload.assignment_image.symm rate.eta rate.eta.property
        selected.view.payload.eta_le_source_cap selected.view.payload.anchor weights
        selected.view.payload.anchor_pos (fun a => (hbounds a).1)
        (fun a => (hbounds a).2.1) (fun a => (hbounds a).2.2)
        ((x.row.2 x.time).1)).fast_outside j
      have hfastEq : (ReleaseRoundKernel.releaseRoundInput p
          selected.view.payload.assignment selected.view.payload.slowSet
          selected.view.payload.assignment_image.symm rate.eta rate.eta.property
          selected.view.payload.eta_le_source_cap selected.view.payload.anchor weights
          selected.view.payload.anchor_pos (fun a => (hbounds a).1)
          (fun a => (hbounds a).2.1) (fun a => (hbounds a).2.2)
          ((x.row.2 x.time).1)).fast = selected.arm := by
        change (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
          selected.view.payload.eta_le_source_cap selected.view.payload.anchor weights
          selected.view.payload.anchor_pos (fun a => (hbounds a).1)
          (fun a => (hbounds a).2.1) (fun a => (hbounds a).2.2)
          selected.view.payload.slowSet
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
            ((x.row.2 x.time).1))).1 = selected.arm
        rw [harm, hdraw]
      exact hfast (hfastEq.trans hj.symm)
    simpa [selected.view.payload.assignment_image] using hnotImage

private def liveContinuationResultPair
    {input : CoordinatorRoundDispatch.LiveInput p}
    (outcome : CoordinatorRoundDispatch.LiveOutcome input) :
    Option (CoordinatorPhaseClock.StartRoundResult p ×
      CoordinatorPhaseClock.StartRoundResult p) :=
  match outcome with
  | .continuingChosen dispatched _ continuation _ =>
      some (dispatched.startResult, continuation.startRoundResult)
  | _ => none

private theorem live_dispatch_continuation_result
    {input : CoordinatorRoundDispatch.LiveInput p}
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      input.registers input.ownedRegisters input.followerBaseScore)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation
      input.registers input.row)
    (selection : CoordinatorRoundDispatch.ArmSelection input.registers.payload
      dispatched.startResult input.registers.time input.registers.complementWeights input.row)
    (hstart : CoordinatorPhaseClock.startRound p input.eta.val input.registers.time
      input.registers.priorClock input.registers.clockPending = .ok dispatched.startResult)
    (hactual : CoordinatorRoundDispatch.dispatchLive input =
      .continuingChosen dispatched hstart continuation selection) :
    continuation.startRoundResult = dispatched.startResult := by
  unfold CoordinatorRoundDispatch.dispatchLive at hactual
  dsimp only at hactual
  repeat' (first | split at hactual <;> try cases hactual)
  case h_3 =>
    rename_i actualDispatched hdispatch hinitialization
    by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
        input.registers actualDispatched.startResult
    · simp only [dite_eq_left hframe] at hactual
      by_cases hpayload : input.registers.priorClock.sigma =
          some input.registers.payload.sigma
      · simp only [dite_eq_left hpayload] at hactual
        by_cases hgrid : input.registers.gridBoundary = input.registers.priorClock.g
        · simp only [dite_eq_left hgrid] at hactual
          by_cases hscore : input.registers.scoreDomainValid
          · simp only [dite_eq_left hscore] at hactual
            by_cases hqueue : input.ownedRegisters.queueDomainValid
            · simp only [dite_eq_left hqueue] at hactual
              by_cases hprevious : input.ownedRegisters.previousServiceDomainValid
              · simp only [dite_eq_left hprevious] at hactual
                by_cases hbase : ∀ i, input.followerBaseScore i ≤ p.T * D p
                · simp only [dite_eq_left hbase] at hactual
                  by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                      input.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        actualDispatched.startResult.clock.u) input.registers.time
                  · simp only [dite_eq_left hlive] at hactual
                    by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                        input.registers.payload
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                          actualDispatched.startResult.clock.u)
                        input.registers.time input.registers.complementWeights
                    · simp only [dite_eq_left hchoice] at hactual
                      by_cases hboundary : actualDispatched.startResult.clock.g ≤ p.T + 1
                      · simp only [dite_eq_left hboundary] at hactual
                        by_cases henvelope : input.registers.complementEnvelopeValid
                        · simp only [dite_eq_left henvelope] at hactual
                          have hnonempty :=
                            CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                              input.registers.payload actualDispatched.startResult.pending
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                actualDispatched.startResult.clock.u)
                              input.registers.time input.registers.complementWeights input.row
                              hchoice
                          split at hactual
                          · rename_i hselected
                            exact False.elim (hnonempty hselected)
                          · have hp := congrArg liveContinuationResultPair hactual
                            have hp' := by
                              simpa only [liveContinuationResultPair] using hp
                            have hpair := Option.some.inj hp'
                            have hfirst := congrArg Prod.fst hpair
                            have hsecond := congrArg Prod.snd hpair
                            exact hsecond.symm.trans hfirst
                        · simp only [dite_eq_right henvelope] at hactual
                          cases hactual
                      · simp only [dite_eq_right hboundary] at hactual
                        cases hactual
                    · simp only [dite_eq_right hchoice] at hactual
                      cases hactual
                  · simp only [dite_eq_right hlive] at hactual
                    cases hactual
                · simp only [dite_eq_right hbase] at hactual
                  cases hactual
              · simp only [dite_eq_right hprevious] at hactual
                cases hactual
            · simp only [dite_eq_right hqueue] at hactual
              cases hactual
          · simp only [dite_eq_right hscore] at hactual
            cases hactual
        · simp only [dite_eq_right hgrid] at hactual
          cases hactual
      · simp only [dite_eq_right hpayload] at hactual
        cases hactual
    · simp only [dite_eq_right hframe] at hactual
      cases hactual
  case h_1 =>
    rename_i actualDispatched hdispatch ledger hinitialization hchoice hboundary
      henvelope hselected
    have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
      input.registers.payload actualDispatched.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        actualDispatched.startResult.clock.u)
      input.registers.time input.registers.complementWeights input.row hchoice
    exact False.elim (hnonempty hselected)

private theorem selected_live_choice_data_of_clock
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : x.state.coordinator = .live r q base)
    (hpriorU : r.priorClock.u = none)
    (hnoCut : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some selected)
    (hempty : selected.view.pendingAtChoice = ∅) :
    CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff x.time ∧
      CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
        selected.view.cutoff x.time selected.view.complementWeights := by
  let liveInput := ReferenceActivePhysicalStep.liveInput x r q base
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live r q base (CoordinatorRoundDispatch.dispatchLive liveInput) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate,
      CoordinatorRoundDispatch.dispatch]
    rfl
  have hselection :
      (ReferenceActivePhysicalStep.DispatchCut.live r q base
        (CoordinatorRoundDispatch.dispatchLive liveInput)).selection = some selected := by
    simpa [ReferenceActivePhysicalStep.prepare, hdispatch] using hselected
  cases hout : CoordinatorRoundDispatch.dispatchLive liveInput with
  | clockFailure failure hfailure =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hout] at hselection
  | initializerFailure dispatched hstart checked hchecked =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hout] at hselection
  | localFailure dispatched hstart reason =>
      simp [ReferenceActivePhysicalStep.DispatchCut.selection, hout] at hselection
  | cutoffChosen dispatched hstart ledger hinitial hledger hvalid hclock hpending hno arm =>
      have hchosen : ReferenceCollectionPhaseHistory.cutoffChosen x = true := by
        simp [ReferenceCollectionPhaseHistory.cutoffChosen,
          ReferenceActivePhysicalStep.prepare, hdispatch, hout]
      rw [hchosen] at hnoCut
      cases hnoCut
  | continuingChosen dispatched hstart continuation arm =>
      have hselectionAt :
          ReferenceActivePhysicalStep.selectionAt x r.payload dispatched.startResult x.time
            (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights arm =
            some selected := by
        simpa [ReferenceActivePhysicalStep.DispatchCut.selection, hout] using hselection
      have hresult := live_dispatch_continuation_result dispatched continuation arm hstart hout
      have hclock : dispatched.startResult.clock = r.priorClock := by
        calc
          dispatched.startResult.clock = continuation.startRoundResult.clock :=
            congrArg CoordinatorPhaseClock.StartRoundResult.clock hresult.symm
          _ = r.priorClock := by
            simpa [liveInput, ReferenceActivePhysicalStep.liveInput,
              ReferenceActivePhysicalStep.liveRegistersAt] using continuation.clockFrame.1
      have hstartU : dispatched.startResult.clock.u = none := by
        rw [hclock]
        exact hpriorU
      have hcutoff : selected.view.cutoff = none := by
        simp only [ReferenceActivePhysicalStep.selectionAt] at hselectionAt
        cases hselectionAt
        change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
          dispatched.startResult.clock.u = none
        rw [hstartU]
        rfl
      have hregFields := ReferenceActivePhysicalStep.liveRegistersAt_fields r x.time
      have hregisterWeight :
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights =
            r.complementWeights := by
        unfold CoordinatorLiveChoiceRecorderStep.Registers.complementWeights
        rw [hregFields.2.2.2.2.1]
        rfl
      have hvalidActual :
          CoordinatorLocalArmChoice.ChoiceInputsValid r.payload none x.time r.complementWeights := by
        have hvalid0 := continuation.choiceInputsValid
        change CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p r.priorClock.u) x.time
          (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights at hvalid0
        rw [hpriorU] at hvalid0
        simpa [CoordinatorLiveChoiceRecorderStep.cutoffFromClock, hregisterWeight] using hvalid0
      have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff x.time selected.view.complementWeights := by
        simp only [ReferenceActivePhysicalStep.selectionAt] at hselectionAt
        cases hselectionAt
        change CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
        rw [hstartU, hregisterWeight]
        exact hvalidActual
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
          selected.view.cutoff x.time := by
        change CoordinatorLocalArmChoice.assignmentStart selected.view.payload ≤
            CoordinatorLocalArmChoice.sourceRound x.time ∧
          CoordinatorLocalArmChoice.sourceRound x.time <
            CoordinatorLocalArmChoice.cutoffRound selected.view.cutoff
        rw [hcutoff]
        simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none]
        constructor
        · exact hvalid.time.assignment_started
        · simp only [CoordinatorLocalArmChoice.sourceRound]
          omega
      exact ⟨hlive, hvalid⟩

private theorem pending_up_other_action_assigned
    {B : ℕ} (hm : 2 ≤ p.m)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a B)
    (j : ActiveRoundActions.Follower p.m)
    (hj : snapshot.status j = .pending) (hslot : input.slot = PublicDiscreteDraws.upSlot)
    (hselected : input.selected ≠ j)
    (htuple : input.tuple.val (ActiveRoundActions.coordinator hm) = a.auxiliary) :
    ActiveRoundActions.followerAction hm snapshot input j = a.assigned j := by
  have haux : a.assigned j ≠ a.auxiliary :=
    fun h => a.auxiliary_outside j h.symm
  simp [ActiveRoundActions.followerAction, PublicDiscreteDraws.dataSlot,
    PublicDiscreteDraws.downSlot, PublicDiscreteDraws.upSlot, hj,
    hslot, hselected, htuple, haux]

private theorem pending_up_feedback_eq_auxiliary
    {B : ℕ} (hm : 2 ≤ p.m)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a B)
    (row : ActiveRoundActions.RewardRow p.K)
    (hmissing : snapshot.missing = ∅)
    (hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released)
    (i : ActiveRoundActions.Follower p.m) (hi : snapshot.status i = .pending)
    (hslot : input.slot = PublicDiscreteDraws.upSlot)
    (hselected : input.selected = i)
    (htuple : input.tuple.val (ActiveRoundActions.coordinator hm) = a.auxiliary)
    (hfast : input.fast ≠ a.auxiliary) :
    ActiveRoundActions.feedback hm snapshot input row
      (PublicDiscreteDraws.followerPlayer hm i) = row.val a.auxiliary := by
  have htarget : ActiveRoundActions.followerAction hm snapshot input i = a.auxiliary := by
    rw [← hselected]
    have hselectedStatus : snapshot.status input.selected = .pending := by
      rw [hselected]
      exact hi
    exact ActiveRoundActions.followerAction_pending_up_test hm snapshot input
      hselectedStatus hslot htuple
  have hfree : FiniteBanditModel.collisionFreeFor
      (ActiveRoundActions.actions hm snapshot input)
      (PublicDiscreteDraws.followerPlayer hm i) := by
    intro q hq hsame
    rcases ActiveRoundActions.player_cases hm q with hcoord | ⟨j, hj⟩
    · rw [hcoord, ActiveRoundActions.actions_coordinator,
        ActiveRoundActions.coordinatorAction_fast hm snapshot input hmissing,
        ActiveRoundActions.actions_follower, htarget] at hsame
      exact hfast hsame
    · have hji : j ≠ i := by
        intro hji
        subst j
        exact hq hj
      have hselected_ne : input.selected ≠ j := by
        rw [hselected]
        exact hji.symm
      have hother : ActiveRoundActions.followerAction hm snapshot input j = a.assigned j := by
        rcases hstatus j with hjp | hjr
        · exact pending_up_other_action_assigned hm a snapshot input j hjp hslot
            hselected_ne htuple
        · exact ActiveRoundActions.followerAction_released hm snapshot input j hjr
      rw [hj, ActiveRoundActions.actions_follower, hother,
        ActiveRoundActions.actions_follower, htarget] at hsame
      exact a.auxiliary_outside j hsame.symm
  rw [ActiveRoundActions.feedback_eq_reward_of_collision_free hm snapshot input row _ hfree,
    ActiveRoundActions.actions_follower, htarget]

private theorem pending_data_feedback_eq_assigned
    {B : ℕ} (hm : 2 ≤ p.m)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a B)
    (row : ActiveRoundActions.RewardRow p.K)
    (hmissing : snapshot.missing = ∅)
    (hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released)
    (i : ActiveRoundActions.Follower p.m)
    (hi : (snapshot.status i).occupied)
    (hslot : input.slot = PublicDiscreteDraws.dataSlot) :
    ActiveRoundActions.feedback hm snapshot input row
      (PublicDiscreteDraws.followerPlayer hm i) = row.val (a.assigned i) := by
  have hfree : FiniteBanditModel.collisionFreeFor
      (ActiveRoundActions.actions hm snapshot input)
      (PublicDiscreteDraws.followerPlayer hm i) := by
    intro q hq hsame
    rcases ActiveRoundActions.player_cases hm q with hcoord | ⟨j, hj⟩
    · rw [hcoord, ActiveRoundActions.actions_coordinator,
        ActiveRoundActions.coordinatorAction_fast hm snapshot input hmissing,
        ActiveRoundActions.actions_follower,
        ActiveRoundActions.followerAction_occupied_data hm snapshot input i hi hslot] at hsame
      exact input.fast_outside i hsame
    · have hji : j ≠ i := by
        intro hji
        subst j
        exact hq hj
      rw [hj, ActiveRoundActions.actions_follower,
        ActiveRoundActions.followerAction_occupied_data hm snapshot input j
          (hstatus j) hslot,
        ActiveRoundActions.actions_follower,
        ActiveRoundActions.followerAction_occupied_data hm snapshot input i hi hslot] at hsame
      exact hji (a.injective hsame)
  rw [ActiveRoundActions.feedback_eq_reward_of_collision_free hm snapshot input row _ hfree,
    ActiveRoundActions.actions_follower,
    ActiveRoundActions.followerAction_occupied_data hm snapshot input i hi hslot]

/-- Exact UP release geometry on a complete occupied snapshot. The collision
argument ranges over every other actual player, including followers that move
to the auxiliary arm. -/
private theorem pending_up_release_geometry
    {B : ℕ} (hm : 2 ≤ p.m)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a B)
    (row : ActiveRoundActions.RewardRow p.K)
    (hmissing : snapshot.missing = ∅)
    (hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released)
    (i : ActiveRoundActions.Follower p.m) (hi : snapshot.status i = .pending) :
    (ActiveRoundActions.releaseObservation hm snapshot input row i ∧
      input.slot = PublicDiscreteDraws.upSlot) ↔
      input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
        input.tuple.val (ActiveRoundActions.coordinator hm) = a.auxiliary ∧
        input.fast ≠ a.auxiliary ∧ 0 < row.val a.auxiliary := by
  constructor
  · rintro ⟨⟨hpos, htest⟩, houter⟩
    rcases htest with ⟨hslot, hselected, htuple⟩ | ⟨hdata, _⟩
    · have hfast : input.fast ≠ a.auxiliary := by
        intro heq
        have htarget : ActiveRoundActions.followerAction hm snapshot input i = a.auxiliary := by
          rw [← hselected]
          have hselectedStatus : snapshot.status input.selected = .pending := by
            rw [hselected]
            exact hi
          exact ActiveRoundActions.followerAction_pending_up_test hm snapshot input
            hselectedStatus hslot htuple
        have hzero := ActiveRoundActions.feedback_eq_zero_of_collision hm snapshot input row
          _ (ActiveRoundActions.coordinator hm)
          (ActiveRoundActions.followerPlayer_ne_coordinator hm i).symm
          (by
            rw [ActiveRoundActions.actions_coordinator,
              ActiveRoundActions.coordinatorAction_fast hm snapshot input hmissing,
              ActiveRoundActions.actions_follower, htarget, heq])
        rw [hzero] at hpos
        exact (lt_irrefl 0) hpos
      have hreward := pending_up_feedback_eq_auxiliary hm a snapshot input row
        hmissing hstatus i hi houter hselected htuple hfast
      exact ⟨houter, hselected, htuple, hfast, by simpa [hreward] using hpos⟩
    · exact False.elim ((by decide : PublicDiscreteDraws.dataSlot ≠
        PublicDiscreteDraws.upSlot) (hdata.symm.trans houter))
  · rintro ⟨hslot, hselected, htuple, hfast, hreward⟩
    refine ⟨⟨?_, Or.inl ⟨hslot, hselected, htuple⟩⟩, hslot⟩
    rw [pending_up_feedback_eq_auxiliary hm a snapshot input row hmissing hstatus
      i hi hslot hselected htuple hfast]
    exact hreward

/-- Exact DATA release geometry. The release test has no recording-mask
condition; it is precisely the coordinator pilot and positive whole-row reward
at the assigned arm. -/
private theorem pending_data_release_geometry
    {B : ℕ} (hm : 2 ≤ p.m)
    (a : ActiveRoundActions.Assignment p.m p.K)
    (snapshot : ActiveRoundActions.Snapshot a)
    (input : ActiveRoundActions.RoundInput a B)
    (row : ActiveRoundActions.RewardRow p.K)
    (hmissing : snapshot.missing = ∅)
    (hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released)
    (i : ActiveRoundActions.Follower p.m) (hi : snapshot.status i = .pending) :
    (ActiveRoundActions.releaseObservation hm snapshot input row i ∧
      input.slot = PublicDiscreteDraws.dataSlot) ↔
      input.slot = PublicDiscreteDraws.dataSlot ∧
        input.pilots (ActiveRoundActions.coordinator hm) = a.assigned i ∧
        0 < row.val (a.assigned i) := by
  constructor
  · rintro ⟨⟨hpos, htest⟩, houter⟩
    rcases htest with ⟨hup, _, _⟩ | ⟨hslot, hpilot⟩
    · exact False.elim ((by decide : PublicDiscreteDraws.upSlot ≠
        PublicDiscreteDraws.dataSlot) (hup.symm.trans houter))
    · have hreward := pending_data_feedback_eq_assigned hm a snapshot input row
        hmissing hstatus i (Or.inl hi) houter
      exact ⟨houter, hpilot, by simpa [hreward] using hpos⟩
  · rintro ⟨hslot, hpilot, hreward⟩
    refine ⟨⟨?_, Or.inr ⟨hslot, hpilot⟩⟩, hslot⟩
    rw [pending_data_feedback_eq_assigned hm a snapshot input row hmissing hstatus
      i (Or.inl hi) hslot]
    exact hreward

/-- The actual ordinary PREPARE states extracted from the integrated
whole-record occupancy theorem at one selected first-live record. -/
theorem prepared_ordinary_states
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0)
    (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hvalid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      selected.view.pendingAtChoice = ∅ →
      ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
        ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
          (∀ i, (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied ∧
            (states i).lastDown = some (selected.view.payload.downRecord i)) := by
  intro E W k selected hselected hempty
  have hoccupied :=
    ReferenceFirstLiveAllFollowerOccupancy.run_first_live_all_follower_occupancy
      initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
      hbacklog hnone hunoccupied hvalid hpair htime hbatch
  have hforall := hoccupied k selected hselected
  classical
  let witness : ∀ i : Fin (p.m - 1),
      ∃ pair : (ReferencePrelaunchFollower.State p rate.eta ×
          ActiveFollowerLifecycle.LocalMemory p) ×
          (ReferencePrelaunchFollower.State p rate.eta ×
            ActiveFollowerLifecycle.LocalMemory p),
        (W[k.val].output.preparation.followers.followers i).configuration =
          .ordinary pair.1.1 pair.1.2 ∧
        (W[k.val].output.followers i).configuration = .ordinary pair.2.1 pair.2.2 ∧
        (W[k.val].output.followers i).failure = none ∧
        (pair.1.1).status ≠ .unoccupied ∧
        (pair.1.1).lastDown = some (selected.view.payload.downRecord i) := by
    intro i
    have hi : i ∉ selected.view.pendingAtChoice := by
      rw [hempty]
      change i ∉ (∅ : Finset (Fin (p.m - 1)))
      simp
    obtain ⟨choice, choiceMemory, next, nextMemory, hprep, hnext, hfailure,
      hstatus, hdown⟩ := hforall i hi
    exact ⟨((choice, choiceMemory), (next, nextMemory)), hprep, hnext,
      hfailure, hstatus, hdown⟩
  let chosen := fun i => Classical.choose (witness i)
  have hchosen := fun i => Classical.choose_spec (witness i)
  refine ⟨fun i => (chosen i).1.1, fun i => (chosen i).1.2, ?_, ?_⟩
  · intro i
    exact (hchosen i).1
  · intro i
    exact ⟨(hchosen i).2.2.2.1, (hchosen i).2.2.2.2⟩

/-- The actual selected record in the exact first-live window is in the
continuing live phase when its computed pending set is empty. Its current
clock, actual cutoff test, and choice validity come from the retained run,
its live dispatcher continuation, and the run clock theorem. -/
theorem first_live_actual_choice_data
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      selected.view.pendingAtChoice = ∅ →
      ∃ r q base,
        W[k.val].input.state.coordinator = .live r q base ∧
        r.time.val + 1 = W[k.val].input.time.val ∧
        r.priorClock.u = none ∧ r.pendingAtChoice = ∅ ∧
        ReferenceCollectionPhaseHistory.cutoffChosen W[k.val].input = false ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
          selected.view.cutoff W[k.val].input.time ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff W[k.val].input.time selected.view.complementWeights := by
  intro E W k selected hselected hempty
  have hprovenance :=
    ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
      initial rows J rewards start count hspan active hfirst
  obtain hzero | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hframes⟩ := hprovenance
  · exact Fin.elim0 (hzero ▸ k)
  · obtain ⟨record, hrecord, sourceSelected, hsourceActual, hpayload, hphase,
        next, nextOwned, nextBase, hnextLive, hnextPayload, hpendingUpdate, hcoverage⟩ :=
      hframes k
    subst record
    have hselectedEq : sourceSelected = selected :=
      Option.some.inj (hsourceActual.symm.trans hselected)
    subst sourceSelected
    have hwindowMember : W[k.val] ∈ W := List.getElem_mem k.isLt
    have hnoCut : ReferenceCollectionPhaseHistory.cutoffChosen W[k.val].input = false := by
      have hpredicate := List.mem_takeWhile_imp hwindowMember
      simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        Bool.not_eq_true'] using hpredicate
    have hclockSeed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
      simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
    have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
      start count hspan active hclockSeed
    have hwindowPrefix : W.IsPrefix E.records := List.takeWhile_prefix _
    have hkRecord : k.val < E.records.length := lt_of_lt_of_le k.isLt hwindowPrefix.length_le
    have hwindowGet : W[k.val] = E.records[k.val] := hwindowPrefix.getElem k.isLt
    have hrecordMem : W[k.val] ∈ E.records := by
      rw [hwindowGet]
      exact List.getElem_mem hkRecord
    have hclockAt := hclockRun.2.2.2 W[k.val] hrecordMem
    change (match W[k.val].input.state.coordinator with
      | .first => selected.view.pendingAtChoice = Finset.univ ∧
          selected.started.pending = Finset.univ
      | .live incoming _ _ => selected.view.payload = incoming.payload ∧
          selected.view.pendingAtChoice = incoming.pendingAtChoice ∧
          selected.started.pending = incoming.pendingAtChoice
      | _ => False) at hphase
    cases hcoord : W[k.val].input.state.coordinator with
    | first =>
        simp only [hcoord] at hphase
        have hemptyUniv : (∅ : Finset (ActiveRoundActions.Follower p.m)) = Finset.univ :=
          hempty.symm.trans hphase.1
        have hnonempty : (Finset.univ : Finset (ActiveRoundActions.Follower p.m)).Nonempty :=
          ⟨⟨0, PublicDiscreteDraws.followerCount_pos p.two_le_m⟩, Finset.mem_univ _⟩
        rcases hnonempty with ⟨i, hi⟩
        rw [← hemptyUniv] at hi
        simp at hi
    | collection payload ledger proposal => simp only [hcoord] at hphase
    | dagger => simp only [hcoord] at hphase
    | live r q base =>
        simp only [hcoord] at hphase
        rcases hphase with ⟨_, hpending, _⟩
        have hstate : W[k.val].input.state.coordinator = .live r q base := hcoord
        have hemptyRegister : r.pendingAtChoice = ∅ := hpending.symm.trans hempty
        have hclockLive := hclockAt.1
        simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclockLive
        have hpriorU : r.priorClock.u = none := hclockLive.2.2.2.1
        have hselectedPrepared :
            (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection =
              some selected := by
          simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
        obtain ⟨hlive, hvalid⟩ := selected_live_choice_data_of_clock selected r q base
          hstate hpriorU hnoCut hselectedPrepared hempty
        exact ⟨r, q, base, rfl, hclockLive.1, hpriorU, hemptyRegister, hnoCut,
          hlive, hvalid⟩

/-- At an actual selected first-live record with empty computed missing set,
construct the existing width-zero release-kernel input from the same physical
continuous slice. Follower states and DOWN getters are characterized on their
actual ordinary PREPARE constructors. -/
theorem first_live_actual_release_projection
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0)
    (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hbuffer : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      selected.view.pendingAtChoice = ∅ →
      ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff W[k.val].input.time selected.view.complementWeights,
        ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
        ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
          (∀ i, (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied ∧
            (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
          ∃ input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0,
            input = actualReleaseKernelInput selected hvalid ∧
            input.slot = PublicDiscreteDraws.slotDraw
              (W[k.val].input.row.2 W[k.val].input.time).1 ∧
            input.selected = PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (W[k.val].input.row.2 W[k.val].input.time).1 ∧
            input.tuple = OrderedTupleSampler.sample p.two_le_m p.m_lt_K
              (W[k.val].input.row.2 W[k.val].input.time).1 ∧
            input.pilots = (fun player => PublicDiscreteDraws.pilotDraw
              (K_pos p) player (W[k.val].input.row.2 W[k.val].input.time).1) ∧
            input.fast = selected.arm ∧
            selected.arm ∉ selected.view.payload.slowSet.val ∧
            (ReferenceActivePhysicalStep.prepare W[k.val].input).arms.actions =
              ActiveRoundActions.actions p.two_le_m
                (actualChoiceSnapshot selected states) input ∧
            (∀ player : Fin p.m,
              ((ReferenceActivePhysicalStep.prepare W[k.val].input).feedback.observations
                player).val.val =
                ActiveRoundActions.feedback p.two_le_m
                  (actualChoiceSnapshot selected states) input
                  (wholeGridRewardRow (W[k.val].input.rewards) W[k.val].input.time) player) ∧
            (∀ i, ActiveFollowerLifecycle.releaseCondition rate.eta i
                (ActiveFollowerLifecycle.publicRowOfCompleteRow W[k.val].input.row
                  W[k.val].input.time)
                ((ReferenceActivePhysicalStep.prepare W[k.val].input).feedback.observations
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i))
                (selected.view.payload.downRecord i) =
              ActiveRoundActions.releaseObservation p.two_le_m
                (actualChoiceSnapshot selected states) input
                (wholeGridRewardRow (W[k.val].input.rewards) W[k.val].input.time) i) := by
  intro E W k selected hselected hempty
  obtain ⟨r, q, base, hstate, _, hpriorU, hpending, hnoCut, hlive, hvalid⟩ :=
    first_live_actual_choice_data initial rows J rewards start count hspan active hfirst
      k selected hselected hempty
  have hselectedPrepared :
      (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection =
        some selected := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
  obtain ⟨states, memories, hordinary, hfields⟩ := prepared_ordinary_states
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hbuffer hpair htime hbatch k selected hselected hempty
  let snapshot := actualChoiceSnapshot selected states
  let input := actualReleaseKernelInput selected hvalid
  have hfastFacts := actual_releaseRoundInput_fast_eq_selected selected hlive hempty hvalid
  have hfast : input.fast = selected.arm := by
    simpa only [input, actualReleaseKernelInput] using hfastFacts.1
  have hfastOutside : selected.arm ∉ selected.view.payload.slowSet.val := by
    simpa only [input, actualReleaseKernelInput] using hfastFacts.2
  have hmissing : snapshot.missing = ∅ := by
    change selected.view.pendingAtChoice = ∅
    exact hempty
  have hslot : PublicDiscreteDraws.slotDraw (W[k.val].input.row.2
      W[k.val].input.time).1 = input.slot := by rfl
  have hselectedDraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (W[k.val].input.row.2 W[k.val].input.time).1 = input.selected := by rfl
  have htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      (W[k.val].input.row.2 W[k.val].input.time).1 = input.tuple := by rfl
  have hordinaryPrepared : ∀ i,
      ((ReferenceActivePhysicalStep.prepare W[k.val].input).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
    intro i
    have hconfiguration := hordinary i
    rw [W[k.val].output_eq] at hconfiguration
    simpa [ReferenceActivePhysicalStep.step] using hconfiguration
  have hactions := prepared_actions_eq_projected selected hselectedPrepared states memories
    hordinaryPrepared hfields input hmissing (by rfl) (by rfl) (by rfl) hfast
  have hstatus : ∀ i, snapshot.status i = .pending ∨ snapshot.status i = .released := by
    intro i
    change (states i).status = .pending ∨ (states i).status = .released
    cases hstateStatus : (states i).status with
    | unoccupied => exact False.elim ((hfields i).1 hstateStatus)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hpilots : input.pilots = fun player => PublicDiscreteDraws.pilotDraw
      (K_pos p) player (W[k.val].input.row.2 W[k.val].input.time).1 := by rfl
  refine ⟨hvalid, states, memories, hordinary, hfields, input, rfl, hslot.symm,
    hselectedDraw.symm, htuple.symm, hpilots, hfast, hfastOutside, hactions, ?_, ?_⟩
  · intro player
    exact prepared_observation_eq_projected selected snapshot input player hactions
  · intro i
    simpa [followerToFin, ActiveRoundActions.Follower,
      PublicDiscreteDraws.followerCount] using
      prepared_releaseCondition_eq_projected selected snapshot input i hactions
        (by rfl) (by rfl) (by rfl) hpilots

/-- Exact pending-UP and pending-DATA release events for an actual local
release condition already identified with the common action kernel. This
conditional helper exposes the state, width-zero input, and release-observation
identity separately; the root projection theorem above supplies them from the
computed first-live record and does not assume them. -/
theorem actual_pending_release_event_geometry
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0)
    (row : ActiveRoundActions.RewardRow p.K)
    (hmissing : snapshot.missing = ∅)
    (hstatus : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released)
    (i : ActiveRoundActions.Follower p.m)
    (hstatusI : snapshot.status i = .pending)
    (hrelease : ActiveFollowerLifecycle.releaseCondition rate.eta (followerToFin i)
        (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) =
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input row i) :
    ((ActiveFollowerLifecycle.releaseCondition rate.eta (followerToFin i)
        (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) ∧
      input.slot = PublicDiscreteDraws.upSlot) ↔
      input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
        input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
          selected.view.payload.assignment.auxiliary ∧
        input.fast ≠ selected.view.payload.assignment.auxiliary ∧
        0 < row.val selected.view.payload.assignment.auxiliary) ∧
    ((ActiveFollowerLifecycle.releaseCondition rate.eta (followerToFin i)
        (ActiveFollowerLifecycle.publicRowOfCompleteRow x.row x.time)
        ((ReferenceActivePhysicalStep.prepare x).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) ∧
      input.slot = PublicDiscreteDraws.dataSlot) ↔
      input.slot = PublicDiscreteDraws.dataSlot ∧
        input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
          selected.view.payload.assignment.assigned i ∧
        0 < row.val (selected.view.payload.assignment.assigned i)) := by
  have hstatus' : ∀ j, snapshot.status j = .pending ∨ snapshot.status j = .released := hstatus
  constructor
  · rw [hrelease]
    exact pending_up_release_geometry p.two_le_m selected.view.payload.assignment snapshot
      input row hmissing hstatus' i hstatusI
  · rw [hrelease]
    exact pending_data_release_geometry p.two_le_m selected.view.payload.assignment snapshot
      input row hmissing hstatus' i hstatusI

/-- The existing physical flags use the same typed own observation as the
prepared round. These are literal tests, including on a detecting round;
they do not assert success of any later service or release update.
Sources: `05_binary_transport.tex:80-88`, `06_interruptions.tex:287-293`. -/
theorem actual_release_flags_iff (record : Record (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    (ReferencePhysicalReleaseQuota.upFlag payload record i = true ↔
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (payload.downRecord i) ∧
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.upSlot) ∧
    (ReferencePhysicalReleaseQuota.dataFlag payload record i = true ↔
      ActiveFollowerLifecycle.releaseCondition rate.eta i
        (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) (payload.downRecord i) ∧
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.dataSlot) := by
  simp only [ReferencePhysicalReleaseQuota.upFlag, ReferencePhysicalReleaseQuota.dataFlag,
    ReferencePhysicalReleaseQuota.releaseFlag, Bool.and_eq_true, decide_eq_true_eq,
    ReferencePhysicalReleaseQuota.own_observation_eq, and_self]

/-- At an actual first-live empty-missing-set record, every pending computed
ordinary follower satisfies the exact physical UP and DATA flag equivalences.
The same witnesses retain all-player actions and whole-row feedback identities.
The lifecycle observation identity comes from `first_live_actual_release_projection`.
Sources: `05_binary_transport.tex:94-124,293-318`, `06_interruptions.tex:287-293`. -/
theorem first_live_actual_pending_release_geometry
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0)
    (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hbuffer : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      selected.view.pendingAtChoice = ∅ →
      ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff W[k.val].input.time selected.view.complementWeights,
        ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
        ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
          (∀ i, (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied ∧
            (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
          ∃ input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0,
            input = actualReleaseKernelInput selected hvalid ∧
            input.fast = selected.arm ∧
            selected.arm ∉ selected.view.payload.slowSet.val ∧
            (ReferenceActivePhysicalStep.prepare W[k.val].input).arms.actions =
              ActiveRoundActions.actions p.two_le_m
                (actualChoiceSnapshot selected states) input ∧
            (∀ player : Fin p.m,
              ((ReferenceActivePhysicalStep.prepare W[k.val].input).feedback.observations
                player).val.val =
                ActiveRoundActions.feedback p.two_le_m
                  (actualChoiceSnapshot selected states) input
                  (wholeGridRewardRow W[k.val].input.rewards W[k.val].input.time) player) ∧
            (∀ i : ActiveRoundActions.Follower p.m, (states (followerToFin i)).status = .pending →
              (ReferencePhysicalReleaseQuota.upFlag selected.view.payload W[k.val]
                (followerToFin i) = true ↔
                input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
                  input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
                    selected.view.payload.assignment.auxiliary ∧
                  input.fast ≠ selected.view.payload.assignment.auxiliary ∧
                  0 < (wholeGridRewardRow W[k.val].input.rewards
                    W[k.val].input.time).val selected.view.payload.assignment.auxiliary)) ∧
            (∀ i : ActiveRoundActions.Follower p.m, (states (followerToFin i)).status = .pending →
              (ReferencePhysicalReleaseQuota.dataFlag selected.view.payload W[k.val]
                (followerToFin i) = true ↔
                input.slot = PublicDiscreteDraws.dataSlot ∧
                  input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
                    selected.view.payload.assignment.assigned i ∧
                  0 < (wholeGridRewardRow W[k.val].input.rewards
                    W[k.val].input.time).val
                    (selected.view.payload.assignment.assigned i))) := by
  intro E W k selected hselected hempty
  obtain ⟨hvalid, states, memories, hordinary, hfields, input, hinput,
      hslot, hselectedDraw, htuple, hpilots, hfast, hfastOutside, hactions,
      hobservations, hrelease⟩ :=
    first_live_actual_release_projection initial rows J rewards start count hspan active hfirst
      seed memory hseed hS hdelta hbacklog hnone hunoccupied hbuffer hpair htime hbatch
      k selected hselected hempty
  let snapshot := actualChoiceSnapshot selected states
  have hmissing : snapshot.missing = ∅ := by
    change selected.view.pendingAtChoice = ∅
    exact hempty
  have hstatus : ∀ i, snapshot.status i = .pending ∨ snapshot.status i = .released := by
    intro i
    change (states (followerToFin i)).status = .pending ∨
      (states (followerToFin i)).status = .released
    cases hstateStatus : (states (followerToFin i)).status with
    | unoccupied => exact False.elim ((hfields (followerToFin i)).1 hstateStatus)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  refine ⟨hvalid, states, memories, hordinary, hfields, input, hinput,
    hfast, hfastOutside, hactions, hobservations, ?_, ?_⟩
  · intro i hi
    have hreleaseI : ActiveFollowerLifecycle.releaseCondition rate.eta (followerToFin i)
        (ActiveFollowerLifecycle.publicRowOfCompleteRow W[k.val].input.row
          W[k.val].input.time)
        ((ReferenceActivePhysicalStep.prepare W[k.val].input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) =
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input
        (wholeGridRewardRow W[k.val].input.rewards W[k.val].input.time) i := by
      have hindex : followerToFin i = i := by
        apply Fin.ext
        rfl
      simpa [hindex] using hrelease (followerToFin i)
    have hstatusI : snapshot.status i = .pending := by
      change (states (followerToFin i)).status = .pending
      exact hi
    have hphysical := (actual_release_flags_iff W[k.val] selected.view.payload
      (followerToFin i)).1
    rw [← hslot] at hphysical
    exact hphysical.trans (actual_pending_release_event_geometry selected snapshot input
      (wholeGridRewardRow W[k.val].input.rewards W[k.val].input.time)
      hmissing hstatus i hstatusI hreleaseI).1
  · intro i hi
    have hreleaseI : ActiveFollowerLifecycle.releaseCondition rate.eta (followerToFin i)
        (ActiveFollowerLifecycle.publicRowOfCompleteRow W[k.val].input.row
          W[k.val].input.time)
        ((ReferenceActivePhysicalStep.prepare W[k.val].input).feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (selected.view.payload.downRecord i) =
      ActiveRoundActions.releaseObservation p.two_le_m snapshot input
        (wholeGridRewardRow W[k.val].input.rewards W[k.val].input.time) i := by
      have hindex : followerToFin i = i := by
        apply Fin.ext
        rfl
      simpa [hindex] using hrelease (followerToFin i)
    have hstatusI : snapshot.status i = .pending := by
      change (states (followerToFin i)).status = .pending
      exact hi
    have hphysical := (actual_release_flags_iff W[k.val] selected.view.payload
      (followerToFin i)).2
    rw [← hslot] at hphysical
    exact hphysical.trans (actual_pending_release_event_geometry selected snapshot input
      (wholeGridRewardRow W[k.val].input.rewards W[k.val].input.time)
      hmissing hstatus i hstatusI hreleaseI).2

/-- Original-source crossing specialization of the joint action, feedback,
and physical-release-flag projection. It reuses the same corrected-launch
witness and terminal zero-record case from the integrated all-follower theorem.
Sources: `05_binary_transport.tex:293-318`, `appendix_a_local_protocol.tex:28-64`. -/
theorem original_source_first_live_release_projection
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s count : ℕ)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (hspan : s + count ≤ p.T) :
    ∃ initial : ReferenceActivePhysicalHorizon.State p rate,
      ∃ seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
        ∃ memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
          ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s,
            ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards
              C_star C_h = some initial ∧
            initial.coordinator = .first ∧
            (∀ i, initial.followers i = .ordinary (seed i) (memory i)) ∧
            (∀ i, (seed i).S = 0) ∧
            (∀ i, (seed i).delta = 0) ∧
            (∀ i, (seed i).backlog = 0) ∧
            (∀ i, (seed i).lastDown = none) ∧
            (∀ i, ReferencePrelaunchFollower.acceptedStart (seed i) = 0) ∧
            (∀ i, (seed i).status = .unoccupied) ∧
            (∀ i, ActiveFollowerLifecycle.localBufferValid (seed i)) ∧
            (∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound)) ∧
            (∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s) ∧
            (∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) ∧
            (let E := ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
              (by omega) hmode
             let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
             (∀ (k : Fin W.length) (selected : Selection W[k.val].input),
               W[k.val].output.preparation.coordinator.selection = some selected →
               selected.view.pendingAtChoice = ∅ →
               ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
                   selected.view.cutoff W[k.val].input.time selected.view.complementWeights,
                 ∃ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
                 ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
                   (∀ i, (W[k.val].output.preparation.followers.followers i).configuration =
                     .ordinary (states i) (memories i)) ∧
                   (∀ i, (states i).status ≠ .unoccupied ∧
                     (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
                   ∃ input : ActiveRoundActions.RoundInput selected.view.payload.assignment 0,
                     input = actualReleaseKernelInput selected hvalid ∧
                     input.fast = selected.arm ∧
                     selected.arm ∉ selected.view.payload.slowSet.val ∧
                     (ReferenceActivePhysicalStep.prepare W[k.val].input).arms.actions =
                       ActiveRoundActions.actions p.two_le_m
                         (actualChoiceSnapshot selected states) input ∧
                     (∀ player : Fin p.m,
                       ((ReferenceActivePhysicalStep.prepare W[k.val].input).feedback.observations
                         player).val.val =
                         ActiveRoundActions.feedback p.two_le_m
                           (actualChoiceSnapshot selected states) input
                           (wholeGridRewardRow W[k.val].input.rewards
                             W[k.val].input.time) player) ∧
                     (∀ i : ActiveRoundActions.Follower p.m,
                       (states (followerToFin i)).status = .pending →
                       (ReferencePhysicalReleaseQuota.upFlag selected.view.payload W[k.val]
                         (followerToFin i) = true ↔
                         input.slot = PublicDiscreteDraws.upSlot ∧ input.selected = i ∧
                           input.tuple.val (ActiveRoundActions.coordinator p.two_le_m) =
                             selected.view.payload.assignment.auxiliary ∧
                           input.fast ≠ selected.view.payload.assignment.auxiliary ∧
                           0 < (wholeGridRewardRow W[k.val].input.rewards
                             W[k.val].input.time).val
                             selected.view.payload.assignment.auxiliary)) ∧
                     (∀ i : ActiveRoundActions.Follower p.m,
                       (states (followerToFin i)).status = .pending →
                       (ReferencePhysicalReleaseQuota.dataFlag selected.view.payload W[k.val]
                         (followerToFin i) = true ↔
                         input.slot = PublicDiscreteDraws.dataSlot ∧
                           input.pilots (ActiveRoundActions.coordinator p.two_le_m) =
                             selected.view.payload.assignment.assigned i ∧
                           0 < (wholeGridRewardRow W[k.val].input.rewards
                             W[k.val].input.time).val
                             (selected.view.payload.assignment.assigned i)))) ∧
             (s = p.T → count = 0 ∧ E.finalState = initial ∧ E.records = [])) := by
  obtain ⟨initial, seed, memory, hmode, hlaunch, hfirst, hseed, hS, hdelta,
      hbacklog, hnone, haccepted, hunoccupied, hbuffer, hpair, htime, hbatch,
      hsourceProofs⟩ :=
    ReferenceFirstLiveAllFollowerOccupancy.original_source_first_live_all_follower_occupancy
      source rewards C_star C_h hc s count helapsed hspan
  have hprojection := first_live_actual_pending_release_geometry initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count (by omega)
    hmode hfirst seed memory hseed hS hdelta hbacklog hnone hunoccupied hbuffer hpair htime hbatch
  refine ⟨initial, seed, memory, hmode, hlaunch, hfirst, hseed, hS, hdelta, hbacklog,
    hnone, haccepted, hunoccupied, hbuffer, hpair, htime, hbatch, ?_⟩
  dsimp only
  constructor
  · exact hprojection
  · exact hsourceProofs.2.2

end Bandits.Support.ReferenceFirstLiveReleaseGeometry

end
