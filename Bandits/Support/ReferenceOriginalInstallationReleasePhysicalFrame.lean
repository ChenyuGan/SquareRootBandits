/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostReplacementCollectionStoppedReleaseSignedCost
public import Bandits.Support.ReferenceOriginalStoppedPhysicalTransferStarts

import Mathlib.Tactic

/-!
# Actual local release frame on the original physical source
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferencePhysicalReleaseQuota
open Bandits.Support.ReleaseRoundKernel
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

variable {p : ConstructorDimensions.Parameters}

private theorem takeWhile_length_le {α : Type} (xs : List α) (pred : α → Bool) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      cases hp : pred head <;> simp [List.takeWhile, hp, ih]

private theorem physical_sentinel_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hstate : record.input.state.coordinator = .live registers owned base)
    (hpayload : registers.payload = selected.view.payload)
    (hpending : registers.pendingAtChoice = ∅)
    (hempty : selected.view.pendingAtChoice = ∅)
    (hfields : ∀ i, (states i).status ≠ .unoccupied ∧
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfast : (actualReleaseKernelInput selected
      (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)).fast = selected.arm)
    (hactions : (ReferenceActivePhysicalStep.prepare record.input).arms.actions =
      ActiveRoundActions.actions p.two_le_m (actualChoiceSnapshot selected states)
        (actualReleaseKernelInput selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))) :
    let row := wholeGridRewardRow record.input.rewards record.input.time
    slowReward row selected.view.payload.slowSet + row.val selected.arm -
        (∑ player : Fin p.m, ((record.ownEntries player).2).val.val) ≤
      (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload record,
        chi row (selected.view.payload.assignment.assigned i)) +
      (if selected.arm = selected.view.payload.assignment.auxiliary ∧
          (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload record).Nonempty then
        row.val selected.view.payload.assignment.auxiliary else 0) := by
  classical
  let snapshot := actualChoiceSnapshot selected states
  let input := actualReleaseKernelInput selected
    (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
  let row := wholeGridRewardRow record.input.rewards record.input.time
  have hobservations (player : Fin p.m) :=
    prepared_observation_eq_projected selected snapshot input player hactions
  have hownObservation : ∀ player : Fin p.m,
      ((record.ownEntries player).2).val.val =
        ((ReferenceActivePhysicalStep.prepare (record.input)).feedback.observations
          player).val.val := by
    intro player
    rw [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula
      record player]
    simp only [ReferenceActivePhysicalHorizon.RoundRecord.actions,
      record.output_eq]
    rfl
  have htotal : ReleaseRoundKernel.physicalFeedbackTotal p.two_le_m snapshot input row =
      ∑ player : Fin p.m, ((record.ownEntries player).2).val.val := by
    have hfollowers (f : Fin p.m → ℝ) :
        (∑ follower : ActiveRoundActions.Follower p.m,
          f (PublicDiscreteDraws.followerPlayer p.two_le_m follower)) =
        ∑ player ∈ Finset.univ.erase (ActiveRoundActions.coordinator p.two_le_m), f player := by
      classical
      apply Finset.sum_bij (s := Finset.univ)
        (t := Finset.univ.erase (ActiveRoundActions.coordinator p.two_le_m))
        (fun follower _ => PublicDiscreteDraws.followerPlayer p.two_le_m follower)
      · intro follower _
        exact Finset.mem_erase.mpr ⟨
          ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m follower,
          Finset.mem_univ _⟩
      · intro follower _ other _ heq
        exact ActiveRoundActions.followerPlayer_injective p.two_le_m heq
      · intro player hplayer
        rcases Finset.mem_erase.mp hplayer with ⟨hne, _⟩
        refine ⟨ActiveRoundActions.followerIndex p.two_le_m player hne,
          Finset.mem_univ _, ?_⟩
        exact ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hne
      · intro follower _
        rfl
    have hsum (f : Fin p.m → ℝ) :
        (∑ player : Fin p.m, f player) =
          f (ActiveRoundActions.coordinator p.two_le_m) +
            ∑ follower : ActiveRoundActions.Follower p.m,
              f (PublicDiscreteDraws.followerPlayer p.two_le_m follower) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ _), hfollowers]
    have hfeedback (player : Fin p.m) :
        ActiveRoundActions.feedback p.two_le_m snapshot input row player =
          ((record.ownEntries player).2).val.val := by
      calc
        ActiveRoundActions.feedback p.two_le_m snapshot input row player =
            ((ReferenceActivePhysicalStep.prepare (record.input)).feedback.observations
              player).val.val :=
          (hobservations player).symm
        _ = ((record.ownEntries player).2).val.val :=
          (hownObservation player).symm
    calc
      ReleaseRoundKernel.physicalFeedbackTotal p.two_le_m snapshot input row =
          ActiveRoundActions.feedback p.two_le_m snapshot input row
            (ActiveRoundActions.coordinator p.two_le_m) +
            ∑ follower : ActiveRoundActions.Follower p.m,
              ActiveRoundActions.feedback p.two_le_m snapshot input row
                (PublicDiscreteDraws.followerPlayer p.two_le_m follower) := rfl
      _ = ((record.ownEntries (ActiveRoundActions.coordinator p.two_le_m)).2).val.val +
            ∑ follower : Fin (p.m - 1),
              ((record.ownEntries
                (PublicDiscreteDraws.followerPlayer p.two_le_m follower)).2).val.val := by
          rw [hfeedback (ActiveRoundActions.coordinator p.two_le_m)]
          apply congrArg
          apply Finset.sum_congr rfl
          intro follower _
          exact hfeedback (PublicDiscreteDraws.followerPlayer p.two_le_m follower)
      _ = ∑ player : Fin p.m, ((record.ownEntries player).2).val.val :=
        (hsum (fun player => ((record.ownEntries player).2).val.val)).symm
  let toFollower (i : Fin (p.m - 1)) : ActiveRoundActions.Follower p.m :=
    ⟨i.val, i.isLt⟩
  have hpendingStatus (i : Fin (p.m - 1)) :
      i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload record ↔
        snapshot.status (toFollower i) = .pending :=
    ReferencePhysicalReleaseQuota.pendingAtStart_ordinary_prepare
      selected.view.payload record.input registers owned base hstate hpayload hpending
      i (states i) (memories i) (hordinary i)
  have hpendingSum :
      (∑ i : ActiveRoundActions.Follower p.m,
        if snapshot.status i = .pending then
          chi row (selected.view.payload.assignment.assigned i) else 0) =
      ∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload record,
        chi row (selected.view.payload.assignment.assigned (toFollower i)) := by
    change (∑ i : Fin (p.m - 1),
      if snapshot.status (toFollower i) = .pending then
        chi row (selected.view.payload.assignment.assigned (toFollower i)) else 0) = _
    simp_rw [← hpendingStatus]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hcollision : (∃ i, snapshot.status i = .pending) ↔
      (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload record).Nonempty := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨followerToFin i, (hpendingStatus (followerToFin i)).mpr hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨toFollower i, (hpendingStatus i).mp hi⟩
  have hstatus (i : ActiveRoundActions.Follower p.m) :
      snapshot.status i = .pending ∨ snapshot.status i = .released := by
    change (states i).status = .pending ∨ (states i).status = .released
    cases hs : (states i).status with
    | unoccupied => exact False.elim ((hfields i).1 hs)
    | pending => exact Or.inl rfl
    | released => exact Or.inr rfl
  have hcost := ReleaseRoundKernel.pathwise_sentinel_cost_bound p.two_le_m
    selected.view.payload.assignment selected.view.payload.slowSet
    selected.view.payload.assignment_image.symm snapshot hempty hstatus input row
  rw [hfast, htotal, hpendingSum] at hcost
  simp only [hcollision] at hcost
  exact hcost

private theorem arbitraryLaterInstallationReleaseProjection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
      ∀ b : Fin R.length,
        if ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true then
          let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
            rate rewards C_star C_h z (b.val + 1)
          let V := R[b.val] :: W
          let Rel := V.dropWhile
            ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
          ∀ i (hi : i < Rel.length),
            ∃ j, ∃ hj : j < W.length,
              Rel[i]'hi = W[j]'hj ∧
              ∃ k : Fin R.length, k.val = b.val + 1 + j ∧
              ∃ selected : ReferenceActivePhysicalStep.Selection
                  (R[k.val].input),
                ∃ states : Fin (p.m - 1) →
                  ReferencePrelaunchFollower.State p rate.eta,
                ∃ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
                ∃ input : ActiveRoundActions.RoundInput
                  selected.view.payload.assignment 0,
                  W[j]'hj = R[k.val] ∧
                  R[k.val].output.preparation.coordinator.selection =
                    some selected ∧
                  selected.view.pendingAtChoice = ∅ ∧
                  CoordinatorLocalArmChoice.assignmentIsLive
                    selected.view.payload selected.view.cutoff
                    R[k.val].input.time ∧
                  CoordinatorLocalArmChoice.ChoiceInputsValid
                    selected.view.payload selected.view.cutoff
                    R[k.val].input.time selected.view.complementWeights ∧
                  (∀ follower,
                    (ReferenceFollowerFixedReply.actualChoice
                      R[k.val] follower).configuration =
                        .ordinary (states follower) (memories follower)) ∧
                  (∀ follower, (states follower).status ≠ .unoccupied ∧
                    (states follower).lastDown =
                      some (selected.view.payload.downRecord follower)) ∧
                  ReferenceActiveDataOwnership.carriedOccupiedFields
                    selected.view.payload R[k.val].input.state ∧
                  ReferenceActiveDataOwnership.carriedOccupiedFields
                    selected.view.payload R[k.val].output.next ∧
                  input = ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput
                    selected (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) ∧
                  input.fast = selected.arm ∧
                  selected.arm ∉ selected.view.payload.slowSet.val ∧
                  (ReferenceActivePhysicalStep.prepare
                    R[k.val].input).arms.actions =
                    ActiveRoundActions.actions p.two_le_m
                      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
                      input ∧
                  (∀ player : Fin p.m,
                    ((ReferenceActivePhysicalStep.prepare
                      R[k.val].input).feedback.observations player).val.val =
                    ActiveRoundActions.feedback p.two_le_m
                      (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
                      input
                      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time) player) ∧
                  ReleaseRoundKernel.slowReward
                    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                      rewards R[k.val].input.time)
                    selected.view.payload.slowSet +
                    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                      rewards R[k.val].input.time).val selected.arm -
                    (∑ player : Fin p.m,
                      ((R[k.val].ownEntries player).2).val.val) ≤
                  (∑ follower ∈ ReferencePhysicalReleaseQuota.pendingSet
                    selected.view.payload R[k.val],
                    ReleaseRoundKernel.chi
                      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                        rewards R[k.val].input.time)
                      (selected.view.payload.assignment.assigned follower)) +
                  (if selected.arm = selected.view.payload.assignment.auxiliary ∧
                      (ReferencePhysicalReleaseQuota.pendingSet
                        selected.view.payload R[k.val]).Nonempty then
                    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                      rewards R[k.val].input.time).val
                        selected.view.payload.assignment.auxiliary
                  else 0)
        else True := by
  classical
  intro R b
  by_cases hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true
  · simp only [ite_eq_left hb]
    let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)
    let V := R[b.val] :: W
    let Rel := V.dropWhile
      ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
    have hoccupied :=
      ReferencePostReplacementCollectionReleaseBoundary.actual_later_installation_release_suffix_actual_occupied
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hoccupied
    have hhistory :=
      ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
    rw [ite_eq_left hb] at hhistory
    rcases hhistory with
      ⟨birthRegisters, birthOwned, beta, birthSelected, _hnext, _hbirth,
        hlaterBirth, _hbSelection, _hbPayload, _hbPending, _hbNoEvent,
        _hbFollowers, _hcontinued, _hnoRelease, hframes⟩
    change ∀ i (hi : i < Rel.length), _
    intro i hi
    obtain ⟨j, hj, hrelW, selectedW, hselectedW, hemptyW, hoccupiedW⟩ :=
      hoccupied i hi
    have hjW : j < W.length := by
      simpa only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix] using hj
    have htake : W.length ≤ (R.drop (b.val + 1)).length := by
      dsimp only [W, ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
      exact takeWhile_length_le _ _
    have hdrop : (R.drop (b.val + 1)).length = R.length - (b.val + 1) := by
      simp only [List.length_drop]
    have hboundW : b.val + 1 + W.length ≤ R.length := by
      rw [hdrop] at htake
      have hbLt := b.isLt
      omega
    have hindexBound : b.val + 1 + j < R.length := by omega
    have hbPlus : b.val + 1 < R.length := by omega
    let k : Fin R.length := ⟨b.val + 1 + j, hindexBound⟩
    have hprefix := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_index
      rewards C_star C_h z ⟨b.val + 1, hbPlus⟩ j hj
    have hrecordW : W[j]'hj = R[k.val]'k.isLt := by
      simpa only [k] using hprefix
    have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h ≠ none := by
      intro hnone
      have hindex : b.val + 1 + j < R.length := by
        simpa only [k] using k.isLt
      simp [R, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone] at hindex
    let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate z rewards C_star C_h hlaunchNe
    have hlaunch := ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
      rate z rewards C_star C_h hlaunchNe
    have hrunRecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hlaunch
    have hrunInputs := ReferenceActivePhysicalHorizon.run_record_inputs
      active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (by
        have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
        omega)
      (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate z rewards C_star C_h active hlaunch)
    have hrecordMemRun : R[k.val]'k.isLt ∈
        (ReferenceActivePhysicalHorizon.run active z.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (by
            have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
              rate z rewards C_star C_h
            omega)
          (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
            rate z rewards C_star C_h active hlaunch)).records := by
      rw [← hrunRecords]
      exact List.getElem_mem k.isLt
    have hrecordRewards := (hrunInputs _ hrecordMemRun).2.2
    have hrewards : R[k.val].input.rewards = rewards := hrecordRewards
    have hrelIndex : Rel[i]'hi = W[j]'hj := hrelW
    have hoccW : ∃ selected : ReferenceActivePhysicalStep.Selection W[j].input,
        W[j].output.preparation.coordinator.selection = some selected ∧
        selected.view.pendingAtChoice = ∅ ∧
        ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p),
          (ReferenceFollowerFixedReply.actualChoice W[j] follower).configuration =
            .ordinary choice memory → choice.status ≠ .unoccupied :=
      ⟨selectedW, hselectedW, hemptyW, hoccupiedW⟩
    have hoccRecord :
        ∃ selected : ReferenceActivePhysicalStep.Selection (R[k.val].input),
          R[k.val].output.preparation.coordinator.selection = some selected ∧
          selected.view.pendingAtChoice = ∅ ∧
          ∀ follower (choice : ReferencePrelaunchFollower.State p rate.eta)
            (memory : ActiveFollowerLifecycle.LocalMemory p),
            (ReferenceFollowerFixedReply.actualChoice R[k.val] follower).configuration =
              .ordinary choice memory → choice.status ≠ .unoccupied := by
      exact hrecordW ▸ hoccW
    obtain ⟨selected, hselected, hempty, hoccupied⟩ := hoccRecord
    have hframeW :
        ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
          ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
            ∃ selectedFrame : ReferenceActivePhysicalStep.Selection W[j].input,
              W[j].input.state.coordinator = .live registers owned beta ∧
              registers.payload = birthRegisters.payload ∧
              W[j].output.preparation.coordinator.selection = some selectedFrame ∧
              selectedFrame.view.payload = birthRegisters.payload ∧
              selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
      obtain ⟨_, hframes⟩ := hframes
      obtain ⟨registers, owned, selectedFrame, next, nextOwned, states, memories,
        hstate, hregisterPayload, hframeSelection, hframePayload, hframePending,
        _hnext, _hnextPayload, _hnextPending, _hordinary, _hoccupied,
        _hcleared, _hfollowing⟩ := hframes ⟨j, hj⟩
      exact ⟨registers, owned, selectedFrame, hstate, hregisterPayload,
        hframeSelection, hframePayload, hframePending⟩
    have hframeRecord :
        ∃ registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
          ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters registers,
            ∃ selectedFrame : ReferenceActivePhysicalStep.Selection (R[k.val].input),
              R[k.val].input.state.coordinator = .live registers owned beta ∧
              registers.payload = birthRegisters.payload ∧
              R[k.val].output.preparation.coordinator.selection = some selectedFrame ∧
              selectedFrame.view.payload = birthRegisters.payload ∧
              selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
      exact hrecordW ▸ hframeW
    obtain ⟨registers, owned, selectedFrame, hstate, hregisterPayload,
      hframeSelection, hframePayload, hframePending⟩ := hframeRecord
    have hselectedEq : selectedFrame = selected :=
      Option.some.inj (hframeSelection.symm.trans hselected)
    subst selectedFrame
    have hstrict : ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h < registers.payload.sigma.val := by
      rw [hregisterPayload]
      exact hlaterBirth
    have hcalendar :=
      ReferenceCompleteLaterLiveCalendarService.complete_later_live_calendar_service
        (rate := rate) rewards C_star C_h z k registers owned beta hstate
    rcases hcalendar with ⟨hpreparedCoordinator, hdispatchBranches⟩
    have hcontinueW :=
      ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
        rewards C_star C_h z ⟨b.val + 1, hbPlus⟩ j hj
    have hcontinue :
        ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest R[k.val] = true := by
      exact hrecordW ▸ hcontinueW
    unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hcontinue
    rw [R[k.val].output_eq] at hcontinue
    simp only [ReferenceActivePhysicalStep.step] at hcontinue
    rw [hpreparedCoordinator] at hcontinue
    let current := ReferenceActivePhysicalStep.liveInput R[k.val].input registers owned beta
    cases hdispatch : CoordinatorRoundDispatch.dispatchLive current with
    | continuingChosen dispatched hstartEq continuation armSelection =>
        have hdispatchExpanded := hdispatch
        dsimp only [current] at hdispatchExpanded
        rw [hdispatchExpanded] at hcontinue
        have hbranch := hdispatchBranches
        dsimp only [current] at hbranch
        rw [hdispatchExpanded] at hbranch
        obtain ⟨chosen, hchosenPreparation, _hchosenPayload, _hchosenCutoff,
          _hchosenStarted, _hchosenArm, hlive, hchosenOutput, _⟩ :=
          hbranch hstrict
        have hchosenEq : chosen = selected :=
          Option.some.inj (hchosenOutput.symm.trans hselected)
        subst chosen
        have hliveSelected :
            CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
              selected.view.cutoff R[k.val].input.time := hlive
        have hvalid :=
          ReferenceLaterLiveNumericalReadout.selection_choiceValid selected
        obtain ⟨states, memories, hordinaryActual, hoccupiedDown,
          hinputFields, houtputFields⟩ :=
          ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
            (rate := rate) rewards C_star C_h z k selected hselected
        have hordinaryPrepared : ∀ follower,
            ((ReferenceActivePhysicalStep.prepare R[k.val].input).followers.followers
              follower).configuration = .ordinary (states follower) (memories follower) := by
          intro follower
          have h := hordinaryActual follower
          change (R[k.val].output.preparation.followers.followers follower).configuration = _ at h
          rw [R[k.val].output_eq] at h
          simpa only [ReferenceActivePhysicalStep.step] using h
        have hfields : ∀ follower,
            (states follower).status ≠ .unoccupied ∧
              (states follower).lastDown = some (selected.view.payload.downRecord follower) := by
          intro follower
          have hnotUnoccupied := hoccupied follower (states follower) (memories follower)
            (hordinaryActual follower)
          exact ⟨hnotUnoccupied, hoccupiedDown follower hnotUnoccupied⟩
        have hselectionPrepared :
            (ReferenceActivePhysicalStep.prepare R[k.val].input).coordinator.selection =
              some selected := by
          simpa only [R[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
        let snapshot := ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states
        let input := ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput selected hvalid
        let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards
          R[k.val].input.time
        have hrowEq : ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
            R[k.val].input.rewards R[k.val].input.time = row := by
          simp only [hrewards, row]
        have hfastFacts :=
          ReferenceFirstLiveReleaseGeometry.actual_releaseRoundInput_fast_eq_selected
            selected hliveSelected hempty hvalid
        have hfast : input.fast = selected.arm := by
          simpa only [input, ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput]
            using hfastFacts.1
        have hfastOutside : selected.arm ∉ selected.view.payload.slowSet.val := by
          simpa only [input, ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput]
            using hfastFacts.2
        have hmissing : snapshot.missing = ∅ := by
          change selected.view.pendingAtChoice = ∅
          exact hempty
        have hordinaryPrepared' : ∀ follower,
            ((ReferenceActivePhysicalStep.prepare R[k.val].input).followers.followers
              follower).configuration = .ordinary (states follower) (memories follower) :=
          hordinaryPrepared
        have hactions :=
          ReferenceFirstLiveReleaseGeometry.prepared_actions_eq_projected selected
            hselectionPrepared states memories hordinaryPrepared' hfields input hmissing
            (by rfl) (by rfl) (by rfl) hfast
        have hobservations : ∀ player : Fin p.m,
            ((ReferenceActivePhysicalStep.prepare (R[k.val].input)).feedback.observations
              player).val.val = ActiveRoundActions.feedback p.two_le_m snapshot input row player := by
          intro player
          have h := ReferenceFirstLiveReleaseGeometry.prepared_observation_eq_projected
            selected snapshot input player hactions
          calc
            _ = ActiveRoundActions.feedback p.two_le_m snapshot input
                (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
                  R[k.val].input.rewards R[k.val].input.time) player := h
            _ = ActiveRoundActions.feedback p.two_le_m snapshot input row player := by
                  rw [hrowEq]
        have hregisterPayloadSelected : registers.payload = selected.view.payload :=
          hregisterPayload.trans hframePayload.symm
        have hregisterPending : registers.pendingAtChoice = ∅ :=
          hframePending.symm.trans hempty
        have hcost := physical_sentinel_bound rate R[k.val] registers owned beta selected
          states memories hstate hregisterPayloadSelected hregisterPending
          hempty hfields hordinaryPrepared hfast hactions
        rw [hrewards] at hcost
        refine ⟨j, hj, hrelIndex, k, rfl, selected, states, memories, input,
          hrecordW, hselected, hempty, hliveSelected, hvalid, hordinaryActual, hfields,
          hinputFields, houtputFields, rfl, hfast, hfastOutside, hactions,
          hobservations, hcost⟩

    | cutoffChosen dispatched startRoundEq ledger initializationEq ledgerEq
        initializationDomain cutoffClock cutoffPending noAssignment selection =>
        have hdispatchExpanded := hdispatch
        dsimp only [current] at hdispatchExpanded
        rw [hdispatchExpanded] at hcontinue
        simp at hcontinue
    | clockFailure failure dispatchEq =>
        have hdispatchExpanded := hdispatch
        dsimp only [current] at hdispatchExpanded
        rw [hdispatchExpanded] at hcontinue
        simp at hcontinue
    | initializerFailure dispatched startRoundEq checked checkedEq =>
        have hdispatchExpanded := hdispatch
        dsimp only [current] at hdispatchExpanded
        rw [hdispatchExpanded] at hcontinue
        simp at hcontinue
    | localFailure dispatched startRoundEq reason =>
        have hdispatchExpanded := hdispatch
        dsimp only [current] at hdispatchExpanded
        rw [hdispatchExpanded] at hcontinue
        simp at hcontinue
  · simp only [ite_eq_right hb]

private theorem completeRecord_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hcal : k.val < (ReferenceActivePhysicalHorizon.calendar
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)).length := by
    rw [← htimes, List.length_map]
    exact k.isLt
  have hget :
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).map (fun r => r.input.time.val))[k.val]'(by
          rw [List.length_map]
          exact k.isLt) =
        (ReferenceActivePhysicalHorizon.calendar
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h))[k.val]'hcal := by
    simp only [htimes]
  simpa only [List.getElem_map, ReferenceActivePhysicalHorizon.calendar,
    List.getElem_range', Nat.one_mul] using hget

private theorem actualRecord_lookup
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    ∃ k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val] = r ∧
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time = t := by
  by_cases hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val
  · have hlookup :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[t.val -
            ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? = some r := by
      simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs] using hr
    obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hlookup
    let k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length := ⟨t.val -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h, hk⟩
    have hrecord' :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val] = r := by
      simpa only [k] using hrecord
    have htime :
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val].input.time = t := by
      apply Fin.ext
      rw [completeRecord_time rate rewards C_star C_h z k]
      dsimp only [k]
      omega
    exact ⟨k, hrecord', htime⟩
  · simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hs] at hr

private theorem actualRecord_input_fields
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem roundInput_ext
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hs : x.state = y.state) (hr : x.rows = y.rows)
    (hi : x.selected = y.selected) (ht : x.time = y.time)
    (hw : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  cases hs
  cases hr
  cases hi
  cases ht
  cases hw
  rfl

private theorem actualRecord_replace_current
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (u : TimeControl p) :
    ∃ ru : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) = some ru ∧
      ru.input = ReferenceLaterOptionalControlResampling.withControl r.input u := by
  let zu := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u
  have hcode := ReferencePostReplacementCollectionReleaseResamplingData.incomingStateCode_replace_current
    rate rewards C_star C_h control0 t z u
  change ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t zu = _ at hcode
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hcode
  rw [hr, Option.map_some] at hcode
  cases hu : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t zu with
  | none => simp only [hu, Option.map_none, reduceCtorEq] at hcode
  | some ru =>
      rw [hu, Option.map_some] at hcode
      have hs := ReferenceActivePhysicalStepMeasurability.encodeState_injective
        (Option.some.inj hcode)
      obtain ⟨hrows, hindex, htime, hrewards⟩ :=
        actualRecord_input_fields rate rewards C_star C_h t z r hr
      obtain ⟨hrowsU, hindexU, htimeU, hrewardsU⟩ :=
        actualRecord_input_fields rate rewards C_star C_h t zu ru hu
      have hbase : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate r.input z =
          r.input := by
        apply roundInput_ext
        · rfl
        · exact hrows.symm
        · exact hindex.symm
        · rfl
        · rfl
      have hsource : ru.input =
          ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate r.input zu := by
        apply roundInput_ext
        · exact hs
        · exact hrowsU
        · exact hindexU
        · exact htimeU.trans htime.symm
        · exact hrewardsU.trans hrewards.symm
      refine ⟨ru, rfl, ?_⟩
      rw [hsource]
      dsimp only [zu]
      rw [← htime, ReferenceFixedTimeSourceControlCoupling.roundInputAtSource_replaceSourceControl,
        hbase]

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

private theorem preparedCoordinator_continuing
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      registers.priorClock registers.clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time) x.row)
    (arm : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).payload
      dispatched.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers x.time).complementWeights x.row)
    (hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live registers owned base
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput x registers owned base)))
    (hdispatch : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput x registers owned base) =
        .continuingChosen dispatched hstart continuation arm) :
    (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live registers owned base (.continuingChosen dispatched hstart continuation arm) := by
  rw [hdispatch] at hprepared
  exact hprepared

private theorem preparedFollower_from_actual
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ follower,
      (ReferenceFollowerFixedReply.actualChoice record follower).configuration =
        .ordinary (states follower) (memories follower)) :
    ∀ follower,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers
        follower).configuration = .ordinary (states follower) (memories follower) := by
  intro follower
  have h := hordinary follower
  change (record.output.preparation.followers.followers follower).configuration = _ at h
  rw [record.output_eq] at h
  simpa only [ReferenceActivePhysicalStep.step] using h

private theorem selected_cutoff_none_of_selectionAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hselection : ReferenceActivePhysicalStep.selectionAt x payload started time weights arm =
      some selected)
    (hcutoff : started.clock.u = none) : selected.view.cutoff = none := by
  classical
  unfold ReferenceActivePhysicalStep.selectionAt at hselection
  split at hselection
  · have hview := congrArg (fun s : ReferenceActivePhysicalStep.Selection x => s.view.cutoff)
      (Option.some.inj hselection)
    simpa [CoordinatorLiveChoiceRecorderStep.cutoffFromClock, hcutoff] using hview.symm
  · cases hselection

private theorem actualLaterLiveCutoffFrame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (j : ℕ)
    (hj : j < (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1)).length)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hk : k.val = b.val + 1 + j)
    (hrecordW : (ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
      rate rewards C_star C_h z (b.val + 1))[j]'hj =
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (selected : ReferenceActivePhysicalStep.Selection
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input)
    (hstate : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator = .live registers owned base)
    (hselected : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].output.preparation.coordinator.selection = some selected)
    (hstrict : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h < registers.payload.sigma.val)
    (hpriorCutoff : registers.priorClock.u = none) :
    ∃ dispatched : CoordinatorStartRoundCutoffDispatch.Output
          (ReferenceActivePhysicalStep.liveRegistersAt registers
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val].input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt registers owned
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val].input.time) base,
      ∃ hstart : CoordinatorPhaseClock.startRound p rate.eta.val
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.time
          registers.priorClock registers.clockPending = .ok dispatched.startResult,
      ∃ continuation : CoordinatorLiveChoiceRecorderStep.Continuation
          (ReferenceActivePhysicalStep.liveRegistersAt registers
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val].input.time)
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.row,
      ∃ arm : CoordinatorRoundDispatch.ArmSelection
          (ReferenceActivePhysicalStep.liveRegistersAt registers
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val].input.time).payload
          dispatched.startResult
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.time
          (ReferenceActivePhysicalStep.liveRegistersAt registers
            (ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val].input.time).complementWeights
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input.row,
        (ReferenceActivePhysicalStep.prepare
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val].input).coordinator =
            .live registers owned base (.continuingChosen dispatched hstart continuation arm) ∧
          selected.view.cutoff = none := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  have hbLeK : b.val + 1 ≤ k.val := by
    rw [hk]
    omega
  have hbPlus : b.val + 1 < R.length := Nat.lt_of_le_of_lt hbLeK k.isLt
  have hcontinueW := ReferenceCompleteLaterLiveComplementPrefixReplay.prefix_test
    (rate := rate) rewards C_star C_h z ⟨b.val + 1, hbPlus⟩ j hj
  have hcontinue :
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest R[k.val] = true :=
    hrecordW ▸ hcontinueW
  have hcalendar := ReferenceCompleteLaterLiveCalendarService.complete_later_live_calendar_service
    (rate := rate) rewards C_star C_h z k registers owned base hstate
  rcases hcalendar with ⟨hpreparedCoordinator, hdispatchBranches⟩
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest at hcontinue
  rw [R[k.val].output_eq] at hcontinue
  simp only [ReferenceActivePhysicalStep.step] at hcontinue
  let current := ReferenceActivePhysicalStep.liveInput R[k.val].input registers owned base
  rw [hpreparedCoordinator] at hcontinue
  cases hdispatch : CoordinatorRoundDispatch.dispatchLive current with
  | continuingChosen dispatched hstart continuation arm =>
      have hdispatchExpanded := hdispatch
      dsimp only [current] at hdispatchExpanded
      rw [hdispatchExpanded] at hcontinue
      have hbranch := hdispatchBranches
      dsimp only [current] at hbranch
      rw [hdispatchExpanded] at hbranch
      obtain ⟨chosen, _hchosenPreparation, _hchosenPayload, _hchosenCutoff,
        _hchosenStarted, _hchosenArm, _hlive, hchosenOutput, _⟩ := hbranch hstrict
      have hchosenEq : chosen = selected :=
        Option.some.inj (hchosenOutput.symm.trans hselected)
      subst chosen
      have hcoord := preparedCoordinator_continuing rate R[k.val].input registers owned base
        dispatched hstart continuation arm hpreparedCoordinator hdispatchExpanded
      have hselectedPrepared :
          (ReferenceActivePhysicalStep.prepare R[k.val].input).coordinator.selection =
            some selected := by
        have hselected' := hselected
        rw [R[k.val].output_eq] at hselected'
        simpa only [ReferenceActivePhysicalStep.step] using hselected'
      have hselectionAt :
          ReferenceActivePhysicalStep.selectionAt R[k.val].input registers.payload
            dispatched.startResult R[k.val].input.time
            (ReferenceActivePhysicalStep.liveRegistersAt registers R[k.val].input.time).complementWeights
            arm = some selected := by
        rw [hcoord] at hselectedPrepared
        simpa only [ReferenceActivePhysicalStep.DispatchCut.selection] using hselectedPrepared
      have hresult := live_dispatch_continuation_result dispatched continuation arm hstart hdispatch
      have hclock : dispatched.startResult.clock = registers.priorClock := by
        calc
          dispatched.startResult.clock = continuation.startRoundResult.clock :=
            congrArg CoordinatorPhaseClock.StartRoundResult.clock hresult.symm
          _ = registers.priorClock := continuation.clockFrame.1
      have hstartCutoff : dispatched.startResult.clock.u = none := by
        rw [hclock, hpriorCutoff]
      have hcutoff := selected_cutoff_none_of_selectionAt rate R[k.val].input registers.payload
        dispatched.startResult R[k.val].input.time
        (ReferenceActivePhysicalStep.liveRegistersAt registers R[k.val].input.time).complementWeights
        arm selected hselectionAt hstartCutoff
      exact ⟨dispatched, hstart, continuation, arm, hcoord, hcutoff⟩
  | cutoffChosen dispatched startRoundEq ledger initializationEq ledgerEq
      initializationDomain cutoffClock cutoffPending noAssignment selection =>
      have hdispatchExpanded := hdispatch
      dsimp only [current] at hdispatchExpanded
      rw [hdispatchExpanded] at hcontinue
      simp at hcontinue
  | clockFailure failure dispatchEq =>
      have hdispatchExpanded := hdispatch
      dsimp only [current] at hdispatchExpanded
      rw [hdispatchExpanded] at hcontinue
      simp at hcontinue
  | initializerFailure dispatched startRoundEq checked checkedEq =>
      have hdispatchExpanded := hdispatch
      dsimp only [current] at hdispatchExpanded
      rw [hdispatchExpanded] at hcontinue
      simp at hcontinue
  | localFailure dispatched startRoundEq reason =>
      have hdispatchExpanded := hdispatch
      dsimp only [current] at hdispatchExpanded
      rw [hdispatchExpanded] at hcontinue
      simp at hcontinue

/-- Actual arbitrary later-installation local release frame on the original
complete physical source. The selector is the literal later-chosen record and
the literal local gate at `t`; the signed deficit uses the all-player physical
feedback and the same record's retained whole reward table.

Sources: `05_binary_transport.tex:293-349` and `06_interruptions.tex:431,489-490`.
-/
theorem actual_later_local_release_physical_frame
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (_control0 : TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (t : Fin p.T)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z).map Prod.fst = some true) :
    ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.input.time = t ∧
      ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
        (base : Fin (p.m - 1) → ℕ)
        (selected : ReferenceActivePhysicalStep.Selection r.input)
        (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
        (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
        r.input.state.coordinator = .live registers owned base ∧
        registers.payload = selected.view.payload ∧
        registers.pendingAtChoice = ∅ ∧
        r.output.preparation.coordinator.selection = some selected ∧
        selected.view.pendingAtChoice = ∅ ∧
        selected.view.cutoff = none ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
          selected.view.cutoff r.input.time ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
          selected.view.cutoff r.input.time selected.view.complementWeights ∧
        (∀ follower,
          ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
            follower).configuration = .ordinary (states follower) (memories follower)) ∧
        (∀ follower, (states follower).status ≠ .unoccupied ∧
          (states follower).lastDown = some (selected.view.payload.downRecord follower)) ∧
        ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload r.input.state ∧
        ReferenceActiveDataOwnership.carriedOccupiedFields selected.view.payload r.output.next ∧
        (∀ a : Fin p.K,
          0 < ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
          selected.view.payload.anchor a ≤
            ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ∧
          ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected a ≤
            2 * selected.view.payload.anchor a) ∧
        let input := ReferenceFirstLiveReleaseGeometry.actualReleaseKernelInput selected
          (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
        input.fast = selected.arm ∧
        (ReferenceActivePhysicalStep.prepare r.input).arms.actions =
          ActiveRoundActions.actions p.two_le_m
            (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states) input ∧
        (∀ player : Fin p.m,
          ((ReferenceActivePhysicalStep.prepare r.input).feedback.observations
            player).val.val =
            ActiveRoundActions.feedback p.two_le_m
              (ReferenceFirstLiveReleaseGeometry.actualChoiceSnapshot selected states)
              input (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) player) ∧
        ReleaseRoundKernel.slowReward
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
            selected.view.payload.slowSet +
          (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val selected.arm -
          (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤
          (∑ follower ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
            ReleaseRoundKernel.chi
              (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned follower)) +
          (if selected.arm = selected.view.payload.assignment.auxiliary ∧
              (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
            (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
              selected.view.payload.assignment.auxiliary else 0) ∧
        let current := ReferenceActivePhysicalStep.liveInput r.input registers owned base
        ∃ dispatched : CoordinatorStartRoundCutoffDispatch.Output current.registers
            current.ownedRegisters current.followerBaseScore,
          ∃ hstart : CoordinatorPhaseClock.startRound p current.eta.val
              current.registers.time current.registers.priorClock current.registers.clockPending =
            .ok dispatched.startResult,
            ∃ continuation : CoordinatorLiveChoiceRecorderStep.Continuation
                current.registers current.row,
              ∃ arm : CoordinatorRoundDispatch.ArmSelection current.registers.payload
                  dispatched.startResult current.registers.time current.registers.complementWeights
                  current.row,
                (ReferenceActivePhysicalStep.prepare r.input).coordinator =
                  .live registers owned base
                    (.continuingChosen dispatched hstart continuation arm) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let W := ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
    rate rewards C_star C_h z (b.val + 1)
  let V := R[b.val] :: W
  let Rel := V.dropWhile ReferenceCompleteLaterInstallationChoiceHistory.missingAtChoice
  let birthIndex := s + b.val
  have hEntry :
      (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birthIndex t z).map
        Prod.fst = some true := by
    simpa only [birthIndex, s] using hg
  have hentryExpanded := hEntry
  unfold ReferenceSourcePrefixHistoryFiltration.entry
    ReferenceSourcePrefixHistoryFiltration.incoming at hentryExpanded
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp [hrecord] at hentryExpanded
  | some actual =>
      have hgate :
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birthIndex t
            (ReferenceActivePhysicalStepMeasurability.encodeState actual.input.state) = true := by
        simpa [hrecord, ReferenceRetainedReleasePhaseObservation.localReleaseEntry] using
          hentryExpanded
      obtain ⟨k0, hactualIndex, hactualTime⟩ :=
        actualRecord_lookup rate rewards C_star C_h t z actual hrecord
      have hgateAtIndex :
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birthIndex
            (R[k0.val].input.time)
            (ReferenceActivePhysicalStepMeasurability.encodeState R[k0.val].input.state) = true := by
        have hactualTime' : actual.input.time = t :=
          (congrArg (fun record => record.input.time) hactualIndex).symm.trans hactualTime
        rw [hactualIndex, hactualTime']
        exact hgate
      have hfilter := ReferencePostReplacementCollectionReleaseSupport.later_release_filter_eq
        rate rewards C_star C_h z b hb
      change R.filter (fun record =>
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birthIndex
            record.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state)) = Rel at hfilter
      have hindexMember : R[k0.val] ∈ R.filter (fun record =>
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birthIndex
            record.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state)) :=
        List.mem_filter.mpr ⟨List.getElem_mem k0.isLt, hgateAtIndex⟩
      have hmember : actual ∈ R.filter (fun record =>
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birthIndex
            record.input.time
            (ReferenceActivePhysicalStepMeasurability.encodeState record.input.state)) := by
        rw [← hactualIndex]
        exact hindexMember
      rw [hfilter] at hmember
      obtain ⟨i, hi, hactualRel⟩ := List.mem_iff_getElem.mp hmember
      have hprojection := arbitraryLaterInstallationReleaseProjection
        rate rewards C_star C_h z b
      rw [ite_eq_left hb] at hprojection
      obtain ⟨j, hj, hrelW, k, hk, selected, states, memories, input,
        hrecordW, hselected, hempty, hliveSelected, hvalid, hordinaryActual, hfields,
        hinputFields, houtputFields, hinput, hfast, hfastOutside, hactions,
        hobservations, hcost⟩ := hprojection i hi
      have hactualRecordEq : actual = R[k.val] :=
        hactualRel.symm.trans (hrelW.trans hrecordW)
      have hactualCurrent :
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
            some R[k.val] := by
        rw [hactualRecordEq] at hrecord
        exact hrecord
      have htimeCurrent : R[k.val].input.time = t := by
        have hindices : R[k0.val] = R[k.val] := hactualIndex.trans hactualRecordEq
        rw [← hindices]
        exact hactualTime
      have hhistory := ReferenceCompleteLaterInstallationChoiceHistory.actual_later_installation_choice_history
        rate rewards C_star C_h z b
      rw [ite_eq_left hb] at hhistory
      rcases hhistory with
        ⟨birthRegisters, birthOwned, beta, birthSelected, _hnext, _hbirth,
          hlaterBirth, _hbSelection, _hbPayload, _hbPending, _hbNoEvent,
          _hbFollowers, _hcontinued, _hnoRelease, hframes⟩
      obtain ⟨_, hframes⟩ := hframes
      have hframeW :
          ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
            (selectedFrame : ReferenceActivePhysicalStep.Selection W[j].input),
            W[j].input.state.coordinator = .live registers owned beta ∧
            registers.payload = birthRegisters.payload ∧
            W[j].output.preparation.coordinator.selection = some selectedFrame ∧
            selectedFrame.view.payload = birthRegisters.payload ∧
            selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
        obtain ⟨registers, owned, selectedFrame, _next, _nextOwned, _states, _memories,
          hstateW, hregisterPayload, hframeSelection, hframePayload, hframePending,
          _houtput, _hnextPayload, _hnextPending, _hordinary, _hoccupied,
          _hcleared, _hfollowing⟩ := hframes ⟨j, hj⟩
        exact ⟨registers, owned, selectedFrame, hstateW, hregisterPayload,
          hframeSelection, hframePayload, hframePending⟩
      have hframeRecord :
          ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
            (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
            (selectedFrame : ReferenceActivePhysicalStep.Selection R[k.val].input),
            R[k.val].input.state.coordinator = .live registers owned beta ∧
            registers.payload = birthRegisters.payload ∧
            R[k.val].output.preparation.coordinator.selection = some selectedFrame ∧
            selectedFrame.view.payload = birthRegisters.payload ∧
            selectedFrame.view.pendingAtChoice = registers.pendingAtChoice := by
        exact hrecordW ▸ hframeW
      obtain ⟨registers, owned, selectedFrame, hstateW, hregisterPayload,
        hframeSelection, hframePayload, hframePending⟩ := hframeRecord
      have hframeSelectionAtRecord :
          R[k.val].output.preparation.coordinator.selection = some selectedFrame :=
        hframeSelection
      have hselectedEq : selectedFrame = selected :=
        Option.some.inj (hframeSelectionAtRecord.symm.trans hselected)
      subst selectedFrame
      have hstate : R[k.val].input.state.coordinator = .live registers owned beta :=
        hrecordW ▸ hstateW
      have hregisterPayloadSelected : registers.payload = selected.view.payload :=
        hregisterPayload.trans hframePayload.symm
      have hregisterPending : registers.pendingAtChoice = ∅ :=
        hframePending.symm.trans hempty
      have hstrict : s < registers.payload.sigma.val := by
        rw [hregisterPayload]
        exact hlaterBirth
      have hgateAtRecord :
          ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birthIndex t
            (ReferenceActivePhysicalStepMeasurability.encodeState R[k.val].input.state) = true := by
        rw [← hactualRecordEq]
        exact hgate
      obtain ⟨gateRegisters, gateOwned, gateBase, hgateState, _hgateStamp,
        _hgatePending, _hgateSigma, hgateCutoff⟩ :=
        ReferenceLocalReleaseGateChronology.gate_live birthIndex t
          R[k.val].input.state hgateAtRecord
      have hregistersEq : gateRegisters = registers :=
        (CoordinatorConfiguration.live.inj (hgateState.symm.trans hstate)).1
      have hpriorCutoff : registers.priorClock.u = none := by
        rw [← hregistersEq]
        exact hgateCutoff
      obtain ⟨dispatched, hstart, continuation, arm, hcoord, hcutoff⟩ :=
        actualLaterLiveCutoffFrame rate rewards C_star C_h z b j hj k hk hrecordW
          registers owned beta selected hstate hselected
          (by rw [hregisterPayload]; exact hlaterBirth) hpriorCutoff
      have hordinaryPrepared :=
        preparedFollower_from_actual rate R[k.val] states memories hordinaryActual
      have hweights := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected)
      have hobservations' := hobservations
      rw [hinput, htimeCurrent] at hobservations'
      have hfast' := hfast
      rw [hinput] at hfast'
      have hactions' := hactions
      rw [hinput] at hactions'
      have hcost' := hcost
      rw [htimeCurrent] at hcost'
      refine ⟨R[k.val], hrecord.symm.trans hactualCurrent, htimeCurrent,
        registers, owned, beta, selected, states, memories,
        hstate, hregisterPayloadSelected, hregisterPending,
        hselected, hempty, hcutoff, hliveSelected, hvalid,
        hordinaryPrepared, hfields, hinputFields, houtputFields,
        ?_, hfast', hactions', hobservations', hcost', ?_⟩
      · intro a
        exact hweights a
      · exact ⟨dispatched, hstart, continuation, arm, hcoord⟩

/-- Every whole current-control replacement is an actual record on the same
original source with that one coordinate replaced. The incoming banks, queues,
registers and follower memories are retained; fresh physical arms may vary.
The empty-pending consequence retains the signed charge on the supported date. -/
theorem actual_later_local_release_physical_frame_all_controls
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (t : Fin p.T)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
      t z).map Prod.fst = some true) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input)
      (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      ∀ u : TimeControl p,
        ∃ (ru : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
          (vu : ReferenceActivePhysicalStep.Selection ru.input),
          ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) = some ru ∧
          ru.input = ReferenceLaterOptionalControlResampling.withControl r.input u ∧
          ru.input.state = r.input.state ∧ ru.input.time = t ∧
          ru.output.preparation.coordinator.selection = some vu ∧
          vu.view = selected.view ∧
          completeCurrentWeights vu = completeCurrentWeights selected ∧
          vu.view.pendingAtChoice = ∅ ∧ vu.view.cutoff = none ∧
          CoordinatorLocalArmChoice.assignmentIsLive vu.view.payload vu.view.cutoff ru.input.time ∧
          (∀ i, ((ReferenceActivePhysicalStep.prepare ru.input).followers.followers i).configuration =
            .ordinary (states i) (memories i)) ∧
          (∀ i, (states i).status ≠ .unoccupied ∧
            (states i).lastDown = some (vu.view.payload.downRecord i)) ∧
          ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru =
            ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r ∧
          let input := actualReleaseKernelInput vu
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid vu)
          input.fast = vu.arm ∧
          (ReferenceActivePhysicalStep.prepare ru.input).arms.actions =
            ActiveRoundActions.actions p.two_le_m (actualChoiceSnapshot vu states) input ∧
          (∀ player : Fin p.m,
            ((ReferenceActivePhysicalStep.prepare ru.input).feedback.observations player).val.val =
              ActiveRoundActions.feedback p.two_le_m (actualChoiceSnapshot vu states)
                input (wholeGridRewardRow rewards t) player) ∧
          (∀ player : Fin p.m, ((ru.ownEntries player).2).val.val =
            ActiveRoundActions.feedback p.two_le_m (actualChoiceSnapshot vu states)
              input (wholeGridRewardRow rewards t) player) ∧
          slowReward (wholeGridRewardRow rewards t) vu.view.payload.slowSet +
              (wholeGridRewardRow rewards t).val vu.arm -
              (∑ player : Fin p.m, ((ru.ownEntries player).2).val.val) ≤
            (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru,
              chi (wholeGridRewardRow rewards t) (vu.view.payload.assignment.assigned i)) +
            (if vu.arm = vu.view.payload.assignment.auxiliary ∧
                (ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru).Nonempty then
              (wholeGridRewardRow rewards t).val vu.view.payload.assignment.auxiliary else 0) ∧
          (ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru = ∅ →
            slowReward (wholeGridRewardRow rewards t) vu.view.payload.slowSet +
                (wholeGridRewardRow rewards t).val vu.arm -
                (∑ player : Fin p.m, ((ru.ownEntries player).2).val.val) ≤ 0) := by
  classical
  obtain ⟨r, hr, ht, registers, owned, base, selected, states, memories,
    hstate, hpayload, hpending, hselection, hempty, hcutoff, hlive, _hvalid,
    hordinary, hfields, _hcarried, _hnextCarried, _hweights,
    _hfast, _hactions, _hfeedback, _hcost, dispatched, hstart, continuation, arm, hcoord⟩ :=
    actual_later_local_release_physical_frame rate rewards C_star C_h control0 z b t hb hg
  have hprepared : (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection =
      some selected := by
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step] using hselection
  have hcanonical := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
    r.input registers owned base dispatched hstart continuation arm hcoord
  have hselectedEq := Option.some.inj (hcanonical.symm.trans hprepared)
  refine ⟨r, selected, states, memories, hr, hselection, ?_⟩
  intro u
  obtain ⟨ru, hru, hinput⟩ :=
    actualRecord_replace_current rate rewards C_star C_h control0 t z r hr u
  let x := ReferenceLaterOptionalControlResampling.withControl r.input u
  obtain ⟨cu, au, hcoordU⟩ :=
    ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
      r.input registers owned base dispatched hstart continuation arm hcoord u
  let vu := ReferenceContinuingLiveSlicePreparation.continuingSelection
    x registers owned base dispatched hstart cu au
  have hview : vu.view = selected.view := by
    have hv := congrArg (fun v : ReferenceActivePhysicalStep.Selection r.input => v.view)
      hselectedEq
    exact hv
  have hselectionU := ReferenceContinuingLiveSlicePreparation.continuingSelection_eq_actual
    x registers owned base dispatched hstart cu au hcoordU
  have hordinaryU := ReferenceFirstLiveOccupiedPreparationControl.occupied_prepare_at_all_controls
    r.input selected.view.payload states memories hordinary hfields u
  have hframe : ∃ v : ReferenceActivePhysicalStep.Selection x,
      (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some v ∧
      v.view = selected.view ∧
      ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
        .ordinary (states i) (memories i) :=
    ⟨vu, hselectionU, hview, hordinaryU⟩
  change ru.input = x at hinput
  rw [← hinput] at hframe
  obtain ⟨v, hselectedU, hviewU, hordinaryU⟩ := hframe
  have hfieldsU : ∀ i, (states i).status ≠ .unoccupied ∧
      (states i).lastDown = some (v.view.payload.downRecord i) := by
    rw [hviewU]
    exact hfields
  have hemptyU : v.view.pendingAtChoice = ∅ := by rw [hviewU]; exact hempty
  have hcutoffU : v.view.cutoff = none := by rw [hviewU]; exact hcutoff
  have htimeU : ru.input.time = t := by rw [hinput]; exact ht
  have hrewardsU : ru.input.rewards = rewards :=
    (actualRecord_input_fields rate rewards C_star C_h t _ ru hru).2.2.2
  have hliveU : CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
      ru.input.time := by
    rw [hviewU, hinput]
    exact hlive
  have hstateU : ru.input.state.coordinator = .live registers owned base := by
    rw [hinput]
    exact hstate
  have hpayloadU : registers.payload = v.view.payload := by rw [hviewU]; exact hpayload
  have hfastU := (actual_releaseRoundInput_fast_eq_selected v hliveU hemptyU
    (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)).1
  let input := actualReleaseKernelInput v
    (ReferenceLaterLiveNumericalReadout.selection_choiceValid v)
  have hactionsU := prepared_actions_eq_projected v hselectedU states memories
    hordinaryU hfieldsU input hemptyU rfl rfl rfl hfastU
  have hfeedbackU (player : Fin p.m) :=
    prepared_observation_eq_projected v (actualChoiceSnapshot v states) input player hactionsU
  have hcostU := physical_sentinel_bound rate ru registers owned base v states memories
    hstateU hpayloadU hpending hemptyU hfieldsU hordinaryU hfastU hactionsU
  have hrowU : wholeGridRewardRow ru.input.rewards ru.input.time =
      wholeGridRewardRow rewards t := by rw [hrewardsU, htimeU]
  rw [hrowU] at hfeedbackU hcostU
  have hownFeedbackU (player : Fin p.m) :
      ((ru.ownEntries player).2).val.val =
        ActiveRoundActions.feedback p.two_le_m (actualChoiceSnapshot v states)
          input (wholeGridRewardRow rewards t) player := by
    have hown : ((ru.ownEntries player).2).val.val =
        ((ReferenceActivePhysicalStep.prepare ru.input).feedback.observations player).val.val := by
      rw [ReferenceActivePhysicalHorizon.RoundRecord.ownEntries_formula ru player]
      simp only [ReferenceActivePhysicalHorizon.RoundRecord.actions, ru.output_eq]
      rfl
    exact hown.trans (hfeedbackU player)
  have hweightsU : completeCurrentWeights v = completeCurrentWeights selected := by
    exact congrArg (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      fun a => if ha : a ∈ view.payload.slowSet.val then view.payload.anchor a
        else view.complementWeights
          ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩) hviewU
  have hpendingU : ReferencePhysicalReleaseQuota.pendingSet v.view.payload ru =
      ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r := by
    unfold ReferencePhysicalReleaseQuota.pendingSet
    rw [hviewU, hinput]
    rfl
  have hselectedOutput : ru.output.preparation.coordinator.selection = some v := by
    simpa only [ru.output_eq, ReferenceActivePhysicalStep.step] using hselectedU
  refine ⟨ru, v, hru, hinput, ?_, htimeU, hselectedOutput, hviewU, hweightsU,
    hemptyU, hcutoffU, hliveU, hordinaryU, hfieldsU, hpendingU,
    hfastU, hactionsU, hfeedbackU, hownFeedbackU, hcostU, ?_⟩
  · rw [hinput]
    rfl
  · intro hnone
    simp only [hnone, Finset.sum_empty, Finset.not_nonempty_empty,
      and_false, ↓reduceIte, zero_add] at hcostU
    exact hcostU

end Bandits.Support.ReferenceOriginalInstallationReleasePhysicalFrame

end
