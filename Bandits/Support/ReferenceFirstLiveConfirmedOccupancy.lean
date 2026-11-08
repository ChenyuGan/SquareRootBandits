/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferencePhysicalReleaseQuota

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual first-live confirmed-follower occupancy

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-318`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-295`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

These internal results retain the original physical run and its first actual
chosen-cutoff window. They expose F's actual ordinary choice outputs together
with K's current-payload field and no-release facts, and derive the selected
follower's occupied state at an actual positive DOWN confirmation. They assert
no release probability, service law, or manuscript closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveConfirmedOccupancy

open ConstructorDimensions
open ReferenceActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)

/-- The C/K local implication used at an actual positive DOWN confirmation.
K derives the no-released fact from the carried first-live state and literal
no-cutoff selector. The ordinary choice and selection are the actual prepared
branch; no replacement snapshot or status vector is used. -/
theorem actual_first_live_selected_confirmation_choice_pending
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : ReferenceFirstLiveConfirmationHistory.FirstLiveState x.state)
    (hnocut : ReferenceCollectionPhaseHistory.cutoffChosen x = false)
    (selected : Selection x)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selected)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : ((ReferenceActivePhysicalStep.prepare x).followers.followers
      (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (x.row.2 x.time).1)).configuration = .ordinary choice choiceMemory)
    (hevent : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff x.time (x.row.2 x.time)
      (ReferenceActivePhysicalStep.prepare x).coordinatorObservation) :
    choice.status = .pending := by
  have hfields := ReferenceFirstLiveConfirmationHistory.selected_choice x hstate hnocut
    selected hselected (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (x.row.2 x.time).1) choice choiceMemory hchoice
  have hoccupied := ReferenceActiveConfirmationRelease.downConfirmationEvent_implies_occupied
    (ReferenceActivePhysicalStep.prepare x) selected hselected choice choiceMemory hchoice hevent
  have hnotReleased := hfields.2 hevent.2.1
  rcases hoccupied with hpending | hreleased
  · exact hpending
  · exact False.elim (hnotReleased hreleased)

/-- On each actual selected first-live record, F supplies every ordinary
follower choice and successful follower finish. K supplies the selected
payload's occupied-field identity and its no-released-while-missing fact.
The selector premise is the actual PREPARE option branch of this same record.
This is not yet an all-player occupancy assertion when the pending set is
empty. -/
theorem run_first_live_actual_choice_fields
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
      ∀ i : Fin (p.m - 1),
        ∃ choice choiceMemory next nextMemory,
          (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary choice choiceMemory ∧
          (W[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
          (W[k.val].output.followers i).failure = none ∧
          (choice.status ≠ .unoccupied →
            choice.lastDown = some (selected.view.payload.downRecord i)) ∧
          (selected.view.pendingAtChoice.Nonempty → choice.status ≠ .released) := by
  intro E W k selected hselected
  intro i
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  obtain ⟨_, hchoices⟩ := hsafe
  obtain ⟨choice, choiceMemory, next, nextMemory, hchoice, hnext, hfailure, _⟩ :=
    hchoices k i
  have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro j s mem hs
    rw [hseed j] at hs
    cases hs
    exact ⟨hunoccupied j, hnone j⟩
  have hselected' : (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection =
      some selected := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
  have hchoiceW : (W[k.val].output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory := by
    change (W[k.val].output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory at hchoice
    exact hchoice
  have hchoice' :
      ((ReferenceActivePhysicalStep.prepare W[k.val].input).followers.followers i).configuration =
        .ordinary choice choiceMemory := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hchoiceW
  have hfields := ReferenceFirstLiveConfirmationHistory.run_firstLive_no_released
    initial rows J rewards start count hspan active hfirst hinitial k selected hselected'
    i choice choiceMemory hchoice'
  exact ⟨choice, choiceMemory, next, nextMemory, hchoice, hnext, hfailure,
    hfields.1, hfields.2⟩

/-- An actual singleton pre-choice missing set and positive DOWN confirmation
commit the actual same-payload coordinator registers with precisely that
follower erased. -/
theorem run_first_live_singleton_confirmation_erases_pending
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
      ∀ (next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (owned : CoordinatorLiveServiceFinish.OwnedRegisters next)
        (base : Fin (p.m - 1) → ℕ),
        W[k.val].output.next.coordinator = .live next owned base →
        selected.view.pendingAtChoice =
          {PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (W[k.val].input.row.2 W[k.val].input.time).1} →
        CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
          selected.view.pendingAtChoice selected.view.cutoff W[k.val].input.time
          (W[k.val].input.row.2 W[k.val].input.time)
          W[k.val].output.preparation.coordinatorObservation →
        next.payload = selected.view.payload ∧
          next.pendingAtChoice = selected.view.pendingAtChoice.erase
            (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (W[k.val].input.row.2 W[k.val].input.time).1) := by
  intro E W k selected hselected next owned base hout hsingle hevent
  have hinitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
    intro j s mem hs
    rw [hseed j] at hs
    cases hs
    exact ⟨hunoccupied j, hnone j⟩
  have hselected' :
      (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection =
        some selected := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
  have hevent' : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff W[k.val].input.time
      (W[k.val].input.row.2 W[k.val].input.time)
      (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinatorObservation := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hevent
  have hseedNext := ReferencePhysicalReleaseQuota.run_firstLive_release_seed
    initial rows J rewards start count hspan active hfirst hinitial k selected hselected'
    hsingle hevent' next owned base hout
  refine ⟨hseedNext.1, ?_⟩
  rw [hseedNext.2, hsingle]
  simp

section ActualLaunch

variable {p : Parameters}
variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (actualRate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p actualRate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p actualRate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h actualRate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h actualRate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h actualRate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h actualRate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h actualRate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p actualRate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p actualRate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)

abbrev LaunchSelection := ReferenceActivePhysicalStep.Selection
  (p := p) (rate := actualRate)

/-- Actual-launched specialization of the actual ordinary-choice and
current-payload field result. The complete source/replay/launch telescope is
retained, including the original rows, selected private row, rewards and
prelaunch selectors. -/
theorem actual_launched_first_live_choice_fields (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards
      actualRate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := fun i =>
      ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards actualRate C_star C_h b h actual past hr hdown hclean hforce launch
        learnerSeed hlaunched i
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : LaunchSelection actualRate W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      ∀ i : Fin (p.m - 1),
        ∃ choice choiceMemory next nextMemory,
          (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary choice choiceMemory ∧
          (W[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
          (W[k.val].output.followers i).failure = none ∧
          (choice.status ≠ .unoccupied →
            choice.lastDown = some (selected.view.payload.downRecord i)) ∧
          (selected.view.pendingAtChoice.Nonempty → choice.status ≠ .released) := by
  intro initial start active E W k selected hselected i
  have hsafety := ReferenceFirstLiveFollowerSafety.actual_launched_first_live_follower_safety
    source rewards actualRate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched count hspan
  obtain ⟨_, hchoices⟩ := hsafety
  obtain ⟨choice, choiceMemory, next, nextMemory, hchoice, hnext, hfailure, _⟩ :=
    hchoices k i
  have hselected' : (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection =
      some selected := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
  have hchoiceW : (W[k.val].output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory := by
    change (W[k.val].output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory at hchoice
    exact hchoice
  have hchoice' :
      ((ReferenceActivePhysicalStep.prepare W[k.val].input).followers.followers i).configuration =
        .ordinary choice choiceMemory := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hchoiceW
  have hfields := ReferenceFirstLiveConfirmationHistory.ofActualLaunchedBoundary_firstLive_no_released
    source rewards actualRate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched count hspan k selected hselected' i choice choiceMemory hchoice'
  exact ⟨choice, choiceMemory, next, nextMemory, hchoiceW, hnext, hfailure,
    hfields.1, hfields.2⟩

end ActualLaunch

end Bandits.Support.ReferenceFirstLiveConfirmedOccupancy

end
