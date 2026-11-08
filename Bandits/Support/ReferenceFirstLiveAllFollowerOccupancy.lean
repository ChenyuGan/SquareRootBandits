/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveMissingSetProvenance
public import Bandits.Support.ReferenceFirstLiveOccupiedPersistence
public import Bandits.Support.ReferenceGeneratedActivePrefixFactor

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual all-follower occupancy on the first-live window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-318`,
`sources/zip4/manuscript/06_interruptions.tex:246-295`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The actual coordinator missing-set provenance and the conditional actual
occupied-follower persistence are assembled over one unchanged physical run.
The exports concern prepared choices and whole DOWN payloads only. A singleton
confirmation has every follower pending at its choice, while the next
coordinator register has the confirmed follower erased. No release service,
probability, cost, stopped-support, or regret assertion is established here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveAllFollowerOccupancy

open ConstructorDimensions
open ReferenceActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)

private theorem initialFollowers_of_seed
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied) :
    ReferenceFirstLiveConfirmationHistory.InitialFollowers initial := by
  intro i state stateMemory hstate
  have heq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary (seed i) (memory i) =
      .ordinary state stateMemory := (hseed i).symm.trans hstate
  injection heq with hstate' hmemory'
  subst state
  subst stateMemory
  exact ⟨hunoccupied i, hnone i⟩

/-- A current actual choice outside the coordinator's actual missing set is
occupied, and its accepted DOWN record is the corresponding field of the
same selected whole payload. The full seed and memory telescope is retained:
in particular inherited buffers and DOWN batches are not replaced by empty
ones. -/
theorem run_first_live_all_follower_occupancy
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
      ∀ i : Fin (p.m - 1), i ∉ selected.view.pendingAtChoice →
        ∃ choice choiceMemory next nextMemory,
          (W[k.val].output.preparation.followers.followers i).configuration =
            .ordinary choice choiceMemory ∧
          (W[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
          (W[k.val].output.followers i).failure = none ∧
          choice.status ≠ .unoccupied ∧
          choice.lastDown = some (selected.view.payload.downRecord i) := by
  intro E W k selected hselected i hi
  by_cases hlen : W.length = 0
  · exact Fin.elim0 (hlen ▸ k)
  have hprovenance := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    initial rows J rewards start count hspan active hfirst
  obtain hzero | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hframes⟩ := hprovenance
  · exact False.elim (hlen hzero)
  · obtain ⟨record, hrecord, currentSelected, hcurrentActual, _, _, _, _, _, _, _, _,
        hcoverage⟩ := hframes k
    subst record
    have hselectedEq : currentSelected = selected :=
      Option.some.inj (hcurrentActual.symm.trans hselected)
    subst currentSelected
    obtain ⟨ell, hell, priorRecord, hpriorRecord, priorSelected,
      hpriorSelected, hpayload, hevent, hdraw⟩ := hcoverage i hi
    subst priorRecord
    have hellW : ell < W.length := lt_trans hell k.isLt
    have hpriorActual : W[ell].output.preparation.coordinator.selection = some priorSelected := by
      exact hpriorSelected
    have hpriorEvent :
        ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent
          W[ell] priorSelected := by
      exact hevent
    have hseedInitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial :=
      initialFollowers_of_seed initial seed memory hseed hnone hunoccupied
    have hpriorState :
        ReferenceFirstLiveConfirmationHistory.FirstLiveState W[ell].input.state :=
      ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
        initial rows J rewards start count hspan active hfirst hseedInitial ⟨ell, hellW⟩
    have hpriorNoCut :
        ReferenceCollectionPhaseHistory.cutoffChosen W[ell].input = false := by
      have hmem : W[ell] ∈ W := List.getElem_mem hellW
      have htake := List.mem_takeWhile_imp hmem
      simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
        Bool.not_eq_true'] using htake
    have hpriorActualPrepared :
        (ReferenceActivePhysicalStep.prepare W[ell].input).coordinator.selection =
          some priorSelected := by
      simpa only [W[ell].output_eq, ReferenceActivePhysicalStep.step] using hpriorActual
    obtain ⟨choicePrior, memoryPrior, nextPrior, nextMemoryPrior,
        hchoicePrior, houtputPrior, hfailurePrior, hfieldsPrior⟩ :=
      ReferenceFirstLiveConfirmedOccupancy.run_first_live_actual_choice_fields
        initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
        hbacklog hnone hunoccupied hvalid hpair htime hbatch ⟨ell, hellW⟩ priorSelected
        hpriorActual i
    have hpriorChoiceActual :
        ((ReferenceActivePhysicalStep.prepare W[ell].input).followers.followers i).configuration =
          .ordinary choicePrior memoryPrior := by
      have hchoicePrior' := hchoicePrior
      rw [W[ell].output_eq] at hchoicePrior'
      exact hchoicePrior'
    let focal := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (W[ell].input.row.2 W[ell].input.time).1
    have hfocalEq : focal = i := hdraw
    have hfocalChoice :
        ((ReferenceActivePhysicalStep.prepare W[ell].input).followers.followers focal).configuration =
          .ordinary choicePrior memoryPrior := by
      rw [hfocalEq]
      exact hpriorChoiceActual
    have hpriorEvent' : CoordinatorLocalArmChoice.downConfirmationEvent
        priorSelected.view.payload priorSelected.view.pendingAtChoice priorSelected.view.cutoff
        W[ell].input.time (W[ell].input.row.2 W[ell].input.time)
        (ReferenceActivePhysicalStep.prepare W[ell].input).coordinatorObservation := by
      simpa only [ReferenceFirstLiveMissingSetProvenance.actualDownConfirmationEvent,
        W[ell].output_eq, ReferenceActivePhysicalStep.step] using hpriorEvent
    have hpendingPrior :=
      ReferenceFirstLiveConfirmedOccupancy.actual_first_live_selected_confirmation_choice_pending
        W[ell].input hpriorState hpriorNoCut priorSelected hpriorActualPrepared choicePrior memoryPrior
        hfocalChoice hpriorEvent'
    have hpendingPriorI : choicePrior.status = .pending := by
      simpa only [focal, hfocalEq] using hpendingPrior
    have hpersist :=
      ReferenceFirstLiveOccupiedPersistence.run_first_live_occupied_follower_persistence
        initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
        hbacklog hnone hunoccupied hvalid hpair htime hbatch ⟨ell, hellW⟩ priorSelected
        hpriorActual i choicePrior memoryPrior hchoicePrior (by
          rw [hpendingPriorI]
          decide)
    obtain ⟨choiceNow, memoryNow, nextNow, nextMemoryNow, incomingNow, incomingMemoryNow,
        hchoiceNow, houtputNow, hfailureNow, hinputNow, hlocalNow, hincomingOccupied,
        hlastIncoming, hsigma, htoken, hstart, hchoiceEq, hmemoryEq, hchoiceOccupied,
        hnextOccupied, hchoiceLast, hnextLast, _hselectedPayload⟩ :=
      hpersist k (Nat.le_of_lt hell)
    have hlastCurrent : choiceNow.lastDown = some (selected.view.payload.downRecord i) := by
      have hrecordEq : priorSelected.view.payload.downRecord i = selected.view.payload.downRecord i :=
        congrArg (fun payload => payload.downRecord i) hpayload
      calc
        choiceNow.lastDown = some (priorSelected.view.payload.downRecord i) := hchoiceLast
        _ = some (selected.view.payload.downRecord i) := congrArg some hrecordEq
    exact ⟨choiceNow, memoryNow, nextNow, nextMemoryNow, hchoiceNow, houtputNow,
      hfailureNow, hchoiceOccupied, hlastCurrent⟩

/-- On an actual positive singleton confirmation, every actual follower choice
is pending and carries the current whole DOWN payload. The actual next
coordinator registers have the same payload and an empty missing set. The
released update may still change a pending follower after this choice. -/
theorem run_first_live_singleton_confirmation_all_pending
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
      let focal := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (W[k.val].input.row.2 W[k.val].input.time).1
      selected.view.pendingAtChoice = {focal} →
      CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff W[k.val].input.time
        (W[k.val].input.row.2 W[k.val].input.time)
        W[k.val].output.preparation.coordinatorObservation →
      ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
        ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
          ∃ base : Fin (p.m - 1) → ℕ,
            W[k.val].output.next.coordinator = .live next owned base ∧
            next.payload = selected.view.payload ∧ next.pendingAtChoice = ∅ ∧
            ∀ i : Fin (p.m - 1),
              ∃ choice choiceMemory nextFollower nextFollowerMemory,
                (W[k.val].output.preparation.followers.followers i).configuration =
                  .ordinary choice choiceMemory ∧
                (W[k.val].output.followers i).configuration =
                  .ordinary nextFollower nextFollowerMemory ∧
                (W[k.val].output.followers i).failure = none ∧
                choice.status = .pending ∧
                choice.lastDown = some (selected.view.payload.downRecord i) := by
  intro E W k selected hselected focal hsingleton hevent
  by_cases hlen : W.length = 0
  · exact Fin.elim0 (hlen ▸ k)
  have hseedInitial : ReferenceFirstLiveConfirmationHistory.InitialFollowers initial :=
    initialFollowers_of_seed initial seed memory hseed hnone hunoccupied
  have hstate : ReferenceFirstLiveConfirmationHistory.FirstLiveState W[k.val].input.state :=
    ReferenceFirstLiveConfirmationHistory.run_firstLive_carried
      initial rows J rewards start count hspan active hfirst hseedInitial k
  have hnoCut : ReferenceCollectionPhaseHistory.cutoffChosen W[k.val].input = false := by
    have hmem : W[k.val] ∈ W := List.getElem_mem k.isLt
    have htake := List.mem_takeWhile_imp hmem
    simpa only [ReferenceFirstLiveConfirmationHistory.firstLiveWindow,
      Bool.not_eq_true'] using htake
  have hselectedPrepared :
      (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinator.selection = some selected := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hselected
  have heventPrepared : CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
      selected.view.pendingAtChoice selected.view.cutoff W[k.val].input.time
      (W[k.val].input.row.2 W[k.val].input.time)
      (ReferenceActivePhysicalStep.prepare W[k.val].input).coordinatorObservation := by
    simpa only [W[k.val].output_eq, ReferenceActivePhysicalStep.step] using hevent
  have hnonempty : selected.view.pendingAtChoice.Nonempty := by
    rw [hsingleton]
    exact ⟨focal, Finset.mem_singleton_self focal⟩
  have hchoiceFields :=
    ReferenceFirstLiveConfirmedOccupancy.run_first_live_actual_choice_fields
      initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
      hbacklog hnone hunoccupied hvalid hpair htime hbatch
  have hallAway := run_first_live_all_follower_occupancy
      initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
      hbacklog hnone hunoccupied hvalid hpair htime hbatch
  have hprovenance := ReferenceFirstLiveMissingSetProvenance.run_first_live_missing_set_provenance
    initial rows J rewards start count hspan active hfirst
  obtain hzero | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hframes⟩ := hprovenance
  · exact False.elim (hlen hzero)
  · obtain ⟨record, hrecord, currentSelected, hcurrentActual, _, _, nextRegisters,
        nextOwned, nextBase, hnext, _, _, _⟩ := hframes k
    subst record
    have hselectedEq : currentSelected = selected :=
      Option.some.inj (hcurrentActual.symm.trans hselected)
    subst currentSelected
    have hnextO :=
      ReferenceFirstLiveConfirmedOccupancy.run_first_live_singleton_confirmation_erases_pending
        initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
        hbacklog hnone hunoccupied hvalid hpair htime hbatch k selected hselected
        nextRegisters nextOwned nextBase hnext hsingleton hevent
    have hempty : selected.view.pendingAtChoice.erase focal = ∅ := by
      rw [hsingleton]
      simp
    refine ⟨nextRegisters, nextOwned, nextBase, hnext, hnextO.1, ?_, ?_⟩
    · rw [hnextO.2, hempty]
    · intro i
      obtain ⟨choice, choiceMemory, nextFollower, nextFollowerMemory,
          hchoice, houtput, hfailure, hfields, hnotReleased⟩ :=
        hchoiceFields k selected hselected i
      by_cases hfocus : i = focal
      · subst i
        have hchoiceFocal : choice.status = .pending := by
          have hchoicePrepared :
              ((ReferenceActivePhysicalStep.prepare W[k.val].input).followers.followers focal).configuration =
                .ordinary choice choiceMemory := by
            have hchoice' := hchoice
            rw [W[k.val].output_eq] at hchoice'
            exact hchoice'
          exact ReferenceFirstLiveConfirmedOccupancy.actual_first_live_selected_confirmation_choice_pending
            W[k.val].input hstate hnoCut selected hselectedPrepared choice choiceMemory
            hchoicePrepared heventPrepared
        have hoccupiedFocal : choice.status ≠ .unoccupied := by
          rw [hchoiceFocal]
          decide
        have hlast : choice.lastDown = some (selected.view.payload.downRecord focal) :=
          hfields hoccupiedFocal
        exact ⟨choice, choiceMemory, nextFollower, nextFollowerMemory,
          hchoice, houtput, hfailure, hchoiceFocal, hlast⟩
      · have hiAway : i ∉ selected.view.pendingAtChoice := by
          rw [hsingleton]
          exact fun hmem => hfocus (Finset.mem_singleton.mp hmem)
        obtain ⟨choiceAway, memoryAway, outputAway, outputMemoryAway,
            hchoiceAway, houtputAway, hfailureAway, hoccupiedAway, _hlastAway⟩ :=
          hallAway k selected hselected i hiAway
        have hsame : choiceAway = choice := by
          have heq := hchoiceAway.symm.trans hchoice
          injection heq with hstateEq hmemoryEq
        have hnotReleasedAway : choiceAway.status ≠ .released := by
          rw [hsame]
          exact hnotReleased hnonempty
        have hpendingAway : choiceAway.status = .pending := by
          cases hstatus : choiceAway.status with
          | unoccupied => exact False.elim (hoccupiedAway hstatus)
          | pending => rfl
          | released => exact False.elim (hnotReleasedAway hstatus)
        have hpendingAway' : choice.status = .pending := by
          rw [← hsame]
          exact hpendingAway
        have hoccupiedChoice : choice.status ≠ .unoccupied := by
          rw [← hsame]
          exact hoccupiedAway
        have hlast : choice.lastDown = some (selected.view.payload.downRecord i) := by
          exact hfields hoccupiedChoice
        exact ⟨choice, choiceMemory, nextFollower, nextFollowerMemory,
          hchoice, houtput, hfailure, hpendingAway', hlast⟩

private theorem source_launch_seed_fields
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some initial)
    (hdownBatch : ReferenceFollowerDecoderChronology.downBatchSeed initial s) :
    ∃ seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
      ∃ memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
        initial.coordinator = .first ∧
        (∀ i, initial.followers i = .ordinary (seed i) (memory i)) ∧
        (∀ i, (seed i).S = 0) ∧ (∀ i, (seed i).delta = 0) ∧
        (∀ i, (seed i).backlog = 0) ∧ (∀ i, (seed i).lastDown = none) ∧
        (∀ i, ReferencePrelaunchFollower.acceptedStart (seed i) = 0) ∧
        (∀ i, (seed i).status = .unoccupied) ∧
        (∀ i, ActiveFollowerLifecycle.localBufferValid (seed i)) ∧
        (∀ i, (seed i).buffer.Pairwise
          (fun a b => a.calendarRound < b.calendarRound)) ∧
        (∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s) ∧
        (∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  have hsourceEta :
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate).eta =
        rate.eta := by rfl
  cases hsourceEta
  have helapsedB : ReferenceInitializationRun.elapsed p b.completed = s := by
    simpa [x, b] using helapsed
  obtain ⟨actual, ⟨hactualLaunch, hfirst, _, _, hfollowers⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hc
  have hactualEq : actual = initial := Option.some.inj (hactualLaunch.symm.trans hlaunch)
  subst actual
  obtain ⟨fieldState, hfieldLaunch, hfields⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_follower_source_fields
      rate source rewards C_star C_h hc
  have hfieldEq : fieldState = initial := Option.some.inj (hfieldLaunch.symm.trans hlaunch)
  subst fieldState
  let seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta := fun i =>
    ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i)
  let memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p := fun _ =>
    ActiveFollowerLifecycle.initialMemory p
  have hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i) := by
    intro i
    simpa [seed, memory, x, b] using hfollowers i
  have hS : ∀ i, (seed i).S = 0 := by
    intro i
    simpa [seed, x, b] using (hfields i).2.2.2.1
  have hdelta : ∀ i, (seed i).delta = 0 := by
    intro i
    simpa [seed, x, b] using (hfields i).2.2.2.2.1
  have hbacklog : ∀ i, (seed i).backlog = 0 := by
    intro i
    simpa [seed, x, b] using (hfields i).2.2.2.2.2.1
  have hnone : ∀ i, (seed i).lastDown = none := by
    intro i
    simpa [seed, x, b, ActualReferenceInitializationBlock.referenceInput] using (hfields i).2.1
  have haccepted : ∀ i, ReferencePrelaunchFollower.acceptedStart (seed i) = 0 := by
    intro i
    simpa [seed, x, b, ActualReferenceInitializationBlock.referenceInput] using (hfields i).2.2.1
  have hunoccupied : ∀ i, (seed i).status = .unoccupied := by
    intro i
    simpa [seed, x, b] using (hfields i).2.2.2.2.2.2.1
  have hvalid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i) := by
    intro i
    have hbuffer := ReferenceFollowerBufferProvenance.initialization_ordinary_buffer_valid
      x b (ActualReferenceInitializationBlock.refFollower i)
    simpa [seed, x, b, ActualReferenceInitializationBlock.referenceInput] using hbuffer.1
  have hpair : ∀ i, (seed i).buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound) := by
    intro i
    have hbuffer := ReferenceFollowerBufferProvenance.initialization_ordinary_buffer_valid
      x b (ActualReferenceInitializationBlock.refFollower i)
    simpa [seed, x, b, ActualReferenceInitializationBlock.referenceInput] using hbuffer.2.1
  have htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s := by
    intro i saved hsaved
    have hbuffer := ReferenceFollowerBufferProvenance.initialization_ordinary_buffer_valid
      x b (ActualReferenceInitializationBlock.refFollower i)
    have htime' := hbuffer.2.2 saved (by simpa [seed, x, b] using hsaved)
    simpa [helapsedB] using htime'
  have hbatch : ∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i) := by
    intro i
    obtain ⟨batchState, batchMemory, hbatchConfig, _, hwell, _, _⟩ := hdownBatch i
    have hstateEq : batchState = seed i := by
      have heq := hbatchConfig.symm.trans (hseed i)
      injection heq with hstateEq hmemoryEq
    have hbatchState : ActiveFollowerLifecycle.downDecoderStateValid batchState := by
      change ReferenceFollowerDecoderChronology.downBatchWellFormed batchState.downBatch
      exact hwell
    rw [← hstateEq]
    exact hbatchState
  exact ⟨seed, memory, hfirst, hseed, hS, hdelta, hbacklog, hnone,
    haccepted, hunoccupied, hvalid, hpair, htime, hbatch⟩

/-- The same first-live occupancy assembly on the original complete source
fibre. Below the terminal round, G's inverse fixed-control split supplies the
actual corrected launch; at `s = T`, G's terminal constructor supplies the
real zero-record run. The complete source, WHOLE reward table, and both
unrestricted constants remain explicit. -/
theorem original_source_first_live_all_follower_occupancy
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
          ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
              some initial ∧
          initial.coordinator = .first ∧
          (∀ i, initial.followers i = .ordinary (seed i) (memory i)) ∧
          (∀ i, (seed i).S = 0) ∧ (∀ i, (seed i).delta = 0) ∧
          (∀ i, (seed i).backlog = 0) ∧ (∀ i, (seed i).lastDown = none) ∧
          (∀ i, ReferencePrelaunchFollower.acceptedStart (seed i) = 0) ∧
          (∀ i, (seed i).status = .unoccupied) ∧
          (∀ i, ActiveFollowerLifecycle.localBufferValid (seed i)) ∧
          (∀ i, (seed i).buffer.Pairwise
            (fun a b => a.calendarRound < b.calendarRound)) ∧
          (∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ s) ∧
          (∀ i, ActiveFollowerLifecycle.downDecoderStateValid (seed i)) ∧
          (let E := ReferenceActivePhysicalHorizon.run initial source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
            (by omega) hmode
           let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
           (∀ (k : Fin W.length) (selected : Selection W[k.val].input),
             W[k.val].output.preparation.coordinator.selection = some selected →
             ∀ i : Fin (p.m - 1), i ∉ selected.view.pendingAtChoice →
               ∃ choice choiceMemory next nextMemory,
                 (W[k.val].output.preparation.followers.followers i).configuration =
                   .ordinary choice choiceMemory ∧
                 (W[k.val].output.followers i).configuration = .ordinary next nextMemory ∧
                 (W[k.val].output.followers i).failure = none ∧
                 choice.status ≠ .unoccupied ∧
                 choice.lastDown = some (selected.view.payload.downRecord i)) ∧
           (∀ (k : Fin W.length) (selected : Selection W[k.val].input),
             W[k.val].output.preparation.coordinator.selection = some selected →
             let focal := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
               (W[k.val].input.row.2 W[k.val].input.time).1
             selected.view.pendingAtChoice = {focal} →
             CoordinatorLocalArmChoice.downConfirmationEvent selected.view.payload
               selected.view.pendingAtChoice selected.view.cutoff W[k.val].input.time
               (W[k.val].input.row.2 W[k.val].input.time)
               W[k.val].output.preparation.coordinatorObservation →
             ∃ next : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
               ∃ owned : CoordinatorLiveServiceFinish.OwnedRegisters next,
                 ∃ base : Fin (p.m - 1) → ℕ,
                   W[k.val].output.next.coordinator = .live next owned base ∧
                   next.payload = selected.view.payload ∧ next.pendingAtChoice = ∅ ∧
                   ∀ i : Fin (p.m - 1),
                     ∃ choice choiceMemory nextFollower nextFollowerMemory,
                       (W[k.val].output.preparation.followers.followers i).configuration =
                         .ordinary choice choiceMemory ∧
                       (W[k.val].output.followers i).configuration =
                         .ordinary nextFollower nextFollowerMemory ∧
                       (W[k.val].output.followers i).failure = none ∧
                       choice.status = .pending ∧
                       choice.lastDown = some (selected.view.payload.downRecord i)) ∧
           (s = p.T → count = 0 ∧ E.finalState = initial ∧ E.records = [])) := by
  have hsle : s ≤ p.T := by omega
  by_cases hterminal : s = p.T
  · have hterminalSource : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T :=
      helapsed.trans hterminal
    obtain ⟨_, hzero⟩ :=
      ReferenceGeneratedActivePrefixFactor.terminal_crossing_generated_seed_run_zero
        rate rewards C_star C_h source hc hterminalSource
    obtain ⟨⟨initial, hmode, hlaunch, hfinal, hrecords⟩, _⟩ := hzero
    obtain ⟨batchInitial, hbatchLaunch, hdownBatch⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
        rate source rewards C_star C_h hc
    have hbatchEq : batchInitial = initial := Option.some.inj (hbatchLaunch.symm.trans hlaunch)
    subst batchInitial
    have hdownBatchS : ReferenceFollowerDecoderChronology.downBatchSeed initial s := by
      simpa only [helapsed, hterminal] using hdownBatch
    obtain ⟨seed, memory, hfirst, hseed, hS, hdelta, hbacklog, hnone,
      haccepted, hunoccupied, hvalid, hpair, htime, hbatch⟩ :=
      source_launch_seed_fields source rewards C_star C_h s hc helapsed initial hlaunch
        hdownBatchS
    have hmodeS : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := by
      simpa [hterminal] using hmode
    refine ⟨initial, seed, memory, hmodeS, hlaunch, hfirst, hseed, hS, hdelta,
      hbacklog, hnone, haccepted, hunoccupied, hvalid, hpair, htime, hbatch, ?_⟩
    dsimp only
    constructor
    · exact run_first_live_all_follower_occupancy initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
        (by omega) hmodeS hfirst seed memory hseed hS hdelta hbacklog hnone
        hunoccupied hvalid hpair htime hbatch
    · constructor
      · exact run_first_live_singleton_confirmation_all_pending initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
          (by omega) hmodeS hfirst seed memory hseed hS hdelta hbacklog hnone
          hunoccupied hvalid hpair htime hbatch
      · intro hsT
        have hcount : count = 0 := by omega
        constructor
        · exact hcount
        · constructor
          · simpa [hcount, hterminal] using hfinal
          · simpa [hcount, hterminal] using hrecords
  · have hbefore : s < p.T := by omega
    let q := ActualInitializationPhysicalStep.selectedRowIndex p source
    let t : Fin p.T := ⟨s, hbefore⟩
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source
    let control := split.1
    let remainder := split.2
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q := rfl
    have hrem : remainder ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t source]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    have hstart : remainder ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control source hselected s (by rfl)).mpr
        ⟨hc, helapsed⟩
    let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
      rate rewards C_star C_h q t control remainder hrem s (by rfl) hstart
    have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control remainder hrem s (by rfl) hstart
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source
        rewards C_star C_h = some generated := by
      have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder = source := by
        dsimp [ReferenceGeneratedActivePrefixFactor.splitSource, q, t, control, remainder, split]
        exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply source
      have hgeneratedLaunch := hspec.1
      change ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder) rewards C_star C_h =
          some generated at hgeneratedLaunch
      rw [hsource] at hgeneratedLaunch
      exact hgeneratedLaunch
    have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart generated s := hspec.2.1
    have hdownBatch : ReferenceFollowerDecoderChronology.downBatchSeed generated s := hspec.2.2
    obtain ⟨seed, memory, hfirst, hseed, hS, hdelta, hbacklog, hnone,
      haccepted, hunoccupied, hvalid, hpair, htime, hbatch⟩ :=
      source_launch_seed_fields source rewards C_star C_h s hc helapsed generated hlaunch
        hdownBatch
    refine ⟨generated, seed, memory, hmode, hlaunch, hfirst, hseed, hS, hdelta,
      hbacklog, hnone, haccepted, hunoccupied, hvalid, hpair, htime, hbatch, ?_⟩
    dsimp only
    constructor
    · exact run_first_live_all_follower_occupancy generated source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
        (by omega) hmode hfirst seed memory hseed hS hdelta hbacklog hnone
        hunoccupied hvalid hpair htime hbatch
    · constructor
      · exact run_first_live_singleton_confirmation_all_pending generated source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
          (by omega) hmode hfirst seed memory hseed hS hdelta hbacklog hnone
          hunoccupied hvalid hpair htime hbatch
      · intro hsT
        exact False.elim (hterminal hsT)

end Bandits.Support.ReferenceFirstLiveAllFollowerOccupancy

end
