/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstComplementMassBudget

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# First-live numeric domains and checked dispatches

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`,
`sources/zip4/manuscript/06_interruptions.tex:40-61,246-267`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

This module transports the admitted first-complement mass theorem to the
literal pre-choice input of each actual first-live record, including the
actual first cutoff record just beyond the `takeWhile` window. It proves the
numeric and initializer checks for that same original prefix and consumes
them at the actual start-round and live dispatches. Recorder rejection,
choice rejection, frame mismatch, envelope failure, and other original
outcomes remain possible. These are internal runtime-domain results; they do
not assert source arrival truth, global score identity, no dagger, follower
safety, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ReferenceCoordinatorClockDomains
open Bandits.Support.ReferenceAssignmentPayloadChronology
open Bandits.Support.ReferenceFirstLiveConfirmationHistory

namespace Bandits.Support.ReferenceFirstLiveDispatchDomains

abbrev Parameters := ReferenceFirstComplementMassBudget.Parameters
abbrev RateInput := ReferenceFirstComplementMassBudget.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem allFin_eq_true_iff_local {length : ℕ}
    (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    subst b
    exact h i

private theorem anyFin_assignment_eq_true_iff
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (a : Fin p.K) :
    CoordinatorCollectionLedger.anyFin (p.m - 1)
        (fun i => decide (r.payload.assignment.assigned i = a)) = true ↔
      a ∈ r.payload.slowSet.1 := by
  have himage : Finset.univ.image r.payload.assignment.assigned = r.payload.slowSet.1 :=
    r.payload.assignment_image
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hbtrue⟩
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    subst b
    have hEq : r.payload.assignment.assigned i = a := of_decide_eq_true hbtrue
    have hmem : a ∈ Finset.univ.image r.payload.assignment.assigned :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hEq⟩
    simpa [himage] using hmem
  · intro ha
    have hmem : a ∈ Finset.univ.image r.payload.assignment.assigned := by
      simpa [himage] using ha
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    refine ⟨true, List.mem_ofFn.mpr ⟨i, ?_⟩, rfl⟩
    simp [hi]

private theorem anyFin_assignment_eq_decide
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (a : Fin p.K) :
    CoordinatorCollectionLedger.anyFin (p.m - 1)
        (fun i => decide (r.payload.assignment.assigned i = a)) =
      decide (a ∈ r.payload.slowSet.1) := by
  by_cases ha : a ∈ r.payload.slowSet.1
  · have h := (anyFin_assignment_eq_true_iff r a).2 ha
    simp [ha, h]
  · have hne : CoordinatorCollectionLedger.anyFin (p.m - 1)
      (fun i => decide (r.payload.assignment.assigned i = a)) ≠ true := by
        intro h
        exact ha ((anyFin_assignment_eq_true_iff r a).1 h)
    cases h : CoordinatorCollectionLedger.anyFin (p.m - 1)
        (fun i => decide (r.payload.assignment.assigned i = a)) <;>
      simp [ha, h] at *

private theorem initializationDomainValid_of_original_prefix_domains
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (start : ℕ) (time : Fin p.T)
    (hσ : r.priorClock.sigma = some r.payload.sigma)
    (hgrid : r.gridBoundary = r.priorClock.g)
    (hpayloadOrigin : r.payload.sigma.val = start)
    (hstartBefore : start < time.val)
    (hnext : time.val + 1 ≤ r.gridBoundary)
    (hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val r.priorClock)
    (hscore : r.scoreDomainValid)
    (hmass : ∀ a, r.complementScores a + q.queue a ≤ p.T * D p)
    (hprevious : q.previousServiceDomainValid)
    (hbase : ∀ i, base i = 0) :
    CoordinatorStartRoundCutoffDispatch.initializationDomainValid r q base time := by
  classical
  have hclock' :
      CoordinatorPhaseClock.clockRegistersValid p rate.eta.val r.priorClock := hclock
  unfold CoordinatorPhaseClock.clockRegistersValid at hclock'
  rw [hσ] at hclock'
  have hbefore : r.payload.sigma.val < time.val := by
    rw [hpayloadOrigin]
    exact hstartBefore
  have hgridBound : r.gridBoundary ≤ p.T + 1 := by
    rw [hgrid]
    exact hclock'.2.2.1
  have hscoreMass : ∀ a, r.complementScores a ≤ p.T * D p := by
    intro a
    exact Nat.le_trans (Nat.le_add_right _ _) (hmass a)
  have hqueueMass : ∀ a, q.queue a ≤ p.T * D p := by
    intro a
    exact Nat.le_trans (Nat.le_add_left _ _) (hmass a)
  have hbaseDomain : ∀ i, base i ≤ p.T * D p := by
    intro i
    rw [hbase i]
    exact Nat.zero_le _
  have houtsideDomain : ∀ a : Fin p.K,
      (if CoordinatorCollectionLedger.anyFin (p.m - 1)
          (fun i : Fin (p.m - 1) =>
            decide ((CoordinatorStartRoundCutoffDispatch.ledgerAssignment r).arm i = a)) then
        decide (CoordinatorStartRoundCutoffDispatch.outsideRegisters r q a = none)
      else
        match CoordinatorStartRoundCutoffDispatch.outsideRegisters r q a with
        | none => false
        | some reg => decide (reg.score ≤ p.T * D p) &&
            decide (reg.queue ≤ p.T * D p) && decide (reg.lastService ≤ D p)) = true := by
    intro a
    have hassignedImage :
        Finset.univ.image (CoordinatorStartRoundCutoffDispatch.ledgerAssignment r).arm =
          r.payload.slowSet.1 := by
      change Finset.univ.image r.payload.assignment.assigned = r.payload.slowSet.1
      exact r.payload.assignment_image
    have hany :
        CoordinatorCollectionLedger.anyFin (p.m - 1)
          (fun i : Fin (p.m - 1) =>
            decide ((CoordinatorStartRoundCutoffDispatch.ledgerAssignment r).arm i = a)) =
          decide (a ∈ r.payload.slowSet.1) := by
      change CoordinatorCollectionLedger.anyFin (p.m - 1)
        (fun i : Fin (p.m - 1) => decide (r.payload.assignment.assigned i = a)) = _
      exact anyFin_assignment_eq_decide r a
    by_cases ha : a ∈ r.payload.slowSet.1
    · have hnotFast : a ∉ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
        simp [CanonicalFastSampling.fastArmFinset, ha]
      simp [hany, ha, CoordinatorStartRoundCutoffDispatch.outsideRegisters, hnotFast]
    · have hfast : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
        simp [CanonicalFastSampling.fastArmFinset, ha]
      let j : CanonicalFastSampling.FastArm r.payload.slowSet := ⟨a, hfast⟩
      have hsum := hmass j
      have hs : r.complementScores j ≤ p.T * D p :=
        Nat.le_trans (Nat.le_add_right _ _) hsum
      have hq : q.queue j ≤ p.T * D p :=
        Nat.le_trans (Nat.le_add_left _ _) hsum
      have hp : q.previousService j ≤ D p := hprevious j
      simp [hany, ha, hfast, j, CoordinatorStartRoundCutoffDispatch.outsideRegisters,
        hs, hq, hp]
  have hinputs :
      CoordinatorCollectionLedger.validInitialInputsCheck
        (CoordinatorStartRoundCutoffDispatch.ledgerAssignment r)
        (r.payload.sigma.val + 1) (time.val + 1) r.gridBoundary base
        (CoordinatorStartRoundCutoffDispatch.outsideRegisters r q) = true := by
    have hbaseAll := (allFin_eq_true_iff_local _).2
      (fun i => decide_eq_true (hbaseDomain i))
    have houtsideAll := (allFin_eq_true_iff_local _).2 houtsideDomain
    have hsigmaUpper : r.payload.sigma.val + 1 ≤ p.T := by
      rw [hpayloadOrigin]
      omega
    have htimeUpper : time.val + 1 ≤ p.T := by omega
    simp only [CoordinatorCollectionLedger.validInitialInputsCheck,
      Bool.and_eq_true, decide_eq_true_eq]
    have hσLower : 1 ≤ r.payload.sigma.val + 1 := by omega
    have htimeLower : 1 ≤ time.val + 1 := by omega
    exact ⟨⟨⟨⟨⟨⟨⟨hσLower, hsigmaUpper⟩, htimeLower⟩,
      hnext⟩, htimeUpper⟩, hgridBound⟩, hbaseAll⟩, houtsideAll⟩
  let candidate := CoordinatorStartRoundCutoffDispatch.collectionStartLedger r q base time
  have hArmPending : ∀ a : Fin p.K,
      CoordinatorCollectionLedger.armPendingCheck candidate a =
        decide (a ∈ r.payload.slowSet.1) := by
    intro a
    unfold CoordinatorCollectionLedger.armPendingCheck
    simp only [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
      Finset.mem_univ, decide_true, Bool.true_and]
    change CoordinatorCollectionLedger.anyFin (p.m - 1)
      (fun i : Fin (p.m - 1) => decide (r.payload.assignment.assigned i = a)) = _
    exact anyFin_assignment_eq_decide r a
  have hcurrentNone : ∀ a : Fin p.K,
      (candidate.currentRegisters a).isNone = decide (a ∈ r.payload.slowSet.1) := by
    intro a
    by_cases ha : a ∈ r.payload.slowSet.1
    · simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
        CoordinatorStartRoundCutoffDispatch.outsideRegisters, ha]
    · have hfast : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
        simp [CanonicalFastSampling.fastArmFinset, ha]
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
        CoordinatorStartRoundCutoffDispatch.outsideRegisters, ha]
  have hcurrentPending :
      CoordinatorCollectionLedger.allFin p.K (fun a =>
        ((candidate.currentRegisters a).isNone ==
          CoordinatorCollectionLedger.armPendingCheck candidate a)) = true := by
    apply (allFin_eq_true_iff_local _).2
    intro a
    simp only [hcurrentNone, hArmPending, beq_self_eq_true]
  have hcutoffNone : ∀ a : Fin p.K,
      (candidate.cutoffRegisters a).isNone = decide (a ∈ r.payload.slowSet.1) := by
    intro a
    by_cases ha : a ∈ r.payload.slowSet.1
    · have hnotFast : a ∉ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
        simp [CanonicalFastSampling.fastArmFinset, ha]
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
        CoordinatorStartRoundCutoffDispatch.outsideRegisters, hnotFast, ha]
    · have hfast : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
        simp [CanonicalFastSampling.fastArmFinset, ha]
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
        CoordinatorStartRoundCutoffDispatch.outsideRegisters, hfast, ha]
  have hcutoffPending :
      CoordinatorCollectionLedger.allFin p.K (fun a =>
        ((candidate.cutoffRegisters a).isNone ==
          CoordinatorCollectionLedger.armPendingCheck candidate a)) = true := by
    apply (allFin_eq_true_iff_local _).2
    intro a
    simp only [hcutoffNone, hArmPending, beq_self_eq_true]
  have hregisterDomains :
      CoordinatorCollectionLedger.registerDomainsCheck candidate = true := by
    simp only [CoordinatorCollectionLedger.registerDomainsCheck,
      Bool.and_eq_true]
    have hcurrent :
        CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
          match candidate.currentRegisters a with
          | none => true
          | some reg => decide (reg.queue ≤ p.T * D p) &&
              decide (reg.lastService ≤ D p)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      by_cases ha : a ∈ r.payload.slowSet.1
      · simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
          CoordinatorStartRoundCutoffDispatch.outsideRegisters, ha]
      · have hfast : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
          simp [CanonicalFastSampling.fastArmFinset, ha]
        let j : CanonicalFastSampling.FastArm r.payload.slowSet := ⟨a, hfast⟩
        have hq := hqueueMass j
        have hp := hprevious j
        simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
          CoordinatorStartRoundCutoffDispatch.outsideRegisters, ha, j, hq, hp]
    have hcutoff :
        CoordinatorCollectionLedger.allFin p.K (fun a : Fin p.K =>
          match candidate.cutoffRegisters a with
          | none => true
          | some reg => decide (reg.score ≤ p.T * D p) &&
              decide (reg.queue ≤ p.T * D p) && decide (reg.lastService ≤ D p)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      by_cases ha : a ∈ r.payload.slowSet.1
      · have hnotFast : a ∉ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
          simp [CanonicalFastSampling.fastArmFinset, ha]
        simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
          CoordinatorStartRoundCutoffDispatch.outsideRegisters, hnotFast]
      · have hfast : a ∈ CanonicalFastSampling.fastArmFinset r.payload.slowSet := by
          simp [CanonicalFastSampling.fastArmFinset, ha]
        let j : CanonicalFastSampling.FastArm r.payload.slowSet := ⟨a, hfast⟩
        have hs := hscoreMass j
        have hq := hqueueMass j
        have hp := hprevious j
        simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
          CoordinatorStartRoundCutoffDispatch.outsideRegisters, hfast, j, hs, hq, hp]
    have hbaseCheck : CoordinatorCollectionLedger.allFin (p.m - 1) (fun i =>
        decide (candidate.baseScore i ≤ p.T * D p)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro i
      rw [show candidate.baseScore i = base i by rfl]
      exact decide_eq_true (hbaseDomain i)
    have hincrement : CoordinatorCollectionLedger.allFin p.K (fun a =>
        decide (candidate.increment a ≤ p.T * D p)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
    have hgammaDomain : CoordinatorCollectionLedger.allFin p.K (fun a =>
        decide (candidate.gammaLoc a ≤ D p)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
    exact ⟨⟨⟨⟨hcurrent, hcutoff⟩, hbaseCheck⟩, hincrement⟩, hgammaDomain⟩
  have hreadyHistory : CoordinatorCollectionLedger.readyHistoryCheck candidate = true := by
    unfold CoordinatorCollectionLedger.readyHistoryCheck
    apply (allFin_eq_true_iff_local _).2
    intro t
    simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger,
      CoordinatorCollectionLedger.sourceRound]
  have hraw : CoordinatorCollectionLedger.rawEntryDomainsCheck candidate = true := by
    unfold CoordinatorCollectionLedger.rawEntryDomainsCheck
    apply (allFin_eq_true_iff_local _).2
    intro a
    apply (allFin_eq_true_iff_local _).2
    intro t
    simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hvalidLedger : CoordinatorCollectionLedger.validLedgerCheck candidate = true := by
    have hphase : candidate.phase = CoordinatorCollectionLedger.Phase.ready := rfl
    have hcursor : candidate.cursor = time.val + 1 := rfl
    have hcutoffTime : candidate.cutoff = time.val + 1 := rfl
    have hfreeze : candidate.freezeAt = r.gridBoundary := rfl
    have htimeBeforeGrid : time.val < r.gridBoundary := by omega
    have hsigmaTime : candidate.sigma = r.payload.sigma.val + 1 := rfl
    have hgammaAll : CoordinatorCollectionLedger.allFin p.K (fun a =>
        decide (candidate.gammaLoc a = 0)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
    have hgammaPending : CoordinatorCollectionLedger.allFin p.K (fun a =>
        (!CoordinatorCollectionLedger.armPendingCheck candidate a) ||
          decide (candidate.gammaLoc a = 0)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
    have hincrementPending : CoordinatorCollectionLedger.allFin p.K (fun a =>
        (!CoordinatorCollectionLedger.armPendingCheck candidate a) ||
          decide (candidate.increment a = 0)) = true := by
      apply (allFin_eq_true_iff_local _).2
      intro a
      simp [candidate, CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
    simp [CoordinatorCollectionLedger.validLedgerCheck, hphase, hcursor, hcutoffTime,
      hfreeze, hsigmaTime, hgridBound, htimeBeforeGrid, hregisterDomains,
      hreadyHistory, hraw, hcurrentPending, hcutoffPending, hgammaAll,
      hgammaPending, hincrementPending]
  unfold CoordinatorStartRoundCutoffDispatch.initializationDomainValid
  exact ⟨hσ, hgrid, hbefore, hnext, hgridBound, r.payload.queues_le_TD,
    hscore, hqueueMass, hprevious, hbaseDomain, hinputs, hvalidLedger⟩

private theorem initializationDomainValid_liveAt
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T)
    (h : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      r q base time) :
    CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (ReferenceActivePhysicalStep.liveRegistersAt r time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q time) base time := by
  cases r with
  | mk payload priorClock pendingAtChoice oldTime gridBoundary complementScores =>
    cases q with
    | mk queue previousService =>
      let oldR : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta :=
        { payload := payload, priorClock := priorClock,
          pendingAtChoice := pendingAtChoice, time := oldTime,
          gridBoundary := gridBoundary, complementScores := complementScores }
      let oldQ : CoordinatorLiveServiceFinish.OwnedRegisters oldR :=
        { queue := queue, previousService := previousService }
      let newR := ReferenceActivePhysicalStep.liveRegistersAt oldR time
      let newQ := ReferenceActivePhysicalStep.liveOwnedAt oldR oldQ time
      have hassignment :
          CoordinatorStartRoundCutoffDispatch.ledgerAssignment newR =
            CoordinatorStartRoundCutoffDispatch.ledgerAssignment oldR := rfl
      have houtside :
          CoordinatorStartRoundCutoffDispatch.outsideRegisters newR newQ =
            CoordinatorStartRoundCutoffDispatch.outsideRegisters oldR oldQ := rfl
      have hcandidate :
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger newR newQ base time =
            CoordinatorStartRoundCutoffDispatch.collectionStartLedger oldR oldQ base time := rfl
      rcases h with ⟨hσ, hgrid, hbefore, hnext, hgridBound, hqueues,
        hscore, hqueue, hprevious, hbase, hinputs, hledger⟩
      refine ⟨hσ, hgrid, hbefore, hnext, hgridBound, hqueues, ?_, ?_, ?_,
        hbase, ?_, ?_⟩
      · change ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
          complementScores j ≤ p.T * D p
        exact hscore
      · change ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
          queue j ≤ p.T * D p
        exact hqueue
      · change ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
          previousService j ≤ D p
        exact hprevious
      · change CoordinatorCollectionLedger.validInitialInputsCheck
          (CoordinatorStartRoundCutoffDispatch.ledgerAssignment newR)
          (payload.sigma.val + 1) (time.val + 1) gridBoundary base
          (CoordinatorStartRoundCutoffDispatch.outsideRegisters newR newQ) = true
        rw [hassignment, houtside]
        exact hinputs
      · change CoordinatorCollectionLedger.validLedgerCheck
          (CoordinatorStartRoundCutoffDispatch.collectionStartLedger newR newQ base time) = true
        rw [hcandidate]
        exact hledger

private theorem cutoffDispatch_success_of_domains
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hdomains : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      r q base r.time)
    (hstart : ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val
      r.time r.priorClock r.clockPending = .ok started) :
    ∃ started,
      CoordinatorStartRoundCutoffDispatch.dispatch r q base =
        .ok ⟨started, .success
          (if started.ledgerCommand = some (.initializeAt r.time) then
            some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              r q base r.time)
          else none)⟩ := by
  obtain ⟨started, hstart⟩ := hstart
  cases hcommand : started.ledgerCommand with
  | none =>
      have hno : ∀ time, started.ledgerCommand ≠ some (.initializeAt time) := by
        intro time
        simp [hcommand]
      refine ⟨started, ?_⟩
      simpa [hcommand] using
        (CoordinatorStartRoundCutoffDispatch.dispatch_no_initialization
          r q base started hstart hno)
  | some command =>
      cases command with
      | initializeAt time =>
          have htime := CoordinatorRoundDispatch.startRound_initializeAt_time
            r.time time r.priorClock r.clockPending started hstart hcommand
          subst time
          refine ⟨started, ?_⟩
          simpa [hcommand] using
            (CoordinatorStartRoundCutoffDispatch.dispatch_initializeAt_success
              r q base started hstart hcommand hdomains)
      | accumulateLocalServiceAt time =>
          have hno : ∀ otherTime,
              started.ledgerCommand ≠ some (.initializeAt otherTime) := by
            intro otherTime
            simp [hcommand]
          refine ⟨started, ?_⟩
          simpa [hcommand] using
            (CoordinatorStartRoundCutoffDispatch.dispatch_no_initialization
              r q base started hstart hno)

/-- The admissible actual live-dispatch outcomes for the first-live numeric
guard: exclude initializer failure and the four numeric local failures while
retaining clock, frame, payload, grid, choice, envelope, recorder-boundary,
and other local outcomes. -/
def dispatchLiveNumericOutcomeSafe
    {p : Parameters} {x : CoordinatorRoundDispatch.LiveInput p}
    (outcome : CoordinatorRoundDispatch.LiveOutcome x) : Prop :=
  match outcome with
  | .initializerFailure _ _ _ _ => False
  | .localFailure _ _ reason =>
      reason ≠ CoordinatorRoundDispatch.LiveFailure.scoreDomainFailure ∧
      reason ≠ CoordinatorRoundDispatch.LiveFailure.queueDomainFailure ∧
      reason ≠ CoordinatorRoundDispatch.LiveFailure.previousServiceDomainFailure ∧
      reason ≠ CoordinatorRoundDispatch.LiveFailure.baseScoreDomainFailure
  | _ => True

private theorem dispatchLive_initializerFailure_impossible
    (x : CoordinatorRoundDispatch.LiveInput p)
    (hdispatch : ∃ dispatched,
      CoordinatorStartRoundCutoffDispatch.dispatch
        x.registers x.ownedRegisters x.followerBaseScore = .ok dispatched ∧
      ∃ initialization,
        dispatched.collectionInitialization = .success initialization)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (hstart : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok dispatched.startResult)
    (checked : CoordinatorCollectionLedger.Checked
      (Option (CoordinatorStartRoundCutoffDispatch.NewLedger x.registers)))
    (hchecked : dispatched.collectionInitialization = checked)
    (hresult : CoordinatorRoundDispatch.dispatchLive x =
      .initializerFailure dispatched hstart checked hchecked) : False := by
  rcases hdispatch with ⟨known, hdispatch_eq, initialization, hinitialization⟩
  unfold CoordinatorRoundDispatch.dispatchLive at hresult
  dsimp only at hresult
  split at hresult
  · simp_all
  · rename_i actual hcall
    have hactual : actual = known :=
      Except.ok.inj (hcall.symm.trans hdispatch_eq)
    subst actual
    split at hresult
    · simp_all
    · simp_all
    · by_cases hframe :
          CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
            x.registers known.startResult
      · rw [dite_eq_left hframe] at hresult
        repeat' split at hresult
        all_goals first
          | cases hresult
          | (rename_i hchoice hboundary henvelope hselected
             exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
               x.registers.payload known.startResult.pending
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                 known.startResult.clock.u)
               x.registers.time x.registers.complementWeights x.row hchoice) hselected).elim)
      · rw [dite_eq_right hframe] at hresult
        cases hresult
    · repeat' split at hresult
      all_goals first
        | (have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
               x.registers.payload
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                 known.startResult.clock.u)
               x.registers.time x.registers.complementWeights := by assumption
           have hselected : CoordinatorLocalArmChoice.coordinatorArmChoice
               x.registers.payload known.startResult.pending
               (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                 known.startResult.clock.u)
               x.registers.time x.registers.complementWeights x.row = none := by assumption
           exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
             x.registers.payload known.startResult.pending
             (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
               known.startResult.clock.u)
             x.registers.time x.registers.complementWeights x.row hchoice) hselected).elim)
        | cases hresult

private theorem dispatchLive_localFailure_not_numeric
    (x : CoordinatorRoundDispatch.LiveInput p)
    (hdomains : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      x.registers x.ownedRegisters x.followerBaseScore x.registers.time)
    (hdispatch : ∃ dispatched,
      CoordinatorStartRoundCutoffDispatch.dispatch
        x.registers x.ownedRegisters x.followerBaseScore = .ok dispatched ∧
      ∃ initialization,
        dispatched.collectionInitialization = .success initialization)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      x.registers x.ownedRegisters x.followerBaseScore)
    (hstart : CoordinatorPhaseClock.startRound p x.eta.val x.registers.time
      x.registers.priorClock x.registers.clockPending = .ok dispatched.startResult)
    (reason : CoordinatorRoundDispatch.LiveFailure)
    (hresult : CoordinatorRoundDispatch.dispatchLive x =
      .localFailure dispatched hstart reason) :
    reason ≠ CoordinatorRoundDispatch.LiveFailure.scoreDomainFailure ∧
    reason ≠ CoordinatorRoundDispatch.LiveFailure.queueDomainFailure ∧
    reason ≠ CoordinatorRoundDispatch.LiveFailure.previousServiceDomainFailure ∧
    reason ≠ CoordinatorRoundDispatch.LiveFailure.baseScoreDomainFailure := by
  rcases hdomains with ⟨hσ, hgrid, _, _, _, _, hscore, hqueue, hprevious,
    hbase, _, _⟩
  rcases hdispatch with ⟨known, hdispatch_eq, initialization, hinitialization⟩
  cases reason <;> simp_all
  all_goals
    unfold CoordinatorRoundDispatch.dispatchLive at hresult
    dsimp only at hresult
    split at hresult
    · simp_all
    · rename_i actual hcall
      have hactual : actual = known :=
        Except.ok.inj (hcall.symm.trans hdispatch_eq)
      subst actual
      split at hresult
      · simp_all
      · simp_all
      · by_cases hframe :
            CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
              x.registers known.startResult
        · rw [dite_eq_left hframe] at hresult
          by_cases hpayload :
              x.registers.priorClock.sigma = some x.registers.payload.sigma
          · rw [dite_eq_left hpayload] at hresult
            by_cases hgridCheck :
                x.registers.gridBoundary = x.registers.priorClock.g
            · rw [dite_eq_left hgridCheck] at hresult
              by_cases hscoreCheck : x.registers.scoreDomainValid
              · rw [dite_eq_left hscoreCheck] at hresult
                by_cases hqueueCheck : x.ownedRegisters.queueDomainValid
                · rw [dite_eq_left hqueueCheck] at hresult
                  by_cases hpreviousCheck :
                      x.ownedRegisters.previousServiceDomainValid
                  · rw [dite_eq_left hpreviousCheck] at hresult
                    by_cases hbaseCheck :
                        ∀ i, x.followerBaseScore i ≤ p.T * D p
                    · rw [dite_eq_left hbaseCheck] at hresult
                      by_cases hlive :
                          CoordinatorLocalArmChoice.assignmentIsLive
                            x.registers.payload
                            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                              known.startResult.clock.u) x.registers.time
                      · rw [dite_eq_left hlive] at hresult
                        by_cases hchoice :
                            CoordinatorLocalArmChoice.ChoiceInputsValid
                              x.registers.payload
                              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                known.startResult.clock.u)
                              x.registers.time x.registers.complementWeights
                        · rw [dite_eq_left hchoice] at hresult
                          by_cases hboundary :
                              known.startResult.clock.g ≤ p.T + 1
                          · rw [dite_eq_left hboundary] at hresult
                            by_cases henvelope :
                                x.registers.complementEnvelopeValid
                            · rw [dite_eq_left henvelope] at hresult
                              split at hresult
                              · have hselected :
                                    CoordinatorLocalArmChoice.coordinatorArmChoice
                                      x.registers.payload known.startResult.pending
                                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                        known.startResult.clock.u)
                                      x.registers.time x.registers.complementWeights x.row = none :=
                                  by assumption
                                exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                                  x.registers.payload known.startResult.pending
                                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                    known.startResult.clock.u)
                                  x.registers.time x.registers.complementWeights x.row hchoice)
                                  hselected).elim
                              · simp_all
                            · rw [dite_eq_right henvelope] at hresult
                              simp_all
                          · rw [dite_eq_right hboundary] at hresult
                            simp_all
                        · rw [dite_eq_right hchoice] at hresult
                          simp_all
                      · rw [dite_eq_right hlive] at hresult
                        simp_all
                    · rw [dite_eq_right hbaseCheck] at hresult
                      simp_all
                  · rw [dite_eq_right hpreviousCheck] at hresult
                    simp_all [CoordinatorLiveServiceFinish.OwnedRegisters.previousServiceDomainValid]
                · rw [dite_eq_right hqueueCheck] at hresult
                  simp_all [CoordinatorLiveServiceFinish.OwnedRegisters.queueDomainValid]
              · rw [dite_eq_right hscoreCheck] at hresult
                simp_all [CoordinatorLiveChoiceRecorderStep.Registers.scoreDomainValid]
            · rw [dite_eq_right hgridCheck] at hresult
              simp_all
          · rw [dite_eq_right hpayload] at hresult
            simp_all
        · rw [dite_eq_right hframe] at hresult
          simp_all
      · by_cases hchoice :
            CoordinatorLocalArmChoice.ChoiceInputsValid x.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                known.startResult.clock.u)
              x.registers.time x.registers.complementWeights
        · rw [dite_eq_left hchoice] at hresult
          by_cases hboundary : known.startResult.clock.g ≤ p.T + 1
          · rw [dite_eq_left hboundary] at hresult
            by_cases henvelope : x.registers.complementEnvelopeValid
            · rw [dite_eq_left henvelope] at hresult
              split at hresult
              · have hselected :
                    CoordinatorLocalArmChoice.coordinatorArmChoice
                      x.registers.payload known.startResult.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                        known.startResult.clock.u)
                      x.registers.time x.registers.complementWeights x.row = none := by
                  assumption
                exact ((CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                  x.registers.payload known.startResult.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                    known.startResult.clock.u)
                  x.registers.time x.registers.complementWeights x.row hchoice)
                  hselected).elim
              · simp_all
            · rw [dite_eq_right henvelope] at hresult
              simp_all
          · rw [dite_eq_right hboundary] at hresult
            simp_all
        · rw [dite_eq_right hchoice] at hresult
          simp_all

private theorem dispatchLive_numeric_failures_excluded
    (x : CoordinatorRoundDispatch.LiveInput p)
    (hdomains : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      x.registers x.ownedRegisters x.followerBaseScore x.registers.time)
    (hdispatch : ∃ dispatched,
      CoordinatorStartRoundCutoffDispatch.dispatch
        x.registers x.ownedRegisters x.followerBaseScore = .ok dispatched ∧
      ∃ initialization,
        dispatched.collectionInitialization = .success initialization) :
    dispatchLiveNumericOutcomeSafe (CoordinatorRoundDispatch.dispatchLive x) := by
  simp only [dispatchLiveNumericOutcomeSafe]
  cases hresult : CoordinatorRoundDispatch.dispatchLive x with
  | clockFailure failure hcall => trivial
  | initializerFailure dispatched hstart checked hchecked =>
      exact (dispatchLive_initializerFailure_impossible x hdispatch dispatched
        hstart checked hchecked hresult).elim
  | localFailure dispatched hstart reason =>
      exact dispatchLive_localFailure_not_numeric x hdomains hdispatch
        dispatched hstart reason hresult
  | cutoffChosen dispatched hstart ledger hinitialization hledger hdomains
      hclock hpending hassignment selection => trivial
  | continuingChosen dispatched hstart continuation selection => trivial

/-- Every actual first-live input prefix before the finite run endpoint has
the literal numeric and full initializer domains. The index bound includes
`k = firstWindow.length` when `k < count`, so it also covers the actual first
chosen cutoff input excluded from the diagnostic window itself.

Source: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`,
`sources/zip4/manuscript/06_interruptions.tex:40-61,246-267`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`. -/
theorem run_first_live_initialization_domains
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k < count)
      (_hkwindow : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active).length),
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k (by omega) active
      match record.input.state.coordinator with
      | .live r q base =>
          CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
            base record.input.time
      | _ => True := by
  intro k hkcount _hkwindow
  dsimp only
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial rows J rewards start k (by omega) active
  let runPrefix := ReferenceFirstComplementMassBudget.originalPrefix
    initial rows J rewards start count hspan active k (Nat.le_of_lt hkcount)
  have hinputState : record.input.state = runPrefix.finalState := rfl
  have hinputTime : record.input.time.val = start + k := rfl
  have hmass := ReferenceFirstComplementMassBudget.run_first_complement_mass
    initial rows J rewards start count hspan active hfirst k (Nat.le_of_lt hkcount)
    _hkwindow
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start count hspan active hseed
  have hclockPrefix := hclockRun.2.1 k (Nat.le_of_lt hkcount)
  have hclockRecord :
      ReferenceCoordinatorClockDomains.clockAt rows J record.input.time.val record.input.state := by
    rw [hinputState, hinputTime]
    exact hclockPrefix
  cases hcoord : record.input.state.coordinator with
  | first => trivial
  | collection payload ledger savedProposal => trivial
  | dagger => trivial
  | live r q base =>
      have hprefixCoord : runPrefix.finalState.coordinator = .live r q base := by
        have hstateCoord := congrArg
          (fun state : ReferenceActivePhysicalHorizon.State p rate => state.coordinator)
          hinputState
        exact hstateCoord.symm.trans hcoord
      simp only [ReferenceFirstComplementMassBudget.originalPrefix] at hmass
      rw [hprefixCoord] at hmass
      rcases hmass with ⟨hmass, hprevious, hbase, birth, hbirthMem, hbirth, hbirthTime⟩
      have hpayloadStart : r.payload.sigma.val = start := by
        exact (ReferenceAssignmentPayloadChronology.installationBirth_time_eq
          birth r.payload hbirth).trans hbirthTime
      have hclockLive := hclockRecord
      simp only [ReferenceCoordinatorClockDomains.clockAt, hcoord] at hclockLive
      rcases hclockLive with ⟨_, hclockValid, hσ, _, hgrid, hbefore, hbeforeGrid, _⟩
      have htimeNext : record.input.time.val + 1 ≤ r.gridBoundary := by
        exact Nat.succ_le_of_lt hbeforeGrid
      have hstartBefore : start < record.input.time.val := by
        rw [← hpayloadStart]
        exact hbefore
      have hkT : k ≤ p.T := by omega
      have hkMass : k * D p ≤ p.T * D p := Nat.mul_le_mul_right _ hkT
      have hmassTD : ∀ a, r.complementScores a + q.queue a ≤ p.T * D p := by
        intro a
        exact Nat.le_trans (hmass a) hkMass
      have hscore : r.scoreDomainValid := by
        intro a
        exact Nat.le_trans (Nat.le_add_right _ _) (hmassTD a)
      have hqueue : ∀ a, q.queue a ≤ p.T * D p := by
        intro a
        exact Nat.le_trans (Nat.le_add_left _ _) (hmassTD a)
      have hpreviousDomain : q.previousServiceDomainValid := hprevious
      have hbaseZero : ∀ i, base i = 0 := hbase
      have hdomainsOriginal := initializationDomainValid_of_original_prefix_domains
        r q base start
        record.input.time hσ hgrid hpayloadStart hstartBefore
        (by simpa [hinputTime, ReferenceActivePhysicalStep.liveRegistersAt] using htimeNext)
        hclockValid hscore hmassTD hpreviousDomain hbaseZero
      have hdomains := initializationDomainValid_liveAt r q base
        record.input.time hdomainsOriginal
      exact hdomains

/-- At every actual live prefix through the bounded first-live window, the
actual start-round cutoff dispatch returns an outer clock success and a
successful optional collection initialization. The range includes
`k = firstWindow.length` when `k < count`, so the actual chosen cutoff input
following the diagnostic window is included. If the actual clock command
initializes at this record's time, the returned ledger is the literal
candidate built from these same live registers, owned queues, and follower
base scores.

Source: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`,
`sources/zip4/manuscript/06_interruptions.tex:40-61,246-267`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`. -/
theorem run_first_live_start_round_dispatch_checked
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k < count)
      (_hkwindow : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active).length),
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k (by omega) active
      match record.input.state.coordinator with
      | .live r q base =>
          ∃ started,
            CoordinatorStartRoundCutoffDispatch.dispatch
              (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base =
              .ok ⟨started, .success
                (if started.ledgerCommand = some (.initializeAt record.input.time) then
                  some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                    (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                    (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
                    base record.input.time)
                else none)⟩
      | _ => True := by
  intro k hkcount _hkwindow
  dsimp only
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial rows J rewards start k (by omega) active
  let runPrefix := ReferenceFirstComplementMassBudget.originalPrefix
    initial rows J rewards start count hspan active k (Nat.le_of_lt hkcount)
  have hinputState : record.input.state = runPrefix.finalState := rfl
  have hinputTime : record.input.time.val = start + k := rfl
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
    start count hspan active hseed
  have hclockPrefix := hclockRun.2.1 k (Nat.le_of_lt hkcount)
  have hclockRecord :
      ReferenceCoordinatorClockDomains.clockAt rows J record.input.time.val record.input.state := by
    rw [hinputState, hinputTime]
    exact hclockPrefix
  have hdomains := run_first_live_initialization_domains
    initial rows J rewards start count hspan active hfirst k hkcount _hkwindow
  cases hcoord : record.input.state.coordinator with
  | first => trivial
  | collection payload ledger savedProposal => trivial
  | dagger => trivial
  | live r q base =>
      simp only
      have hdomainsLive :
          CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
            base record.input.time := by
        simpa [record, hcoord] using hdomains
      have hstart := ReferenceCoordinatorClockDomains.live_dispatch_startRound_success
        r q base hcoord hclockRecord
      have hstartLive :
          ∃ started, CoordinatorPhaseClock.startRound p rate.eta.val
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).time
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).priorClock
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).clockPending =
              .ok started := by
        rcases hstart with ⟨started, hstarted⟩
        refine ⟨started, ?_⟩
        simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hstarted
      obtain ⟨started, hdispatch⟩ := cutoffDispatch_success_of_domains
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base
        hdomainsLive hstartLive
      refine ⟨started, ?_⟩
      exact hdispatch

/-- The actual round dispatcher on every such first-live input, including the
actual cutoff input at `k = firstWindow.length` when `k < count`, cannot return
an initializer failure or one of its four local numeric-domain failures.
Other frame, payload, grid, choice, envelope, recorder-boundary, and local
rejection outcomes remain in the actual outcome type.

Source: `sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-53`,
`sources/zip4/manuscript/06_interruptions.tex:40-61,246-267`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`. -/
theorem run_first_live_dispatchLive_numeric_failures_excluded
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    ∀ k (hkcount : k < count)
      (_hkwindow : k ≤
        (ReferenceFirstComplementMassBudget.firstWindow initial rows J rewards
          start count hspan active).length),
      let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
        initial rows J rewards start k (by omega) active
      match record.input.state.coordinator with
      | .live r q base =>
          dispatchLiveNumericOutcomeSafe
            (CoordinatorRoundDispatch.dispatchLive
              (ReferenceActivePhysicalStep.liveInput record.input r q base))
      | _ => True := by
  intro k hkcount _hkwindow
  dsimp only
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt
    initial rows J rewards start k (by omega) active
  have hdomains := run_first_live_initialization_domains
    initial rows J rewards start count hspan active hfirst k hkcount _hkwindow
  have hstartChecked := run_first_live_start_round_dispatch_checked
    initial rows J rewards start count hspan active hfirst k hkcount _hkwindow
  cases hcoord : record.input.state.coordinator with
  | first => trivial
  | collection payload ledger savedProposal => trivial
  | dagger => trivial
  | live r q base =>
      have hdomainsLive :
          CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
            base record.input.time := by
        simpa [record, hcoord] using hdomains
      have hstarted :
          ∃ started,
            CoordinatorStartRoundCutoffDispatch.dispatch
              (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
              (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base =
              .ok ⟨started, .success
                (if started.ledgerCommand = some (.initializeAt record.input.time) then
                  some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                    (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
                    (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time)
                    base record.input.time)
                else none)⟩ := by
        simpa [record, hcoord] using hstartChecked
      let x := ReferenceActivePhysicalStep.liveInput record.input r q base
      have hdispatch : ∃ dispatched,
          CoordinatorStartRoundCutoffDispatch.dispatch
            x.registers x.ownedRegisters x.followerBaseScore = .ok dispatched ∧
          ∃ initialization,
            dispatched.collectionInitialization = .success initialization := by
        rcases hstarted with ⟨started, hstarted⟩
        let initialization :
            Option (CoordinatorStartRoundCutoffDispatch.NewLedger x.registers) :=
          if started.ledgerCommand = some (.initializeAt record.input.time) then
            some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              x.registers x.ownedRegisters x.followerBaseScore record.input.time)
          else none
        let dispatched :
            CoordinatorStartRoundCutoffDispatch.Output
              x.registers x.ownedRegisters x.followerBaseScore :=
          ⟨started, .success initialization⟩
        refine ⟨dispatched, ?_, initialization, rfl⟩
        simpa [dispatched, initialization, x,
          ReferenceActivePhysicalStep.liveInput] using hstarted
      have hnoBad := dispatchLive_numeric_failures_excluded
        x (by simpa [x, ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveRegistersAt] using hdomainsLive)
        hdispatch
      simpa [record, x, ReferenceActivePhysicalStep.liveInput] using hnoBad

end Bandits.Support.ReferenceFirstLiveDispatchDomains

end
