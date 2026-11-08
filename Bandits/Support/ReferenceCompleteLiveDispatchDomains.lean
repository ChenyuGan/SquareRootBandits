/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteCoordinatorMass

import Lean.Elab.Tactic.Omega

/-!
# Complete-suffix live numeric domains and initializer dispatch

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64`,
`sources/zip4/manuscript/06_interruptions.tex:40-61,246-299`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

This leaf follows each actual LIVE input in the original complete physical
suffix. It combines the complete coordinator mass with the retained installation
base and the source clock at that same record, then proves the literal local
initializer checks and excludes only initializer and numeric dispatch failures.
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
open Bandits.Support.ReferenceCompleteCoordinatorMass
open Bandits.Support.ReferenceAssignmentRetainedBirthProvenance
open Bandits.Support.ReferenceAssignmentMassComposer
open Bandits.Support.ReferenceAssignmentCollectionMassSteps
open Bandits.Support.ReferenceFirstLiveDispatchDomains

namespace Bandits.Support.ReferenceCompleteLiveDispatchDomains

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

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
    (hbase : ∀ i, base i ≤ p.T * D p) :
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
  have hbaseDomain : ∀ i, base i ≤ p.T * D p := hbase
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

private theorem complete_suffix_member_clockAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.state := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hlength := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hlength
      omega
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let launchState := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      let J : Fin (M p) := ActualInitializationPhysicalStep.selectedRowIndex p source
      let rows : CompletePublicTable.CompleteRows p := source.1.2
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      let initial := active
      have hactiveLaunch : initial = launchState := by
        have hboth := hlaunch.symm.trans hcanonical
        exact Option.some.inj hboth
      have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        have hfirst : initial.coordinator = .first := by
          rw [hactiveLaunch]
          exact seed.coordinatorFirst
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let run := ReferenceActivePhysicalHorizon.run initial rows J rewards start
        (p.T - start) hspan hmode
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start (p.T - start) hspan hmode hseed
      have hmember : (R[k.val]'k.isLt) ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      have hrecord := hclockRun.2.2.2 (R[k.val]'k.isLt) hmember
      rw [hrecord.2.2.1, hrecord.2.2.2.1]
      exact hrecord.1

/-- Every actual LIVE input in the original complete suffix has the literal
numeric domains, a successful actual cutoff-initializer dispatch, and no
initializer or numeric local failure at its actual live dispatcher. The
installation base is bounded from the same earlier birth that retained it.

The result is intentionally limited to numeric and initializer failures;
frame, payload, grid, choice, envelope, recorder-boundary, and later physical
failures remain represented by the source dispatch outcome.
-/
theorem complete_live_numeric_domains_and_dispatch
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live r q base) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    let x := (R[k.val]'k.isLt).input
    let v := ReferenceActivePhysicalStep.liveInput x r q base
    v.registers.scoreDomainValid ∧
    v.ownedRegisters.queueDomainValid ∧
    v.ownedRegisters.previousServiceDomainValid ∧
    (∀ i, base i ≤ p.T * ConstructorDimensions.D p) ∧
    CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      v.registers v.ownedRegisters base x.time ∧
    (∃ started : CoordinatorPhaseClock.StartRoundResult p,
      CoordinatorPhaseClock.startRound p rate.eta.val x.time
        v.registers.priorClock v.registers.clockPending = .ok started ∧
      CoordinatorStartRoundCutoffDispatch.dispatch
        v.registers v.ownedRegisters base = .ok ⟨started, .success
          (if started.ledgerCommand = some (.initializeAt x.time) then
            some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
              v.registers v.ownedRegisters base x.time)
          else none)⟩) ∧
    ReferenceFirstLiveDispatchDomains.dispatchLiveNumericOutcomeSafe
      (CoordinatorRoundDispatch.dispatchLive v) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let x := record.input
  let v := ReferenceActivePhysicalStep.liveInput x r q base
  have hmassAll := ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
    rate rewards C_star C_h source
  have hmassAt := hmassAll k
  have hinputMass := hmassAt.1
  unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hinputMass
  rw [hlive] at hinputMass
  rcases hinputMass with ⟨hfastMass, hprevious⟩
  have htimeBound : x.time.val ≤ p.T := Nat.le_of_lt x.time.isLt
  have hmassTD : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores a + q.queue a ≤ p.T * D p := by
    intro a
    exact Nat.le_trans (hfastMass a)
      (Nat.mul_le_mul_right (D p) htimeBound)
  have hscore : r.scoreDomainValid := by
    intro a
    exact Nat.le_trans (Nat.le_add_right _ _) (hmassTD a)
  have hqueue : q.queueDomainValid := by
    intro a
    exact Nat.le_trans (Nat.le_add_left _ _) (hmassTD a)
  have hscoreV : v.registers.scoreDomainValid := by
    change r.scoreDomainValid
    exact hscore
  have hqueueV : v.ownedRegisters.queueDomainValid := by
    change q.queueDomainValid
    exact hqueue
  have hpreviousV : v.ownedRegisters.previousServiceDomainValid := by
    change q.previousServiceDomainValid
    exact hprevious

  have hretained := ReferenceAssignmentRetainedBirthProvenance.complete_coordinator_retained_birth
    rate rewards C_star C_h source k
  dsimp only at hretained
  rw [hlive] at hretained
  rcases hretained.1 with ⟨b, hbk, hbirth, hbaseAtBirth⟩
  obtain ⟨beta, hinstd, _hqueueCredit, hcredit, _hdownCredit⟩ :=
    ReferenceAssignmentMassComposer.complete_assignment_birth_mass
      rate rewards C_star C_h source b r.payload hbirth
  have hbaseEq : base = beta := by
    cases hcoord : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[b.val]'b.isLt).output.preparation.coordinator with
    | first outcome =>
        cases outcome with
        | chosen installed _ =>
            have hbase : base = installed.followerBaseScore := by
              simpa [hcoord, ActiveRoundActions.Follower,
                PublicDiscreteDraws.followerCount] using hbaseAtBirth
            have hβ : installed.followerBaseScore = beta := by
              have hsome :
                  some installed.followerBaseScore = some beta := by
                simpa [ReferenceAssignmentCollectionMassSteps.installedBaseScore,
                  hcoord, ActiveRoundActions.Follower,
                  PublicDiscreteDraws.followerCount] using hinstd
              exact Option.some.inj hsome
            exact hbase.trans hβ
        | _ => simp [hcoord] at hbaseAtBirth
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | laterChosen _ _ _ _ _ _ _ _ _ installed _ =>
            have hbase : base = installed.retainedBaseScore := by
              simpa [hcoord, ActiveRoundActions.Follower,
                PublicDiscreteDraws.followerCount] using hbaseAtBirth
            have hβ : installed.retainedBaseScore = beta := by
              have hsome : some installed.retainedBaseScore = some beta := by
                simpa [ReferenceAssignmentCollectionMassSteps.installedBaseScore,
                  hcoord, ActiveRoundActions.Follower,
                  PublicDiscreteDraws.followerCount] using hinstd
              exact Option.some.inj hsome
            exact hbase.trans hβ
        | _ => simp [hcoord] at hbaseAtBirth
    | _ => simp [hcoord] at hbaseAtBirth
  have hbaseDomain : ∀ i, base i ≤ p.T * D p := by
    intro i
    rw [hbaseEq]
    have hbaseCredit : beta i ≤ beta i +
        r.payload.queues (r.payload.assignment.assigned i) := Nat.le_add_right _ _
    have htime : r.payload.sigma.val ≤ p.T := Nat.le_of_lt r.payload.sigma.isLt
    exact Nat.le_trans (Nat.le_trans hbaseCredit (hcredit i))
      (Nat.mul_le_mul_right (D p) htime)

  have hclockAt := complete_suffix_member_clockAt rate rewards C_star C_h source k
  have hclockLive := hclockAt
  simp only [ReferenceCoordinatorClockDomains.clockAt, hlive] at hclockLive
  rcases hclockLive with
    ⟨_hstoredTime, hclockValid, hσ, _hu, hgrid, hstartBefore,
      hbeforeGrid, _hfresh⟩
  have hnext : x.time.val + 1 ≤ r.gridBoundary :=
    Nat.succ_le_of_lt hbeforeGrid
  let currentRegisters := ReferenceActivePhysicalStep.liveRegistersAt r x.time
  let currentOwned := ReferenceActivePhysicalStep.liveOwnedAt r q x.time
  have hscoreCurrent : currentRegisters.scoreDomainValid := by
    change r.scoreDomainValid
    exact hscore
  have hmassCurrent : ∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      currentRegisters.complementScores a + currentOwned.queue a ≤ p.T * D p := by
    intro a
    simpa [currentRegisters, currentOwned,
      ReferenceActivePhysicalStep.liveRegistersAt,
      ReferenceActivePhysicalStep.liveOwnedAt] using hmassTD a
  have hpreviousCurrent : currentOwned.previousServiceDomainValid := by
    change q.previousServiceDomainValid
    exact hprevious
  have hdomainsOriginal := initializationDomainValid_of_original_prefix_domains
    currentRegisters currentOwned base r.payload.sigma.val x.time
    hσ hgrid rfl hstartBefore hnext hclockValid hscoreCurrent hmassCurrent
    hpreviousCurrent hbaseDomain
  have hdomains : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      v.registers v.ownedRegisters base x.time := by
    simpa [v, ReferenceActivePhysicalStep.liveInput,
      currentRegisters, currentOwned] using hdomainsOriginal

  have hstarted := ReferenceCoordinatorClockDomains.live_dispatch_startRound_success
    r q base hlive hclockAt
  obtain ⟨started, hstart⟩ := hstarted
  have hstartV : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      v.registers.priorClock v.registers.clockPending = .ok started := by
    simpa [v, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt] using hstart
  have htimeV : v.registers.time = x.time := rfl
  have hchecked :
      ∃ started : CoordinatorPhaseClock.StartRoundResult p,
        CoordinatorPhaseClock.startRound p rate.eta.val x.time
          v.registers.priorClock v.registers.clockPending = .ok started ∧
        CoordinatorStartRoundCutoffDispatch.dispatch
          v.registers v.ownedRegisters base = .ok ⟨started, .success
            (if started.ledgerCommand = some (.initializeAt x.time) then
              some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                v.registers v.ownedRegisters base x.time)
            else none)⟩ := by
    refine ⟨started, hstartV, ?_⟩
    cases hcommand : started.ledgerCommand with
    | none =>
        have hno : ∀ time, started.ledgerCommand ≠ some (.initializeAt time) := by
          intro time
          simp [hcommand]
        simpa [hcommand] using
          (CoordinatorStartRoundCutoffDispatch.dispatch_no_initialization
            v.registers v.ownedRegisters base started hstartV hno)
    | some command =>
        cases command with
        | initializeAt time =>
            have htime := CoordinatorRoundDispatch.startRound_initializeAt_time
              v.registers.time time v.registers.priorClock v.registers.clockPending
              started hstartV hcommand
            subst time
            simpa [hcommand, htimeV] using
              (CoordinatorStartRoundCutoffDispatch.dispatch_initializeAt_success
                v.registers v.ownedRegisters base started hstartV hcommand hdomains)
        | accumulateLocalServiceAt time =>
            have hno : ∀ otherTime,
                started.ledgerCommand ≠ some (.initializeAt otherTime) := by
              intro otherTime
              simp [hcommand]
            simpa [hcommand] using
              (CoordinatorStartRoundCutoffDispatch.dispatch_no_initialization
                v.registers v.ownedRegisters base started hstartV hno)
  have hdispatch :
      ∃ dispatched,
        CoordinatorStartRoundCutoffDispatch.dispatch
          v.registers v.ownedRegisters base = .ok dispatched ∧
        ∃ initialization,
          dispatched.collectionInitialization = .success initialization := by
    rcases hchecked with ⟨started, hstart, hdispatch⟩
    refine ⟨⟨started, .success
      (if started.ledgerCommand = some (.initializeAt x.time) then
        some (CoordinatorStartRoundCutoffDispatch.collectionStartLedger
          v.registers v.ownedRegisters base x.time)
      else none)⟩, hdispatch, ?_⟩
    exact ⟨_, rfl⟩
  have hsafe := dispatchLive_numeric_failures_excluded v hdomains hdispatch

  exact ⟨hscoreV, hqueueV, hpreviousV, hbaseDomain, hdomains, hchecked, hsafe⟩


end Bandits.Support.ReferenceCompleteLiveDispatchDomains

end
