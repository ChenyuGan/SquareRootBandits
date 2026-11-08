/-
Copyright (c) 2026 Bandits Lean formalization contributors. All rights reserved.
-/
module

public import Bandits.Support.ReferenceFirstFollowerMassBudget

import Mathlib.Data.List.TakeWhile

/-!
# Actual first-assignment DOWN recovery guard

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-60`,
`06_interruptions.tex:192-209,246-275,327-348`,
`04_slow_fast_learner.tex:143-175`, and `05_binary_transport.tex:426-431`
under `sources/zip4/manuscript/`.

The original physical run, whole public rows, selected index, rewards and
retained pre-effect diagnostics determine every recovery input. Arithmetic
replay guards are proved before recovery is evaluated. This internal result
establishes neither later assignment mass nor global safety or regret.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceDownReception
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.QueueReplay
open Bandits.Support.ReferenceAssignmentPayloadPersistence

namespace Bandits.Support.ReferenceFirstDownRecoveryBudget

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev Record {p : Parameters} {rate : RateInput p} :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownRecord {p : Parameters} {rate : RateInput p} :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters} {rate : RateInput p}

private theorem replay_mass_after_arrivals (capacity D : ℕ)
    (initial : ℕ × ℕ) (arrivals : List ℕ)
    (harrivals : ∀ a ∈ arrivals, a ≤ D) :
    (QueueReplay.replay capacity initial (arrivals.map fun a => (true, a))).1 +
        (QueueReplay.replay capacity initial (arrivals.map fun a => (true, a))).2 ≤
      initial.1 + initial.2 + arrivals.length * D := by
  induction arrivals generalizing initial with
  | nil => simp [QueueReplay.replay]
  | cons a rest ih =>
      have ha := harrivals a List.mem_cons_self
      have htail : ∀ x ∈ rest, x ≤ D := by
        intro x hx
        exact harrivals x (List.mem_cons_of_mem _ hx)
      have hstep :
          (QueueReplay.transition capacity initial (true, a)).1 +
              (QueueReplay.transition capacity initial (true, a)).2 =
            initial.1 + initial.2 + a := by
        simp [QueueReplay.transition]
        omega
      change
        (QueueReplay.replay capacity initial ((true, a) ::
          rest.map fun x => (true, x))).1 +
            (QueueReplay.replay capacity initial ((true, a) ::
              rest.map fun x => (true, x))).2 ≤
          initial.1 + initial.2 + (rest.length + 1) * D
      rw [QueueReplay.replay, List.foldl_cons]
      have hnext := ih (QueueReplay.transition capacity initial (true, a)) htail
      calc
        _ ≤ (QueueReplay.transition capacity initial (true, a)).1 +
              (QueueReplay.transition capacity initial (true, a)).2 + rest.length * D := by
          simpa only [QueueReplay.replay] using hnext
        _ = initial.1 + initial.2 + a + rest.length * D := by rw [hstep]
        _ ≤ initial.1 + initial.2 + (rest.length + 1) * D := by
          have hadd : (rest.length + 1) * D = rest.length * D + D := by
            rw [Nat.add_mul, one_mul]
          rw [hadd]
          omega

private theorem checkedCalendarReplay_success_of_mass
    (D T capacity offset elapsed : ℕ)
    (current : ActiveFollowerDownAcceptance.ReplayRegisters)
    (arrivalAt : ℕ → ℕ) (rounds : List ℕ)
    (hscore : current.registers.1 ≤ elapsed * D)
    (hbacklog : current.registers.2 ≤ elapsed * D)
    (hlast : current.lastService ≤ D)
    (hmass : current.registers.1 + current.registers.2 ≤ elapsed * D)
    (hcapacity : capacity ≤ D)
    (harrival : ∀ r ∈ rounds, arrivalAt r ≤ D)
    (hspan : elapsed + rounds.length ≤ T) :
    ∃ final, ActiveFollowerDownAcceptance.checkedCalendarReplay D (T * D) capacity offset
        current arrivalAt rounds = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (elapsed + rounds.length) * D ∧
      final.lastService ≤ D := by
  induction rounds generalizing current offset elapsed with
  | nil =>
      have htime : elapsed ≤ T := by omega
      have hqueue : current.registers.1 ≤ T * D := by
        exact hscore.trans (Nat.mul_le_mul_right D htime)
      have hbacklog' : current.registers.2 ≤ T * D := by
        exact hbacklog.trans (Nat.mul_le_mul_right D htime)
      have hdomain : ActiveFollowerDownAcceptance.replay_register_domain D (T * D) current :=
        ⟨hqueue, hlast, hbacklog'⟩
      refine ⟨current, ?_, ?_, hlast⟩
      · simp [ActiveFollowerDownAcceptance.checkedCalendarReplay, hdomain]
      · simpa using hmass
  | cons r rest ih =>
      have ha := harrival r List.mem_cons_self
      have htail : ∀ u ∈ rest, arrivalAt u ≤ D := by
        intro u hu
        exact harrival u (List.mem_cons_of_mem _ hu)
      let service := ActiveFollowerDownAcceptance.replayService capacity current (true, arrivalAt r)
      let next := QueueReplay.transition capacity current.registers (true, arrivalAt r)
      have hservice : service ≤ D := by
        dsimp [service, ActiveFollowerDownAcceptance.replayService]
        exact (Nat.min_le_left _ _).trans hcapacity
      have hmin : min capacity (current.registers.2 + arrivalAt r) ≤
          current.registers.2 + arrivalAt r := Nat.min_le_right _ _
      have hnextMass : next.1 + next.2 ≤ (elapsed + 1) * D := by
        have hconserve : next.1 + next.2 = current.registers.1 +
            current.registers.2 + arrivalAt r := by
          dsimp [next, QueueReplay.transition]
          omega
        have hmul : (elapsed + 1) * D = elapsed * D + D := by
          rw [Nat.add_mul, one_mul]
        rw [hconserve, hmul]
        omega
      have hnextScore : next.1 ≤ (elapsed + 1) * D :=
        (Nat.le_add_right _ _).trans hnextMass
      have hnextBacklog : next.2 ≤ (elapsed + 1) * D :=
        (Nat.le_add_left _ _).trans hnextMass
      have htime : elapsed + 1 ≤ T := by
        have : elapsed + (r :: rest).length ≤ T := hspan
        simp only [List.length_cons] at this
        omega
      have hnextBound : (elapsed + 1) * D ≤ T * D :=
        Nat.mul_le_mul_right D htime
      have hdomain : ActiveFollowerDownAcceptance.replay_register_domain D (T * D) current := by
        refine ⟨?_, hlast, ?_⟩
        · exact hscore.trans (Nat.mul_le_mul_right D (by omega))
        · exact hbacklog.trans (Nat.mul_le_mul_right D (by omega))
      have hscoreCheck : next.1 ≤ T * D := hnextScore.trans hnextBound
      have hbacklogCheck : next.2 ≤ T * D := hnextBacklog.trans hnextBound
      have hscoreGuard : current.registers.1 +
          min capacity (current.registers.2 + arrivalAt r) ≤ T * D := by
        simpa [next, QueueReplay.transition] using hscoreCheck
      have hqueuePlusArrival : current.registers.2 + arrivalAt r ≤ (elapsed + 1) * D := by
        have hmul : (elapsed + 1) * D = elapsed * D + D := by
          rw [Nat.add_mul, one_mul]
        rw [hmul]
        omega
      have hbacklogGuard : current.registers.2 + arrivalAt r ≤
          T * D + min capacity (current.registers.2 + arrivalAt r) := by
        exact (hqueuePlusArrival.trans hnextBound).trans (Nat.le_add_right _ _)
      have hupdate : ActiveFollowerDownAcceptance.checkedReplayUpdate D (T * D) capacity
          current (true, arrivalAt r) = .ok ⟨next, service⟩ := by
        simp [ActiveFollowerDownAcceptance.checkedReplayUpdate,
          ActiveFollowerDownAcceptance.replayService, next, service,
          QueueReplay.transition, ha, hcapacity, hscoreGuard, hbacklogGuard]
      have htailspan : elapsed + 1 + rest.length ≤ T := by
        simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hspan
      obtain ⟨final, hfinal, hfinalMass, hfinalLast⟩ := ih
        (offset + 1) (elapsed + 1) ⟨next, service⟩
        hnextScore hnextBacklog hservice hnextMass htail htailspan
      refine ⟨final, ?_, ?_, hfinalLast⟩
      · simpa [ActiveFollowerDownAcceptance.checkedCalendarReplay, hdomain, hupdate] using hfinal
      · calc
          final.registers.1 + final.registers.2 ≤ (elapsed + 1 + rest.length) * D :=
            hfinalMass
          _ = (elapsed + (rest.length + 1)) * D := by
            congr 1
            omega

private theorem sparseBufferContribution_zero_of_no_key
    (d : ℕ) (D : ℝ) (eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hno : ∀ saved ∈ buffer, ¬ (saved.calendarRound = r ∧ saved.pilot = arm)) :
    sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => rfl
  | cons saved rest ih =>
      have hhead : ¬ (saved.calendarRound = r ∧ saved.pilot = arm) :=
        hno saved List.mem_cons_self
      have htail : ∀ item ∈ rest,
          ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
        intro item hi
        exact hno item (List.mem_cons_of_mem _ hi)
      change (if saved.calendarRound = r ∧ saved.pilot = arm then
          savedContribution p.K d D eta h saved.observation saved.thinScalar else 0) +
        sparseBufferContribution d D eta h arm r rest = 0
      rw [ite_eq_right hhead, zero_add]
      exact ih htail

private theorem sparseBufferContribution_le_of_unique_key
    (d D : ℕ) (eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hkeys : (buffer.map fun saved => (saved.calendarRound, saved.pilot)).Nodup)
    (hcontribution : ∀ saved ∈ buffer,
      saved.calendarRound = r → saved.pilot = arm →
        savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar ≤ D) :
    sparseBufferContribution d (D : ℝ) eta h arm r buffer ≤ D := by
  classical
  induction buffer with
  | nil => simp [sparseBufferContribution]
  | cons saved rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hkeys
      have htail : ∀ item ∈ rest,
          item.calendarRound = r → item.pilot = arm →
            savedContribution p.K d (D : ℝ) eta h item.observation item.thinScalar ≤ D := by
        intro item hitem hround hpilot
        exact hcontribution item (List.mem_cons_of_mem _ hitem) hround hpilot
      by_cases hkey : saved.calendarRound = r ∧ saved.pilot = arm
      · have hnotTail : ∀ item ∈ rest,
            ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
          intro item hitem hitemKey
          apply hkeys.1
          apply List.mem_map.mpr
          exact ⟨item, hitem,
            Prod.ext (hitemKey.1.trans hkey.1.symm) (hitemKey.2.trans hkey.2.symm)⟩
        have hone := sparseBufferContribution_zero_of_no_key d (D : ℝ) eta h arm r rest hnotTail
        change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_left hkey, hone]
        exact hcontribution saved List.mem_cons_self hkey.1 hkey.2
      · change (if saved.calendarRound = r ∧ saved.pilot = arm then
            savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar else 0) +
          sparseBufferContribution d (D : ℝ) eta h arm r rest ≤ D
        rw [ite_eq_right hkey, zero_add]
        exact ih hkeys.2 htail

private theorem bufferArrival_le_D
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (r : ℕ) :
    ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged r ≤ D p := by
  change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ)
    rate.eta.val M.val.h (PrelaunchBufferRecovery.downArm rate.eta M) r logged.buffer ≤ D p
  apply sparseBufferContribution_le_of_unique_key
    (d := p.m - 1) (D := D p) (eta := rate.eta.val) (h := M.val.h)
    (arm := PrelaunchBufferRecovery.downArm rate.eta M) (r := r)
    (buffer := logged.buffer)
    (ActiveFollowerLifecycle.localBufferValid_keys_nodup hvalid)
  intro saved hsaved hround harm
  by_cases hthin : saved.thinScalar.1 ≤
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * (((2 : ℝ) ^ M.val.h)⁻¹)) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  · rw [SparseCalendarReplay.savedContribution_eq_floor_of_le
      p.K (p.m - 1) (D p : ℝ) rate.eta.val M.val.h saved.observation
      saved.thinScalar hthin]
    obtain ⟨own, hown⟩ := ActiveFollowerLifecycle.localBufferValid_observation_typed
      hvalid saved hsaved
    have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_le_D rate.eta M own
    have hsame := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor rate.eta M own
    rw [hown] at hsame
    rw [hsame] at hfloor
    exact hfloor
  · simp [SparseCalendarReplay.savedContribution, hthin]

private theorem checkedRecovery_budget_of_zero_queue_and_valid_buffer
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hell : M.val.q = 0)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (ell : ℕ) (hlen : ell - M.val.sigma ≤ p.T) :
    ∃ final, ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (ell - M.val.sigma) * D p ∧
      final.lastService ≤ D p ∧
      ∀ j, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell).take j) =
            .ok middle ∧
        middle.registers.1 + middle.registers.2 ≤ j * D p := by
  let arrivals := ActiveFollowerDownAcceptance.recoveryArrivals p rate M logged ell
  have harrivals : ∀ a ∈ arrivals, a ≤ D p := by
    intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact bufferArrival_le_D M logged hvalid r
  have hlength := ActiveFollowerDownAcceptance.recoveryRounds_length p rate M ell
  have hrounds : (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).length ≤ p.T := by
    rw [ActiveFollowerDownAcceptance.recoveryRounds_length]
    exact hlen
  have hcapacity := ActiveFollowerDownAcceptance.four_n_le_D p rate
  let current : ActiveFollowerDownAcceptance.ReplayRegisters := ⟨(0, 0), 0⟩
  obtain ⟨final, hchecked, hmass, hlast⟩ := checkedCalendarReplay_success_of_mass
    (D p) p.T (4 * rate.n) 0 0 current
    (ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged)
    (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell)
    (by simp [current]) (by simp [current]) (by simp [current]) (by simp [current])
    hcapacity
    (by
      intro r hr
      exact bufferArrival_le_D M logged hvalid r)
    (by simpa only [Nat.zero_add] using hrounds)
  have hfinal : ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final := by
    rw [ActiveFollowerDownAcceptance.checkedRecovery, hell]
    exact hchecked
  have hmass' : final.registers.1 + final.registers.2 ≤
      (ell - M.val.sigma) * D p := by
    simpa only [ActiveFollowerDownAcceptance.recoveryArrivals,
      ActiveFollowerDownAcceptance.recoveryRounds, List.length_map,
      SparseCalendarReplay.sparseCalendarRounds_length, Nat.zero_add] using hmass
  refine ⟨final, hfinal, hmass', hlast, ?_⟩
  intro j
  obtain ⟨middle, hprefix, _, hregisters⟩ :=
    ActiveFollowerDownAcceptance.checkedRecovery_success_prefix p rate M logged ell final hfinal j
  have hregisters' : middle.registers =
      QueueReplay.replay (4 * rate.n) (0, 0)
        ((arrivals.take j).map fun a => (true, a)) := by
    simpa [ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals, List.map_take, hell,
      arrivals] using hregisters
  have hprefixMass := replay_mass_after_arrivals (4 * rate.n) (D p) (0, 0)
    (arrivals.take j) (by
      intro a ha
      exact harrivals a (List.mem_of_mem_take ha))
  have htake : (arrivals.take j).length ≤ j := List.length_take_le _ _
  have hprefixMass' :
      (QueueReplay.replay (4 * rate.n) (0, 0)
        ((arrivals.take j).map fun a => (true, a))).1 +
        (QueueReplay.replay (4 * rate.n) (0, 0)
          ((arrivals.take j).map fun a => (true, a))).2 ≤
        (arrivals.take j).length * D p := by
    simpa using hprefixMass
  have hbound : middle.registers.1 + middle.registers.2 ≤ j * D p := by
    rw [hregisters']
    exact hprefixMass'.trans (Nat.mul_le_mul_right _ htake)
  refine ⟨middle, ?_, hbound⟩
  simpa [ActiveFollowerDownAcceptance.checkedRecovery,
    ActiveFollowerDownAcceptance.recoveryQueueRecords, hell] using hprefix

private theorem selectionAt_payload (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (selected : Selection x)
    (h : selectionAt x payload started time weights arm = some selected) :
    selected.view.payload = payload := by
  unfold selectionAt at h
  split at h
  · cases h; rfl
  · cases h

private theorem live_step_payload (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hc : x.state.coordinator = .live r q base)
    (hcutoff : ReferenceCollectionPhaseHistory.cutoffChosen x = false) :
    (∀ selected, (prepare x).coordinator.selection = some selected →
      selected.view.payload = r.payload) ∧
    ((ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ next owned, (ReferenceActivePhysicalStep.step x).next.coordinator = .live next owned base ∧
        next.payload = r.payload) := by
  have hd : (prepare x).coordinator = .live r q base
      (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
    change dispatch x = _
    simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch]
    rfl
  have he := observeCoordinator_live_equation (prepare x) r q base _ hd
  cases ho : CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) with
  | clockFailure failure hfailure =>
      constructor
      · intro selected hs
        simp only [hd, ho, DispatchCut.selection] at hs
        cases hs
      · left
        simp only [ReferenceActivePhysicalStep.step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure]
  | initializerFailure dispatched hstart checked hchecked =>
      constructor
      · intro selected hs
        simp only [hd, ho, DispatchCut.selection] at hs
        cases hs
      · left
        simp only [ReferenceActivePhysicalStep.step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure]
  | localFailure dispatched hstart reason =>
      constructor
      · intro selected hs
        simp only [hd, ho, DispatchCut.selection] at hs
        cases hs
      · left
        simp only [ReferenceActivePhysicalStep.step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure]
  | cutoffChosen =>
      simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hd, ho,
        Bool.true_eq_false] at hcutoff
  | continuingChosen dispatched hstart continuation arm =>
      constructor
      · intro selected hs
        rw [hd, ho] at hs
        exact selectionAt_payload x r.payload dispatched.startResult x.time
          (liveRegistersAt r x.time).complementWeights arm selected hs
      · cases hsel : (DispatchCut.live r q base
            (.continuingChosen dispatched hstart continuation arm)).selection with
        | none =>
            left
            simp only [ReferenceActivePhysicalStep.step, he, ho, hsel, ite_true, coordinatorFailure]
        | some selected =>
            have ht := ReferenceFirstLiveConfirmationHistory.livePostChoice_frame x
              (prepare x) (liveRegistersAt r x.time) (liveOwnedAt r q x.time)
              base dispatched.startResult
            have hnext : (ReferenceActivePhysicalStep.step x).next.coordinator =
                (livePostChoice (prepare x) (liveRegistersAt r x.time)
                  (liveOwnedAt r q x.time) base dispatched.startResult).configuration := by
              change (prepare x).observeCoordinator.configuration = _
              rw [he, ho, hsel]
              rfl
            rcases ht with hdagger | ⟨next, owned, hn, _, _⟩
            · exact Or.inl (hnext.trans hdagger)
            · have hn' := hnext.trans hn
              refine Or.inr ⟨next, owned, hn', ?_⟩
              have hclass := ReferenceAssignmentPayloadChronology.actualStep_payload_classification x
              rcases hclass with hnone | ⟨old, hold, hout⟩ | ⟨fresh, hb, hout⟩
              · simp only [hn', storedPayload] at hnone
                cases hnone
              · have hold' : old = r.payload := by
                  simpa only [hc, storedPayload, Option.some.injEq] using hold.symm
                have hout' : next.payload = old := by
                  simpa only [hn', storedPayload, Option.some.injEq] using hout
                exact hout'.trans hold'
              · simp only [InstallationBirth, ReferenceAssignmentPayloadChronology.actualStepRecord, ReferenceActivePhysicalStep.step, hd, ho] at hb

private theorem connected_dagger_no_selection
    {initial final : ReferenceActivePhysicalStep.State p rate} (records : List (Record (p := p) (rate := rate)))
    (chain : Connected initial records final) (hd : initial.coordinator = .dagger)
    (record : Record (p := p) (rate := rate)) (hr : record ∈ records) :
    record.output.preparation.coordinator.selection = none := by
  induction records generalizing initial with
  | nil => cases hr
  | cons head rest ih =>
      obtain ⟨hpre, hrest⟩ := chain
      have hc : head.input.state.coordinator = .dagger := by rw [hpre]; exact hd
      rcases List.mem_cons.mp hr with heq | hr
      · subst record
        rw [head.output_eq]
        simp only [ReferenceActivePhysicalStep.step, prepare, dispatch, hc, DispatchCut.selection]
      · apply ih hrest _ hr
        rw [head.output_eq]
        exact (step_coordinator_dagger head.input hc).1

private theorem connected_live_selected_payload
    {initial final : ReferenceActivePhysicalStep.State p rate} (records : List (Record (p := p) (rate := rate)))
    (chain : Connected initial records final) (payload : Payload rate)
    (hstate : initial.coordinator = .dagger ∨
      ∃ r q base, initial.coordinator = .live r q base ∧ r.payload = payload)
    (hno : ∀ r ∈ records, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false)
    (record : Record (p := p) (rate := rate)) (hr : record ∈ records)
    (selected : Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected) :
    selected.view.payload = payload := by
  induction records generalizing initial with
  | nil => cases hr
  | cons head rest ih =>
      rcases hstate with hd | ⟨r, q, base, hc, hp⟩
      · rw [connected_dagger_no_selection (head :: rest) chain hd record hr] at hs
        cases hs
      · obtain ⟨hpre, hrest⟩ := chain
        have hc' : head.input.state.coordinator = .live r q base := by rw [hpre]; exact hc
        have hf := live_step_payload head.input r q base hc' (hno head List.mem_cons_self)
        rcases List.mem_cons.mp hr with heq | hr
        · subst record
          have hs' : (prepare head.input).coordinator.selection = some selected := by
            simpa only [head.output_eq, ReferenceActivePhysicalStep.step] using hs
          exact (hf.1 selected hs').trans hp
        · have hn : head.output.next.coordinator = .dagger ∨
              ∃ next owned base, head.output.next.coordinator = .live next owned base ∧
                next.payload = payload := by
            rw [head.output_eq]
            rcases hf.2 with hd | ⟨next, owned, hn, hnp⟩
            · exact Or.inl hd
            · exact Or.inr ⟨next, owned, base, hn, hnp.trans hp⟩
          exact ih hrest hn (fun r hr => hno r (List.mem_cons_of_mem _ hr)) hr

private theorem first_chosen_zero_queues (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput x) = .chosen installed arm) :
    ∀ a, installed.registers.payload.queues a = 0 := by
  classical
  have hseed := dispatchFirst_zero_seed x installed arm hchosen
  have hownedPayload (a : CanonicalFastSampling.FastArm installed.registers.payload.slowSet) :
      installed.ownedRegisters.queue a = installed.registers.payload.queues a.val := by
    have heq := dispatchFirst_chosen_installation x installed arm hchosen
    cases heq
    rfl
  intro a
  by_cases ha : a ∈ CanonicalFastSampling.fastArmFinset installed.registers.payload.slowSet
  · exact (hownedPayload ⟨a, ha⟩).symm.trans (hseed.2.1 ⟨a, ha⟩)
  · rw [dispatchFirst_chosen_installation x installed arm hchosen]
    rfl

private theorem connected_first_selected_payload
    {initial final : ReferenceActivePhysicalStep.State p rate} (head : Record (p := p) (rate := rate))
    (rest : List (Record (p := p) (rate := rate)))
    (chain : Connected initial (head :: rest) final)
    (hfirst : initial.coordinator = .first)
    (hno : ∀ r ∈ head :: rest, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false)
    (record : Record (p := p) (rate := rate)) (hr : record ∈ head :: rest)
    (selected : Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected) :
    InstallationBirth head selected.view.payload ∧
      selected.view.payload.sigma.val = head.input.time.val ∧
      ∀ a, selected.view.payload.queues a = 0 := by
  obtain ⟨hpre, hrest⟩ := chain
  have hc : head.input.state.coordinator = .first := by rw [hpre]; exact hfirst
  have hd : (prepare head.input).coordinator = .first
      (CoordinatorRoundDispatch.dispatchFirst (firstInput head.input)) := dispatch_first head.input hc
  have he := observeCoordinator_first_equation (prepare head.input) _ hd
  have hselected : record.output.preparation.coordinator.selection ≠ none := by rw [hs]; exact Option.some_ne_none _
  cases ho : CoordinatorRoundDispatch.dispatchFirst (firstInput head.input) with
  | choiceDomainFailure installed | recorderBoundaryFailure installed | choiceRejected installed =>
      have hn : head.output.next.coordinator = .dagger := by
        rw [head.output_eq]
        simp only [ReferenceActivePhysicalStep.step, he, ho, DispatchCut.selection, ite_true, coordinatorFailure]
      rcases List.mem_cons.mp hr with heq | hr
      · subst record
        apply False.elim
        apply hselected
        rw [head.output_eq]
        simp only [ReferenceActivePhysicalStep.step, hd, ho, DispatchCut.selection]
      · exact (hselected (connected_dagger_no_selection rest hrest hn record hr)).elim
  | chosen installed arm =>
      have hb : InstallationBirth head installed.registers.payload := by
        have hactual : ReferenceAssignmentPayloadChronology.actualStepRecord head.input = head := by
          cases head with
          | mk input output output_eq => cases output_eq; rfl
        simpa only [hactual] using
          ReferenceAssignmentPayloadChronology.actualFirstChosen_installationBirth
            head.input hc installed arm ho
      have ht := ReferenceAssignmentPayloadChronology.installationBirth_time_eq head
        installed.registers.payload hb
      have hz := first_chosen_zero_queues head.input installed arm ho
      have hp : selected.view.payload = installed.registers.payload := by
        rcases List.mem_cons.mp hr with heq | hr
        · subst record
          have hs' : (prepare head.input).coordinator.selection = some selected := by
            simpa only [head.output_eq, ReferenceActivePhysicalStep.step] using hs
          rw [hd, ho] at hs'
          exact selectionAt_payload head.input installed.registers.payload
            installed.startRoundResult installed.registers.time
            installed.registers.complementWeights arm selected hs'
        · have hn : head.output.next.coordinator = .dagger ∨
              ∃ r q base, head.output.next.coordinator = .live r q base ∧
                r.payload = installed.registers.payload := by
            rw [head.output_eq]
            cases hsel : (DispatchCut.first (.chosen installed arm)).selection with
            | none =>
                left
                simp only [ReferenceActivePhysicalStep.step, he, ho, hsel, ite_true, coordinatorFailure]
            | some sel =>
                have hframe := ReferenceFirstLiveConfirmationHistory.livePostChoice_frame
                  head.input (prepare head.input) installed.registers installed.ownedRegisters
                  installed.followerBaseScore installed.startRoundResult
                have hnext : (ReferenceActivePhysicalStep.step head.input).next.coordinator =
                    (livePostChoice (prepare head.input) installed.registers installed.ownedRegisters
                      installed.followerBaseScore installed.startRoundResult).configuration := by
                  change (prepare head.input).observeCoordinator.configuration = _
                  rw [he, ho, hsel]
                  rfl
                rcases hframe with hdagger | ⟨next, owned, hn, hnp, _⟩
                · exact Or.inl (hnext.trans hdagger)
                · exact Or.inr ⟨next, owned, installed.followerBaseScore, hnext.trans hn, hnp⟩
          exact connected_live_selected_payload rest hrest installed.registers.payload hn
            (fun r hr => hno r (List.mem_cons_of_mem _ hr)) record hr selected hs
      rw [hp]
      exact ⟨hb, ht, hz⟩

private theorem reference_diagnostic_parse
    (view : Option (ChoiceTimeView p rate.eta)) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (M : DownRecord (p := p) (rate := rate))
    (hcomp : (referenceDownCut p view i row t observation rate logged).rawComparison = some true)
    (hparse : (referenceDownCut p view i row t observation rate logged).ordinaryParse = some M)
    (haccept : (referenceDownCut p view i row t observation rate logged).ordinaryAcceptance) :
    ordinaryParse p rate (expectedDownFlatWord view i row t) = some M ∧
      OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
        (acceptedStart logged) (t.val + 1) M := by
  unfold referenceDownCut at hcomp
  split at hcomp
  · rename_i hselected
    split at hcomp
    · rename_i hstatus
      split at hcomp
      · rename_i hregisters
        split at hcomp
        · rename_i hbatch
          split at hcomp
          · rename_i hbuffer
            dsimp only at hcomp
            split at hcomp
            · rename_i hmatches
              have hp : ordinaryParse p rate
                  (currentDecodeStep p i row t observation rate logged).2 = some M := by
                simpa only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
                  dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
                  dite_eq_left hmatches] using hparse
              have ha : OrdinaryMessageCodec.acceptDown
                  (ReferencePrelaunchFollower.codecParams p rate.eta)
                  (acceptedStart logged) (t.val + 1) M := by
                simpa only [referenceDownCut, dite_eq_left hselected, dite_eq_left hstatus,
                  dite_eq_left hregisters, dite_eq_left hbatch, dite_eq_left hbuffer,
                  dite_eq_left hmatches, hp, ordinaryLocalAcceptanceTest] using haccept
              exact ⟨hmatches ▸ hp, ha⟩
            · cases hcomp
          · cases hcomp
        · cases hcomp
      · cases hcomp
    · cases hcomp
  · cases hcomp

private theorem expected_parse_payload
    (view : Option (ChoiceTimeView p rate.eta)) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (M : DownRecord (p := p) (rate := rate))
    (hparse : ordinaryParse p rate (expectedDownFlatWord view i row t) = some M) :
    ∃ actual, view = some actual ∧ M = actual.payload.downRecord i := by
  classical
  cases view with
  | none =>
      simp only [expectedDownFlatWord, ordinaryParse, OrdinaryMessageCodec.parseDown] at hparse
      cases hparse
  | some actual =>
      by_cases hchannel : CoordinatorLocalArmChoice.coordinatorArmChoice actual.payload
          actual.pendingAtChoice actual.cutoff t actual.complementWeights row ≠ none ∧
          selectedDownSenderBranch actual i row t
      · have hp : ordinaryParse p rate
            (some (CoordinatorLocalArmChoice.storedDownFlatWord actual.payload i)) = some M := by
          simpa only [expectedDownFlatWord, ite_eq_left hchannel] using hparse
        have hf : ordinaryParse p rate
            (some (CoordinatorLocalArmChoice.storedDownFlatWord actual.payload i)) =
              some (actual.payload.downRecord i) := by
          unfold ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
          change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
            (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
              ((OrdinaryMessageCodec.wordEquivFlat _) (actual.payload.downWord i)))) = _
          exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
            (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
              ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
                (actual.payload.downWord i))).trans (actual.payload.parseDown_downWord i)
        exact ⟨actual, rfl, Option.some.inj (hp.symm.trans hf)⟩
      · simp only [expectedDownFlatWord, ite_eq_right hchannel, ordinaryParse,
          OrdinaryMessageCodec.parseDown] at hparse
        cases hparse

/-- Every retained successful choice before the first chosen cutoff carries
the whole payload born in the first physical round, with all initial queues
zero. No initial follower-register or successful-tail premise is used. -/
theorem run_first_selected_payload (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (selected : Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      ∃ birth, birth ∈ E.records ∧ birth.input.time.val = start ∧
        InstallationBirth birth selected.view.payload ∧
        selected.view.payload.sigma.val = start ∧
        (∀ a, selected.view.payload.queues a = 0) := by
  intro E W k selected hs
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have htake : W = E.records.take W.length := List.prefix_iff_eq_take.mp hprefix
  obtain ⟨endpoint, hchain⟩ : ∃ endpoint, Connected initial W endpoint := by
    by_cases hlt : W.length < E.records.length
    · refine ⟨E.records[W.length].input.state, ?_⟩
      simpa only [← htake] using
        ReferenceFollowerReplyChronology.connected_take_to_input E.connected W.length hlt
    · have heq : W = E.records := hprefix.eq_of_length_le (by omega)
      exact ⟨E.finalState, heq ▸ E.connected⟩
  have hno : ∀ r ∈ W, ReferenceCollectionPhaseHistory.cutoffChosen r.input = false := by
    intro r hr
    have hb := List.mem_takeWhile_imp hr
    simpa only [Bool.not_eq_true'] using hb
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards
    start count hspan hmode
  change E.records.map (fun r => r.input.time.val) = calendar start count at htimes
  have hnonempty : W ≠ [] := by
    intro heq
    have hk := k.isLt
    simp only [heq, List.length_nil] at hk
    omega
  obtain ⟨head, rest, hw⟩ := List.exists_cons_of_ne_nil hnonempty
  have hhead : head ∈ W := by rw [hw]; exact List.mem_cons_self
  have hpositive : 0 < E.records.length := by
    have := hprefix.length_le
    have := k.isLt
    omega
  have hpositiveMap : 0 < (E.records.map (fun r => r.input.time.val)).length := by
    simpa only [List.length_map] using hpositive
  have hfirstTime : head.input.time.val = start := by
    have he : (head :: rest)[0] = E.records[0] :=
      (hw ▸ hprefix).getElem (by simp)
    have hmap : (E.records.map (fun r => r.input.time.val))[0] = start := by
      simp only [htimes, ReferenceActivePhysicalHorizon.calendar, List.getElem_range'_1, Nat.add_zero]
    simpa only [List.getElem_map, ← he, List.getElem_cons_zero] using hmap
  have hmem : W[k.val] ∈ head :: rest := by
    simpa only [← hw] using (List.getElem_mem k.isLt : W[k.val] ∈ W)
  have hresult := connected_first_selected_payload head rest (hw ▸ hchain) hfirst
    (hw ▸ hno) W[k.val] hmem selected hs
  exact ⟨head, hprefix.sublist.subset hhead, hfirstTime, hresult.1,
    hresult.2.1.trans hfirstTime, hresult.2.2⟩

/-- A true filtered comparison and the ordinary parse/test identify the actual
first payload before recovery. Logging success supplies validity of this same
real buffer even when recording or finishing later enters dagger. -/
theorem run_first_down_diagnostic_payload (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownCutOutput p rate) (M : DownRecord (p := p) (rate := rate)),
      (W[k.val].output.followers i).downInput = some logged →
      (W[k.val].output.followers i).down = some cut →
      cut.rawComparison = some true → cut.ordinaryParse = some M → cut.ordinaryAcceptance →
      ∃ (selected : Selection W[k.val].input) (birth : Record (p := p) (rate := rate)),
        W[k.val].output.preparation.coordinator.selection = some selected ∧
        birth ∈ E.records ∧ birth.input.time.val = start ∧
        InstallationBirth birth selected.view.payload ∧
        M = selected.view.payload.downRecord i ∧
        selected.view.payload.sigma.val = start ∧
        (∀ a, selected.view.payload.queues a = 0) ∧
        M.val.sigma = start + 1 ∧ M.val.q = 0 ∧ localBufferValid logged ∧
        OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
          (acceptedStart logged) (W[k.val].input.time.val + 1) M ∧
        W[k.val].input.time.val = start + k.val := by
  intro E W k i logged cut M hlogged hdown hcomp hparse haccept
  let record := W[k.val]
  obtain ⟨choice, memory, actualLogged, _hchoice, _hstatus, hlogging, hactualLogged, hcall⟩ :=
    ReferenceFollowerSparseEmissionRecovery.actualDownDiagnostic_choice record i cut hdown
  have hsame : actualLogged = logged := Option.some.inj (hactualLogged.symm.trans hlogged)
  subst actualLogged
  have hvalid : localBufferValid logged :=
    ((ActiveFollowerLogging.checkedLogging_success_iff
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice logged).mp hlogging).2.2
  have halign := record.output.preparation.follower_alignment i
  have hcall' : cut = referenceDownCut p record.output.preparation.coordinator.downView
      i record.input.row record.input.time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged := by
    simpa only [halign.1, halign.2.1, halign.2.2.1] using hcall
  obtain ⟨hp, ha⟩ := reference_diagnostic_parse record.output.preparation.coordinator.downView
    i record.input.row record.input.time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) logged M
    (hcall' ▸ hcomp) (hcall' ▸ hparse) (hcall' ▸ haccept)
  obtain ⟨view, hview, hM⟩ := expected_parse_payload
    record.output.preparation.coordinator.downView i record.input.row record.input.time M hp
  obtain ⟨selected, hs, hsv⟩ := Option.map_eq_some_iff.mp hview
  have hM' : M = selected.view.payload.downRecord i := by simpa only [hsv] using hM
  obtain ⟨birth, hbirth, htime, hb, hsigma, hzero⟩ :=
    run_first_selected_payload initial rows J rewards start count hspan hmode hfirst k selected hs
  have hMsigma : M.val.sigma = start + 1 := by
    have hf : (selected.view.payload.downRecord i).val.sigma =
        selected.view.payload.sigma.val + 1 := rfl
    exact (congrArg (fun N : DownRecord (p := p) (rate := rate) => N.val.sigma) hM').trans
      (hf.trans (congrArg (fun n => n + 1) hsigma))
  have hMq : M.val.q = 0 :=
    (congrArg (fun N : DownRecord (p := p) (rate := rate) => N.val.q) hM').trans
      ((selected.down_initial_queue i).trans (hzero _))
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hk : k.val < E.records.length := k.isLt.trans_le hprefix.length_le
  have hkmap : k.val < (E.records.map (fun r => r.input.time.val)).length := by
    simpa only [List.length_map] using hk
  have htimes := ReferenceActivePhysicalHorizon.run_time_values initial rows J rewards
    start count hspan hmode
  change E.records.map (fun r => r.input.time.val) = ReferenceActivePhysicalHorizon.calendar start count
    at htimes
  have hcalendar : (E.records.map (fun r => r.input.time.val))[k.val] = start + k.val := by
    simp only [htimes, ReferenceActivePhysicalHorizon.calendar, List.getElem_range'_1]
  have htimek : record.input.time.val = start + k.val := by
    simpa only [List.getElem_map, ← hprefix.getElem k.isLt] using hcalendar
  exact ⟨selected, birth, hs, hbirth, htime, hb, hM', hsigma, hzero,
    hMsigma, hMq, hvalid, ha, htimek⟩

/-- Produce every checked-recovery guard at the actual pre-effect DOWN call.
The test equations select the call; neither an accepted outcome nor recovery
success is a premise. Every calendar round, including zero arrivals, is replayed.
The actual first-payload identities and elapsed-index bound remain public for
the following original-prefix mass induction. -/
theorem run_first_down_recovery_budget (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : allActiveAtStart initial start) (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownCutOutput p rate) (M : DownRecord (p := p) (rate := rate)),
      (W[k.val].output.followers i).downInput = some logged →
      (W[k.val].output.followers i).down = some cut →
      cut.rawComparison = some true → cut.ordinaryParse = some M → cut.ordinaryAcceptance →
      ∃ (selected : Selection W[k.val].input) (birth : Record (p := p) (rate := rate))
        (hstart : (downStart p rate M).val ≤ W[k.val].input.time.val),
        let ell := (acceptedCutoffScan p rate M W[k.val].input.time hstart W[k.val].input.row).endpoint
        W[k.val].output.preparation.coordinator.selection = some selected ∧
        birth ∈ E.records ∧ birth.input.time.val = start ∧
        InstallationBirth birth selected.view.payload ∧
        M = selected.view.payload.downRecord i ∧
        selected.view.payload.sigma.val = start ∧
        (∀ a, selected.view.payload.queues a = 0) ∧
        M.val.sigma = start + 1 ∧ M.val.q = 0 ∧ localBufferValid logged ∧
        W[k.val].input.time.val = start + k.val ∧
        ell ≤ W[k.val].input.time.val + 2 ∧
        W[k.val].input.time.val + 2 ≤ p.T + 1 ∧ ell ≤ p.T + 1 ∧
        ell - M.val.sigma ≤ p.T ∧ ell - M.val.sigma ≤ k.val + 1 ∧
        ∃ final, checkedRecovery p rate M logged ell = .ok final ∧
          final.registers.1 + final.registers.2 ≤ (ell - M.val.sigma) * D p ∧
          final.lastService ≤ D p ∧
          ∀ j, ∃ middle,
            checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
              ((recoveryQueueRecords p rate M logged ell).take j) = .ok middle ∧
            middle.registers.1 + middle.registers.2 ≤ j * D p := by
  intro E W k i logged cut M hlogged hdown hcomp hparse haccept
  obtain ⟨selected, birth, hs, hbirth, htime, hb, hM, hsigma, hzero,
      hMsigma, hMq, hvalid, ha, htimek⟩ :=
    run_first_down_diagnostic_payload initial rows J rewards start count hspan hmode hfirst
      k i logged cut M hlogged hdown hcomp hparse haccept
  let hstart := acceptedDownStartLE p rate M W[k.val].input.time logged ha
  let ell := (acceptedCutoffScan p rate M W[k.val].input.time hstart W[k.val].input.row).endpoint
  have hbounds := acceptedCutoff_interval_bounds p rate M W[k.val].input.time
    W[k.val].input.row logged ha
  have helltime : ell ≤ W[k.val].input.time.val + 2 := hbounds.2.1
  have hphysicalTime : W[k.val].input.time.val + 2 ≤ p.T + 1 := by
    have ht := W[k.val].input.time.isLt
    omega
  have hellT : ell ≤ p.T + 1 := hbounds.2.2.1
  have hlength : ell - M.val.sigma ≤ p.T := hbounds.2.2.2
  have hindex : ell - M.val.sigma ≤ k.val + 1 := by
    rw [hMsigma]
    have htimek' : W[k.val].input.time.val = start + k.val := htimek
    have hstep : ell ≤ start + k.val + 2 :=
      helltime.trans_eq (congrArg (fun n : ℕ => n + 2) htimek')
    omega
  obtain ⟨final, hchecked, hmass, hlast, hprefix⟩ :=
    checkedRecovery_budget_of_zero_queue_and_valid_buffer M logged hMq hvalid ell hlength
  exact ⟨selected, birth, hstart, hs, hbirth, htime, hb, hM, hsigma, hzero,
    hMsigma, hMq, hvalid, htimek, helltime, hphysicalTime, hellT, hlength, hindex,
    final, hchecked, hmass, hlast, hprefix⟩

section ActualLaunch

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)


/-- Original-source launch specialization. The initialization relation, clean
prefix, no-generated-DOWN, no-force and actual launch conditions remain
explicit. Rows, selected J, rewards and the block endpoint are the original
literal launch inputs; inherited follower registers and buffers are retained. -/
theorem actual_launched_first_down_recovery_budget (count : ℕ)
    (hspan : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      count ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let hmode : allActiveAtStart initial start := fun i =>
      ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let E := ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count hspan hmode
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ (k : Fin W.length) (i : Fin (p.m - 1))
      (logged : ReferencePrelaunchFollower.State p rate.eta)
      (cut : ReferenceDownCutOutput p rate) (M : DownRecord (p := p) (rate := rate)),
      (W[k.val].output.followers i).downInput = some logged →
      (W[k.val].output.followers i).down = some cut →
      cut.rawComparison = some true → cut.ordinaryParse = some M → cut.ordinaryAcceptance →
      ∃ (selected : Selection W[k.val].input) (birth : Record (p := p) (rate := rate))
        (hstart : (downStart p rate M).val ≤ W[k.val].input.time.val),
        let ell := (acceptedCutoffScan p rate M W[k.val].input.time hstart W[k.val].input.row).endpoint
        W[k.val].output.preparation.coordinator.selection = some selected ∧
        birth ∈ E.records ∧ birth.input.time.val = start ∧
        InstallationBirth birth selected.view.payload ∧
        M = selected.view.payload.downRecord i ∧
        selected.view.payload.sigma.val = start ∧
        (∀ a, selected.view.payload.queues a = 0) ∧
        M.val.sigma = start + 1 ∧ M.val.q = 0 ∧ localBufferValid logged ∧
        W[k.val].input.time.val = start + k.val ∧
        ell ≤ W[k.val].input.time.val + 2 ∧
        W[k.val].input.time.val + 2 ≤ p.T + 1 ∧ ell ≤ p.T + 1 ∧
        ell - M.val.sigma ≤ p.T ∧ ell - M.val.sigma ≤ k.val + 1 ∧
        ∃ final, checkedRecovery p rate M logged ell = .ok final ∧
          final.registers.1 + final.registers.2 ≤ (ell - M.val.sigma) * D p ∧
          final.lastService ≤ D p ∧
          ∀ j, ∃ middle,
            checkedReplay (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
              ((recoveryQueueRecords p rate M logged ell).take j) = .ok middle ∧
            middle.registers.1 + middle.registers.2 ≤ j * D p := by
  dsimp only
  exact run_first_down_recovery_budget _ source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards _ count hspan _
    (ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched)

end ActualLaunch

end Bandits.Support.ReferenceFirstDownRecoveryBudget

end
