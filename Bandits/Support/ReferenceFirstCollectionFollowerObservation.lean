/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferenceFirstCutoffRecordedService

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual follower observation in the first collection interval

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,258-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module proves a conditional transition for one actual post-cutoff record
of the original physical run. The local state fields are explicit inputs; the
result does not claim that those inputs hold throughout the collection prefix.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstCollectionFollowerObservation

open ConstructorDimensions
open ActiveFollowerLifecycle
open ActiveFollowerDownAcceptance
open ReferenceDownReception
open SparseCalendarReplay
open ReferenceActivePhysicalStep

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev DownRecord :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

private theorem takeWhile_length_le (α : Type) (pred : α → Bool) (xs : List α) :
    (xs.takeWhile pred).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
      by_cases hp : pred head
      · simp [List.takeWhile, hp, ih]
      · simp [List.takeWhile, hp]

private theorem getElem_takeWhile_eq (α : Type) (pred : α → Bool)
    (xs : List α) (k : ℕ) (hk : k < (xs.takeWhile pred).length) :
    (xs.takeWhile pred)[k] = xs[k]'(by
      exact Nat.lt_of_lt_of_le hk (takeWhile_length_le α pred xs)) := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons head tail ih =>
      cases hp : pred head with
      | false => simp [List.takeWhile, hp] at hk
      | true =>
          cases k with
          | zero => simp [List.takeWhile, hp]
          | succ k =>
              have htail : k < (tail.takeWhile pred).length := by
                simpa [List.takeWhile, hp] using hk
              simpa only [List.takeWhile, hp, List.getElem_cons_succ] using ih k htail

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
      have hqueue : current.registers.1 ≤ T * D :=
        hscore.trans (Nat.mul_le_mul_right D htime)
      have hbacklog' : current.registers.2 ≤ T * D :=
        hbacklog.trans (Nat.mul_le_mul_right D htime)
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

private theorem checkedRecovery_cutoff_budget
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hq : M.val.q = 0) (hvalid : localBufferValid logged)
    (ell elapsed : ℕ) (hlen : ell - M.val.sigma = elapsed)
    (hspan : elapsed ≤ p.T) :
    ∃ final, checkedRecovery p rate M logged ell = .ok final ∧
      final.registers.1 + final.registers.2 ≤ elapsed * D p ∧
      final.lastService ≤ D p := by
  have hrounds : (recoveryRounds p rate M ell).length ≤ p.T := by
    rw [recoveryRounds_length]
    rw [hlen]
    exact hspan
  let current : ReplayRegisters := ⟨(0, 0), 0⟩
  obtain ⟨final, hchecked, hmass, hlast⟩ := checkedCalendarReplay_success_of_mass
    (D p) p.T (4 * rate.n) 0 0 current
    (bufferArrivalAt p rate M logged) (recoveryRounds p rate M ell)
    (by simp [current]) (by simp [current]) (by simp [current]) (by simp [current])
    (four_n_le_D p rate)
    (fun r _ => bufferArrival_le_D M logged hvalid r)
    (by simpa only [Nat.zero_add] using hrounds)
  refine ⟨final, ?_, ?_, hlast⟩
  · rw [checkedRecovery, hq]
    exact hchecked
  · rw [recoveryRounds_length, hlen, Nat.zero_add] at hmass
    exact hmass

private theorem down_buffer_domain (s : ReferencePrelaunchFollower.State p rate.eta)
    (h : localBufferValid s) : bufferInputDomain p s.buffer := by
  refine ⟨?_, h.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.2 saved hsaved
  exact ⟨(h.1 saved hsaved).1, (h.1 saved hsaved).2, ⟨q, by omega⟩, heq⟩

private theorem parse_stored_word (payload : Payload rate) (i : Fin (p.m - 1)) :
    ordinaryParse p rate (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
      some (payload.downRecord i) := by
  unfold ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
  change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
    (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
      ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
        (payload.downWord i))).trans (payload.parseDown_downWord i)

private theorem logging_chronology
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (s logged : ReferencePrelaunchFollower.State p rate.eta)
    (hbuffer : logged.buffer = s.buffer ++ ReferencePrelaunchFollower.logAt i row alpha t own)
    (hpair : s.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hbefore : ∀ saved ∈ s.buffer, saved.calendarRound < t.val + 1) :
    logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ logged.buffer, saved.calendarRound < t.val + 2 := by
  rw [hbuffer]
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hpair, ?_, ?_⟩
    · unfold ReferencePrelaunchFollower.logAt
      split
      · exact List.pairwise_singleton _ _
      · exact List.Pairwise.nil
    · intro a ha b hb
      rw [(ActiveFollowerLogging.logAt_member_fields i row alpha t own b hb).1]
      exact hbefore a ha
  · intro saved hsaved
    rcases List.mem_append.mp hsaved with h | h
    · exact Nat.lt_trans (hbefore saved h) (by omega)
    · have ht := (ActiveFollowerLogging.logAt_member_fields i row alpha t own saved h).1
      omega

private theorem actualSelection_view
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hcoord : x.state.coordinator = .dagger ∨
      ∃ ledger saved, x.state.coordinator = .collection payload ledger saved)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.downView = none ∨
      ∃ view : ReferenceDownReception.ChoiceTimeView p rate.eta,
        (ReferenceActivePhysicalStep.prepare x).coordinator.downView = some view ∧
        view.payload = payload := by
  rcases hcoord with hdagger | ⟨ledger, saved, hcollection⟩
  · left
    change (ReferenceActivePhysicalStep.dispatch x).downView = none
    rw [ReferenceActivePhysicalStep.dispatch_dagger x hdagger]
    simp [ReferenceActivePhysicalStep.DispatchCut.downView,
      ReferenceActivePhysicalStep.DispatchCut.selection]
  · by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
      let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
      cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection input) with
      | collection outcome =>
          have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
              .collection payload ledger clock cutoff outcome := by
            change ReferenceActivePhysicalStep.dispatch x =
              .collection payload ledger clock cutoff outcome
            unfold ReferenceActivePhysicalStep.dispatch
            rw [hcollection]
            simp only [dite_eq_left hvalid]
            dsimp [cutoff, clock, input]
            rw [hdispatch]
            rfl
          cases outcome with
          | continuing core snapshot boundary scores =>
              let view : ReferenceDownReception.ChoiceTimeView p rate.eta := {
                payload := payload
                pendingAtChoice := snapshot.clockStarted.pending
                cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                  snapshot.clockStarted.clock.u
                complementWeights :=
                  CoordinatorCollectionInteractive.PreObservationInputs.weights input
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq }
              right
              refine ⟨view, ?_, rfl⟩
              rw [ReferenceActivePhysicalStep.DispatchCut.downView, hcut]
              rfl
          | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
              have hfalse := hnotLater
              unfold ReferenceCollectionPhaseHistory.laterChosen at hfalse
              rw [hcut] at hfalse
              simp at hfalse
          | _ =>
              left
              rw [ReferenceActivePhysicalStep.DispatchCut.downView, hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
    · left
      have hbad : ledger.cutoff = 0 ∨ p.T < ledger.cutoff := by omega
      rcases hbad with hzero | hlarge
      · simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hzero, hcollection, ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection]
      · simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hcollection, dite_eq_right hvalid, ReferenceActivePhysicalStep.DispatchCut.downView,
          ReferenceActivePhysicalStep.DispatchCut.selection]
        rfl

private theorem step_collection_same_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hcoord : x.state.coordinator = .collection payload ledger saved)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen x = false) :
    (ReferenceActivePhysicalStep.step x).next.coordinator = .dagger ∨
      ∃ movingLedger movingSaved,
        (ReferenceActivePhysicalStep.step x).next.coordinator =
          .collection payload movingLedger movingSaved := by
  by_cases hvalid : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
    cases hdispatch : CoordinatorRoundDispatch.dispatch (.collection input) with
    | collection outcome =>
        have hcut : (ReferenceActivePhysicalStep.prepare x).coordinator =
            .collection payload ledger clock cutoff outcome := by
          change ReferenceActivePhysicalStep.dispatch x =
            .collection payload ledger clock cutoff outcome
          unfold ReferenceActivePhysicalStep.dispatch
          rw [hcoord]
          simp only [dite_eq_left hvalid]
          dsimp [cutoff, clock, input]
          rw [hdispatch]
          rfl
        have hobs := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
          (ReferenceActivePhysicalStep.prepare x) payload ledger clock cutoff outcome hcut
        cases outcome with
        | continuing core snapshot boundary scores =>
            have hselection :
                (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff
                  (.continuing core snapshot boundary scores)).selection ≠ none := by
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            have hpost : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
                ReferenceActivePhysicalStep.collectionPostChoice
                  (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) := by
              simpa [hselection] using hobs
            have hphase := ReferenceCollectionPhaseHistory.collectionPostChoice_no_installation
              (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
            have hpayloadFrame := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
              (ReferenceActivePhysicalStep.prepare x) payload ledger snapshot.clockStarted
              (CoordinatorCollectionInteractive.PreObservationInputs.weights input
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)
            rcases hphase with hdagger | ⟨nextPayload, nextLedger, nextSaved, hnext⟩
            · left
              rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
              rw [congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost]
              exact hdagger
            · have hpayload : nextPayload = payload := by
                rw [hnext] at hpayloadFrame
                simp [ReferenceAssignmentPayloadPersistence.storedPayload] at hpayloadFrame
                exact hpayloadFrame
              right
              refine ⟨nextLedger, nextSaved, ?_⟩
              rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
              rw [congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration hpost,
                hnext, hpayload]
        | laterChosen core consistent started hstart instruction hi output hcons data installed selected =>
            have hfalse := hnotLater
            unfold ReferenceCollectionPhaseHistory.laterChosen at hfalse
            rw [hcut] at hfalse
            simp at hfalse
        | _ =>
            have hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none := by
              rw [hcut]
              simp [ReferenceActivePhysicalStep.DispatchCut.selection]
            have hselectionOut := hselection
            rw [hcut] at hselectionOut
            left
            rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
            have hfailure : (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
                ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank
                  .dispatchRejected none none := by
              simpa [hselectionOut] using hobs
            rw [hfailure]
            rfl
  · left
    rw [(ReferenceActivePhysicalStep.step_next_fields x).1]
    have hbad : ledger.cutoff = 0 ∨ p.T < ledger.cutoff := by omega
    rcases hbad with hzero | hlarge
    · simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hzero, hcoord, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.coordinatorFailure]
    · simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hvalid, hcoord, ReferenceActivePhysicalStep.PreparedRound.observeCoordinator,
        ReferenceActivePhysicalStep.coordinatorFailure]

private theorem expectedDownWord_same_payload
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (hview : view = none ∨ ∃ actual, view = some actual ∧ actual.payload = payload) :
    expectedDownFlatWord view i row t = none ∨
      expectedDownFlatWord view i row t =
        some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := by
  classical
  rcases hview with hnone | ⟨actual, hsome, hpayload⟩
  · rw [hnone]
    simp [expectedDownFlatWord]
  · rw [hsome]
    by_cases hsend :
        CoordinatorLocalArmChoice.coordinatorArmChoice actual.payload
            actual.pendingAtChoice actual.cutoff t actual.complementWeights row ≠ none ∧
          ReferenceDownReception.selectedDownSenderBranch actual i row t
    · right
      simp [expectedDownFlatWord, hsend, hpayload]
      rfl
    · left
      simp [expectedDownFlatWord, hsend]

private theorem first_collection_record_logging_down
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (start d u : ℕ)
    (hsigma : payload.sigma.val = start)
    (hqueue : ∀ i, (payload.downRecord i).val.q = 0)
    (hcutoff : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) = u)
    (hnow : u ≤ record.input.time.val) (hu : u = start + d + 1) (hdT : d ≤ p.T)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : choice.status = .unoccupied)
    (hservice : ActiveFollowerLifecycle.serviceRegistersValid p choice)
    (hbuffer : ActiveFollowerLifecycle.localBufferValid choice)
    (hbatch : ActiveFollowerLifecycle.downDecoderStateValid choice)
    (hmass : choice.S + choice.backlog ≤ d * D p)
    (hchronological : choice.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hbefore : ∀ saved ∈ choice.buffer,
      saved.calendarRound < record.input.time.val + 1)
    (hprevious : (choice.lastDown = none ∧ choice.S = 0 ∧ choice.delta = 0 ∧
        choice.backlog = 0) ∨
      choice.lastDown = some (payload.downRecord i))
    (hcoordinator : record.input.state.coordinator = .dagger ∨
      ∃ ledger saved, record.input.state.coordinator = .collection payload ledger saved)
    (hnotLater : ReferenceCollectionPhaseHistory.laterChosen record.input = false) :
    let prepared := record.output.preparation.followers.followers i
    let own := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := record.output.preparation.coordinator.downView
    ∃ logged diagnostic post,
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time (prepared.arm, own) choice =
          .ok logged ∧
      logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time (prepared.arm, own) ∧
      diagnostic = ReferenceDownReception.referenceDownCut p view i record.input.row
        record.input.time own rate logged ∧
      (ReferenceActivePhysicalStep.recordFollower view i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        prepared.arm own choice).result = .ok post ∧
      (ReferenceActivePhysicalStep.recordFollower view i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        prepared.arm own choice).downInput = some logged ∧
      (ReferenceActivePhysicalStep.recordFollower view i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        prepared.arm own choice).down = some diagnostic ∧
      post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
      post.S + post.backlog ≤ d * D p ∧
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ post.buffer, saved.calendarRound < record.input.time.val + 2) ∧
      ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
        post.lastDown = some (payload.downRecord i)) ∧
      post.initializationFailure = choice.initializationFailure := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let own := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := record.output.preparation.coordinator.downView
  obtain ⟨logged, hlog, hbufferEq, hstatusLogged, hfailureLogged, hloggedBuffer⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i record.input.row
      (record.input.state.activations i) record.input.time (prepared.arm, own)
      choice hbuffer hbefore hstatus
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame i record.input.row
    (record.input.state.activations i) record.input.time (prepared.arm, own) choice logged hlog
  have hloggedStatus : logged.status = .unoccupied := hstatusLogged.trans hstatus
  have hloggedMass : logged.S + logged.backlog ≤ d * D p := by
    simpa only [hframe.2.1, hframe.2.2.2.1] using hmass
  have hloggedService : ActiveFollowerLifecycle.serviceRegistersValid p logged := by
    rcases hservice with ⟨hS, hdelta, hbacklog⟩
    exact ⟨by simpa only [hframe.2.1] using hS,
      by simpa only [hframe.2.2.1] using hdelta,
      by simpa only [hframe.2.2.2.1] using hbacklog⟩
  have hloggedBatch : ActiveFollowerLifecycle.downDecoderStateValid logged := by
    rw [ActiveFollowerLifecycle.downDecoderStateValid, hframe.2.2.2.2.2.1]
    exact hbatch
  have hloggedValid : ActiveFollowerLifecycle.localStateDomainValid logged :=
    ⟨hloggedService, hloggedBuffer, hloggedBatch⟩
  have hchron := logging_chronology i record.input.row
    (record.input.state.activations i) record.input.time (prepared.arm, own)
    choice logged hbufferEq hchronological hbefore
  have hloggedPrevious :
      (logged.lastDown = none ∧ logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0) ∨
        logged.lastDown = some (payload.downRecord i) := by
    rcases hprevious with hnone | hsame
    · left
      rw [hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.1]
      exact hnone
    · right
      rw [hframe.1]
      exact hsame
  have hloggedFailure : logged.initializationFailure = choice.initializationFailure :=
    hframe.2.2.2.2.2.2
  have hregs : ActiveFollowerDownAcceptance.registerInputDomain p rate logged :=
    hloggedService
  have hbatchDomain : ActiveFollowerDownAcceptance.decoderInputDomain p logged.downBatch :=
    hloggedBatch
  have hbufferDomain := down_buffer_domain logged hloggedBuffer
  have hstepSpec := AffineBatchDecoder.step_spec p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        own rate logged))
    logged.downBatch record.input.time hbatchDomain.1 hbatchDomain.2
  have hstepBatch : ActiveFollowerDownAcceptance.decoderInputDomain p
      (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
        own rate logged).1 := ⟨hstepSpec.1, hstepSpec.2.1⟩
  let advanced := { logged with downBatch :=
    (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
      own rate logged).1 }
  have hadvancedValid : ActiveFollowerLifecycle.localStateDomainValid advanced :=
    ⟨hloggedService, hloggedBuffer, hstepBatch⟩
  have hadvancedMass : advanced.S + advanced.backlog ≤ d * D p := by
    simpa only [advanced, hframe.2.1, hframe.2.2.2.1] using hmass
  have hadvancedChron : advanced.buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound) := by
    simpa only [advanced] using hchron.1
  have hadvancedBefore : ∀ saved ∈ advanced.buffer,
      saved.calendarRound < record.input.time.val + 2 := by
    simpa only [advanced] using hchron.2
  have hadvancedPrevious :
      (advanced.lastDown = none ∧ advanced.S = 0 ∧ advanced.delta = 0 ∧ advanced.backlog = 0) ∨
        advanced.lastDown = some (payload.downRecord i) := by
    simpa only [advanced, hframe.1, hframe.2.1, hframe.2.2.1,
      hframe.2.2.2.1] using hloggedPrevious
  have hadvancedFailure : advanced.initializationFailure = choice.initializationFailure := by
    simpa only [advanced] using hloggedFailure
  let cut := ReferenceDownReception.referenceDownCut p view i record.input.row
    record.input.time own rate logged
  have hrecorded :
      (ReferenceActivePhysicalStep.recordFollower view i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        prepared.arm own choice).result =
      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hstatus, hlog, cut]
  have hdiagnostics := ReferenceActivePhysicalStep.recordFollower_logged view i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    prepared.arm own choice logged hstatus hlog
  have hview := actualSelection_view record.input payload hcoordinator hnotLater
  have hviewOutput : view = (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView := by
    dsimp [view]
    rw [record.output_eq]
    rfl
  have hviewActual : view = none ∨
      ∃ actual, view = some actual ∧ actual.payload = payload := by
    rw [hviewOutput]
    exact hview
  have hexpected := expectedDownWord_same_payload view payload i record.input.row
    record.input.time hviewActual
  have hsimple : ∀ post : ReferencePrelaunchFollower.State p rate.eta,
      post.status = .unoccupied →
      ActiveFollowerLifecycle.localStateDomainValid post →
      post.S + post.backlog ≤ d * D p →
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) →
      (∀ saved ∈ post.buffer, saved.calendarRound < record.input.time.val + 2) →
      ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
        post.lastDown = some (payload.downRecord i)) →
      post.initializationFailure = choice.initializationFailure →
      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post →
      ∃ logged diagnostic post,
        ActiveFollowerLogging.checkedLogging i record.input.row
          (record.input.state.activations i) record.input.time (prepared.arm, own) choice =
            .ok logged ∧
        logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
          (record.input.state.activations i) record.input.time (prepared.arm, own) ∧
        diagnostic = ReferenceDownReception.referenceDownCut p view i record.input.row
          record.input.time own rate logged ∧
        (ReferenceActivePhysicalStep.recordFollower view i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          prepared.arm own choice).result = .ok post ∧
        (ReferenceActivePhysicalStep.recordFollower view i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          prepared.arm own choice).downInput = some logged ∧
        (ReferenceActivePhysicalStep.recordFollower view i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          prepared.arm own choice).down = some diagnostic ∧
        post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
        post.S + post.backlog ≤ d * D p ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ post.buffer, saved.calendarRound < record.input.time.val + 2) ∧
        ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
          post.lastDown = some (payload.downRecord i)) ∧
        post.initializationFailure = choice.initializationFailure := by
    intro post hpostStatus hpostValid hpostMass hpostChron hpostBefore hpostLast
      hpostFailure hconsume
    exact ⟨logged, cut, post, hlog, hbufferEq, rfl, hrecorded.trans hconsume,
      hdiagnostics.1, hdiagnostics.2, hpostStatus, hpostValid, hpostMass,
      hpostChron, hpostBefore, hpostLast, hpostFailure⟩
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time
  · by_cases hmatches :
        (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
          own rate logged).2 = expectedDownFlatWord view i record.input.row record.input.time
    · cases hparse : ReferenceDownReception.ordinaryParse p rate
        (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row record.input.time
          own rate logged).2 with
      | none =>
          apply hsimple advanced hloggedStatus hadvancedValid hadvancedMass
            hadvancedChron hadvancedBefore hadvancedPrevious hadvancedFailure
          simp only [cut, ReferenceDownReception.referenceDownCut,
            dite_eq_left hselected, dite_eq_left hloggedStatus, dite_eq_left hregs,
            dite_eq_left hbatchDomain, dite_eq_left hbufferDomain,
            dite_eq_left hmatches, hparse,
            DeclaredFollowerLocalRound.consumeDownResult, advanced]
      | some M =>
          have hM : M = payload.downRecord i := by
            rcases hexpected with hnone | hsome
            · rw [hnone] at hmatches
              have hrawNone :
                  (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
                    record.input.time own rate logged).2 = none :=
                hmatches
              rw [hrawNone] at hparse
              simp [ReferenceDownReception.ordinaryParse] at hparse
              cases hparse
            · rw [hsome] at hmatches
              have hraw :
                  (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
                    record.input.time own rate logged).2 =
                    some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) := hmatches
              have hparsed := parse_stored_word (p := p) (rate := rate) payload i
              rw [hraw] at hparse
              exact Option.some.inj (hparse.symm.trans hparsed)
          have hMsigma : M.val.sigma = start + 1 := by
            rw [hM]
            have hfield := congrArg OrdinaryMessageCodec.DownFields.sigma
              (payload.downRecord_fields i)
            change (payload.downRecord i).val.sigma = start + 1
            rw [hfield, hsigma]
          by_cases haccept : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart logged)
              (record.input.time.val + 1) M
          · have hnone : choice.lastDown = none := by
              rcases hprevious with hnone | hsame
              · exact hnone.1
              · have hstartEqual : ReferencePrelaunchFollower.acceptedStart logged = M.val.sigma := by
                  unfold ReferencePrelaunchFollower.acceptedStart
                  rw [hframe.1, hsame, ← hM]
                exact False.elim (by
                  have hlt := haccept.1
                  rw [hstartEqual] at hlt
                  exact Nat.lt_irrefl _ hlt)
            have hzero : choice.S = 0 ∧ choice.delta = 0 ∧ choice.backlog = 0 := by
              rcases hprevious with ⟨_, hS, hdelta, hbacklog⟩ | hsame
              · exact ⟨hS, hdelta, hbacklog⟩
              · have hfalse : (none : Option (DownRecord (p := p) (rate := rate))) =
                    some (payload.downRecord i) := hnone.symm.trans hsame
                cases hfalse
            have hacceptStart : ReferencePrelaunchFollower.acceptedStart logged = 0 := by
              unfold ReferencePrelaunchFollower.acceptedStart
              rw [hframe.1, hnone]
            have hacceptSigma : 0 < M.val.sigma := by rw [hMsigma]; omega
            have hacceptTime : M.val.sigma ≤ record.input.time.val + 1 := by omega
            have hacceptExact : OrdinaryMessageCodec.acceptDown
                (ReferencePrelaunchFollower.codecParams p rate.eta)
                (ReferencePrelaunchFollower.acceptedStart logged)
                (record.input.time.val + 1) M := ⟨by omega, hacceptTime⟩
            have hstart := ActiveFollowerDownAcceptance.acceptedDownStartLE
              p rate M record.input.time logged hacceptExact
            have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = payload.sigma := by
              apply Fin.ext
              have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
              rw [hMsigma] at hval
              change M.val.sigma - 1 = payload.sigma.val
              rw [hMsigma, hsigma]
              omega
            have hell :
                (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M record.input.time
                  hstart record.input.row).endpoint = u := by
              unfold ActiveFollowerDownAcceptance.acceptedCutoffScan
                FollowerCutoffScan.completeRowCutoffScan
              rw [FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff]
              rw [hdownStart, hcutoff]
              exact Nat.min_eq_left (by omega)
            have hlength : u - M.val.sigma = d := by
              rw [hMsigma]
              omega
            have hq : M.val.q = 0 := by rw [hM]; exact hqueue i
            obtain ⟨final, hchecked, hfinalMass, hlastService⟩ :=
              checkedRecovery_cutoff_budget M logged hq hloggedBuffer u d hlength hdT
            let after := { advanced with
              lastDown := some M
              S := final.registers.1
              delta := final.lastService
              backlog := final.registers.2
              status := ActiveRoundActions.FollowerStatus.unoccupied
              buffer := [] }
            have houtput := (ActiveFollowerDownAcceptance.checkedRecovery_success
              p rate M logged u final hchecked).1
            have hafterService : ActiveFollowerLifecycle.serviceRegistersValid p after := by
              exact ⟨houtput.1, houtput.2.1, houtput.2.2⟩
            have hafterBuffer : ActiveFollowerLifecycle.localBufferValid after := by
              simp [ActiveFollowerLifecycle.localBufferValid, after]
            have hafterValid : ActiveFollowerLifecycle.localStateDomainValid after :=
              ⟨hafterService, hafterBuffer, hstepBatch⟩
            have hafterMass : after.S + after.backlog ≤ d * D p := by
              simpa only [after] using hfinalMass
            have hafterChron : after.buffer.Pairwise
                (fun a b => a.calendarRound < b.calendarRound) := by
              simp [after]
            have hafterBefore : ∀ saved ∈ after.buffer,
                saved.calendarRound < record.input.time.val + 2 := by
              intro saved hsaved
              cases hsaved
            have hafterLast : after.lastDown = some (payload.downRecord i) := by
              simp [after, hM]
            have hafterFailure : after.initializationFailure = choice.initializationFailure := by
              simp [after, advanced, hframe.2.2.2.2.2.2]
            have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome =
                .ok after := by
              have hnotLive : u ≠ record.input.time.val + 2 := by omega
              simp only [cut, ReferenceDownReception.referenceDownCut,
                dite_eq_left hselected, dite_eq_left hloggedStatus, dite_eq_left hregs,
                dite_eq_left hbatchDomain, dite_eq_left hbufferDomain,
                dite_eq_left hmatches, hparse, dite_eq_left hacceptExact,
                hell, hnotLive, hchecked,
                DeclaredFollowerLocalRound.consumeDownResult, after, advanced]
              simp
            exact hsimple after rfl hafterValid hafterMass hafterChron hafterBefore
              (Or.inr hafterLast) hafterFailure hconsume
          · apply hsimple advanced hloggedStatus hadvancedValid hadvancedMass
              hadvancedChron hadvancedBefore hadvancedPrevious hadvancedFailure
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hloggedStatus, dite_eq_left hregs,
              dite_eq_left hbatchDomain, dite_eq_left hbufferDomain,
              dite_eq_left hmatches, hparse, dite_eq_right haccept,
              DeclaredFollowerLocalRound.consumeDownResult, advanced]
    · apply hsimple advanced hloggedStatus hadvancedValid hadvancedMass
        hadvancedChron hadvancedBefore hadvancedPrevious hadvancedFailure
      simp only [cut, ReferenceDownReception.referenceDownCut,
        dite_eq_left hselected, dite_eq_left hloggedStatus, dite_eq_left hregs,
        dite_eq_left hbatchDomain, dite_eq_left hbufferDomain,
        dite_eq_right hmatches, DeclaredFollowerLocalRound.consumeDownResult, advanced]
  · apply hsimple logged hloggedStatus hloggedValid hloggedMass hchron.1 hchron.2
      hloggedPrevious hloggedFailure
    simp only [cut, ReferenceDownReception.referenceDownCut,
      dite_eq_right hselected, DeclaredFollowerLocalRound.consumeDownResult]

private theorem first_preparation_queue_zero
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput birth.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights
      birth.input.row)
    (hprep : birth.output.preparation.coordinator = .first (.chosen installed selected))
    (i : Fin (p.m - 1)) : (installed.registers.payload.downRecord i).val.q = 0 := by
  have hd : ReferenceActivePhysicalStep.dispatch birth.input = .first (.chosen installed selected) :=
    birth.output.preparation.coordinator_eq.symm.trans hprep
  have hfirst : birth.input.state.coordinator = .first := by
    cases hc : birth.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [ReferenceActivePhysicalStep.dispatch, hc,
          CoordinatorRoundDispatch.dispatch] at hd
        cases hd
    | collection payload ledger proposal =>
        simp only [ReferenceActivePhysicalStep.dispatch, hc] at hd
        split at hd
        · cases hd
        · cases hd
    | dagger =>
        simp only [ReferenceActivePhysicalStep.dispatch, hc] at hd
        cases hd
  have hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput birth.input) = .chosen installed selected := by
    rw [ReferenceActivePhysicalStep.dispatch_first birth.input hfirst] at hd
    exact ReferenceActivePhysicalStep.DispatchCut.first.inj hd
  exact ReferenceAssignmentPayloadPersistence.firstChosen_down_queue_zero
    birth.input installed selected hchosen i

/-- One actual post-cutoff observation transition in the original run.
The cutoff, complete payload, original rows/private index/rewards, and first
DOWN queues are produced by the admitted actual cutoff producer. The current
local domains and coordinator/follower constructors remain explicit inputs;
this theorem does not propagate them over the collection prefix.
-/
theorem run_first_collection_follower_observation_step
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let d := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let b := d + 1
    let W := (E.records.drop b).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
    ∀ (hshort : d < count),
      ∃ cut,
        cut = E.records[d]'(by
          simpa only [E, ReferenceActivePhysicalHorizon.run_record_count] using hshort) ∧
        ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
          (base : Fin (p.m - 1) → ℕ)
          (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.clockPending =
              .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).ownedRegisters base
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time)
          (hclock : dispatched.startResult.clock =
            { (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.priorClock with
              u := some (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.payload
            dispatched.startResult
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.time
            (ReferenceActivePhysicalStep.liveInput cut.input r q base).registers.complementWeights
            cut.input.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          cut.input.time.val = start + d ∧
          r.payload.sigma.val = start ∧
          (let u := cut.input.time.val + 1;
            u = start + d + 1 ∧ u ≤ p.T ∧
            FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) = u) ∧
          (∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0) ∧
          (∀ (j : ℕ), j < W.length →
            ∀ (hrecord : b + j < E.records.length),
            let currentSpan : start + (b + j) ≤ p.T := by
              have hcount := ReferenceActivePhysicalHorizon.run_record_count
                initial rows J rewards start count hspan active
              rw [hcount] at hrecord
              omega
            let current := ReferenceActivePhysicalHorizon.run initial rows J rewards
              start (b + j) currentSpan active
            let nextSpan : start + (b + j + 1) ≤ p.T := by
              have hcount := ReferenceActivePhysicalHorizon.run_record_count
                initial rows J rewards start count hspan active
              rw [hcount] at hrecord
              omega
            let next := ReferenceActivePhysicalHorizon.run initial rows J rewards
              start (b + j + 1) nextSpan active
            let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
              E.records[b + j]'hrecord
            ∀ (i : Fin (p.m - 1)) (s : ReferencePrelaunchFollower.State p rate.eta)
              (mu : ActiveFollowerLifecycle.LocalMemory p),
              current.finalState.followers i = .ordinary s mu →
              s.status = .unoccupied →
              s.S ≤ p.T * D p → s.delta ≤ D p → s.backlog ≤ p.T * D p →
              s.S + s.backlog ≤ d * D p →
              (∀ saved ∈ s.buffer, 1 ≤ saved.calendarRound ∧
                saved.calendarRound ≤ p.T) →
              (s.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup →
              (∀ saved ∈ s.buffer, ∃ q : ℕ, q ≤ D p ∧
                saved.observation.val = (q : ℝ) / (D p : ℝ)) →
              s.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) →
              (∀ saved ∈ s.buffer, saved.calendarRound < start + b + j + 1) →
              s.downBatch.pending.length < AffineBatchDecoder.quota p →
              (∀ batch ∈ s.downBatch.completed, batch.length = AffineBatchDecoder.quota p) →
              ((s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0) ∨
                s.lastDown = some (r.payload.downRecord i)) →
              (current.finalState.coordinator = .dagger ∨
                ∃ movingLedger movingSaved,
                  current.finalState.coordinator =
                    .collection r.payload movingLedger movingSaved) →
              (next.finalState.coordinator = .dagger ∨
                ∃ movingLedger movingSaved,
                  next.finalState.coordinator =
                    .collection r.payload movingLedger movingSaved) ∧
              (match (record.output.preparation.followers.followers i).configuration with
              | .dagger =>
                  (record.output.followers i).configuration = .dagger ∧
                    (record.output.followers i).downInput = none ∧
                    (record.output.followers i).down = none ∧
                    (record.output.followers i).failure = none
              | .ordinary choice choiceMemory =>
                  choice = s ∧ choiceMemory = mu ∧
                  ∃ logged diagnostic post,
                    ActiveFollowerLogging.checkedLogging i record.input.row
                      (record.input.state.activations i) record.input.time
                      ((record.output.preparation.followers.followers i).arm,
                        record.output.preparation.feedback.observations
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s = .ok logged ∧
                    logged.buffer = s.buffer ++ ReferencePrelaunchFollower.logAt i
                      record.input.row (record.input.state.activations i) record.input.time
                      ((record.output.preparation.followers.followers i).arm,
                        record.output.preparation.feedback.observations
                          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) ∧
                    diagnostic = ReferenceDownReception.referenceDownCut p
                      record.output.preparation.coordinator.downView i record.input.row
                      record.input.time
                      (record.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged ∧
                    (ReferenceActivePhysicalStep.recordFollower
                      record.output.preparation.coordinator.downView i record.input.row
                      (record.input.state.activations i) record.input.time (record.input.active i)
                      (record.output.preparation.followers.followers i).arm
                      (record.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s).result = .ok post ∧
                    (ReferenceActivePhysicalStep.recordFollower
                      record.output.preparation.coordinator.downView i record.input.row
                      (record.input.state.activations i) record.input.time (record.input.active i)
                      (record.output.preparation.followers.followers i).arm
                      (record.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s).downInput = some logged ∧
                    (ReferenceActivePhysicalStep.recordFollower
                      record.output.preparation.coordinator.downView i record.input.row
                      (record.input.state.activations i) record.input.time (record.input.active i)
                      (record.output.preparation.followers.followers i).arm
                      (record.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s).down = some diagnostic ∧
                    DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
                      record.input.time
                      (record.output.preparation.feedback.observations
                        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) s mu post =
                        .ok (post, mu) ∧
                    (record.output.followers i).configuration = .ordinary post mu ∧
                    (record.output.followers i).failure = none ∧
                    (record.output.followers i).downInput = some logged ∧
                    (record.output.followers i).down = some diagnostic ∧
                    post.status = .unoccupied ∧ post.S ≤ p.T * D p ∧
                    post.delta ≤ D p ∧ post.backlog ≤ p.T * D p ∧
                    post.S + post.backlog ≤ d * D p ∧
                    (∀ saved ∈ post.buffer, 1 ≤ saved.calendarRound ∧
                      saved.calendarRound ≤ p.T) ∧
                    (post.buffer.map (fun saved => (saved.calendarRound, saved.pilot))).Nodup ∧
                    (∀ saved ∈ post.buffer, ∃ q : ℕ, q ≤ D p ∧
                      saved.observation.val = (q : ℝ) / (D p : ℝ)) ∧
                    post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                    (∀ saved ∈ post.buffer, saved.calendarRound < start + b + j + 2) ∧
                    post.downBatch.pending.length < AffineBatchDecoder.quota p ∧
                    (∀ batch ∈ post.downBatch.completed,
                      batch.length = AffineBatchDecoder.quota p) ∧
                    ((post.lastDown = none ∧ post.S = 0 ∧ post.delta = 0 ∧ post.backlog = 0) ∨
                      post.lastDown = some (r.payload.downRecord i)) ∧
                    post.initializationFailure = s.initializationFailure)) := by
  classical
  intro E d b W hshort
  have hservice := ReferenceFirstCutoffRecordedService.run_first_cutoff_recorded_service
    initial rows J rewards start count hspan active hfirst (by
      simpa only [E, d] using hshort)
  obtain ⟨serviceCut, serviceSuffix, hserviceParts⟩ := hservice
  have hserviceIndex : serviceCut = E.records[d]'(by
      simpa only [E, ReferenceActivePhysicalHorizon.run_record_count] using hshort) :=
    hserviceParts.2.1
  obtain ⟨cut, suffix, hsplit, hindex, hcutTime, hactual, r, q, base,
    hinput, hcoordinator, hcall⟩ :=
    ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
      initial rows J rewards start count hspan active hfirst (by
        simpa only [E, d] using hshort)
  have hsameCut : serviceCut = cut := by
    exact hserviceIndex.trans hindex.symm
  dsimp [ReferenceActivePhysicalStep.liveInput] at hcall
  rcases hcall with ⟨dispatched, hstart, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, selected, hbranchRest⟩
  rcases hbranchRest with ⟨hbranch, hkpos, hsigma, hbaseZero, hbirth,
    hbits, hqueues, hcutoffRest⟩
  rcases hcutoffRest with ⟨huEq, _, huT, _, _, _, _, _, hcut, hcutoffTail⟩
  have hsameIndexed : cut = E.records[d]'(by
      simpa only [E, ReferenceActivePhysicalHorizon.run_record_count] using hshort) := hindex
  have hcutRow : cut.input.row = rows J := by
    rw [hactual]
    rfl
  have hfirstCutoff :
      FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)) =
        cut.input.time.val + 1 := by
    simpa only [hcutRow] using hcut
  have hqzero : ∀ i : Fin (p.m - 1), (r.payload.downRecord i).val.q = 0 := by
    intro i
    obtain ⟨birth, _, _, _, installed, birthSelection, hbirthPrep, hbirthPayload⟩ := hbirth
    rw [← hbirthPayload]
    exact first_preparation_queue_zero birth installed birthSelection hbirthPrep i
  let u := cut.input.time.val + 1
  have hu : u = start + d + 1 := by
    dsimp [u]
    exact huEq
  have huBound : u ≤ p.T := by
    dsimp [u]
    exact huT
  have hshortBound : d ≤ p.T := by
    have hcount := ReferenceActivePhysicalHorizon.run_record_count
      initial rows J rewards start count hspan active
    rw [← hcount] at hshort
    omega
  refine ⟨cut, hsameIndexed, r, q, base, dispatched, hstart, ledger, hinit, hledger,
    hdomain, hclock, hpending, hnoAssignment, selected, hbranch, hcutTime, hsigma,
    ?_, hqzero, ?_⟩
  · exact ⟨hu, huBound, by simpa only [hcutRow] using hfirstCutoff⟩
  · intro j hj hrecord currentSpan current nextSpan next record i s mu hstate hstatus
      hS hdelta hbacklog hmass hround hkeys hquant hpair
      hbefore hpendingLocal hcompleted hprevious hcoord
    have hactualRecord : record =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
          start (b + j) nextSpan active := by
      let prefixNext := ReferenceActivePhysicalHorizon.run initial rows J rewards
        start (b + j + 1) nextSpan active
      have hprefix : prefixNext.records.IsPrefix E.records := by
        obtain ⟨rest, he⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
          initial rows J rewards start (b + j + 1) (count - (b + j + 1)) (by omega) active
        have hcount := ReferenceActivePhysicalHorizon.run_record_count
          initial rows J rewards start count hspan active
        rw [hcount] at hrecord
        have htotal : b + j + 1 + (count - (b + j + 1)) = count := by omega
        refine ⟨rest, ?_⟩
        simpa [prefixNext, E, htotal] using he.symm
      have hindex : b + j < prefixNext.records.length := by
        rw [ReferenceActivePhysicalHorizon.run_record_count]
        omega
      have hrecordIndex : prefixNext.records[b + j]'hindex =
          ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards
            start (b + j) nextSpan active := by
        have hsuccessor := ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
          initial rows J rewards start (b + j) nextSpan active
        have hpriorLength :
            (ReferenceActivePhysicalHorizon.run initial rows J rewards start (b + j)
              (by omega) active).records.length = b + j := by
          rw [ReferenceActivePhysicalHorizon.run_record_count]
        simp [prefixNext, hsuccessor, hpriorLength, List.getElem_append_right]
      exact (hprefix.getElem hindex).symm.trans hrecordIndex
    have hstateActual : record.input.state = current.finalState := by
      rw [hactualRecord]
      rfl
    have htimeActual : record.input.time.val = start + b + j := by
      rw [hactualRecord]
      simp [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
        ReferenceActivePhysicalHorizon.roundInputAt]
      omega
    have hrowActual : record.input.row = rows J := by
      rw [hactualRecord]
      rfl
    have hnextState : next.finalState = record.output.next := by
      rw [hactualRecord]
      exact ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt
        initial rows J rewards start (b + j) nextSpan active
    have htag : ReferenceCollectionPhaseHistory.laterChosen record.input = false := by
      have hdrop : j < (E.records.drop b).length := by
        have htake := takeWhile_length_le _
          (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
            !ReferenceCollectionPhaseHistory.laterChosen record.input) (E.records.drop b)
        dsimp only [W] at hj
        omega
      have hget : W[j]'hj = (E.records.drop b)[j]'hdrop := by
        dsimp only [W]
        exact getElem_takeWhile_eq _ _ _ j hj
      have hmem : (E.records.drop b)[j]'hdrop ∈ W := by
        rw [← hget]
        exact List.getElem_mem hj
      have hpred := List.mem_takeWhile_imp hmem
      have hdropRecord : (E.records.drop b)[j]'hdrop = record := by
        simp [record, List.getElem_drop]
      rw [hdropRecord] at hpred
      simpa using hpred
    have hrecordCoord : record.input.state.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          record.input.state.coordinator = .collection r.payload movingLedger movingSaved := by
      rw [hstateActual]
      exact hcoord
    have hnextCoordinator : next.finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          next.finalState.coordinator = .collection r.payload movingLedger movingSaved := by
      have hstep : (ReferenceActivePhysicalStep.step record.input).next.coordinator = .dagger ∨
          ∃ movingLedger movingSaved,
            (ReferenceActivePhysicalStep.step record.input).next.coordinator =
              .collection r.payload movingLedger movingSaved := by
        rcases hrecordCoord with hdagger | ⟨movingLedger, movingSaved, hcollection⟩
        · exact Or.inl (ReferenceActivePhysicalStep.step_coordinator_dagger
            record.input hdagger).1
        · exact step_collection_same_payload record.input r.payload movingLedger movingSaved
            hcollection htag
      rw [hnextState, record.output_eq]
      exact hstep
    have hstateDomains : ActiveFollowerLifecycle.localStateDomainValid s := by
      refine ⟨⟨hS, hdelta, hbacklog⟩, ⟨hround, hkeys, hquant⟩,
        ⟨hpendingLocal, hcompleted⟩⟩
    have hrecordInput : record.input.state.followers i = .ordinary s mu := by
      rw [hstateActual]
      exact hstate
    have hnotLater : ReferenceCollectionPhaseHistory.laterChosen record.input = false := htag
    have hrowCutoff :
        FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) = u := by
      rw [hrowActual]
      simpa [u] using hfirstCutoff
    have hnow : u ≤ record.input.time.val := by
      rw [hu, htimeActual]
      dsimp [b]
      omega
    have hcoordInput : record.input.state.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          record.input.state.coordinator = .collection r.payload movingLedger movingSaved :=
      hrecordCoord
    have hstepFollower := first_collection_record_logging_down record r.payload start d u
      hsigma hqzero hrowCutoff hnow hu hshortBound i s hstatus hstateDomains.1 hstateDomains.2.1
      hstateDomains.2.2 hmass hpair (by
        intro saved hsaved
        simpa [htimeActual] using hbefore saved hsaved)
      hprevious hcoordInput hnotLater
    rcases hstepFollower with ⟨logged, diagnostic, post, hlog, hloggedBuffer,
      hdiagnostic, hrecorded, hdownInput, hdown, hpostStatus, hpostValid, hpostMass,
      hpostPair, hpostBefore, hpostPrevious, hpostFailure⟩
    have hpostDomain := hpostValid
    rcases hpostValid with ⟨⟨hpostS, hpostDelta, hpostBacklog⟩,
      ⟨hpostRound, hpostKeys, hpostQuant⟩, ⟨hpostPending, hpostCompleted⟩⟩
    let hprepared := record.output.preparation.followers.followers i
    let own := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := record.output.preparation.coordinator.downView
    have halign := record.output.preparation.follower_alignment i
    have hobs : record.output.followers i = finishFollower view hprepared own := by
      dsimp [view, own, hprepared]
      rw [record.output_eq]
      rfl
    have hnextCoordinator' : next.finalState.coordinator = .dagger ∨
        ∃ movingLedger movingSaved,
          next.finalState.coordinator = .collection r.payload movingLedger movingSaved :=
      hnextCoordinator
    refine ⟨hnextCoordinator', ?_⟩
    cases hc : hprepared.configuration with
    | dagger =>
        rw [hobs]
        simp [finishFollower, hprepared, hc]
    | ordinary choice choiceMemory =>
        have hprepare :
            (DeclaredFollowerLocalRound.prepare rate i record.input.row
              (record.input.state.activations i) record.input.time (record.input.active i)
              (.ordinary s mu)).configuration = .ordinary choice choiceMemory := by
          have he := record.output.preparation.followers.followers_eq i
          change hprepared = DeclaredFollowerLocalRound.prepare rate i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.input.state.followers i) at he
          rw [hrecordInput] at he
          rw [← he]
          exact hc
        obtain ⟨before, beforeMemory, hinput, hstart, _, _⟩ :=
          ReferenceFollowerReplyChronology.prepare_ordinary_inversion i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (.ordinary s mu) choice choiceMemory hprepare
        obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hinput
        have hstartUnoccupied := ActiveFollowerLifecycle.startRound_unoccupied rate.eta
          record.input.time s mu hstateDomains hstatus
        have hstartEq : ActiveFollowerLifecycle.startRound rate.eta record.input.time s mu =
            .ok (choice, choiceMemory) := hstart
        have hchoiceMemory : choice = s ∧ choiceMemory = mu := by
          have heq := Except.ok.inj (hstartEq.symm.trans hstartUnoccupied)
          exact Prod.mk.inj heq
        rcases hchoiceMemory with ⟨hchoice, hmemory⟩
        subst choice
        subst choiceMemory
        have hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row
            record.input.time own s mu post = .ok (post, mu) := by
          simp only [DeclaredFollowerLocalRound.releaseAndFinish,
            ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i
              record.input.time (ActiveFollowerLifecycle.publicRowOfCompleteRow
                record.input.row record.input.time) own s post hstatus]
          simp only [ActiveFollowerLifecycle.finishRound_unoccupied rate.eta
            record.input.time record.input.row post mu hpostDomain hpostStatus]
        have hrecordLocal :
            (ReferenceActivePhysicalStep.recordFollower view hprepared.follower hprepared.row
              hprepared.activation hprepared.time hprepared.active hprepared.arm own s).result =
                .ok post := by
          simpa only [view, own, hprepared, halign.1, halign.2.1, halign.2.2.1,
            halign.2.2.2] using hrecorded
        have hfinishLocal : DeclaredFollowerLocalRound.releaseAndFinish rate hprepared.follower
            hprepared.row hprepared.time own s mu post = .ok (post, mu) := by
          simpa only [hprepared, halign.1, halign.2.1, halign.2.2.1] using hfinish
        have hout := ReferenceActivePhysicalStep.finishFollower_success view hprepared own
          s post post mu mu hc hrecordLocal hfinishLocal
        have hdiagnostics := ReferenceFollowerSparseEmissionRecovery.finishFollower_diagnostics
          view hprepared own s mu hc
        have hactualInput : (record.output.followers i).downInput = some logged := by
          rw [hobs, hdiagnostics.1]
          simpa only [view, own, hprepared, halign.1, halign.2.1, halign.2.2.1,
            halign.2.2.2] using hdownInput
        have hactualDown : (record.output.followers i).down = some diagnostic := by
          rw [hobs, hdiagnostics.2]
          simpa only [view, own, hprepared, halign.1, halign.2.1, halign.2.2.1,
            halign.2.2.2] using hdown
        have hactualOutput :
            (record.output.followers i).configuration = .ordinary post mu ∧
              (record.output.followers i).failure = none := by
          rw [hobs]
          exact hout
        refine ⟨rfl, rfl, logged, diagnostic, post, hlog, hloggedBuffer, hdiagnostic,
          hrecorded, hdownInput, hdown, hfinish, ?_, ?_, hactualInput, hactualDown,
          hpostStatus, ?_, ?_, ?_, hpostMass, ?_, hpostKeys, ?_, hpostPair, ?_,
          hpostPending, hpostCompleted, hpostPrevious, hpostFailure⟩
        · exact hactualOutput.1
        · exact hactualOutput.2
        · exact hpostS
        · exact hpostDelta
        · exact hpostBacklog
        · intro saved hsaved
          exact hpostRound saved hsaved
        · intro saved hsaved
          exact hpostQuant saved hsaved
        · intro saved hsaved
          simpa [htimeActual] using hpostBefore saved hsaved

end Bandits.Support.ReferenceFirstCollectionFollowerObservation

end
