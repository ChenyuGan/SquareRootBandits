/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConfirmedOccupancy

import Lean.Elab.Tactic.Omega
import Mathlib.Data.List.TakeWhile

/-!
# Actual first-live occupied-follower persistence

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-318`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,40-70,246-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

From one actual occupied prepared choice, this module derives occupancy of
that follower's later actual choices throughout the same first-live window.
The unchanged start-round equation is derived from the actual assignment grid,
proposal memory, and F's successful prefix outputs. Local service, release,
and finish operations preserve occupancy and the actual accepted DOWN record.
This is a conditional one-follower producer; it does not establish missing-set
provenance, all-player occupancy, release geometry, or manuscript closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLiveOccupiedPersistence

open ConstructorDimensions
open ActiveFollowerLifecycle
open ReferenceActivePhysicalStep

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
private abbrev Selection := ReferenceActivePhysicalStep.Selection (p := p) (rate := rate)
private abbrev DownRecord := OrdinaryMessageCodec.DownRecord
  (ReferencePrelaunchFollower.codecParams p rate.eta)

private theorem queue_input_domain (s : ReferencePrelaunchFollower.State p rate.eta)
    (h : localStateDomainValid s) : ActiveFollowerQueueOperation.stateInputDomain s :=
  ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2.1⟩

/-- If the actual start operation leaves an ordinary state unchanged, the
actual prepared follower remains that same ordinary state. The UP offer and
arm-choice checks are discharged from F's local-domain and status fields. -/
private theorem prepare_after_unchanged_start
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : alpha.val ≤ t.val + 1)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hvalid : localStateDomainValid s)
    (hzero : s.status = .unoccupied →
      s.lastDown = none ∧ s.S = 0 ∧ s.delta = 0 ∧ s.backlog = 0)
    (hrecord : s.status ≠ .unoccupied → ∃ M, s.lastDown = some M)
    (hstart : startRound rate.eta t s memory = .ok (s, memory)) :
    (DeclaredFollowerLocalRound.prepare rate i row alpha t active (.ordinary s memory)).configuration =
      .ordinary s memory := by
  classical
  have hdomain := queue_input_domain s hvalid
  by_cases hu : s.status = .unoccupied
  · obtain ⟨hnone, hS, hd, hb⟩ := hzero hu
    have hfields : ActiveFollowerQueueOperation.upOfferFields s =
        OrdinaryMessageCodec.upPlaceholder := by
      simp [ActiveFollowerQueueOperation.upOfferFields,
        ReferencePrelaunchFollower.acceptedStart, hnone, hS, hd, hb,
        OrdinaryMessageCodec.upPlaceholder]
    have hadm : OrdinaryMessageCodec.upAdmissible
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (ActiveFollowerQueueOperation.upOfferFields s) := Or.inl hfields
    by_cases hselected : ActiveFollowerQueueOperation.selectedUpRound i row alpha t
    · let offered : OrdinaryMessageCodec.UpRecord
          (ReferencePrelaunchFollower.codecParams p rate.eta) :=
        ⟨ActiveFollowerQueueOperation.upOfferFields s, hadm⟩
      have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t s =
          .offer offered := by
        simp [ActiveFollowerQueueOperation.checkedUpOffer, hdomain, hselected, hu,
          hadm, offered]
      have hmatch : ActiveFollowerArmChoice.upStateDomain s ∧
          ActiveFollowerArmChoice.offeredUpMatchesState s offered :=
        ⟨hvalid.1, rfl, rfl, rfl, rfl⟩
      obtain ⟨_, hslot, hsender⟩ := hselected
      have hchoice := ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_selected_up
        s (row.2 t) i offered hu hslot hsender hmatch
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff,
        ActiveFollowerArmChoice.followerArmChoice, hchoice]
    · have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row alpha t s =
          .noOffer := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row alpha t s
            hdomain (fun h => hselected h.1)
      have hnot : ¬ (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.upSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) :=
        fun h => hselected ⟨active, h⟩
      have hchoice : ∃ arm,
          ActiveFollowerArmChoice.followerArmChoice s row t i none = some arm := by
        simp only [ActiveFollowerArmChoice.followerArmChoice,
          ActiveFollowerArmChoice.followerArmChoiceCore, ite_eq_left hu, ite_eq_right hnot]
        split <;> exact ⟨_, rfl⟩
      obtain ⟨arm, hc⟩ := hchoice
      simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hc]
  · obtain ⟨M, hM⟩ := hrecord hu
    have hoff := ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i row alpha t s
      hdomain (fun h => hu h.2)
    have hchoice : ∃ arm,
        ActiveFollowerArmChoice.followerArmChoice s row t i none = some arm := by
      simp only [ActiveFollowerArmChoice.followerArmChoice,
        ActiveFollowerArmChoice.followerArmChoiceCore, ite_eq_right hu, hM]
      split
      · exact ⟨_, rfl⟩
      · split
        · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
    obtain ⟨arm, hc⟩ := hchoice
    simp only [DeclaredFollowerLocalRound.prepare, hstart, hoff, hc]

/-- The real first-live list entries are the corresponding records of the
original run, with the physical state at each round boundary retained. -/
private theorem window_record_actual
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length) :
    ∃ hstep : start + (k + 1) ≤ p.T,
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)[k] =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k hstep active := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  change k < W.length at hk
  have hprefix : W.IsPrefix E.records := List.takeWhile_prefix _
  have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan active
  have hkcount : k < count := by
    have := hprefix.length_le
    change E.records.length = count at hcount
    omega
  have hstep : start + (k + 1) ≤ p.T := by omega
  refine ⟨hstep, ?_⟩
  have hnextPrefix :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hstep active).records.IsPrefix
        E.records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start (k + 1) (count - (k + 1)) (by omega) active
    exact ⟨suffix, by simpa only [Nat.add_sub_of_le (by omega : k + 1 ≤ count)] using heq.symm⟩
  have hlength := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start k
    (by omega) active
  have hkNext : k <
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hstep active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  have helem :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k + 1) hstep active).records[k] =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start k hstep active := by
    simp only [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt,
      List.getElem_append_right (by omega :
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start k (by omega) active).records.length ≤ k),
      hlength, Nat.sub_self, List.getElem_singleton]
  exact (hprefix.getElem hk).trans ((hnextPrefix.getElem hkNext).symm.trans helem)

/-- The source-level interruption argument for this exact W. The common actual
assignment has not reached its clipped grid endpoint, and every actual prior
proposal bit since its start is false. Selected payloads come from the actual
coordinator branch and the unique actual installation birth. -/
private theorem first_window_geometry
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    ∀ k : Fin W.length, ∃ payload : ReferenceActivePhysicalStep.Payload rate,
      payload.sigma.val = start ∧
      W[k.val].input.time.val + 2 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      (∀ j : Fin p.T, start ≤ j.val → j.val < W[k.val].input.time.val →
        FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) j = false) ∧
      (∀ selected : Selection W[k.val].input,
        W[k.val].output.preparation.coordinator.selection = some selected →
          selected.view.payload = payload) := by
  intro E W k
  have hw : W.length ≤ count := by
    calc
      W.length ≤ E.records.length := (List.takeWhile_prefix _).length_le
      _ = count := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start count hspan active
  obtain ⟨hstep, hactual⟩ := window_record_actual initial rows J rewards start count hspan active k.val k.isLt
  have htime : W[k.val].input.time.val = start + k.val := by
    rw [hactual]
    rfl
  have hN := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial rows J rewards start count hspan active hfirst
  have hkWindow : k.val + 1 ≤
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length :=
    Nat.succ_le_of_lt k.isLt
  have hkCount : k.val + 1 ≤ count := (Nat.succ_le_of_lt k.isLt).trans hw
  obtain ⟨r, q, base, hr⟩ := (hN.2.1 (k.val + 1) hkWindow).2 (by omega)
  obtain ⟨_, hsigma, _, ⟨birth, hbirth, hborn, hbirthTime, _⟩, hbits, _⟩ :=
    ReferenceFirstComplementReplay.run_first_complement_replay initial rows J rewards start count
      hspan active hfirst (k.val + 1) hkCount hkWindow r q base hr
  have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
    simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
  have hc := (ReferenceRunClockPreservation.run_clockAt initial rows J rewards start
    (k.val + 1) hstep active hseed).1
  simp only [ReferenceCoordinatorClockDomains.clockAt, hr] at hc
  obtain ⟨_, hclock, hclockSigma, _, hgrid, _, hbeforeGrid, _⟩ := hc
  have hg : r.gridBoundary =
      FollowerCutoffScan.gridBoundary p rate.eta.val r.payload.sigma := by
    rw [hgrid, hclock.1, hclockSigma]
    rfl
  have hbirthFull : birth ∈ E.records := by
    obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J
      rewards start (k.val + 1) (count - (k.val + 1)) (by omega) active
    have heq' : E.records =
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start (k.val + 1) hstep active).records ++ suffix := by
      simpa only [Nat.add_sub_of_le (by omega : k.val + 1 ≤ count)] using heq
    rw [heq']
    exact List.mem_append_left _ hbirth
  refine ⟨r.payload, hsigma, ?_, ?_, ?_⟩
  · rw [htime]
    rw [hg] at hbeforeGrid
    omega
  · intro j hj ht
    apply hbits j hj
    rw [htime] at ht
    omega
  · intro selected hs
    obtain ⟨other, hother, hotherTime, hotherBorn, _, _⟩ :=
      ReferenceFirstDownRecoveryBudget.run_first_selected_payload initial rows J rewards start count
        hspan active hfirst k selected hs
    have heq : other = birth :=
      ReferenceAssignmentPayloadChronology.run_records_time_injective initial rows J rewards start
        count hspan active hother hbirthFull (hotherTime.trans hbirthTime.symm)
    subst other
    exact ReferenceAssignmentPayloadChronology.installationBirth_payload_unique birth _ _ hotherBorn hborn

/-- F's actual endpoint telescope supplies the incoming ordinary state and
proposal read; the grid and bit proof above turns its real StartRound call into
an unchanged equation and hence the actual prepared-choice state. -/
private theorem first_live_choice_start
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
    ∀ (k : Fin W.length) (i : Fin (p.m - 1)),
      ∃ incoming incomingMemory,
        W[k.val].input.state.followers i = .ordinary incoming incomingMemory ∧
        localStateDomainValid incoming ∧
        (incoming.status = .unoccupied →
          incoming.lastDown = none ∧ incoming.S = 0 ∧ incoming.delta = 0 ∧ incoming.backlog = 0) ∧
        (incoming.status ≠ .unoccupied →
          0 < k.val ∧ ∃ M token,
            incoming.lastDown = some M ∧ M.val.sigma = start + 1 ∧
            incomingMemory.lastProposalRead = some token ∧
            token.timestamp.val + 1 = start + k.val ∧
            token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J) token.timestamp) ∧
        W[k.val].input.time.val = start + k.val ∧
        startRound rate.eta W[k.val].input.time incoming incomingMemory =
          .ok (incoming, incomingMemory) ∧
        (W[k.val].output.preparation.followers.followers i).configuration =
          .ordinary incoming incomingMemory := by
  intro E W k i
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  obtain ⟨hprefixes, _⟩ := hsafe
  obtain ⟨hprefix, hstates⟩ := hprefixes k.val (Nat.le_of_lt k.isLt)
  rcases hstates i with ⟨incoming, incomingMemory, hstate, hlocal, _, _, _, hzero, hoccupied⟩
  obtain ⟨_, hactual⟩ := window_record_actual initial rows J rewards start count hspan active
    k.val k.isLt
  let record := W[k.val]
  let prior := ReferenceActivePhysicalHorizon.run initial rows J rewards start k.val hprefix active
  have hinputState : record.input.state = prior.finalState := by
    change W[k.val].input.state = _
    rw [hactual]
    rfl
  have hinput : record.input.state.followers i = .ordinary incoming incomingMemory := by
    rw [hinputState]
    exact hstate
  have hround : record.input.time.val = start + k.val := by
    change W[k.val].input.time.val = _
    rw [hactual]
    rfl
  obtain ⟨payload, _, hpGrid, hpBits, _⟩ :=
    first_window_geometry initial rows J rewards start count hspan active hfirst k
  have hstart : startRound rate.eta record.input.time incoming incomingMemory =
      .ok (incoming, incomingMemory) := by
    by_cases hu : incoming.status = .unoccupied
    · exact startRound_unoccupied rate.eta record.input.time incoming incomingMemory hlocal hu
    · obtain ⟨hkpos, M, token, hM, hMsigma, hread, hstamp, hbit⟩ := hoccupied hu
      have hcoord : acceptedStartCoordinate M = payload.sigma := by
        apply Fin.ext
        have hh := accepted_start_coordinate_one_based M
        omega
      have htimeM : M.val.sigma ≤ record.input.time.val := by omega
      have hgrid : record.input.time.val + 2 ≤
          FollowerCutoffScan.gridBoundary p rate.eta.val (acceptedStartCoordinate M) := by
        rw [hcoord]
        exact hpGrid
      have hbitFalse : token.bit = false := by
        rw [hbit]
        apply hpBits token.timestamp
        · omega
        · change token.timestamp.val < record.input.time.val
          omega
      have hgridNe :
          FollowerCutoffScan.gridBoundary p rate.eta.val (acceptedStartCoordinate M) ≠
            record.input.time.val + 1 := by omega
      have hbranch := startRound_occupied_branch rate.eta record.input.time incoming incomingMemory
        hu hlocal M hM htimeM (by omega) token hread
        (by change token.timestamp.val + 1 = _; omega)
      simpa only [hgridNe, decide_false, hbitFalse, Bool.false_or,
        Bool.false_eq_true, ite_false] using hbranch
  have hchoice :
      (record.output.preparation.followers.followers i).configuration =
        .ordinary incoming incomingMemory := by
    rw [record.output.preparation.followers.followers_eq i]
    change (DeclaredFollowerLocalRound.prepare rate i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i)).configuration = _
    rw [hinput]
    apply prepare_after_unchanged_start i record.input.row (record.input.state.activations i)
      record.input.time (record.input.active i) incoming incomingMemory hlocal hzero
    · intro h
      obtain ⟨_, M, _, hM, _⟩ := hoccupied h
      exact ⟨M, hM⟩
    · exact hstart
  exact ⟨incoming, incomingMemory, hinput, hlocal, hzero, hoccupied,
    hround, hstart, hchoice⟩

/-- Adjacent records in W are adjacent actual run operations: the next real
input carries the previous real output state. -/
private theorem window_successor_input
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (j : ℕ)
    (hj : j + 1 < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)[j + 1].input.state =
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records)[j].output.next := by
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  change j + 1 < W.length at hj
  have hj0 : j < W.length := by omega
  obtain ⟨hstep, hactual⟩ := window_record_actual initial rows J rewards start count hspan active j hj0
  obtain ⟨hstepNext, hactualNext⟩ := window_record_actual initial rows J rewards start count hspan active
    (j + 1) hj
  have hfinal :
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (j + 1) hstep active).finalState =
        W[j].output.next := by
    rw [ReferenceAssignmentPayloadChronology.run_successor_finalState_eq_actualRunRecordAt]
    exact congrArg (fun r => r.output.next) hactual.symm
  have hinput : W[j + 1].input.state =
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start (j + 1) hstep active).finalState := by
    rw [hactualNext]
    rfl
  exact hinput.trans hfinal

/-- Invert the successful ordinary-follower observation branch without
replacing the run's actual record, checked service result, or finish result. -/
private theorem finishFollower_ordinary_inv
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary choice choiceMemory)
    (hout : (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
      .ordinary next nextMemory) :
    ∃ post,
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post ∧
      DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row prepared.time
        observation choice choiceMemory post = .ok (next, nextMemory) := by
  classical
  unfold ReferenceActivePhysicalStep.finishFollower at hout
  rw [hconfiguration] at hout
  cases hrecord : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation choice).result with
  | error failure =>
      simp only [hrecord] at hout
      cases hout
  | ok post =>
      cases hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
          prepared.time observation choice choiceMemory post with
      | error failure =>
          simp only [hrecord, hfinish] at hout
          cases hout
      | ok result =>
          rcases result with ⟨final, finalMemory⟩
          simp only [hrecord, hfinish] at hout
          injection hout with hstate hmemory
          subst final
          subst finalMemory
          exact ⟨post, rfl, hfinish⟩

/-- In the actual ordinary local round, service preserves status and lastDown;
the pending-only release can change pending to released, while EndRound frames
the resulting state. Thus a successful actual output remains occupied and
retains the same accepted DOWN record. -/
private theorem actual_occupied_finish_preserves
    (record : Record) (i : Fin (p.m - 1))
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (choiceMemory : ActiveFollowerLifecycle.LocalMemory p)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice choiceMemory)
    (hnext : (record.output.followers i).configuration = .ordinary next nextMemory)
    (hoccupied : choice.status ≠ .unoccupied)
    (hvalid : localStateDomainValid choice)
    (M : DownRecord)
    (hrecord : choice.lastDown = some M)
    (htime : M.val.sigma ≤ record.input.time.val) :
          next.status ≠ .unoccupied ∧ next.lastDown = choice.lastDown := by
  classical
  let prepared := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let view := record.output.preparation.coordinator.downView
  have hfinishOrdinary :
      (ReferenceActivePhysicalStep.finishFollower view prepared observation).configuration =
        .ordinary next nextMemory := by
    have hobs : record.output.followers i =
        ReferenceActivePhysicalStep.finishFollower view prepared observation := by
      dsimp only [view, prepared, observation]
      rw [record.output_eq]
      rfl
    rw [← hobs]
    exact hnext
  have halign := record.output.preparation.follower_alignment i
  obtain ⟨post, hserviceOut, htail⟩ := finishFollower_ordinary_inv
    view prepared observation choice choiceMemory next nextMemory hchoice hfinishOrdinary
  have hrecordPrepared :
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation choice).result =
          .ok post := hserviceOut
  have hrecordStage : DeclaredFollowerLocalRound.recordOrServiceThenDown rate
      prepared.follower prepared.row prepared.activation prepared.time prepared.active
      prepared.arm observation choice = .ok post := by
    simpa only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hoccupied]
      using hrecordPrepared
  have hreleaseFinish := htail
  cases hservice : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale prepared.follower prepared.row prepared.activation
      prepared.time observation choice with
  | failure =>
      have h := hrecordStage
      rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied rate
        prepared.follower prepared.row prepared.activation prepared.time prepared.active
        prepared.arm observation choice hoccupied, hservice] at h
      cases h
  | success serviced =>
      have hpostEq : post = serviced.output := by
        have h := hrecordStage
        rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied rate
          prepared.follower prepared.row prepared.activation prepared.time prepared.active
          prepared.arm observation choice hoccupied, hservice] at h
        exact (Except.ok.inj h).symm
      have hserviceRegisters := ActiveFollowerQueueOperation.serviceOutput_preserves_other_registers
        rate.n choice serviced.arrival
      have hpostStatus : post.status = choice.status := by
        calc
          post.status = serviced.output.status := congrArg
            (fun s : ReferencePrelaunchFollower.State p rate.eta => s.status) hpostEq
          _ = (ActiveFollowerQueueOperation.serviceOutput rate.n choice serviced.arrival).status :=
            congrArg (fun s : ReferencePrelaunchFollower.State p rate.eta => s.status)
              serviced.queueUpdate
          _ = choice.status := hserviceRegisters.2.2.2.1
      have hpostLast : post.lastDown = choice.lastDown := by
        calc
          post.lastDown = serviced.output.lastDown := congrArg
            (fun s : ReferencePrelaunchFollower.State p rate.eta => s.lastDown) hpostEq
          _ = (ActiveFollowerQueueOperation.serviceOutput rate.n choice serviced.arrival).lastDown :=
            congrArg (fun s : ReferencePrelaunchFollower.State p rate.eta => s.lastDown)
              serviced.queueUpdate
          _ = choice.lastDown := hserviceRegisters.1
      have hpostValid : localStateDomainValid post := by
        have hoccupiedState : choice.status.occupied := by
          cases hstatus : choice.status <;> simp_all [ActiveRoundActions.FollowerStatus.occupied]
        have hserviceUpdate :
            ActiveFollowerQueueOperation.serviceOutput rate.n choice serviced.arrival =
              ActiveFollowerQueueOperation.serviceUpdate rate.n choice serviced.arrival := by
          simp [ActiveFollowerQueueOperation.serviceOutput, hoccupiedState]
        have hserviceAction : serviced.service = ActiveFollowerQueueOperation.localService
            rate.n choice.backlog serviced.arrival := by
          cases hstatus : choice.status with
          | unoccupied => exact (hoccupied hstatus).elim
          | pending =>
              have h := serviced.action
              simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at h
              rcases h with ⟨_, M', _, _, _, hservice⟩
              exact hservice
          | released =>
              have h := serviced.action
              simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at h
              rcases h with ⟨_, M', _, _, _, hservice⟩
              exact hservice
        have hdeltaOutput : serviced.output.delta = serviced.service := by
          calc
            serviced.output.delta =
                (ActiveFollowerQueueOperation.serviceOutput rate.n choice serviced.arrival).delta :=
              congrArg (fun s : ReferencePrelaunchFollower.State p rate.eta => s.delta)
                serviced.queueUpdate
            _ = (ActiveFollowerQueueOperation.serviceUpdate rate.n choice serviced.arrival).delta :=
              congrArg (fun s : ReferencePrelaunchFollower.State p rate.eta => s.delta)
                hserviceUpdate
            _ = ActiveFollowerQueueOperation.localService rate.n choice.backlog serviced.arrival := rfl
            _ = serviced.service := hserviceAction.symm
        have hbufferOutput : serviced.output.buffer = choice.buffer := by
          calc
            serviced.output.buffer =
                (ActiveFollowerQueueOperation.serviceOutput rate.n choice serviced.arrival).buffer :=
              congrArg (fun s : ReferencePrelaunchFollower.State p rate.eta => s.buffer)
                serviced.queueUpdate
            _ = choice.buffer := hserviceRegisters.2.2.1
        have hbatchOutput : serviced.output.downBatch = choice.downBatch := by
          calc
            serviced.output.downBatch =
                (ActiveFollowerQueueOperation.serviceOutput rate.n choice serviced.arrival).downBatch :=
              congrArg (fun s : ReferencePrelaunchFollower.State p rate.eta => s.downBatch)
                serviced.queueUpdate
            _ = choice.downBatch := hserviceRegisters.2.1
        rw [hpostEq]
        change ActiveFollowerLifecycle.serviceRegistersValid p serviced.output ∧
          ActiveFollowerLifecycle.localBufferValid serviced.output ∧
          ActiveFollowerLifecycle.downDecoderStateValid serviced.output
        unfold ActiveFollowerLifecycle.serviceRegistersValid
        refine ⟨⟨serviced.score_le_TD, ?_, serviced.backlog_le_TD⟩, ?_, ?_⟩
        · rw [hdeltaOutput]
          exact serviced.service_le_D
        · unfold ActiveFollowerLifecycle.localBufferValid
          rw [hbufferOutput]
          exact hvalid.2.1
        · unfold ActiveFollowerLifecycle.downDecoderStateValid
          rw [hbatchOutput]
          exact hvalid.2.2
      have hpostStatusOccupied : post.status ≠ .unoccupied := by
        rw [hpostStatus]
        exact hoccupied
      have hpostLastRecord : post.lastDown = some M := by
        rw [hpostLast, hrecord]
      have htimePrepared : M.val.sigma ≤ prepared.time.val := by
        exact htime.trans (le_of_eq (congrArg Fin.val halign.2.2.1.symm))
      have hpostRecord :
          (¬ ActiveFollowerLifecycle.releaseCondition rate.eta prepared.follower
              (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
              observation M ∧ post.status = .unoccupied) ∨
            (∃ M', post.lastDown = some M' ∧ M'.val.sigma ≤ prepared.time.val + 1) := by
        exact Or.inr ⟨M, hpostLastRecord, by
          omega⟩
      unfold DeclaredFollowerLocalRound.releaseAndFinish at hreleaseFinish
      cases hrelease : ActiveFollowerLifecycle.releaseAfterService rate.eta prepared.follower
          prepared.time (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
          observation choice post with
      | error reason =>
          simp only [hrelease] at hreleaseFinish
          cases hreleaseFinish
      | ok released =>
          cases hround : ActiveFollowerLifecycle.finishRound rate.eta prepared.time
              prepared.row released choiceMemory with
          | error reason =>
              simp only [hrelease, hround] at hreleaseFinish
              cases hreleaseFinish
          | ok result =>
              rcases result with ⟨final, finalMemory⟩
              have hresultEq : (final, finalMemory) = (next, nextMemory) :=
                Except.ok.inj (by simpa only [hrelease, hround] using hreleaseFinish)
              have hpair : final = next ∧ finalMemory = nextMemory :=
                ⟨congrArg Prod.fst hresultEq, congrArg Prod.snd hresultEq⟩
              have hframe := ActiveFollowerLifecycle.finishRound_frame rate.eta
                prepared.time prepared.row released final choiceMemory finalMemory hround
              have hfinal : next = released := by
                rcases hpair with ⟨hfinal, _⟩
                exact hfinal.symm.trans hframe
              have hreleased : released.status ≠ .unoccupied ∧
                  released.lastDown = choice.lastDown := by
                cases hstatus : choice.status with
                | unoccupied => exact (hoccupied hstatus).elim
                | released =>
                    have hnotPending : choice.status ≠ .pending := by simp [hstatus]
                    rw [ActiveFollowerLifecycle.releaseAfterService_not_pending
                      rate.eta prepared.follower prepared.time
                      (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
                      observation choice post hnotPending] at hrelease
                    have heq : released = post := (Except.ok.inj hrelease).symm
                    constructor
                    · rw [heq, hpostStatus, hstatus]
                      decide
                    · rw [heq]
                      exact hpostLast
                | pending =>
                    have hexpected := ActiveFollowerLifecycle.releaseAfterService_pending_branch
                      rate.eta prepared.follower prepared.time
                      (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
                      observation choice post hstatus hvalid M hrecord
                      htimePrepared hpostValid hpostRecord
                    rw [hexpected] at hrelease
                    by_cases htest : ActiveFollowerLifecycle.releaseCondition rate.eta prepared.follower
                        (ActiveFollowerLifecycle.publicRowOfCompleteRow prepared.row prepared.time)
                        observation M
                    · simp only [htest] at hrelease
                      have heq : released = {post with status := .released} :=
                        (Except.ok.inj hrelease).symm
                      constructor
                      · rw [heq]
                        simp
                      · rw [heq]
                        simp [hpostLast]
                    · simp only [htest] at hrelease
                      have heq : released = post := (Except.ok.inj hrelease).symm
                      constructor
                      · rw [heq, hpostStatus, hstatus]
                        decide
                      · rw [heq]
                        exact hpostLast
              exact ⟨by rw [hfinal]; exact hreleased.1,
                by rw [hfinal]; exact hreleased.2⟩

/-- In an actual prepared-choice selection branch, O identifies the carried
DOWN record of every occupied ordinary follower with that branch's payload. -/
private theorem actual_selection_lastDown
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
    ∀ (k : Fin W.length)
      (selected : ReferenceActivePhysicalStep.Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      ∀ (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
        (W[k.val].output.preparation.followers.followers i).configuration =
          .ordinary choice choiceMemory →
        choice.status ≠ .unoccupied →
        choice.lastDown = some (selected.view.payload.downRecord i) := by
  intro E W k selected hselected i choice choiceMemory hchoice hoccupied
  obtain ⟨selectedChoice, selectedMemory, _, _, hselectedChoice, _, _, hfields, _⟩ :=
    ReferenceFirstLiveConfirmedOccupancy.run_first_live_actual_choice_fields
      initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
      hbacklog hnone hunoccupied hvalid hpair htime hbatch k selected hselected i
  have hstate : selectedChoice = choice ∧ selectedMemory = choiceMemory := by
    have heq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary selectedChoice selectedMemory =
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice choiceMemory :=
      hselectedChoice.symm.trans hchoice
    injection heq with hstate hmemory
    exact ⟨hstate, hmemory⟩
  rcases hstate with ⟨rfl, rfl⟩
  exact hfields hoccupied

/-- Occupancy of one actual prepared follower persists through every later
actual choice in the same first-live window. At each such round the theorem
exposes the real incoming state, local domain, timestamped proposal read, and
unchanged StartRound equation. Its accepted DOWN record agrees with O's actual
selection branch whenever that branch is selected. The sole occupied premise
is at the one caller-supplied actual choice. -/
theorem run_first_live_occupied_follower_persistence
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
    ∀ (k : Fin W.length)
      (selected : ReferenceActivePhysicalStep.Selection W[k.val].input),
      W[k.val].output.preparation.coordinator.selection = some selected →
      ∀ (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
        (choiceMemory : ActiveFollowerLifecycle.LocalMemory p),
        (W[k.val].output.preparation.followers.followers i).configuration =
          .ordinary choice choiceMemory →
        choice.status ≠ .unoccupied →
        ∀ (j : Fin W.length), k.val ≤ j.val →
          ∃ choiceJ choiceMemoryJ next nextMemory incoming incomingMemory,
            (W[j.val].output.preparation.followers.followers i).configuration =
              .ordinary choiceJ choiceMemoryJ ∧
            (W[j.val].output.followers i).configuration = .ordinary next nextMemory ∧
            (W[j.val].output.followers i).failure = none ∧
            W[j.val].input.state.followers i = .ordinary incoming incomingMemory ∧
            localStateDomainValid incoming ∧
            incoming.status ≠ .unoccupied ∧
            incoming.lastDown = some (selected.view.payload.downRecord i) ∧
            (selected.view.payload.downRecord i).val.sigma = start + 1 ∧
            (∃ token,
              incomingMemory.lastProposalRead = some token ∧
              token.timestamp.val + 1 = start + j.val ∧
              token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
                (rows J) token.timestamp) ∧
            startRound rate.eta W[j.val].input.time incoming incomingMemory =
              .ok (incoming, incomingMemory) ∧
            choiceJ = incoming ∧ choiceMemoryJ = incomingMemory ∧
            choiceJ.status ≠ .unoccupied ∧ next.status ≠ .unoccupied ∧
            choiceJ.lastDown = some (selected.view.payload.downRecord i) ∧
            next.lastDown = some (selected.view.payload.downRecord i) ∧
            (∀ selectedJ : ReferenceActivePhysicalStep.Selection W[j.val].input,
              W[j.val].output.preparation.coordinator.selection = some selectedJ →
                selectedJ.view.payload.downRecord i = selected.view.payload.downRecord i) := by
  intro E W k selected hselected i choice choiceMemory hchoice hoccupied
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  obtain ⟨_, houtputs⟩ := hsafe
  obtain ⟨incoming, incomingMemory, hinput, hlocal, _, htoken, hround, hstart, hchoiceStart⟩ :=
    first_live_choice_start initial rows J rewards start count hspan active hfirst seed memory
      hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch k i
  obtain ⟨choiceAtStart, memoryAtStart, nextAtStart, nextMemoryAtStart,
      hchoiceAtStart, hnextAtStart, hfailureAtStart, hlastAtStart, _⟩ :=
    ReferenceFirstLiveConfirmedOccupancy.run_first_live_actual_choice_fields
      initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
      hbacklog hnone hunoccupied hvalid hpair htime hbatch k selected hselected i
  have hincomingEq : incoming = choice ∧ incomingMemory = choiceMemory := by
    have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary incoming incomingMemory =
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice choiceMemory :=
      hchoiceStart.symm.trans hchoice
    injection hconfig with hstate hmemory
    exact ⟨hstate, hmemory⟩
  have hchoiceEq : choiceAtStart = choice ∧ memoryAtStart = choiceMemory := by
    have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary choiceAtStart memoryAtStart =
        DeclaredFollowerLocalRound.LocalConfiguration.ordinary choice choiceMemory :=
      hchoiceAtStart.symm.trans hchoice
    injection hconfig with hstate hmemory
    exact ⟨hstate, hmemory⟩
  have hoccupiedAtStart : choiceAtStart.status ≠ .unoccupied := by
    rw [hchoiceEq.1]
    exact hoccupied
  have hoccupiedIncoming : incoming.status ≠ .unoccupied := by
    rw [hincomingEq.1]
    exact hoccupied
  have hbaseRecord := hlastAtStart hoccupiedAtStart
  obtain ⟨hbasePos, M, token, hMIncoming, hMsigma, hread, hstamp, hbit⟩ :=
    htoken hoccupiedIncoming
  have hM : choice.lastDown = some M := by
    rw [← hincomingEq.1]
    exact hMIncoming
  have hbaseRecordChoice : choice.lastDown =
      some (selected.view.payload.downRecord i) := by
    rw [hchoiceEq.1] at hbaseRecord
    exact hbaseRecord
  have hbaseRecordEq : M = selected.view.payload.downRecord i := by
    rw [hM] at hbaseRecordChoice
    exact Option.some.inj hbaseRecordChoice
  have hbaseIncomingRecord : incoming.lastDown =
      some (selected.view.payload.downRecord i) := by
    simpa only [hbaseRecordEq] using hMIncoming
  have hbaseTime : M.val.sigma ≤ W[k.val].input.time.val := by
    rw [hMsigma, hround]
    have hkpos : 1 ≤ k.val := Nat.succ_le_iff.mpr hbasePos
    omega
  have hlocalChoice : localStateDomainValid choice := by
    rw [← hincomingEq.1]
    exact hlocal
  have hbaseStep := actual_occupied_finish_preserves W[k.val] i choice choiceMemory
    nextAtStart nextMemoryAtStart hchoice hnextAtStart hoccupied hlocalChoice M hM hbaseTime
  have hbaseOutputRecord : nextAtStart.lastDown = some (selected.view.payload.downRecord i) := by
    exact hbaseStep.2.trans hbaseRecordChoice
  have hbaseOutputOccupied := hbaseStep.1
  have hbaseInputOccupied : incoming.status ≠ .unoccupied := hoccupiedIncoming
  have hbasePayloadStart : (selected.view.payload.downRecord i).val.sigma = start + 1 := by
    calc
      (selected.view.payload.downRecord i).val.sigma = M.val.sigma :=
        congrArg (fun M : DownRecord => M.val.sigma) hbaseRecordEq.symm
      _ = start + 1 := hMsigma

  have hfuture : ∀ (j : ℕ) (hkj : k.val ≤ j) (hjlen : j < W.length),
      ∃ choiceJ choiceMemoryJ next nextMemory incoming incomingMemory,
        (W[j].output.preparation.followers.followers i).configuration =
          .ordinary choiceJ choiceMemoryJ ∧
        (W[j].output.followers i).configuration = .ordinary next nextMemory ∧
        (W[j].output.followers i).failure = none ∧
        W[j].input.state.followers i = .ordinary incoming incomingMemory ∧
        localStateDomainValid incoming ∧ incoming.status ≠ .unoccupied ∧
        incoming.lastDown = some (selected.view.payload.downRecord i) ∧
        (selected.view.payload.downRecord i).val.sigma = start + 1 ∧
        (∃ token, incomingMemory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = start + j ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (rows J) token.timestamp) ∧
        startRound rate.eta W[j].input.time incoming incomingMemory =
          .ok (incoming, incomingMemory) ∧
        choiceJ = incoming ∧ choiceMemoryJ = incomingMemory ∧
        choiceJ.status ≠ .unoccupied ∧ next.status ≠ .unoccupied ∧
        choiceJ.lastDown = some (selected.view.payload.downRecord i) ∧
        next.lastDown = some (selected.view.payload.downRecord i) ∧
        (∀ selectedJ : Selection W[j].input,
          W[j].output.preparation.coordinator.selection = some selectedJ →
            selectedJ.view.payload.downRecord i = selected.view.payload.downRecord i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        intro hkj hjlen
        by_cases heq : j = k.val
        · subst j
          refine ⟨choice, choiceMemory, nextAtStart, nextMemoryAtStart, incoming,
            incomingMemory, hchoice, hnextAtStart, hfailureAtStart, hinput, hlocal,
            hbaseInputOccupied, ?_, hbasePayloadStart, ⟨token, hread, hstamp, hbit⟩,
            hstart, hincomingEq.1.symm, hincomingEq.2.symm, hoccupied,
            hbaseOutputOccupied, ?_, hbaseOutputRecord, ?_⟩
          · exact hbaseIncomingRecord
          · exact hbaseRecordChoice
          · intro selectedJ hselectedJ
            have hlastJ := actual_selection_lastDown initial rows J rewards start count hspan active
              hfirst seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch
              ⟨k.val, by omega⟩ selectedJ hselectedJ i choice choiceMemory hchoice hoccupied
            have hsameRecord := hlastJ.symm.trans hbaseRecordChoice
            exact Option.some.inj hsameRecord
        · have hprevPos : 0 < j := by omega
          have hprevLe : k.val ≤ j - 1 := by omega
          have hprevLen : j - 1 < W.length := by omega
          obtain ⟨prevChoice, prevChoiceMemory, prevNext, prevNextMemory,
              prevIncoming, prevIncomingMemory,
              hprevChoice, hprevNext, hprevFailure, hprevInput, hprevValid,
              hprevOccupied, hprevLast, _hprevSigma, hprevToken, hprevStart,
              hprevChoiceEq, hprevMemoryEq, hprevChoiceOccupied, hprevNextOccupied,
              hprevChoiceLast, hprevNextLast, hprevSelected⟩ :=
            ih (j - 1) (by omega) hprevLe hprevLen
          have hsucc : (j - 1) + 1 < W.length := by omega
          have hnextInputState := window_successor_input initial rows J rewards start count
            hspan active (j - 1) hsucc
          have hidx : j - 1 + 1 = j := by omega
          have hnextInputState' : W[j].input.state = W[j - 1].output.next := by
            simpa only [hidx] using hnextInputState
          have houtputState : W[j - 1].output.next.followers i =
              (W[j - 1].output.followers i).configuration := by
            rw [W[j - 1].output_eq]
            rfl
          have hcurrentInput : W[j].input.state.followers i =
              DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory := by
            calc
              W[j].input.state.followers i = W[j - 1].output.next.followers i :=
                congrArg (fun s : ReferenceActivePhysicalHorizon.State p rate => s.followers i)
                  hnextInputState'
              _ = (W[j - 1].output.followers i).configuration :=
                congrArg (fun s : DeclaredFollowerLocalRound.LocalConfiguration p rate => s)
                  houtputState
              _ = DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory :=
                hprevNext
          obtain ⟨incomingNow, incomingMemoryNow, hinputNow, hlocalNow,
              _, htokenNow, hroundNow, hstartNow, hchoiceNow⟩ :=
            first_live_choice_start initial rows J rewards start count hspan active hfirst
              seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch
              ⟨j, hjlen⟩ i
          have hsameIncoming : incomingNow = prevNext ∧ incomingMemoryNow = prevNextMemory := by
            have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                incomingNow incomingMemoryNow =
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory :=
              hinputNow.symm.trans hcurrentInput
            injection hconfig with hstate hmemory
            exact ⟨hstate, hmemory⟩
          have hoccupiedIncomingNow : incomingNow.status ≠ .unoccupied := by
            rw [hsameIncoming.1]
            exact hprevNextOccupied
          have hlocalPrev : localStateDomainValid prevNext := by
            rw [← hsameIncoming.1]
            exact hlocalNow
          have hstartPrev : startRound rate.eta W[j].input.time prevNext prevNextMemory =
              .ok (prevNext, prevNextMemory) := by
            simpa only [hsameIncoming.1, hsameIncoming.2] using hstartNow
          have hcurrentToken := htokenNow hoccupiedIncomingNow
          obtain ⟨hcurrentPos, MCurrent, tokenNow, hMCurrent, hMCurrentSigma,
              hreadNow, hstampNow, hbitNow⟩ := hcurrentToken
          have hreadPrev : prevNextMemory.lastProposalRead = some tokenNow := by
            calc
              prevNextMemory.lastProposalRead = incomingMemoryNow.lastProposalRead :=
                congrArg (fun mem : ActiveFollowerLifecycle.LocalMemory p => mem.lastProposalRead)
                  hsameIncoming.2.symm
              _ = some tokenNow := hreadNow
          have hstatesConfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
              incomingNow incomingMemoryNow =
              DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory := by
            rw [hsameIncoming.1, hsameIncoming.2]
          have hchoiceNowEq :
              (W[j].output.preparation.followers.followers i).configuration =
              DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory := by
            exact hchoiceNow.trans hstatesConfig
          obtain ⟨choiceNow, memoryNow, nextNow, nextMemoryNow,
              hchoiceActual, hnextActual, hfailureNow, _⟩ := houtputs ⟨j, hjlen⟩ i
          have hstateChoice : choiceNow = prevNext ∧ memoryNow = prevNextMemory := by
            have hconfig : DeclaredFollowerLocalRound.LocalConfiguration.ordinary choiceNow memoryNow =
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory :=
              hchoiceActual.symm.trans hchoiceNowEq
            injection hconfig with hstate hmemory
            exact ⟨hstate, hmemory⟩
          have hchoiceActualPrev :
              (W[j].output.preparation.followers.followers i).configuration =
                DeclaredFollowerLocalRound.LocalConfiguration.ordinary prevNext prevNextMemory := by
            rw [hstateChoice.1, hstateChoice.2] at hchoiceActual
            exact hchoiceActual
          have hchoiceLastNow : prevNext.lastDown =
              some (selected.view.payload.downRecord i) := hprevNextLast
          have hMCurrentEq : MCurrent = selected.view.payload.downRecord i := by
            have hcurrentRecord : incomingNow.lastDown =
                some (selected.view.payload.downRecord i) := by
              rw [hsameIncoming.1]
              exact hchoiceLastNow
            rw [hMCurrent] at hcurrentRecord
            exact Option.some.inj hcurrentRecord
          have hMNow : ∃ M, prevNext.lastDown = some M :=
            ⟨selected.view.payload.downRecord i, hchoiceLastNow⟩
          obtain ⟨MNow, hMNow⟩ := hMNow
          have hMNowEq : MNow = selected.view.payload.downRecord i :=
            Option.some.inj (hMNow.symm.trans hchoiceLastNow)
          have hpayloadSigma : (selected.view.payload.downRecord i).val.sigma = start + 1 := by
            calc
              (selected.view.payload.downRecord i).val.sigma = MCurrent.val.sigma :=
                congrArg (fun M : DownRecord => M.val.sigma) hMCurrentEq.symm
              _ = start + 1 := hMCurrentSigma
          have hMNowSigma : MNow.val.sigma = start + 1 := by
            rw [hMNowEq]
            exact hpayloadSigma
          have htimeNow : MNow.val.sigma ≤ W[j].input.time.val := by
            have hjpos : 1 ≤ j := Nat.succ_le_iff.mpr hcurrentPos
            rw [hMNowSigma, hroundNow]
            omega
          have hstepNow := actual_occupied_finish_preserves W[j] i prevNext prevNextMemory
            nextNow nextMemoryNow hchoiceActualPrev hnextActual hprevNextOccupied hlocalPrev
            MNow hMNow htimeNow
          have hnextLastNow : nextNow.lastDown =
              some (selected.view.payload.downRecord i) := by
            exact hstepNow.2.trans hchoiceLastNow
          refine ⟨prevNext, prevNextMemory, nextNow, nextMemoryNow, prevNext,
            prevNextMemory, hchoiceActualPrev, hnextActual, hfailureNow, hcurrentInput,
            hlocalPrev, hprevNextOccupied, hchoiceLastNow, hpayloadSigma,
            ⟨tokenNow, hreadPrev, ?_, hbitNow⟩, hstartPrev, rfl, rfl,
            hprevNextOccupied, hstepNow.1, hchoiceLastNow, hnextLastNow, ?_⟩
          · exact hstampNow
          · intro selectedJ hselectedJ
            have hlastJ := actual_selection_lastDown initial rows J rewards start count hspan active
              hfirst seed memory hseed hS hdelta hbacklog hnone hunoccupied hvalid hpair htime hbatch
              ⟨j, hjlen⟩ selectedJ hselectedJ i prevNext prevNextMemory hchoiceActualPrev
              hprevNextOccupied
            exact Option.some.inj (hlastJ.symm.trans hchoiceLastNow)
  intro j hkj
  obtain ⟨choiceJ, choiceMemoryJ, next, nextMemory, incomingJ, incomingMemoryJ,
      hchoiceJ, hnextJ, hfailureJ, hinputJ, hlocalJ, hinputOccupiedJ, hlastJ,
      hsigmaJ, htokenJ, hstartJ, hchoiceEqJ, hmemoryEqJ, hchoiceOccupiedJ,
      hnextOccupiedJ, hchoiceLastJ, hnextLastJ, hselectedJ⟩ :=
    hfuture j.val hkj j.isLt
  refine ⟨choiceJ, choiceMemoryJ, next, nextMemory, incomingJ, incomingMemoryJ,
    hchoiceJ, hnextJ, hfailureJ, hinputJ, hlocalJ, hinputOccupiedJ, hlastJ,
    hsigmaJ, htokenJ, hstartJ, hchoiceEqJ, hmemoryEqJ, hchoiceOccupiedJ,
    hnextOccupiedJ, hchoiceLastJ, hnextLastJ, ?_⟩
  exact hselectedJ

end Bandits.Support.ReferenceFirstLiveOccupiedPersistence

end
