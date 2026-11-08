/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary

import Lean.Elab.Tactic.Omega

/-!
# First replacement cutoff DOWN recovery and follower finish

Sources: `sources/zip4/manuscript/06_interruptions.tex:9-70,193-233,246-295`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This internal result continues the actual PREPARE record from
`ReferenceFirstReplacementCutoffPreparedBoundary`. It runs that record's
logging, reference DOWN receiver, checked sparse recovery, and follower finish.
The receiver alternatives remain explicit; this theorem does not assert that
any particular decoding or acceptance branch occurs.
-/

@[expose] public section
noncomputable section

namespace Bandits.Support.ReferenceFirstReplacementCutoffDownRecovery

open _root_.Bandits.Support.ReferenceFirstReplacementCutoffPreparedBoundary

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws

local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private abbrev DownRecord :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

private theorem operation_input_of_local_domain
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localStateDomainValid state) :
    ActiveFollowerDownAcceptance.operationInputDomain p rate state := by
  refine ⟨h.1, h.2.2, ?_⟩
  refine ⟨?_, h.2.1.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.1.2.2 saved hsaved
  exact ⟨(h.2.1.1 saved hsaved).1, (h.2.1.1 saved hsaved).2,
    ⟨⟨q, by omega⟩, heq⟩⟩

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
        have hconserve : next.1 + next.2 =
            current.registers.1 + current.registers.2 + arrivalAt r := by
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
          T * D + min capacity (current.registers.2 + arrivalAt r) :=
        (hqueuePlusArrival.trans hnextBound).trans (Nat.le_add_right _ _)
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
          final.registers.1 + final.registers.2 ≤ (elapsed + 1 + rest.length) * D := hfinalMass
          _ = (elapsed + (rest.length + 1)) * D := by congr 1 <;> omega

private theorem sparseBufferContribution_zero_of_no_key
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hno : ∀ saved ∈ buffer, ¬ (saved.calendarRound = r ∧ saved.pilot = arm)) :
    sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => rfl
  | cons saved rest ih =>
      have hhead : ¬ (saved.calendarRound = r ∧ saved.pilot = arm) := hno saved List.mem_cons_self
      have htail : ∀ item ∈ rest, ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
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
    (hcontribution : ∀ saved ∈ buffer, saved.calendarRound = r → saved.pilot = arm →
      savedContribution p.K d (D : ℝ) eta h saved.observation saved.thinScalar ≤ D) :
    sparseBufferContribution d (D : ℝ) eta h arm r buffer ≤ D := by
  classical
  induction buffer with
  | nil => simp [sparseBufferContribution]
  | cons saved rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hkeys
      have htail : ∀ item ∈ rest, item.calendarRound = r → item.pilot = arm →
          savedContribution p.K d (D : ℝ) eta h item.observation item.thinScalar ≤ D := by
        intro item hi hr hp
        exact hcontribution item (List.mem_cons_of_mem _ hi) hr hp
      by_cases hkey : saved.calendarRound = r ∧ saved.pilot = arm
      · have hnotTail : ∀ item ∈ rest,
            ¬ (item.calendarRound = r ∧ item.pilot = arm) := by
          intro item hi hitem
          apply hkeys.1
          apply List.mem_map.mpr
          exact ⟨item, hi, Prod.ext (hitem.1.trans hkey.1.symm)
            (hitem.2.trans hkey.2.symm)⟩
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
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged) (r : ℕ) :
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
  · rw [SparseCalendarReplay.savedContribution_eq_floor_of_le p.K (p.m - 1)
      (D p : ℝ) rate.eta.val M.val.h saved.observation saved.thinScalar hthin]
    obtain ⟨own, hobs⟩ :=
      ActiveFollowerLifecycle.localBufferValid_observation_typed hvalid saved hsaved
    have hfloor := ActiveFollowerQueueOperation.sourceArrivalFloor_le_D rate.eta M own
    have hsame := ActiveFollowerQueueOperation.sourceArrivalFloor_eq_savedFloor rate.eta M own
    rw [hobs] at hsame
    rw [hsame] at hfloor
    exact hfloor
  · simp [SparseCalendarReplay.savedContribution, hthin]

private theorem checkedRecovery_cutoff_budget
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (ell : ℕ) (hstarted : M.val.sigma ≤ ell) (hspan : ell ≤ p.T) :
    ∃ recovered, ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok recovered ∧
      recovered.registers.1 + recovered.registers.2 ≤ (ell - 1) * D p ∧
      recovered.lastService ≤ D p := by
  have hrounds : (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).length =
      ell - M.val.sigma := ActiveFollowerDownAcceptance.recoveryRounds_length p rate M ell
  have hsigma : 1 ≤ M.val.sigma := PrelaunchBufferRecovery.down_sigma_pos rate.eta M
  have hcredit' : M.val.q ≤ (M.val.sigma - 1) * D p := hcredit
  let elapsed := M.val.sigma - 1
  let current : ActiveFollowerDownAcceptance.ReplayRegisters := ⟨(0, M.val.q), 0⟩
  obtain ⟨recovered, hchecked, hmass, hlast⟩ := checkedCalendarReplay_success_of_mass
    (D p) p.T (4 * rate.n) 0 elapsed current
    (ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged)
    (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell)
    (by simp [current]) hcredit' (by simp [current]) (by simpa [current] using hcredit')
    (four_n_le_D p rate)
    (fun r _ => bufferArrival_le_D M logged hvalid r)
    (by rw [hrounds]; dsimp [elapsed]; omega)
  refine ⟨recovered, ?_, ?_, hlast⟩
  · rw [ActiveFollowerDownAcceptance.checkedRecovery]
    simpa [current] using hchecked
  · have hlen : elapsed +
        (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).length = ell - 1 := by
      rw [hrounds]
      dsimp [elapsed]
      omega
    rw [hlen] at hmass
    exact hmass

private theorem down_buffer_domain (state : ReferencePrelaunchFollower.State p rate.eta)
    (h : ActiveFollowerLifecycle.localBufferValid state) :
    ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
  refine ⟨?_, h.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.2 saved hsaved
  exact ⟨(h.1 saved hsaved).1, (h.1 saved hsaved).2, ⟨q, by omega⟩, heq⟩

private theorem logging_chronology
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (choice logged : ReferencePrelaunchFollower.State p rate.eta)
    (hbuffer : logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i row activation t own)
    (hpair : choice.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hbefore : ∀ saved ∈ choice.buffer, saved.calendarRound < t.val + 1) :
    logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      ∀ saved ∈ logged.buffer, saved.calendarRound < t.val + 2 := by
  rw [hbuffer]
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hpair, ?_, ?_⟩
    · unfold ReferencePrelaunchFollower.logAt
      split <;> simp only [List.pairwise_singleton, List.Pairwise.nil]
    · intro a ha b hb
      rw [(ActiveFollowerLogging.logAt_member_fields i row activation t own b hb).1]
      exact hbefore a ha
  · intro saved hsaved
    rcases List.mem_append.mp hsaved with hsaved | hsaved
    · exact Nat.lt_trans (hbefore saved hsaved) (by omega)
    · have ht := (ActiveFollowerLogging.logAt_member_fields i row activation t own saved hsaved).1
      omega

private theorem logged_eq_old_on_down
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (old logged : ReferencePrelaunchFollower.State p rate.eta)
    (hlogging : ActiveFollowerLogging.checkedLogging i row activation t own old = .ok logged)
    (hdown : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot) :
    logged = old := by
  classical
  have htests : ¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i row activation t own) := by
    intro h
    have hdata := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask
      i row activation t own).mp h |>.2.1
    rw [hdown] at hdata
    cases hdata
  have hnil := ActiveFollowerLogging.logAt_eq_nil_of_not_tests i row activation t own htests
  have heq := ((ActiveFollowerLogging.checkedLogging_success_iff
      i row activation t own old logged).mp hlogging).2.1
  rw [heq]
  unfold ActiveFollowerLogging.loggingUpdate
  split <;> simp only [hnil, List.append_nil]

private theorem parse_stored_word (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) :
    ReferenceDownReception.ordinaryParse p rate
      (some (CoordinatorLocalArmChoice.storedDownFlatWord payload i)) =
      some (payload.downRecord i) := by
  unfold ReferenceDownReception.ordinaryParse CoordinatorLocalArmChoice.storedDownFlatWord
  change OrdinaryMessageCodec.parseDown (ReferencePrelaunchFollower.codecParams p rate.eta)
    (some ((OrdinaryMessageCodec.wordEquivFlat _).symm
      ((OrdinaryMessageCodec.wordEquivFlat _) (payload.downWord i)))) = _
  exact (congrArg (fun word => OrdinaryMessageCodec.parseDown
    (ReferencePrelaunchFollower.codecParams p rate.eta) (some word))
      ((OrdinaryMessageCodec.wordEquivFlat _).symm_apply_apply
        (payload.downWord i))).trans (payload.parseDown_downWord i)

private theorem cutoff_expected_word {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hpending : selected.view.pendingAtChoice = Finset.univ) (i : Fin (p.m - 1)) :
    ReferenceDownReception.expectedDownFlatWord (some selected.view) i x.row x.time =
      if ActiveFollowerDownAcceptance.downSelected p i x.row x.time then
        some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) else none := by
  classical
  have hb : ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time ↔
      ActiveFollowerDownAcceptance.downSelected p i x.row x.time := by
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hpending ▸ Finset.mem_univ i⟩
  by_cases hsel : ActiveFollowerDownAcceptance.downSelected p i x.row x.time
  · rw [if_pos hsel]
    exact selected.expected_down_word i (hb.mpr hsel)
  · have hn : ¬ (CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff x.time
        selected.view.complementWeights x.row ≠ none ∧
        ReferenceDownReception.selectedDownSenderBranch selected.view i x.row x.time) :=
      fun h => hsel (hb.mp h.2)
    simp only [ReferenceDownReception.expectedDownFlatWord,
      ite_eq_right hn, ite_eq_right hsel]
    rfl

private theorem accepted_cutoff_endpoint
    (M : DownRecord (p := p) (rate := rate)) (t : Fin p.T)
    (row : CompletePublicTable.CompleteRow p)
    (hstart : (ActiveFollowerDownAcceptance.downStart p rate M).val ≤ t.val)
    (sigma : Fin p.T)
    (hdownStart : ActiveFollowerDownAcceptance.downStart p rate M = sigma)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = t.val + 1)
    (hgrid : t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val sigma) :
    (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t hstart row).endpoint =
      t.val + 1 := by
  unfold ActiveFollowerDownAcceptance.acceptedCutoffScan
    FollowerCutoffScan.completeRowCutoffScan
  rw [FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff]
  rw [hdownStart, hfirst]
  exact Nat.min_eq_left (by omega)

private theorem cutoff_record_success
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselection : record.output.preparation.coordinator.selection = some selected)
    (hpending : selected.view.pendingAtChoice = Finset.univ)
    (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hinput : record.input.state.followers i = .ordinary old memory)
    (hchoiceEq : choice = { old with status := .unoccupied })
    (hprepared : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hchoiceStatus : choice.status = .unoccupied)
    (hdomain : ActiveFollowerLifecycle.localStateDomainValid choice)
    (hmass : choice.S + choice.backlog ≤ record.input.time.val * D p)
    (hpair : choice.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hbefore : ∀ saved ∈ choice.buffer, saved.calendarRound < record.input.time.val + 1)
    (hstrict : old.status = .unoccupied →
      ReferencePrelaunchFollower.acceptedStart old <
        (selected.view.payload.downRecord i).val.sigma)
    (hbusy : old.status ≠ .unoccupied →
      old.lastDown = some (selected.view.payload.downRecord i) ∧
        ∃ token : ActiveFollowerLifecycle.ProposalRead p,
          memory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = record.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit
            p rate.eta.val record.input.row token.timestamp)
    (hfirst : FollowerCutoffScan.firstCutoff p rate.eta.val selected.view.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) =
        record.input.time.val + 1)
    (hgrid : record.input.time.val + 1 ≤
      FollowerCutoffScan.gridBoundary p rate.eta.val selected.view.payload.sigma)
    (hcredit : (selected.view.payload.downRecord i).val.q ≤
      ((selected.view.payload.downRecord i).val.sigma - 1) * D p)
    (hstarted : (selected.view.payload.downRecord i).val.sigma ≤ record.input.time.val) :
    let prepared := record.output.preparation.followers.followers i
    let own := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := record.output.preparation.coordinator.downView
    let M := selected.view.payload.downRecord i
    ∃ logged post,
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time (prepared.arm, own) choice = .ok logged ∧
      logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time (prepared.arm, own) ∧
      ActiveFollowerDownAcceptance.operationInputDomain p rate logged ∧
      logged.lastDown = choice.lastDown ∧ logged.S = choice.S ∧
      logged.delta = choice.delta ∧ logged.backlog = choice.backlog ∧
      logged.initializationFailure = choice.initializationFailure ∧
      logged.status = .unoccupied ∧
      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ logged.buffer, saved.calendarRound < record.input.time.val + 2) ∧
      (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time →
        logged = choice) ∧
      let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
        p i record.input.row record.input.time own rate logged
      let cut := ReferenceDownReception.referenceDownCut p view i record.input.row
        record.input.time own rate logged
      let advanced := { logged with downBatch := decoded.1 }
      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post ∧
      post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
      post.S + post.backlog ≤ record.input.time.val * D p ∧ post.delta ≤ D p ∧
      post.initializationFailure = old.initializationFailure ∧
      ( (¬ ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
          cut.outcome = .skipped logged .notSelectedDown ∧ post = logged) ∨
        (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
          cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord
            selected.view.payload i) ∧ decoded.2 ≠ cut.expectedWord ∧
          cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧ cut.rawComparison = some false ∧
          cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
          (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
            p rate record.input.time logged
              (ReferenceDownReception.ordinaryParse p rate decoded.2)) ∧
          cut.outcome = .decodeOrParseRejected logged advanced decoded.2 ∧ post = advanced) ∨
        (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
          decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord
            selected.view.payload i) ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
          cut.rawComparison = some true ∧ cut.ordinaryParse = some M ∧
          ¬ cut.ordinaryAcceptance ∧
          cut.outcome = .parsedButUnaccepted logged advanced decoded.2 M ∧ post = advanced ∧
          (old.status ≠ .unoccupied →
            ReferencePrelaunchFollower.acceptedStart logged = M.val.sigma)) ∨
        (ActiveFollowerDownAcceptance.downSelected p i record.input.row record.input.time ∧
          decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord
            selected.view.payload i) ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
          cut.rawComparison = some true ∧ cut.ordinaryParse = some M ∧
          cut.ordinaryAcceptance ∧
          ∃ accepted : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart logged) (record.input.time.val + 1) M,
            let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M
              record.input.time
              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M record.input.time logged accepted)
              record.input.row
            ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
              ActiveFollowerDownAcceptance.checkedRecovery p rate M logged
                (record.input.time.val + 1) = .ok recovered ∧
              scan.endpoint = record.input.time.val + 1 ∧
              ActiveFollowerDownAcceptance.recoveryRounds p rate M (record.input.time.val + 1) =
                SparseCalendarReplay.sparseCalendarRounds M.val.sigma
                  (record.input.time.val + 1) ∧
              ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                  (record.input.time.val + 1) =
                ((ActiveFollowerDownAcceptance.recoveryArrivals p rate M logged
                  (record.input.time.val + 1)).map fun arrival => (true, arrival)) ∧
              (∀ q ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                  (record.input.time.val + 1), q.1 = true) ∧
              recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                  (record.input.time.val + 1)) ∧
              (∀ k, ∃ middle,
                ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p)
                  (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩
                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                    (record.input.time.val + 1)).take k) = .ok middle ∧
                ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
                middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                  ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                    (record.input.time.val + 1)).take k)) ∧
              (∀ hstarted : M.val.sigma ≤ record.input.time.val,
                recovered.lastService = ActiveFollowerDownAcceptance.recoveredLastService
                  p rate M logged (record.input.time.val + 1)
                    (Nat.lt_succ_of_le hstarted)) ∧
              cut.outcome = .accepted logged post decoded.2 M scan
                recovered.registers recovered.lastService ∧
              post = { advanced with
                lastDown := some M
                S := recovered.registers.1
                delta := recovered.lastService
                backlog := recovered.registers.2
                status := .unoccupied
                buffer := [] })) := by
  classical
  intro prepared own view M
  obtain ⟨logged, hlogging, hbuffer, hlogStatus, hlogFlag, hloggingValid⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i record.input.row
      (record.input.state.activations i) record.input.time (prepared.arm, own) choice
      hdomain.2.1 hbefore hchoiceStatus
  let decoded := ActiveFollowerDownAcceptance.currentDecodeStep
    p i record.input.row record.input.time own rate logged
  let cut := ReferenceDownReception.referenceDownCut p view i record.input.row
    record.input.time own rate logged
  let advanced := { logged with downBatch := decoded.1 }
  have hframe := ActiveFollowerLogging.checkedLogging_success_frame i record.input.row
    (record.input.state.activations i) record.input.time (prepared.arm, own) choice logged hlogging
  have hlu : logged.status = .unoccupied := hlogStatus.trans hchoiceStatus
  have hlogDomain : ActiveFollowerLifecycle.localStateDomainValid logged := by
    refine ⟨?_, hloggingValid, ?_⟩
    · simpa only [ActiveFollowerLifecycle.serviceRegistersValid,
        hframe.2.1, hframe.2.2.1, hframe.2.2.2.1] using hdomain.1
    · simpa only [ActiveFollowerLifecycle.downDecoderStateValid, hframe.2.2.2.2.2.1]
        using hdomain.2.2
  have hlogMass : logged.S + logged.backlog ≤ record.input.time.val * D p := by
    simpa only [hframe.2.1, hframe.2.2.2.1] using hmass
  have hdeltaLogged : logged.delta ≤ D p := by
    simpa only [hframe.2.2.1] using hdomain.1.2.1
  have hchron := logging_chronology i record.input.row (record.input.state.activations i)
    record.input.time (prepared.arm, own) choice logged hbuffer hpair hbefore
  have hoperation := operation_input_of_local_domain logged hlogDomain
  have hbusyLogged : old.status ≠ .unoccupied →
      ReferencePrelaunchFollower.acceptedStart logged = M.val.sigma := by
    intro ho
    obtain ⟨hdown, _, _⟩ := hbusy ho
    have hdownChoice : choice.lastDown = some M := by simpa [hchoiceEq] using hdown
    have hlast : logged.lastDown = some M := hframe.1.trans hdownChoice
    simpa only [ReferencePrelaunchFollower.acceptedStart, hlast] using rfl
  have hchoiceFlag : choice.initializationFailure = old.initializationFailure := by
    simpa [hchoiceEq]
  have hloggedFlag : logged.initializationFailure = old.initializationFailure :=
    hframe.2.2.2.2.2.2.trans hchoiceFlag
  have hstep := AffineBatchDecoder.step_spec p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (ActiveFollowerDownAcceptance.currentRoundInput p i record.input.row record.input.time
        own rate logged)) logged.downBatch record.input.time
      hoperation.2.1.1 hoperation.2.1.2
  have hstepBatch : ActiveFollowerDownAcceptance.decoderInputDomain p decoded.1 := by
    dsimp only [decoded, ActiveFollowerDownAcceptance.currentDecodeStep]
    exact ⟨hstep.1, hstep.2.1⟩
  have hadvanced : ActiveFollowerLifecycle.localStateDomainValid advanced := by
    exact ⟨hlogDomain.1, hlogDomain.2.1, hstepBatch⟩
  have hlogBufferPair := hchron.1
  have hview : view = some selected.view := by
    change Option.map (fun s : ReferenceActivePhysicalStep.Selection record.input => s.view)
        record.output.preparation.coordinator.selection = some selected.view
    rw [hselection]
    rfl
  have hexpected := cutoff_expected_word selected hpending i
  rw [← hview] at hexpected
  have hdownNoAppend : ActiveFollowerDownAcceptance.downSelected p i
      record.input.row record.input.time → logged = choice := by
    intro hdown
    exact logged_eq_old_on_down i record.input.row (record.input.state.activations i)
      record.input.time (prepared.arm, own) choice logged hlogging hdown.1
  by_cases hselected : ActiveFollowerDownAcceptance.downSelected p i record.input.row
      record.input.time
  · have hstored := hexpected
    rw [if_pos hselected] at hstored
    by_cases hmatches : decoded.2 = ReferenceDownReception.expectedDownFlatWord
        view i record.input.row record.input.time
    · have hmatchesExpected := hmatches
      rw [hstored] at hmatches
      dsimp only [decoded] at hmatchesExpected
      have hparse : ReferenceDownReception.ordinaryParse p rate decoded.2 = some M := by
        rw [hmatches]
        exact parse_stored_word selected.view.payload i
      have hparseActual : ReferenceDownReception.ordinaryParse p rate
          (ActiveFollowerDownAcceptance.currentDecodeStep p i record.input.row
            record.input.time own rate logged).2 = some M := by
        simpa only [decoded] using hparse
      by_cases haccepted : OrdinaryMessageCodec.acceptDown
          (ReferencePrelaunchFollower.codecParams p rate.eta)
          (ReferencePrelaunchFollower.acceptedStart logged)
          (record.input.time.val + 1) M
      · have hscanStart := ActiveFollowerDownAcceptance.acceptedDownStartLE
          p rate M record.input.time logged haccepted
        have hMsigma : M.val.sigma = selected.view.payload.sigma.val + 1 := by
          change (selected.view.payload.downRecord i).val.sigma = _
          rw [selected.view.payload.downRecord_fields i]
        have hdownStart : ActiveFollowerDownAcceptance.downStart p rate M =
            selected.view.payload.sigma := by
          apply Fin.ext
          have h := ActiveFollowerDownAcceptance.downStart_val_add_one p rate M
          rw [hMsigma] at h
          omega
        let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M
          record.input.time
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M record.input.time logged haccepted)
          record.input.row
        have hscan : scan.endpoint = record.input.time.val + 1 := by
          exact accepted_cutoff_endpoint M record.input.time record.input.row
            (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M
              record.input.time logged haccepted)
            selected.view.payload.sigma hdownStart hfirst hgrid
        have hstarted' : M.val.sigma ≤ record.input.time.val := by
          simpa only [M] using hstarted
        have hinterval : M.val.sigma < record.input.time.val + 1 := by omega
        obtain ⟨recovered, hchecked, hfinalMass, hlast⟩ := checkedRecovery_cutoff_budget
          M logged hcredit hlogDomain.2.1 (record.input.time.val + 1) (by omega) (by omega)
        have hsuccess := ActiveFollowerDownAcceptance.checkedRecovery_success
          p rate M logged (record.input.time.val + 1) recovered hchecked
        have hprefix : ∀ k, ∃ middle,
            ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
              ⟨(0, M.val.q), 0⟩
              ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                (record.input.time.val + 1)).take k) = .ok middle ∧
            ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
            middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                (record.input.time.val + 1)).take k) := by
          intro k
          exact ActiveFollowerDownAcceptance.checkedRecovery_success_prefix p rate M logged
            (record.input.time.val + 1) recovered hchecked k
        let post := { advanced with
          lastDown := some M
          S := recovered.registers.1
          delta := recovered.lastService
          backlog := recovered.registers.2
          status := ActiveRoundActions.FollowerStatus.unoccupied
          buffer := [] }
        have hpostDomain : ActiveFollowerLifecycle.localStateDomainValid post := by
          obtain ⟨hS, hdeltaBound, hbacklog⟩ := hsuccess.1
          refine ⟨⟨hS, hdeltaBound, hbacklog⟩, ?_, ?_⟩
          · simp [ActiveFollowerLifecycle.localBufferValid, post]
          · change ActiveFollowerDownAcceptance.decoderInputDomain p post.downBatch
            simpa only [ActiveFollowerDownAcceptance.decoderInputDomain,
              ActiveFollowerLifecycle.downDecoderStateValid, post, advanced] using
                hstepBatch
        have hfinalExact : recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
            (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
              (record.input.time.val + 1)) := hsuccess.2.1
        have hlastExact : ∀ hstarted : M.val.sigma ≤ record.input.time.val,
            recovered.lastService = ActiveFollowerDownAcceptance.recoveredLastService
              p rate M logged (record.input.time.val + 1) (Nat.lt_succ_of_le hstarted) := by
          intro hstarted
          exact ActiveFollowerDownAcceptance.checkedRecovery_success_last_service
            p rate M logged (record.input.time.val + 1)
            (Nat.lt_succ_of_le hstarted) recovered hchecked
        have hmassPost : post.S + post.backlog ≤ record.input.time.val * D p := by
          simpa [post] using hfinalMass
        have hcutOutcome : cut.outcome = .accepted logged post decoded.2 M scan
            recovered.registers recovered.lastService := by
          have hne : record.input.time.val + 1 ≠ record.input.time.val + 2 := by omega
          simp only [cut, ReferenceDownReception.referenceDownCut,
            dite_eq_left hselected, dite_eq_left hlu,
            dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
            dite_eq_left hoperation.2.2,
            dite_eq_left hmatchesExpected,
            decoded, advanced, post, hparseActual, dite_eq_left haccepted,
            scan, hscan, hchecked, ite_eq_right hne]
        have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post := by
          rw [hcutOutcome]
          rfl
        have hrounds : ActiveFollowerDownAcceptance.recoveryRounds p rate M
            (record.input.time.val + 1) =
            SparseCalendarReplay.sparseCalendarRounds M.val.sigma
              (record.input.time.val + 1) := rfl
        have hallEnabled := ActiveFollowerDownAcceptance.recoveryQueueRecords_all_enabled
          p rate M logged (record.input.time.val + 1)
        have hlength := ActiveFollowerDownAcceptance.recoveryRounds_length p rate M
          (record.input.time.val + 1)
        have hflag : post.initializationFailure = old.initializationFailure := by
          simp [post, advanced, hloggedFlag]
        refine ⟨logged, post, hlogging, hbuffer, hoperation, hframe.1, hframe.2.1,
          hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.2.2, hlu, hchron.1, hchron.2,
          hdownNoAppend, hconsume, ?_, hpostDomain, hmassPost, ?_, hflag,
          Or.inr (Or.inr (Or.inr ?_))⟩
        · exact (by simp [post])
        · simpa [post] using hlast
        · refine ⟨hselected, ?_⟩
          refine ⟨by simpa [hstored] using hmatches, ?_⟩
          have hcutRaw : cut.raw = decoded.2 := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected, decoded]
          have hcutFiltered : cut.filteredRaw = decoded.2 := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected, decoded]
          have hcutComparison : cut.rawComparison = some true := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected, decoded]
          have hcutParse : cut.ordinaryParse = some M := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected,
              decoded, hparseActual]
          have hcutAcceptance : cut.ordinaryAcceptance := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2, dite_eq_left hmatchesExpected,
              decoded, hparseActual, ReferenceDownReception.ordinaryLocalAcceptanceTest,
              haccepted]
          refine ⟨hcutRaw, hcutFiltered, hcutComparison, hcutParse,
            hcutAcceptance, ?_⟩
          refine ⟨haccepted, ?_⟩
          refine ⟨recovered, ?_⟩
          exact ⟨hchecked, hscan, hrounds, rfl, hallEnabled,
            hfinalExact, hprefix, hlastExact, hcutOutcome, rfl⟩
      · have hcutOutcome : cut.outcome = .parsedButUnaccepted logged advanced decoded.2 M := by
          simp only [cut, ReferenceDownReception.referenceDownCut,
            dite_eq_left hselected, dite_eq_left hlu,
            dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
            dite_eq_left hoperation.2.2,
            dite_eq_left hmatchesExpected,
              decoded, advanced, hparseActual, dite_eq_right haccepted]
        have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok advanced := by
          rw [hcutOutcome]
          rfl
        have hmarker : advanced.initializationFailure = old.initializationFailure := by
          simpa [advanced] using hloggedFlag
        have hdelta : advanced.delta ≤ D p := by
          simpa only [advanced] using hdeltaLogged
        have hmassAdvanced : advanced.S + advanced.backlog ≤ record.input.time.val * D p := by
          simpa [advanced] using hlogMass
        refine ⟨logged, advanced, hlogging, hbuffer, hoperation, hframe.1, hframe.2.1,
          hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.2.2, hlu, hchron.1, hchron.2,
          hdownNoAppend, hconsume, ?_, hadvanced, hmassAdvanced, hdelta, hmarker,
          Or.inr (Or.inr (Or.inl ?_))⟩
        · exact (by simpa [advanced] using hlu)
        · refine ⟨hselected, ?_⟩
          refine ⟨by simpa [hstored] using hmatches, ?_⟩
          have hnotAccepted : ¬ cut.ordinaryAcceptance := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2,
              dite_eq_left hmatchesExpected, decoded, hparseActual,
              ReferenceDownReception.ordinaryLocalAcceptanceTest, haccepted]
            exact not_false
          have hcutRaw : cut.raw = decoded.2 := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2,
              dite_eq_left hmatchesExpected, decoded]
          have hcutFiltered : cut.filteredRaw = decoded.2 := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2,
              dite_eq_left hmatchesExpected, decoded, hparseActual]
          have hcutComparison : cut.rawComparison = some true := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2,
              dite_eq_left hmatchesExpected, decoded, hparseActual]
          have hcutParse : cut.ordinaryParse = some M := by
            simp only [cut, ReferenceDownReception.referenceDownCut,
              dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
              dite_eq_left hoperation.2.2,
              dite_eq_left hmatchesExpected, decoded, hparseActual]
          exact ⟨hcutRaw, hcutFiltered, hcutComparison, hcutParse,
            hnotAccepted, hcutOutcome, rfl, hbusyLogged⟩
    · have hcutOutcome : cut.outcome = .decodeOrParseRejected logged advanced decoded.2 := by
        simp only [cut, ReferenceDownReception.referenceDownCut,
          dite_eq_left hselected, dite_eq_left hlu,
          dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
          dite_eq_left hoperation.2.2,
          decoded, dite_eq_right (by simpa [decoded] using hmatches)]
        rfl
      have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok advanced := by
        rw [hcutOutcome]
        rfl
      have hmarker : advanced.initializationFailure = old.initializationFailure := by
        simpa [advanced] using hloggedFlag
      have hdelta : advanced.delta ≤ D p := by simpa only [advanced] using hdeltaLogged
      have hmassAdvanced : advanced.S + advanced.backlog ≤ record.input.time.val * D p := by
        simpa [advanced] using hlogMass
      refine ⟨logged, advanced, hlogging, hbuffer, hoperation, hframe.1, hframe.2.1,
        hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.2.2, hlu, hchron.1, hchron.2,
        hdownNoAppend, hconsume, ?_, hadvanced, hmassAdvanced, hdelta, hmarker,
        Or.inr (Or.inl ?_)⟩
      · exact (by simpa [advanced] using hlu)
      · refine ⟨hselected, ?_⟩
        have hcutExpected : cut.expectedWord = some
            (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) := by
          simp only [cut, ReferenceDownReception.referenceDownCut,
            dite_eq_left hselected, dite_eq_left hlu,
            dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
            dite_eq_left hoperation.2.2,
            dite_eq_right (by simpa [decoded] using hmatches)]
          exact hstored
        have hstoredMismatch : decoded.2 ≠
            some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) := by
          intro heq
          apply hmatches
          rw [hstored]
          exact heq
        have hcutMismatch : decoded.2 ≠ cut.expectedWord := by
          rw [hcutExpected]
          exact hstoredMismatch
        have hcutRaw : cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
            cut.rawComparison = some false ∧
            cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
            (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest
              p rate record.input.time logged
                (ReferenceDownReception.ordinaryParse p rate decoded.2)) := by
          simp only [cut, ReferenceDownReception.referenceDownCut,
            dite_eq_left hselected, dite_eq_left hlu,
            dite_eq_left hoperation.1, dite_eq_left hoperation.2.1,
            dite_eq_left hoperation.2.2,
            decoded, dite_eq_right (by simpa [decoded] using hmatches)]
          exact ⟨trivial, trivial, trivial, trivial, trivial⟩
        exact ⟨hcutExpected, hcutMismatch, hcutRaw.1, hcutRaw.2.1,
          hcutRaw.2.2.1, hcutRaw.2.2.2.1, hcutRaw.2.2.2.2,
          hcutOutcome, rfl⟩
  · have hcutOutcome : cut.outcome = .skipped logged .notSelectedDown := by
      simp [cut, ReferenceDownReception.referenceDownCut, hselected]
    have hconsume : DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok logged := by
      rw [hcutOutcome]
      rfl
    have hmarker : logged.initializationFailure = old.initializationFailure := hloggedFlag
    have hdelta : logged.delta ≤ D p := by simpa only [hframe.2.2.1] using hdomain.1.2.1
    exact ⟨logged, logged, hlogging, hbuffer, hoperation, hframe.1, hframe.2.1,
      hframe.2.2.1, hframe.2.2.2.1, hframe.2.2.2.2.2.2, hlu, hchron.1, hchron.2,
      hdownNoAppend, hconsume, hlu, hlogDomain, hlogMass, hdelta, hmarker,
      Or.inl ⟨hselected, hcutOutcome, rfl⟩⟩

private theorem cutoff_finish_actual
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice logged post : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : (record.output.preparation.followers.followers i).configuration =
      .ordinary choice memory)
    (hchoiceStatus : choice.status = .unoccupied)
    (hlogging : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      ((record.output.preparation.followers.followers i).arm,
        record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice = .ok logged)
    (hconsume : DeclaredFollowerLocalRound.consumeDownResult rate
      (ReferenceDownReception.referenceDownCut p record.output.preparation.coordinator.downView
        i record.input.row record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome = .ok post)
    (hpostDomain : ActiveFollowerLifecycle.localStateDomainValid post)
    (hpostUnoccupied : post.status = .unoccupied)
    (hmass : post.S + post.backlog ≤ (record.input.time.val + 1) * D p)
    (hmarker : post.initializationFailure = choice.initializationFailure) :
    DeclaredFollowerLocalRound.consumeDownResult rate
        (ReferenceDownReception.referenceDownCut p record.output.preparation.coordinator.downView
          i record.input.row record.input.time
          (record.output.preparation.feedback.observations
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged).outcome = .ok post ∧
    ActiveFollowerLifecycle.releaseAfterService rate.eta i record.input.time
      (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post = .ok post ∧
    ActiveFollowerLifecycle.finishRound rate.eta record.input.time record.input.row post memory =
      .ok (post, memory) ∧
    DeclaredFollowerLocalRound.releaseAndFinish rate i record.input.row record.input.time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice memory post = .ok (post, memory) ∧
    record.output.followers i = ⟨.ordinary post memory, none,
      some logged, some (ReferenceDownReception.referenceDownCut p
        record.output.preparation.coordinator.downView i record.input.row record.input.time
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) rate logged)⟩ ∧
    ActiveFollowerLifecycle.localStateDomainValid post ∧
    post.S + post.backlog ≤ (record.input.time.val + 1) * D p ∧ post.delta ≤ D p ∧
    post.initializationFailure = choice.initializationFailure := by
  classical
  have hrelease := ActiveFollowerLifecycle.releaseAfterService_unoccupied rate.eta i
    record.input.time
    (ActiveFollowerLifecycle.publicRowOfCompleteRow record.input.row record.input.time)
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice post hchoiceStatus
  have hfinish := ActiveFollowerLifecycle.finishRound_unoccupied rate.eta
    record.input.time record.input.row post memory hpostDomain hpostUnoccupied
  have htail := DeclaredFollowerLocalRound.releaseAndFinish_unoccupied_memory rate i
    record.input.row record.input.time
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice memory post post
    hrelease hpostDomain hpostUnoccupied
  have halign := record.output.preparation.follower_alignment i
  have hrecord : (ReferenceActivePhysicalStep.recordFollower
      record.output.preparation.coordinator.downView i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.output.preparation.followers.followers i).arm
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hchoiceStatus,
      hlogging, hconsume]
  have hdiagnostic := ReferenceActivePhysicalStep.recordFollower_logged
    record.output.preparation.coordinator.downView i record.input.row
    (record.input.state.activations i) record.input.time (record.input.active i)
    (record.output.preparation.followers.followers i).arm
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice logged
    hchoiceStatus hlogging
  have hresultP : (ReferenceActivePhysicalStep.recordFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.followers.followers i).active
      (record.output.preparation.followers.followers i).arm
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice).result = .ok post := by
    simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hrecord
  have htailP : DeclaredFollowerLocalRound.releaseAndFinish rate
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) choice memory post =
      .ok (post, memory) := by
    simpa only [halign.1, halign.2.1, halign.2.2.1] using htail
  refine ⟨hconsume, hrelease, hfinish, htail, ?_, hpostDomain, hmass,
    hpostDomain.1.2.1, hmarker⟩
  have hout : record.output.followers i = record.output.preparation.observeFollower i := by
    rw [record.output_eq]
    rfl
  rw [hout]
  unfold ReferenceActivePhysicalStep.PreparedRound.observeFollower
    ReferenceActivePhysicalStep.finishFollower
  simp only [hconfiguration, hresultP, htailP]
  congr 1
  · simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostic.1
  · simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostic.2

/-- The same source-selected first replacement cutoff record as the prepared
boundary, continued through actual logging, DOWN reception, checked calendar
recovery, and follower FINISH. All scope selectors remain inside the result.
-/
theorem complete_first_replacement_cutoff_down_recovery_and_finish
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
        match R[v + 1 + tail.length]? with
        | none => True
        | some r =>
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen r = false ∧
          match r.output.preparation.coordinator with
          | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            registers.payload = payload ∧
            r.input.time.val = birth.input.time.val + 1 + tail.length ∧
            r.input.time.val = s + v + 1 + tail.length ∧
            r.input.rows = source.1.2 ∧
            r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
            r.input.rewards = rewards ∧
            payload.sigma.val = birth.input.time.val ∧
            s < payload.sigma.val ∧
            FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) =
                r.input.time.val + 1 ∧
            r.input.time.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
            (FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma = r.input.time.val + 1 ∨
              ∃ stamp : Fin p.T,
                registers.priorClock.lastProposal = some (stamp, true) ∧
                stamp.val + 1 = r.input.time.val ∧
                FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row stamp = true) ∧
            ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
              r.output.preparation.coordinator.selection = some selected ∧
              selected.view.payload = payload ∧ selected.view.pendingAtChoice = Finset.univ ∧
              selected.view.cutoff = some (CoordinatorCollectionUpRoundStep.localCutoff r.input.time) ∧
              ∀ i : Fin (p.m - 1),
                ∃ old : ReferencePrelaunchFollower.State p rate.eta,
                  ∃ memory : ActiveFollowerLifecycle.LocalMemory p,
                    r.input.state.followers i = .ordinary old memory ∧
                    ActiveFollowerLifecycle.localStateDomainValid old ∧
                    old.S + old.backlog ≤ r.input.time.val * D p ∧
                    (old.lastDown = none → old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∧
                    (old.status = .unoccupied →
                      ReferencePrelaunchFollower.acceptedStart old < (payload.downRecord i).val.sigma) ∧
                    (old.status ≠ .unoccupied → old.lastDown = some (payload.downRecord i) ∧
                      ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                        memory.lastProposalRead = some token ∧ token.timestamp.val + 1 = r.input.time.val ∧
                        token.bit = FollowerCutoffScan.completeRowProposalBit
                          p rate.eta.val r.input.row token.timestamp) ∧
                    let c : ReferencePrelaunchFollower.State p rate.eta :=
                      { old with status := .unoccupied }
                    ActiveFollowerLifecycle.interruptionDecision rate.eta r.input.time old memory =
                      .ok (decide (old.status ≠ .unoccupied)) ∧
                    ActiveFollowerLifecycle.startRound rate.eta r.input.time old memory = .ok (c, memory) ∧
                    (r.output.preparation.followers.followers i).configuration = .ordinary c memory ∧
                    ActiveFollowerLifecycle.localStateDomainValid c ∧
                    c.S + c.backlog ≤ r.input.time.val * D p ∧
                    c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                    (∀ saved ∈ c.buffer, saved.calendarRound < r.input.time.val + 1) ∧
                    OrdinaryMessageCodec.upAdmissible (ReferencePrelaunchFollower.codecParams p rate.eta)
                      (ActiveFollowerQueueOperation.upOfferFields c) ∧
                    (payload.downRecord i).val.sigma ≤ r.input.time.val ∧
                    (payload.downRecord i).val.q ≤ ((payload.downRecord i).val.sigma - 1) * D p ∧
                    let prepared := r.output.preparation.followers.followers i
                    let own := r.output.preparation.feedback.observations (followerPlayer p.two_le_m i)
                    let view := r.output.preparation.coordinator.downView
                    let M := payload.downRecord i
                    ∃ logged post,
                      ActiveFollowerLogging.checkedLogging i r.input.row
                        (r.input.state.activations i) r.input.time (prepared.arm, own) c = .ok logged ∧
                      logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i r.input.row
                        (r.input.state.activations i) r.input.time (prepared.arm, own) ∧
                      ActiveFollowerDownAcceptance.operationInputDomain p rate logged ∧
                      logged.lastDown = c.lastDown ∧ logged.S = c.S ∧ logged.delta = c.delta ∧
                      logged.backlog = c.backlog ∧ logged.initializationFailure = c.initializationFailure ∧
                      logged.status = .unoccupied ∧
                      logged.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
                      (∀ saved ∈ logged.buffer, saved.calendarRound < r.input.time.val + 2) ∧
                      (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time → logged = c) ∧
                      let decoded := ActiveFollowerDownAcceptance.currentDecodeStep p i r.input.row
                        r.input.time own rate logged
                      let cut := ReferenceDownReception.referenceDownCut p view i r.input.row
                        r.input.time own rate logged
                      let advanced := { logged with downBatch := decoded.1 }
                      DeclaredFollowerLocalRound.consumeDownResult rate cut.outcome = .ok post ∧
                      post.status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid post ∧
                      post.S + post.backlog ≤ r.input.time.val * D p ∧ post.delta ≤ D p ∧
                      post.initializationFailure = old.initializationFailure ∧
                      ((¬ ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                        cut.outcome = .skipped logged .notSelectedDown ∧ post = logged) ∨
                       (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                        cut.expectedWord = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                        decoded.2 ≠ cut.expectedWord ∧ cut.raw = decoded.2 ∧ cut.filteredRaw = none ∧
                        cut.rawComparison = some false ∧
                        cut.ordinaryParse = ReferenceDownReception.ordinaryParse p rate decoded.2 ∧
                        (cut.ordinaryAcceptance ↔ ReferenceDownReception.ordinaryLocalAcceptanceTest p rate
                          r.input.time logged (ReferenceDownReception.ordinaryParse p rate decoded.2)) ∧
                        cut.outcome = .decodeOrParseRejected logged advanced decoded.2 ∧ post = advanced) ∨
                       (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                        decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                        cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
                        cut.rawComparison = some true ∧ cut.ordinaryParse = some M ∧
                        ¬ cut.ordinaryAcceptance ∧
                        cut.outcome = .parsedButUnaccepted logged advanced decoded.2 M ∧ post = advanced ∧
                        (old.status ≠ .unoccupied →
                          ReferencePrelaunchFollower.acceptedStart logged = M.val.sigma)) ∨
                       (ActiveFollowerDownAcceptance.downSelected p i r.input.row r.input.time ∧
                        decoded.2 = some (CoordinatorLocalArmChoice.storedDownFlatWord payload i) ∧
                        cut.raw = decoded.2 ∧ cut.filteredRaw = decoded.2 ∧
                        cut.rawComparison = some true ∧ cut.ordinaryParse = some M ∧ cut.ordinaryAcceptance ∧
                        ∃ accepted : OrdinaryMessageCodec.acceptDown
                          (ReferencePrelaunchFollower.codecParams p rate.eta)
                          (ReferencePrelaunchFollower.acceptedStart logged) (r.input.time.val + 1) M,
                          let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M r.input.time
                            (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M r.input.time logged accepted)
                            r.input.row
                          ∃ recovered : ActiveFollowerDownAcceptance.ReplayRegisters,
                            ActiveFollowerDownAcceptance.checkedRecovery p rate M logged
                              (r.input.time.val + 1) = .ok recovered ∧
                            scan.endpoint = r.input.time.val + 1 ∧
                            ActiveFollowerDownAcceptance.recoveryRounds p rate M (r.input.time.val + 1) =
                              SparseCalendarReplay.sparseCalendarRounds M.val.sigma (r.input.time.val + 1) ∧
                            ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                              (r.input.time.val + 1) =
                              ((ActiveFollowerDownAcceptance.recoveryArrivals p rate M logged
                                (r.input.time.val + 1)).map fun arrival => (true, arrival)) ∧
                            (∀ q ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                              (r.input.time.val + 1), q.1 = true) ∧
                            recovered.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                              (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                (r.input.time.val + 1)) ∧
                            (∀ k, ∃ middle,
                              ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
                                ⟨(0, M.val.q), 0⟩
                                ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                  (r.input.time.val + 1)).take k) = .ok middle ∧
                              ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
                              middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                                ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
                                  (r.input.time.val + 1)).take k)) ∧
                            (∀ hstarted : M.val.sigma ≤ r.input.time.val,
                              recovered.lastService = ActiveFollowerDownAcceptance.recoveredLastService
                                p rate M logged (r.input.time.val + 1)
                                  (Nat.lt_succ_of_le hstarted)) ∧
                            cut.outcome = .accepted logged post decoded.2 M scan
                              recovered.registers recovered.lastService ∧
                            post = { advanced with
                              lastDown := some M
                              S := recovered.registers.1
                              delta := recovered.lastService
                              backlog := recovered.registers.2
                              status := .unoccupied
                              buffer := [] })) ∧
                      (ReferenceActivePhysicalStep.recordFollower view i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        prepared.arm own c).result = .ok post ∧
                      (ReferenceActivePhysicalStep.recordFollower view i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        prepared.arm own c).downInput = some logged ∧
                      (ReferenceActivePhysicalStep.recordFollower view i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        prepared.arm own c).down = some cut ∧
                      ActiveFollowerLifecycle.releaseAfterService rate.eta i r.input.time
                        (ActiveFollowerLifecycle.publicRowOfCompleteRow r.input.row r.input.time)
                        own c post = .ok post ∧
                      ActiveFollowerLifecycle.finishRound rate.eta r.input.time r.input.row post memory =
                        .ok (post, memory) ∧
                      DeclaredFollowerLocalRound.releaseAndFinish rate i r.input.row r.input.time
                        own c memory post = .ok (post, memory) ∧
                      r.output.followers i = ⟨.ordinary post memory, none, some logged, some cut⟩
          | _ => True
      | _ => True := by
  classical
  have hboundary := complete_first_replacement_cutoff_follower_boundary
    rate source rewards C_star C_h
  dsimp only at hboundary ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  cases hbirthGet : R[v]? with
  | none => trivial
  | some birth =>
      simp only [hbirthGet] at hboundary ⊢
      cases hbirthCoord : birth.output.preparation.coordinator with
      | first _ => trivial
      | live _ _ _ _ => trivial
      | dagger => trivial
      | invalidCollectionCutoff => trivial
      | collection _ _ _ _ outcome =>
          rw [hbirthCoord] at hboundary
          cases outcome <;> try trivial
          rename_i core consistent started hstart instruction hinstruction output hconsistent
            clockData installed birthArm
          dsimp only at hboundary ⊢
          let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
          let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
          cases hcurrentGet : R[v + 1 + tail.length]? with
          | none => trivial
          | some r =>
              simp only [tail, hcurrentGet] at hboundary ⊢
              have hnotContinuing := hboundary.1
              refine ⟨hnotContinuing, ?_⟩
              cases hcurrentCoord : r.output.preparation.coordinator with
              | first _ => trivial
              | collection _ _ _ _ _ => trivial
              | dagger => trivial
              | invalidCollectionCutoff => trivial
              | live registers owned base outcome =>
                  rw [hcurrentCoord] at hboundary
                  cases outcome <;> try trivial
                  rename_i dispatched hs ledger hi he hd hc hp hn chosen
                  dsimp only at hboundary ⊢
                  rcases hboundary.2 with ⟨hpayload, htimeBirth, htimeSource, hrows,
                    hselectedRow, hrewards, hsigmaPayload, hsourceStart, hfirst, hgrid,
                    hcause, hselectedBlock⟩
                  rcases hselectedBlock with ⟨selected, hselection, hselectedPayload,
                    hpending, hcutoff, hfollower⟩
                  have hselectionActual : r.output.preparation.coordinator.selection =
                      some selected := by
                    rw [hcurrentCoord]
                    exact hselection
                  refine ⟨hpayload, htimeBirth, htimeSource, hrows, hselectedRow,
                    hrewards, hsigmaPayload, hsourceStart, hfirst, hgrid, hcause,
                    ⟨selected, hselection, hselectedPayload, hpending, hcutoff, ?_⟩⟩
                  intro i
                  rcases hfollower i with ⟨old, memory, hinput, hdomainOld, hmassOld,
                    hzero, hstrict, hbusy, hdecision, hstart, hprepared, hdomainChoice,
                    hmassChoice, hpair, hdates, hup, hstarted, hcredit⟩
                  let c : ReferencePrelaunchFollower.State p rate.eta :=
                    { old with status := .unoccupied }
                  have hstrictSelected : old.status = .unoccupied →
                      ReferencePrelaunchFollower.acceptedStart old <
                        (selected.view.payload.downRecord i).val.sigma := by
                    have h := hstrict
                    rw [← hselectedPayload] at h
                    exact h
                  have hstartedSelected : (selected.view.payload.downRecord i).val.sigma ≤
                      r.input.time.val := by
                    have h := hstarted
                    rw [← hselectedPayload] at h
                    exact h
                  have hcreditSelected : (selected.view.payload.downRecord i).val.q ≤
                      ((selected.view.payload.downRecord i).val.sigma - 1) * D p := by
                    have h := hcredit
                    rw [← hselectedPayload] at h
                    exact h
                  have hfirstSelected : FollowerCutoffScan.firstCutoff p rate.eta.val
                      selected.view.payload.sigma
                      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) =
                      r.input.time.val + 1 := by
                    have h := hfirst
                    rw [← hselectedPayload] at h
                    exact h
                  have hgridSelected : r.input.time.val + 1 ≤
                      FollowerCutoffScan.gridBoundary p rate.eta.val selected.view.payload.sigma := by
                    have h := hgrid
                    rw [← hselectedPayload] at h
                    exact h
                  have hbusySelected : old.status ≠ .unoccupied →
                      old.lastDown = some (selected.view.payload.downRecord i) ∧
                      ∃ token : ActiveFollowerLifecycle.ProposalRead p,
                        memory.lastProposalRead = some token ∧
                        token.timestamp.val + 1 = r.input.time.val ∧
                        token.bit = FollowerCutoffScan.completeRowProposalBit
                          p rate.eta.val r.input.row token.timestamp := by
                    have h := hbusy
                    rw [← hselectedPayload] at h
                    exact h
                  have hlocalActual := cutoff_record_success r selected hselectionActual hpending i old
                    memory c hinput rfl hprepared rfl hdomainChoice hmassChoice hpair hdates
                    hstrictSelected hbusySelected hfirstSelected hgridSelected hcreditSelected
                    hstartedSelected
                  have hlocal := by
                    simpa only [hcurrentCoord, hselectedPayload, payload] using hlocalActual
                  rcases hlocal with ⟨logged, post, hlogging, hbuffer, hoperation,
                    hlast, hS, hdelta, hbacklog, hflagChoice, hloggedUnoccupied,
                    hloggedPair, hloggedDates, hnoAppend, hconsume, hpostUnoccupied,
                    hpostDomain, hpostMass, hpostDelta, hpostFlag, hbranches⟩
                  refine ⟨old, memory, hinput, hdomainOld, hmassOld, hzero, hstrict,
                    hbusy, hdecision, hstart, hprepared, hdomainChoice, hmassChoice,
                    hpair, hdates, hup, hstarted, hcredit, logged, post, hlogging,
                    hbuffer, hoperation, hlast, hS, hdelta, hbacklog, hflagChoice,
                    hloggedUnoccupied, hloggedPair, hloggedDates, hnoAppend,
                    hconsume, hpostUnoccupied, hpostDomain, hpostMass, hpostDelta,
                    hpostFlag, hbranches, ?_⟩
                  have hrecord :
                      (ReferenceActivePhysicalStep.recordFollower
                        (DispatchCut.live registers owned base
                          (.cutoffChosen dispatched hs ledger hi he hd hc hp hn chosen)).downView
                        i r.input.row
                        (r.input.state.activations i) r.input.time (r.input.active i)
                        (r.output.preparation.followers.followers i).arm
                        (r.output.preparation.feedback.observations (followerPlayer p.two_le_m i)) c).result =
                        .ok post := by
                    have hconsumeActual := by
                      simpa only [← hcurrentCoord] using hconsume
                    have hrecordActual :
                        (ReferenceActivePhysicalStep.recordFollower
                          r.output.preparation.coordinator.downView i r.input.row
                          (r.input.state.activations i) r.input.time (r.input.active i)
                          (r.output.preparation.followers.followers i).arm
                          (r.output.preparation.feedback.observations
                            (followerPlayer p.two_le_m i)) c).result = .ok post := by
                      simp [ReferenceActivePhysicalStep.recordFollower, c, hlogging, hconsumeActual]
                    simpa only [hcurrentCoord] using hrecordActual
                  have hdiagnosticActual := ReferenceActivePhysicalStep.recordFollower_logged
                    r.output.preparation.coordinator.downView i r.input.row
                    (r.input.state.activations i) r.input.time (r.input.active i)
                    (r.output.preparation.followers.followers i).arm
                    (r.output.preparation.feedback.observations (followerPlayer p.two_le_m i))
                    c logged (by simp [c]) hlogging
                  have hdiagnostic := by
                    simpa only [hcurrentCoord] using hdiagnosticActual
                  have hchoiceFlag : c.initializationFailure = old.initializationFailure := by
                    simp [c]
                  have hpostFlagChoice : post.initializationFailure = c.initializationFailure :=
                    hpostFlag.trans hchoiceFlag.symm
                  have hfinishMass : post.S + post.backlog ≤ (r.input.time.val + 1) * D p := by
                    calc
                      post.S + post.backlog ≤ r.input.time.val * D p := hpostMass
                      _ ≤ (r.input.time.val + 1) * D p :=
                        Nat.mul_le_mul_right (D p) (by omega)
                  have hconsumeActual := by
                    simpa only [← hcurrentCoord] using hconsume
                  have hfinish := cutoff_finish_actual r i c logged post memory hprepared
                    rfl hlogging hconsumeActual hpostDomain hpostUnoccupied hfinishMass hpostFlagChoice
                  rcases hfinish with ⟨_, hrelease, hfinishRound, hreleaseFinish,
                    hfollowers, _, _, _, _⟩
                  have hfollowers' := by
                    simpa only [hcurrentCoord] using hfollowers
                  exact ⟨hrecord, hdiagnostic.1, hdiagnostic.2, hrelease,
                    hfinishRound, hreleaseFinish, hfollowers'⟩
