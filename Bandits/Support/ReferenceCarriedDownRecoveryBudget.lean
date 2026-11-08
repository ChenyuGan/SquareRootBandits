/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCutoffDownRecovery

import Lean.Elab.Tactic.Omega

/-!
# Carried local DOWN recovery budget

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-64` and
`sources/zip4/manuscript/06_interruptions.tex:246-282,303-348`.

This module checks the actual carried local buffer and proves bounded checked
recovery for one accepted DOWN record.  It does not prove buffer propagation
or all-assignment survival.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCarriedDownRecoveryBudget

open ConstructorDimensions ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open ReferencePrelaunchFollower ActiveFollowerLifecycle ActiveFollowerDownAcceptance
open ReferenceDownReception SparseCalendarReplay PublicDiscreteDraws QueueReplay
open CompletePublicTable

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)

private abbrev DownRecord :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

private theorem sparseBufferContribution_zero_of_no_key
    (d : ℕ) (D eta : ℝ) (h : ℕ) (arm : Fin p.K) (r : ℕ)
    (buffer : List (SparseCalendarRecord p.K))
    (hno : ∀ saved ∈ buffer, ¬ (saved.calendarRound = r ∧ saved.pilot = arm)) :
    sparseBufferContribution d D eta h arm r buffer = 0 := by
  classical
  induction buffer with
  | nil => rfl
  | cons saved rest ih =>
      have hhead : ¬ (saved.calendarRound = r ∧ saved.pilot = arm) :=
        hno saved List.mem_cons_self
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

/-- The actual local buffer contributes at most one source-bounded arrival
for each calendar-round/arm key.  The cap follows from its saved observation,
quantization, and the original saved-contribution floor. -/
theorem bufferArrivalAt_le_D
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
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
      have hscore' : current.registers.1 ≤ T * D :=
        hscore.trans (Nat.mul_le_mul_right D htime)
      have hbacklog' : current.registers.2 ≤ T * D :=
        hbacklog.trans (Nat.mul_le_mul_right D htime)
      have hdomain : ActiveFollowerDownAcceptance.replay_register_domain D (T * D) current :=
        ⟨hscore', hlast, hbacklog'⟩
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
      have hnextBound : (elapsed + 1) * D ≤ T * D := Nat.mul_le_mul_right D htime
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
          _ = (elapsed + (rest.length + 1)) * D := by congr 1; omega

private theorem replay_mass_after_enabled_records (capacity D : ℕ)
    (initial : ℕ × ℕ) (records : List (Bool × ℕ))
    (hrecords : ∀ record ∈ records, record.1 = true ∧ record.2 ≤ D) :
    (QueueReplay.replay capacity initial records).1 +
        (QueueReplay.replay capacity initial records).2 ≤
      initial.1 + initial.2 + records.length * D := by
  induction records generalizing initial with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      obtain ⟨henabled, harrival⟩ := hrecords record List.mem_cons_self
      have htail : ∀ item ∈ rest, item.1 = true ∧ item.2 ≤ D := by
        intro item hi
        exact hrecords item (List.mem_cons_of_mem _ hi)
      have hstep :
          (QueueReplay.transition capacity initial record).1 +
              (QueueReplay.transition capacity initial record).2 =
            initial.1 + initial.2 + record.2 := by
        simp [QueueReplay.transition, henabled]
        omega
      simp only [QueueReplay.replay, List.foldl_cons]
      have hnext := ih (QueueReplay.transition capacity initial record) htail
      calc
        _ ≤ (QueueReplay.transition capacity initial record).1 +
              (QueueReplay.transition capacity initial record).2 + rest.length * D := hnext
        _ = initial.1 + initial.2 + record.2 + rest.length * D := by rw [hstep]
        _ ≤ initial.1 + initial.2 + (rest.length + 1) * D := by
          have hmul : (rest.length + 1) * D = rest.length * D + D := by
            rw [Nat.add_mul, one_mul]
          rw [hmul]
          omega

private theorem down_sigma_pos
    (M : DownRecord (p := p) (rate := rate)) : 1 ≤ M.val.sigma :=
  PrelaunchBufferRecovery.down_sigma_pos rate.eta M

private theorem checkedRecovery_local_budget
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p)
    (ell : ℕ) (hstarted : M.val.sigma ≤ ell) (hspan : ell ≤ p.T + 1) :
    ∃ final, ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final ∧
      final.registers.1 + final.registers.2 ≤ M.val.q + (ell - M.val.sigma) * D p ∧
      final.registers.1 + final.registers.2 ≤ (ell - 1) * D p ∧
      final.lastService ≤ D p := by
  have hrounds : (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).length =
      ell - M.val.sigma := ActiveFollowerDownAcceptance.recoveryRounds_length p rate M ell
  have hsigma := down_sigma_pos rate M
  let elapsed := M.val.sigma - 1
  let current : ActiveFollowerDownAcceptance.ReplayRegisters := ⟨(0, M.val.q), 0⟩
  obtain ⟨final, hchecked, hmass, hlast⟩ := checkedCalendarReplay_success_of_mass
    (D p) p.T (4 * rate.n) 0 elapsed current
    (ActiveFollowerDownAcceptance.bufferArrivalAt p rate M logged)
    (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell)
    (by simp [current]) hcredit (by simp [current]) (by simpa [current] using hcredit)
    (ActiveFollowerDownAcceptance.four_n_le_D p rate)
    (fun r _ => bufferArrivalAt_le_D rate M logged hvalid r)
    (by rw [hrounds]; dsimp [elapsed]; omega)
  have hchecked' : ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final := by
    rw [ActiveFollowerDownAcceptance.checkedRecovery]
    simpa [current] using hchecked
  have hlen : elapsed + (ActiveFollowerDownAcceptance.recoveryRounds p rate M ell).length =
      ell - 1 := by
    rw [hrounds]
    dsimp [elapsed]
    omega
  have hmass' : final.registers.1 + final.registers.2 ≤ (ell - 1) * D p := by
    rw [← hlen]
    exact hmass
  have hsuccess := ActiveFollowerDownAcceptance.checkedRecovery_success
    p rate M logged ell final hchecked'
  have harrivals : ∀ record ∈ ActiveFollowerDownAcceptance.recoveryQueueRecords
      p rate M logged ell, record.1 = true ∧ record.2 ≤ D p := by
    intro record hrecord
    obtain ⟨arrival, ha, rfl⟩ := List.mem_map.mp hrecord
    obtain ⟨r, hr, harrival⟩ := List.mem_map.mp ha
    rw [← harrival]
    exact ⟨rfl, bufferArrivalAt_le_D rate M logged hvalid r⟩
  have hconserve := replay_mass_after_enabled_records (4 * rate.n) (D p)
    (0, M.val.q) (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell)
    harrivals
  have hfinalEq := hsuccess.2.1
  have hrecordsLength : (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell).length =
      ell - M.val.sigma := by
    simp [ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals, hrounds]
  refine ⟨final, hchecked', ?_, hmass', hlast⟩
  have hfinalMass : final.registers.1 + final.registers.2 ≤
      M.val.q + (ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell).length * D p := by
    rw [hfinalEq, ActiveFollowerDownAcceptance.recoveredRegisters]
    simpa using hconserve
  rw [hrecordsLength] at hfinalMass
  exact hfinalMass

/-- A successful replay of the actual carried buffer preserves the parsed
initial queue and checks every intermediate register before the next date. -/
theorem checkedRecovery_with_prefix_budget
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p)
    (ell : ℕ) (hstarted : M.val.sigma ≤ ell) (hspan : ell ≤ p.T + 1) :
    ∃ final,
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged ell = .ok final ∧
      final.registers = ActiveFollowerDownAcceptance.recoveredRegisters p rate M logged ell ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) final ∧
      final.registers.1 + final.registers.2 ≤ M.val.q + (ell - M.val.sigma) * D p ∧
      final.registers.1 + final.registers.2 ≤ (ell - 1) * D p ∧
      final.lastService ≤ D p ∧
      (∀ hinterval : M.val.sigma < ell,
        final.lastService = ActiveFollowerDownAcceptance.recoveredLastService
          p rate M logged ell hinterval) ∧
      (ell = M.val.sigma → final.registers = (0, M.val.q) ∧ final.lastService = 0) ∧
      ∀ j : ℕ, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell).take j) =
            .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell).take j) ∧
        middle.registers.1 + middle.registers.2 ≤
          M.val.q + min j (ell - M.val.sigma) * D p := by
  obtain ⟨final, hchecked, hmassCarried, hmassTotal, hlast⟩ :=
    checkedRecovery_local_budget rate M logged hvalid hcredit ell hstarted hspan
  have hsuccess := ActiveFollowerDownAcceptance.checkedRecovery_success
    p rate M logged ell final hchecked
  have hservice : ∀ hinterval : M.val.sigma < ell,
      final.lastService = ActiveFollowerDownAcceptance.recoveredLastService
        p rate M logged ell hinterval := by
    intro hinterval
    exact ActiveFollowerDownAcceptance.checkedRecovery_success_last_service
      p rate M logged ell hinterval final hchecked
  have hempty : ell = M.val.sigma → final.registers = (0, M.val.q) ∧ final.lastService = 0 := by
    intro hell
    have hrecords : ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp [ActiveFollowerDownAcceptance.recoveryQueueRecords,
        ActiveFollowerDownAcceptance.recoveryArrivals,
        ActiveFollowerDownAcceptance.recoveryRounds_length, hell]
    have hraw := hchecked
    rw [ActiveFollowerDownAcceptance.checkedRecovery_eq_checkedReplay, hrecords] at hraw
    have hdomain := ActiveFollowerDownAcceptance.checkedReplay_success_input
      (D p) (p.T * D p) (4 * rate.n) 0 ⟨(0, M.val.q), 0⟩ final [] hraw
    simp only [ActiveFollowerDownAcceptance.checkedReplay, ite_eq_left hdomain] at hraw
    cases hraw
    exact ⟨rfl, rfl⟩
  refine ⟨final, hchecked, hsuccess.2.1, hsuccess.1, hmassCarried, hmassTotal,
    hlast, hservice, hempty, ?_⟩
  intro j
  obtain ⟨middle, hprefix, hprefixDomain, hprefixReplay⟩ :=
    ActiveFollowerDownAcceptance.checkedRecovery_success_prefix
      p rate M logged ell final hchecked j
  let records := ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged ell
  have harrivals : ∀ record ∈ records, record.1 = true ∧ record.2 ≤ D p := by
    intro record hrecord
    obtain ⟨arrival, ha, rfl⟩ := List.mem_map.mp hrecord
    obtain ⟨r, hr, harrival⟩ := List.mem_map.mp ha
    rw [← harrival]
    exact ⟨rfl, bufferArrivalAt_le_D rate M logged hvalid r⟩
  have htakeRecords : ∀ record ∈ records.take j, record.1 = true ∧ record.2 ≤ D p := by
    intro record hrecord
    exact harrivals record ((List.take_sublist j records).subset hrecord)
  have hmassPrefix := replay_mass_after_enabled_records (4 * rate.n) (D p)
    (0, M.val.q) (records.take j) htakeRecords
  have hlength : (records.take j).length = min j (ell - M.val.sigma) := by
    simp [records, ActiveFollowerDownAcceptance.recoveryQueueRecords,
      ActiveFollowerDownAcceptance.recoveryArrivals,
      ActiveFollowerDownAcceptance.recoveryRounds_length]
  refine ⟨middle, hprefix, hprefixDomain, hprefixReplay, ?_⟩
  have hprefixBudget : middle.registers.1 + middle.registers.2 ≤
      M.val.q + (records.take j).length * D p := by
    rw [hprefixReplay]
    simpa using hmassPrefix
  rw [hlength] at hprefixBudget
  exact hprefixBudget

/-- The accepted scan specializes the same local-buffer result at its actual
clipped endpoint.  Acceptance is only the codec test; no reception or
recovery-success condition is added. -/
theorem acceptedDown_checkedRecovery_with_prefix_budget
    (M : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : ActiveFollowerLifecycle.localBufferValid logged)
    (hcredit : M.val.q ≤ (M.val.sigma - 1) * D p)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (ha : OrdinaryMessageCodec.acceptDown (ReferencePrelaunchFollower.codecParams p rate.eta)
      (ReferencePrelaunchFollower.acceptedStart logged) (t.val + 1) M) :
    ∃ final,
      ActiveFollowerDownAcceptance.checkedRecovery p rate M logged
        (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint =
            .ok final ∧
      final.registers = ActiveFollowerDownAcceptance.recoveredRegisters p rate M logged
        (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint ∧
      ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) final ∧
      final.registers.1 + final.registers.2 ≤ M.val.q +
        ((ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint -
            M.val.sigma) * D p ∧
      final.registers.1 + final.registers.2 ≤
        ((ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint - 1) * D p ∧
      final.lastService ≤ D p ∧
      final.lastService = ActiveFollowerDownAcceptance.recoveredLastService p rate M logged
        (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
          (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint
        (ActiveFollowerDownAcceptance.acceptedCutoff_interval_bounds
          p rate M t row logged ha).1 ∧
      ∀ j : ℕ, ∃ middle,
        ActiveFollowerDownAcceptance.checkedReplay (D p) (p.T * D p) (4 * rate.n) 0
          ⟨(0, M.val.q), 0⟩
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
            (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint).take j) =
            .ok middle ∧
        ActiveFollowerDownAcceptance.replay_register_domain (D p) (p.T * D p) middle ∧
        middle.registers = QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((ActiveFollowerDownAcceptance.recoveryQueueRecords p rate M logged
            (ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
              (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint).take j) ∧
        middle.registers.1 + middle.registers.2 ≤ M.val.q +
          (min j ((ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
            (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row).endpoint -
              M.val.sigma)) * D p := by
  let scan := ActiveFollowerDownAcceptance.acceptedCutoffScan p rate M t
    (ActiveFollowerDownAcceptance.acceptedDownStartLE p rate M t logged ha) row
  have hscan := ActiveFollowerDownAcceptance.acceptedCutoff_interval_bounds
    p rate M t row logged ha
  have hmain := checkedRecovery_with_prefix_budget rate M logged hvalid hcredit
    scan.endpoint hscan.1.le hscan.2.2.1
  rcases hmain with ⟨final, hchecked, hregisters, hdomain, hcarried, htotal,
    hlast, hservice, _, hpref⟩
  refine ⟨final, ?_, ?_, hdomain, ?_, ?_, hlast, ?_, ?_⟩
  · simpa [scan] using hchecked
  · simpa [scan] using hregisters
  · simpa [scan] using hcarried
  · simpa [scan] using htotal
  · simpa [scan] using hservice hscan.1
  · intro j
    obtain ⟨middle, hprefix, hprefixDomain, hprefixReplay, hprefixMass⟩ := hpref j
    refine ⟨middle, ?_, hprefixDomain, ?_, ?_⟩
    · simpa [scan] using hprefix
    · simpa [scan] using hprefixReplay
    · simpa [scan] using hprefixMass

end Bandits.Support.ReferenceCarriedDownRecoveryBudget
