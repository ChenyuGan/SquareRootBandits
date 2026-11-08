/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFollowerSafety
public import Bandits.Support.ReferenceFirstCutoffRecordedService

import Lean.Elab.Tactic.Omega

/-!
# First-cutoff follower observation and finish

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-14,192-209,258-297`,
`05_binary_transport.tex:354-396`, and `appendix_a_local_protocol.tex:46-60`.

This internal producer branches on the actual PREPARE constructor. An ordinary
constructor permits logging, reference DOWN reception, and unoccupied finish;
a dagger constructor stays dagger. It does not establish ordinary preparation,
unconditional survival, a generated-launch adapter, source queue identities,
collection continuation, or any manuscript theorem or regret closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstCutoffFollowerObservation

open ConstructorDimensions
open ActiveFollowerLifecycle
open ActiveFollowerDownAcceptance
open ReferenceDownReception
open SparseCalendarReplay
open ReferenceActivePhysicalStep

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

private abbrev DownRecord :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

/- The following arithmetic is reproved locally: the public live-window
recovery theorem excludes the cutoff, and the zero-recovery theorem requires
an already retained acceptance. Neither can establish this call's guards. -/

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

private theorem checkedRecovery_cutoff_budget
    (M : DownRecord (p := p) (rate := rate))
    (logged : ReferencePrelaunchFollower.State p rate.eta)
    (hq : M.val.q = 0) (hvalid : localBufferValid logged)
    (ell : ℕ) (hlen : ell - M.val.sigma ≤ p.T) :
    ∃ final, checkedRecovery p rate M logged ell = .ok final ∧
      final.registers.1 + final.registers.2 ≤ (ell - M.val.sigma) * D p ∧
      final.lastService ≤ D p := by
  have hrounds : (recoveryRounds p rate M ell).length ≤ p.T := by
    rw [recoveryRounds_length]
    exact hlen
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
  · simpa only [recoveryRounds_length, Nat.zero_add] using hmass

private theorem down_buffer_domain (s : ReferencePrelaunchFollower.State p rate.eta)
    (h : localBufferValid s) : bufferInputDomain p s.buffer := by
  refine ⟨?_, h.2.1⟩
  intro saved hsaved
  obtain ⟨q, hq, heq⟩ := h.2.2 saved hsaved
  exact ⟨(h.1 saved hsaved).1, (h.1 saved hsaved).2, ⟨q, by omega⟩, heq⟩

/-- The actual minimum yields its actual grid or prior-bit cause. -/
private theorem cutoff_cause (sigma t : Fin p.T)
    (row : CompletePublicTable.CompleteRow p)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = t.val + 1) :
    t.val + 1 ≤ FollowerCutoffScan.gridBoundary p rate.eta.val sigma ∧
      (FollowerCutoffScan.gridBoundary p rate.eta.val sigma = t.val + 1 ∨
        ∃ stamp, stamp.val + 1 = t.val ∧
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val row stamp = true) := by
  have hle := Finset.min'_le
    (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
    (FollowerCutoffScan.gridBoundary p rate.eta.val sigma) (Finset.mem_insert_self _ _)
  change FollowerCutoffScan.firstCutoff p rate.eta.val sigma _ ≤ _ at hle
  rw [hcut] at hle
  refine ⟨hle, ?_⟩
  have hm := Finset.min'_mem
    (FollowerCutoffScan.firstCutoffCarrier p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row))
    (FollowerCutoffScan.firstCutoffCarrier_nonempty _ _ _ _)
  change FollowerCutoffScan.firstCutoff p rate.eta.val sigma _ ∈ _ at hm
  rw [hcut] at hm
  rcases Finset.mem_insert.mp hm with hg | hevent
  · exact Or.inl hg.symm
  · obtain ⟨stamp, hs, he⟩ := Finset.mem_image.mp hevent
    have hbit := (Finset.mem_filter.mp hs).2
    have he' : stamp.val + 2 = t.val + 1 := he
    exact Or.inr ⟨stamp, by omega, hbit⟩

/-- Only successful StartRound is inverted here; no offer or arm existence
is proved or assumed. The original complete memory is framed. -/
private theorem ordinary_cutoff_choice
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : ReferencePrelaunchFollower.Activation p) (t sigma : Fin p.T)
    (active : alpha.val ≤ t.val + 1)
    (s c : ReferencePrelaunchFollower.State p rate.eta) (mem mu : LocalMemory p)
    (hchoice : (DeclaredFollowerLocalRound.prepare rate i row alpha t active
      (.ordinary s mem)).configuration = .ordinary c mu)
    (hv : localStateDomainValid s)
    (hoccupied : s.status ≠ .unoccupied → ∃ M token,
      s.lastDown = some M ∧ M.val.sigma = sigma.val + 1 ∧
      mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = t.val ∧
      token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val row token.timestamp)
    (hafter : sigma.val + 1 < t.val + 1)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val row) = t.val + 1) :
    c.status = .unoccupied ∧ localStateDomainValid c ∧
      c.S = s.S ∧ c.backlog = s.backlog ∧ c.buffer = s.buffer ∧ mu = mem := by
  obtain ⟨before, memory, hin, hs, _, hu⟩ :=
    ReferenceFollowerReplyChronology.prepare_ordinary_inversion i row alpha t active
      (.ordinary s mem) c mu hchoice
  obtain ⟨rfl, rfl⟩ := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hin
  have hf := startRound_frame rate.eta t s c mem mu hs
  have hcvalid : localStateDomainValid c := by
    rcases hv with ⟨hreg, hbuf, hbatch⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [serviceRegistersValid, hf.2.1, hf.2.2.1, hf.2.2.2.1] using hreg
    · simpa only [localBufferValid, hf.2.2.2.2.2.1] using hbuf
    · simpa only [downDecoderStateValid, hf.2.2.2.2.1] using hbatch
  refine ⟨?_, hcvalid, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.2.1, hf.2.2.2.2.2.2.2⟩
  by_cases hun : s.status = .unoccupied
  · exact hu hun
  · obtain ⟨M, token, hM, hsigma, htoken, hstamp, hbit⟩ := hoccupied hun
    have hcoord : acceptedStartCoordinate M = sigma := by
      apply Fin.ext
      change M.val.sigma - 1 = sigma.val
      omega
    obtain ⟨hgrid, hcause⟩ := cutoff_cause sigma t row hcut
    have hinterrupt : (FollowerCutoffScan.gridBoundary p rate.eta.val
        (acceptedStartCoordinate M) = t.val + 1 || token.bit) = true := by
      rw [hcoord]
      rcases hcause with hg | ⟨stamp, hst, hb⟩
      · simp only [hg, decide_true, Bool.true_or]
      · have he : stamp = token.timestamp := Fin.ext (by omega)
        rw [he] at hb
        rw [hbit, hb]
        exact Bool.or_true _
    have hs' := startRound_occupied_branch rate.eta t s mem hun hv M hM
      (by omega) (by simpa only [hcoord] using hgrid) token htoken hstamp
    rw [hinterrupt] at hs'
    have he := Except.ok.inj (hs.symm.trans hs')
    have hec := congrArg (fun pair => pair.1.status) he
    exact hec

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

/-- A selected ordinary sender view with the actual cutoff pending set keeps
sending the stored assignment, without an assignment-live test. -/
private theorem cutoff_expected_word {x : RoundInput p rate} (selected : Selection x)
    (hpending : selected.view.pendingAtChoice = Finset.univ) (i : Fin (p.m - 1)) :
    expectedDownFlatWord (some selected.view) i x.row x.time =
      if downSelected p i x.row x.time then
        some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) else none := by
  classical
  have hb : selectedDownSenderBranch selected.view i x.row x.time ↔
      downSelected p i x.row x.time := by
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro h
      exact ⟨h.1, h.2, hpending ▸ Finset.mem_univ i⟩
  by_cases hsel : downSelected p i x.row x.time
  · rw [ite_eq_left hsel]
    exact selected.expected_down_word i (hb.mpr hsel)
  · have hn : ¬ (CoordinatorLocalArmChoice.coordinatorArmChoice selected.view.payload
        selected.view.pendingAtChoice selected.view.cutoff x.time
        selected.view.complementWeights x.row ≠ none ∧
        selectedDownSenderBranch selected.view i x.row x.time) := fun h => hsel (hb.mp h.2)
    simp only [expectedDownFlatWord, ite_eq_right hn, ite_eq_right hsel]
    rfl

/-- Logging appends exactly the source/mask record, preserving strict order.
The new stamp is the cutoff round itself, outside the recovery interval. -/
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

/-- Explicit local inputs are domains, mass, and chronology of the actual
choice, plus the actual cutoff sender geometry and first-birth queue. No
accepted outcome or successful recovery is an input. -/
private theorem cutoff_record_success
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected)
    (hpending : selected.view.pendingAtChoice = Finset.univ)
    (start k : ℕ) (htime : record.input.time.val = start + k)
    (hsigma : selected.view.payload.sigma.val = start)
    (hq : ∀ i, (selected.view.payload.downRecord i).val.q = 0)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val selected.view.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) =
        record.input.time.val + 1)
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (hu : choice.status = .unoccupied) (hvalid : localStateDomainValid choice)
    (hmass : choice.S + choice.backlog ≤ k * D p)
    (hpair : choice.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (hbefore : ∀ saved ∈ choice.buffer, saved.calendarRound < record.input.time.val + 1) :
    let prepared := record.output.preparation.followers.followers i
    let own := record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)
    let view := record.output.preparation.coordinator.downView
    ∃ logged post,
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time (prepared.arm, own) choice = .ok logged ∧
      logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
        (record.input.state.activations i) record.input.time (prepared.arm, own) ∧
      (recordFollower view i record.input.row (record.input.state.activations i)
        record.input.time (record.input.active i) prepared.arm own choice).result = .ok post ∧
      post.status = .unoccupied ∧ localStateDomainValid post ∧
      post.S + post.backlog ≤ k * D p ∧
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
      (∀ saved ∈ post.buffer, saved.calendarRound < record.input.time.val + 2) := by
  classical
  intro prepared own view
  obtain ⟨logged, hlog, hbuf, hstatus, _, hloggedBuffer⟩ :=
    ActiveFollowerLogging.checkedLogging_success_of_chronological i record.input.row
      (record.input.state.activations i) record.input.time (prepared.arm, own)
      choice hvalid.2.1 hbefore hu
  have hf := ActiveFollowerLogging.checkedLogging_success_frame i record.input.row
    (record.input.state.activations i) record.input.time (prepared.arm, own) choice logged hlog
  have hlu : logged.status = .unoccupied := hstatus.trans hu
  have hlvalid : localStateDomainValid logged := by
    refine ⟨?_, hloggedBuffer, ?_⟩
    · simpa only [serviceRegistersValid, hf.2.1, hf.2.2.1, hf.2.2.2.1] using hvalid.1
    · simpa only [downDecoderStateValid, hf.2.2.2.2.2.1] using hvalid.2.2
  have hlmass : logged.S + logged.backlog ≤ k * D p := by
    simpa only [hf.2.1, hf.2.2.2.1] using hmass
  have hlchron := logging_chronology i record.input.row (record.input.state.activations i)
    record.input.time (prepared.arm, own) choice logged hbuf hpair hbefore
  have hregs : registerInputDomain p rate logged := hlvalid.1
  have hbatch : decoderInputDomain p logged.downBatch := hlvalid.2.2
  have hbuffer := down_buffer_domain logged hloggedBuffer
  have hstep := AffineBatchDecoder.step_spec p
    (currentInputExtension p (currentRoundInput p i record.input.row record.input.time own rate logged))
    logged.downBatch record.input.time hbatch.1 hbatch.2
  have hstepBatch : decoderInputDomain p
      (currentDecodeStep p i record.input.row record.input.time own rate logged).1 :=
    ⟨hstep.1, hstep.2.1⟩
  let advanced := { logged with downBatch :=
    (currentDecodeStep p i record.input.row record.input.time own rate logged).1 }
  have hadvanced : localStateDomainValid advanced := ⟨hlvalid.1, hloggedBuffer, hstepBatch⟩
  let d := referenceDownCut p view i record.input.row record.input.time own rate logged
  have hrecorded : (recordFollower view i record.input.row (record.input.state.activations i)
      record.input.time (record.input.active i) prepared.arm own choice).result =
      DeclaredFollowerLocalRound.consumeDownResult rate d.outcome := by
    simp only [recordFollower, dite_eq_left hu, hlog, d]
  have hview : view = some selected.view := by
    simp only [view, DispatchCut.downView, hs, Option.map_some]
  have hexpected := cutoff_expected_word selected hpending i
  rw [← hview] at hexpected
  have hsimple : ∀ post : ReferencePrelaunchFollower.State p rate.eta,
      post.status = .unoccupied → localStateDomainValid post →
      post.S + post.backlog ≤ k * D p →
      post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) →
      (∀ saved ∈ post.buffer, saved.calendarRound < record.input.time.val + 2) →
      DeclaredFollowerLocalRound.consumeDownResult rate d.outcome = .ok post →
      ∃ logged post,
        ActiveFollowerLogging.checkedLogging i record.input.row
          (record.input.state.activations i) record.input.time (prepared.arm, own) choice = .ok logged ∧
        logged.buffer = choice.buffer ++ ReferencePrelaunchFollower.logAt i record.input.row
          (record.input.state.activations i) record.input.time (prepared.arm, own) ∧
        (recordFollower view i record.input.row (record.input.state.activations i)
          record.input.time (record.input.active i) prepared.arm own choice).result = .ok post ∧
        post.status = .unoccupied ∧ localStateDomainValid post ∧
        post.S + post.backlog ≤ k * D p ∧
        post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        (∀ saved ∈ post.buffer, saved.calendarRound < record.input.time.val + 2) := by
    intro post hpu hpv hpm hpp hpt he
    exact ⟨logged, post, hlog, hbuf, hrecorded.trans he, hpu, hpv, hpm, hpp, hpt⟩
  by_cases hselected : downSelected p i record.input.row record.input.time
  · by_cases hmatches : (currentDecodeStep p i record.input.row record.input.time own rate logged).2 =
        expectedDownFlatWord view i record.input.row record.input.time
    · cases hp : ordinaryParse p rate
        (currentDecodeStep p i record.input.row record.input.time own rate logged).2 with
      | none =>
          apply hsimple advanced hlu hadvanced hlmass hlchron.1 hlchron.2
          simp only [d, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
            dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer,
            dite_eq_left hmatches, hp, DeclaredFollowerLocalRound.consumeDownResult, advanced]
      | some M =>
          by_cases ha : OrdinaryMessageCodec.acceptDown
              (ReferencePrelaunchFollower.codecParams p rate.eta)
              (ReferencePrelaunchFollower.acceptedStart logged) (record.input.time.val + 1) M
          · have hM : M = selected.view.payload.downRecord i := by
              have he : (currentDecodeStep p i record.input.row record.input.time own rate logged).2 =
                  some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i) := by
                rw [hmatches, hexpected, ite_eq_left hselected]
              have hf : ordinaryParse p rate
                  (some (CoordinatorLocalArmChoice.storedDownFlatWord selected.view.payload i)) =
                  some (selected.view.payload.downRecord i) :=
                parse_stored_word (p := p) (rate := rate) selected.view.payload i
              exact Option.some.inj (hp.symm.trans
                ((congrArg (ordinaryParse p rate) he).trans hf))
            have hMsigma : M.val.sigma = start + 1 := by
              rw [hM]
              change selected.view.payload.sigma.val + 1 = start + 1
              rw [hsigma]
            have hMq : M.val.q = 0 := by rw [hM]; exact hq i
            have hstart := acceptedDownStartLE p rate M record.input.time logged ha
            have hdownStart : downStart p rate M = selected.view.payload.sigma := by
              apply Fin.ext
              have hv := (downStart_val_add_one p rate M).trans hMsigma
              rw [hsigma]
              omega
            have hell : (acceptedCutoffScan p rate M record.input.time hstart record.input.row).endpoint =
                record.input.time.val + 1 := by
              unfold acceptedCutoffScan FollowerCutoffScan.completeRowCutoffScan
              rw [FollowerCutoffScan.followerCutoffScan_endpoint_eq_min_firstCutoff]
              rw [hdownStart, hcut, Nat.min_eq_left (by omega)]
            have hlength : record.input.time.val + 1 - M.val.sigma = k := by omega
            obtain ⟨final, hchecked, hfinalMass, hlast⟩ := checkedRecovery_cutoff_budget M logged
              hMq hloggedBuffer (record.input.time.val + 1) (by rw [hlength]; omega)
            let after := { advanced with
              lastDown := some M
              S := final.registers.1
              delta := final.lastService
              backlog := final.registers.2
              status := ActiveRoundActions.FollowerStatus.unoccupied
              buffer := [] }
            have hout := (checkedRecovery_success p rate M logged _ final hchecked).1
            have hafterBuffer : localBufferValid after := by simp [localBufferValid, after]
            have hafterValid : localStateDomainValid after := ⟨hout, hafterBuffer, hstepBatch⟩
            apply hsimple after rfl hafterValid
            · simpa only [after, hlength] using hfinalMass
            · exact List.Pairwise.nil
            · intro saved hsaved
              cases hsaved
            · have hne : record.input.time.val + 1 ≠ record.input.time.val + 2 := by omega
              simp only [d, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
                dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer,
                dite_eq_left hmatches, hp, dite_eq_left ha, hell, hchecked,
                ite_eq_right hne, DeclaredFollowerLocalRound.consumeDownResult, after, advanced]
          · apply hsimple advanced hlu hadvanced hlmass hlchron.1 hlchron.2
            simp only [d, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
              dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer,
              dite_eq_left hmatches, hp, dite_eq_right ha,
              DeclaredFollowerLocalRound.consumeDownResult, advanced]
    · apply hsimple advanced hlu hadvanced hlmass hlchron.1 hlchron.2
      simp only [d, referenceDownCut, dite_eq_left hselected, dite_eq_left hlu,
        dite_eq_left hregs, dite_eq_left hbatch, dite_eq_left hbuffer,
        dite_eq_right hmatches, DeclaredFollowerLocalRound.consumeDownResult, advanced]
  · apply hsimple logged hlu hlvalid hlmass hlchron.1 hlchron.2
    simp only [d, referenceDownCut, dite_eq_right hselected,
      DeclaredFollowerLocalRound.consumeDownResult]

private theorem first_preparation_queue_zero
    (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput birth.input)))
    (selected : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights birth.input.row)
    (hprep : birth.output.preparation.coordinator = .first (.chosen installed selected))
    (i : Fin (p.m - 1)) : (installed.registers.payload.downRecord i).val.q = 0 := by
  have hd : dispatch birth.input = .first (.chosen installed selected) :=
    birth.output.preparation.coordinator_eq.symm.trans hprep
  have hfirst : birth.input.state.coordinator = .first := by
    cases hc : birth.input.state.coordinator with
    | first => rfl
    | live r q base =>
        simp only [dispatch, hc, CoordinatorRoundDispatch.dispatch] at hd
        cases hd
    | collection payload ledger proposal =>
        simp only [dispatch, hc] at hd
        split at hd
        · cases hd
        · cases hd
    | dagger =>
        simp only [dispatch, hc] at hd
        cases hd
  have hchosen : CoordinatorRoundDispatch.dispatchFirst (firstInput birth.input) =
      .chosen installed selected := by
    rw [dispatch_first birth.input hfirst] at hd
    exact DispatchCut.first.inj hd
  exact ReferenceAssignmentPayloadPersistence.firstChosen_down_queue_zero
    birth.input installed selected hchosen i

/-- Actual first-cutoff observation and finish, on exactly the explicit
first-live boundary and a cutoff inside the physical run. The result branches
on the actual PREPARE constructor; it does not prove ordinary preparation or
unconditional survival. The whole rows, reward table, initial memories, and
private index are retained. In particular, cutoff equal to freeze does not
skip follower logging, DOWN delivery, or finish. -/
theorem run_first_cutoff_follower_observation
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory : Fin (p.m - 1) → LocalMemory p)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (memory i))
    (hS : ∀ i, (seed i).S = 0) (hdelta : ∀ i, (seed i).delta = 0)
    (hbacklog : ∀ i, (seed i).backlog = 0) (hnone : ∀ i, (seed i).lastDown = none)
    (hunoccupied : ∀ i, (seed i).status = .unoccupied)
    (hvalid : ∀ i, localBufferValid (seed i))
    (hpair : ∀ i, (seed i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (hbatch : ∀ i, downDecoderStateValid (seed i))
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length < count) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let k := W.length
    let cut := E.records[k]'(by
      simpa only [E, ReferenceActivePhysicalHorizon.run_record_count] using hshort)
    ∀ i : Fin (p.m - 1),
      let prepared := cut.output.preparation.followers.followers i
      let own := cut.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      let view := cut.output.preparation.coordinator.downView
      match prepared.configuration with
      | .dagger =>
          (cut.output.followers i).configuration = .dagger ∧
          (cut.output.followers i).downInput = none ∧
          (cut.output.followers i).down = none ∧ (cut.output.followers i).failure = none
      | .ordinary c mu =>
          ∃ logged d post,
            ActiveFollowerLogging.checkedLogging i cut.input.row
              (cut.input.state.activations i) cut.input.time (prepared.arm, own) c = .ok logged ∧
            logged.buffer = c.buffer ++ ReferencePrelaunchFollower.logAt i cut.input.row
              (cut.input.state.activations i) cut.input.time (prepared.arm, own) ∧
            d = referenceDownCut p view i cut.input.row cut.input.time own rate logged ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).result = .ok post ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).downInput = some logged ∧
            (recordFollower view i cut.input.row (cut.input.state.activations i)
              cut.input.time (cut.input.active i) prepared.arm own c).down = some d ∧
            DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row cut.input.time
              own c mu post = .ok (post, mu) ∧
            (cut.output.followers i).configuration = .ordinary post mu ∧
            (cut.output.followers i).failure = none ∧
            post.status = .unoccupied ∧ localStateDomainValid post ∧
            post.S + post.backlog ≤ k * D p ∧
            post.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
            (∀ saved ∈ post.buffer, saved.calendarRound < (cut.input.time.val + 1) + 1) ∧
            (cut.output.followers i).downInput = some logged ∧
            (cut.output.followers i).down = some d := by
  classical
  intro E W k indexedCut
  obtain ⟨cut, suffix, hsplit, hindex, hcutTime, hactual, r, q, base,
    hinput, hcoordinator, dispatched, hstart, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, arm, hprep, hkpos, hsigma, hbase, hbirth,
    hbits, hqueues, hu, hsource, huT, hugrid, hgridT, hledgerSigma,
    hledgerCut, hledgerFreeze, hcut, _⟩ :=
    ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
      initial rows J rewards start count hspan active hfirst hshort
  have hindexed : cut = indexedCut := hindex
  rw [← hindexed]
  have hrow : cut.input.row = rows J := by
    rw [hactual]
    rfl
  have hcutRow : FollowerCutoffScan.firstCutoff p rate.eta.val r.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val cut.input.row) =
        cut.input.time.val + 1 := by
    rw [hrow]
    exact hcut
  have hsafe := ReferenceFirstLiveFollowerSafety.run_first_live_follower_safety
    initial rows J rewards start count hspan active hfirst seed memory hseed hS hdelta
    hbacklog hnone hunoccupied hvalid hpair htime hbatch
  obtain ⟨hprefix, hend⟩ := hsafe.1 k (by rfl)
  have hselect : ∃ selected : Selection cut.input,
      cut.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = r.payload ∧ selected.view.pendingAtChoice = Finset.univ := by
    simp only [hprep, DispatchCut.selection, selectionAt]
    exact ⟨_, rfl, rfl, hpending⟩
  obtain ⟨selected, hselection, hpayload, hselectedPending⟩ := hselect
  have hqzero : ∀ i, (selected.view.payload.downRecord i).val.q = 0 := by
    intro i
    obtain ⟨birth, _, _, _, installed, birthSelection, hbirthPrep, hbirthPayload⟩ := hbirth
    rw [hpayload, ← hbirthPayload]
    exact first_preparation_queue_zero birth installed birthSelection hbirthPrep i
  have hselectedSigma : selected.view.payload.sigma.val = start := by rw [hpayload]; exact hsigma
  have hselectedCut : FollowerCutoffScan.firstCutoff p rate.eta.val selected.view.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val cut.input.row) =
        cut.input.time.val + 1 := by rw [hpayload]; exact hcutRow
  intro i prepared own view
  have halign := cut.output.preparation.follower_alignment i
  change prepared.row = cut.input.row ∧ prepared.follower = i ∧
    prepared.time = cut.input.time ∧ prepared.activation = cut.input.state.activations i at halign
  have hobs : cut.output.followers i = finishFollower view prepared own := by
    dsimp only [view, prepared, own]
    rw [cut.output_eq]
    rfl
  cases hc : prepared.configuration with
  | dagger =>
      rw [hobs]
      simp [finishFollower, hc]
  | ordinary c mu =>
      obtain ⟨s, mem, hs, hv, hm, hp, hb, hz, ho⟩ := hend i
      have hinputFollower : cut.input.state.followers i = .ordinary s mem := by
        rw [hinput]
        exact hs
      have hchoice : (DeclaredFollowerLocalRound.prepare rate i cut.input.row
          (cut.input.state.activations i) cut.input.time (cut.input.active i)
          (.ordinary s mem)).configuration = .ordinary c mu := by
        have he := cut.output.preparation.followers.followers_eq i
        change prepared = DeclaredFollowerLocalRound.prepare rate i cut.input.row
          (cut.input.state.activations i) cut.input.time (cut.input.active i)
          (cut.input.state.followers i) at he
        rw [hinputFollower] at he
        rw [← he]
        exact hc
      have hocc : s.status ≠ .unoccupied → ∃ M token,
          s.lastDown = some M ∧ M.val.sigma = r.payload.sigma.val + 1 ∧
          mem.lastProposalRead = some token ∧ token.timestamp.val + 1 = cut.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val cut.input.row token.timestamp := by
        intro hne
        obtain ⟨_, M, token, hM, hMsigma, ht, hstamp, hbit⟩ := ho hne
        exact ⟨M, token, hM, by rw [hsigma]; exact hMsigma, ht,
          by rw [hcutTime]; exact hstamp, by rw [hrow]; exact hbit⟩
      obtain ⟨hcu, hcv, hcS, hcb, hcbuf, _⟩ := ordinary_cutoff_choice i cut.input.row
        (cut.input.state.activations i) cut.input.time r.payload.sigma (cut.input.active i)
        s c mem mu hchoice hv hocc hsource hcutRow
      have hcmass : c.S + c.backlog ≤ k * D p := by rw [hcS, hcb]; exact hm
      have hcpair : c.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) := by
        rw [hcbuf]
        exact hp
      have hcbefore : ∀ saved ∈ c.buffer, saved.calendarRound < cut.input.time.val + 1 := by
        rw [hcbuf, hcutTime]
        exact hb
      obtain ⟨logged, post, hlog, hlogbuf, hrecord, hpostu, hpostv, hpostmass,
          hpostpair, hposttime⟩ := cutoff_record_success cut selected hselection hselectedPending
        start k hcutTime hselectedSigma hqzero hselectedCut i c hcu hcv hcmass hcpair hcbefore
      let d := referenceDownCut p view i cut.input.row cut.input.time own rate logged
      have hdiagnostics := recordFollower_logged view i cut.input.row
        (cut.input.state.activations i) cut.input.time (cut.input.active i)
        prepared.arm own c logged hcu hlog
      have hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate i cut.input.row
          cut.input.time own c mu post = .ok (post, mu) := by
        rw [DeclaredFollowerLocalRound.releaseAndFinish,
          releaseAfterService_unoccupied rate.eta i cut.input.time
            (publicRowOfCompleteRow cut.input.row cut.input.time) own c post hcu]
        simp only [finishRound_unoccupied rate.eta cut.input.time cut.input.row post mu hpostv hpostu]
      have hrecordLocal : (recordFollower view prepared.follower prepared.row
          prepared.activation prepared.time prepared.active prepared.arm own c).result = .ok post := by
        simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hrecord
      have hfinishLocal : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower
          prepared.row prepared.time own c mu post = .ok (post, mu) := by
        simpa only [halign.1, halign.2.1, halign.2.2.1] using hfinish
      have hout := finishFollower_success view prepared own c post post mu mu hc hrecordLocal hfinishLocal
      have hdiag := ReferenceFollowerSparseEmissionRecovery.finishFollower_diagnostics view prepared own c mu hc
      have hactualInput : (cut.output.followers i).downInput = some logged := by
        rw [hobs, hdiag.1]
        simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostics.1
      have hactualDown : (cut.output.followers i).down = some d := by
        rw [hobs, hdiag.2]
        simpa only [halign.1, halign.2.1, halign.2.2.1, halign.2.2.2] using hdiagnostics.2
      exact ⟨logged, d, post, hlog, hlogbuf, rfl, hrecord, hdiagnostics.1, hdiagnostics.2,
        hfinish, hobs ▸ hout.1, hobs ▸ hout.2, hpostu, hpostv, hpostmass,
        hpostpair, hposttime, hactualInput, hactualDown⟩

end Bandits.Support.ReferenceFirstCutoffFollowerObservation

end
