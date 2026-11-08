/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedLiveConfirmationAcceptedDown
public import Bandits.Support.ReferenceFirstReplacementInstalledCredit

import Lean.Elab.Tactic.Omega

/-!
# Coordinator collection and assignment mass steps

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64` and
`sources/zip4/manuscript/06_interruptions.tex:255-282,303-348,355-390`.

These numerical lemmas preserve local credit through collection, reconstruction,
and actual assignment installation. The birth result has a per-record incoming
credit premise; collection-round preservation has an explicit missing local UP
reply producer. The complete original-run simultaneous induction and the
historical coordinator/reply alignment are separate obligations.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceAssignmentCollectionMassSteps

open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal base stored by an actual installation constructor. There is
no base on a noninstallation branch, and no base is reconstructed from a
payload alone. -/
def installedBaseScore
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (Fin (p.m - 1) → ℕ) :=
  match record.output.preparation.coordinator with
  | .first (.chosen installed _) => some installed.followerBaseScore
  | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      some installed.retainedBaseScore
  | _ => none

/-- A pointwise arrival cap bounds the total accepted queue mass. -/
private theorem accepted_total_le
    (records : List (Bool × ℕ)) (bound : ℕ)
    (hcap : ∀ record ∈ records, record.2 ≤ bound) :
    RecordedQueueRun.acceptedTotal records ≤ records.length * bound := by
  induction records with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      have hh : RecordedQueueRun.acceptedArrival head ≤ bound := by
        unfold RecordedQueueRun.acceptedArrival
        split
        · exact hcap head (List.mem_cons_self)
        · exact Nat.zero_le _
      have ht := ih (fun record hmem => hcap record (List.mem_cons_of_mem _ hmem))
      change RecordedQueueRun.acceptedArrival head +
        RecordedQueueRun.acceptedTotal tail ≤ (tail.length + 1) * bound
      calc
        _ ≤ bound + tail.length * bound := Nat.add_le_add hh ht
        _ = (tail.length + 1) * bound := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem collection_start_arrival_cap
    (l started : ReferenceActivePhysicalStep.Ledger rate)
    (r : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (hstart : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound r) enabled raw = .success started)
    (a : Fin p.K) :
    (CoordinatorCollectionLedger.localQueueRecord l r enabled raw a).2 ≤ D p := by
  have hinput : CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = .ready ∧ CoordinatorCollectionLedger.sourceRound r = l.cursor ∧
      1 ≤ CoordinatorCollectionLedger.sourceRound r ∧
      CoordinatorCollectionLedger.sourceRound r ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
    by_contra hnot
    simp only [CoordinatorCollectionLedger.startRound, dite_eq_right hnot] at hstart
    cases hstart
  unfold CoordinatorCollectionLedger.localQueueRecord
  split
  · dsimp only
    cases raw with
    | none => exact Nat.zero_le _
    | some entry =>
        have hcap : entry.2 ≤ D p := of_decide_eq_true hinput.2.2.2.2.2
        rcases entry with ⟨arm, amount⟩
        change (if arm = a then amount else 0) ≤ D p
        split
        · exact hcap
        · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- One known collection entry preserves its numerical credit through START,
either kind of ordinary decode, and FINISH. The existing operational theorem
accounts for transient local service and for acceptance on a different arm. -/
theorem collection_known_round_mass
    (l started decoded finished : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (a : Fin p.K) (cutoff : CoordinatorCollectionLedger.CutoffRegister)
    (current : CoordinatorCollectionLedger.CurrentRegister) (e : ℕ)
    (hcutoff : l.cutoffRegisters a = some cutoff)
    (hknown : l.currentRegisters a = some current)
    (hcredit : cutoff.score + l.increment a + current.queue ≤ e * D p)
    (hstart : CoordinatorCollectionLedger.startRound l
      (CoordinatorCollectionLedger.sourceRound input.round) input.enabled input.raw = .success started)
    (hdecode : CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed =
        .success decoded ∨
      CoordinatorCollectionLedger.decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : CoordinatorCollectionLedger.finishRound decoded = .success finished) :
    ∃ next : CoordinatorCollectionLedger.CurrentRegister,
      finished.cutoffRegisters a = some cutoff ∧ finished.currentRegisters a = some next ∧
      cutoff.score + finished.increment a + next.queue ≤ (e + 1) * D p ∧
      next.lastService ≤ D p := by
  let record := CoordinatorCollectionLedger.localQueueRecord l input.round input.enabled input.raw a
  let next := QueueReplay.transition (4 * rate.n) (l.increment a, current.queue) record
  obtain ⟨hcurrent, hincrement, _hassignment, _hsigma, _hcut, _hfreeze, hcutoffRegister⟩ :=
    CollectionKnownQueueContinuation.checkedRound_known_transition l started decoded finished
      input a current hknown hstart hdecode hfinish
  refine ⟨⟨next.2, next.1 - l.increment a⟩,
    hcutoffRegister.trans hcutoff, hcurrent, ?_, ?_⟩
  · change cutoff.score + finished.increment a + next.2 ≤ _
    rw [hincrement]
    have htotal := RecordedQueueRun.transition_total (4 * rate.n)
      (l.increment a, current.queue) record
    have hcap := collection_start_arrival_cap l started input.round input.enabled input.raw hstart a
    have haccept : RecordedQueueRun.acceptedArrival record ≤ D p := by
      unfold RecordedQueueRun.acceptedArrival
      split
      · exact hcap
      · exact Nat.zero_le _
    have hmass : cutoff.score + next.1 + next.2 =
        cutoff.score + l.increment a + current.queue + RecordedQueueRun.acceptedArrival record := by
      dsimp only at htotal
      change next.1 + next.2 = _ at htotal
      omega
    change cutoff.score + next.1 + next.2 ≤ _
    rw [hmass, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hcredit haccept
  · change next.1 - l.increment a ≤ D p
    have hscore := RecordedQueueRun.transition_score_eq_add_recordService
      (4 * rate.n) (l.increment a, current.queue) record
    change next.1 = l.increment a + _ at hscore
    rw [hscore, Nat.add_sub_cancel_left]
    unfold RecordedQueueRun.recordService
    split
    · exact (CappedService.service_le_capacity _ _ _).trans
        (ActiveFollowerDownAcceptance.four_n_le_D p rate)
    · exact Nat.zero_le _

/-- Successful reconstruction copies every present pair before the new
assignment restricts arms. This numerical lemma uses no truthful source-score
or source-queue identity. -/
theorem reconstruction_mass
    {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (D p : ℝ)}
    (l : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart l instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart l instruction =
      .success l instruction out)
    (hcredit : ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
      (q : CoordinatorCollectionLedger.CurrentRegister),
      l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤ instruction.time.val * D p) :
    ∀ a : Fin p.K, AssignmentScoreReconstruction.sourceScore out a +
      AssignmentScoreReconstruction.initialQueue out a ≤ instruction.time.val * D p := by
  obtain ⟨_hchecks, hcutoff, hcurrent, hscore, hqueue, _hrest⟩ :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations l instruction out hcall
  intro a
  rw [hscore a, hqueue a]
  exact hcredit a (out.registers.cutoff a) (out.registers.current a) (hcutoff a) (hcurrent a)

/-- New installation simultaneously inherits all-arm queue credit, complement
mass and the stronger retained-base-plus-DOWN credit. Its old ledger premise
is local numerical credit, to be supplied before any tail operation. -/
theorem later_installation_mass
    {old : ReferenceActivePhysicalStep.Payload rate}
    {l : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old l instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (hcredit : ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
      (q : CoordinatorCollectionLedger.CurrentRegister),
      l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤ instruction.time.val * D p) :
    let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
    (∀ a : Fin p.K, installed.registers.payload.queues a ≤
      installed.registers.payload.sigma.val * D p) ∧
    (∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      installed.registers.complementScores j + installed.ownedRegisters.queue j ≤
        installed.registers.payload.sigma.val * D p) ∧
    (∀ i : Fin (p.m - 1), installed.retainedBaseScore i +
      installed.registers.payload.queues (installed.registers.payload.assignment.assigned i) ≤
        installed.registers.payload.sigma.val * D p) ∧
    (∀ i : Fin (p.m - 1), let M := installed.registers.payload.downRecord i
      installed.retainedBaseScore i + M.val.q ≤ (M.val.sigma - 1) * D p) := by
  have hmass := reconstruction_mass l instruction output.reconstruction output.reconstruction_eq hcredit
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hsigma : installed.registers.payload.sigma = instruction.time := output.payload_start
  have hqueue : ∀ a, installed.registers.payload.queues a =
      AssignmentScoreReconstruction.initialQueue output.reconstruction a :=
    CoordinatorAssignmentRegisterInstall.later_payload_queue_eq_initial_queue output clockData
  have hfollower : ∀ i : Fin (p.m - 1), installed.retainedBaseScore i +
      installed.registers.payload.queues (installed.registers.payload.assignment.assigned i) ≤
        installed.registers.payload.sigma.val * D p := by
    intro i
    rw [CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source output clockData i,
      hqueue, hsigma]
    exact hmass (output.payload.assignment.assigned i)
  refine ⟨?_, ?_, hfollower, ?_⟩
  · intro a
    rw [hqueue a, hsigma]
    exact (Nat.le_add_left _ _).trans (hmass a)
  · intro j
    rw [CoordinatorAssignmentRegisterInstall.later_complement_score_eq_source_score output clockData j,
      CoordinatorAssignmentRegisterInstall.later_owned_queue_eq_initial_queue output clockData j, hsigma]
    exact hmass j.val
  · intro i
    dsimp only
    rw [installed.registers.payload.downRecord_initialQueue i,
      installed.registers.payload.downRecord_fields i]
    simpa only [Nat.add_sub_cancel] using hfollower i

/-- Conditional PREPARE preservation on the actual record. Its sole numerical
input concerns the actual incoming collection ledger. The first branch derives
its zero seed; the later branch establishes all-arm credit before the tail,
even when that tail subsequently enters dagger.

The complete fold must discharge `hready` at each original prefix. This lemma
does not assert the requested unconditional all-birth theorem. -/
theorem record_birth_mass_of_ready_credit
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hready : ∀ (old : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool)),
      record.input.state.coordinator = .collection old l saved →
      ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
        (q : CoordinatorCollectionLedger.CurrentRegister),
        l.cutoffRegisters a = some c → l.currentRegisters a = some q →
        c.score + l.increment a + q.queue ≤ record.input.time.val * D p)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth record P) :
    ∃ beta : Fin (p.m - 1) → ℕ,
      installedBaseScore record = some beta ∧
      (∀ a : Fin p.K, P.queues a ≤ P.sigma.val * D p) ∧
      (∀ i : Fin (p.m - 1), beta i + P.queues (P.assignment.assigned i) ≤ P.sigma.val * D p) := by
  classical
  have hactual : record.output.preparation.coordinator = dispatch record.input := by
    rw [record.output_eq]
    rfl
  cases hconfiguration : record.input.state.coordinator with
  | first =>
      have hdispatch : record.output.preparation.coordinator =
          .first (CoordinatorRoundDispatch.dispatchFirst (firstInput record.input)) := by
        rw [hactual]
        simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch] at hbirth
      cases hfirst : CoordinatorRoundDispatch.dispatchFirst (firstInput record.input) with
      | choiceDomainFailure installed => simp only [hfirst] at hbirth
      | recorderBoundaryFailure installed => simp only [hfirst] at hbirth
      | choiceRejected installed => simp only [hfirst] at hbirth
      | chosen installed selected =>
          simp only [hfirst] at hbirth
          rcases hbirth with ⟨rfl, _htime⟩
          have hzero := (dispatchFirst_zero_seed record.input installed selected hfirst).2.2.2
          have hqueues : ∀ a : Fin p.K, installed.registers.payload.queues a = 0 := by
            rw [dispatchFirst_chosen_installation record.input installed selected hfirst,
              CoordinatorAssignmentRegisterInstall.first_payload_queues_eq_start]
            exact FirstAssignmentLaunch.Input.start_queues_zero _
          refine ⟨installed.followerBaseScore, ?_, ?_, ?_⟩
          · simp only [installedBaseScore, hdispatch, hfirst]
          · intro a
            rw [hqueues a]
            exact Nat.zero_le _
          · intro i
            rw [hzero i, hqueues, Nat.zero_add]
            exact Nat.zero_le _
  | live registers owned base =>
      have hdispatch : record.output.preparation.coordinator =
          .live registers owned base
            (CoordinatorRoundDispatch.dispatchLive (liveInput record.input registers owned base)) := by
        rw [hactual]
        simp only [dispatch, hconfiguration, CoordinatorRoundDispatch.dispatch]
        rfl
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch] at hbirth
  | collection old ledger saved =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := collectionClock old ledger saved cutoff
        have hdispatch : record.output.preparation.coordinator = .collection old ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection (collectionInput record.input old ledger clock cutoff)) := by
          rw [hactual]
          simp only [dispatch, hconfiguration, dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch] at hbirth
        cases houtcome : CoordinatorRoundDispatch.dispatchCollection
            (collectionInput record.input old ledger clock cutoff) <;>
          rw [houtcome] at hbirth <;> dsimp only at hbirth
        rename_i core consistent started hstart instruction hinstruction output hlocal
          clockData installed selected
        have hprovenance := ReferenceLaterInstallationProvenance.dispatch_laterChosen_provenance
          record.input
        rw [← hactual, hdispatch, houtcome] at hprovenance
        obtain ⟨hinstalled, _hpayload, _hsigma, _hdown⟩ := hprovenance
        have fields := CoordinatorRoundDispatch.collectionOperationLedger_fields
          (collectionInput record.input old ledger clock cutoff) core.payload_n_eq
        obtain ⟨_hassignment, _hstartSigma, _hcut, _hfreeze, _hbase, _hpending,
          hcutoffRegisters, hcurrentRegisters, hincrement, _hother⟩ := fields
        have htime := later_instruction_time record.input old ledger clock cutoff core
          started instruction hstart hinstruction
        have hoperation : ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
            (q : CoordinatorCollectionLedger.CurrentRegister),
            (CoordinatorRoundDispatch.collectionOperationLedger
              (collectionInput record.input old ledger clock cutoff) core.payload_n_eq).cutoffRegisters a =
                some c →
            (CoordinatorRoundDispatch.collectionOperationLedger
              (collectionInput record.input old ledger clock cutoff) core.payload_n_eq).currentRegisters a =
                some q →
            c.score + (CoordinatorRoundDispatch.collectionOperationLedger
              (collectionInput record.input old ledger clock cutoff) core.payload_n_eq).increment a +
                q.queue ≤ instruction.time.val * D p := by
          intro a c q hc hq
          rw [hcutoffRegisters] at hc
          rw [hcurrentRegisters] at hq
          rw [hincrement, htime]
          exact hready old ledger saved hconfiguration a c q hc hq
        obtain ⟨hqueues, _hcomplement, hfollowers, _hdownCredit⟩ :=
          later_installation_mass output clockData hoperation
        subst installed
        rcases hbirth with ⟨rfl, _hbirthTime⟩
        refine ⟨(CoordinatorAssignmentRegisterInstall.installLater output clockData).retainedBaseScore,
          ?_, hqueues, hfollowers⟩
        simp only [installedBaseScore, hdispatch, houtcome]
      · have hdispatch : record.output.preparation.coordinator = .invalidCollectionCutoff := by
          rw [hactual]
          simp only [dispatch, hconfiguration, dite_eq_right hcutoff]
        simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch] at hbirth
  | dagger =>
      have hdispatch : record.output.preparation.coordinator = .dagger := by
        rw [hactual]
        simp only [dispatch, hconfiguration]
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hdispatch] at hbirth

section CollectionReplay

open CoordinatorCollectionLedger CollectionCheckedExecution

private theorem replay_records_length
    (l : ReferenceActivePhysicalStep.Ledger rate) (a : Fin p.K)
    (indices : List (Fin p.T)) (records : List (Bool × ℕ))
    (hcall : replayRecords? l a indices = some records) :
    records.length = indices.length := by
  induction indices generalizing records with
  | nil =>
      have heq : [] = records := Option.some.inj hcall
      subst records
      rfl
  | cons index indices ih =>
      cases he : l.enabledHistory index with
      | none => simp [replayRecords?, he] at hcall
      | some enabled =>
          cases ht : replayRecords? l a indices with
          | none =>
              simp [replayRecords?, he, ht] at hcall
          | some tail =>
              simp [replayRecords?, he, ht] at hcall
              subst records
              simp only [List.length_cons, ih tail ht]

/-- Numerical information from the actual replay-domain check. This private
inversion retains the exact replay records computed by this decode. -/
private theorem decode_replay_caps
    (l result : ReferenceActivePhysicalStep.Ledger rate) (i : Fin (p.m - 1))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val))
    (h : decodeUp l i (some M) = .success result) :
    1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧
      ∃ hbound : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T,
      ∃ lastIndex : Fin p.T, sourceRound lastIndex = l.cursor ∧
      ∃ past current,
        replayRecords? l (l.assignment.arm i)
          (calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) hbound) = some past ∧
        replayRecords? l (l.assignment.arm i) [lastIndex] = some [current] ∧
        (∀ record ∈ past ++ [current], record.2 ≤ D p) := by
  by_cases hinput : validLedgerCheck l = true ∧ l.phase = .started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · by_cases haccept : acceptUpCheck l i M = true
    · by_cases hunknown : l.currentRegisters (l.assignment.arm i) = none ∧
          l.cutoffRegisters (l.assignment.arm i) = none
      · have hcutPos := hinput.2.2.1
        have hcutCursor := hinput.2.2.2.1
        have hcursorT := hinput.2.2.2.2
        have hprefix : l.cutoff - 1 + (l.cursor - l.cutoff) ≤ p.T := by omega
        let indices := calendarIndices p.T (l.cutoff - 1) (l.cursor - l.cutoff) hprefix
        let lastIndex : Fin p.T := ⟨l.cursor - 1, by omega⟩
        cases hpast : replayRecords? l (l.assignment.arm i) indices with
        | none => simp [decodeUp, hinput, haccept, hunknown, indices, hpast] at h
        | some past =>
            cases hlast : replayRecords? l (l.assignment.arm i) [lastIndex] with
            | none => simp [decodeUp, hinput, haccept, hunknown, indices, lastIndex, hpast, hlast] at h
            | some records =>
                cases records with
                | nil => simp [decodeUp, hinput, haccept, hunknown, indices, lastIndex, hpast, hlast] at h
                | cons current tail =>
                    cases tail with
                    | nil =>
                        by_cases hdomain : replayOutputDomainsCheck (p := p)
                            (4 * rate.n) M.val.q (past ++ [current]) = true
                        · have hcap : (past ++ [current]).all (fun record => decide (record.2 ≤ D p)) =
                              true := by
                            have hc := hdomain
                            simp only [replayOutputDomainsCheck, Bool.and_eq_true] at hc
                            exact hc.1.2
                          refine ⟨hcutPos, hcutCursor, hprefix, lastIndex, ?_, past, current,
                            hpast, hlast, ?_⟩
                          · dsimp only [sourceRound, lastIndex]
                            omega
                          · intro record hrecord
                            exact of_decide_eq_true ((List.all_eq_true.mp hcap) record hrecord)
                        · simp [decodeUp, hinput, haccept, hunknown, indices, lastIndex,
                            hpast, hlast, hdomain] at h
                    | cons _ _ =>
                        simp [decodeUp, hinput, haccept, hunknown, indices, lastIndex, hpast, hlast] at h
      · simp [decodeUp, hinput, haccept, hunknown] at h
    · let next : ReferenceActivePhysicalStep.Ledger rate := { l with phase := .decoded }
      by_cases hvalid : validLedgerCheck next = true <;>
        simp [decodeUp, hinput, haccept, next, hvalid] at h
  · simp [decodeUp, hinput] at h

private theorem replay_final_service_le (capacity : ℕ) (initial : ℕ × ℕ)
    (past : List (Bool × ℕ)) (current : Bool × ℕ) :
    (QueueReplay.replay capacity initial (past ++ [current])).1 -
      (QueueReplay.replay capacity initial past).1 ≤ capacity := by
  rw [QueueReplay.replay_append]
  change (QueueReplay.transition capacity (QueueReplay.replay capacity initial past) current).1 -
    (QueueReplay.replay capacity initial past).1 ≤ capacity
  rw [RecordedQueueRun.transition_score_eq_add_recordService, Nat.add_sub_cancel_left]
  unfold RecordedQueueRun.recordService
  split
  · exact CappedService.service_le_capacity _ _ _
  · exact Nat.zero_le _

/-- An accepted collection reply carries OLD-cutoff mass through every
computed replay date up to receipt. Enabled zero arrivals serve and disabled
dates preserve mass. The checked FINISH theorem supplies the zero transient
service on this just-recovered arm, so receipt is counted once.

The reply inequality is a local induction input. Its same-birth producer on
the original run is still required by the complete simultaneous fold. -/
theorem collection_acceptance_mass
    (l started decoded finished : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (M : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val))
    (hreply : l.baseScore input.selectedFollower + M.val.S + M.val.q ≤ (l.cutoff - 1) * D p)
    (hdelta : M.val.delta ≤ D p)
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw = .success started)
    (hdecode : decodeUp started input.selectedFollower (some M) = .success decoded)
    (hfinish : finishRound decoded = .success finished) :
    ∃ (cutoff : CutoffRegister) (current : CurrentRegister),
      finished.cutoffRegisters (l.assignment.arm input.selectedFollower) = some cutoff ∧
      finished.currentRegisters (l.assignment.arm input.selectedFollower) = some current ∧
      cutoff.score + finished.increment (l.assignment.arm input.selectedFollower) + current.queue ≤
        (sourceRound input.round) * D p ∧
      cutoff.score + cutoff.queue ≤ (l.cutoff - 1) * D p ∧
      cutoff.lastService ≤ D p ∧ current.lastService ≤ D p := by
  obtain ⟨hb, lastIndex, hlastSource, past, current, hpast, hlast, _hunknown,
    hcurrent, hincrement, hcutoff⟩ := checked_acceptance_finish_once l started decoded finished
      (sourceRound input.round) input.enabled input.raw input.selectedFollower M hstart hdecode hfinish
  obtain ⟨hcutPos, hcutCursor, hb', lastIndex', hlastSource', past', current', hpast', hlast', hcaps⟩ :=
    decode_replay_caps started decoded input.selectedFollower M hdecode
  have hcursor := startRound_success_cursor l started (sourceRound input.round)
    input.enabled input.raw hstart
  have hlastEq : lastIndex' = lastIndex := by
    apply Fin.ext
    have hsourceEq := hlastSource'.trans (hcursor.trans hlastSource.symm)
    change lastIndex'.val + 1 = lastIndex.val + 1 at hsourceEq
    exact Nat.add_right_cancel hsourceEq
  subst lastIndex'
  have hpastEq : past' = past := Option.some.inj (hpast'.symm.trans hpast)
  subst past'
  have hcurrentEq : current' = current :=
    (List.cons.inj (Option.some.inj (hlast'.symm.trans hlast))).1
  subst current'
  have hpastLength : past.length = started.cursor - started.cutoff := by
    rw [replay_records_length started _ _ past hpast, calendarIndices_length]
  have hcandidate := startRound_success_candidate l started (sourceRound input.round)
    input.enabled input.raw hstart
  have hassignment : started.assignment = l.assignment := by rw [hcandidate]; rfl
  have hbase : started.baseScore = l.baseScore := by rw [hcandidate]; rfl
  have hcut : started.cutoff = l.cutoff := by rw [hcandidate]; rfl
  rw [hassignment] at hcurrent hincrement hcutoff
  let records := past ++ [current]
  let replayed := QueueReplay.replay (4 * rate.n) (0, M.val.q) records
  let previous := QueueReplay.replay (4 * rate.n) (0, M.val.q) past
  refine ⟨⟨started.baseScore input.selectedFollower + M.val.S, M.val.q, M.val.delta⟩,
    ⟨replayed.2, replayed.1 - previous.1⟩, hcutoff, hcurrent, ?_, ?_, hdelta, ?_⟩
  · dsimp only
    rw [hincrement]
    change started.baseScore input.selectedFollower + M.val.S + replayed.1 + replayed.2 ≤ _
    have htotal := RecordedQueueRun.replay_total (4 * rate.n) (0, M.val.q) records
    change replayed.1 + replayed.2 = 0 + M.val.q + RecordedQueueRun.acceptedTotal records at htotal
    have hcap := accepted_total_le records (D p) hcaps
    have hlength : records.length = started.cursor - started.cutoff + 1 := by
      simp only [records, List.length_append, List.length_singleton, hpastLength]
    rw [hlength] at hcap
    have hreply' : started.baseScore input.selectedFollower + M.val.S + M.val.q ≤
        (started.cutoff - 1) * D p := by rw [hbase, hcut]; exact hreply
    have htimes : started.cutoff - 1 + (started.cursor - started.cutoff + 1) = started.cursor := by omega
    calc
      _ = (started.baseScore input.selectedFollower + M.val.S + M.val.q) +
          RecordedQueueRun.acceptedTotal records := by omega
      _ ≤ (started.cutoff - 1) * D p + (started.cursor - started.cutoff + 1) * D p :=
        Nat.add_le_add hreply' hcap
      _ = (sourceRound input.round) * D p := by rw [← Nat.add_mul, htimes, hcursor]
  · dsimp only
    rw [hbase]
    exact hreply
  · exact (replay_final_service_le (4 * rate.n) (0, M.val.q) past current).trans
      (ActiveFollowerDownAcceptance.four_n_le_D p rate)

/-- Simultaneous numerical preservation for every actually present pair in
one completed collection round. Unknown entries acquire mass only on the
actual accepted arm. Rejection and other-arm acceptance frame existing
cutoff credit; absent entries are never interpreted as zero queues.

The incoming per-entry inequalities are explicit local inputs. The `hreply`
argument is the MISSING physical producer of the accepted sender's frozen reply
credit; it is not established as a law of the run. -/
theorem collection_round_mass
    (l started decoded finished : ReferenceActivePhysicalStep.Ledger rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hcredit : ∀ (a : Fin p.K) (c : CutoffRegister) (q : CurrentRegister),
      l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤ input.round.val * D p ∧
        c.score + c.queue ≤ (l.cutoff - 1) * D p ∧ c.lastService ≤ D p)
    (hreply : ∀ M : OrdinaryMessageCodec.UpRecord (codecParams p rate.eta.val),
      input.parsed = some M → decodeUp started input.selectedFollower (some M) = .success decoded →
      l.baseScore input.selectedFollower + M.val.S + M.val.q ≤ (l.cutoff - 1) * D p ∧
        M.val.delta ≤ D p)
    (hstart : startRound l (sourceRound input.round) input.enabled input.raw = .success started)
    (hdecode : decodeUp started input.selectedFollower input.parsed = .success decoded ∨
      decodeUp started input.selectedFollower input.parsed = .rejected decoded)
    (hfinish : finishRound decoded = .success finished) :
    ∀ (a : Fin p.K) (c : CutoffRegister) (q : CurrentRegister),
      finished.cutoffRegisters a = some c → finished.currentRegisters a = some q →
      c.score + finished.increment a + q.queue ≤ (input.round.val + 1) * D p ∧
        c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
        c.lastService ≤ D p ∧ q.lastService ≤ D p := by
  intro a c q hc hq
  cases hknown : l.currentRegisters a with
  | some previous =>
      obtain ⟨_hcurrent, _hincrement, _hassignment, _hsigma, _hcut, _hfreeze, hcutFrame⟩ :=
        CollectionKnownQueueContinuation.checkedRound_known_transition l started decoded finished
          input a previous hknown hstart hdecode hfinish
      have hcutOld : l.cutoffRegisters a = some c := hcutFrame.symm.trans hc
      obtain ⟨hmass, hfrozen, hlast⟩ := hcredit a c previous hcutOld hknown
      obtain ⟨next, _hcutoff, hcurrent, hmassNext, hlastNext⟩ := collection_known_round_mass
        l started decoded finished input a c previous input.round.val
        hcutOld hknown hmass hstart hdecode hfinish
      have hsame : next = q := Option.some.inj (hcurrent.symm.trans hq)
      subst next
      exact ⟨hmassNext, hfrozen, hlast, hlastNext⟩
  | none =>
      have hstartCandidate := startRound_success_candidate l started (sourceRound input.round)
        input.enabled input.raw hstart
      have hindex : (⟨sourceRound input.round - 1, by simp [sourceRound]⟩ : Fin p.T) =
          input.round := by
        apply Fin.ext
        simp only [sourceRound, Nat.add_sub_cancel]
      rw [hindex] at hstartCandidate
      have hstartedNone : started.currentRegisters a = none := by
        rw [hstartCandidate]
        simp only [startRoundCandidate, hknown]
      have hfinishCandidate := finishRound_success_candidate decoded finished hfinish
      rcases hdecode with hsuccess | hrejected
      · cases hparsed : input.parsed with
        | none =>
            rw [hparsed] at hsuccess
            unfold decodeUp at hsuccess
            split at hsuccess
            · dsimp only at hsuccess
              split at hsuccess <;> contradiction
            · contradiction
        | some M =>
            have hs : decodeUp started input.selectedFollower (some M) = .success decoded := by
              simpa only [hparsed] using hsuccess
            obtain ⟨_hb, _lastIndex, _hsource, past, current, _hpast, _hcurrent, _hunknown,
              hdecodedCandidate⟩ := decodeUp_success_candidate started decoded input.selectedFollower M hs
            have harm : a = started.assignment.arm input.selectedFollower := by
              by_contra hne
              have hdecodedNone : decoded.currentRegisters a = none := by
                rw [hdecodedCandidate]
                simp only [acceptUpCandidate, Function.update_of_ne hne, hstartedNone]
              have hfinishedNone : finished.currentRegisters a = none := by
                rw [hfinishCandidate]
                exact hdecodedNone
              rw [hfinishedNone] at hq
              cases hq
            have hassignment : started.assignment = l.assignment := by rw [hstartCandidate]; rfl
            rw [hassignment] at harm
            subst a
            obtain ⟨hmass, hdelta⟩ := hreply M hparsed hs
            obtain ⟨cutoff, current, hcutoff, hcurrent, hmass, hfrozen, hlast, hlastCurrent⟩ :=
              collection_acceptance_mass l started decoded finished input M hmass hdelta hstart hs hfinish
            have hcutEq : cutoff = c := Option.some.inj (hcutoff.symm.trans hc)
            have hcurrentEq : current = q := Option.some.inj (hcurrent.symm.trans hq)
            subst cutoff
            subst current
            exact ⟨hmass, hfrozen, hlast, hlastCurrent⟩
      · have hdecodedCandidate := CollectionKnownQueueContinuation.decodeUp_rejected_candidate
          started decoded input.selectedFollower input.parsed hrejected
        have hfinishedNone : finished.currentRegisters a = none := by
          rw [hfinishCandidate, hdecodedCandidate]
          exact hstartedNone
        rw [hfinishedNone] at hq
        cases hq

end CollectionReplay

/-- A checked live complement service pass spends exactly one capped arrival
per arm. In particular a zero arrival still performs the queue transition. -/
theorem live_service_mass
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (serviced : CoordinatorLiveServiceFinish.ServicedRegisters r owned) (e : ℕ)
    (hcredit : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j + owned.queue j ≤ e * D p) :
    ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      serviced.score j + serviced.queue j ≤ (e + 1) * D p := by
  intro j
  rw [CoordinatorLiveServiceFinish.serviced_conservation r owned serviced j,
    Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add (hcredit j) (serviced.arrivalDomain j)

/-- At the actual cutoff initializer, every present pair comes from a real
old complement arm. Its initial increment is zero, its cutoff mass is frozen
at `u - 1`, and both last-service fields are copied from that arm. Unknown
assigned arms remain absent; they acquire no invented numerical registers. -/
theorem collection_start_mass
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (time : Fin p.T)
    (hcredit : ∀ j : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores j + owned.queue j ≤ time.val * D p)
    (hprevious : owned.previousServiceDomainValid) :
    let l := CoordinatorStartRoundCutoffDispatch.collectionStartLedger r owned base time
    ∀ (a : Fin p.K) (c : CoordinatorCollectionLedger.CutoffRegister)
      (q : CoordinatorCollectionLedger.CurrentRegister),
      l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤ time.val * D p ∧
        c.score + c.queue ≤ (l.cutoff - 1) * D p ∧
        c.lastService ≤ D p ∧ q.lastService ≤ D p := by
  dsimp only
  intro a c q hc hq
  dsimp only [CoordinatorStartRoundCutoffDispatch.collectionStartLedger] at hc hq ⊢
  rw [hc] at hq
  simp only [Option.map_some, Option.some.injEq] at hq
  subst q
  unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters at hc
  split at hc
  · rename_i hfast
    have heq := Option.some.inj hc
    subst c
    refine ⟨?_, ?_, hprevious ⟨a, hfast⟩, hprevious ⟨a, hfast⟩⟩
    · simpa only [Nat.add_zero] using hcredit ⟨a, hfast⟩
    · simpa only [Nat.add_sub_cancel] using hcredit ⟨a, hfast⟩
  · cases hc
end Bandits.Support.ReferenceAssignmentCollectionMassSteps

end
