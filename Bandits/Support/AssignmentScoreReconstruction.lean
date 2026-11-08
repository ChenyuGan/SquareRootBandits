/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.CoordinatorCollectionLedger
public import Bandits.Support.CoordinatorPhaseClock
public import Bandits.Support.ScoreWeights

/-!
# Checked later assignment score reconstruction

This module implements only the coordinator's local numerical reconstruction
at a later assignment start. It consumes an existing completed collection
ledger and the existing source-clock instruction. It does not construct a
physical run, replay the collection, or assert recovery to physical scores.
This module owns that local numerical operation; active-run-frontier work
remains limited to its separately bounded report.

Source: `sources/zip4/manuscript/06_interruptions.tex:16-35,46-61,80-100`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

public section

namespace Bandits.Support.AssignmentScoreReconstruction

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock

variable {p : ConstructorDimensions.Parameters}
variable {eta : ℝ} {heta : 0 < eta}
variable {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
variable {n : ℕ}
variable {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}

abbrev LocalLedger (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : CoordinatorCollectionLedger.sourceLearningCap p eta)
    (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) :=
  CoordinatorCollectionLedger.Ledger p eta heta hcap n hn

/-- The source weight base for this constructor's literal dyadic denominator.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:139-172`. -/
@[expose] noncomputable def sourceWeightBase
    (p : ConstructorDimensions.Parameters) : ℝ :=
  1 + 1 / (ConstructorDimensions.D p : ℝ)

theorem sourceWeightBase_pos (p : ConstructorDimensions.Parameters) :
    0 < sourceWeightBase p := by
  exact ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))

/-- The later-start branch selected by the source comparison with the
ledger's existing freeze boundary. The time coordinate is zero-based in Lean,
so the manuscript round is `time.val + 1`. -/
@[expose] def expectedLaterStartKind (freezeAt : ℕ) (time : Fin p.T) :
    AssignmentStartKind :=
  if time.val + 1 < freezeAt then .corrected else .renewal

theorem expectedLaterStartKind_eq_corrected_iff (freezeAt : ℕ)
    (time : Fin p.T) :
    expectedLaterStartKind (p := p) freezeAt time = .corrected ↔
      time.val + 1 < freezeAt := by
  simp [expectedLaterStartKind]

theorem expectedLaterStartKind_eq_renewal_iff (freezeAt : ℕ)
    (time : Fin p.T) :
    expectedLaterStartKind (p := p) freezeAt time = .renewal ↔
      freezeAt ≤ time.val + 1 := by
  simp [expectedLaterStartKind]

private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔
      ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h (test i) (by simp)
  · intro h b hb
    obtain ⟨i, hi⟩ := (List.mem_ofFn.mp hb)
    subst b
    exact h i

private theorem armPendingCheck_eq_true_iff (l : LocalLedger p eta heta hcap n hn)
    (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = true ↔
      CoordinatorCollectionLedger.armPending l a := by
  unfold CoordinatorCollectionLedger.armPendingCheck
  unfold CoordinatorCollectionLedger.anyFin
  rw [List.any_eq_true]
  simp [CoordinatorCollectionLedger.armPending]

private theorem armPendingCheck_eq_false_of_empty (l : LocalLedger p eta heta hcap n hn)
    (hpending : l.pending = ∅) (a : Fin p.K) :
    CoordinatorCollectionLedger.armPendingCheck l a = false := by
  cases h : CoordinatorCollectionLedger.armPendingCheck l a with
  | false => rfl
  | true =>
      have hArm : CoordinatorCollectionLedger.armPending l a :=
        (armPendingCheck_eq_true_iff l a).mp h
      rcases hArm with ⟨i, hi, _⟩
      simp [hpending] at hi

theorem cutoffRegister_present (l : LocalLedger p eta heta hcap n hn)
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hpending : l.pending = ∅) (a : Fin p.K) :
    (l.cutoffRegisters a).isSome := by
  have hcheck : CoordinatorCollectionLedger.validLedgerCheck l = true := hvalid
  have hconsistency :
      CoordinatorCollectionLedger.allFin p.K (fun b =>
        (l.cutoffRegisters b).isNone ==
          CoordinatorCollectionLedger.armPendingCheck l b) = true := by
    have h := hcheck
    simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at h
    tauto
  have hentry := (allFin_eq_true_iff _).mp hconsistency a
  have hpendingArm := armPendingCheck_eq_false_of_empty l hpending a
  have hnotNone : (l.cutoffRegisters a).isNone = false := by
    simpa [hpendingArm] using hentry
  cases hregister : l.cutoffRegisters a with
  | none => simp [hregister] at hnotNone
  | some _ => simp

theorem currentRegister_present (l : LocalLedger p eta heta hcap n hn)
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hpending : l.pending = ∅) (a : Fin p.K) :
    (l.currentRegisters a).isSome := by
  have hcheck : CoordinatorCollectionLedger.validLedgerCheck l = true := hvalid
  have hconsistency :
      CoordinatorCollectionLedger.allFin p.K (fun b =>
        (l.currentRegisters b).isNone ==
          CoordinatorCollectionLedger.armPendingCheck l b) = true := by
    have h := hcheck
    simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at h
    tauto
  have hentry := (allFin_eq_true_iff _).mp hconsistency a
  have hpendingArm := armPendingCheck_eq_false_of_empty l hpending a
  have hnotNone : (l.currentRegisters a).isNone = false := by
    simpa [hpendingArm] using hentry
  cases hregister : l.currentRegisters a with
  | none => simp [hregister] at hnotNone
  | some _ => simp

/-- Full actual register vectors extracted from the options in a checked
completed ledger. The equality fields show that each entry is the actual
stored option value; there is no zero/default extraction. -/
structure CompleteRegisters (l : LocalLedger p eta heta hcap n hn) where
  cutoff : Fin p.K → CoordinatorCollectionLedger.CutoffRegister
  current : Fin p.K → CoordinatorCollectionLedger.CurrentRegister
  cutoff_eq : ∀ a, l.cutoffRegisters a = some (cutoff a)
  current_eq : ∀ a, l.currentRegisters a = some (current a)

/-- Extract the actual complete register vectors after the ledger and empty
pending set have proved that every option is present. -/
@[expose] def extractCompleteRegisters (l : LocalLedger p eta heta hcap n hn)
    (hvalid : CoordinatorCollectionLedger.validLedger l)
    (hpending : l.pending = ∅) : CompleteRegisters l where
  cutoff := fun a => Option.get _ (cutoffRegister_present l hvalid hpending a)
  current := fun a => Option.get _ (currentRegister_present l hvalid hpending a)
  cutoff_eq := by
    intro a
    exact (Option.coe_get (cutoffRegister_present l hvalid hpending a)).symm
  current_eq := by
    intro a
    exact (Option.coe_get (currentRegister_present l hvalid hpending a)).symm

/-- The output-domain check for every newly stored current score and queue.
Missing options fail this check as well, though a valid ledger with empty
pending set proves that they are present. -/
@[expose] def currentOutputDomainsCheck (l : LocalLedger p eta heta hcap n hn) : Bool :=
  CoordinatorCollectionLedger.allFin p.K fun a =>
    match l.cutoffRegisters a, l.currentRegisters a with
    | some cutoff, some current =>
        decide (cutoff.score + l.increment a ≤ p.T * ConstructorDimensions.D p) &&
          decide (current.queue ≤ p.T * ConstructorDimensions.D p)
    | _, _ => false

/-- The corrected-only output-domain check for `z(u-1)`. The subtraction is
evaluated only after its required nonnegativity comparison succeeds. Renewal
does not evaluate this vector or its checks. -/
@[expose] def previousOutputDomainsCheck (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p) : Bool :=
  if instruction.time.val + 1 < l.freezeAt then
    CoordinatorCollectionLedger.allFin p.K fun a =>
      match l.cutoffRegisters a with
      | none => false
      | some cutoff =>
          if _hnonnegative : cutoff.lastService ≤ cutoff.score then
            decide (cutoff.score - cutoff.lastService ≤
              p.T * ConstructorDimensions.D p)
          else false
  else true

private theorem currentOutputDomains_bounds (l : LocalLedger p eta heta hcap n hn)
    (hcheck : currentOutputDomainsCheck l = true)
    (registers : CompleteRegisters l) (a : Fin p.K) :
    (registers.cutoff a).score + l.increment a ≤
        p.T * ConstructorDimensions.D p ∧
      (registers.current a).queue ≤ p.T * ConstructorDimensions.D p := by
  have hentry := (allFin_eq_true_iff _).mp hcheck a
  have hpair :
      (decide ((registers.cutoff a).score + l.increment a ≤
          p.T * ConstructorDimensions.D p) &&
        decide ((registers.current a).queue ≤
          p.T * ConstructorDimensions.D p)) = true := by
    simpa [registers.cutoff_eq a, registers.current_eq a] using hentry
  rcases Bool.and_eq_true_iff.mp hpair with ⟨hscore, hqueue⟩
  exact ⟨of_decide_eq_true hscore, of_decide_eq_true hqueue⟩

private theorem previousOutputDomains_nonnegative (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (hcheck : previousOutputDomainsCheck l instruction = true)
    (hcorrected : instruction.time.val + 1 < l.freezeAt)
    (registers : CompleteRegisters l) (a : Fin p.K) :
    (registers.cutoff a).lastService ≤ (registers.cutoff a).score := by
  have hall : CoordinatorCollectionLedger.allFin p.K (fun b =>
      match l.cutoffRegisters b with
      | none => false
      | some cutoff =>
          if _hnonnegative : cutoff.lastService ≤ cutoff.score then
            decide (cutoff.score - cutoff.lastService ≤
              p.T * ConstructorDimensions.D p)
          else false) = true := by
    simpa [previousOutputDomainsCheck, hcorrected] using hcheck
  have hentry := (allFin_eq_true_iff _).mp hall a
  rw [registers.cutoff_eq a] at hentry
  by_cases hnonnegative : (registers.cutoff a).lastService ≤
      (registers.cutoff a).score
  · exact hnonnegative
  · simp [hnonnegative] at hentry

private theorem previousOutputDomains_bound (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (hcheck : previousOutputDomainsCheck l instruction = true)
    (hcorrected : instruction.time.val + 1 < l.freezeAt)
    (registers : CompleteRegisters l) (a : Fin p.K) :
    (registers.cutoff a).score - (registers.cutoff a).lastService ≤
      p.T * ConstructorDimensions.D p := by
  have hall : CoordinatorCollectionLedger.allFin p.K (fun b =>
      match l.cutoffRegisters b with
      | none => false
      | some cutoff =>
          if _hnonnegative : cutoff.lastService ≤ cutoff.score then
            decide (cutoff.score - cutoff.lastService ≤
              p.T * ConstructorDimensions.D p)
          else false) = true := by
    simpa [previousOutputDomainsCheck, hcorrected] using hcheck
  have hentry := (allFin_eq_true_iff _).mp hall a
  rw [registers.cutoff_eq a] at hentry
  have hnonnegative := previousOutputDomains_nonnegative l instruction hcheck
    hcorrected registers a
  simpa [hnonnegative] using hentry

/-- A successful later start contains the full cutoff/current register vectors
and checked domain facts for every numerical value it will expose. -/
structure ReconstructedStart (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p) where
  registers : CompleteRegisters l
  currentScore_le : ∀ a,
    (registers.cutoff a).score + l.increment a ≤ p.T * ConstructorDimensions.D p
  initialQueue_le : ∀ a,
    (registers.current a).queue ≤ p.T * ConstructorDimensions.D p
  previousScore_nonnegative : ∀ a,
    instruction.time.val + 1 < l.freezeAt →
      (registers.cutoff a).lastService ≤ (registers.cutoff a).score
  previousScore_le : ∀ a, instruction.time.val + 1 < l.freezeAt →
    (registers.cutoff a).score - (registers.cutoff a).lastService ≤
      p.T * ConstructorDimensions.D p

variable {l : LocalLedger p eta heta hcap n hn}
variable {instruction : AssignmentStartInstruction p}

/-- The reconstructed source score `z_t = cutoff.score + increment`. -/
@[expose] def sourceScore (out : ReconstructedStart l instruction)
    (a : Fin p.K) : ℕ :=
  (out.registers.cutoff a).score + l.increment a

/-- The new assignment's initial queue, taken from the complete current
register vector in the finished collection ledger. -/
@[expose] def initialQueue (out : ReconstructedStart l instruction)
    (a : Fin p.K) : ℕ :=
  (out.registers.current a).queue

/-- The source weight `w_t = (1 + 1/D) ^ z_t`. -/
@[expose] noncomputable def currentWeight
    (out : ReconstructedStart l instruction)
    (a : Fin p.K) : ℝ :=
  ScoreWeights.scoreWeight (sourceWeightBase p) (sourceScore out a)

/-- The cutoff weight `w_u = (1 + 1/D) ^ cutoff.score`. -/
@[expose] noncomputable def cutoffWeight
    (out : ReconstructedStart l instruction)
    (a : Fin p.K) : ℝ :=
  ScoreWeights.scoreWeight (sourceWeightBase p) (out.registers.cutoff a).score

/-- The preceding-score vector exists only for a corrected same-episode
start. Its subtraction is the literal natural subtraction guarded by the
source nonnegativity check. -/
@[expose] def previousScore (out : ReconstructedStart l instruction) :
    Option (Fin p.K → ℕ) :=
  if instruction.time.val + 1 < l.freezeAt then
    some fun a =>
      (out.registers.cutoff a).score - (out.registers.cutoff a).lastService
  else none

/-- The preceding weight vector is likewise absent on renewal starts. -/
@[expose] noncomputable def previousWeight
    (out : ReconstructedStart l instruction) :
    Option (Fin p.K → ℝ) :=
  (previousScore out).map fun z a =>
    ScoreWeights.scoreWeight (sourceWeightBase p) (z a)

/-- Checked operation failures identify the first local check that failed. -/
inductive Failure where
  | invalidLedger
  | phaseNotReady
  | cursorMismatch
  | collectionPending
  | instructionKindMismatch
  | currentOutputDomain
  | previousOutputDomain
  deriving DecidableEq, Repr

/-- The checked result of one actual later assignment-start call. -/
inductive Result (p : ConstructorDimensions.Parameters) (eta : ℝ)
    (heta : 0 < eta)
    (hcap : CoordinatorCollectionLedger.sourceLearningCap p eta)
    (n : ℕ)
    (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) where
  | success (ledger : LocalLedger p eta heta hcap n hn)
      (instruction : AssignmentStartInstruction p)
      (value : ReconstructedStart ledger instruction)
  | failure (reason : Failure)

/-- Whether a checked result contains a reconstructed state. -/
def isSuccess (result : Result p eta heta hcap n hn) : Bool :=
  match result with
  | .success _ _ _ => true
  | .failure _ => false

/-- The explicit local failure recorded by a checked result. -/
def failureCode (result : Result p eta heta hcap n hn) : Option Failure :=
  match result with
  | .success _ _ _ => none
  | .failure reason => some reason

/-- Run the source's later-start local checks in order and, only after all
input and output checks pass, extract and return the actual numerical state.
Renewal accepts any later cursor relative to the previous freeze boundary. -/
@[expose] def reconstructLaterStart (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p) : Result p eta heta hcap n hn := by
  exact if hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true then
    if hphase : l.phase = .ready then
      if hcursor : l.cursor = instruction.time.val + 1 then
        if hpending : l.pending = ∅ then
          if hkind : instruction.kind = expectedLaterStartKind l.freezeAt instruction.time then
            if hcurrent : currentOutputDomainsCheck l = true then
              if hprevious : previousOutputDomainsCheck l instruction = true then
                .success l instruction {
                  registers := extractCompleteRegisters l hvalid hpending
                  currentScore_le := by
                    intro a
                    exact (currentOutputDomains_bounds l hcurrent
                      (extractCompleteRegisters l hvalid hpending) a).1
                  initialQueue_le := by
                    intro a
                    exact (currentOutputDomains_bounds l hcurrent
                      (extractCompleteRegisters l hvalid hpending) a).2
                  previousScore_nonnegative := by
                    intro a hcorrected
                    exact previousOutputDomains_nonnegative l instruction hprevious
                      hcorrected (extractCompleteRegisters l hvalid hpending) a
                  previousScore_le := by
                    intro a hcorrected
                    exact previousOutputDomains_bound l instruction hprevious
                      hcorrected (extractCompleteRegisters l hvalid hpending) a
                }
              else .failure .previousOutputDomain
            else .failure .currentOutputDomain
          else .failure .instructionKindMismatch
        else .failure .collectionPending
      else .failure .cursorMismatch
    else .failure .phaseNotReady
  else .failure .invalidLedger

/-- Exact success characterization of the checked call. These are the actual
runtime checks; there is no recovery-equality or physical-run premise. -/
theorem reconstructLaterStart_success_iff (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p) :
    isSuccess (reconstructLaterStart l instruction) = true ↔
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = .ready ∧
      l.cursor = instruction.time.val + 1 ∧
      l.pending = ∅ ∧
      instruction.kind = expectedLaterStartKind l.freezeAt instruction.time ∧
      currentOutputDomainsCheck l = true ∧
      previousOutputDomainsCheck l instruction = true := by
  simp only [reconstructLaterStart, isSuccess]
  split_ifs <;> simp_all

/-- Exact first-failure equations for the checked call. -/
def failureCondition (l : LocalLedger p eta heta hcap n hn) (instruction : AssignmentStartInstruction p) :
    Failure → Prop
  | .invalidLedger => CoordinatorCollectionLedger.validLedgerCheck l = false
  | .phaseNotReady =>
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase ≠ .ready
  | .cursorMismatch =>
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase = .ready ∧
        l.cursor ≠ instruction.time.val + 1
  | .collectionPending =>
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase = .ready ∧
        l.cursor = instruction.time.val + 1 ∧ l.pending ≠ ∅
  | .instructionKindMismatch =>
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase = .ready ∧
        l.cursor = instruction.time.val + 1 ∧ l.pending = ∅ ∧
        instruction.kind ≠ expectedLaterStartKind l.freezeAt instruction.time
  | .currentOutputDomain =>
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase = .ready ∧
        l.cursor = instruction.time.val + 1 ∧ l.pending = ∅ ∧
        instruction.kind = expectedLaterStartKind l.freezeAt instruction.time ∧
        currentOutputDomainsCheck l = false
  | .previousOutputDomain =>
      CoordinatorCollectionLedger.validLedgerCheck l = true ∧ l.phase = .ready ∧
        l.cursor = instruction.time.val + 1 ∧ l.pending = ∅ ∧
        instruction.kind = expectedLaterStartKind l.freezeAt instruction.time ∧
        currentOutputDomainsCheck l = true ∧
        previousOutputDomainsCheck l instruction = false

theorem reconstructLaterStart_failure_iff (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p) (failure : Failure) :
    failureCode (reconstructLaterStart l instruction) = some failure ↔
      failureCondition l instruction failure := by
  cases failure <;>
    simp only [failureCondition, failureCode, reconstructLaterStart] <;>
    split_ifs <;> simp_all

/-- Equations for the data returned by an actual successful checked call. -/
theorem reconstructLaterStart_success_equations (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (out : ReconstructedStart l instruction)
    (hcall : reconstructLaterStart l instruction = .success l instruction out) :
    (CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = .ready ∧
      l.cursor = instruction.time.val + 1 ∧
      l.pending = ∅ ∧
      instruction.kind = expectedLaterStartKind l.freezeAt instruction.time ∧
      currentOutputDomainsCheck l = true ∧
      previousOutputDomainsCheck l instruction = true) ∧
    (∀ a, l.cutoffRegisters a = some (out.registers.cutoff a)) ∧
    (∀ a, l.currentRegisters a = some (out.registers.current a)) ∧
    (∀ a, sourceScore out a =
      (out.registers.cutoff a).score + l.increment a) ∧
    (∀ a, initialQueue out a = (out.registers.current a).queue) ∧
    (∀ a, currentWeight out a =
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ sourceScore out a) ∧
    (∀ a, cutoffWeight out a =
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
        (out.registers.cutoff a).score) ∧
    (∀ a, 0 < currentWeight out a) ∧
    (∀ a, 0 < cutoffWeight out a) ∧
    (∀ a, sourceScore out a ≤ p.T * ConstructorDimensions.D p) ∧
    (∀ a, initialQueue out a ≤ p.T * ConstructorDimensions.D p) := by
  have hsuccess : isSuccess (reconstructLaterStart l instruction) = true := by
    rw [hcall]
    rfl
  have hchecks := (reconstructLaterStart_success_iff l instruction).mp hsuccess
  have hbase : 0 < sourceWeightBase p := sourceWeightBase_pos p
  exact ⟨hchecks, out.registers.cutoff_eq, out.registers.current_eq,
    fun _ => rfl, fun _ => rfl, fun _ => by rfl, fun _ => by rfl,
    fun a => ScoreWeights.scoreWeight_pos hbase _,
    fun a => ScoreWeights.scoreWeight_pos hbase _,
    out.currentScore_le, out.initialQueue_le⟩

/-- A successful instruction is corrected exactly on the source's strict
before-freeze comparison. -/
theorem reconstructLaterStart_corrected_iff (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (out : ReconstructedStart l instruction)
    (hcall : reconstructLaterStart l instruction = .success l instruction out) :
    (instruction.kind = .corrected ↔ instruction.time.val + 1 < l.freezeAt) := by
  have hsuccess : isSuccess (reconstructLaterStart l instruction) = true := by
    rw [hcall]
    rfl
  have hchecks := (reconstructLaterStart_success_iff l instruction).mp hsuccess
  rw [hchecks.2.2.2.2.1]
  exact expectedLaterStartKind_eq_corrected_iff l.freezeAt instruction.time

/-- A successful instruction is renewal exactly at or beyond the old
ledger freeze boundary; the operation does not reject a later cursor. -/
theorem reconstructLaterStart_renewal_iff (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (out : ReconstructedStart l instruction)
    (hcall : reconstructLaterStart l instruction = .success l instruction out) :
    (instruction.kind = .renewal ↔ l.freezeAt ≤ instruction.time.val + 1) := by
  have hsuccess : isSuccess (reconstructLaterStart l instruction) = true := by
    rw [hcall]
    rfl
  have hchecks := (reconstructLaterStart_success_iff l instruction).mp hsuccess
  rw [hchecks.2.2.2.2.1]
  exact expectedLaterStartKind_eq_renewal_iff l.freezeAt instruction.time

/-- Corrected starts expose the actual preceding-score vector and its source
weight formula, together with the checked addition identity. -/
theorem reconstructLaterStart_corrected_equations (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (out : ReconstructedStart l instruction)
    (hcall : reconstructLaterStart l instruction = .success l instruction out)
    (hcorrected : instruction.kind = .corrected) :
    previousScore out = some (fun a : Fin p.K =>
      (out.registers.cutoff a).score - (out.registers.cutoff a).lastService) ∧
    (∀ a, (out.registers.cutoff a).score =
      ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService) +
        (out.registers.cutoff a).lastService) ∧
    (∃ weights, previousWeight out = some weights ∧
      ∀ a, weights a = (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
        ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService)) ∧
    (∀ a, 0 < (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
      ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService)) := by
  have hsource := (reconstructLaterStart_corrected_iff l instruction out hcall).mp
    hcorrected
  have hnonnegative := out.previousScore_nonnegative
  have hbase : 0 < (1 + 1 / (ConstructorDimensions.D p : ℝ)) :=
    sourceWeightBase_pos p
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [previousScore, hsource]
  · intro a
    exact (Nat.sub_add_cancel (hnonnegative a hsource)).symm
  · refine ⟨fun a =>
      ScoreWeights.scoreWeight (sourceWeightBase p)
        ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService), ?_, ?_⟩
    · simp [previousWeight, previousScore, hsource]
    · intro a
      rfl
  · intro a
    exact pow_pos hbase _

/-- Renewal preserves the absence of a preceding-score and preceding-weight
vector: neither is evaluated or required on this branch. -/
theorem reconstructLaterStart_renewal_equations (l : LocalLedger p eta heta hcap n hn)
    (instruction : AssignmentStartInstruction p)
    (out : ReconstructedStart l instruction)
    (hcall : reconstructLaterStart l instruction = .success l instruction out)
    (hrenewal : instruction.kind = .renewal) :
    previousScore out = none ∧ previousWeight out = none := by
  have hsource := (reconstructLaterStart_renewal_iff l instruction out hcall).mp
    hrenewal
  simp [previousScore, previousWeight, hsource]

end Bandits.Support.AssignmentScoreReconstruction

end
