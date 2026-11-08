/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# All-known collection clock and checked numerical reconstruction

This internal module constructs the actual empty-pending collection clock,
core, and start instruction, identifies the unchanged actual dispatcher call,
and classifies its checked numerical reconstruction. It retains corrected
underflow and proves the stored weight envelopes. It supplies no assignment
sample, installed replacement, whole-stream existence, physical-score identity,
or manuscript-closure claim. The original-source next-input construction is a
separate campaign owner.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
246-299`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-82`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:97-174,219-243`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceAllKnownCollectionStartDomains

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalStep.State
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput
abbrev Payload {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Payload rate
abbrev Ledger {p : Parameters} (rate : RateInput p) :=
  ReferenceActivePhysicalStep.Ledger rate

variable {p : Parameters} {rate : RateInput p}

private theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
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

private theorem clippedGridSpan_le_episodeHorizon
    (sigma : Fin p.T) (cursor freezeAt : ℕ)
    (hfreeze : freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val sigma) :
    min cursor freezeAt - (sigma.val + 1) ≤
      ReplayWeightStability.episodeHorizon rate.eta.val := by
  let H := ReplayWeightStability.episodeHorizon rate.eta.val
  have hH : 0 < H := by
    exact FollowerCutoffScan.episodeHorizon_pos_of_source_cap p rate.eta.val
      rate.eta.property rate.sourceCap
  have hmod : (sigma.val + 1) % H < H := Nat.mod_lt _ hH
  have hdiv : (sigma.val + 1) % H + H * ((sigma.val + 1) / H) =
      sigma.val + 1 := Nat.mod_add_div _ _
  have hrounded : H * ((sigma.val + 1) / H + 1) ≤ sigma.val + 1 + H := by
    rw [Nat.mul_succ]
    omega
  have hclip : freezeAt ≤ H * ((sigma.val + 1) / H + 1) := by
    rw [hfreeze]
    exact Nat.min_le_right _ _
  dsimp [H] at *
  omega

private theorem source_score_weight_bounds
    (z : ℕ) (hz : z ≤ 4 * rate.n * ReplayWeightStability.episodeHorizon rate.eta.val) :
    1 ≤ ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) z ∧
      ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p) z ≤ 2 := by
  have hD : 0 < (ConstructorDimensions.D p : ℝ) := by
    exact_mod_cast ConstructorDimensions.D_pos p
  have heta : 0 < rate.eta.val := rate.eta.property
  have hnscale : (rate.n : ℝ) = rate.eta.val * (ConstructorDimensions.D p : ℝ) :=
    rate.n_scale
  have hscoreReal : (z : ℝ) ≤
      4 * (rate.n : ℝ) * (ReplayWeightStability.episodeHorizon rate.eta.val : ℝ) :=
    by exact_mod_cast hz
  have hlogBase := ScoreWeightLogBounds.source_base_log_pow_le hD z
  have hlog : Real.log (ScoreWeights.scoreWeight
      (AssignmentScoreReconstruction.sourceWeightBase p) z) ≤ (1 : ℝ) / 16 := by
    change Real.log ((1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ z) ≤ _
    calc
      Real.log ((1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ z) ≤
          (z : ℝ) / (ConstructorDimensions.D p : ℝ) := by
        simpa [ReplayWeightStability.sourceBase,
          AssignmentScoreReconstruction.sourceWeightBase] using hlogBase
      _ ≤ (4 * (rate.n : ℝ) *
          (ReplayWeightStability.episodeHorizon rate.eta.val : ℝ)) /
          (ConstructorDimensions.D p : ℝ) :=
        div_le_div_of_nonneg_right hscoreReal hD.le
      _ = 4 * rate.eta.val *
          (ReplayWeightStability.episodeHorizon rate.eta.val : ℝ) := by
        rw [hnscale]
        field_simp [ne_of_gt hD]
      _ ≤ 4 * rate.eta.val * (1 / (64 * rate.eta.val)) :=
        mul_le_mul_of_nonneg_left
          (ReplayWeightStability.episodeHorizon_cast_le heta) (by positivity)
      _ = (1 : ℝ) / 16 := by
        field_simp [ne_of_gt heta]
        norm_num
  have hpos : 0 < ScoreWeights.scoreWeight
      (AssignmentScoreReconstruction.sourceWeightBase p) z := by
    exact ReplayWeightStability.source_weight_pos
      (D := ConstructorDimensions.D p) (score := z) (ConstructorDimensions.D_pos p)
  have hupper : ScoreWeights.scoreWeight
      (AssignmentScoreReconstruction.sourceWeightBase p) z ≤ 2 := by
    have hlogTwo : Real.log (ScoreWeights.scoreWeight
        (AssignmentScoreReconstruction.sourceWeightBase p) z) ≤ Real.log 2 :=
      hlog.trans ReplayWeightStability.one_sixteenth_lt_log_two.le
    exact (Real.log_le_log_iff hpos (by norm_num)).mp hlogTwo
  have hbase : 1 ≤ AssignmentScoreReconstruction.sourceWeightBase p := by
    unfold AssignmentScoreReconstruction.sourceWeightBase
    exact ScoreWeights.sourceBase_one_le hD
  exact ⟨ScoreWeights.scoreWeight_mono hbase (Nat.zero_le z), hupper⟩

private theorem current_output_domains_of_joint_mass
    {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : AssignmentScoreReconstruction.LocalLedger p eta heta hcap n hn)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hpending : l.pending = ∅)
    (horizon : l.cursor ≤ p.T)
    (hmass : ∀ a c q, l.cutoffRegisters a = some c →
      l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤
        (l.cursor - l.sigma) * ConstructorDimensions.D p) :
    AssignmentScoreReconstruction.currentOutputDomainsCheck l = true := by
  classical
  have hspan : l.cursor - l.sigma ≤ p.T := by omega
  have hspanD : (l.cursor - l.sigma) * ConstructorDimensions.D p ≤
      p.T * ConstructorDimensions.D p := Nat.mul_le_mul_right _ hspan
  unfold AssignmentScoreReconstruction.currentOutputDomainsCheck
  rw [allFin_eq_true_iff]
  intro a
  let registers := AssignmentScoreReconstruction.extractCompleteRegisters l hvalid hpending
  let c := registers.cutoff a
  let q := registers.current a
  have hcut : l.cutoffRegisters a = some c := registers.cutoff_eq a
  have hcur : l.currentRegisters a = some q := registers.current_eq a
  have hjoint := hmass a c q hcut hcur
  have hscore : c.score + l.increment a ≤
      p.T * ConstructorDimensions.D p := by omega
  have hqueue : q.queue ≤ p.T * ConstructorDimensions.D p := by omega
  simp [hcut, hcur, hscore, hqueue]

private theorem previous_output_domains_failure_iff_underflow
    {eta : ℝ} {heta : 0 < eta}
    {hcap : CoordinatorCollectionLedger.sourceLearningCap p eta}
    {n : ℕ} {hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)}
    (l : AssignmentScoreReconstruction.LocalLedger p eta heta hcap n hn)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hpending : l.pending = ∅)
    (horizon : l.cursor ≤ p.T)
    (hmass : ∀ a c q, l.cutoffRegisters a = some c →
      l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤
        (l.cursor - l.sigma) * ConstructorDimensions.D p) :
    AssignmentScoreReconstruction.previousOutputDomainsCheck l instruction = false ↔
      instruction.time.val + 1 < l.freezeAt ∧
        ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService := by
  classical
  let registers := AssignmentScoreReconstruction.extractCompleteRegisters l hvalid hpending
  have hspan : l.cursor - l.sigma ≤ p.T := by omega
  have hspanD : (l.cursor - l.sigma) * ConstructorDimensions.D p ≤
      p.T * ConstructorDimensions.D p := Nat.mul_le_mul_right _ hspan
  have hscore : ∀ a c, l.cutoffRegisters a = some c →
      c.score ≤ p.T * ConstructorDimensions.D p := by
    intro a c hc
    have hcurrent := AssignmentScoreReconstruction.currentRegister_present
      l hvalid hpending a
    obtain ⟨q, hq⟩ : ∃ q, l.currentRegisters a = some q := by
      cases hq : l.currentRegisters a with
      | none => simp [hq] at hcurrent
      | some q => exact ⟨q, rfl⟩
    have h := hmass a c q hc hq
    omega
  have htrue_iff (hcorrected : instruction.time.val + 1 < l.freezeAt) :
      AssignmentScoreReconstruction.previousOutputDomainsCheck l instruction = true ↔
        ¬ ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService := by
    unfold AssignmentScoreReconstruction.previousOutputDomainsCheck
    simp only [hcorrected, ↓reduceIte]
    rw [allFin_eq_true_iff]
    constructor
    · intro hall hex
      rcases hex with ⟨a, c, hc, hunderflow⟩
      have hentry := hall a
      rw [hc] at hentry
      simp [Nat.not_le_of_lt hunderflow] at hentry
    · intro hno a
      let c := (registers.cutoff a)
      have hc : l.cutoffRegisters a = some c := registers.cutoff_eq a
      by_cases hnonnegative : c.lastService ≤ c.score
      · have hbound := hscore a c hc
        have hsub : c.score - c.lastService ≤ p.T * ConstructorDimensions.D p := by omega
        simp [hc, hnonnegative, hsub]
      · have hex : ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService :=
          ⟨a, c, hc, by omega⟩
        exact False.elim (hno hex)
  constructor
  · intro hfalse
    by_cases hcorrected : instruction.time.val + 1 < l.freezeAt
    · have hne :
          AssignmentScoreReconstruction.previousOutputDomainsCheck l instruction ≠ true := by
        simp [hfalse]
      have hnotnot : ¬ ¬ ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService := by
        intro hno
        exact hne ((htrue_iff hcorrected).2 hno)
      exact ⟨hcorrected, Classical.not_not.mp hnotnot⟩
    · unfold AssignmentScoreReconstruction.previousOutputDomainsCheck at hfalse
      simp [hcorrected] at hfalse
  · rintro ⟨hcorrected, a, c, hc, hunderflow⟩
    have hnotTrue :
        AssignmentScoreReconstruction.previousOutputDomainsCheck l instruction ≠ true := by
      intro htrue
      exact (htrue_iff hcorrected).mp htrue ⟨a, c, hc, hunderflow⟩
    exact Bool.eq_false_of_not_eq_true hnotTrue

private theorem empty_collection_core
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool)) (cutoff : Fin p.T)
    (_hstate : x.state.coordinator = .collection payload l saved)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hphase : l.phase = .ready)
    (hsigma : l.sigma = payload.sigma.val + 1)
    (horder : l.sigma < l.cutoff)
    (hcutoffTime : l.cutoff < l.cursor)
    (hcutoff : cutoff.val + 1 = l.cutoff)
    (hcursor : l.cursor = x.time.val + 1)
    (hfreeze : l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hassign : l.assignment.arm = payload.assignment.assigned)
    (hbank : CoordinatorUpReception.decoderBankCheck p x.state.upDecoderBank = true) :
    CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload l
        (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff) := by
  classical
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  have hcutBounds : 1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧
      l.freezeAt ≤ p.T + 1 ∧ l.cutoff ≤ l.cursor := by
    have hcheck := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck,
      Bool.and_eq_true, decide_eq_true_eq] at hcheck
    tauto
  have hparameter : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val :=
    ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have hgridBounds := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
    rate.eta.property rate.sourceCap payload.sigma
  have hfreezeBounds : payload.sigma.val + 1 < l.freezeAt ∧
      l.freezeAt ≤ p.T + 1 := by
    rw [hfreeze]
    exact hgridBounds
  have hcutIndex : payload.sigma.val < cutoff.val := by omega
  have hcutGrid : cutoff.val + 1 ≤ l.freezeAt := by omega
  have hclockValid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock := by
    unfold CoordinatorPhaseClock.clockRegistersValid CoordinatorPhaseClock.boundaryFromSigma
    change l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma ∧
      payload.sigma.val + 1 < l.freezeAt ∧ l.freezeAt ≤ p.T + 1 ∧
      payload.sigma.val < cutoff.val ∧ cutoff.val + 1 ≤ l.freezeAt
    exact ⟨hfreeze, hfreezeBounds.1, hfreezeBounds.2, hcutIndex, hcutGrid⟩
  have htime : CoordinatorPhaseClock.startRoundTimeValid p x.time clock := by
    unfold CoordinatorPhaseClock.startRoundTimeValid
    simp only [clock, ReferenceActivePhysicalStep.collectionClock]
    constructor
    · have hcutTime : l.cutoff ≤ x.time.val := by omega
      omega
    · have hcutTime : l.cutoff ≤ x.time.val := by omega
      omega
  refine {
    payload_n_eq := ReferenceActivePhysicalStep.payload_n_eq payload
    ledger_valid := ?_
    ledger_ready := hphase
    assignment_eq := ?_
    base_score_eq := rfl
    clock_parameter_valid := hparameter
    clock_registers_valid := ?_
    clock_start_time_valid := ?_
    clock_sigma_eq := rfl
    clock_cutoff_eq := rfl
    ledger_sigma_eq := ?_
    ledger_cutoff_eq := ?_
    ledger_freeze_eq := rfl
    ledger_cursor_eq := ?_
    decoder_bank_valid := hbank }
  · change CoordinatorCollectionLedger.validLedgerCheck l = true
    exact hvalid
  · intro i
    exact congrArg (fun f : Fin (p.m - 1) → Fin p.K => f i) hassign
  · exact hclockValid
  · exact htime
  · change l.sigma = CoordinatorRecorderComplementBridge.sourceStart payload
    simpa [CoordinatorRecorderComplementBridge.sourceStart] using hsigma
  · change l.cutoff = CoordinatorCollectionUpRoundStep.sourceCutoff cutoff
    simp [CoordinatorCollectionUpRoundStep.sourceCutoff, hcutoff]
  · change l.cursor = CoordinatorCollectionUpRoundStep.sourceRound x.time
    simpa [CoordinatorCollectionUpRoundStep.sourceRound] using hcursor

private theorem empty_collection_start_data
    (x : RoundInput p rate) (payload : Payload rate) (l : Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (cutoff : Fin p.T) (hcutoff : cutoff.val + 1 = l.cutoff)
    (hstate : x.state.coordinator = .collection payload l saved)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hphase : l.phase = .ready)
    (hsigma : l.sigma = payload.sigma.val + 1)
    (horder : l.sigma < l.cutoff)
    (hcutoffTime : l.cutoff < l.cursor)
    (hcursor : l.cursor = x.time.val + 1)
    (hfreeze : l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hassign : l.assignment.arm = payload.assignment.assigned)
    (hempty : l.pending = ∅)
    (hbank : CoordinatorUpReception.decoderBankCheck p x.state.upDecoderBank = true) :
      let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
      ∃ _core : CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff),
      ∃ started : CoordinatorPhaseClock.StartRoundResult p,
      ∃ _hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock l.pending =
        .ok started,
      ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
      ∃ _hassignment : started.assignmentStart = some instruction,
        instruction.time = x.time := by
  classical
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  have core := empty_collection_core x payload l saved cutoff hstate hvalid hphase
    hsigma horder hcutoffTime hcutoff hcursor hfreeze hassign hbank
  have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have hclock := core.clock_registers_valid
  change CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock at hclock
  have hgridBounds := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
    rate.eta.property rate.sourceCap payload.sigma
  have hgrid : CoordinatorPhaseClock.newGridBoundaryValid p x.time
      (FollowerCutoffScan.gridBoundary p rate.eta.val x.time) := by
    have hb := FollowerCutoffScan.gridBoundary_bounds p rate.eta.val
      rate.eta.property rate.sourceCap x.time
    simpa [CoordinatorPhaseClock.newGridBoundaryValid,
      FollowerCutoffScan.calendarRound] using hb
  have hstartEq := CoordinatorPhaseClock.startRound_collection_empty p rate.eta.val
    x.time payload.sigma cutoff clock hparam hclock rfl rfl (by
      omega) hgrid
  let started : CoordinatorPhaseClock.StartRoundResult p := {
    clock := {
      sigma := some x.time
      u := none
      g := FollowerCutoffScan.gridBoundary p rate.eta.val x.time
      lastProposal := saved }
    gridDomain := hgrid
    pending := Finset.univ
    ledgerCommand := none
    assignmentStart := some ⟨x.time,
      CoordinatorPhaseClock.classifyAssignmentStart clock.sigma x.time clock.g⟩ }
  have hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock l.pending =
      .ok started := by
    rw [hempty]
    simpa [started, clock, ReferenceActivePhysicalStep.collectionClock] using hstartEq
  let instruction : CoordinatorPhaseClock.AssignmentStartInstruction p :=
    ⟨x.time, CoordinatorPhaseClock.classifyAssignmentStart clock.sigma x.time clock.g⟩
  have hassignment : started.assignmentStart = some instruction := rfl
  dsimp only
  exact ⟨core, started, hstart, instruction, hassignment, rfl⟩

/-- Local empty-pending clock/core construction and the actual checked
numerical reconstruction alternatives. Every induction-boundary premise is
explicit. The stored scores are not identified with calendar scores. -/
theorem all_known_collection_reconstruction_cases
    {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload l saved)
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck l = true)
    (hphase : l.phase = .ready)
    (hsigma : l.sigma = payload.sigma.val + 1)
    (horder : l.sigma < l.cutoff)
    (hcutoff : l.cutoff < l.cursor)
    (hcursor : l.cursor = x.time.val + 1)
    (hfreeze : l.freezeAt = FollowerCutoffScan.gridBoundary p rate.eta.val payload.sigma)
    (hassign : l.assignment.arm = payload.assignment.assigned)
    (hempty : l.pending = ∅)
    (hanchor : ∀ a, payload.anchor a = 1)
    (hmass : ∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a + q.queue ≤
        (l.cursor - l.sigma) * ConstructorDimensions.D p)
    (hservice : ∀ a c q, l.cutoffRegisters a = some c → l.currentRegisters a = some q →
      c.score + l.increment a ≤
        4 * rate.n * (min l.cursor l.freezeAt - l.sigma))
    (hbank : CoordinatorUpReception.decoderBankCheck p x.state.upDecoderBank = true) :
    ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
      let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
      let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
      ∃ core : CoordinatorRoundDispatch.CollectionCoreValid input,
      ∃ started : CoordinatorPhaseClock.StartRoundResult p,
      ∃ _hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock l.pending = .ok started,
      ∃ instruction : CoordinatorPhaseClock.AssignmentStartInstruction p,
      ∃ _hassignment : started.assignmentStart = some instruction,
      let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
      ∃ _consistent : LaterAssignmentStartOperation.LocalConsistency input.payload operationLedger,
      instruction.time = x.time ∧
      instruction.kind = AssignmentScoreReconstruction.expectedLaterStartKind
        operationLedger.freezeAt instruction.time ∧
      (ReferenceActivePhysicalStep.prepare x).coordinator =
        .collection payload l clock cutoff (CoordinatorRoundDispatch.dispatchCollection input) ∧
      AssignmentScoreReconstruction.currentOutputDomainsCheck operationLedger = true ∧
      (AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .failure .previousOutputDomain ↔
        instruction.time.val + 1 < l.freezeAt ∧
          ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService) ∧
      ((AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .failure .previousOutputDomain ∧ instruction.kind = .corrected ∧
          ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService) ∨
        ∃ out : AssignmentScoreReconstruction.ReconstructedStart operationLedger instruction,
        ∃ _hrec : AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .success operationLedger instruction out,
        (∀ a, operationLedger.cutoffRegisters a = some (out.registers.cutoff a)) ∧
        (∀ a, operationLedger.currentRegisters a = some (out.registers.current a)) ∧
        (∀ a, AssignmentScoreReconstruction.sourceScore out a =
          (out.registers.cutoff a).score + operationLedger.increment a) ∧
        (∀ a, AssignmentScoreReconstruction.initialQueue out a = (out.registers.current a).queue) ∧
        (∀ a, AssignmentScoreReconstruction.currentWeight out a =
          (1 + 1 / (D p : ℝ)) ^ AssignmentScoreReconstruction.sourceScore out a) ∧
        (∀ a, AssignmentScoreReconstruction.cutoffWeight out a =
          (1 + 1 / (D p : ℝ)) ^ (out.registers.cutoff a).score) ∧
        (∀ a, 1 ≤ AssignmentScoreReconstruction.currentWeight out a ∧
          AssignmentScoreReconstruction.currentWeight out a ≤ 2) ∧
        (∀ a, 1 ≤ AssignmentScoreReconstruction.cutoffWeight out a ∧
          AssignmentScoreReconstruction.cutoffWeight out a ≤ 2) ∧
        (∀ a, payload.anchor a ≤ AssignmentScoreReconstruction.currentWeight out a ∧
          AssignmentScoreReconstruction.currentWeight out a ≤ 2 * payload.anchor a) ∧
        (instruction.kind = .corrected →
          AssignmentScoreReconstruction.previousScore out = some (fun a =>
            (out.registers.cutoff a).score - (out.registers.cutoff a).lastService) ∧
          (∀ a, (out.registers.cutoff a).lastService ≤ (out.registers.cutoff a).score) ∧
          ∃ previous, AssignmentScoreReconstruction.previousWeight out = some previous ∧
            (∀ a, previous a = (1 + 1 / (D p : ℝ)) ^
              ((out.registers.cutoff a).score - (out.registers.cutoff a).lastService)) ∧
            (∀ a, 1 ≤ previous a ∧ previous a ≤ 2)) ∧
        (instruction.kind = .renewal →
          AssignmentScoreReconstruction.previousScore out = none ∧
          AssignmentScoreReconstruction.previousWeight out = none)) ∧
      (instruction.kind = .renewal →
        ∃ out, AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .success operationLedger instruction out) := by
  classical
  have hcutDomain : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    have hv := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    tauto
  have hcutoff_lt : l.cutoff - 1 < p.T := by
    have hcutTime : l.cutoff ≤ x.time.val := by omega
    omega
  let cutoff : Fin p.T := ⟨l.cutoff - 1, hcutoff_lt⟩
  have hcutoffFin : cutoff.val + 1 = l.cutoff := by
    dsimp [cutoff]
    omega
  have hsetup := empty_collection_start_data x payload l saved cutoff hcutoffFin
    hstate hvalid hphase hsigma horder hcutoff hcursor hfreeze hassign hempty hbank
  dsimp only at hsetup
  rcases hsetup with ⟨core, started, hstart, instruction,
    hassignment, hinstructionTime⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  let operationLedger :=
    CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq
  let consistent : LaterAssignmentStartOperation.LocalConsistency input.payload
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq) := {
    oldStart_eq := by
      simpa [input, ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRoundDispatch.collectionOperationLedger,
        CoordinatorRecorderComplementBridge.sourceStart] using hsigma.symm
    oldAssignment_eq := by
      intro i
      simpa [input, ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRoundDispatch.collectionOperationLedger] using
        congrArg (fun f : Fin (p.m - 1) → Fin p.K => f i) hassign.symm
    oldFreezeAt := input.ledger.freezeAt
    oldFreezeAt_eq := rfl }
  let outcome := CoordinatorRoundDispatch.dispatchCollection input
  have hprepared : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload l clock cutoff outcome := by
    change ReferenceActivePhysicalStep.dispatch x = _
    unfold ReferenceActivePhysicalStep.dispatch
    rw [hstate]
    simp only [dite_eq_left hcutDomain]
    rfl
  have hcutBounds : 1 ≤ l.cutoff ∧ l.cutoff ≤ l.freezeAt ∧
      l.freezeAt ≤ p.T + 1 ∧ l.cutoff ≤ l.cursor := by
    have hv := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck,
      Bool.and_eq_true, decide_eq_true_eq] at hv
    tauto
  have hcursorHorizon : l.cursor ≤ p.T := by omega
  have hcurrent := current_output_domains_of_joint_mass operationLedger hvalid hempty
    (by change l.cursor ≤ p.T; exact hcursorHorizon) (by
      intro a c q hc hq
      change l.cutoffRegisters a = some c at hc
      change l.currentRegisters a = some q at hq
      simpa only [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger, input,
        ReferenceActivePhysicalStep.collectionInput] using hmass a c q hc hq)
  have hstartEq : CoordinatorPhaseClock.startRound p input.etaReal input.time input.clock
      input.ledger.pending = .ok started := by
    simpa [input, ReferenceActivePhysicalStep.collectionInput] using hstart
  have hstartEffects := CoordinatorPhaseClock.startRound_assignment_effect p input.etaReal
    input.time input.clock input.ledger.pending started instruction
    core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid
    hstartEq hassignment
  rcases hstartEffects with ⟨htime, hkind, _, _, _, _, _, _⟩
  have hkindExpected : instruction.kind =
      AssignmentScoreReconstruction.expectedLaterStartKind operationLedger.freezeAt
        instruction.time := by
    rw [htime]
    by_cases hb : x.time.val + 1 < l.freezeAt
    all_goals
      simp only [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger, input,
        ReferenceActivePhysicalStep.collectionInput, clock,
        ReferenceActivePhysicalStep.collectionClock] at *
      simpa [CoordinatorPhaseClock.classifyAssignmentStart,
      AssignmentScoreReconstruction.expectedLaterStartKind,
      FollowerCutoffScan.calendarRound,
      CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput, hb, Nat.not_le_of_lt,
      Nat.le_of_not_gt] using hkind
  have hvalidOp : CoordinatorCollectionLedger.validLedgerCheck operationLedger = true := by
    simpa only [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput, CoordinatorCollectionLedger.validLedgerCheck,
      CoordinatorCollectionLedger.readyHistoryCheck, CoordinatorCollectionLedger.startedHistoryCheck,
      CoordinatorCollectionLedger.armPendingCheck, CoordinatorCollectionLedger.registerDomainsCheck,
      CoordinatorCollectionLedger.rawEntryDomainsCheck] using hvalid
  have hphaseOp : operationLedger.phase = .ready := by
    simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput] using hphase
  have hcursorOp : operationLedger.cursor = instruction.time.val + 1 := by
    simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput, htime] using hcursor
  have hpendingOp : operationLedger.pending = ∅ := by
    simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger, input,
      ReferenceActivePhysicalStep.collectionInput] using hempty
  have hfailureCheck :
      AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
        .failure .previousOutputDomain ↔
      AssignmentScoreReconstruction.previousOutputDomainsCheck operationLedger instruction = false := by
    unfold AssignmentScoreReconstruction.reconstructLaterStart
    simp only [dite_eq_left hvalidOp, dite_eq_left hphaseOp, dite_eq_left hcursorOp,
      dite_eq_left hpendingOp, dite_eq_left hkindExpected, dite_eq_left hcurrent]
    by_cases hprevious : AssignmentScoreReconstruction.previousOutputDomainsCheck
        operationLedger instruction = true
    · simp only [hprevious, ↓reduceDIte, reduceCtorEq, Bool.true_eq_false]
    · simp only [dite_eq_right hprevious, true_iff]
      exact Bool.eq_false_of_not_eq_true hprevious
  have hfailure :
      AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
          .failure .previousOutputDomain ↔
        instruction.time.val + 1 < l.freezeAt ∧
          ∃ a c, l.cutoffRegisters a = some c ∧ c.score < c.lastService := by
    rw [hfailureCheck]
    have h := previous_output_domains_failure_iff_underflow operationLedger instruction
      hvalidOp hpendingOp hcursorHorizon (by
        intro a c q hc hq
        simpa only [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
          input, ReferenceActivePhysicalStep.collectionInput] using hmass a c q hc hq)
    simpa only [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
      input, ReferenceActivePhysicalStep.collectionInput] using h
  have hrenewal : instruction.kind = .renewal →
      ∃ out, AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
        .success operationLedger instruction out := by
    intro hk
    have hbefore : ¬ instruction.time.val + 1 < operationLedger.freezeAt := by
      rw [hkindExpected] at hk
      exact Nat.not_lt.mpr
        ((AssignmentScoreReconstruction.expectedLaterStartKind_eq_renewal_iff _ _).mp hk)
    have hprevious : AssignmentScoreReconstruction.previousOutputDomainsCheck
        operationLedger instruction = true := by
      simp only [AssignmentScoreReconstruction.previousOutputDomainsCheck, hbefore, ↓reduceIte]
    unfold AssignmentScoreReconstruction.reconstructLaterStart
    simp only [dite_eq_left hvalidOp, dite_eq_left hphaseOp, dite_eq_left hcursorOp,
      dite_eq_left hpendingOp, dite_eq_left hkindExpected, dite_eq_left hcurrent,
      dite_eq_left hprevious]
    exact ⟨_, rfl⟩
  refine ⟨cutoff, hcutoffFin, ?_⟩
  dsimp only
  refine ⟨core, started, hstart, instruction, hassignment, consistent,
    hinstructionTime, hkindExpected, hprepared, hcurrent, hfailure, ?_, hrenewal⟩
  by_cases hprevious : AssignmentScoreReconstruction.previousOutputDomainsCheck
      operationLedger instruction = true
  · have hexists : ∃ out, AssignmentScoreReconstruction.reconstructLaterStart
        operationLedger instruction = .success operationLedger instruction out := by
      unfold AssignmentScoreReconstruction.reconstructLaterStart
      simp only [dite_eq_left hvalidOp, dite_eq_left hphaseOp, dite_eq_left hcursorOp,
        dite_eq_left hpendingOp, dite_eq_left hkindExpected, dite_eq_left hcurrent,
        dite_eq_left hprevious]
      exact ⟨_, rfl⟩
    obtain ⟨out, hrec⟩ := hexists
    have he := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      operationLedger instruction out hrec
    have hscoreBound (a : Fin p.K) : AssignmentScoreReconstruction.sourceScore out a ≤
        4 * rate.n * ReplayWeightStability.episodeHorizon rate.eta.val := by
      have hz := hservice a (out.registers.cutoff a) (out.registers.current a)
        (out.registers.cutoff_eq a) (out.registers.current_eq a)
      have hspan := clippedGridSpan_le_episodeHorizon payload.sigma l.cursor l.freezeAt hfreeze
      rw [← hsigma] at hspan
      change (out.registers.cutoff a).score + l.increment a ≤ _
      exact hz.trans (Nat.mul_le_mul_left _ hspan)
    have hcurrentBounds (a : Fin p.K) :
        1 ≤ AssignmentScoreReconstruction.currentWeight out a ∧
          AssignmentScoreReconstruction.currentWeight out a ≤ 2 :=
      source_score_weight_bounds _ (hscoreBound a)
    have hcutoffBounds (a : Fin p.K) :
        1 ≤ AssignmentScoreReconstruction.cutoffWeight out a ∧
          AssignmentScoreReconstruction.cutoffWeight out a ≤ 2 :=
      source_score_weight_bounds (out.registers.cutoff a).score
        ((Nat.le_add_right _ _).trans (hscoreBound a))
    refine Or.inr ⟨out, hrec, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2.1,
      he.2.2.2.2.2.1, he.2.2.2.2.2.2.1, hcurrentBounds, hcutoffBounds, ?_, ?_, ?_⟩
    · intro a
      rw [hanchor a]
      simpa only [mul_one] using hcurrentBounds a
    · intro hk
      have hc := AssignmentScoreReconstruction.reconstructLaterStart_corrected_equations
        operationLedger instruction out hrec hk
      obtain ⟨previous, hpreviousEq, hpower⟩ := hc.2.2.1
      have hbefore := (AssignmentScoreReconstruction.reconstructLaterStart_corrected_iff
        operationLedger instruction out hrec).mp hk
      refine ⟨hc.1, fun a => out.previousScore_nonnegative a hbefore,
        previous, hpreviousEq, hpower, ?_⟩
      intro a
      rw [hpower a]
      exact source_score_weight_bounds _
        ((Nat.sub_le _ _).trans ((Nat.le_add_right _ _).trans (hscoreBound a)))
    · exact fun hk => AssignmentScoreReconstruction.reconstructLaterStart_renewal_equations
        operationLedger instruction out hrec hk
  · have hfailed := hfailureCheck.mpr (Bool.eq_false_of_not_eq_true hprevious)
    have hunderflow := hfailure.mp hfailed
    have hk : instruction.kind = .corrected := by
      rw [hkindExpected]
      apply (AssignmentScoreReconstruction.expectedLaterStartKind_eq_corrected_iff _ _).2
      simpa only [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
        input, ReferenceActivePhysicalStep.collectionInput] using hunderflow.1
    exact Or.inl ⟨hfailed, hk, hunderflow.2⟩

end Bandits.Support.ReferenceAllKnownCollectionStartDomains

end
