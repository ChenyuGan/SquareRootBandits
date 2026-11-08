/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence
public import Bandits.Support.ReferenceFirstComplementMassBudget
public import Bandits.Support.ReferenceFirstCutoffOutsideInitialization

/-!
# Actual first-cutoff recorded collection service

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:246-295`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module follows one actual first chosen cutoff in the original physical
run, uses its actual recorder call and its initialized outside registers, and
proves the checked collection stage-(1) update succeeds. It makes no claim
about the later UP reception, finish, clock, follower behavior, or regret.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceFirstCutoffRecordedService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev State := ReferenceActivePhysicalHorizon.State
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

variable {p : Parameters} {rate : RateInput p}

private theorem rawSlotFreshCheck_round_congr
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    {left right : Fin p.T} (h : left = right)
    (raw : Option (Fin p.K × ℕ)) :
    CoordinatorCollectionLedger.rawSlotFreshCheck ledger left raw =
      CoordinatorCollectionLedger.rawSlotFreshCheck ledger right raw := by
  cases h
  rfl

private theorem startRoundCandidate_round_congr
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    {left right : Fin p.T} (h : left = right) (enabled : Bool)
    (raw : Option (Fin p.K × ℕ)) :
    CoordinatorCollectionLedger.startRoundCandidate ledger left enabled raw =
      CoordinatorCollectionLedger.startRoundCandidate ledger right enabled raw := by
  cases h
  rfl

private theorem startRound_success_of_owned_checks
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (time : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (hvalid : CoordinatorCollectionLedger.validLedgerCheck ledger = true)
    (hready : ledger.phase = .ready)
    (hcursor : ledger.cursor = time.val + 1)
    (hraw : CoordinatorCollectionLedger.rawInputDomainCheck raw = true)
    (hslot : CoordinatorCollectionLedger.rawSlotFreshCheck ledger time raw = true)
    (hcandidate : CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) = true) :
    CoordinatorCollectionLedger.startRound ledger (time.val + 1) enabled raw =
      .success (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) := by
  have hinput : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .ready ∧ time.val + 1 = ledger.cursor ∧
      1 ≤ time.val + 1 ∧ time.val + 1 ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true := by
    exact ⟨hvalid, hready, hcursor.symm, by omega,
      Nat.succ_le_of_lt time.isLt, hraw⟩
  have hr : (⟨(time.val + 1) - 1, by omega⟩ : Fin p.T) = time := by
    apply Fin.ext
    simp
  unfold CoordinatorCollectionLedger.startRound
  rw [dif_pos hinput]
  have hslot' : CoordinatorCollectionLedger.rawSlotFreshCheck ledger
      ⟨(time.val + 1) - 1, by omega⟩ raw = true :=
    (rawSlotFreshCheck_round_congr ledger hr raw).trans hslot
  rw [if_pos hslot']
  have hcand : CoordinatorCollectionLedger.startRoundCandidate ledger
      ⟨(time.val + 1) - 1, by omega⟩ enabled raw =
        CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw :=
    startRoundCandidate_round_congr ledger hr enabled raw
  rw [hcand, if_pos hcandidate]

/-- The finite checker used by the existing ledger is exactly a universal
check over its original `Fin` carrier. -/
theorem allFin_eq_true_iff {length : ℕ} (test : Fin length → Bool) :
    CoordinatorCollectionLedger.allFin length test = true ↔ ∀ i, test i = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  constructor
  · intro hall i
    exact hall (test i) (by simp)
  · intro hall value hvalue
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hvalue
    subst value
    exact hall i

/-- A checked initial ledger records the exact agreement between unknown
registers and assigned pending arms. This field is preserved by stage (1). -/
theorem validLedger_pendingChecks
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (hvalid : CoordinatorCollectionLedger.validLedger ledger) :
    (∀ a, (ledger.currentRegisters a).isNone =
        CoordinatorCollectionLedger.armPendingCheck ledger a) ∧
      (∀ a, (ledger.cutoffRegisters a).isNone =
        CoordinatorCollectionLedger.armPendingCheck ledger a) := by
  have hcheck : CoordinatorCollectionLedger.validLedgerCheck ledger = true := hvalid
  simp only [CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true] at hcheck
  have hcurrent := hcheck.1.1.1.1.1.2
  have hcutoff := hcheck.1.1.1.1.2
  constructor
  · intro a
    have h := (allFin_eq_true_iff _).1 hcurrent a
    cases hleft : (ledger.currentRegisters a).isNone <;>
      cases hright : CoordinatorCollectionLedger.armPendingCheck ledger a <;>
      simp_all
  · intro a
    have h := (allFin_eq_true_iff _).1 hcutoff a
    cases hleft : (ledger.cutoffRegisters a).isNone <;>
      cases hright : CoordinatorCollectionLedger.armPendingCheck ledger a <;>
      simp_all

private theorem executeValid_total_of_owned
    (input : CoordinatorRecordingOperation.Input p)
    (hvalid : CoordinatorRecordingOperation.InputsValid input)
    (howns : CoordinatorRecordingOperation.ownsArm input.mode input.ownArm) :
    ∃ output, CoordinatorRecordingOperation.executeValid input hvalid = some output := by
  classical
  by_cases hdata : CoordinatorRecordingOperation.selectedSlot input = PublicDiscreteDraws.dataSlot
  · by_cases hsource : CoordinatorRecordingOperation.selectedRecorder input =
        ActiveRoundActions.coordinator p.two_le_m
    · by_cases hfrozen : CoordinatorRecordingOperation.isFrozen input
      · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
          CoordinatorRecordingOperation.executeValid_zero_of_frozen input hvalid
            hdata hsource hfrozen⟩
      · by_cases howns' : CoordinatorRecordingOperation.ownsArm input.mode input.ownArm
        · by_cases hmask : CoordinatorRecordingOperation.ownMaskPasses input
          · let hmass := CoordinatorRecordingOperation.rawGateMass_feasible input hvalid howns'
            let hthreshold :=
              CoordinatorRecordingOperation.coordinatorThreshold_mem_Icc_of_owned
                input hvalid howns'
            let hfloor := CoordinatorRecordingOperation.floorArrival_le_D input hvalid
            by_cases hthin :
                (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                  (ContinuousLearningRows.sliceAt input.time input.row.2)).val ≤
                  CoordinatorRecordingOperation.coordinatorThreshold input hvalid
            · exact ⟨⟨some input.ownArm,
                  CoordinatorRecordingOperation.floorArrival input, hfloor⟩,
                CoordinatorRecordingOperation.executeValid_recorded_of_gate input hvalid
                  hdata hsource hfrozen howns' hmask hthin⟩
            · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
                CoordinatorRecordingOperation.executeValid_zero_of_thinning_rejected
                  input hvalid hdata hsource hfrozen howns' hmask hthin⟩
          · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
              CoordinatorRecordingOperation.executeValid_zero_of_mask_rejected input hvalid
                hdata hsource hfrozen howns' hmask⟩
        · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
            CoordinatorRecordingOperation.executeValid_zero_of_unowned input hvalid
              hdata hsource hfrozen howns'⟩
    · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
        CoordinatorRecordingOperation.executeValid_zero_of_other_source input hvalid
          hdata hsource⟩
  · exact ⟨CoordinatorRecordingOperation.zeroOutput p,
      CoordinatorRecordingOperation.executeValid_zero_of_not_data input hvalid hdata⟩

/-- The actual checked recorder is total on a valid collection input. The
output retains a successful gate even when its integer floor is zero. -/
private theorem recorder_run_total_of_collection
    {payload : Bandits.Support.AssignmentStartPayload.Input p rate.eta}
    (input : CoordinatorRecorderComplementBridge.Input payload)
    (hlocal : CoordinatorRecorderComplementBridge.LocalInputsValid input)
    (hcollection : input.mode = .collection) :
    ∃ output, CoordinatorRecorderComplementBridge.run input = some output := by
  let accepted := CoordinatorRecorderComplementBridge.recorderInput input
  have hvalid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input hlocal
  have hmode : (CoordinatorRecordingOperation.Input.mode accepted) = .collection := by
    simp [accepted, CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecorderComplementBridge.operationMode, hcollection]
  have howns : CoordinatorRecordingOperation.ownsArm accepted.mode accepted.ownArm := by
    rw [hmode]
    trivial
  obtain ⟨output, hrun⟩ := executeValid_total_of_owned accepted hvalid howns
  have hbridge := CoordinatorRecorderComplementBridge.run_eq_executeValid input hlocal
  refine ⟨output, ?_⟩
  rw [hbridge]
  exact hrun

private theorem output_rawInput_domain
    (output : CoordinatorRecordingOperation.Output p) :
    CoordinatorCollectionLedger.rawInputDomainCheck
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output) = true := by
  cases hgate : output.gateArm with
  | none => simp [hgate, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
      CoordinatorCollectionLedger.rawInputDomainCheck]
  | some arm =>
      simp [hgate, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
        CoordinatorCollectionLedger.rawInputDomainCheck, output.rawArrival_le_D]

/-- The active raw arrival is bounded by the existing mass bound plus one
actual recorder output. This lemma is used only for the literal candidate's
known-register domains. -/
private theorem queueTransition_domains
    (capacity queue : ℕ) (record : Bool × ℕ)
    (harrival : record.2 ≤ ConstructorDimensions.D p)
    (hcapacity : capacity ≤ ConstructorDimensions.D p) :
    (QueueReplay.transition capacity (0, queue) record).1 ≤
        ConstructorDimensions.D p ∧
      (QueueReplay.transition capacity (0, queue) record).2 ≤
        queue + record.2 := by
  cases record with
  | mk active value =>
      cases active with
      | false => simp [QueueReplay.transition]
      | true =>
          simp only [QueueReplay.transition, if_pos, zero_add]
          constructor
          · exact (Nat.min_le_left _ _).trans hcapacity
          · exact Nat.sub_le _ _

private theorem queueTransition_service_le_capacity
    (capacity queue : ℕ) (record : Bool × ℕ) :
    (QueueReplay.transition capacity (0, queue) record).1 ≤ capacity := by
  cases record with
  | mk active value =>
      cases active <;> simp [QueueReplay.transition]

/-- A cutoff initializer with the real prefix mass, one bounded actual
arrival, and an empty raw buffer has a valid literal stage-(1) candidate.
All queue changes are the existing `QueueReplay.transition` equations. -/
private theorem cutoffCandidate_valid
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      rate.sourceCap rate.n rate.n_scale)
    (time : Fin p.T) (enabled : Bool) (raw : Option (Fin p.K × ℕ)) (k : ℕ)
    (hvalid : CoordinatorCollectionLedger.validLedger ledger)
    (hsigmaPos : 1 ≤ ledger.sigma) (hsigmaT : ledger.sigma ≤ p.T)
    (hcutoffPos : 1 ≤ ledger.cutoff) (hcutoffFreeze : ledger.cutoff ≤ ledger.freezeAt)
    (hfreeze : ledger.freezeAt ≤ p.T + 1) (hcutoffT : ledger.cutoff ≤ p.T)
    (hcutoff : ledger.cutoff = time.val + 1)
    (hcursor : ledger.cursor = time.val + 1)
    (hphase : ledger.phase = .ready)
    (hbase : ∀ i, ledger.baseScore i ≤ p.T * D p)
    (hincrement : ledger.increment = fun _ => 0)
    (hrawBuffer : ledger.rawBuffer = fun _ _ => none)
    (henabledHistory : ledger.enabledHistory = fun _ => none)
    (hgamma : ledger.gammaLoc = fun _ => 0)
    (hcurrentQueue : ∀ a current, ledger.currentRegisters a = some current →
      current.queue ≤ k * D p)
    (hcutoffMass : ∀ a current, ledger.cutoffRegisters a = some current →
      current.score + current.queue ≤ k * D p ∧ current.lastService ≤ D p)
    (harrival : match raw with
      | none => True
      | some (_, amount) => amount ≤ D p)
    (hk : k + 1 ≤ p.T)
    (hcapacity : 4 * rate.n ≤ D p) :
    CoordinatorCollectionLedger.validLedgerCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) = true := by
  classical
  let candidate := CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw
  have hpending := validLedger_pendingChecks ledger hvalid
  have htime : time.val + 1 ≤ p.T := Nat.succ_le_of_lt time.isLt
  have hsource : CoordinatorCollectionLedger.sourceRound time = time.val + 1 := rfl
  have hcurrentPending : ∀ a,
      (candidate.currentRegisters a).isNone =
        CoordinatorCollectionLedger.armPendingCheck candidate a := by
    intro a
    have hsame :
        CoordinatorCollectionLedger.armPendingCheck candidate a =
          CoordinatorCollectionLedger.armPendingCheck ledger a := by
      simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
        CoordinatorCollectionLedger.armPendingCheck]
    rw [hsame]
    cases hknown : ledger.currentRegisters a with
    | none =>
        have hp : CoordinatorCollectionLedger.armPendingCheck ledger a = true := by
          simpa [hknown] using (hpending.1 a).symm
        simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown] using hp.symm
    | some current =>
        have hp : CoordinatorCollectionLedger.armPendingCheck ledger a = false := by
          simpa [hknown] using (hpending.1 a).symm
        simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown] using hp.symm
  have hcutoffPending : ∀ a,
      (candidate.cutoffRegisters a).isNone =
        CoordinatorCollectionLedger.armPendingCheck candidate a := by
    intro a
    have hsame :
        CoordinatorCollectionLedger.armPendingCheck candidate a =
          CoordinatorCollectionLedger.armPendingCheck ledger a := by
      simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
        CoordinatorCollectionLedger.armPendingCheck]
    rw [hsame]
    simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate] using hpending.2 a
  have hstartedHistory :
      CoordinatorCollectionLedger.startedHistoryCheck candidate = true := by
    apply (allFin_eq_true_iff _).2
    intro t
    by_cases heq : t = time
    · subst t
      simp [candidate, CoordinatorCollectionLedger.startedHistoryCheck,
        CoordinatorCollectionLedger.startRoundCandidate, henabledHistory,
        CoordinatorCollectionLedger.sourceRound, hcutoff, hcursor]
    · have hround : CoordinatorCollectionLedger.sourceRound t ≠
          CoordinatorCollectionLedger.sourceRound time := by
        intro hequal
        apply heq
        apply Fin.ext
        dsimp [CoordinatorCollectionLedger.sourceRound] at hequal
        omega
      by_cases hlt : CoordinatorCollectionLedger.sourceRound t < ledger.cutoff
      · simp [candidate, CoordinatorCollectionLedger.startedHistoryCheck,
          CoordinatorCollectionLedger.startRoundCandidate, henabledHistory,
          hlt]
      · have hnotCursor : ¬ CoordinatorCollectionLedger.sourceRound t ≤
            CoordinatorCollectionLedger.sourceRound time := by
          have hle : CoordinatorCollectionLedger.sourceRound time ≤
              CoordinatorCollectionLedger.sourceRound t := by
            apply Nat.le_of_not_gt
            simpa [hcutoff, CoordinatorCollectionLedger.sourceRound] using hlt
          intro hle'
          exact hround (Nat.le_antisymm hle' hle)
        simp [candidate, CoordinatorCollectionLedger.startedHistoryCheck,
          CoordinatorCollectionLedger.startRoundCandidate, henabledHistory,
          hlt, hnotCursor, heq]
  have hcurrentDomains : ∀ a,
      match candidate.currentRegisters a with
      | none => True
      | some current => current.queue ≤ p.T * D p ∧ current.lastService ≤ D p := by
    intro a
    cases hknown : ledger.currentRegisters a with
    | none => simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown]
    | some current =>
        have hqueue := hcurrentQueue a current hknown
        have harrivalLocal :
            CoordinatorCollectionLedger.localArrival raw a ≤ D p := by
          cases raw with
          | none => simp [CoordinatorCollectionLedger.localArrival]
          | some pair =>
              rcases pair with ⟨b, amount⟩
              by_cases hba : b = a
              · subst b
                simpa [CoordinatorCollectionLedger.localArrival] using harrival
              · simp [CoordinatorCollectionLedger.localArrival, hba]
        have hrecordBound :
            (CoordinatorCollectionLedger.localQueueRecord ledger time enabled raw a).2 ≤ D p := by
          unfold CoordinatorCollectionLedger.localQueueRecord
          split
          · exact harrivalLocal
          · simp
        have htransition := queueTransition_domains (4 * rate.n) current.queue
          (CoordinatorCollectionLedger.localQueueRecord ledger time enabled raw a)
          hrecordBound hcapacity
        simp only [candidate, CoordinatorCollectionLedger.startRoundCandidate,
          hknown]
        exact ⟨by
          exact (htransition.2.trans (by nlinarith [hqueue, hk])).trans
            (Nat.mul_le_mul_right (D p) hk), htransition.1⟩
  have hcutoffDomains : ∀ a,
      match candidate.cutoffRegisters a with
      | none => True
      | some current => current.score ≤ p.T * D p ∧ current.queue ≤ p.T * D p ∧
          current.lastService ≤ D p := by
    intro a
    cases hknown : ledger.cutoffRegisters a with
    | none => simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown]
    | some current =>
        have hm := hcutoffMass a current hknown
        have hkT : k * D p ≤ p.T * D p := Nat.mul_le_mul_right (D p) (by omega)
        simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown]
        omega
  have hgammaDomain : ∀ a, candidate.gammaLoc a ≤ D p := by
    intro a
    cases hknown : ledger.currentRegisters a with
    | none => simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown]
    | some current =>
        have harrivalLocal :
            CoordinatorCollectionLedger.localArrival raw a ≤ D p := by
          cases raw with
          | none => simp [CoordinatorCollectionLedger.localArrival]
          | some pair =>
              rcases pair with ⟨b, amount⟩
              by_cases hba : b = a
              · subst b
                simpa [CoordinatorCollectionLedger.localArrival] using harrival
              · simp [CoordinatorCollectionLedger.localArrival, hba]
        have hrecordBound :
            (CoordinatorCollectionLedger.localQueueRecord ledger time enabled raw a).2 ≤ D p := by
          unfold CoordinatorCollectionLedger.localQueueRecord
          split
          · exact harrivalLocal
          · simp
        have htransition := queueTransition_domains (4 * rate.n) current.queue
          (CoordinatorCollectionLedger.localQueueRecord ledger time enabled raw a)
          hrecordBound hcapacity
        simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown] using
          htransition.1
  have hrawEntries :
      CoordinatorCollectionLedger.rawEntryDomainsCheck candidate = true := by
    unfold CoordinatorCollectionLedger.rawEntryDomainsCheck
    apply (allFin_eq_true_iff _).2
    intro a
    apply (allFin_eq_true_iff _).2
    intro t
    cases raw with
    | none => simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
        hrawBuffer]
    | some pair =>
        rcases pair with ⟨b, amount⟩
        by_cases hwrite : ledger.currentRegisters b = none ∧ 0 < amount ∧
            CoordinatorCollectionLedger.sourceRound time < ledger.freezeAt
        · by_cases ha : a = b
          · subst a
            by_cases ht : t = time
            · subst t
              have hpendingUnknown :
                  CoordinatorCollectionLedger.armPendingCheck ledger b = true := by
                have hcur := hpending.1 b
                rw [hwrite.1] at hcur
                simpa using hcur
              have hamount : amount ≤ D p := harrival
              have hpendingCandidate :
                  CoordinatorCollectionLedger.armPendingCheck candidate b = true := by
                have hcur := hcurrentPending b
                simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate,
                  hwrite.1] using hcur.symm
              have hnew := CoordinatorCollectionLedger.startRoundCandidate_rawBuffer_positive
                ledger time enabled b amount hwrite.1 hwrite.2.1 hwrite.2.2
              have hcandidateCell : candidate.rawBuffer b time = some amount := by
                simpa [candidate] using hnew
              have hfreezeBound : time.val + 1 < ledger.freezeAt := by
                simpa [hsource] using hwrite.2.2
              rw [hcandidateCell]
              rw [hpendingCandidate]
              simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
                hrawBuffer, hwrite, hwrite.2.1, hwrite.2.2,
                hamount, hcutoff, hsource, hfreezeBound,
                CoordinatorCollectionLedger.sourceRound]
            · have hother : b ≠ b ∨ t ≠ time := Or.inr ht
              have hput := CoordinatorCollectionLedger.putRaw_other ledger.rawBuffer
                b b time t amount hother
              have hputNone :
                  CoordinatorCollectionLedger.putRaw (fun _ _ => none) b time amount b t = none := by
                simpa [hrawBuffer] using hput
              have hcandidateCell : candidate.rawBuffer b t = none := by
                simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate,
                  hrawBuffer, hwrite] using hputNone
              rw [hcandidateCell]
          · have hother : a ≠ b ∨ t ≠ time := Or.inl ha
            have hput := CoordinatorCollectionLedger.putRaw_other ledger.rawBuffer
              b a time t amount hother
            have hputNone :
                CoordinatorCollectionLedger.putRaw (fun _ _ => none) b time amount a t = none := by
              simpa [hrawBuffer] using hput
            have hcandidateCell : candidate.rawBuffer a t = none := by
              simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate,
                hrawBuffer, hwrite] using hputNone
            rw [hcandidateCell]
        · have hcandidateCell : candidate.rawBuffer a t = none := by
            simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
              hrawBuffer, hwrite]
          rw [hcandidateCell]
  have hregisterDomains :
      CoordinatorCollectionLedger.registerDomainsCheck candidate = true := by
    have hcurrentCheck : CoordinatorCollectionLedger.allFin p.K (fun a =>
        match candidate.currentRegisters a with
        | none => true
        | some current => decide (current.queue ≤ p.T * D p) &&
            decide (current.lastService ≤ D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro a
      cases hknown : candidate.currentRegisters a with
      | none => rfl
      | some current =>
          have hd := hcurrentDomains a
          simpa only [hknown, decide_eq_true_eq, Bool.and_eq_true] using hd
    have hcutoffCheck : CoordinatorCollectionLedger.allFin p.K (fun a =>
        match candidate.cutoffRegisters a with
        | none => true
        | some current => decide (current.score ≤ p.T * D p) &&
            decide (current.queue ≤ p.T * D p) &&
            decide (current.lastService ≤ D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro a
      cases hknown : candidate.cutoffRegisters a with
      | none => rfl
      | some current =>
          have hd := hcutoffDomains a
          simp only [hknown] at hd
          rcases hd with ⟨hs, hq, hl⟩
          simp [hknown, hs, hq, hl]
    have hbaseCheck : CoordinatorCollectionLedger.allFin (p.m - 1)
        (fun i => decide (candidate.baseScore i ≤ p.T * D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro i
      simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate] using
        (decide_eq_true_eq.mpr (hbase i))
    have hincrementCheck : CoordinatorCollectionLedger.allFin p.K
        (fun a => decide (candidate.increment a ≤ p.T * D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro a
      simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hincrement]
    have hgammaCheck : CoordinatorCollectionLedger.allFin p.K
        (fun a => decide (candidate.gammaLoc a ≤ D p)) = true := by
      apply (allFin_eq_true_iff _).2
      intro a
      exact decide_eq_true_eq.mpr (hgammaDomain a)
    unfold CoordinatorCollectionLedger.registerDomainsCheck
    simp only [Bool.and_eq_true]
    constructor
    · constructor
      · constructor
        · constructor
          · exact hcurrentCheck
          · exact hcutoffCheck
        · exact hbaseCheck
      · exact hincrementCheck
    · exact hgammaCheck
  have hstarted : candidate.phase = .started := by
    simp [candidate, CoordinatorCollectionLedger.startRoundCandidate]
  have hcursorBound : candidate.cursor ≤ p.T := by
    simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
      CoordinatorCollectionLedger.sourceRound]
  have hpendingGammaCheck : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck candidate a) ||
        decide (candidate.gammaLoc a = 0)) = true := by
    apply (allFin_eq_true_iff _).2
    intro a
    cases hknown : ledger.currentRegisters a with
    | none =>
        have hg := CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
          ledger time enabled raw a hknown
        simp [candidate, hg]
    | some current =>
        have hcurrent := hcurrentPending a
        have hnotPending : CoordinatorCollectionLedger.armPendingCheck candidate a = false := by
          simpa [candidate, CoordinatorCollectionLedger.startRoundCandidate, hknown] using
            hcurrent.symm
        simp [hnotPending]
  have hincrementCandidate : candidate.increment = fun _ => 0 := by
    simp [candidate, CoordinatorCollectionLedger.startRoundCandidate, hincrement]
  have hsigmaPosCandidate : 1 ≤
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).sigma := by
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using hsigmaPos
  have hsigmaTCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).sigma ≤ p.T := by
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using hsigmaT
  have hcutoffPosCandidate : 1 ≤
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cutoff := by
    simpa [CoordinatorCollectionLedger.startRoundCandidate, hcutoff] using hcutoffPos
  have hcutoffFreezeCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cutoff ≤
        (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).freezeAt := by
    simpa [CoordinatorCollectionLedger.startRoundCandidate, hcutoff] using hcutoffFreeze
  have hfreezeCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).freezeAt ≤ p.T + 1 := by
    simpa [CoordinatorCollectionLedger.startRoundCandidate] using hfreeze
  have hcutoffTCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cutoff ≤ p.T := by
    simpa [CoordinatorCollectionLedger.startRoundCandidate, hcutoff] using hcutoffT
  have hcutoffCursorCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cutoff ≤
        (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cursor := by
    simp [CoordinatorCollectionLedger.startRoundCandidate, hcutoff, hsource]
  have hcursorCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cursor ≤ p.T + 1 := by
    have ht := htime
    simpa [CoordinatorCollectionLedger.startRoundCandidate,
      CoordinatorCollectionLedger.sourceRound] using Nat.le_trans ht (Nat.le_succ _)
  have hcursorTCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cursor ≤ p.T := by
    simpa [candidate] using hcursorBound
  have hstartedCandidate :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).phase = .started := by
    simpa [candidate] using hstarted
  have hstartedHistoryCandidate : CoordinatorCollectionLedger.startedHistoryCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) = true := by
    simpa [candidate] using hstartedHistory
  have hcurrentPendingCandidate : ∀ a,
      ((CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).currentRegisters a).isNone =
        CoordinatorCollectionLedger.armPendingCheck
          (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) a := by
    simpa [candidate] using hcurrentPending
  have hcutoffPendingCandidate : ∀ a,
      ((CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).cutoffRegisters a).isNone =
        CoordinatorCollectionLedger.armPendingCheck
          (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) a := by
    simpa [candidate] using hcutoffPending
  have hpendingGammaCandidate : CoordinatorCollectionLedger.allFin p.K (fun a =>
      (!CoordinatorCollectionLedger.armPendingCheck
          (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) a) ||
        decide ((CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).gammaLoc a = 0)) = true := by
    simpa [candidate] using hpendingGammaCheck
  have hincrementCandidate' :
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw).increment = fun _ => 0 := by
    simpa [candidate] using hincrementCandidate
  have hregisterDomainsCandidate : CoordinatorCollectionLedger.registerDomainsCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) = true := by
    simpa [candidate] using hregisterDomains
  have hrawEntriesCandidate : CoordinatorCollectionLedger.rawEntryDomainsCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw) = true := by
    simpa [candidate] using hrawEntries
  have hsigmaPosLet : 1 ≤ candidate.sigma := by
    simpa only [candidate] using hsigmaPosCandidate
  have hsigmaTLet : candidate.sigma ≤ p.T := by
    simpa only [candidate] using hsigmaTCandidate
  have hcutoffPosLet : 1 ≤ candidate.cutoff := by
    simpa only [candidate] using hcutoffPosCandidate
  have hcutoffFreezeLet : candidate.cutoff ≤ candidate.freezeAt := by
    simpa only [candidate] using hcutoffFreezeCandidate
  have hfreezeLet : candidate.freezeAt ≤ p.T + 1 := by
    simpa only [candidate] using hfreezeCandidate
  have hcutoffTLet : candidate.cutoff ≤ p.T := by
    simpa only [candidate] using hcutoffTCandidate
  have hcutoffCursorLet : candidate.cutoff ≤ candidate.cursor := by
    simpa only [candidate] using hcutoffCursorCandidate
  have hcursorLet : candidate.cursor ≤ p.T + 1 := by
    simpa only [candidate] using hcursorCandidate
  have hstartedLet : candidate.phase = .started := by
    simpa only [candidate] using hstartedCandidate
  change CoordinatorCollectionLedger.validLedgerCheck candidate = true
  simp [CoordinatorCollectionLedger.validLedgerCheck,
    hsigmaPosLet, hsigmaTLet, hcutoffPosLet, hcutoffFreezeLet, hfreezeLet,
    hcutoffTLet, hcutoffCursorLet, hcursorLet, hstartedLet, hcursorBound,
    hstartedHistory, hcurrentPending, hcutoffPending, hpendingGammaCheck,
    hincrementCandidate, hregisterDomains, hrawEntries]
  apply (allFin_eq_true_iff _).2
  intro a
  rfl

/-- Produce the first actual cutoff's collection stage-(1) success from the
same original execution and same private row index. The conditional premise
is exactly the existence of a chosen cutoff inside the supplied interval.
The result retains the actual branch, initialized ledger, recorder output,
and literal candidate, before any UP or finish result is inspected. -/
theorem run_first_cutoff_recorded_service
    (initial : State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hshort : (firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count hspan active).records).length
        < count) :
    let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active
    let window := firstLiveWindow execution.records
    let k := window.length
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[k]'(by
        simpa [execution, ReferenceActivePhysicalHorizon.run_record_count] using hshort) ∧
      cut.input.time.val = start + k ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        cut.input.state = (ReferenceActivePhysicalHorizon.run initial rows J rewards
          start k (by
            have hk : k < count := by simpa [window, execution] using hshort
            exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active).finalState ∧
        (ReferenceActivePhysicalHorizon.run initial rows J rewards
          start k (by
            have hk : k < count := by simpa [window, execution] using hshort
            exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active).finalState.coordinator =
          .live r q base ∧
        let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            callInput.registers callInput.ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
            callInput.registers.time callInput.registers.priorClock
            callInput.registers.clockPending = .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hclock : dispatched.startResult.clock =
            { callInput.registers.priorClock with u := some callInput.registers.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection callInput.registers.payload
            dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights cut.input.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          ∃ output,
            ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
              some (CoordinatorRecorderComplementBridge.recorderInput
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  cut.output.preparation callInput.registers.payload dispatched.startResult
                  callInput.registers.complementWeights)) ∧
            ReferenceCoordinatorRecorderCallTrace.recording
              (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some output ∧
            cut.coordinatorDiagnostics.recording = some output ∧
            CoordinatorRecordingOperation.run
              (CoordinatorRecorderComplementBridge.recorderInput
                (ReferenceActivePhysicalStep.collectionRecordingInput
                  cut.output.preparation callInput.registers.payload dispatched.startResult
                  callInput.registers.complementWeights)) = some output ∧
            let shared := ReferenceActivePhysicalStep.sharedLedger ledger
            let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output
            let enabled := ReferenceActivePhysicalStep.collectionEnabled shared cut.input.time
            ∃ next,
              CoordinatorCollectionLedger.startRound shared (cut.input.time.val + 1)
                enabled raw = .success next ∧
              next = CoordinatorCollectionLedger.startRoundCandidate shared cut.input.time
                enabled raw ∧
              (∀ a current, shared.currentRegisters a = some current →
                next.currentRegisters a = some ⟨
                  (QueueReplay.transition (4 * rate.n) (0, current.queue)
                    (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                      enabled raw a)).2,
                  (QueueReplay.transition (4 * rate.n) (0, current.queue)
                    (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                      enabled raw a)).1⟩) ∧
              (∀ a, shared.currentRegisters a = none →
                next.currentRegisters a = none ∧ next.gammaLoc a = 0) ∧
              (∀ a amount, shared.currentRegisters a = none → 0 < amount →
                CoordinatorCollectionLedger.sourceRound cut.input.time < shared.freezeAt →
                raw = some (a, amount) → next.rawBuffer a cut.input.time = some amount) ∧
              (∀ a amount other armRound, shared.currentRegisters a = none →
                0 < amount →
                CoordinatorCollectionLedger.sourceRound cut.input.time < shared.freezeAt →
                raw = some (a, amount) → (other ≠ a ∨ armRound ≠ cut.input.time) →
                next.rawBuffer other armRound = shared.rawBuffer other armRound) ∧
              (∀ a current, shared.currentRegisters a = some current →
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).2 ≤ (k + 1) * D p ∧
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).2 ≤ p.T * D p ∧
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).1 ≤ 4 * rate.n ∧
                (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time
                    enabled raw a)).1 ≤ D p) := by
  classical
  let execution := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start count hspan active
  let window := firstLiveWindow execution.records
  let k := window.length
  have houtside := ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
    initial rows J rewards start count hspan active hfirst (by simpa [execution, window] using hshort)
  rcases houtside with ⟨cut, suffix, hcutParts⟩
  have hsplit := hcutParts.1
  have hindex := hcutParts.2.1
  have htime := hcutParts.2.2.1
  have hstateWitness := hcutParts.2.2.2.2
  rcases hstateWitness with ⟨r, q, base, hstate, hprefixLive, hcall⟩
  dsimp only at hcall
  rcases hcall with ⟨dispatched, hstart, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, selected, hbranchRest⟩
  have hbranch := hbranchRest.1
  let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
  let localInput := ReferenceActivePhysicalStep.collectionRecordingInput
    cut.output.preparation callInput.registers.payload dispatched.startResult
    callInput.registers.complementWeights
  let recorderInput := CoordinatorRecorderComplementBridge.recorderInput localInput
  let shared := ReferenceActivePhysicalStep.sharedLedger ledger
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows J rewards
    start k (by
      have hk : k < count := by simpa [window, execution] using hshort
      exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) start) hspan) active
  have hmass := ReferenceFirstComplementMassBudget.run_first_complement_mass
    initial rows J rewards start count hspan active hfirst k (by
      have hk : k < count := by simpa [window, execution] using hshort
      omega) (by rfl)
  dsimp only [ReferenceFirstComplementMassBudget.originalPrefix] at hmass
  have hprefixMass : prefixRun.finalState.coordinator = .live r q base := by
    simpa only [prefixRun, ReferenceFirstComplementMassBudget.originalPrefix] using hprefixLive
  rw [hprefixMass] at hmass
  change (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      r.complementScores a + q.queue a ≤ k * D p) ∧
    (∀ a : CanonicalFastSampling.FastArm r.payload.slowSet,
      q.previousService a ≤ D p) ∧
    (∀ i : Fin (p.m - 1), base i = 0) ∧
    ∃ birth, birth ∈ (ReferenceFirstComplementMassBudget.originalRun
      initial rows J rewards start count hspan active).records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth r.payload ∧
      birth.input.time.val = start at hmass
  have hlocal : CoordinatorRecorderComplementBridge.LocalInputsValid localInput := by
    refine ⟨selected.recorderBoundaryValid, ?_⟩
    intro j
    exact ⟨selected.choiceInputsValid.anchor_le_current j,
      selected.choiceInputsValid.current_le_twice_anchor j⟩
  have hcollection : localInput.mode = .collection := rfl
  obtain ⟨output, hbridgeRun⟩ :=
    recorder_run_total_of_collection localInput hlocal hcollection
  have hrecorderRun : CoordinatorRecordingOperation.run recorderInput = some output := by
    rw [← CoordinatorRecorderComplementBridge.run_eq_accepted localInput]
    exact hbridgeRun
  let selection := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
    cut.input callInput.registers.payload dispatched.startResult callInput.registers.time
    callInput.registers.complementWeights selected rfl
  have hprep : cut.output.preparation = ReferenceActivePhysicalStep.prepare cut.input :=
    congrArg ReferenceActivePhysicalStep.RoundOutput.preparation cut.output_eq
  have hdispatch : ReferenceActivePhysicalStep.dispatch cut.input =
      .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain
        hclock hpending hnoAssignment selected) := by
    have hprepared : (ReferenceActivePhysicalStep.prepare cut.input).coordinator =
        .live r q base (.cutoffChosen dispatched hstart ledger hinit hledger hdomain
          hclock hpending hnoAssignment selected) := by
      rw [← hprep]
      exact hbranch
    simpa [ReferenceActivePhysicalStep.prepare] using hprepared
  have hselected : (ReferenceActivePhysicalStep.dispatch cut.input).selection =
      some selection := by
    rw [hdispatch]
    change ReferenceActivePhysicalStep.selectionAt cut.input callInput.registers.payload
      dispatched.startResult cut.input.time callInput.registers.complementWeights selected =
        some selection
    exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq cut.input
      callInput.registers.payload dispatched.startResult cut.input.time
      callInput.registers.complementWeights selected rfl
  have hpreparedSelected : cut.output.preparation.coordinator.selection = some selection := by
    rw [hprep]
    exact hselected
  have hnotLive : ¬ CoordinatorLocalArmChoice.assignmentIsLive
      selection.view.payload selection.view.cutoff cut.input.time := by
    have hbits := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits
      cut selection hselected
    rw [hbranch] at hbits
    have htraceLive := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode cut)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selection)
      cut.input.time rfl
    change ReferenceCoordinatorRecorderCallTrace.live
        (ReferenceActiveHorizonMeasurability.roundRecordCode cut)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selection) =
      decide (CoordinatorLocalArmChoice.assignmentIsLive
        selection.view.payload selection.view.cutoff cut.input.time) at htraceLive
    intro hlive
    rw [htraceLive, decide_eq_true hlive] at hbits
    simp at hbits
  have hinputSelected :=
    ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_collection_selected
      cut selection hpreparedSelected hnotLive
  have hactualInput : ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
      some recorderInput := by
    calc
      ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
          ReferenceCoordinatorRecorderCallTrace.inputFromCode cut :=
        (ReferenceCoordinatorRecorderCallCorrespondence.inputFromCode_eq_actualBranchInput cut).symm
      _ = ReferenceCoordinatorRecorderCallTrace.inputFromSelection cut
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selection) :=
        ReferenceCoordinatorRecorderCallTrace.inputFromCode_of_selected cut selection hselected
      _ = recorderInput := congrArg some hinputSelected
  have hrecording := ReferenceCoordinatorRecorderCallCorrespondence.recording_eq_run_of_selected
    cut selection hselected
  have htrace : ReferenceCoordinatorRecorderCallTrace.recording
      (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some output := by
    rw [hrecording, hinputSelected]
    exact hrecorderRun
  have hdiagnostic : cut.coordinatorDiagnostics.recording = some output := by
    rw [← ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics cut]
    exact htrace
  have hdomainSaved := hdomain
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output
  let enabled := ReferenceActivePhysicalStep.collectionEnabled shared cut.input.time
  rcases hdomain with ⟨_, _, hsigmaTime, htimeFreeze, hgridBound, _, _, hqueueDomain,
    hpreviousDomain, hbaseDomain, _, hledgerValid⟩
  have hvalidShared : CoordinatorCollectionLedger.validLedger shared := by
    have hvalidLedger : CoordinatorCollectionLedger.validLedgerCheck ledger = true := by
      simpa [hledger] using hledgerValid
    rcases ReferenceActivePhysicalStep.sharedLedger_fields ledger with
      ⟨hassignment, hsigma, hcutoff, hfreezeAt, hbaseScore, hpending,
        hcutoffRegisters, hcurrentRegisters, hincrement, hgammaLoc,
        hrawBuffer', henabledHistory', hcursor', hphase'⟩
    change CoordinatorCollectionLedger.validLedgerCheck
      (ReferenceActivePhysicalStep.sharedLedger ledger) = true
    simpa only [CoordinatorCollectionLedger.validLedgerCheck,
      CoordinatorCollectionLedger.readyHistoryCheck,
      CoordinatorCollectionLedger.startedHistoryCheck,
      CoordinatorCollectionLedger.registerDomainsCheck,
      CoordinatorCollectionLedger.rawEntryDomainsCheck,
      CoordinatorCollectionLedger.armPendingCheck,
      hassignment, hsigma, hcutoff, hfreezeAt, hbaseScore, hpending,
      hcutoffRegisters, hcurrentRegisters, hincrement, hgammaLoc,
      hrawBuffer', henabledHistory', hcursor', hphase'] using hvalidLedger
  have hmassFast : ∀ a : CanonicalFastSampling.FastArm callInput.registers.payload.slowSet,
      callInput.registers.complementScores a + callInput.ownedRegisters.queue a ≤ k * D p := by
    intro a
    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.liveOwnedAt] using
      hmass.1 a
  have hpreviousFast : ∀ a : CanonicalFastSampling.FastArm callInput.registers.payload.slowSet,
      callInput.ownedRegisters.previousService a ≤ D p := by
    intro a
    simpa [callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.liveOwnedAt] using
      hmass.2.1 a
  have hcutoffFields : shared.cutoffRegisters =
      CoordinatorStartRoundCutoffDispatch.outsideRegisters
        callInput.registers callInput.ownedRegisters := by
    simp [shared, callInput, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hcurrentFields : shared.currentRegisters = fun a =>
      (CoordinatorStartRoundCutoffDispatch.outsideRegisters
        callInput.registers callInput.ownedRegisters a).map
          (fun reg => ⟨reg.queue, reg.lastService⟩) := by
    simp [shared, callInput, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hcutoffMass : ∀ a cutoff, shared.cutoffRegisters a = some cutoff →
      cutoff.score + cutoff.queue ≤ k * D p ∧ cutoff.lastService ≤ D p := by
    intro a cutoff hknown
    have hknownOutside :
        CoordinatorStartRoundCutoffDispatch.outsideRegisters
          callInput.registers callInput.ownedRegisters a = some cutoff := by
      simpa [hcutoffFields] using hknown
    unfold CoordinatorStartRoundCutoffDispatch.outsideRegisters at hknownOutside
    split at hknownOutside
    · rename_i hfast
      let arm : CanonicalFastSampling.FastArm callInput.registers.payload.slowSet := ⟨a, hfast⟩
      have heq := Option.some.inj hknownOutside
      subst cutoff
      simpa [arm] using ⟨hmassFast arm, hpreviousFast arm⟩
    · simp at hknownOutside
  have hcurrentQueue : ∀ a current, shared.currentRegisters a = some current →
      current.queue ≤ k * D p := by
    intro a current hknown
    rw [hcurrentFields] at hknown
    cases houtside : CoordinatorStartRoundCutoffDispatch.outsideRegisters
        callInput.registers callInput.ownedRegisters a with
    | none => simp [houtside] at hknown
    | some cutoff =>
        have houtsideCutoff : shared.cutoffRegisters a = some cutoff := by
          rw [hcutoffFields]
          exact houtside
        have hmassReg := hcutoffMass a cutoff houtsideCutoff
        simp [houtside] at hknown
        subst current
        have hqueueBound : cutoff.queue ≤ k * D p :=
          Nat.le_trans (Nat.le_add_left cutoff.queue cutoff.score) hmassReg.1
        simpa using hqueueBound
  have hsigmaPos : 1 ≤ shared.sigma := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hsigmaT : shared.sigma ≤ p.T := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hcutoffPos : 1 ≤ shared.cutoff := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hcutoffFreeze : shared.cutoff ≤ shared.freezeAt := by
    simpa [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using htimeFreeze
  have hfreeze : shared.freezeAt ≤ p.T + 1 := by
    simpa [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using hgridBound
  have hcutoffT : shared.cutoff ≤ p.T := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hcutoff : shared.cutoff = cut.input.time.val + 1 := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hcursor : shared.cursor = cut.input.time.val + 1 := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hphase : shared.phase = .ready := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hbase : ∀ i, shared.baseScore i ≤ p.T * D p := by
    simpa [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger] using hbaseDomain
  have hincrement : shared.increment = fun _ => 0 := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hrawBuffer : shared.rawBuffer = fun _ _ => none := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have henabledHistory : shared.enabledHistory = fun _ => none := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hgamma : shared.gammaLoc = fun _ => 0 := by
    simp [shared, callInput, ReferenceActivePhysicalStep.liveInput,
      ReferenceActivePhysicalStep.liveRegistersAt, ReferenceActivePhysicalStep.sharedLedger, hledger,
      CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hrawDomain := output_rawInput_domain output
  have harrival : match raw with
      | none => True
      | some (_, amount) => amount ≤ D p := by
    cases hgate : output.gateArm with
    | none => simp [raw, hgate, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
    | some arm =>
        simpa [raw, hgate, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
          using output.rawArrival_le_D
  have hcapacity : 4 * rate.n ≤ D p :=
    ActiveFollowerDownAcceptance.four_n_le_D p rate
  have hkService : k + 1 ≤ p.T := by
    have hk : k < count := by simpa [window, execution] using hshort
    omega
  have hcandidateValid := cutoffCandidate_valid shared cut.input.time enabled raw k
    hvalidShared hsigmaPos hsigmaT hcutoffPos hcutoffFreeze hfreeze hcutoffT
    hcutoff hcursor hphase hbase hincrement hrawBuffer henabledHistory hgamma
    hcurrentQueue hcutoffMass harrival hkService hcapacity
  have hslot : CoordinatorCollectionLedger.rawSlotFreshCheck shared cut.input.time raw = true := by
    cases hgate : output.gateArm with
    | none =>
        simp [raw, hgate, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
          CoordinatorCollectionLedger.rawSlotFreshCheck]
    | some arm =>
        simp [raw, hgate, CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
          CoordinatorCollectionLedger.rawSlotFreshCheck,
          shared, callInput, ReferenceActivePhysicalStep.sharedLedger, hledger,
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger]
  have hstartSuccess : CoordinatorCollectionLedger.startRound shared
      (cut.input.time.val + 1) enabled raw =
      .success (CoordinatorCollectionLedger.startRoundCandidate shared cut.input.time enabled raw) := by
    exact startRound_success_of_owned_checks shared cut.input.time enabled raw
      hvalidShared hphase hcursor hrawDomain hslot hcandidateValid
  refine ⟨cut, suffix, hsplit, hindex, htime, r, q, base, hstate, ?_, ?_⟩
  · simpa [prefixRun] using hprefixLive
  · refine ⟨dispatched, hstart, ledger, hinit, hledger, hdomainSaved, hclock, hpending,
      hnoAssignment, selected, hbranch, ?_⟩
    refine ⟨output, ?_, htrace, hdiagnostic, hrecorderRun, ?_⟩
    · simpa [recorderInput, localInput] using hactualInput
    · refine ⟨CoordinatorCollectionLedger.startRoundCandidate shared cut.input.time enabled raw,
        hstartSuccess, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro a current hknown
        rw [CoordinatorCollectionLedger.startRoundCandidate_known_transition
          shared cut.input.time enabled raw a current hknown]
      · intro a hunknown
        have hunknownShared : shared.currentRegisters a = none := by
          simpa only [shared] using hunknown
        constructor
        · simp [CoordinatorCollectionLedger.startRoundCandidate, hunknownShared]
        · exact CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
            shared cut.input.time enabled raw a hunknownShared
      · intro a amount hunknown hpositive hbefore hraw
        have hraw' : raw = some (a, amount) := by
          change CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output =
            some (a, amount)
          exact hraw
        rw [hraw']
        exact CoordinatorCollectionLedger.startRoundCandidate_rawBuffer_positive
          shared cut.input.time enabled a amount hunknown hpositive hbefore
      · intro a amount other armRound hunknown hpositive hbefore hraw hframe
        have hraw' : raw = some (a, amount) := by
          change CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output =
            some (a, amount)
          exact hraw
        rw [hraw']
        have hcondition : shared.currentRegisters a = none ∧ amount > 0 ∧
            CoordinatorCollectionLedger.sourceRound cut.input.time < shared.freezeAt :=
          ⟨hunknown, hpositive, hbefore⟩
        have hsharedRawEq : shared.rawBuffer =
            (ReferenceActivePhysicalStep.sharedLedger ledger).rawBuffer := rfl
        have hsharedRawCell := congrArg (fun buffer => buffer other armRound) hsharedRawEq
        have hput := CoordinatorCollectionLedger.putRaw_other shared.rawBuffer a other
          cut.input.time armRound amount hframe
        have hput' := hput.trans hsharedRawCell
        simpa only [CoordinatorCollectionLedger.startRoundCandidate, hcondition,
          true_and, and_true, if_true] using hput'
      · intro a current hknown
        have hqueue := hcurrentQueue a current hknown
        have harrivalLocal : CoordinatorCollectionLedger.localArrival raw a ≤ D p := by
          cases hrawCase : raw with
          | none => simp [CoordinatorCollectionLedger.localArrival]
          | some pair =>
              rcases pair with ⟨b, amount⟩
              have hamount : amount ≤ D p := by
                simpa [hrawCase] using harrival
              by_cases hba : b = a
              · subst b
                simpa [CoordinatorCollectionLedger.localArrival] using hamount
              · simp [CoordinatorCollectionLedger.localArrival, hba]
        have hrecordBound :
            (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time enabled raw a).2 ≤ D p := by
          unfold CoordinatorCollectionLedger.localQueueRecord
          split
          · exact harrivalLocal
          · simp
        have htransition := queueTransition_domains (4 * rate.n) current.queue
          (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time enabled raw a)
          hrecordBound hcapacity
        have hqueueStep :
            (QueueReplay.transition (4 * rate.n) (0, current.queue)
              (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time enabled raw a)).2 ≤
              (k + 1) * D p := by
          calc
            (QueueReplay.transition (4 * rate.n) (0, current.queue)
              (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time enabled raw a)).2
                ≤ current.queue +
                    (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time enabled raw a).2 :=
              htransition.2
            _ ≤ k * D p + D p := Nat.add_le_add hqueue hrecordBound
            _ = (k + 1) * D p := by rw [Nat.add_mul]; simp
        constructor
        · exact hqueueStep
        constructor
        · exact hqueueStep.trans (Nat.mul_le_mul_right (D p) hkService)
        constructor
        · exact queueTransition_service_le_capacity (4 * rate.n) current.queue
            (CoordinatorCollectionLedger.localQueueRecord shared cut.input.time enabled raw a)
        · exact htransition.1

end Bandits.Support.ReferenceFirstCutoffRecordedService

end
