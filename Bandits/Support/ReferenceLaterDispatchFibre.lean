/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterAssignmentFibreStep

/-!
# Actual pre-choice later-assignment fibres

Internal deterministic mathematics for the original collection dispatcher.
Sources: `sources/zip4/manuscript/06_interruptions.tex:30-69,235-296,376-423`,
`sources/zip4/manuscript/05_binary_transport.tex:62-80`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

Only the whole assignment-coordinate vector changes. Rejected sampler tags
are retained, and are compared through absence of continuation. No truthful
ledger, feasible law, physical history, or manuscript closure is assumed.
The complete pre-choice comparisons are proved here. Post-choice physical
evidence assembly, horizon records and finite-fibre measure consumption remain
separate obligations.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceLaterAssignmentFibreStep

namespace Bandits.Support.ReferenceLaterDispatchFibre

variable {p : Parameters} {rate : RateInput p}

private local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

private theorem core_row (x : CoordinatorRoundDispatch.CollectionInput p)
    (row : CompletePublicTable.CompleteRow p) :
    CoordinatorRoundDispatch.CollectionCoreValid { x with row := row } ↔
      CoordinatorRoundDispatch.CollectionCoreValid x := by
  constructor <;> intro h <;>
    exact ⟨h.payload_n_eq, h.ledger_valid, h.ledger_ready, h.assignment_eq,
      h.base_score_eq, h.clock_parameter_valid, h.clock_registers_valid,
      h.clock_start_time_valid, h.clock_sigma_eq, h.clock_cutoff_eq,
      h.ledger_sigma_eq, h.ledger_cutoff_eq, h.ledger_freeze_eq,
      h.ledger_cursor_eq, h.decoder_bank_valid⟩

private theorem collection_pair
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (left right : CompletePublicTable.CompleteRow p)
    (hf : match collectionParameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector left x.time) =
        AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector right x.time))
    (hchoice : ∀ (payload : AssignmentStartPayload.Input p ⟨x.etaReal, x.etaPositive⟩)
      (pending : Finset (Fin (p.m - 1)))
      (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ),
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights left =
        CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights right) :
    match CoordinatorRoundDispatch.dispatchCollection { x with row := left },
      CoordinatorRoundDispatch.dispatchCollection { x with row := right } with
    | .continuing _ a _ _, .continuing _ b _ _ =>
        a.clockStarted = b.clockStarted ∧ a.arm = b.arm ∧
        CoordinatorCollectionInteractive.PreObservationInputs.weights { x with row := left }
          a.inputsValid.ledger_valid a.inputsValid.assignment_eq =
        CoordinatorCollectionInteractive.PreObservationInputs.weights { x with row := right }
          b.inputsValid.ledger_valid b.inputsValid.assignment_eq
    | .laterChosen ca ka sa _ ia _ oa ha da ra aa,
        .laterChosen cb kb sb _ ib _ ob hb db rb ab =>
        sa = sb ∧ ia = ib ∧ ra.registers = rb.registers ∧
        HEq ra.ownedRegisters rb.ownedRegisters ∧
        ra.retainedBaseScore = rb.retainedBaseScore ∧ aa.arm = ab.arm ∧
        da.result = db.result ∧
        LaterAssignmentStartOperation.laterAssignmentStart x.payload
          (CoordinatorRoundDispatch.collectionOperationLedger { x with row := left } ca.payload_n_eq)
          ia left ka = .success oa ha ∧
        LaterAssignmentStartOperation.laterAssignmentStart x.payload
          (CoordinatorRoundDispatch.collectionOperationLedger { x with row := right } cb.payload_n_eq)
          ib right kb = .success ob hb ∧
        ra = CoordinatorAssignmentRegisterInstall.installLater oa da ∧
        rb = CoordinatorAssignmentRegisterInstall.installLater ob db
    | a, b =>
        (match a with | .continuing .. | .laterChosen .. => False | _ => True) ∧
        (match b with | .continuing .. | .laterChosen .. => False | _ => True) := by
  generalize hleftDispatch : CoordinatorRoundDispatch.dispatchCollection
    { x with row := left } = leftOutcome
  generalize hrightDispatch : CoordinatorRoundDispatch.dispatchCollection
    { x with row := right } = rightOutcome
  unfold CoordinatorRoundDispatch.dispatchCollection at hleftDispatch hrightDispatch
  split at hleftDispatch
  · rename_i failure hfailure
    split at hrightDispatch
    · cases hleftDispatch; cases hrightDispatch; trivial
    · rename_i started hstart
      rw [hfailure] at hstart
      cases hstart
  · rename_i started hstart
    split at hrightDispatch
    · rename_i failure hfailure
      rw [hstart] at hfailure
      cases hfailure
    · rename_i startedRight hstartRight
      have heq : startedRight = started := Except.ok.inj (hstartRight.symm.trans hstart)
      subst startedRight
      by_cases hc : CoordinatorRoundDispatch.CollectionCoreValid x
      · have hl := (core_row x left).mpr hc
        have hr := (core_row x right).mpr hc
        rw [dite_eq_left hl] at hleftDispatch
        rw [dite_eq_left hr] at hrightDispatch
        by_cases hp : x.ledger.pending.Nonempty
        · rw [dite_eq_left hp] at hleftDispatch hrightDispatch
          have hut : x.cutoffIndex.val ≤ x.time.val := by
            have hparts : x.payload.sigma.val < x.time.val ∧ x.cutoffIndex.val ≤ x.time.val := by
              simpa only [CoordinatorPhaseClock.startRoundTimeValid,
                hc.clock_sigma_eq, hc.clock_cutoff_eq] using hc.clock_start_time_valid
            exact hparts.2
          have hknown := CoordinatorPhaseClock.startRound_collection_pending p x.etaReal x.time
            x.payload.sigma x.cutoffIndex x.clock x.ledger.pending hc.clock_parameter_valid
            hc.clock_registers_valid hc.clock_sigma_eq hc.clock_cutoff_eq hut
            (Finset.nonempty_iff_ne_empty.mp hp)
          have hstarted := Except.ok.inj (hstart.symm.trans hknown)
          have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
              some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex) := by
            rw [hstarted, hc.clock_cutoff_eq]
            rfl
          by_cases hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck x = true
          · have hsl : CoordinatorRoundDispatch.collectionCurrentScoresCheck { x with row := left } = true := hs
            have hsr : CoordinatorRoundDispatch.collectionCurrentScoresCheck { x with row := right } = true := hs
            rw [dite_eq_left hsl] at hleftDispatch
            rw [dite_eq_left hsr] at hrightDispatch
            dsimp only at hleftDispatch hrightDispatch
            by_cases hv : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)) x.time
                (CoordinatorCollectionInteractive.PreObservationInputs.weights x
                  hc.ledger_valid hc.assignment_eq)
            · have hvl : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                  (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)) x.time
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    { x with row := left } hl.ledger_valid hl.assignment_eq) := hv
              have hvr : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                  (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)) x.time
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    { x with row := right } hr.ledger_valid hr.assignment_eq) := hv
              rw [dite_eq_left hvl] at hleftDispatch
              rw [dite_eq_left hvr] at hrightDispatch
              have hrow := hchoice x.payload started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
                (CoordinatorCollectionInteractive.PreObservationInputs.weights x
                  hc.ledger_valid hc.assignment_eq)
              have hva : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights x
                    hc.ledger_valid hc.assignment_eq) := by rw [hcutoff]; exact hv
              have hnonempty (row : CompletePublicTable.CompleteRow p) :=
                CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none x.payload
                  started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  x.time (CoordinatorCollectionInteractive.PreObservationInputs.weights x
                    hc.ledger_valid hc.assignment_eq) row hva
              split at hleftDispatch
              · rename_i hnone
                exact (hnonempty left hnone).elim
              · rename_i arm harm
                split at hrightDispatch
                · rename_i hnone
                  exact (hnonempty right hnone).elim
                · rename_i armRight harmRight
                  have hal : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload started.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
                      (CoordinatorCollectionInteractive.PreObservationInputs.weights x
                        hc.ledger_valid hc.assignment_eq) left = some arm := harm
                  have har : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload started.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
                      (CoordinatorCollectionInteractive.PreObservationInputs.weights x
                        hc.ledger_valid hc.assignment_eq) right = some armRight := harmRight
                  have ha : armRight = arm := Option.some.inj
                    (har.symm.trans (hrow.symm.trans hal))
                  subst armRight
                  cases hleftDispatch; cases hrightDispatch
                  exact ⟨rfl, rfl, rfl⟩
            · have hvl : ¬ CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                  (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)) x.time
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    { x with row := left } hl.ledger_valid hl.assignment_eq) := hv
              have hvr : ¬ CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
                  (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)) x.time
                  (CoordinatorCollectionInteractive.PreObservationInputs.weights
                    { x with row := right } hr.ledger_valid hr.assignment_eq) := hv
              rw [dite_eq_right hvl] at hleftDispatch
              rw [dite_eq_right hvr] at hrightDispatch
              cases hleftDispatch; cases hrightDispatch; trivial
          · have hsl : ¬ CoordinatorRoundDispatch.collectionCurrentScoresCheck { x with row := left } = true := hs
            have hsr : ¬ CoordinatorRoundDispatch.collectionCurrentScoresCheck { x with row := right } = true := hs
            rw [dite_eq_right hsl] at hleftDispatch
            rw [dite_eq_right hsr] at hrightDispatch
            cases hleftDispatch; cases hrightDispatch; trivial
        · rw [dite_eq_right hp] at hleftDispatch hrightDispatch
          split at hleftDispatch
          · rename_i hi
            split at hrightDispatch
            · cases hleftDispatch; cases hrightDispatch; trivial
            · rename_i instructionRight hiRight
              rw [hi] at hiRight
              cases hiRight
          · rename_i instruction hi
            split at hrightDispatch
            · rename_i hiRight
              rw [hi] at hiRight
              cases hiRight
            · rename_i instructionRight hiRight
              have heq : instructionRight = instruction := Option.some.inj (hiRight.symm.trans hi)
              subst instructionRight
              have htime : instruction.time = x.time :=
                (CoordinatorPhaseClock.startRound_assignment_effect p x.etaReal x.time
                  x.clock x.ledger.pending started instruction hc.clock_parameter_valid
                  hc.clock_registers_valid hc.clock_start_time_valid hstart hi).1
              have hlocal : match LaterAssignmentStartMeasurability.selectedSamplerParameters?
                  x.payload ⟨CoordinatorRoundDispatch.collectionOperationLedger x hc.payload_n_eq,
                    instruction, collectionConsistency x hc⟩ with
                | none => True
                | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
                    (LaterAssignmentStartOperation.ownAssignmentVector left instruction.time) =
                  AssignmentParameterFibreKernel.successfulSlowSet p theta
                    (LaterAssignmentStartOperation.ownAssignmentVector right instruction.time) := by
                have hparameters : collectionParameters? x =
                    LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
                      ⟨CoordinatorRoundDispatch.collectionOperationLedger x hc.payload_n_eq,
                        instruction, collectionConsistency x hc⟩ := by
                  unfold collectionParameters?
                  rw [hstart]
                  dsimp only
                  rw [dite_eq_left hc, ite_eq_right hp, hi]
                rw [hparameters] at hf
                cases htheta : LaterAssignmentStartMeasurability.selectedSamplerParameters?
                    x.payload ⟨CoordinatorRoundDispatch.collectionOperationLedger x hc.payload_n_eq,
                      instruction, collectionConsistency x hc⟩ with
                | none => trivial
                | some theta =>
                    simp only [htheta] at hf ⊢
                    simpa only [htime] using hf
              have hpayload := laterPayloadAndBaseScore?_fibre x.payload
                ⟨CoordinatorRoundDispatch.collectionOperationLedger x hc.payload_n_eq,
                  instruction, collectionConsistency x hc⟩ left right hlocal
              dsimp only at hleftDispatch hrightDispatch
              unfold laterPayloadAndBaseScore? at hpayload
              change payloadAndBaseScoreOfResult
                  (LaterAssignmentStartOperation.laterAssignmentStart x.payload
                    (CoordinatorRoundDispatch.collectionOperationLedger { x with row := left } hl.payload_n_eq)
                    instruction left (collectionConsistency { x with row := left } hl)) =
                payloadAndBaseScoreOfResult
                  (LaterAssignmentStartOperation.laterAssignmentStart x.payload
                    (CoordinatorRoundDispatch.collectionOperationLedger { x with row := right } hr.payload_n_eq)
                    instruction right (collectionConsistency { x with row := right } hr)) at hpayload
              unfold collectionConsistency at hpayload
              clear htime
              split at hleftDispatch <;> split at hrightDispatch
              all_goals simp_all only [payloadAndBaseScoreOfResult,
                Option.some.injEq, Prod.mk.injEq]
              all_goals try (cases hleftDispatch; cases hrightDispatch; trivial)
              rename_i oa hla ob hlb calla callb
              have htime : instruction.time = x.time :=
                (CoordinatorPhaseClock.startRound_assignment_effect p x.etaReal x.time
                  x.clock x.ledger.pending started instruction hc.clock_parameter_valid
                  hc.clock_registers_valid hc.clock_start_time_valid hstart hi).1
              let da : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence oa := {
                priorClock := x.clock
                pending := x.ledger.pending
                proposalParameterValid := hc.clock_parameter_valid
                priorClockValid := hc.clock_registers_valid
                startTimeValid := by rw [htime]; exact hc.clock_start_time_valid
                result := started
                startRound_eq := by rw [htime]; exact hstart
                assignmentStart_eq := hi
                priorSigma_eq := hc.clock_sigma_eq
                priorGrid_eq_freezeAt := hc.ledger_freeze_eq.symm.trans
                  (congrArg LaterAssignmentStartOperation.LocalConsistency.oldFreezeAt hla).symm }
              let db : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence ob := {
                priorClock := x.clock
                pending := x.ledger.pending
                proposalParameterValid := hc.clock_parameter_valid
                priorClockValid := hc.clock_registers_valid
                startTimeValid := by rw [htime]; exact hc.clock_start_time_valid
                result := started
                startRound_eq := by rw [htime]; exact hstart
                assignmentStart_eq := hi
                priorSigma_eq := hc.clock_sigma_eq
                priorGrid_eq_freezeAt := hc.ledger_freeze_eq.symm.trans
                  (congrArg LaterAssignmentStartOperation.LocalConsistency.oldFreezeAt hlb).symm }
              obtain ⟨hregs, howned, hbase⟩ := successful_installation_fibre x.payload
                ⟨CoordinatorRoundDispatch.collectionOperationLedger x hc.payload_n_eq,
                  instruction, collectionConsistency x hc⟩ left right (by
                    cases htheta : LaterAssignmentStartMeasurability.selectedSamplerParameters?
                        x.payload ⟨CoordinatorRoundDispatch.collectionOperationLedger x hc.payload_n_eq,
                          instruction, collectionConsistency x hc⟩ with
                    | none => trivial
                    | some theta =>
                        simp only [htheta] at hlocal ⊢
                        simpa only [htime] using hlocal)
                oa ob hla hlb calla callb da db rfl
              let ra := CoordinatorAssignmentRegisterInstall.installLater oa da
              let rb := CoordinatorAssignmentRegisterInstall.installLater ob db
              change ra.registers = rb.registers at hregs
              change HEq ra.ownedRegisters rb.ownedRegisters at howned
              change ra.retainedBaseScore = rb.retainedBaseScore at hbase
              by_cases hb : ∀ i, ra.retainedBaseScore i ≤ p.T * D p
              · have hbr : ∀ i, rb.retainedBaseScore i ≤ p.T * D p := by
                  rw [← hbase]; exact hb
                rw [dite_eq_left hb] at hleftDispatch
                rw [dite_eq_left hbr] at hrightDispatch
                by_cases hv : CoordinatorLocalArmChoice.ChoiceInputsValid ra.registers.payload
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                    instruction.time ra.registers.complementWeights
                · have hvr : CoordinatorLocalArmChoice.ChoiceInputsValid rb.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time rb.registers.complementWeights := by rw [← hregs]; exact hv
                  rw [dite_eq_left hv] at hleftDispatch
                  rw [dite_eq_left hvr] at hrightDispatch
                  by_cases he : ra.registers.complementEnvelopeValid
                  · have her : rb.registers.complementEnvelopeValid := by rw [← hregs]; exact he
                    rw [dite_eq_left he] at hleftDispatch
                    rw [dite_eq_left her] at hrightDispatch
                    have hrow := hchoice ra.registers.payload started.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time ra.registers.complementWeights
                    have hnonemptyL := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                      ra.registers.payload started.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time ra.registers.complementWeights left hv
                    have hnonemptyR := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                      rb.registers.payload started.pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time rb.registers.complementWeights right hvr
                    split at hleftDispatch
                    · rename_i hnone
                      exact (hnonemptyL hnone).elim
                    · rename_i arm harm
                      split at hrightDispatch
                      · rename_i hnone
                        exact (hnonemptyR hnone).elim
                      · rename_i armRight harmRight
                        have hal : CoordinatorLocalArmChoice.coordinatorArmChoice ra.registers.payload
                            started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                            instruction.time ra.registers.complementWeights left = some arm := harm
                        have har : CoordinatorLocalArmChoice.coordinatorArmChoice ra.registers.payload
                            started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                            instruction.time ra.registers.complementWeights right = some armRight := by
                          rw [hregs]; exact harmRight
                        have ha : armRight = arm := Option.some.inj
                          (har.symm.trans (hrow.symm.trans hal))
                        subst armRight
                        cases hleftDispatch; cases hrightDispatch
                        exact ⟨rfl, rfl, hregs, howned, hbase, rfl, rfl, calla, callb, rfl, rfl⟩
                  · have her : ¬ rb.registers.complementEnvelopeValid := by rw [← hregs]; exact he
                    rw [dite_eq_right he] at hleftDispatch
                    rw [dite_eq_right her] at hrightDispatch
                    cases hleftDispatch; cases hrightDispatch; trivial
                · have hvr : ¬ CoordinatorLocalArmChoice.ChoiceInputsValid rb.registers.payload
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time rb.registers.complementWeights := by rw [← hregs]; exact hv
                  rw [dite_eq_right hv] at hleftDispatch
                  rw [dite_eq_right hvr] at hrightDispatch
                  cases hleftDispatch; cases hrightDispatch; trivial
              · have hbr : ¬ ∀ i, rb.retainedBaseScore i ≤ p.T * D p := by rw [← hbase]; exact hb
                rw [dite_eq_right hb] at hleftDispatch
                rw [dite_eq_right hbr] at hrightDispatch
                cases hleftDispatch; cases hrightDispatch; trivial
      · have hl : ¬ CoordinatorRoundDispatch.CollectionCoreValid { x with row := left } :=
          fun h => hc ((core_row x left).mp h)
        have hr : ¬ CoordinatorRoundDispatch.CollectionCoreValid { x with row := right } :=
          fun h => hc ((core_row x right).mp h)
        rw [dite_eq_right hl] at hleftDispatch
        rw [dite_eq_right hr] at hrightDispatch
        cases hleftDispatch; cases hrightDispatch; trivial

private theorem assignment_state (x : RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) : (withAssignment x v).state = x.state := rfl

/-- Exhaustive correspondence of the actual pre-choice continuations. The
only assignment-coordinate hypothesis is the fibre of the actual optional
parameters. Rejected outcomes need not have the same sampler-failure tag.
Successful branches expose both original success calls and installations;
continuing branches retain the same old payload, ledger, clock and weights.
-/
theorem dispatch_collection_continuations_fibre
    (x : RoundInput p rate) (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hf : match parameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w) :
    match dispatch (withAssignment x v), dispatch (withAssignment x w) with
    | .collection pa la ca ua (.continuing _ a _ _),
        .collection pb lb cb ub (.continuing _ b _ _) =>
        pa = pb ∧ la = lb ∧ ca = cb ∧ ua = ub ∧
        a.clockStarted = b.clockStarted ∧ a.arm = b.arm ∧
        HEq (CoordinatorCollectionInteractive.PreObservationInputs.weights
          (collectionInput (withAssignment x v) pa la ca ua)
          a.inputsValid.ledger_valid a.inputsValid.assignment_eq)
          (CoordinatorCollectionInteractive.PreObservationInputs.weights
            (collectionInput (withAssignment x w) pb lb cb ub)
            b.inputsValid.ledger_valid b.inputsValid.assignment_eq)
    | .collection pa la ca ua (.laterChosen corea ka sa _ ia _ oa ha da ra aa),
        .collection pb lb cb ub (.laterChosen coreb kb sb _ ib _ ob hb db rb ab) =>
        ia.time = x.time ∧ ib.time = x.time ∧
        oa.assignmentVector = v ∧ ob.assignmentVector = w ∧
        sa = sb ∧ ia = ib ∧ ra.registers = rb.registers ∧
        HEq ra.ownedRegisters rb.ownedRegisters ∧
        ra.retainedBaseScore = rb.retainedBaseScore ∧ aa.arm = ab.arm ∧
        da.result = db.result ∧
        LaterAssignmentStartOperation.laterAssignmentStart pa
          (CoordinatorRoundDispatch.collectionOperationLedger
            (collectionInput (withAssignment x v) pa la ca ua) corea.payload_n_eq)
          ia (withAssignment x v).row ka = .success oa ha ∧
        LaterAssignmentStartOperation.laterAssignmentStart pb
          (CoordinatorRoundDispatch.collectionOperationLedger
            (collectionInput (withAssignment x w) pb lb cb ub) coreb.payload_n_eq)
          ib (withAssignment x w).row kb = .success ob hb ∧
        ra = CoordinatorAssignmentRegisterInstall.installLater oa da ∧
        rb = CoordinatorAssignmentRegisterInstall.installLater ob db
    | a, b => a.selection = none ∧ b.selection = none := by
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := collectionClock payload ledger proposal cutoff
    let source := collectionInput x payload ledger clock cutoff
    have hparameters : parameters? x = collectionParameters? source := by
      simp only [parameters?, hphase, dite_eq_left hcutoff]
      rfl
    have hv : LaterAssignmentStartOperation.ownAssignmentVector
        (withAssignment x v).row source.time = v := by
      rw [withAssignment_row]
      exact ownAssignmentVector_rowWithAssignment x v
    have hw : LaterAssignmentStartOperation.ownAssignmentVector
        (withAssignment x w).row source.time = w := by
      rw [withAssignment_row]
      exact ownAssignmentVector_rowWithAssignment x w
    have hlocal : match collectionParameters? source with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector (withAssignment x v).row source.time) =
        AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector (withAssignment x w).row source.time) := by
      cases ht : collectionParameters? source with
      | none => trivial
      | some theta =>
          have ht' := hparameters.trans ht
          simp only [ht'] at hf
          simpa only [ht, hv, hw] using hf
    have hp := collection_pair source (withAssignment x v).row (withAssignment x w).row hlocal
      (by
        intro newPayload pending localCutoff time weights
        rw [withAssignment_row, withAssignment_row]
        exact (coordinatorArmChoice_row x v time newPayload pending localCutoff weights).trans
          (coordinatorArmChoice_row x w time newPayload pending localCutoff weights).symm)
    generalize hl : CoordinatorRoundDispatch.dispatchCollection
      { source with row := (withAssignment x v).row } = a at hp
    generalize hr : CoordinatorRoundDispatch.dispatchCollection
      { source with row := (withAssignment x w).row } = b at hp
    have hl' : CoordinatorRoundDispatch.dispatchCollection
        (collectionInput (withAssignment x v) payload ledger clock cutoff) = a := hl
    have hr' : CoordinatorRoundDispatch.dispatchCollection
        (collectionInput (withAssignment x w) payload ledger clock cutoff) = b := hr
    simp only [dispatch, assignment_state, hphase, dite_eq_left hcutoff,
      CoordinatorRoundDispatch.dispatch]
    rw [hl', hr']
    cases a <;> cases b <;> dsimp only at hp ⊢
    all_goals try first
      | exact ⟨rfl, rfl⟩
      | exact False.elim (show False from hp.1)
      | exact False.elim (show False from hp.2)
    · exact ⟨rfl, rfl, rfl, rfl, hp.1, hp.2.1, heq_of_eq hp.2.2⟩
    · rename_i corea ka sa hsa ia hia oa ha da ra aa
        coreb kb sb hsb ib hib ob hb db rb ab
      have hta := later_instruction_time (withAssignment x v) payload ledger clock cutoff
        corea sa ia hsa hia
      have htb := later_instruction_time (withAssignment x w) payload ledger clock cutoff
        coreb sb ib hsb hib
      have hva : oa.assignmentVector = v := by
        rw [oa.assignmentVector_eq_row_projection, hta]
        exact hv
      have hwb : ob.assignmentVector = w := by
        rw [ob.assignmentVector_eq_row_projection, htb]
        exact hw
      exact ⟨hta, htb, hva, hwb, hp⟩
  · simp only [dispatch, assignment_state, hphase, dite_eq_right hcutoff]
    exact ⟨rfl, rfl⟩

private theorem arm_downView_of_selection_none
    {x y : RoundInput p rate} (a : DispatchCut x) (b : DispatchCut y)
    (ha : a.selection = none) (hb : b.selection = none) :
    a.arm = b.arm ∧ a.downView = b.downView := by
  simp only [DispatchCut.arm, DispatchCut.downView, ha, hb, Option.map_none]
  trivial

/-- The actual coordinator arm and actual DOWN sender view are constant on
one whole-vector successful-set fibre, including every checked rejection and
all paths on which the actual optional parameters are absent. -/
theorem dispatch_collection_arm_downView_fibre
    (x : RoundInput p rate) (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hf : match parameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
          AssignmentParameterFibreKernel.successfulSlowSet p theta w) :
    (dispatch (withAssignment x v)).arm = (dispatch (withAssignment x w)).arm ∧
      (dispatch (withAssignment x v)).downView = (dispatch (withAssignment x w)).downView := by
  have hp := dispatch_collection_continuations_fibre x payload ledger proposal hphase v w hf
  generalize hl : dispatch (withAssignment x v) = a at hp ⊢
  generalize hr : dispatch (withAssignment x w) = b at hp ⊢
  split at hp
  · rcases hp with ⟨rfl, rfl, rfl, rfl, hstarted, harm, hweights⟩
    simp only [DispatchCut.arm, DispatchCut.downView, DispatchCut.selection, Option.map_some]
    exact ⟨harm, by rw [hstarted, eq_of_heq hweights]⟩
  · rename_i leftCut rightCut pa la ca ua corea ka sa hsa ia hia oa ha da ra aa
      pb lb cb ub coreb kb sb hsb ib hib ob hb db rb ab
    rcases hp with ⟨hta, htb, _, _, hstarted, _, hregisters, _, _, harm, _⟩
    have hta' : ia.time = (withAssignment x v).time := hta
    have htb' : ib.time = (withAssignment x w).time := htb
    simp only [DispatchCut.arm, DispatchCut.downView, DispatchCut.selection,
      selectionAt, dite_eq_left hta', dite_eq_left htb', Option.map_some]
    exact ⟨harm, congrArg some (congrArg₂
      (fun (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
          (started : CoordinatorPhaseClock.StartRoundResult p) =>
        ({ payload := registers.payload
           pendingAtChoice := started.pending
           cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
           complementWeights := registers.complementWeights } :
          ReferenceDownReception.ChoiceTimeView p rate.eta)) hregisters hstarted)⟩
  · exact arm_downView_of_selection_none _ _ hp.1 hp.2

end Bandits.Support.ReferenceLaterDispatchFibre

end
