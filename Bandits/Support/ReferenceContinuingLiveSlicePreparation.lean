/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOccupiedFieldHistory
public import Bandits.Support.ReferenceActiveStepCompositionMeasurability

/-!
# Continuing-live preparation on one DATA slice

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-423`,
`sources/zip4/manuscript/06_interruptions.tex:246-260`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-160`.

The control replacement below changes the complete selected current slice at
the original row and time, while retaining the incoming state, original row
index, reward table, forwards, every other time, and every other row. The
results concern the actual continuing-live dispatcher and DATA-only follower
PREPARE. They make no physical marker law or successful logger claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorStartRoundCutoffDispatch
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.PublicDiscreteDraws

namespace Bandits.Support.ReferenceContinuingLiveSlicePreparation

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- Replace the entire selected row's current continuous slice. -/
def rowAtControl (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : CompletePublicTable.CompleteRow p :=
  (x.row.1, Function.update x.row.2 x.time u)

/-- Replace only the original selected row. -/
def rowsAtControl (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : CompletePublicTable.CompleteRows p :=
  Function.update x.rows x.selected (rowAtControl x u)

/-- The same incoming round with the selected row's complete current slice
replaced. Every other field, including `selected`, is definitionally retained.
-/
def inputAtControl (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : ReferenceActivePhysicalStep.RoundInput p rate :=
  { x with rows := rowsAtControl x u }

private abbrev liveInputAtControl (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (u : ContinuousLearningRows.TimeControl p) : CoordinatorRoundDispatch.LiveInput p := {
  eta := rate.eta
  registers := ReferenceActivePhysicalStep.liveRegistersAt r x.time
  ownedRegisters := ReferenceActivePhysicalStep.liveOwnedAt r q x.time
  followerBaseScore := base
  row := (inputAtControl x u).row }

@[simp] theorem rowAtControl_forward (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (rowAtControl x u).1 = x.row.1 := rfl

@[simp] theorem rowAtControl_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (rowAtControl x u).2 x.time = u := by
  simp [rowAtControl]

theorem rowAtControl_other_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (ht : t ≠ x.time) :
    (rowAtControl x u).2 t = x.row.2 t := by
  simp [rowAtControl, ht]

theorem rowsAtControl_other_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) (j : Fin (M p)) (hj : j ≠ x.selected) :
    rowsAtControl x u j = x.rows j := by
  simp [rowsAtControl, hj]

@[simp] theorem inputAtControl_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (inputAtControl x u).row = rowAtControl x u := by
  simp [inputAtControl, rowsAtControl, ReferenceActivePhysicalStep.RoundInput.row]

@[simp] theorem inputAtControl_state (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (inputAtControl x u).state = x.state := rfl

@[simp] theorem inputAtControl_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (inputAtControl x u).time = x.time := rfl

@[simp] theorem inputAtControl_rewards (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (inputAtControl x u).rewards = x.rewards := rfl

@[simp] theorem inputAtControl_selected (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (inputAtControl x u).selected = x.selected := rfl

@[simp] theorem inputAtControl_active (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) : (inputAtControl x u).active = x.active := rfl

@[simp] theorem inputAtControl_slot (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (u : ContinuousLearningRows.TimeControl p) :
    PublicDiscreteDraws.slotDraw ((inputAtControl x u).row.2 (inputAtControl x u).time).1 =
      PublicDiscreteDraws.slotDraw u.1 := by
  simp

theorem inputAtControl_actual (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    inputAtControl x (x.row.2 x.time) = x := by
  cases x
  simp [inputAtControl, rowsAtControl, rowAtControl,
    ReferenceActivePhysicalStep.RoundInput.row]

/-- The local extension used by the canonical recording kernel: anchors on
the slow assignment and the actual live complement weights on its complement.
-/
def liveSliceWeights (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) : Fin p.K → ℝ := by
  let R := ReferenceActivePhysicalStep.liveRegistersAt r t
  exact fun j => if hj : j ∈ R.payload.slowSet.1 then R.payload.anchor j else
    R.complementWeights ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩

/-- The recording snapshot at a continuing-live cut uses the actual pending
confirmation set and this round's ordinary prepared follower statuses. -/
def liveSliceSnapshot (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (t : Fin p.T)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r t)
      (ReferenceActivePhysicalStep.liveOwnedAt r q t) base)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) :
    ActiveRoundActions.Snapshot r.payload.assignment :=
  { missing := d.startResult.pending, status := fun i => (states i).status }

theorem liveSliceWeights_pos (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) (u : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload
      u
      t (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights) :
    ∀ j, 0 < liveSliceWeights r t j := by
  intro j
  dsimp [liveSliceWeights]
  split_ifs with hj
  · exact hvalid.anchor_pos j
  · exact hvalid.current_weight_pos ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem liveSliceWeights_lower (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) (u : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload
      u
      t (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights) :
    ∀ j, (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.anchor j ≤
      liveSliceWeights r t j := by
  intro j
  dsimp [liveSliceWeights]
  split_ifs with hj
  · exact le_rfl
  · exact hvalid.anchor_le_current ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem liveSliceWeights_upper (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) (u : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload
      u
      t (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights) :
    ∀ j, liveSliceWeights r t j ≤
      2 * (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.anchor j := by
  intro j
  dsimp [liveSliceWeights]
  split_ifs with hj
  · calc
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.anchor j =
          1 * (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.anchor j := by ring
      _ ≤ 2 * (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.anchor j :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (le_of_lt (hvalid.anchor_pos j))
  · exact hvalid.current_le_twice_anchor ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩

/-- The same envelope with the payload field exposed directly for consumers. -/
theorem liveSliceWeights_lower_payload
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) (u : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload u t
      (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights) :
    ∀ j, r.payload.anchor j ≤ liveSliceWeights r t j := by
  intro j
  simpa [ReferenceActivePhysicalStep.liveRegistersAt] using
    liveSliceWeights_lower r t u hvalid j

/-- The upper envelope with the payload field exposed directly for consumers. -/
theorem liveSliceWeights_upper_payload
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) (u : Option (CoordinatorLocalArmChoice.Cutoff p))
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload u t
      (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights) :
    ∀ j, liveSliceWeights r t j ≤ 2 * r.payload.anchor j := by
  intro j
  simpa [ReferenceActivePhysicalStep.liveRegistersAt] using
    liveSliceWeights_upper r t u hvalid j

theorem liveSliceWeights_restrict (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (t : Fin p.T) (j : CanonicalFastSampling.FastArm
      (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.slowSet) :
    liveSliceWeights r t j.1 =
      (ReferenceActivePhysicalStep.liveRegistersAt r t).complementWeights j := by
  have hj : j.1 ∉ (ReferenceActivePhysicalStep.liveRegistersAt r t).payload.slowSet.1 := by
    exact (Finset.mem_sdiff.mp j.2).2
  dsimp [liveSliceWeights]
  rw [ite_eq_right hj]

/-- Reconstruct the actual same-round selection carried by a continuing live
constructor. -/
def continuingSelection (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (_hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (_c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row) :
    ReferenceActivePhysicalStep.Selection x := {
      view := {
        payload := (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
        pendingAtChoice := d.startResult.pending
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
        complementWeights := (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights }
      started := d.startResult
      pending_eq := rfl
      cutoff_eq := rfl
      arm := a.arm
      choice_eq := a.armChoice_eq }

theorem continuingSelection_eq_actual (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a)) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some (continuingSelection x r q base d hs c a) := by
  simp [continuingSelection, hc, ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, ReferenceActivePhysicalStep.liveRegistersAt]

private theorem actual_live_outcome_of_selector
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a)) :
    x.state.coordinator = .live r q base ∧
      CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) =
        .continuingChosen d hs c a := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live r q base (.continuingChosen d hs c a) := by
    calc
      ReferenceActivePhysicalStep.dispatch x = (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .live r q base (.continuingChosen d hs c a) := hc
  cases hstate : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      cases hdispatch
  | live r' q' base' =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate,
        CoordinatorRoundDispatch.dispatch] at hdispatch
      injection hdispatch with hr hq hbase hout
      subst r'
      have hqEq : q' = q := eq_of_heq hq
      subst q'
      subst base'
      exact ⟨rfl, eq_of_heq hout⟩
  | collection payload ledger proposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hcollection : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
        all_goals
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff, cutoff, clock,
            hcollection] at hdispatch
          cases hdispatch
      · simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff] at hdispatch
  | dagger => simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch

private theorem continuing_actual_invariants
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a)) :
    CoordinatorStartRoundCutoffDispatch.dispatch
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base = .ok d ∧
      d.collectionInitialization = .success none ∧
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).queueDomainValid ∧
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).previousServiceDomainValid ∧
      (∀ i, base i ≤ p.T * D p) ∧
      CoordinatorLocalArmChoice.assignmentIsLive r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) x.time ∧
      c.startRoundResult = d.startResult := by
  classical
  have hout := actual_live_outcome_of_selector x r q base d hs c a hc
  let actualOutcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x r q base) :=
    .continuingChosen (x := ReferenceActivePhysicalStep.liveInput x r q base) d hs c a
  have hcode : ReferenceLiveDispatchOutputMeasurability.dataFormula
      (ReferenceActivePhysicalStep.liveInput x r q base) =
        ReferenceLiveDispatchOutputMeasurability.outcomeData
          actualOutcome := by
    calc
      _ = ReferenceLiveDispatchOutputMeasurability.outcomeData
          (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x r q base)) :=
          (ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive _).symm
      _ = _ := congrArg
        (ReferenceLiveDispatchOutputMeasurability.outcomeData
          (x := ReferenceActivePhysicalStep.liveInput x r q base)) hout.2
  -- The proof-free formula preserves the real cutoff dispatch and exposes
  -- every row-independent condition used by the actual continuing branch.
  change ReferenceLiveDispatchOutputMeasurability.dataFormula
      (ReferenceActivePhysicalStep.liveInput x r q base) = _ at hcode
  dsimp only [ReferenceActivePhysicalStep.liveInput] at hcode
  simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData, actualOutcome] at hcode
  cases hcall : CoordinatorStartRoundCutoffDispatch.dispatch
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base with
  | error failure => simp [ReferenceLiveDispatchOutputMeasurability.dataFormula, hcall] at hcode
  | ok out =>
      cases hinitialization : out.collectionInitialization with
      | invalid =>
          simp [ReferenceLiveDispatchOutputMeasurability.dataFormula, hcall,
            hinitialization] at hcode
      | rejected value =>
          simp [ReferenceLiveDispatchOutputMeasurability.dataFormula, hcall,
            hinitialization] at hcode
      | success value =>
          cases value with
          | some ledger =>
              unfold ReferenceLiveDispatchOutputMeasurability.dataFormula at hcode
              simp only [hcall, hinitialization] at hcode
              simp only [ReferenceLiveDispatchOutputMeasurability.choiceData] at hcode
              split_ifs at hcode
          | none =>
              unfold ReferenceLiveDispatchOutputMeasurability.dataFormula at hcode
              simp only [hcall, hinitialization] at hcode
              unfold ReferenceLiveDispatchOutputMeasurability.choiceData at hcode
              by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time) out.startResult
              · simp only [ite_eq_left hframe] at hcode
                by_cases hsigma : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock.sigma =
                    some (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload.sigma
                · simp only [ite_eq_left hsigma] at hcode
                  by_cases hgrid : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary =
                      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock.g
                  · simp only [ite_eq_left hgrid] at hcode
                    by_cases hscore : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).scoreDomainValid
                    · simp only [ite_eq_left hscore] at hcode
                      by_cases hqueue :
                          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).queueDomainValid
                      · simp only [ite_eq_left hqueue] at hcode
                        by_cases hprevious :
                            (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).previousServiceDomainValid
                        · simp only [ite_eq_left hprevious] at hcode
                          by_cases hbase : ∀ i, base i ≤ p.T * D p
                          · simp only [ite_eq_left hbase] at hcode
                            by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                                (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
                                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                  out.startResult.clock.u)
                                (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
                            · simp only [ite_eq_left hlive] at hcode
                              by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
                                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                    out.startResult.clock.u)
                                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
                                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
                              · simp only [ite_eq_left hchoice] at hcode
                                by_cases hboundary : out.startResult.clock.g ≤ p.T + 1
                                · simp only [ite_eq_left hboundary] at hcode
                                  by_cases henvelope :
                                      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementEnvelopeValid
                                  · simp only [ite_eq_left henvelope] at hcode
                                    have hinj := ReferenceLiveDispatchOutputMeasurability.OutcomeData.continuingChosen.inj hcode
                                    rcases hinj with ⟨hdata, hstarted, _⟩
                                    have hout := ReferenceLiveDispatchOutputMeasurability.dispatchData_injective hdata
                                    have hstarted' : c.startRoundResult = d.startResult := by
                                      simpa [hout] using hstarted.symm
                                    subst out
                                    exact ⟨by simp, hinitialization, hqueue, hprevious,
                                      hbase, hlive, hstarted'⟩
                                  · simp only [ite_eq_right henvelope] at hcode
                                    cases hcode
                                · simp only [ite_eq_right hboundary] at hcode
                                  cases hcode
                              · simp only [ite_eq_right hchoice] at hcode
                                cases hcode
                            · simp only [ite_eq_right hlive] at hcode
                              cases hcode
                          · simp only [ite_eq_right hbase] at hcode
                            cases hcode
                        · simp only [ite_eq_right hprevious] at hcode
                          cases hcode
                      · simp only [ite_eq_right hqueue] at hcode
                        cases hcode
                    · simp only [ite_eq_right hscore] at hcode
                      cases hcode
                  · simp only [ite_eq_right hgrid] at hcode
                    cases hcode
                · simp only [ite_eq_right hsigma] at hcode
                  cases hcode
              · simp only [ite_eq_right hframe] at hcode
                cases hcode

/-- For every replacement of the original current control, the real physical
PREPARE still selects the same continuing-live constructor and same clock,
registers, queues, base scores, and cutoff-dispatch output. Only the locally
sampled continuation and its actual arm selector vary. -/
theorem continuing_cut_at_control
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a)) :
    ∀ u : ContinuousLearningRows.TimeControl p,
      ∃ c_u a_u,
        (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).coordinator =
          .live r q base (.continuingChosen d hs c_u a_u) := by
  intro u
  classical
  have hinv := continuing_actual_invariants x r q base d hs c a hc
  rcases hinv with ⟨hcall, hinit, hqueue, hprevious, hbase, hlive, hstartedEq⟩
  let R := ReferenceActivePhysicalStep.liveRegistersAt r x.time
  let localWeights := R.complementWeights
  let cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u
  have hvalid := a.choiceInputsValid
  have hboundary := a.recorderBoundaryValid
  have henvelope := c.recorderInputsValid.2
  let actualChoice := CoordinatorLocalArmChoice.coordinatorArmChoice R.payload
    d.startResult.pending cutoff x.time localWeights (inputAtControl x u).row
  have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
    R.payload d.startResult.pending cutoff x.time localWeights
    (inputAtControl x u).row hvalid
  let arm := actualChoice.getD (⟨0, K_pos p⟩)
  have harm : actualChoice = some arm := by
    cases hchoice : actualChoice with
    | none => exact False.elim (hnonempty hchoice)
    | some value => simp [arm, hchoice]
  have hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame R d.startResult := by
    simpa [hstartedEq] using c.clockFrame
  have hframe' : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) d.startResult := by
    simpa [R] using hframe
  have hlive' : CoordinatorLocalArmChoice.assignmentIsLive
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time := by
    simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hlive
  have hvalid' : CoordinatorLocalArmChoice.ChoiceInputsValid
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights := by
    simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hvalid
  have henvelope' : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementEnvelopeValid := by
    simpa [R, ReferenceActivePhysicalStep.liveRegistersAt] using henvelope
  have hnotnonePrior : CoordinatorLocalArmChoice.coordinatorArmChoice R.payload
      R.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p R.priorClock.u)
      R.time R.complementWeights (inputAtControl x u).row ≠ none :=
    CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none R.payload
      R.pendingAtChoice (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p R.priorClock.u)
      R.time R.complementWeights (inputAtControl x u).row c.choiceInputsValid
  let a_u : CoordinatorRoundDispatch.ArmSelection R.payload d.startResult x.time
      localWeights (inputAtControl x u).row := {
    arm := arm
    choiceInputsValid := hvalid
    recorderBoundaryValid := hboundary
    armChoice_eq := harm }
  let c_u : CoordinatorLiveChoiceRecorderStep.Continuation R (inputAtControl x u).row := {
    startRoundResult := d.startResult
    clockFrame := hframe
    payloadClockStart := c.payloadClockStart
    gridBoundary_eq_clock := c.gridBoundary_eq_clock
    sourceTimeValid := c.sourceTimeValid
    choiceInputsValid := c.choiceInputsValid
    scoreDomainValid := c.scoreDomainValid
    recorderInputsValid := c.recorderInputsValid
    confirmationInputsValid := c.confirmationInputsValid
    currentControl := (inputAtControl x u).row.2 x.time
    currentControl_eq := rfl
    preChoiceMode := c.preChoiceMode
    preChoiceMode_eq := c.preChoiceMode_eq
    armChoice_ne_none := hnotnonePrior }
  have hformula : ReferenceLiveDispatchOutputMeasurability.dataFormula
      (liveInputAtControl x r q base u) =
        ReferenceLiveDispatchOutputMeasurability.OutcomeData.continuingChosen
          (ReferenceLiveDispatchOutputMeasurability.dispatchData d) d.startResult arm := by
    unfold ReferenceLiveDispatchOutputMeasurability.dataFormula
    simp only [liveInputAtControl]
    simp only [hcall, hinit]
    simp only [ite_eq_left hframe', ite_eq_left c.payloadClockStart,
      ite_eq_left c.gridBoundary_eq_clock, ite_eq_left c.scoreDomainValid,
      ite_eq_left hqueue, ite_eq_left hprevious, ite_eq_left hbase]
    have hchoiceRow : CoordinatorLocalArmChoice.coordinatorArmChoice R.payload
        d.startResult.pending cutoff x.time localWeights (inputAtControl x u).row = some arm := by
      change actualChoice = some arm
      exact harm
    simp [ReferenceLiveDispatchOutputMeasurability.choiceData, hlive', hvalid',
      hboundary, henvelope']
    have hchoiceActual : CoordinatorLocalArmChoice.coordinatorArmChoice
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
        (rowAtControl x u) = some arm := by
      simpa [R, cutoff, localWeights, ReferenceActivePhysicalStep.liveRegistersAt,
        inputAtControl_row] using hchoiceRow
    rw [hchoiceActual]
    rfl
  have hinput : ReferenceActivePhysicalStep.liveInput
      (inputAtControl x u) r q base = liveInputAtControl x r q base u := by
    rfl
  have hformulaActual : ReferenceLiveDispatchOutputMeasurability.dataFormula
      (ReferenceActivePhysicalStep.liveInput (inputAtControl x u) r q base) =
        ReferenceLiveDispatchOutputMeasurability.OutcomeData.continuingChosen
          (ReferenceLiveDispatchOutputMeasurability.dispatchData d) d.startResult arm :=
    (congrArg ReferenceLiveDispatchOutputMeasurability.dataFormula hinput).trans hformula
  have houtcome : CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput (inputAtControl x u) r q base) =
        .continuingChosen d hs c_u a_u := by
    apply ReferenceLiveDispatchOutputMeasurability.outcomeData_injective
    rw [ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive]
    exact hformulaActual
  have hstate : (inputAtControl x u).state.coordinator = .live r q base := by
    rw [inputAtControl_state]
    exact (actual_live_outcome_of_selector x r q base d hs c a hc).1
  refine ⟨c_u, a_u, ?_⟩
  calc
    (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).coordinator =
        ReferenceActivePhysicalStep.dispatch (inputAtControl x u) :=
      (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).coordinator_eq
    _ = .live r q base (.continuingChosen d hs c_u a_u) := by
      have hstateOriginal : x.state.coordinator = .live r q base :=
        (actual_live_outcome_of_selector x r q base d hs c a hc).1
      have hinputState : (inputAtControl x u).state.coordinator = .live r q base := by
        simpa only [inputAtControl_state] using hstateOriginal
      change ReferenceActivePhysicalStep.dispatch (inputAtControl x u) = _
      simp only [ReferenceActivePhysicalStep.dispatch, hinputState,
        CoordinatorRoundDispatch.dispatch]
      exact congrArg (ReferenceActivePhysicalStep.DispatchCut.live r q base) houtcome

/-- On a DATA replacement, every follower's actual PREPARE keeps the same
ordinary state and proposal memory. The original successful StartRound is
recovered from the actual ordinary selector; its checked domain makes the
DATA replacement's UP offer a genuine `noOffer`, while DATA makes the local
arm choice total for both unoccupied pilots and occupied DOWN records. -/
theorem data_preparation_at_control
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i)) :
    ∀ u : ContinuousLearningRows.TimeControl p,
      PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
      ∀ i, ((ReferenceActivePhysicalStep.prepare (inputAtControl x u)).followers.followers i).configuration =
        .ordinary (states i) (memories i) := by
  intro u hdata i
  have hordinary := ho i
  obtain ⟨before, beforeMemory, _offered, hinput, hstart, hchoice⟩ :=
    ReferenceActiveDataOwnership.prepare_ordinary_choice i x.row
      (x.state.activations i) x.time (x.active i) (x.state.followers i)
      (states i) (memories i) hordinary
  have hlocal : ActiveFollowerLifecycle.localStateDomainValid before := by
    by_contra hbad
    have hreject := ActiveFollowerLifecycle.interruptionDecision_invalid_domain
      rate.eta x.time before beforeMemory hbad
    simp [ActiveFollowerLifecycle.startRound, hreject] at hstart
  have hdomainBefore : ActiveFollowerQueueOperation.stateInputDomain before := by
    rcases hlocal with ⟨hregisters, hbuffer, _⟩
    rcases hregisters with ⟨hS, hdelta, hbacklog⟩
    rcases hbuffer with ⟨htimestamps, hkeys, _⟩
    exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩
  have hstartFrame := ActiveFollowerLifecycle.startRound_frame rate.eta x.time
    before (states i) beforeMemory (memories i) hstart
  have hdomainState : ActiveFollowerQueueOperation.stateInputDomain (states i) := by
    rcases hdomainBefore with ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩
    rcases hstartFrame with ⟨_, hS', hdelta', hbacklog', _, hbuffer', _, _⟩
    change (states i).S ≤ p.T * D p ∧ (states i).delta ≤ D p ∧
      (states i).backlog ≤ p.T * D p ∧
      (∀ record ∈ (states i).buffer, 1 ≤ record.calendarRound ∧
        record.calendarRound ≤ p.T) ∧
      ((states i).buffer.map ActiveFollowerQueueOperation.bufferKey).Nodup
    rw [hS', hdelta', hbacklog', hbuffer']
    exact ⟨hS, hdelta, hbacklog, htimestamps, hkeys⟩
  have hnotUp : ¬ ActiveFollowerQueueOperation.selectedUpRound i
      (inputAtControl x u).row (x.state.activations i) x.time := by
    intro hselectedUp
    have hslotUp : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.upSlot := by
      simpa only [inputAtControl_row, rowAtControl_time, inputAtControl_time] using hselectedUp.2.1
    exact (by decide : PublicDiscreteDraws.upSlot ≠ PublicDiscreteDraws.dataSlot)
      (hslotUp.symm.trans hdata)
  have hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (inputAtControl x u).row (x.state.activations i) x.time (states i) = .noOffer := by
    apply ActiveFollowerQueueOperation.checkedUpOffer_noOffer rate.eta i
      (inputAtControl x u).row (x.state.activations i) x.time (states i) hdomainState
    intro h
    exact hnotUp h.1
  have hdataAtTime : PublicDiscreteDraws.slotDraw
      (((inputAtControl x u).row).2 x.time).1 = PublicDiscreteDraws.dataSlot := by
    simpa only [inputAtControl_row, rowAtControl_time] using hdata
  have hchoiceData : ∃ arm, ActiveFollowerArmChoice.followerArmChoice
      (states i) (inputAtControl x u).row x.time i none = some arm := by
    by_cases hu : (states i).status = .unoccupied
    · refine ⟨PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) (((inputAtControl x u).row).2 x.time).1, ?_⟩
      simpa [ActiveFollowerArmChoice.followerArmChoice, inputAtControl_row,
        rowAtControl_time] using
        ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
          (states i) (((inputAtControl x u).row).2 x.time) i none hu hdataAtTime
    · have hlast : ∃ M, (states i).lastDown = some M := by
        cases hM : (states i).lastDown with
        | none =>
            simp [ActiveFollowerArmChoice.followerArmChoice,
              ActiveFollowerArmChoice.followerArmChoiceCore, hu, hM] at hchoice
        | some M => exact ⟨M, rfl⟩
      rcases hlast with ⟨M, hM⟩
      refine ⟨PrelaunchBufferRecovery.downArm rate.eta M, ?_⟩
      simp [ActiveFollowerArmChoice.followerArmChoice,
        ActiveFollowerArmChoice.followerArmChoiceCore, hu, hM, hdata,
        inputAtControl_row, rowAtControl_time]
  rcases hchoiceData with ⟨arm, hchoiceData⟩
  have hoffRow : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i
      (rowAtControl x u) (x.state.activations i) x.time (states i) = .noOffer := by
    simpa only [inputAtControl_row] using hoff
  have hchoiceDataRow : ActiveFollowerArmChoice.followerArmChoice
      (states i) (rowAtControl x u) x.time i none = some arm := by
    simpa only [inputAtControl_row] using hchoiceData
  change (DeclaredFollowerLocalRound.prepare rate i (inputAtControl x u).row
      (x.state.activations i) x.time (x.active i) (x.state.followers i)).configuration =
    .ordinary (states i) (memories i)
  simp [DeclaredFollowerLocalRound.prepare, hinput, hstart, hoffRow, hchoiceDataRow]

/-- Every DATA replacement preserves the same actual continuing-live
selection, ordinary follower preparation, and action profile prescribed by
the existing fixed-slice recording kernel. The global extension is anchored
on the payload slow set and equals the actual complement weights elsewhere.
Sources: `05_binary_transport.tex:354-423` and
`04_slow_fast_learner.tex:140-160`. -/
theorem data_actions_at_control
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i)) :
    ∀ u : ContinuousLearningRows.TimeControl p,
      PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot →
      ∃ c_u a_u,
        (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).coordinator =
          .live r q base (.continuingChosen d hs c_u a_u) ∧
        ∀ player : Fin p.m,
          (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).arms.actions player =
            SnapshotRecordingKernel.dataAction p
              (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
              (liveSliceWeights r x.time)
              r.payload.anchor_pos
              (liveSliceWeights_pos r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (liveSliceWeights_lower_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (liveSliceWeights_upper_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              u.1 player := by
  intro u hdata
  rcases continuing_cut_at_control x r q base d hs c a hc u with ⟨c_u, a_u, hctor⟩
  have hinv := continuing_actual_invariants x r q base d hs c a hc
  rcases hinv with ⟨_, _, _, _, _, hlive, _⟩
  have hweightsPos : ∀ j, 0 < liveSliceWeights r x.time j :=
    liveSliceWeights_pos r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid
  have hweightsLower : ∀ j, r.payload.anchor j ≤ liveSliceWeights r x.time j :=
    liveSliceWeights_lower r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid
  have hweightsUpper : ∀ j, liveSliceWeights r x.time j ≤ 2 * r.payload.anchor j :=
    liveSliceWeights_upper r x.time
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      a.choiceInputsValid
  have hweightsLowerRoot : ∀ j, r.payload.anchor j ≤ liveSliceWeights r x.time j := by
    intro j
    simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hweightsLower j
  have hweightsUpperRoot : ∀ j, liveSliceWeights r x.time j ≤ 2 * r.payload.anchor j := by
    intro j
    simpa [ReferenceActivePhysicalStep.liveRegistersAt] using hweightsUpper j
  have hweightsRestrict : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights =
      fun j => liveSliceWeights r x.time j.1 := by
    funext j
    exact (liveSliceWeights_restrict r x.time j).symm
  have hdataAtTime : PublicDiscreteDraws.slotDraw
      (((inputAtControl x u).row).2 x.time).1 = PublicDiscreteDraws.dataSlot := by
    simpa only [inputAtControl_row, rowAtControl_time] using hdata
  have hcurrent : c_u.currentControl = u := by
    simpa [ReferenceActivePhysicalStep.liveInput, inputAtControl_time,
      ReferenceActivePhysicalStep.liveRegistersAt, inputAtControl_row,
      rowAtControl_time] using c_u.currentControl_eq
  have hselectedSlot : PublicDiscreteDraws.slotDraw c_u.currentControl.1 =
      PublicDiscreteDraws.dataSlot := by
    simpa [hcurrent] using hdata
  have hchoiceCore : CoordinatorLocalArmChoice.coordinatorArmChoiceCore
      r.payload d.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
      c_u.currentControl = some a_u.arm := by
    have hchoice := a_u.armChoice_eq
    change CoordinatorLocalArmChoice.coordinatorArmChoiceCore
      (liveInputAtControl x r q base u).registers.payload d.startResult.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
      (liveInputAtControl x r q base u).registers.time
      (liveInputAtControl x r q base u).registers.complementWeights
      ((liveInputAtControl x r q base u).row.2
        (liveInputAtControl x r q base u).registers.time) = some a_u.arm at hchoice
    simpa [liveInputAtControl, ReferenceActivePhysicalStep.liveRegistersAt,
      inputAtControl_time, inputAtControl_row, rowAtControl_time, hcurrent] using hchoice
  refine ⟨c_u, a_u, hctor, ?_⟩
  intro player
  by_cases hcoordinator : player = ActiveRoundActions.coordinator p.two_le_m
  · subst player
    have hactualArm : (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) = a_u.arm := by
      rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator, hctor]
      simp [ReferenceActivePhysicalStep.DispatchCut.arm,
        ReferenceActivePhysicalStep.DispatchCut.selection,
        ReferenceActivePhysicalStep.selectionAt]
    rw [hactualArm]
    by_cases hempty : d.startResult.pending = ∅
    · have hbranch := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty
        r.payload d.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
        c_u.currentControl a.choiceInputsValid hlive hempty
      have harm : a_u.arm =
          (CoordinatorLocalArmChoice.localFastDraw r.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
            a.choiceInputsValid c_u.currentControl).1 :=
        Option.some.inj (hchoiceCore.symm.trans hbranch)
      have hdraw := CoordinatorLocalArmChoice.localFastDraw_eq_canonical r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
        a.choiceInputsValid (liveSliceWeights r x.time)
        hweightsPos hweightsLowerRoot hweightsUpperRoot hweightsRestrict c_u.currentControl
      have hdrawValue := congrArg Subtype.val hdraw
      have hset : SnapshotRecordingKernel.assignmentSlowSet p r.payload.assignment =
          r.payload.slowSet :=
        CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload r.payload
      have hmissing : (liveSliceSnapshot r q base x.time d states).missing = ∅ := by
        exact hempty
      have hkernel : SnapshotRecordingKernel.dataAction p
          (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
          (liveSliceWeights r x.time) r.payload.anchor_pos hweightsPos
          hweightsLowerRoot hweightsUpperRoot u.1 (ActiveRoundActions.coordinator p.two_le_m) =
            (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
              r.payload.anchor (liveSliceWeights r x.time) r.payload.anchor_pos
              hweightsPos hweightsLowerRoot hweightsUpperRoot r.payload.slowSet
              (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).1 := by
        change (if d.startResult.pending = ∅ then _ else _) = _
        rw [ite_eq_left hempty, hset]
      calc
        a_u.arm = (CoordinatorLocalArmChoice.localFastDraw r.payload
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
            a.choiceInputsValid c_u.currentControl).1 := harm
        _ = (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property rate.sourceCap
            r.payload.anchor (liveSliceWeights r x.time) r.payload.anchor_pos
            hweightsPos hweightsLowerRoot hweightsUpperRoot r.payload.slowSet
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1)).1 := by
              simpa [hcurrent] using hdrawValue
        _ = SnapshotRecordingKernel.dataAction p
            (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
            rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
            (liveSliceWeights r x.time) r.payload.anchor_pos hweightsPos
            hweightsLowerRoot hweightsUpperRoot u.1 (ActiveRoundActions.coordinator p.two_le_m) :=
              hkernel.symm
    · have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) x.time ∧
          d.startResult.pending = ∅) := by
        intro h
        exact hempty h.2
      have hbranch := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data
        r.payload d.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        x.time (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
        c_u.currentControl a.choiceInputsValid hnotfast hselectedSlot
      have hpilot : a_u.arm = PublicDiscreteDraws.pilotDraw
          (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m) u.1 := by
        have hpilotCurrent : a_u.arm = PublicDiscreteDraws.pilotDraw
            (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
            c_u.currentControl.1 := Option.some.inj (hchoiceCore.symm.trans hbranch)
        simpa [hcurrent] using hpilotCurrent
      have hkernel : SnapshotRecordingKernel.dataAction p
          (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
          (liveSliceWeights r x.time) r.payload.anchor_pos hweightsPos
          hweightsLowerRoot hweightsUpperRoot u.1 (ActiveRoundActions.coordinator p.two_le_m) =
            PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p)
              (ActiveRoundActions.coordinator p.two_le_m) u.1 := by
        change (if d.startResult.pending = ∅ then _ else _) = _
        rw [ite_eq_right hempty]
      exact hpilot.trans hkernel.symm
  · let i := ActiveRoundActions.followerIndex p.two_le_m player hcoordinator
    have hi : PublicDiscreteDraws.followerPlayer p.two_le_m i = player :=
      ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hcoordinator
    have hprepared := data_preparation_at_control x states memories ho u hdata i
    have hdataArm := ReferenceActiveDataOwnership.ordinary_data_arm r.payload i
      (inputAtControl x u).row (x.state.activations i) x.time (x.active i)
      (x.state.followers i) (states i) (memories i) hprepared (hf i) hdataAtTime
    have hsourceNe : PublicDiscreteDraws.followerPlayer p.two_le_m i ≠
        ActiveRoundActions.coordinator p.two_le_m :=
      ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
    have hsourceIndex : ActiveRoundActions.followerIndex p.two_le_m
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) hsourceNe = i :=
      ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hsourceNe
    have hindexPlayer : ActiveRoundActions.followerIndex p.two_le_m player hcoordinator = i := rfl
    have hactualFollowerArm :
        (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).arms.actions player =
          (DeclaredFollowerLocalRound.prepare rate i (inputAtControl x u).row
            (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm := by
      rw [← hi]
      exact ReferenceActivePhysicalStep.PreparedRound.action_follower
        (ReferenceActivePhysicalStep.prepare (inputAtControl x u)) i
    have hdataArm' :
        (DeclaredFollowerLocalRound.prepare rate i (inputAtControl x u).row
          (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm =
          if (states i).status = .unoccupied then
            PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player u.1
          else r.payload.assignment.assigned i := by
      simpa [inputAtControl_row, rowAtControl_time, hi] using hdataArm
    by_cases hunoccupied : (states i).status = .unoccupied
    · have hkernel : SnapshotRecordingKernel.dataAction p
          (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
          (liveSliceWeights r x.time) r.payload.anchor_pos hweightsPos
          hweightsLowerRoot hweightsUpperRoot u.1 player =
            PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player u.1 := by
        simp [SnapshotRecordingKernel.dataAction, hcoordinator, hindexPlayer,
          liveSliceSnapshot, hunoccupied]
      have harm :
          (DeclaredFollowerLocalRound.prepare rate i (inputAtControl x u).row
            (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm =
            PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player u.1 := by
        simpa [hunoccupied] using hdataArm'
      exact hactualFollowerArm.trans (harm.trans hkernel.symm)
    · have hkernel : SnapshotRecordingKernel.dataAction p
          (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
          (liveSliceWeights r x.time) r.payload.anchor_pos hweightsPos
          hweightsLowerRoot hweightsUpperRoot u.1 player =
            r.payload.assignment.assigned i := by
        simp [SnapshotRecordingKernel.dataAction, hcoordinator, hindexPlayer,
          liveSliceSnapshot, hunoccupied]
      have harm :
          (DeclaredFollowerLocalRound.prepare rate i (inputAtControl x u).row
            (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm =
            r.payload.assignment.assigned i := by
        simpa [hunoccupied] using hdataArm'
      exact hactualFollowerArm.trans (harm.trans hkernel.symm)

/-- A pointwise canonical DATA recording atom identifies the actual owner,
action, ownership, and pilot mask on the same replacement slice. The real
simultaneous action geometry then gives the owner's actual grid feedback and
typed observation, including the zero-reward case. -/
theorem data_owner_feedback_at_control
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i))
    (u : ContinuousLearningRows.TimeControl p)
    (hdata : PublicDiscreteDraws.slotDraw u.1 = PublicDiscreteDraws.dataSlot)
    (arm : Fin p.K)
    (hrecording : SnapshotRecordingKernel.recordingMap p
      (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
      true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
      (liveSliceWeights r x.time) r.payload.anchor_pos
      (liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      ((inputAtControl x u).row.2 (inputAtControl x u).time).1 = some arm) :
    let owner := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
        ((inputAtControl x u).row.2 (inputAtControl x u).time).1)
    (ReferenceActivePhysicalStep.prepare (inputAtControl x u)).feedback.feedback owner =
        x.rewards x.time arm ∧
      ((ReferenceActivePhysicalStep.prepare (inputAtControl x u)).feedback.observations owner).val.val =
        ((x.rewards x.time arm).val : ℝ) / (D p : ℝ) := by
  classical
  let y := inputAtControl x u
  rcases data_actions_at_control x r q base d hs c a hc states memories ho hf u hdata with
    ⟨c_u, a_u, hctor, hactions⟩
  let selected := continuingSelection y r q base d hs c_u a_u
  have hselected := continuingSelection_eq_actual y r q base d hs c_u a_u hctor
  have hinvariants := continuing_actual_invariants y r q base d hs c_u a_u hctor
  rcases hinvariants with ⟨_, _, _, _, _, hlive, _⟩
  have hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i) := by
    intro i hoccupied
    simpa [selected, continuingSelection, ReferenceActivePhysicalStep.liveRegistersAt] using
      hf i hoccupied
  have hordinary := data_preparation_at_control x states memories ho u hdata
  have hdataY : PublicDiscreteDraws.slotDraw (y.row.2 y.time).1 =
      PublicDiscreteDraws.dataSlot := by
    simpa [y, inputAtControl_row, inputAtControl_time, rowAtControl_time] using hdata
  have hmapFacts := (SnapshotRecordingKernel.recordingMap_some_iff p
      (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
      rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
      (liveSliceWeights r x.time) r.payload.anchor_pos
      (liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (y.row.2 y.time).1 arm).mp hrecording
  rcases hmapFacts with ⟨_, hkernelAction, hownsMap, hmask, _⟩
  let owner := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
      (y.row.2 y.time).1)
  have haction : (ReferenceActivePhysicalStep.prepare y).arms.actions owner = arm := by
    calc
      (ReferenceActivePhysicalStep.prepare y).arms.actions owner =
          SnapshotRecordingKernel.dataAction p
            (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
            rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
            (liveSliceWeights r x.time) r.payload.anchor_pos
            (liveSliceWeights_pos r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (liveSliceWeights_lower_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (liveSliceWeights_upper_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            u.1 owner := by
              simpa [y, inputAtControl_time, inputAtControl_row, rowAtControl_time] using
                hactions owner
      _ = SnapshotRecordingKernel.dataAction p
            (.live r.payload.assignment (liveSliceSnapshot r q base x.time d states))
            rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
            (liveSliceWeights r x.time) r.payload.anchor_pos
            (liveSliceWeights_pos r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (liveSliceWeights_lower_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (liveSliceWeights_upper_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (y.row.2 y.time).1 owner := by
              simp [y, inputAtControl_time, inputAtControl_row, rowAtControl_time]
      _ = arm := hkernelAction
  have howns : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment
        (ReferenceActiveDataOwnership.choiceSnapshot selected states)) owner arm := by
    simpa [selected, continuingSelection, ReferenceActivePhysicalStep.liveRegistersAt,
      ReferenceActiveDataOwnership.choiceSnapshot, liveSliceSnapshot] using hownsMap
  have hactual := ReferenceActiveDataOwnership.actual_data_owner_feedback y selected hselected
    states memories hordinary hfields hlive hdataY owner arm haction howns hmask
  simpa [owner, y, inputAtControl_rewards, inputAtControl_time,
    inputAtControl_row, rowAtControl_time] using hactual

/-- A checked DATA marker on an actual full-table run record gives the
recording source the complete current grid reward and the matching numerical
observation. The source, original selected row, full rows, and full reward
table remain those of `ReferenceActivePhysicalHorizon.run`. Occupied DOWN
fields are derived from O's prefix history at this record; they are not input
premises. -/
theorem run_record_continuing_data_slice
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i s memory, initial.followers i = .ordinary s memory →
      s.status = .unoccupied)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards
      start count hspan active).records)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time
      r.priorClock r.clockPending = .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time) record.input.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).payload
      d.startResult record.input.time
      (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
      record.input.row)
    (hc : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (arm : Fin p.K)
    (hrecording : SnapshotRecordingKernel.recordingMap p
      (.live r.payload.assignment
        (liveSliceSnapshot r q base record.input.time d states))
      true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
      (liveSliceWeights r record.input.time) r.payload.anchor_pos
      (liveSliceWeights_pos r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_lower_payload r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_upper_payload r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (record.input.row.2 record.input.time).1 = some arm) :
    let owner := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
        (record.input.row.2 record.input.time).1)
    record.gridFeedback owner = rewards record.input.time arm ∧
      ReferenceActivePhysicalHorizon.observationValue (record.ownEntries owner).2 =
        ((rewards record.input.time arm).val : ℝ) / (D p : ℝ) := by
  let selected := continuingSelection record.input r q base d hs c a
  have hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected := by
    exact continuingSelection_eq_actual record.input r q base d hs c a hc
  have hselectedOutput : record.output.preparation.coordinator.selection = some selected := by
    simpa [record.output_eq, ReferenceActivePhysicalStep.step] using hselected
  have hhistory := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history
    initial rows J rewards start count hspan active hfirst hseed count le_rfl
  have hfieldsPreparedOutput :=
    (hhistory.2 record hrecord selected hselectedOutput).2.1
  have hfieldsPrepared : ∀ i,
      ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
        ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration := by
    intro i
    simpa [record.output_eq, ReferenceActivePhysicalStep.step] using hfieldsPreparedOutput i
  have hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i) := by
    intro i hoccupied
    have hfield := hfieldsPrepared i
    rw [ho i] at hfield
    change (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i) at hfield
    have hfield' : (states i).status ≠ .unoccupied →
        (states i).lastDown = some (r.payload.downRecord i) := by
      simpa [selected, continuingSelection, ReferenceActivePhysicalStep.liveRegistersAt] using hfield
    exact hfield' hoccupied
  have hslot := ((SnapshotRecordingKernel.recordingMap_some_iff p
      (.live r.payload.assignment
        (liveSliceSnapshot r q base record.input.time d states))
      rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
      (liveSliceWeights r record.input.time) r.payload.anchor_pos
      (liveSliceWeights_pos r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_lower_payload r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_upper_payload r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (record.input.row.2 record.input.time).1 arm).mp hrecording).1
  have hdata : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.dataSlot := by
    simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
  let u : ContinuousLearningRows.TimeControl p := record.input.row.2 record.input.time
  have hrecordingAtControl : SnapshotRecordingKernel.recordingMap p
      (.live r.payload.assignment
        (liveSliceSnapshot r q base record.input.time d states))
      true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
      (liveSliceWeights r record.input.time) r.payload.anchor_pos
      (liveSliceWeights_pos r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_lower_payload r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (liveSliceWeights_upper_payload r record.input.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      ((inputAtControl record.input u).row.2 (inputAtControl record.input u).time).1 = some arm := by
    simpa [u, inputAtControl_row, rowAtControl_time] using hrecording
  have hfeedbackAtControl := data_owner_feedback_at_control record.input r q base d hs c a hc
    states memories ho hf u hdata arm hrecordingAtControl
  let owner := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
      (record.input.row.2 record.input.time).1)
  have hinput : inputAtControl record.input u = record.input := by
    simpa [u] using inputAtControl_actual record.input
  have hfeedbackSlice :
      (ReferenceActivePhysicalStep.prepare (inputAtControl record.input u)).feedback.feedback owner =
        record.input.rewards record.input.time arm := by
    simpa [u, inputAtControl_row, rowAtControl_time] using hfeedbackAtControl.1
  have hfeedbackPrepared :
      (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback owner =
        record.input.rewards record.input.time arm := by
    calc
      _ = (ReferenceActivePhysicalStep.prepare (inputAtControl record.input u)).feedback.feedback owner :=
        (congrArg
          (fun z : ReferenceActivePhysicalStep.RoundInput p rate =>
            (ReferenceActivePhysicalStep.prepare z).feedback.feedback owner) hinput).symm
      _ = _ := hfeedbackSlice
  have hrunInputs := ReferenceActivePhysicalHorizon.run_record_inputs initial rows J rewards
    start count hspan active record hrecord
  have hrewardInput : record.input.rewards record.input.time arm =
      rewards record.input.time arm :=
    congrArg (fun table : ActualInitializationPhysicalStep.GridRewardTable p =>
      table record.input.time arm) hrunInputs.2.2
  have hgrid : record.gridFeedback owner = rewards record.input.time arm := by
    unfold ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback
    rw [record.output_eq]
    exact hfeedbackPrepared.trans hrewardInput
  constructor
  · exact hgrid
  · unfold ReferenceActivePhysicalHorizon.RoundRecord.ownEntries
      ReferenceActivePhysicalHorizon.observationValue
    rw [record.output_eq, ReferenceActivePhysicalStep.step_own_entry]
    change (ActualInitializationPhysicalStep.observationOfGrid p
      ((ReferenceActivePhysicalStep.prepare record.input).feedback.feedback owner)).val.val = _
    rw [ActualInitializationPhysicalStep.observationOfGrid_value, hfeedbackPrepared,
      hrewardInput]

/-- The same DATA feedback conclusion on the original source-derived launch
run. Every initialization, clean-prefix, generated-DOWN, forcing, and actual
handoff condition remains explicit; the admitted launch history supplies the
first tag and ordinary unoccupied seed consumed by the real-run theorem above.
-/
theorem ofActualLaunchedBoundary_record_continuing_data_slice
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : ReferenceActivePhysicalStep.RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      (count + 1) ≤ p.T) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start :=
      fun player => ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
        source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
        hlaunched player
    ∀ record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
      record ∈ (ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
        span active).records →
      ∀ r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta,
        ∀ q : CoordinatorLiveServiceFinish.OwnedRegisters r,
        ∀ base : Fin (p.m - 1) → ℕ,
        ∀ d : CoordinatorStartRoundCutoffDispatch.Output
          (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
          (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base,
        ∀ hs : CoordinatorPhaseClock.startRound p rate.eta.val record.input.time r.priorClock
          r.clockPending = .ok d.startResult,
        ∀ c : CoordinatorLiveChoiceRecorderStep.Continuation
          (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time) record.input.row,
        ∀ a : CoordinatorRoundDispatch.ArmSelection
          (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).payload
          d.startResult record.input.time
          (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
          record.input.row,
        (ReferenceActivePhysicalStep.prepare record.input).coordinator =
          .live r q base (.continuingChosen d hs c a) →
        ∀ states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
          ∀ memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
          (∀ i,
            ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
              .ordinary (states i) (memories i)) →
          ∀ arm : Fin p.K,
            SnapshotRecordingKernel.recordingMap p
              (.live r.payload.assignment
                (liveSliceSnapshot r q base record.input.time d states))
              true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
              (liveSliceWeights r record.input.time) r.payload.anchor_pos
              (liveSliceWeights_pos r record.input.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (liveSliceWeights_lower_payload r record.input.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (liveSliceWeights_upper_payload r record.input.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (record.input.row.2 record.input.time).1 = some arm →
            let owner := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
              (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.rec
                (record.input.row.2 record.input.time).1)
            record.gridFeedback owner = rewards record.input.time arm ∧
              ReferenceActivePhysicalHorizon.observationValue
                (record.ownEntries owner).2 =
                  ((rewards record.input.time arm).val : ℝ) / (D p : ℝ) := by
  intro initial start active record hrecord
  have hboundary := ReferenceOccupiedFieldHistory.ofActualLaunchedBoundary_occupied_field_history
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched count span
  rcases hboundary with ⟨hfirst, hfollowers, _hactive, _⟩
  have hseed : ∀ i state memory, initial.followers i = .ordinary state memory →
      state.status = .unoccupied := by
    intro i state memory hconfiguration
    obtain ⟨first, firstMemory, hfirstConfig, _, hunoccupied⟩ := hfollowers i
    have hstate : first = state := by
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hfirstConfig.symm.trans hconfiguration)).1
    simpa [hstate] using hunoccupied
  exact fun r q base d hs c a hc states memories ho arm hrecording =>
    run_record_continuing_data_slice initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (count + 1)
      span active hfirst hseed record hrecord r q base d hs c a hc states memories ho
      arm hrecording

end Bandits.Support.ReferenceContinuingLiveSlicePreparation

end
