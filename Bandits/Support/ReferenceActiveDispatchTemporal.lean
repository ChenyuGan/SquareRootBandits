/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStep

/-!
# Current-control locality of the active coordinator dispatch data

Literal argument projections of the accepted physical step. Source motivation:
`sources/zip4/manuscript/06_interruptions.tex:197-209,235-297,376-423`,
`appendix_a_local_protocol.tex:6-14`, `appendix_b_communication.tex:25-55`, and
`08_main_theorem.tex:29-42` (the last three under the same manuscript directory).
The entire original tables and reward arrays remain inputs. These internal
deterministic comparisons assert no probability law or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceActiveDispatchTemporal


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal four arguments of the live observation continuation. -/
abbrev LiveArgs (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Sigma (fun r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta => CoordinatorLiveServiceFinish.OwnedRegisters r ×
    ((Fin (p.m - 1) → ℕ) × CoordinatorPhaseClock.StartRoundResult p))

/-- The literal four arguments of the collection observation continuation. -/
abbrev CollectionArgs (p : Parameters) (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Sigma (fun payload : ReferenceActivePhysicalStep.Payload rate => ReferenceActivePhysicalStep.Ledger rate ×
    (CoordinatorPhaseClock.StartRoundResult p × (CanonicalFastSampling.FastArm payload.slowSet → ℝ)))

/-- Exactly the guard and branch arguments of `ReferenceActivePhysicalStep.PreparedRound.observeCoordinator`.
The first unit is dagger; the second is dispatch rejection. -/
def tailArgs {x : ReferenceActivePhysicalStep.RoundInput p rate} (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate)) := by
  classical
  if cut.selection = none then
    exact match cut with
    | .dagger => .inl ()
    | _ => .inr (.inl ())
  else
    match cut with
    | .first (.chosen installed _) =>
        exact .inr (.inr (.inl ⟨installed.registers, installed.ownedRegisters,
          installed.followerBaseScore, installed.startRoundResult⟩))
    | .live r q base (.continuingChosen dispatched _ _ _) =>
        exact .inr (.inr (.inl ⟨ReferenceActivePhysicalStep.liveRegistersAt r x.time, ReferenceActivePhysicalStep.liveOwnedAt r q x.time,
          base, dispatched.startResult⟩))
    | .live r _ _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        exact .inr (.inr (.inr ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
          dispatched.startResult, (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights⟩))
    | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
        let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
        exact .inr (.inr (.inr ⟨payload, ledger, snapshot.clockStarted,
          CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩))
    | .collection _ _ _ _ (.laterChosen _ _ started _ _ _ _ _ _ installed _) =>
        exact .inr (.inr (.inl ⟨installed.registers, installed.ownedRegisters,
          installed.retainedBaseScore, started⟩))
    | _ => exact .inr (.inl ())

/-- Arm, DOWN view, and the literal row-free observation continuation arguments. -/
def cutData {x : ReferenceActivePhysicalStep.RoundInput p rate} (cut : ReferenceActivePhysicalStep.DispatchCut x) :=
  (cut.arm, cut.downView, tailArgs cut)

/-- Project the existing dispatch; no new dispatcher or state is constructed. -/
def dispatchData (x : ReferenceActivePhysicalStep.RoundInput p rate) := cutData (ReferenceActivePhysicalStep.dispatch x)

/-- Literal successful live-branch arguments, before adjoining the physical cut.
All failures have exactly the observation consumer's dispatch-rejection readout. -/
def liveOutcomeData (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row }) :
    Fin p.K × Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      (Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate))) :=
  match out with
  | .continuingChosen dispatched _ _ selected =>
      (selected.arm, some ⟨r.payload, dispatched.startResult.pending,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u,
        r.complementWeights⟩,
        .inr (.inr (.inl ⟨r, q, base, dispatched.startResult⟩)))
  | .cutoffChosen dispatched _ ledger _ _ _ _ _ _ selected =>
      (selected.arm, some ⟨r.payload, dispatched.startResult.pending,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u,
        r.complementWeights⟩,
        .inr (.inr (.inr ⟨r.payload, ReferenceActivePhysicalStep.sharedLedger ledger,
          dispatched.startResult, r.complementWeights⟩)))
  | _ => (ReferenceActivePhysicalStep.coordinatorFallback p, none, .inr (.inl ()))

theorem liveOutcomeData_eq_of_current
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (row otherRow : CompletePublicTable.CompleteRow p)
    (hc : row.2 r.time = otherRow.2 r.time) :
    liveOutcomeData r q base row (CoordinatorRoundDispatch.dispatchLive
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row }) =
    liveOutcomeData r q base otherRow (CoordinatorRoundDispatch.dispatchLive
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := otherRow }) := by
  classical
  unfold CoordinatorRoundDispatch.dispatchLive
  dsimp only
  split
  · rename_i failure hdispatch
    rfl
  · rename_i dispatched hdispatch
    split
    · rfl
    · rfl
    · rename_i hinit
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h11
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h10
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h9
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h8
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h7
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h6
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h5
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h4
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h3
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h2
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h1
      have heq := CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
        r.payload dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
        r.time r.complementWeights row otherRow hc
      split
      · rename_i hselected
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          r.payload dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          r.time r.complementWeights row (by assumption) hselected)
      · rename_i arm hselected
        split
        · rename_i hother
          have hsome : some arm = none := hselected.symm.trans (heq.trans hother)
          exact False.elim (Option.some_ne_none _ hsome)
        · rename_i otherArm hother
          have harm : arm = otherArm := Option.some.inj (hselected.symm.trans (heq.trans hother))
          subst otherArm
          rfl
    · rename_i ledger hinit
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h3
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h2
      conv_lhs => rw [apply_dite (liveOutcomeData r q base row)]
      conv_rhs => rw [apply_dite (liveOutcomeData r q base otherRow)]
      congr 1
      funext h1
      have heq := CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
        r.payload dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
        r.time r.complementWeights row otherRow hc
      split
      · rename_i hselected
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          r.payload dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          r.time r.complementWeights row (by assumption) hselected)
      · rename_i arm hselected
        split
        · rename_i hother
          have hsome : some arm = none := hselected.symm.trans (heq.trans hother)
          exact False.elim (Option.some_ne_none _ hsome)
        · rename_i otherArm hother
          have harm : arm = otherArm := Option.some.inj (hselected.symm.trans (heq.trans hother))
          subst otherArm
          rfl

/-- Only the successful later-start fields read by the register installation.
The row-indexed success object itself is deliberately retained by its caller. -/
def laterResultData (old : ReferenceActivePhysicalStep.Payload rate)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent) :
    Option (ReferenceActivePhysicalStep.Payload rate ×
      AssignmentScoreReconstruction.ReconstructedStart ledger instruction ×
      (Fin (p.m - 1) → ℕ)) :=
  match result with
  | .success output _ => some (output.payload, output.reconstruction, output.baseScore)
  | _ => none

theorem finishCheckedSample_data_eq_of_current
    (old : ReferenceActivePhysicalStep.Payload rate)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row otherRow : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hcutoff : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i)
    (hcutoffPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i)
    (law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out)
    (hselected : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
      hcutoff hcurrentPos = some law)
    (hc : row.2 instruction.time = otherRow.2 instruction.time) :
    laterResultData old ledger instruction row consistent
      (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
        consistent out hcall hcutoff hcurrentPos hcutoffPos law hselected) =
    laterResultData old ledger instruction otherRow consistent
      (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction otherRow
        consistent out hcall hcutoff hcurrentPos hcutoffPos law hselected) := by
  have hv : LaterAssignmentStartOperation.ownAssignmentVector row instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector otherRow instruction.time := by
    unfold LaterAssignmentStartOperation.ownAssignmentVector
    rw [hc]
  have hsEq := congrArg (CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor) hv
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> rename_i hsLeft
  all_goals
    split <;> rename_i hsRight
    all_goals
      have hresult := hsLeft.symm.trans (hsEq.trans hsRight)
      cases hresult
      all_goals rfl

/-- The actual reconstruction/law/sample computation has identical installation
data at equal whole controls of its instruction's round. No sampler law is assumed. -/
theorem laterResultData_eq_of_current
    (old : ReferenceActivePhysicalStep.Payload rate)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row otherRow : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (hc : row.2 instruction.time = otherRow.2 instruction.time) :
    laterResultData old ledger instruction row consistent
      (LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row consistent) =
    laterResultData old ledger instruction otherRow consistent
      (LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction otherRow consistent) := by
  unfold LaterAssignmentStartOperation.laterAssignmentStart
  cases LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason => rfl
  | success out hcall =>
      dsimp only [LaterAssignmentStartOperation.runReconstructionDecision]
      exact finishCheckedSample_data_eq_of_current _ _ _ _ _ _ _ _ _ _ _ _ _ hc

/-- The collection branch's literal arm, sender view and continuation arguments.
The alignment guard is the original physical selection guard. -/
def collectionOutcomeData (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p)
    (bank : CoordinatorUpReception.UpDecoderBank p) (cutoff : Fin p.T)
    (time : Fin p.T) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.CollectionOutcome {
      etaReal := rate.eta.val, etaPositive := rate.eta.property,
      n := rate.n, n_cast_identity := rate.n_scale,
      payload := payload, baseScores := ledger.baseScore, ledger := ledger,
      clock := clock, upDecoderBank := bank, cutoffIndex := cutoff,
      time := time, row := row }) :
    Fin p.K × Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      (Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate))) := by
  classical
  let source : CoordinatorRoundDispatch.CollectionInput p := {
    etaReal := rate.eta.val, etaPositive := rate.eta.property,
    n := rate.n, n_cast_identity := rate.n_scale,
    payload := payload, baseScores := ledger.baseScore, ledger := ledger,
    clock := clock, upDecoderBank := bank, cutoffIndex := cutoff,
    time := time, row := row }
  match out with
  | .continuing _ snapshot _ _ =>
      let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
      exact (snapshot.arm, some ⟨payload, snapshot.clockStarted.pending,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u,
        weights⟩,
        .inr (.inr (.inr ⟨payload, ledger, snapshot.clockStarted, weights⟩)))
  | .laterChosen _ _ started _ instruction _ _ _ _ installed selected =>
      if instruction.time = time then
        exact (selected.arm, some ⟨installed.registers.payload, started.pending,
          CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u,
          installed.registers.complementWeights⟩,
          .inr (.inr (.inl ⟨installed.registers, installed.ownedRegisters,
            installed.retainedBaseScore, started⟩)))
      else exact (ReferenceActivePhysicalStep.coordinatorFallback p, none, .inr (.inl ()))
  | _ => exact (ReferenceActivePhysicalStep.coordinatorFallback p, none, .inr (.inl ()))

/-- Core validity reads no row field. This compares the checks, not a supplied
certificate of successful dispatch. -/
theorem collectionCoreValid_row_iff (source : CoordinatorRoundDispatch.CollectionInput p)
    (otherRow : CompletePublicTable.CompleteRow p) :
    CoordinatorRoundDispatch.CollectionCoreValid source ↔
      CoordinatorRoundDispatch.CollectionCoreValid { source with row := otherRow } := by
  constructor <;> intro h <;> exact { h with }

section SharedInputs

variable (state : ReferenceActivePhysicalStep.State p rate)
  (rows otherRows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
  (t : Fin p.T) (active : ∀ i, (state.activations i).val ≤ t.val + 1)
  (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)

local notation "x" => (ReferenceActivePhysicalStep.RoundInput.mk state rows J t active rewards)
local notation "y" => (ReferenceActivePhysicalStep.RoundInput.mk state otherRows J t active otherRewards)

theorem cutData_live (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (out : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x r q base)) :
    cutData (ReferenceActivePhysicalStep.DispatchCut.live r q base out) =
      liveOutcomeData (ReferenceActivePhysicalStep.liveRegistersAt r t)
        (ReferenceActivePhysicalStep.liveOwnedAt r q t) base (rows J) out := by
  classical
  cases out <;>
    simp only [cutData, liveOutcomeData, ReferenceActivePhysicalStep.DispatchCut.arm,
      ReferenceActivePhysicalStep.DispatchCut.downView, tailArgs,
      ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
      Option.map_none]
  all_goals rfl

theorem cutData_collection (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (out : CoordinatorRoundDispatch.CollectionOutcome
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) :
    cutData (ReferenceActivePhysicalStep.DispatchCut.collection payload ledger clock cutoff out) =
      collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out := by
  classical
  cases out <;> first
  | rfl
  | (rename_i core consistent started hstart instruction hinstruction output hlocal
        clockData installed selected
     by_cases ht : instruction.time = t
     · simp only [cutData, ReferenceActivePhysicalStep.DispatchCut.arm,
         ReferenceActivePhysicalStep.DispatchCut.downView, tailArgs,
         ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
         ht, dite_true, reduceCtorEq, dite_false, collectionOutcomeData,
         Option.map_some]
       rfl
     · simp only [cutData, ReferenceActivePhysicalStep.DispatchCut.arm,
         ReferenceActivePhysicalStep.DispatchCut.downView, tailArgs,
         ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
         ht, dite_false, dite_true, collectionOutcomeData,
         Option.map_none])

/-- Every collection dispatch branch has the same consumed data at equal
whole current controls. The incoming ledger and clock are arbitrary. -/
theorem collectionOutcomeData_eq_of_current
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (hc : (rows J).2 t = (otherRows J).2 t) :
    collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J)
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) =
    collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J)
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff)) := by
  classical
  let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  have hcores := collectionCoreValid_row_iff source (otherRows J)
  dsimp only [source, ReferenceActivePhysicalStep.collectionInput,
    ReferenceActivePhysicalStep.RoundInput.row] at hcores
  change collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J)
      (CoordinatorRoundDispatch.dispatchCollection {
        etaReal := rate.eta.val, etaPositive := rate.eta.property,
        n := rate.n, n_cast_identity := rate.n_scale, payload := payload,
        baseScores := ledger.baseScore, ledger := ledger, clock := clock,
        upDecoderBank := state.upDecoderBank, cutoffIndex := cutoff, time := t, row := rows J }) =
    collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J)
      (CoordinatorRoundDispatch.dispatchCollection {
        etaReal := rate.eta.val, etaPositive := rate.eta.property,
        n := rate.n, n_cast_identity := rate.n_scale, payload := payload,
        baseScores := ledger.baseScore, ledger := ledger, clock := clock,
        upDecoderBank := state.upDecoderBank, cutoffIndex := cutoff, time := t, row := otherRows J })
  unfold CoordinatorRoundDispatch.dispatchCollection
  dsimp only
  split
  · rename_i failure hclock
    split
    · rfl
    · rename_i startedOther hclockOther
      have hbad := hclock.symm.trans hclockOther
      cases hbad
  · rename_i started hstart
    symm
    split
    · rename_i failure hclockOther
      have hbad := hstart.symm.trans hclockOther
      cases hbad
    · rename_i startedOther hstartOther
      have hsame := Except.ok.inj (hstart.symm.trans hstartOther)
      subst startedOther
      symm
      conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
      conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
      refine dite_congr (propext hcores) ?_ ?_
      · intro coreOther
        have core : CoordinatorRoundDispatch.CollectionCoreValid source := hcores.mpr coreOther
        conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
        conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
        refine dite_congr rfl ?_ ?_
        · intro hpending
          conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
          conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
          congr 1
          funext hscores
          conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
          conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
          congr 1
          funext hchoice
          let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
            core.ledger_valid core.assignment_eq
          let pending : Finset (ActiveRoundActions.Follower p.m) := started.pending
          have heq := CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
            payload pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            t weights (rows J) (otherRows J) hc
          split
          · rename_i hselected
            exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
              payload pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              t weights (rows J) (by
              have hut : cutoff.val ≤ t.val := by
                have htime : source.payload.sigma.val < source.time.val ∧
                    source.cutoffIndex.val ≤ source.time.val := by
                  simpa [CoordinatorPhaseClock.startRoundTimeValid,
                    core.clock_sigma_eq, core.clock_cutoff_eq] using core.clock_start_time_valid
                exact htime.2
              have hknown := CoordinatorPhaseClock.startRound_collection_pending
                p rate.eta.val t payload.sigma cutoff clock ledger.pending
                core.clock_parameter_valid core.clock_registers_valid core.clock_sigma_eq
                core.clock_cutoff_eq hut (Finset.nonempty_iff_ne_empty.mp hpending)
              have hclock : started.clock = clock :=
                congrArg CoordinatorPhaseClock.StartRoundResult.clock
                  (Except.ok.inj (hstart.symm.trans hknown))
              have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
                  some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
                have hu : clock.u = some cutoff := core.clock_cutoff_eq
                rw [hclock, hu]
                rfl
              rw [hcutoff]
              exact hchoice) hselected)
          · rename_i arm hselected
            split
            · rename_i hother
              exact False.elim (Option.some_ne_none arm
                (hselected.symm.trans (heq.trans hother)))
            · rename_i otherArm hother
              have harm := Option.some.inj (hselected.symm.trans (heq.trans hother))
              subst otherArm
              rfl
        · intro hpending
          split
          · rfl
          · rename_i instruction hinstruction
            have ht := ReferenceActivePhysicalStep.later_instruction_time x payload ledger clock cutoff
              core started instruction hstart hinstruction
            have hcurrent : (rows J).2 instruction.time = (otherRows J).2 instruction.time := by
              simpa only [ht] using hc
            let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger source core.payload_n_eq
            let consistent : LaterAssignmentStartOperation.LocalConsistency payload operationLedger := {
              oldStart_eq := core.ledger_sigma_eq.symm
              oldAssignment_eq := fun i => (core.assignment_eq i).symm
              oldFreezeAt := ledger.freezeAt
              oldFreezeAt_eq := rfl }
            let sourceOther := ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff
            let operationLedgerOther := CoordinatorRoundDispatch.collectionOperationLedger sourceOther coreOther.payload_n_eq
            let consistentOther : LaterAssignmentStartOperation.LocalConsistency payload operationLedgerOther := {
              oldStart_eq := coreOther.ledger_sigma_eq.symm
              oldAssignment_eq := fun i => (coreOther.assignment_eq i).symm
              oldFreezeAt := ledger.freezeAt
              oldFreezeAt_eq := rfl }
            have hdata : laterResultData payload operationLedger instruction (rows J) consistent
                (LaterAssignmentStartOperation.laterAssignmentStart payload operationLedger instruction
                  (rows J) consistent) =
                laterResultData payload operationLedgerOther instruction (otherRows J) consistentOther
                (LaterAssignmentStartOperation.laterAssignmentStart payload operationLedgerOther instruction
                  (otherRows J) consistentOther) :=
              laterResultData_eq_of_current payload operationLedger instruction
                (rows J) (otherRows J) consistent hcurrent
            dsimp only [operationLedger, consistent, source, operationLedgerOther, consistentOther, sourceOther,
              ReferenceActivePhysicalStep.collectionInput, ReferenceActivePhysicalStep.RoundInput.row] at hdata
            split <;> rename_i hlater
            all_goals
              symm
              split <;> rename_i hother
              all_goals
                symm
                first
                | rfl
                | (have hbad := hdata
                   simp only [hlater, hother, laterResultData, reduceCtorEq] at hbad)
            rename_i output hlocal outputOther hlocalOther
            have hfields : (output.payload, output.reconstruction, output.baseScore) =
                (outputOther.payload, outputOther.reconstruction, outputOther.baseScore) := by
              have hprojected := hdata
              simp only [hlater, hother, laterResultData] at hprojected
              exact Option.some.inj hprojected
            let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
              priorClock := clock, pending := ledger.pending
              proposalParameterValid := core.clock_parameter_valid
              priorClockValid := core.clock_registers_valid
              startTimeValid := by rw [ht]; exact core.clock_start_time_valid
              result := started
              startRound_eq := by rw [ht]; exact hstart
              assignmentStart_eq := hinstruction
              priorSigma_eq := core.clock_sigma_eq
              priorGrid_eq_freezeAt := by
                rw [hlocal]
                exact core.ledger_freeze_eq.symm }
            let clockDataOther : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence outputOther := {
              priorClock := clock, pending := ledger.pending
              proposalParameterValid := core.clock_parameter_valid
              priorClockValid := core.clock_registers_valid
              startTimeValid := by rw [ht]; exact core.clock_start_time_valid
              result := started
              startRound_eq := by rw [ht]; exact hstart
              assignmentStart_eq := hinstruction
              priorSigma_eq := core.clock_sigma_eq
              priorGrid_eq_freezeAt := by
                rw [hlocalOther]
                exact core.ledger_freeze_eq.symm }
            let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
            let installedOther := CoordinatorAssignmentRegisterInstall.installLater outputOther clockDataOther
            have hargs : (⟨installed.registers, installed.ownedRegisters,
                installed.retainedBaseScore, started⟩ : LiveArgs p rate) =
                ⟨installedOther.registers, installedOther.ownedRegisters,
                  installedOther.retainedBaseScore, started⟩ := by
              let project := fun data : ReferenceActivePhysicalStep.Payload rate ×
                  AssignmentScoreReconstruction.ReconstructedStart operationLedger instruction ×
                    (Fin (p.m - 1) → ℕ) =>
                (⟨{ payload := data.1, priorClock := started.clock,
                      pendingAtChoice := started.pending, time := instruction.time,
                      gridBoundary := started.clock.g,
                      complementScores := fun j => AssignmentScoreReconstruction.sourceScore data.2.1 j.1 },
                    { queue := fun j => AssignmentScoreReconstruction.initialQueue data.2.1 j.1,
                      previousService := fun j => (data.2.1.registers.current j.1).lastService },
                    data.2.2, started⟩ : LiveArgs p rate)
              exact congrArg project hfields
            have hregisters : installed.registers = installedOther.registers :=
              congrArg Sigma.fst hargs
            have hbase : installed.retainedBaseScore = installedOther.retainedBaseScore :=
              congrArg (fun args : LiveArgs p rate => args.2.2.1) hargs
            conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
            conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
            refine dite_congr (congrArg (fun b : Fin (p.m - 1) → ℕ => ∀ i, b i ≤ p.T * D p) hbase) ?_ ?_
            · intro hbaseValid
              conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
              conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
              refine dite_congr (congrArg (fun r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta =>
                CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  instruction.time r.complementWeights) hregisters) ?_ ?_
              · intro hchoice
                conv_lhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J))]
                conv_rhs => rw [apply_dite (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J))]
                refine dite_congr (congrArg CoordinatorLiveChoiceRecorderStep.Registers.complementEnvelopeValid hregisters) ?_ ?_
                · intro henvelope
                  let pending : Finset (ActiveRoundActions.Follower p.m) := started.pending
                  have heq : CoordinatorLocalArmChoice.coordinatorArmChoice installed.registers.payload pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) instruction.time
                      installed.registers.complementWeights (rows J) =
                      CoordinatorLocalArmChoice.coordinatorArmChoice installedOther.registers.payload pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) instruction.time
                      installedOther.registers.complementWeights (otherRows J) := by
                    rw [hregisters]
                    exact CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
                      _ _ _ _ _ _ _ hcurrent
                  split
                  · rename_i hselected
                    apply False.elim
                    apply CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                      installed.registers.payload pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                      instruction.time installed.registers.complementWeights (rows J) _ hselected
                    rw [hregisters]
                    exact hchoice
                  · rename_i arm hselected
                    split
                    · rename_i hselectedOther
                      exact False.elim (Option.some_ne_none arm
                        (hselected.symm.trans (heq.trans hselectedOther)))
                    · rename_i armOther hselectedOther
                      have harm := Option.some.inj (hselected.symm.trans (heq.trans hselectedOther))
                      subst armOther
                      have hfinal := congrArg (fun args : LiveArgs p rate =>
                        (arm, some (ReferenceDownReception.ChoiceTimeView.mk args.1.payload
                          started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                          args.1.complementWeights),
                          (Sum.inr (Sum.inr (Sum.inl args)) :
                            Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate))))) hargs
                      simpa only [collectionOutcomeData, ht, dite_true] using hfinal
                · intro henvelope
                  rfl
              · intro hchoice
                rfl
            · intro hbaseValid
              rfl
      · intro hcore
        rfl
/-- Current whole-control equality suffices for every live dispatcher branch.
The phase equality selects the incoming constructor; no validity is assumed. -/
theorem live_dispatch_data_eq_of_current
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : state.coordinator = .live r q base)
    (hc : (rows J).2 t = (otherRows J).2 t) :
    dispatchData x = dispatchData y := by
  classical
  unfold dispatchData
  have hx : ReferenceActivePhysicalStep.dispatch x =
      .live r q base (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput x r q base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  have hy : ReferenceActivePhysicalStep.dispatch y =
      .live r q base (CoordinatorRoundDispatch.dispatchLive
        (ReferenceActivePhysicalStep.liveInput y r q base)) := by
    simp only [ReferenceActivePhysicalStep.dispatch, hstate, CoordinatorRoundDispatch.dispatch]
    rfl
  rw [hx, hy, cutData_live, cutData_live]
  exact liveOutcomeData_eq_of_current _ _ _ _ _ hc

/-- Current whole-control equality suffices for every collection dispatcher
branch, including an out-of-domain ledger cutoff. Neither past proposals nor
any rewards are read at this pre-choice cut. -/
theorem collection_dispatch_data_eq_of_current
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (savedProposal : Option (Fin p.T × Bool))
    (hstate : state.coordinator = .collection payload ledger savedProposal)
    (hc : (rows J).2 t = (otherRows J).2 t) :
    dispatchData x = dispatchData y := by
  classical
  unfold dispatchData
  by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
  · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger savedProposal cutoff
    have hx : ReferenceActivePhysicalStep.dispatch x =
        .collection payload ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)) := by
      simp only [ReferenceActivePhysicalStep.dispatch, hstate, dite_eq_left hcutoff,
        CoordinatorRoundDispatch.dispatch]
      rfl
    have hy : ReferenceActivePhysicalStep.dispatch y =
        .collection payload ledger clock cutoff (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff)) := by
      simp only [ReferenceActivePhysicalStep.dispatch, hstate, dite_eq_left hcutoff,
        CoordinatorRoundDispatch.dispatch]
      rfl
    rw [hx, hy, cutData_collection, cutData_collection]
    exact collectionOutcomeData_eq_of_current _ _ _ _ _ _ _ _ _ _ _ _ hc
  · have hx := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff x
      payload ledger savedProposal hstate hcutoff
    have hy := ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff y
      payload ledger savedProposal hstate hcutoff
    rw [hx.1, hy.1]
    rfl

end SharedInputs

end Bandits.Support.ReferenceActiveDispatchTemporal
