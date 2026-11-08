/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveAffinePositiveTest
public import Bandits.Support.ReferenceActiveDispatchTemporal

/-!
# Pair independence of the actual coordinator dispatch data

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-137` and
`sources/zip4/manuscript/05_binary_transport.tex:7-42,74-124`.

These internal deterministic comparisons retain the original dispatcher and
continuous rows. They concern its DOWN view, selection presence and literal
observation continuation arguments. The coordinator arm can change on DOWN.
The later sampler is compared by its full assignment-vector read, including
all failures. The public replacement theorems have only the original round
input, direction and replacement sample as arguments. The conditional helpers
expose full assignment-vector equality or scalar/DOWN-sample equality; the
actual applications discharge these from the accepted coordinate-preservation
results. No selected view, branch, installation, choice or output agreement is
an input to those applications.

The proposed next consumer is `ReferenceAffinePhysicalHashRule`: the literal
DOWN/UP Boolean profile and guard rules, zero-bit collision exclusion and
selected UP sender identity remain separate obligations, followed by the
physical one-step-half adapter. This module proves no positive-test
factorization, incoming-state/word/batch-history pre-pair measurability, fresh
conditional pair law, reset/stopping chronology, decoder tail, recorder, Borel,
history or law result. It asserts no manuscript or main-regret closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceAffineDispatchPairInvariance

open ConstructorDimensions AffineChannelLaw
open ReferenceActiveDispatchTemporal


local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The real arm operation rejects exactly its input-domain failures. Every
branch after that check returns an arm, including either hash bit on DOWN. -/
theorem coordinatorArmChoiceCore_none_iff
    (payload : ReferenceActivePhysicalStep.Payload rate) (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (control : ContinuousLearningRows.TimeControl p) :
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights control = none ↔
      ¬ CoordinatorLocalArmChoice.ChoiceInputsValid payload cutoff time weights := by
  unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
  split
  · rename_i hvalid
    split_ifs <;> simp_all only [false_iff, not_not]
  · rename_i hinvalid
    exact ⟨fun _ => hinvalid, fun _ => rfl⟩

/-- In particular the success/failure decision reads no row coordinate. -/
theorem coordinatorArmChoice_none_iff (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (row otherRow : CompletePublicTable.CompleteRow p) :
    CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights row = none ↔
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights otherRow = none := by
  exact (coordinatorArmChoiceCore_none_iff payload pending cutoff time weights _).trans
    (coordinatorArmChoiceCore_none_iff payload pending cutoff time weights _).symm

/-- Full assignment-vector equality at any calendar time follows from the
proved preservation of all scalar labels, rather than whole-control equality. -/
theorem ownAssignmentVector_replace (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) (time : Fin p.T) :
    LaterAssignmentStartOperation.ownAssignmentVector (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s).row time =
      LaterAssignmentStartOperation.ownAssignmentVector x.row time := by
  funext k
  change (((ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s).rows x.selected).2 time).1
      (ContinuousControlSlice.Label.assign k) = _
  exact ReferenceActiveAffinePositiveTest.replaceCurrentPair_assignment x dir s x.selected time k

/-- First launch equality includes its entire vector and the shared rate and
time witnesses; applying the original sampler and installer preserves all data. -/
theorem firstLaunchInput_replace (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s)) =
      CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x) := by
  unfold CoordinatorRoundDispatch.firstLaunchInput ReferenceActivePhysicalStep.firstInput
  dsimp only
  rw [ownAssignmentVector_replace]
  rfl

/-- Exact dependent equality of the full computed first installation. -/
theorem installFirst_replace (x : ReferenceActivePhysicalStep.RoundInput p rate) (dir : Fin 2)
    (s : Sample (AffineBatchDecoder.width p)) :
    HEq (CoordinatorAssignmentRegisterInstall.installFirst
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s))))
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x))) := by
  rw [firstLaunchInput_replace]
  rfl

/-- The checked later sampler reads only the original whole assignment vector.
Reconstruction, law, domain and consistency inputs are explicit and fixed. -/
theorem finishCheckedSample_data_eq_of_assignment
    (old : ReferenceActivePhysicalStep.Payload rate) (ledger : LaterAssignmentStartOperation.LocalLedger old)
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
    (hv : LaterAssignmentStartOperation.ownAssignmentVector row instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector otherRow instruction.time) :
    laterResultData old ledger instruction row consistent
      (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
        consistent out hcall hcutoff hcurrentPos hcutoffPos law hselected) =
    laterResultData old ledger instruction otherRow consistent
      (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction otherRow
        consistent out hcall hcutoff hcurrentPos hcutoffPos law hselected) := by
  have hsEq := congrArg (CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor) hv
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> rename_i hsLeft
  all_goals
    split <;> rename_i hsRight
    all_goals
      have hresult := hsLeft.symm.trans (hsEq.trans hsRight)
      cases hresult
      all_goals rfl

/-- The actual later-start computation has the same row-free installation
data at equal assignment-vector reads, including every failure alternative. -/
theorem laterResultData_eq_of_assignment
    (old : ReferenceActivePhysicalStep.Payload rate) (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row otherRow : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector row instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector otherRow instruction.time) :
    laterResultData old ledger instruction row consistent
      (LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row consistent) =
    laterResultData old ledger instruction otherRow consistent
      (LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction otherRow consistent) := by
  unfold LaterAssignmentStartOperation.laterAssignmentStart
  cases LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason => rfl
  | success out hcall =>
      dsimp only [LaterAssignmentStartOperation.runReconstructionDecision]
      exact finishCheckedSample_data_eq_of_assignment _ _ _ _ _ _ _ _ _ _ _ _ _ hv

/-- Both live StartRound alternatives retain identical views and continuation
arguments for arbitrary rows. Choice rejection is compared by the literal core. -/
theorem liveOutcomeData_tail_eq
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (row otherRow : CompletePublicTable.CompleteRow p) :
    (liveOutcomeData r q base row (CoordinatorRoundDispatch.dispatchLive
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := row })).2 =
    (liveOutcomeData r q base otherRow (CoordinatorRoundDispatch.dispatchLive
      { eta := rate.eta, registers := r, ownedRegisters := q,
        followerBaseScore := base, row := otherRow })).2 := by
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
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h11
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h10
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h9
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h8
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h7
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h6
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h5
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h4
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h3
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h2
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h1
      have heq := coordinatorArmChoice_none_iff
        r.payload dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
        r.time r.complementWeights row otherRow
      split
      · rename_i hselected
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          r.payload dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          r.time r.complementWeights row (by assumption) hselected)
      · rename_i arm hselected
        split
        · rename_i hother
          have hsome : some arm = none := hselected.symm.trans (heq.mpr hother)
          exact False.elim (Option.some_ne_none _ hsome)
        · rename_i otherArm hother
          rfl
    · rename_i ledger hinit
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h3
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h2
      conv_lhs => rw [apply_dite (fun out => (liveOutcomeData r q base row out).2)]
      conv_rhs => rw [apply_dite (fun out => (liveOutcomeData r q base otherRow out).2)]
      congr 1
      funext h1
      have heq := coordinatorArmChoice_none_iff
        r.payload dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
        r.time r.complementWeights row otherRow
      split
      · rename_i hselected
        exact False.elim (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          r.payload dispatched.startResult.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          r.time r.complementWeights row (by assumption) hselected)
      · rename_i arm hselected
        split
        · rename_i hother
          have hsome : some arm = none := hselected.symm.trans (heq.mpr hother)
          exact False.elim (Option.some_ne_none _ hsome)
        · rename_i otherArm hother
          rfl

/-- The actual first dispatcher retains its complete computed installation.
The only discarded component here is the returned physical arm. -/
theorem firstCut_tail (input : ReferenceActivePhysicalStep.RoundInput p rate) :
    (cutData (.first (CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput input)))).2 =
      let installed := CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput input))
      (some (ReferenceDownReception.ChoiceTimeView.mk installed.registers.payload
        installed.startRoundResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
        installed.registers.complementWeights),
        (Sum.inr (Sum.inr (Sum.inl (⟨installed.registers, installed.ownedRegisters,
          installed.followerBaseScore, installed.startRoundResult⟩ : LiveArgs p rate))) :
          Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate)))) := by
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · rename_i hselected
    exact False.elim (hnonempty hselected)
  · rename_i arm hselected
    have ht : installed.registers.time = input.time :=
      CoordinatorAssignmentRegisterInstall.first_registers_time launch
    simp only [cutData, ReferenceActivePhysicalStep.DispatchCut.downView,
      ReferenceActivePhysicalStep.DispatchCut.selection, ReferenceActivePhysicalStep.selectionAt,
      ht, dite_true, Option.map_some, tailArgs, reduceCtorEq, dite_false]
    rfl

section SharedInputs

variable (state : ReferenceActivePhysicalStep.State p rate)
  (rows otherRows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
  (t : Fin p.T) (active : ∀ i, (state.activations i).val ≤ t.val + 1)
  (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)

local notation "x" => (ReferenceActivePhysicalStep.RoundInput.mk state rows J t active rewards)
local notation "y" => (ReferenceActivePhysicalStep.RoundInput.mk state otherRows J t active otherRewards)

/-- Original collection clock, ledger and installation checks, compared
using only all-time full-vector reads. The physical time-alignment check is
retained, as are continuing, reconstruction, sampler and local failures. -/
theorem collectionOutcomeData_tail_eq_of_assignment
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (hv : ∀ time, LaterAssignmentStartOperation.ownAssignmentVector (rows J) time =
      LaterAssignmentStartOperation.ownAssignmentVector (otherRows J) time) :
    (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J)
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))).2 =
    (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J)
      (CoordinatorRoundDispatch.dispatchCollection
        (ReferenceActivePhysicalStep.collectionInput y payload ledger clock cutoff))).2 := by
  classical
  let source := ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff
  have hcores := collectionCoreValid_row_iff source (otherRows J)
  dsimp only [source, ReferenceActivePhysicalStep.collectionInput,
    ReferenceActivePhysicalStep.RoundInput.row] at hcores
  change (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J)
      (CoordinatorRoundDispatch.dispatchCollection {
        etaReal := rate.eta.val, etaPositive := rate.eta.property,
        n := rate.n, n_cast_identity := rate.n_scale, payload := payload,
        baseScores := ledger.baseScore, ledger := ledger, clock := clock,
        upDecoderBank := state.upDecoderBank, cutoffIndex := cutoff, time := t, row := rows J })).2 =
    (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J)
      (CoordinatorRoundDispatch.dispatchCollection {
        etaReal := rate.eta.val, etaPositive := rate.eta.property,
        n := rate.n, n_cast_identity := rate.n_scale, payload := payload,
        baseScores := ledger.baseScore, ledger := ledger, clock := clock,
        upDecoderBank := state.upDecoderBank, cutoffIndex := cutoff, time := t, row := otherRows J })).2
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
      conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
      conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
      refine dite_congr (propext hcores) ?_ ?_
      · intro coreOther
        have core : CoordinatorRoundDispatch.CollectionCoreValid source := hcores.mpr coreOther
        conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
        conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
        refine dite_congr rfl ?_ ?_
        · intro hpending
          conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
          conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
          congr 1
          funext hscores
          conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
          conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
          congr 1
          funext hchoice
          let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights source
            core.ledger_valid core.assignment_eq
          let pending : Finset (ActiveRoundActions.Follower p.m) := started.pending
          have heq := coordinatorArmChoice_none_iff
            payload pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
            t weights (rows J) (otherRows J)
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
                (hselected.symm.trans (heq.mpr hother)))
            · rename_i otherArm hother
              rfl
        · intro hpending
          split
          · rfl
          · rename_i instruction hinstruction
            have ht := ReferenceActivePhysicalStep.later_instruction_time x payload ledger clock cutoff
              core started instruction hstart hinstruction
            have hcurrent := hv instruction.time
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
              laterResultData_eq_of_assignment payload operationLedger instruction
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
            conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
            conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
            refine dite_congr (congrArg (fun b : Fin (p.m - 1) → ℕ => ∀ i, b i ≤ p.T * D p) hbase) ?_ ?_
            · intro hbaseValid
              conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
              conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
              refine dite_congr (congrArg (fun r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta =>
                CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                  instruction.time r.complementWeights) hregisters) ?_ ?_
              · intro hchoice
                conv_lhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (rows J) out).2)]
                conv_rhs => rw [apply_dite (fun out => (collectionOutcomeData payload ledger clock state.upDecoderBank cutoff t (otherRows J) out).2)]
                refine dite_congr (congrArg CoordinatorLiveChoiceRecorderStep.Registers.complementEnvelopeValid hregisters) ?_ ?_
                · intro henvelope
                  let pending : Finset (ActiveRoundActions.Follower p.m) := started.pending
                  have heq : CoordinatorLocalArmChoice.coordinatorArmChoice installed.registers.payload pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) instruction.time
                      installed.registers.complementWeights (rows J) = none ↔
                      CoordinatorLocalArmChoice.coordinatorArmChoice installedOther.registers.payload pending
                      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) instruction.time
                      installedOther.registers.complementWeights (otherRows J) = none := by
                    rw [hregisters]
                    exact coordinatorArmChoice_none_iff _ _ _ _ _ _ _
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
                        (hselected.symm.trans (heq.mpr hselectedOther)))
                    · rename_i armOther hselectedOther
                      have hfinal := congrArg (fun args : LiveArgs p rate =>
                        (some (ReferenceDownReception.ChoiceTimeView.mk args.1.payload
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
/-- Compare the literal original dispatchers at common incoming state and
calendar time. Only full assignment-vector reads are conditional inputs. -/
theorem dispatch_tail_eq_of_assignment
    (hv : ∀ time, LaterAssignmentStartOperation.ownAssignmentVector (rows J) time =
      LaterAssignmentStartOperation.ownAssignmentVector (otherRows J) time) :
    (dispatchData x).2 = (dispatchData y).2 := by
  unfold dispatchData
  cases hstate : state.coordinator with
  | dagger =>
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hstate,
        ReferenceActivePhysicalStep.dispatch_dagger y hstate]
      rfl
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first x hstate,
        ReferenceActivePhysicalStep.dispatch_first y hstate, firstCut_tail, firstCut_tail]
      have hlaunch : CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x) =
          CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput y) := by
        unfold CoordinatorRoundDispatch.firstLaunchInput ReferenceActivePhysicalStep.firstInput
        dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
        rw [hv t]
      rw [hlaunch]
      rfl
  | live r q base =>
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
      exact liveOutcomeData_tail_eq _ _ _ _ _
  | collection payload ledger savedProposal =>
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
        exact collectionOutcomeData_tail_eq_of_assignment _ _ _ _ _ _ _ _ _ _ _ _ hv
      · rw [(ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff x
            payload ledger savedProposal hstate hcutoff).1,
          (ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff y
            payload ledger savedProposal hstate hcutoff).1]
        rfl

end SharedInputs

/-- Actual pair replacement preserves the DOWN view and the literal
continuation arguments together, on the whole RoundInput carrier. -/
theorem dispatch_tail_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    (dispatchData (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s)).2 =
      (dispatchData x).2 := by
  exact dispatch_tail_eq_of_assignment x.state
    (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s).rows x.rows x.selected
    x.time x.active x.rewards x.rewards (ownAssignmentVector_replace x dir s)

/-- The actual DOWN sender view is independent of the current directed pair. -/
theorem downView_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    (ReferenceActivePhysicalStep.dispatch (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s)).downView =
      (ReferenceActivePhysicalStep.dispatch x).downView :=
  congrArg Prod.fst (dispatch_tail_replace x dir s)

/-- These are D's canonical literal continuation arguments of observeCoordinator. -/
theorem tailArgs_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    tailArgs (ReferenceActivePhysicalStep.dispatch (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s)) =
      tailArgs (ReferenceActivePhysicalStep.dispatch x) :=
  congrArg Prod.snd (dispatch_tail_replace x dir s)

/-- Map-to-view preserves exactly selection presence, including all rejections. -/
theorem selection_isSome_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    (ReferenceActivePhysicalStep.dispatch (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s)).selection.isSome =
      (ReferenceActivePhysicalStep.dispatch x).selection.isSome := by
  have h := congrArg Option.isSome (downView_replace x dir s)
  simpa only [ReferenceActivePhysicalStep.DispatchCut.downView, Option.isSome_map] using h

/-- The actual DOWN word is fixed even on failure and time-mismatch paths.
The enabling test uses choice presence and the preserved scalar branch labels. -/
theorem downSent_replace (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (dir : Fin 2) (s : Sample (AffineBatchDecoder.width p)) :
    ReferenceActiveAffinePositiveTest.downSent (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s) =
      ReferenceActiveAffinePositiveTest.downSent x := by
  unfold ReferenceActiveAffinePositiveTest.downSent
  rw [(ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x dir s).2.2.1]
  rw [downView_replace, ReferenceActiveAffinePositiveTest.upSenderIndex_replace]
  cases (ReferenceActivePhysicalStep.dispatch x).downView with
  | none => rfl
  | some view =>
      unfold ReferenceDownReception.expectedDownFlatWord
      have hn := coordinatorArmChoice_none_iff view.payload view.pendingAtChoice view.cutoff
        x.time view.complementWeights (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s).row x.row
      have hb : ReferenceDownReception.selectedDownSenderBranch view
          (ReferenceActivePhysicalStep.upSenderIndex x)
          (ReferenceActiveAffinePositiveTest.replaceCurrentPair x dir s).row x.time ↔
          ReferenceDownReception.selectedDownSenderBranch view
            (ReferenceActivePhysicalStep.upSenderIndex x) x.row x.time := by
        unfold ReferenceDownReception.selectedDownSenderBranch
        rw [ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice]
      have hg := and_congr (not_congr hn) hb
      change (if _ then _ else _) = (if _ then _ else _)
      exact ite_congr (propext hg) (fun _ => rfl) (fun _ => rfl)

/-- Literal coordinator arm choice reads the scalar slice and the DOWN
samples only. No input-domain, live, selected-slot or hash-bit premise is used. -/
theorem coordinatorArmChoiceCore_eq_of_slice_down
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (control otherControl : ContinuousLearningRows.TimeControl p)
    (hc : control.1 = otherControl.1)
    (hs : ∀ i, control.2 (0, i) = otherControl.2 (0, i)) :
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights control =
      CoordinatorLocalArmChoice.coordinatorArmChoiceCore payload pending cutoff time weights otherControl := by
  rcases control with ⟨scalars, samples⟩
  rcases otherControl with ⟨otherScalars, otherSamples⟩
  change scalars = otherScalars at hc
  subst otherScalars
  change ∀ i, samples (0, i) = otherSamples (0, i) at hs
  unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
  dsimp only
  split
  · split
    · rfl
    · split
      · rfl
      · split
        · apply congrArg some
          apply congrArg (fun bit => ActiveRoundActions.sendArm bit _ _)
          apply congrArg (fun pair => affineHash pair _)
          exact hs _
        · rfl
  · rfl

/-- On UP replacement the coordinator's actual choice is unchanged for
arbitrary fixed choice data, including rejected domain checks. -/
theorem coordinatorArmChoice_replace_up
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff x.time weights
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s).row =
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff x.time weights x.row := by
  apply coordinatorArmChoiceCore_eq_of_slice_down
  · exact ReferenceActiveAffinePositiveTest.replaceCurrentPair_current_slice x 1 s
  · intro i
    apply ReferenceActiveAffinePositiveTest.replaceCurrentPair_other_sample
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst h)

/-- The actual coordinator arm, with its actual installed choice data,
ignores an UP-pair replacement. DOWN arm equality is not asserted. -/
theorem coordinator_arm_replace_up (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) :
    (ReferenceActivePhysicalStep.dispatch (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arm =
      (ReferenceActivePhysicalStep.dispatch x).arm := by
  have hview := downView_replace x 1 s
  unfold ReferenceActivePhysicalStep.DispatchCut.downView at hview
  cases hn : (ReferenceActivePhysicalStep.dispatch
      (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).selection with
  | none =>
      cases ho : (ReferenceActivePhysicalStep.dispatch x).selection with
      | none => simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hn, ho]
      | some selected => simp only [hn, ho, Option.map_none, Option.map_some] at hview; cases hview
  | some selected =>
      cases ho : (ReferenceActivePhysicalStep.dispatch x).selection with
      | none => simp only [hn, ho, Option.map_none, Option.map_some] at hview; cases hview
      | some original =>
          simp only [hn, ho, Option.map_some, Option.some.injEq] at hview
          have hchoice := coordinatorArmChoice_replace_up x s original.view.payload
            original.view.pendingAtChoice original.view.cutoff original.view.complementWeights
          have hselected := selected.choice_eq
          rw [(ReferenceActiveAffinePositiveTest.replaceCurrentPair_fields x 1 s).2.2.1,
            hview] at hselected
          rw [hchoice, original.choice_eq] at hselected
          have harm : selected.arm = original.arm := (Option.some.inj hselected).symm
          simpa only [ReferenceActivePhysicalStep.DispatchCut.arm, hn, ho] using harm

/-- The physical PREPARE action uses exactly the coordinator's dispatch arm. -/
theorem coordinator_action_replace_up (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (s : Sample (AffineBatchDecoder.width p)) :
    (ReferenceActivePhysicalStep.prepare (ReferenceActiveAffinePositiveTest.replaceCurrentPair x 1 s)).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) =
      (ReferenceActivePhysicalStep.prepare x).arms.actions (ActiveRoundActions.coordinator p.two_le_m) := by
  exact coordinator_arm_replace_up x s

end Bandits.Support.ReferenceAffineDispatchPairInvariance
