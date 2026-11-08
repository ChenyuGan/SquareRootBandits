/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.LaunchAssignmentCoordinateSplit
public import Bandits.Support.AssignmentParameterFibreKernel
public import Bandits.Support.LaterAssignmentJointCodeMeasurability

/-!
# Fixed-input later-assignment coordinate fibres

Internal pointwise mathematics for the actual collection dispatcher. Sources:
`sources/zip4/manuscript/06_interruptions.tex:30-69,376-386,399-423`,
`sources/zip4/manuscript/05_binary_transport.tex:62-80`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

The incoming state, private arrays, selected index, calendar coordinate and
complete reward table are fixed. Only the complete K+1 assignment vector in
the selected current control is changed. This constructs no incoming history,
truthful reconstruction, feasible law, or manuscript theorem.

Status: partial. `computedEvidence_collection_fibre` is not declared here.
The proved pieces are the exact coordinate update, the actual parameter
projection and its dispatch agreement, control-read invariance, successful
payload/base-score sufficiency, and conditional successful installation.
The last helper exposes its two actual success equations and original clock
evidences, including equality of their returned clock results. It does not
produce those dispatcher branches.

The remaining producer must compare the original physical selection and tails
for continuing collection, no-sampler paths, and both rejected-sampler tags,
then assemble equality of `ReferenceActivePhysicalHorizon.computedEvidence`.
In particular followers must still run their logging/service/DOWN/release tail
on rejected dispatches. No evidence/successor equality or valid-run record is
assumed here to replace that missing proof. Horizon-record specialization and
consumption by the finite-fibre measure and successor-step APIs remain open.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceLaterAssignmentFibreStep


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

/-- Replace the complete assignment vector using the accepted inverse split;
the labelled non-assignment scalars and all affine channels are retained. -/
def controlWithAssignment (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) : ContinuousLearningRows.TimeControl p :=
  (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
    (v, (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p (x.row.2 x.time)).2)

/-- Keep all private/forward arrays and change only the selected current
calendar entry of its learning row. -/
def rowWithAssignment (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) : CompletePublicTable.CompleteRow p :=
  (x.row.1, Function.update x.row.2 x.time (controlWithAssignment x v))

/-- Literal single-row, single-time perturbation of the original input. -/
def withAssignment (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) : ReferenceActivePhysicalStep.RoundInput p rate :=
  { x with rows := Function.update x.rows x.selected (rowWithAssignment x v) }

theorem withAssignment_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    (withAssignment x v).row = rowWithAssignment x v := by
  exact Function.update_self _ _ _

theorem withAssignment_other_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (q : Fin (M p))
    (hq : q ≠ x.selected) : (withAssignment x v).rows q = x.rows q :=
  Function.update_of_ne hq _ _

theorem rowWithAssignment_arrays (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    (rowWithAssignment x v).1 = x.row.1 := rfl

theorem rowWithAssignment_other_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (ht : t ≠ x.time) : (rowWithAssignment x v).2 t = x.row.2 t :=
  Function.update_of_ne ht _ _

private theorem split_first (c : ContinuousLearningRows.TimeControl p) :
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).1 =
      ContinuousControlSlice.assignmentVector c.1 := by
  rfl

private theorem split_scalar (c : ContinuousLearningRows.TimeControl p)
    (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2.1 label = c.1 label.1 := rfl

private theorem split_affine (c : ContinuousLearningRows.TimeControl p) :
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p c).2.2 = c.2 := rfl

theorem ownAssignmentVector_rowWithAssignment (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    LaterAssignmentStartOperation.ownAssignmentVector (rowWithAssignment x v) x.time = v := by
  change ContinuousControlSlice.assignmentVector
    ((Function.update x.row.2 x.time (controlWithAssignment x v) x.time).1) = v
  rw [Function.update_self, ← split_first]
  exact congrArg Prod.fst ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply _)

theorem rowWithAssignment_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((rowWithAssignment x v).2 t).1 label.1 = (x.row.2 t).1 label.1 := by
  by_cases ht : t = x.time
  · subst t
    change (Function.update x.row.2 x.time (controlWithAssignment x v) x.time).1 _ = _
    rw [Function.update_self, ← split_scalar]
    exact congrArg (fun z => z.2.1 label)
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply _)
  · rw [rowWithAssignment_other_time x v t ht]

theorem rowWithAssignment_affine (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    ((rowWithAssignment x v).2 t).2 = (x.row.2 t).2 := by
  by_cases ht : t = x.time
  · subst t
    change (Function.update x.row.2 x.time (controlWithAssignment x v) x.time).2 = _
    rw [Function.update_self, ← split_affine]
    exact congrArg (fun z => z.2.2)
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply _)
  · rw [rowWithAssignment_other_time x v t ht]

private theorem named_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (label : ContinuousControlSlice.NamedLabel) :
    ((rowWithAssignment x v).2 t).1 (Sum.inl label) =
      (x.row.2 t).1 (Sum.inl label) := by
  exact rowWithAssignment_scalar x v t ⟨Sum.inl label, by rintro ⟨r, h⟩; cases h⟩

private theorem tuple_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) (i : Fin p.m) :
    ((rowWithAssignment x v).2 t).1 (ContinuousControlSlice.Label.tuple i) =
      (x.row.2 t).1 (ContinuousControlSlice.Label.tuple i) := by
  exact rowWithAssignment_scalar x v t
    ⟨ContinuousControlSlice.Label.tuple i, by rintro ⟨r, h⟩; cases h⟩

private theorem pilot_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) (i : Fin p.m) :
    ((rowWithAssignment x v).2 t).1 (ContinuousControlSlice.Label.pilot i) =
      (x.row.2 t).1 (ContinuousControlSlice.Label.pilot i) := by
  exact rowWithAssignment_scalar x v t
    ⟨ContinuousControlSlice.Label.pilot i, by rintro ⟨r, h⟩; cases h⟩

private theorem slotDraw_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    PublicDiscreteDraws.slotDraw ((rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.slotDraw (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.slotDraw, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.slot, named_scalar]

private theorem selectedFollowerDraw_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ((rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.selectedFollowerDraw, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.sel, named_scalar]

private theorem recorderSourceDraw_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K ((rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.recorderSourceDraw, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.rec, named_scalar]

private theorem pilotDraw_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) (i : Fin p.m) :
    PublicDiscreteDraws.pilotDraw (K_pos p) i ((rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.pilotDraw (K_pos p) i (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.pilotDraw, ContinuousControlSlice.coordinate, pilot_scalar]

private theorem tupleDraw_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((rowWithAssignment x v).2 t).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 t).1 := by
  apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq
  intro i
  exact tuple_scalar x v t i

/-- The actual choice operation ignores assignment scalars, even in its
invalid-input and fallback tuple branches. -/
theorem coordinatorArmChoice_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (pending : Finset (Fin (p.m - 1)))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p))
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff t weights
        (rowWithAssignment x v) =
      CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff t weights x.row := by
  simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
    CoordinatorLocalArmChoice.coordinatorArmChoiceCore,
    CoordinatorLocalArmChoice.localFastDraw, CoordinatorLocalArmChoice.currentDownHash,
    slotDraw_row, selectedFollowerDraw_row, pilotDraw_row, tupleDraw_row,
    rowWithAssignment_affine, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.fast, named_scalar]
  split_ifs <;> rfl

/-- Follower UP-offer checks see the original local state and unchanged
selection controls. -/
theorem checkedUpOffer_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (rowWithAssignment x v)
        activation t state =
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row activation t state := by
  simp only [ActiveFollowerQueueOperation.checkedUpOffer,
    ActiveFollowerQueueOperation.selectedUpRound, slotDraw_row, selectedFollowerDraw_row]

/-- All checked follower arm branches use only the unchanged control labels
and affine samples. This does not compare retained raw preparations. -/
theorem followerArmChoice_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (offer : Option (OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta))) :
    ActiveFollowerArmChoice.followerArmChoice state (rowWithAssignment x v) t i offer =
      ActiveFollowerArmChoice.followerArmChoice state x.row t i offer := by
  simp only [ActiveFollowerArmChoice.followerArmChoice,
    ActiveFollowerArmChoice.followerArmChoiceCore, ActiveFollowerArmChoice.offeredUpBit,
    slotDraw_row, selectedFollowerDraw_row, pilotDraw_row, tupleDraw_row,
    rowWithAssignment_affine]

/-- The consistency data are constructed from the actual checked core and
actual operation ledger; no reconstruction or history is supplied. -/
def collectionConsistency (x : CoordinatorRoundDispatch.CollectionInput p) (core : CoordinatorRoundDispatch.CollectionCoreValid x) :
    LaterAssignmentStartOperation.LocalConsistency x.payload (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) := {
  oldStart_eq := by
    simpa only [CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRoundDispatch.collectionOperationLedger] using core.ledger_sigma_eq.symm
  oldAssignment_eq := fun i => (core.assignment_eq i).symm
  oldFreezeAt := x.ledger.freezeAt
  oldFreezeAt_eq := rfl }

/-- The exact pre-sampler projection: call the actual clock, check the core
and empty pending set, and use its actual instruction and reconstructed law.
Failures and paths with no sampler have no parameters. -/
def collectionParameters? (x : CoordinatorRoundDispatch.CollectionInput p) : Option (AssignmentParameterFibreKernel.Theta p) :=
  match CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending with
  | .error _ => none
  | .ok started =>
      if core : CoordinatorRoundDispatch.CollectionCoreValid x then
        if x.ledger.pending.Nonempty then none
        else match started.assignmentStart with
          | none => none
          | some instruction =>
              LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
                ⟨CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq,
                  instruction, collectionConsistency x core⟩
      else none

/-- Literal projection of the physical dispatch's finite cutoff check and
collection input. Outside collection there is no later sampler. -/
def parameters? (x : ReferenceActivePhysicalStep.RoundInput p rate) : Option (AssignmentParameterFibreKernel.Theta p) :=
  match x.state.coordinator with
  | .collection payload ledger proposal =>
      if hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T then
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        collectionParameters?
          (ReferenceActivePhysicalStep.collectionInput x payload ledger (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff)
      else none
  | _ => none

/-- The sampler parameters do not inspect any coordinate of the row. -/
theorem collectionParameters?_row (x : CoordinatorRoundDispatch.CollectionInput p)
    (row : CompletePublicTable.CompleteRow p) :
    collectionParameters? { x with row := row } = collectionParameters? x := by
  have hc : CoordinatorRoundDispatch.CollectionCoreValid { x with row := row } ↔
      CoordinatorRoundDispatch.CollectionCoreValid x := by
    constructor <;> intro h
    · exact ⟨h.payload_n_eq, h.ledger_valid, h.ledger_ready, h.assignment_eq,
        h.base_score_eq, h.clock_parameter_valid, h.clock_registers_valid,
        h.clock_start_time_valid, h.clock_sigma_eq, h.clock_cutoff_eq,
        h.ledger_sigma_eq, h.ledger_cutoff_eq, h.ledger_freeze_eq,
        h.ledger_cursor_eq, h.decoder_bank_valid⟩
    · exact ⟨h.payload_n_eq, h.ledger_valid, h.ledger_ready, h.assignment_eq,
        h.base_score_eq, h.clock_parameter_valid, h.clock_registers_valid,
        h.clock_start_time_valid, h.clock_sigma_eq, h.clock_cutoff_eq,
        h.ledger_sigma_eq, h.ledger_cutoff_eq, h.ledger_freeze_eq,
        h.ledger_cursor_eq, h.decoder_bank_valid⟩
  unfold collectionParameters?
  cases CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending with
  | error _ => rfl
  | ok started =>
      dsimp only
      by_cases h : CoordinatorRoundDispatch.CollectionCoreValid x
      · rw [dite_eq_left h, dite_eq_left (hc.mpr h)]
        rfl
      · rw [dite_eq_right h, dite_eq_right (fun h' => h (hc.mp h'))]

/-- The actual parameters are independent of the replacement vector, without
a supplied factorization premise or an arbitrary selected law. -/
theorem parameters?_withAssignment (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    parameters? (withAssignment x v) = parameters? x := by
  unfold parameters? withAssignment
  cases x.state.coordinator with
  | first => rfl
  | live _ _ _ => rfl
  | dagger => rfl
  | collection payload ledger proposal =>
      dsimp only
      split
      · rename_i hc
        let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        exact collectionParameters?_row
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff)
          ((withAssignment x v).row)
      · rfl


/-- Project the actual instruction and checked local ledger from a retained
collection outcome. All three later failures keep their original tags; this
projection does not equate those records. -/
def outcomeParameters? {x : CoordinatorRoundDispatch.CollectionInput p}
    (outcome : CoordinatorRoundDispatch.CollectionOutcome x) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  match outcome with
  | .laterReconstructionFailure core consistent _ _ instruction _ _ _ =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
        ⟨CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq,
          instruction, consistent⟩
  | .laterPrefixFailure core consistent _ _ instruction _ _ _ _ =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
        ⟨CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq,
          instruction, consistent⟩
  | .laterOrientationFailure core consistent _ _ instruction _ _ _ =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
        ⟨CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq,
          instruction, consistent⟩
  | .laterChoiceFailure core consistent _ _ instruction _ _ _ _ _ _ =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
        ⟨CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq,
          instruction, consistent⟩
  | .laterChosen core consistent _ _ instruction _ _ _ _ _ _ =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters? x.payload
        ⟨CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq,
          instruction, consistent⟩
  | _ => none

private theorem pending_choice_failure_false (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock x.ledger.pending = .ok started)
    (hpending : x.ledger.pending.Nonempty)
    (hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
      (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex)) x.time
      (CoordinatorCollectionInteractive.PreObservationInputs.weights x core.ledger_valid core.assignment_eq))
    (hselected : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
      (CoordinatorCollectionInteractive.PreObservationInputs.weights x core.ledger_valid core.assignment_eq)
      x.row = none) : False := by
  have hut : x.cutoffIndex.val ≤ x.time.val := by
    have hparts : x.payload.sigma.val < x.time.val ∧ x.cutoffIndex.val ≤ x.time.val := by
      simpa only [CoordinatorPhaseClock.startRoundTimeValid, core.clock_sigma_eq,
        core.clock_cutoff_eq] using core.clock_start_time_valid
    exact hparts.2
  have hknown := CoordinatorPhaseClock.startRound_collection_pending p x.etaReal x.time
    x.payload.sigma x.cutoffIndex x.clock x.ledger.pending core.clock_parameter_valid
    core.clock_registers_valid core.clock_sigma_eq core.clock_cutoff_eq hut
    (Finset.nonempty_iff_ne_empty.mp hpending)
  have heq := Except.ok.inj (hstart.symm.trans hknown)
  have hcutoff : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u =
      some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex) := by
    rw [heq, core.clock_cutoff_eq]
    rfl
  exact (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none x.payload started.pending
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time
    (CoordinatorCollectionInteractive.PreObservationInputs.weights x core.ledger_valid core.assignment_eq)
    x.row (by simpa only [hcutoff] using hchoice)) hselected

private theorem choice_failure_false
    {eta : ReferencePrelaunchFollower.LearningRate}
    {payload : AssignmentStartPayload.Input p eta}
    {pending : Finset (Fin (p.m - 1))}
    {cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)} {time : Fin p.T}
    {weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ}
    {row : CompletePublicTable.CompleteRow p}
    (hv : CoordinatorLocalArmChoice.ChoiceInputsValid payload cutoff time weights)
    (hs : CoordinatorLocalArmChoice.coordinatorArmChoice payload pending cutoff time weights row = none) :
    False :=
  (CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
    payload pending cutoff time weights row hv) hs

/-- The literal pre-sampler projection agrees with the actual dispatch
computation, including the paths that never call reconstruction or sampling. -/
theorem collectionParameters?_eq_dispatch (x : CoordinatorRoundDispatch.CollectionInput p) :
    collectionParameters? x = outcomeParameters? (CoordinatorRoundDispatch.dispatchCollection x) := by
  generalize hd : CoordinatorRoundDispatch.dispatchCollection x = outcome
  unfold CoordinatorRoundDispatch.dispatchCollection at hd
  repeat' (split at hd <;> try dsimp only at hd)
  all_goals cases hd
  all_goals simp_all only [collectionParameters?, outcomeParameters?,
    dite_eq_left, ite_eq_left, ite_false]
  all_goals first
    | rfl
    | (exfalso; apply pending_choice_failure_false x <;> assumption)
    | (exfalso; apply choice_failure_false <;> assumption)

/-- Read only actual collection parameters from the retained physical dispatch.
Other source phases do not issue a later-assignment sampler. -/
def dispatchParameters? {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (cut : ReferenceActivePhysicalStep.DispatchCut x) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  match cut with
  | .collection _ _ _ _ outcome => outcomeParameters? outcome
  | _ => none

/-- Agreement with the original physical dispatch, including its finite cutoff
check and the internally constructed consistency data. -/
theorem parameters?_eq_physicalDispatch (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    parameters? x = dispatchParameters? (ReferenceActivePhysicalStep.dispatch x) := by
  unfold parameters? ReferenceActivePhysicalStep.dispatch
  cases x.state.coordinator with
  | first => rfl
  | live _ _ _ => rfl
  | dagger => rfl
  | collection payload ledger proposal =>
      dsimp only
      split
      · exact collectionParameters?_eq_dispatch _
      · rfl

/-- Derive the sampler's calendar coordinate from the actual checked clock
call before identifying the complete replacement vector. -/
theorem ownAssignmentVector_laterInstruction
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending = .ok started)
    (hinstruction : started.assignmentStart = some instruction) :
    LaterAssignmentStartOperation.ownAssignmentVector (withAssignment x v).row instruction.time = v := by
  rw [ReferenceActivePhysicalStep.later_instruction_time x payload ledger clock cutoff core
    started instruction hstart hinstruction, withAssignment_row,
    ownAssignmentVector_rowWithAssignment]

/-- Literal successful payload/base-score projection of an original result. -/
def payloadAndBaseScoreOfResult
    {eta : ReferencePrelaunchFollower.LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    {consistent : LaterAssignmentStartOperation.LocalConsistency old ledger}
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent) :
    Option (AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ)) :=
  match result with
  | .success output _ => some (output.payload, output.baseScore)
  | _ => none

/-- Read the actual successful payload and retained base scores. All original
failure records remain in `laterAssignmentStart`; this comparison projection
records their common absence of an installed payload. -/
def laterPayloadAndBaseScore?
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger) :
    Option (AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ)) :=
  payloadAndBaseScoreOfResult
    (LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row consistent)

private theorem payloadAndBaseScoreOfResult_finish
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : LaterAssignmentStartMeasurability.SuccessfulLawSelection old ledger instruction out) :
    payloadAndBaseScoreOfResult (LaterAssignmentStartOperation.finishCheckedSample
      old ledger instruction row consistent out hcall selection.cutoffReached
      selection.currentWeightPos selection.cutoffWeightPos selection.law selection.lawSelected) =
    (CheckedAssignmentSample.successfulSlowSet p
      (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time))).map
      (fun slow =>
        let payload := LaterAssignmentStartOperation.payloadInput old instruction out selection.law slow
        (payload, LaterAssignmentStartOperation.retainedBaseScore out payload)) := by
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> simp_all only [payloadAndBaseScoreOfResult, CheckedAssignmentSample.successfulSlowSet,
    Option.map_none, Option.map_some]

/-- At the actual selected law, the entire successful payload (including its
anchor and reconstructed queues) and retained base scores depend on the
coordinates only through the successful slow set. Prefix and orientation
failures share the absent projection, without identifying their raw tags.
All helper inputs are explicit local inputs; no truthful-ledger or feasible-law
condition is assumed. -/
theorem laterPayloadAndBaseScore?_fibre
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (input : LaterAssignmentStartMeasurability.LocalStartInput old)
    (left right : CompletePublicTable.CompleteRow p)
    (hf : match LaterAssignmentStartMeasurability.selectedSamplerParameters? old input with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector left input.2.1.time) =
        AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector right input.2.1.time)) :
    laterPayloadAndBaseScore? old input.1 input.2.1 left input.2.2 =
      laterPayloadAndBaseScore? old input.1 input.2.1 right input.2.2 := by
  rcases input with ⟨ledger, instruction, consistent⟩
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match] at hf
  unfold laterPayloadAndBaseScore? LaterAssignmentStartOperation.laterAssignmentStart
  cases hd : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason => rfl
  | success out hcall =>
      let selection := LaterAssignmentStartMeasurability.successfulLawSelection
        old ledger instruction out hcall
      have hrun (row : CompletePublicTable.CompleteRow p) :
          LaterAssignmentStartOperation.runReconstructionDecision old ledger instruction row consistent
            (.success out hcall) =
          LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row consistent
            out hcall selection.cutoffReached selection.currentWeightPos
            selection.cutoffWeightPos selection.law selection.lawSelected := by
        rfl
      simp only [hd] at hf ⊢
      rw [hrun left, hrun right, payloadAndBaseScoreOfResult_finish,
        payloadAndBaseScoreOfResult_finish]
      exact congrArg (Option.map fun slow =>
        let payload := LaterAssignmentStartOperation.payloadInput old instruction out selection.law slow
        (payload, LaterAssignmentStartOperation.retainedBaseScore out payload)) hf

/-- Conditional installation helper for two actual successful calls. The
success equations, original clock evidences, and equality of their returned
clock results are explicit inputs. This compares installed physical registers
and owned queues/service, never the retained raw assignment vectors. It does
not produce the dispatch cases or compare the ensuing physical tails. -/
theorem successful_installation_fibre
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (input : LaterAssignmentStartMeasurability.LocalStartInput old)
    (left right : CompletePublicTable.CompleteRow p)
    (hf : match LaterAssignmentStartMeasurability.selectedSamplerParameters? old input with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector left input.2.1.time) =
        AssignmentParameterFibreKernel.successfulSlowSet p theta
          (LaterAssignmentStartOperation.ownAssignmentVector right input.2.1.time))
    (leftOutput : LaterAssignmentStartOperation.SuccessfulStart old input.1 input.2.1 left)
    (rightOutput : LaterAssignmentStartOperation.SuccessfulStart old input.1 input.2.1 right)
    (hleft : leftOutput.localConsistency = input.2.2)
    (hright : rightOutput.localConsistency = input.2.2)
    (leftCall : LaterAssignmentStartOperation.laterAssignmentStart old input.1 input.2.1 left input.2.2 =
      .success leftOutput hleft)
    (rightCall : LaterAssignmentStartOperation.laterAssignmentStart old input.1 input.2.1 right input.2.2 =
      .success rightOutput hright)
    (leftClock : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence leftOutput)
    (rightClock : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence rightOutput)
    (hclock : leftClock.result = rightClock.result) :
    (CoordinatorAssignmentRegisterInstall.installLater leftOutput leftClock).registers =
        (CoordinatorAssignmentRegisterInstall.installLater rightOutput rightClock).registers ∧
      HEq (CoordinatorAssignmentRegisterInstall.installLater leftOutput leftClock).ownedRegisters
        (CoordinatorAssignmentRegisterInstall.installLater rightOutput rightClock).ownedRegisters ∧
      (CoordinatorAssignmentRegisterInstall.installLater leftOutput leftClock).retainedBaseScore =
        (CoordinatorAssignmentRegisterInstall.installLater rightOutput rightClock).retainedBaseScore := by
  have hp := laterPayloadAndBaseScore?_fibre old input left right hf
  simp only [laterPayloadAndBaseScore?, leftCall, rightCall, payloadAndBaseScoreOfResult,
    Option.some.injEq, Prod.mk.injEq] at hp
  have hr : leftOutput.reconstruction = rightOutput.reconstruction := by
    have h := leftOutput.reconstruction_eq.symm.trans rightOutput.reconstruction_eq
    injection h
  rcases hp with ⟨hpayload, hbase⟩
  let bundle (payload : AssignmentStartPayload.Input p eta)
      (reconstruction : AssignmentScoreReconstruction.ReconstructedStart input.1 input.2.1)
      (started : CoordinatorPhaseClock.StartRoundResult p) :
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p eta) ×
        CoordinatorLiveServiceFinish.OwnedRegisters registers :=
    ⟨{ payload := payload
       priorClock := started.clock
       pendingAtChoice := started.pending
       time := input.2.1.time
       gridBoundary := started.clock.g
       complementScores := fun j => AssignmentScoreReconstruction.sourceScore reconstruction j.1 },
      { queue := fun j => AssignmentScoreReconstruction.initialQueue reconstruction j.1
        previousService := fun j => (reconstruction.registers.current j.1).lastService }⟩
  have hb : bundle leftOutput.payload leftOutput.reconstruction leftClock.result =
      bundle rightOutput.payload rightOutput.reconstruction rightClock.result :=
    (congrArg (fun payload => bundle payload leftOutput.reconstruction leftClock.result) hpayload).trans
      (congrArg₂ (bundle rightOutput.payload) hr hclock)
  have hi := Sigma.mk.inj_iff.mp hb
  exact ⟨hi.1, hi.2, hbase⟩

/-- A failed reconstruction really leaves the optional selected parameters
absent. This is derived from the original operation result, not a null-mass
assumption about sampler failures. -/
theorem selectedSamplerParameters?_eq_none_of_reconstructionFailure
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (input : LaterAssignmentStartMeasurability.LocalStartInput old)
    (row : CompletePublicTable.CompleteRow p)
    (reason : AssignmentScoreReconstruction.Failure)
    (hfailure : LaterAssignmentStartOperation.laterAssignmentStart
      old input.1 input.2.1 row input.2.2 = .reconstructionFailure reason) :
    LaterAssignmentStartMeasurability.selectedSamplerParameters? old input = none := by
  rcases input with ⟨ledger, instruction, consistent⟩
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
  cases hd : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure _ => rfl
  | success out hcall =>
      let selection := LaterAssignmentStartMeasurability.successfulLawSelection
        old ledger instruction out hcall
      have hrun : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row consistent =
          LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row consistent
            out hcall selection.cutoffReached selection.currentWeightPos
            selection.cutoffWeightPos selection.law selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hd]
        rfl
      rw [hrun] at hfailure
      unfold LaterAssignmentStartOperation.finishCheckedSample at hfailure
      split at hfailure <;> cases hfailure

end Bandits.Support.ReferenceLaterAssignmentFibreStep

end
