/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceLaterAssignmentFibreStep

/-!
# Physical assignment-effect congruence

Internal pointwise comparisons of the existing physical round operations.
Sources: `sources/zip4/manuscript/06_interruptions.tex:195-233,235-296,376-423`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

The sole perturbation is `ReferenceLaterAssignmentFibreStep.withAssignment`,
which changes the complete K+1 assignment-coordinate vector in the selected
current row while retaining its original arrays, non-assignment controls and
affine reads. The incoming state, rewards, activations and local operation
arguments are literal and shared.

Exports compare the actual follower preparation and complete post-choice
observations, the live and collection coordinator tails, full UP reception
diagnostics, and computed physical evidence. Their local equality premises
for the actual selected arm, DOWN view and coordinator observation remain
explicit. These are internal conditional comparisons; they do not construct a
completed sampler fibre or prove a manuscript theorem.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceAssignmentEffectCongruence


variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

private theorem assignment_state (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    (ReferenceLaterAssignmentFibreStep.withAssignment x v).state = x.state := rfl

private theorem assignment_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    (ReferenceLaterAssignmentFibreStep.withAssignment x v).time = x.time := rfl

/-- The pointwise perturbation keeps the literal physical state, time and
complete reward table fixed. -/
theorem with_assignment_fixed_round_data (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    (ReferenceLaterAssignmentFibreStep.withAssignment x v).state = x.state ∧
      (ReferenceLaterAssignmentFibreStep.withAssignment x v).time = x.time ∧
      (ReferenceLaterAssignmentFibreStep.withAssignment x v).rewards = x.rewards :=
  ⟨rfl, rfl, rfl⟩

private theorem prepare_arm (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    (ReferenceActivePhysicalStep.prepare x).coordinator.arm =
      (ReferenceActivePhysicalStep.dispatch x).arm := rfl

private theorem named_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T)
    (label : ContinuousControlSlice.NamedLabel) :
    ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 (Sum.inl label) = (x.row.2 t).1 (Sum.inl label) :=
  ReferenceLaterAssignmentFibreStep.rowWithAssignment_scalar x v t ⟨Sum.inl label, by rintro ⟨r, h⟩; cases h⟩

private theorem pilot_scalar (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) (i : Fin p.m) :
    ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 (ContinuousControlSlice.Label.pilot i) =
      (x.row.2 t).1 (ContinuousControlSlice.Label.pilot i) :=
  ReferenceLaterAssignmentFibreStep.rowWithAssignment_scalar x v t
    ⟨ContinuousControlSlice.Label.pilot i, by rintro ⟨r, h⟩; cases h⟩

private theorem slot_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    PublicDiscreteDraws.slotDraw ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.slotDraw (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.slotDraw, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.slot, named_scalar]

private theorem selected_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.selectedFollowerDraw, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.sel, named_scalar]

private theorem recorder_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
        ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.recorderSourceDraw, ContinuousControlSlice.coordinate,
    ContinuousControlSlice.Label.rec, named_scalar]

private theorem pilot_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) (i : Fin p.m) :
    PublicDiscreteDraws.pilotDraw (K_pos p) i ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 =
      PublicDiscreteDraws.pilotDraw (K_pos p) i (x.row.2 t).1 := by
  simp only [PublicDiscreteDraws.pilotDraw, ContinuousControlSlice.coordinate, pilot_scalar]

private theorem tuple_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 t).1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K (x.row.2 t).1 := by
  apply OrderedTupleSampler.sample_eq_of_tupleInputs_eq
  intro i
  exact ReferenceLaterAssignmentFibreStep.rowWithAssignment_scalar x v t
    ⟨ContinuousControlSlice.Label.tuple i, by rintro ⟨r, h⟩; cases h⟩

/-- Every calendar coordinate in the actual proposal row is unchanged by the
assignment-vector replacement. -/
theorem proposal_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) =
      FollowerCutoffScan.completeRowProposalBit p rate.eta.val x.row := by
  funext t
  simp only [FollowerCutoffScan.completeRowProposalBit, CompletePublicTable.completeRowLearning,
    ContinuousControlSlice.Label.prop, named_scalar]

private theorem public_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (t : Fin p.T) :
    ActiveFollowerLifecycle.publicRowOfCompleteRow (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t =
      ActiveFollowerLifecycle.publicRowOfCompleteRow x.row t := by
  simp only [ActiveFollowerLifecycle.publicRowOfCompleteRow, slot_row, selected_row,
    tuple_row, pilot_row]

/-- The actual checked logging call, including its failure tag and appended
record data, is unchanged. -/
theorem logging_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1))
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (own : Fin p.K × ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ActiveFollowerLogging.checkedLogging i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) activation t own state =
      ActiveFollowerLogging.checkedLogging i x.row activation t own state := by
  have hl : ReferencePrelaunchFollower.loggingRound i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) activation t own =
      ReferencePrelaunchFollower.loggingRound i x.row activation t own := by
    simp only [ReferencePrelaunchFollower.loggingRound, slot_row, recorder_row, pilot_row,
      ContinuousControlSlice.Label.thin, named_scalar]
  have hu : ActiveFollowerLogging.loggingUpdate i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v)
      activation t own state = ActiveFollowerLogging.loggingUpdate i x.row activation t own state := by
    unfold ActiveFollowerLogging.loggingUpdate ReferencePrelaunchFollower.logAt
    split_ifs <;> simp_all only [not_true_eq_false]
  simp only [ActiveFollowerLogging.checkedLogging, hu]

/-- The actual gated raw arrival is unchanged, including suppression when the
recorder gate fails. -/
theorem raw_arrival_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (observation : ReferencePrelaunchFollower.Observation p) :
    ActiveFollowerQueueOperation.rawArrival rate.eta i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t message observation =
      ActiveFollowerQueueOperation.rawArrival rate.eta i x.row t message observation := by
  have hg : ActiveFollowerQueueOperation.recorderGate rate.eta i
      (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t message ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i x.row t message := by
    simp only [ActiveFollowerQueueOperation.recorderGate,
      CanonicalRecordingSlice.recordingMask, slot_row, recorder_row, pilot_row,
      ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.thin, named_scalar]
  by_cases h : ActiveFollowerQueueOperation.recorderGate rate.eta i x.row t message
  · simp only [ActiveFollowerQueueOperation.rawArrival, ite_eq_left h, ite_eq_left (hg.mpr h),
      ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.thin, named_scalar]
  · simp only [ActiveFollowerQueueOperation.rawArrival, ite_eq_right h,
      ite_eq_right (fun hv => h (hg.mp hv))]

/-- The actual occupied service operation is unchanged, including every
checked failure branch and zero-arrival service. -/
theorem service_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1))
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) (hs : state.status ≠ .unoccupied) :
    DeclaredFollowerLocalRound.recordOrServiceThenDown rate i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v)
        activation t active arm observation state =
      DeclaredFollowerLocalRound.recordOrServiceThenDown rate i x.row
        activation t active arm observation state := by
  rcases state with ⟨lastDown, served, previous, backlog, status, batch, buffer, marker⟩
  cases status with
  | unoccupied => exact False.elim (hs rfl)
  | pending =>
    cases lastDown <;>
      simp only [DeclaredFollowerLocalRound.recordOrServiceThenDown, dite_eq_right hs,
        ActiveFollowerQueueOperation.checkedService, raw_arrival_row] <;>
      split_ifs <;> rfl
  | released =>
    cases lastDown <;>
      simp only [DeclaredFollowerLocalRound.recordOrServiceThenDown, dite_eq_right hs,
        ActiveFollowerQueueOperation.checkedService, raw_arrival_row] <;>
      split_ifs <;> rfl

/-- The whole actual DOWN cut is unchanged, retaining its expected word,
decoder diagnostics, rejection, recovery, and all output-failure tags. -/
theorem down_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceDownReception.referenceDownCut p view i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t observation rate state =
      ReferenceDownReception.referenceDownCut p view i x.row t observation rate state := by
  have he : ReferenceDownReception.expectedDownFlatWord view i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t =
      ReferenceDownReception.expectedDownFlatWord view i x.row t := by
    cases view with
    | none => rfl
    | some view =>
      have hg :
          (CoordinatorLocalArmChoice.coordinatorArmChoice view.payload view.pendingAtChoice
            view.cutoff t view.complementWeights (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) ≠ none ∧
            ReferenceDownReception.selectedDownSenderBranch view i
              (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t) ↔
          (CoordinatorLocalArmChoice.coordinatorArmChoice view.payload view.pendingAtChoice
            view.cutoff t view.complementWeights x.row ≠ none ∧
            ReferenceDownReception.selectedDownSenderBranch view i x.row t) := by
        rw [ReferenceLaterAssignmentFibreStep.coordinatorArmChoice_row x v t
          view.payload view.pendingAtChoice view.cutoff view.complementWeights]
        simp only [ReferenceDownReception.selectedDownSenderBranch, slot_row, selected_row]
      by_cases h : CoordinatorLocalArmChoice.coordinatorArmChoice view.payload view.pendingAtChoice
          view.cutoff t view.complementWeights x.row ≠ none ∧
          ReferenceDownReception.selectedDownSenderBranch view i x.row t
      · simp only [ReferenceDownReception.expectedDownFlatWord,
          ite_eq_left h, ite_eq_left (hg.mpr h)]
      · simp only [ReferenceDownReception.expectedDownFlatWord,
          ite_eq_right h, ite_eq_right (fun hv => h (hg.mp hv))]
  have hd : ActiveFollowerDownAcceptance.currentDecodeStep p i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v)
      t observation rate state =
      ActiveFollowerDownAcceptance.currentDecodeStep p i x.row t observation rate state := by
    simp only [ActiveFollowerDownAcceptance.currentDecodeStep,
      ActiveFollowerDownAcceptance.currentRoundInput, slot_row, selected_row, ReferenceLaterAssignmentFibreStep.rowWithAssignment_affine]
  have hc (message : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
      (hstart : (ActiveFollowerDownAcceptance.downStart p rate message).val ≤ t.val) :
      ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message t hstart (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) =
        ActiveFollowerDownAcceptance.acceptedCutoffScan p rate message t hstart x.row := by
    simp only [ActiveFollowerDownAcceptance.acceptedCutoffScan,
      FollowerCutoffScan.completeRowCutoffScan, proposal_row]
  simp only [ReferenceDownReception.referenceDownCut, he,
    ActiveFollowerDownAcceptance.downSelected, slot_row, selected_row, hd, hc]

/-- The whole actual follower record-or-service result is unchanged. -/
theorem record_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1) (arm : Fin p.K)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ReferenceActivePhysicalStep.recordFollower view i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) activation t active arm observation state =
      ReferenceActivePhysicalStep.recordFollower view i x.row activation t active arm observation state := by
  by_cases hs : state.status = .unoccupied
  · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_left hs, logging_row, down_row]
  · simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hs, service_row x v i activation t active arm observation state hs]

/-- The actual release and proposal-finish call is unchanged on its complete
result, including lifecycle failures. -/
theorem release_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state post : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p) :
    DeclaredFollowerLocalRound.releaseAndFinish rate i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) t observation state memory post =
      DeclaredFollowerLocalRound.releaseAndFinish rate i x.row t observation state memory post := by
  simp only [DeclaredFollowerLocalRound.releaseAndFinish, public_row,
    ActiveFollowerLifecycle.finishRound, proposal_row]

/-- The actual follower PREPARE call changes only its retained complete row;
arm, post-StartRound configuration, private buffers and every other prepared
field are unchanged. -/
theorem prepare_follower_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1))
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (active : activation.val ≤ t.val + 1)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    DeclaredFollowerLocalRound.prepare rate i (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) activation t active configuration =
      { DeclaredFollowerLocalRound.prepare rate i x.row activation t active configuration with
        row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } := by
  cases configuration with
  | dagger => rfl
  | ordinary state memory =>
    cases hs : ActiveFollowerLifecycle.startRound rate.eta t state memory with
    | error reason => simp only [DeclaredFollowerLocalRound.prepare, hs]
    | ok result =>
      rcases result with ⟨choiceState, choiceMemory⟩
      cases ho : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i x.row activation t choiceState with
      | failure => simp only [DeclaredFollowerLocalRound.prepare, hs,
          ReferenceLaterAssignmentFibreStep.checkedUpOffer_row, ho]
      | noOffer =>
        cases hc : ActiveFollowerArmChoice.followerArmChoice choiceState x.row t i none <;>
          simp only [DeclaredFollowerLocalRound.prepare, hs,
            ReferenceLaterAssignmentFibreStep.checkedUpOffer_row, ho,
            ReferenceLaterAssignmentFibreStep.followerArmChoice_row, hc]
      | offer offered =>
        cases hc : ActiveFollowerArmChoice.followerArmChoice choiceState x.row t i (some offered) <;>
          simp only [DeclaredFollowerLocalRound.prepare, hs,
            ReferenceLaterAssignmentFibreStep.checkedUpOffer_row, ho,
            ReferenceLaterAssignmentFibreStep.followerArmChoice_row, hc]

/-- On prepared primitive fields identical apart from the row, the actual
`finishFollower` equation holds without selecting a success branch. -/
theorem finish_follower_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow : prepared.row = x.row)
    (observation : ReferencePrelaunchFollower.Observation p) :
    ReferenceActivePhysicalStep.finishFollower view { prepared with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } observation =
      ReferenceActivePhysicalStep.finishFollower view prepared observation := by
  simp only [ReferenceActivePhysicalStep.finishFollower, record_row, release_row, hrow]

/-- Simultaneous coordinator and follower actions agree when the two actual
dispatches select the same arm. -/
theorem actions_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm) :
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arms.actions =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arms.actions := by
  funext player
  unfold ReferenceActiveFeedbackCut.ActionInputs.actions
  split
  · exact ha
  · let i : Fin (p.m - 1) := ActiveRoundActions.followerIndex p.two_le_m player (by assumption)
    change (DeclaredFollowerLocalRound.prepare rate i (ReferenceLaterAssignmentFibreStep.withAssignment x v).row
        (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm =
      (DeclaredFollowerLocalRound.prepare rate i (ReferenceLaterAssignmentFibreStep.withAssignment x w).row
        (x.state.activations i) x.time (x.active i) (x.state.followers i)).arm
    rw [ReferenceLaterAssignmentFibreStep.withAssignment_row,
      ReferenceLaterAssignmentFibreStep.withAssignment_row]
    exact (congrArg DeclaredFollowerLocalRound.PreparedRound.arm
      (prepare_follower_row x v i _ _ _ _)).trans
        (congrArg DeclaredFollowerLocalRound.PreparedRound.arm
          (prepare_follower_row x w i _ _ _ _)).symm

/-- The entire grid-feedback function agrees, using the original fixed reward
table and the actual simultaneous actions. -/
theorem feedback_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm) :
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).feedback.feedback =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).feedback.feedback := by
  funext player
  rw [ReferenceActivePhysicalStep.PreparedRound.feedback_rule, ReferenceActivePhysicalStep.PreparedRound.feedback_rule, actions_fibre x v w ha]
  rfl

/-- Every typed own action/observation entry agrees as well as the raw grid
feedback. -/
theorem own_entries_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm) :
    (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x v)).ownEntries =
      (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x w)).ownEntries := by
  have ha' := actions_fibre x v w ha
  have hg := feedback_fibre x v w ha
  funext player
  rw [ReferenceActivePhysicalStep.step_own_entry,
    ReferenceActivePhysicalStep.step_own_entry, ha', hg]

/-- The three simultaneous physical outputs compared by this module. Rewards
are the same original table carried by `x`. -/
theorem simultaneous_outputs_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm) :
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arms.actions =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arms.actions ∧
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).feedback.feedback =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).feedback.feedback ∧
    (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x v)).ownEntries =
      (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x w)).ownEntries := by
  exact ⟨actions_fibre x v w ha, feedback_fibre x v w ha, own_entries_fibre x v w ha⟩

/-- The full actual follower observations agree when the actual DOWN views
also agree. This retains each configuration, failure, DOWN input and cut. -/
theorem followers_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm)
    (hv : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).downView =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).downView) :
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).observeFollower =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).observeFollower := by
  have ho : (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).feedback.observations =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).feedback.observations := by
    funext player
    rw [ReferenceActiveFeedbackCut.FeedbackCut.observations_eq,
      ReferenceActiveFeedbackCut.FeedbackCut.observations_eq, feedback_fibre x v w ha]
  funext i
  change ReferenceActivePhysicalStep.finishFollower (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).downView
      (DeclaredFollowerLocalRound.prepare rate i (ReferenceLaterAssignmentFibreStep.withAssignment x v).row
        (x.state.activations i) x.time (x.active i) (x.state.followers i)) _ =
    ReferenceActivePhysicalStep.finishFollower (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).downView
      (DeclaredFollowerLocalRound.prepare rate i (ReferenceLaterAssignmentFibreStep.withAssignment x w).row
        (x.state.activations i) x.time (x.active i) (x.state.followers i)) _
  rw [ReferenceLaterAssignmentFibreStep.withAssignment_row, ReferenceLaterAssignmentFibreStep.withAssignment_row, prepare_follower_row, prepare_follower_row,
    finish_follower_row x v _ _ (ReferenceActivePhysicalStep.local_prepare_alignment i x.row _ _ _ _).1,
    finish_follower_row x w _ _ (ReferenceActivePhysicalStep.local_prepare_alignment i x.row _ _ _ _).1,
    hv, ho]

/-- Assemble computed-evidence equality from the three actual local matching
conditions. No sampler or dispatch-fibre conclusion is assumed. -/
theorem computed_evidence_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm)
    (hv : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).downView =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).downView)
    (hc : (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).observeCoordinator =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).observeCoordinator) :
    ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  have ha' := actions_fibre x v w ha
  have hg := feedback_fibre x v w ha
  have hf := followers_fibre x v w ha hv
  have he : (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x v)).ownEntries =
      (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x w)).ownEntries := by
    funext player
    rw [ReferenceActivePhysicalStep.step_own_entry, ReferenceActivePhysicalStep.step_own_entry, ha', hg]
  have hn : (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x v)).next = (ReferenceActivePhysicalStep.step (ReferenceLaterAssignmentFibreStep.withAssignment x w)).next := by
    exact congrArg₂ (fun (coordinator : ReferenceActivePhysicalStep.CoordinatorObservation p rate)
      (followers : Fin (p.m - 1) → ReferenceActivePhysicalStep.FollowerObservation p rate) =>
        ReferenceActivePhysicalStep.State.mk coordinator.configuration coordinator.upDecoderBank
          x.state.activations (fun i => (followers i).configuration)) hc hf
  change ReferenceActivePhysicalHorizon.RoundEvidence.mk x.state x.time _ _ _ _ _ _ =
    ReferenceActivePhysicalHorizon.RoundEvidence.mk x.state x.time _ _ _ _ _ _
  congr 1

private theorem rejected_coordinator (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hs : (ReferenceActivePhysicalStep.dispatch x).selection = none) :
    (ReferenceActivePhysicalStep.prepare x).observeCoordinator =
      ReferenceActivePhysicalStep.coordinatorFailure x.state.upDecoderBank .dispatchRejected none none := by
  unfold ReferenceActivePhysicalStep.PreparedRound.observeCoordinator
  change (if (ReferenceActivePhysicalStep.dispatch x).selection = none then _ else _) = _
  rw [ite_eq_left hs]
  dsimp only [ReferenceActivePhysicalStep.prepare]
  unfold ReferenceActivePhysicalStep.dispatch
  rw [hphase]
  dsimp only [CoordinatorRoundDispatch.dispatch]
  split_ifs <;> rfl

/-- Internal rejected-branch comparison. Both actual selection failures are
explicit inputs here; this helper does not assert that sampler failure is null
or identify the retained raw dispatch tags. All follower tails still run. -/
private theorem computedEvidence_of_rejected_collection (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (hv : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).selection = none)
    (hw : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).selection = none) :
    ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  apply computed_evidence_fibre x v w
  · simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hv, hw]
  · simp only [ReferenceActivePhysicalStep.DispatchCut.downView, hv, hw, Option.map_none]
  · rw [rejected_coordinator (ReferenceLaterAssignmentFibreStep.withAssignment x v) payload ledger proposal hphase hv,
      rejected_coordinator (ReferenceLaterAssignmentFibreStep.withAssignment x w) payload ledger proposal hphase hw]
    rfl

/-- The finite-cutoff failure has no sampler, and its full physical evidence
is independent of the complete replacement vector, including follower tails. -/
theorem computed_evidence_collection_invalid_cutoff (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T))
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  apply computedEvidence_of_rejected_collection x payload ledger proposal hphase v w
  · rw [(ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff (ReferenceLaterAssignmentFibreStep.withAssignment x v)
      payload ledger proposal hphase hcutoff).1]
    rfl
  · rw [(ReferenceActivePhysicalStep.dispatch_collection_invalid_cutoff (ReferenceLaterAssignmentFibreStep.withAssignment x w)
      payload ledger proposal hphase hcutoff).1]
    rfl

/-- The actual clock finish is invariant under the changed assignment
coordinates, including both its success and failure results. -/
theorem clock_finish_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (time : Fin p.T)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (pending : Finset (Fin (p.m - 1))) :
    CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) =
      CoordinatorPhaseClock.finishRound p rate.eta.val time clock pending x.row := by
  simp only [CoordinatorPhaseClock.finishRound, proposal_row]

/-- The actual confirmation update is unchanged, including invalid-input and
no-confirmation paths. -/
theorem confirmation_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (time : Fin p.T)
    (payload : ReferenceActivePhysicalStep.Payload rate) (pending : Finset (ActiveRoundActions.Follower p.m))
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (observation : Fin (D p + 1)) :
    CoordinatorLocalArmChoice.confirmationUpdate payload pending cutoff time
      (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) observation =
    CoordinatorLocalArmChoice.confirmationUpdate payload pending cutoff time x.row observation := by
  have hg : CoordinatorLocalArmChoice.downConfirmationEvent payload pending cutoff time
      ((ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2 time) observation ↔
      CoordinatorLocalArmChoice.downConfirmationEvent payload pending cutoff time (x.row.2 time) observation := by
    simp only [CoordinatorLocalArmChoice.downConfirmationEvent,
      CoordinatorLocalArmChoice.currentDownHash, slot_row, selected_row,
      ReferenceLaterAssignmentFibreStep.rowWithAssignment_affine]
  by_cases hv : CoordinatorLocalArmChoice.ConfirmationInputsValid payload cutoff time
  · simp only [CoordinatorLocalArmChoice.confirmationUpdate,
      CoordinatorLocalArmChoice.confirmationUpdateCore, dite_eq_left hv]
    by_cases h : CoordinatorLocalArmChoice.downConfirmationEvent payload pending cutoff time (x.row.2 time) observation
    · rw [ite_eq_left h, ite_eq_left (hg.mpr h), selected_row]
    · rw [ite_eq_right h, ite_eq_right (fun hv => h (hg.mp hv))]
  · simp only [CoordinatorLocalArmChoice.confirmationUpdate,
      CoordinatorLocalArmChoice.confirmationUpdateCore, dite_eq_right hv]

/-- The checked recording operation agrees on the two rows, retaining its
domain and rejection branches. -/
theorem recorder_run_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (input : CoordinatorRecordingOperation.Input p) (hrow : input.row = x.row) :
    CoordinatorRecordingOperation.run { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } =
      CoordinatorRecordingOperation.run input := by
  have hi : CoordinatorRecordingOperation.InputsValid { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } ↔
      CoordinatorRecordingOperation.InputsValid input := by
    constructor <;> intro h <;>
      exact ⟨h.sigma_le_terminal, h.boundary_le_terminal, h.eta_pos, h.eta_source_cap,
        h.anchor_pos, h.current_pos, h.anchor_le_current, h.current_le_twice_anchor⟩
  by_cases hv : CoordinatorRecordingOperation.InputsValid input
  · simp only [CoordinatorRecordingOperation.run, dite_eq_left hv, dite_eq_left (hi.mpr hv)]
    have hslot : CoordinatorRecordingOperation.selectedSlot
        { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } =
        CoordinatorRecordingOperation.selectedSlot input := by
      simp only [CoordinatorRecordingOperation.selectedSlot, ContinuousLearningRows.sliceAt,
        ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.slot, hrow, named_scalar]
    have hrec : CoordinatorRecordingOperation.selectedRecorder
        { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } =
        CoordinatorRecordingOperation.selectedRecorder input := by
      simp only [CoordinatorRecordingOperation.selectedRecorder, ContinuousLearningRows.sliceAt,
        ContinuousControlSlice.coordinate, ContinuousControlSlice.Label.rec, hrow, named_scalar]
    have hmask : CoordinatorRecordingOperation.ownMaskPasses
        { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } ↔
        CoordinatorRecordingOperation.ownMaskPasses input := by
      simp only [CoordinatorRecordingOperation.ownMaskPasses, CanonicalRecordingSlice.recordingMask,
        ContinuousLearningRows.sliceAt, hrow, pilot_row]
    have hraw : CoordinatorRecordingOperation.coordinatorRawGateMass
        { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } (hi.mpr hv) =
        CoordinatorRecordingOperation.coordinatorRawGateMass input hv := rfl
    have hthin : ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
        (ContinuousLearningRows.sliceAt input.time (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v).2) =
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          (ContinuousLearningRows.sliceAt input.time input.row.2) := by
      simp only [ContinuousLearningRows.sliceAt, ContinuousControlSlice.coordinate,
        ContinuousControlSlice.Label.thin, hrow, named_scalar]
    have hfrozen : CoordinatorRecordingOperation.isFrozen
        { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } ↔
        CoordinatorRecordingOperation.isFrozen input := Iff.rfl
    have hfloor : CoordinatorRecordingOperation.floorArrival
        { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } =
        CoordinatorRecordingOperation.floorArrival input := rfl
    simp only [CoordinatorRecordingOperation.executeValid, hslot, hrec, hmask, hraw, hthin,
      hfrozen, hfloor]
  · simp only [CoordinatorRecordingOperation.run, dite_eq_right hv,
      dite_eq_right (fun h => hv (hi.mp h))]

/-- The actual coordinator recorder bridge inherits complete run equality. -/
theorem recorder_bridge_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (payload : ReferenceActivePhysicalStep.Payload rate)
    (input : CoordinatorRecorderComplementBridge.Input payload) (hrow : input.row = x.row) :
    CoordinatorRecorderComplementBridge.run { input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } =
      CoordinatorRecorderComplementBridge.run input := by
  change CoordinatorRecordingOperation.run
      { CoordinatorRecorderComplementBridge.recorderInput input with
        row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } =
    CoordinatorRecordingOperation.run (CoordinatorRecorderComplementBridge.recorderInput input)
  exact recorder_run_row x v (CoordinatorRecorderComplementBridge.recorderInput input) hrow

/-- The direct live POST-CHOICE operation agrees for identical literal
registers, owned queues, base scores and start result, given only equal actual
dispatch arms. The operation arguments are not claimed to be produced by both
dispatches. -/
theorem live_post_choice_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    ReferenceActivePhysicalStep.livePostChoice (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)) registers owned base started =
      ReferenceActivePhysicalStep.livePostChoice (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) registers owned base started := by
  have ho : (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).coordinatorObservation =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).coordinatorObservation :=
    congrFun (feedback_fibre x v w ha) (ActiveRoundActions.coordinator p.two_le_m)
  let input : CoordinatorRecorderComplementBridge.Input registers.payload := {
    currentWeights := registers.complementWeights
    time := x.time
    gridBoundary := started.clock.g
    row := x.row
    ownArm := (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm
    observation := (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).coordinatorObservation
    mode := .live (decide (started.pending = ∅)) }
  have hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)) registers started) =
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) registers started) := by
    simp only [ReferenceActivePhysicalStep.liveRecordingInput, ReferenceLaterAssignmentFibreStep.withAssignment_row]
    change CoordinatorRecorderComplementBridge.run {input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v} = _
    rw [recorder_bridge_row x v registers.payload input rfl]
    have hw := recorder_bridge_row x w registers.payload input rfl
    dsimp only [input] at hw
    rw [ha, ho] at hw
    simpa only [input, ha, ho, assignment_time, prepare_arm] using hw.symm
  have hc (z : CheckedAssignmentSample.AssignmentVector p) := confirmation_row x z x.time
    registers.payload started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).coordinatorObservation
  have hf (z : CheckedAssignmentSample.AssignmentVector p) (pending : Finset (Fin (p.m - 1))) :=
    clock_finish_row x z x.time started.clock pending
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) registers started) with
  | none => simp only [ReferenceActivePhysicalStep.livePostChoice, hr, hrecord, assignment_state]
  | some recording =>
    cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
    | error reason =>
      simp only [ReferenceActivePhysicalStep.livePostChoice, hr, hrecord, hservice, assignment_state]
    | ok serviced =>
      simp only [ReferenceActivePhysicalStep.livePostChoice, hr, hrecord, hservice, ho,
        ReferenceLaterAssignmentFibreStep.withAssignment_row, assignment_state, assignment_time, hc]
      cases hconfirm : CoordinatorLocalArmChoice.confirmationUpdate registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time x.row
          (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).coordinatorObservation with
      | none => rfl
      | some pending =>
        change Finset (Fin (p.m - 1)) at pending
        dsimp only
        rw [hf v pending, hf w pending]

/-- The actual `S.prepare` follower component differs only in its row. -/
theorem prepared_follower_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1)) :
    (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).followers.followers i =
      { (ReferenceActivePhysicalStep.prepare x).followers.followers i with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v } := by
  change DeclaredFollowerLocalRound.prepare rate i (ReferenceLaterAssignmentFibreStep.withAssignment x v).row
      (x.state.activations i) x.time (x.active i) (x.state.followers i) = _
  rw [ReferenceLaterAssignmentFibreStep.withAssignment_row]
  exact prepare_follower_row x v i _ _ _ _

/-- The selected follower's actual PREPARE arm is invariant. -/
theorem prepared_follower_arm (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1)) :
    ((ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).followers.followers i).arm =
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).arm := by
  rw [prepared_follower_row]

/-- The prepared follower configuration is unchanged. In particular, the
already saved sparse-record buffer and partial DOWN batch are retained. -/
theorem prepared_follower_configuration (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (i : Fin (p.m - 1)) :
    ((ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).followers.followers i).configuration =
      ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
  rw [prepared_follower_row]

/-- The actual selected UP reception input is unchanged, including its
selected follower, calendar time, sample and decoder-bank data. -/
theorem reception_input_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p)
    (inputs : ReferenceUpReception.ReceptionLocalInputs rate) (t : Fin p.T) :
    ReferenceUpReception.receptionInputAtRow rate (ReferenceLaterAssignmentFibreStep.rowWithAssignment x v) inputs t =
      ReferenceUpReception.receptionInputAtRow rate x.row inputs t := by
  simp only [ReferenceUpReception.receptionInputAtRow,
    CoordinatorUpMeasurability.receptionInputAtRow, CoordinatorUpMeasurability.receptionInputAtControl,
    CoordinatorUpMeasurability.selectedChannelFollower,
    CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw, slot_row, selected_row,
    ReferenceLaterAssignmentFibreStep.rowWithAssignment_affine]

/-- The actual UP sender index is selected from an unchanged coordinate. -/
theorem up_index_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalStep.upSenderIndex (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalStep.upSenderIndex x := by
  simp only [ReferenceActivePhysicalStep.upSenderIndex, ReferenceLaterAssignmentFibreStep.withAssignment_row,
    CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw, selected_row, assignment_time]
  rfl

/-- The actual selected sender's current UP offer word is derived from the
same prepared follower and unchanged UP coordinate on both calls. -/
theorem up_expected_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)) =
      ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) := by
  simp only [ReferenceActivePhysicalStep.upExpected, up_index_row,
    prepared_follower_row, ReferenceUpReception.currentOfferWord,
    ReferenceLaterAssignmentFibreStep.checkedUpOffer_row]

/-- The full actual `receiveUp` result agrees for the same literal ledger,
including every `UpCut` diagnostic field and wrong-unique suppression. -/
theorem receive_up_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) :
    ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)) ledger =
      ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) ledger := by
  have ho : (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).coordinatorObservation =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).coordinatorObservation :=
    congrFun (feedback_fibre x v w ha) (ActiveRoundActions.coordinator p.two_le_m)
  simp only [ReferenceActivePhysicalStep.receiveUp, ReferenceActivePhysicalStep.upInputs, ReferenceActivePhysicalStep.upExpected, up_index_row,
    prepared_follower_row, ReferenceLaterAssignmentFibreStep.withAssignment_row,
    ReferenceUpReception.receiveUpFilteredAtRow,
    ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow, reception_input_row,
    ReferenceUpReception.currentOfferWord, ReferenceLaterAssignmentFibreStep.checkedUpOffer_row, ho,
    assignment_state, assignment_time]

/-- The actual collection finish agrees for a shared recording and UP cut,
retaining the returned decoder bank across all later failure branches. -/
theorem collection_finish_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p) (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p) (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    ReferenceActivePhysicalStep.collectionFinish (x := ReferenceLaterAssignmentFibreStep.withAssignment x v) payload started recording cut =
      ReferenceActivePhysicalStep.collectionFinish (x := ReferenceLaterAssignmentFibreStep.withAssignment x w) payload started recording cut := by
  simp only [ReferenceActivePhysicalStep.collectionFinish, ReferenceLaterAssignmentFibreStep.withAssignment_row, clock_finish_row]
  rfl

/-- The full direct collection POST-CHOICE operation agrees for literal
payload, ledger, start result and weights, given only equal actual dispatch
arms. Recorder rejection, invalid reception, decoder rejection, enabled
zero-arrival service, disabled preservation and all finish failures remain in
the compared observation. -/
theorem collection_post_choice_fibre (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v w : CheckedAssignmentSample.AssignmentVector p)
    (ha : (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm =
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x w)).arm)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)) payload ledger started weights =
      ReferenceActivePhysicalStep.collectionPostChoice (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) payload ledger started weights := by
  have ho : (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).coordinatorObservation =
      (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)).coordinatorObservation :=
    congrFun (feedback_fibre x v w ha) (ActiveRoundActions.coordinator p.two_le_m)
  let input : CoordinatorRecorderComplementBridge.Input payload := {
    currentWeights := weights
    time := x.time
    gridBoundary := started.clock.g
    row := x.row
    ownArm := (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x v)).arm
    observation := (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)).coordinatorObservation
    mode := .collection }
  have hr : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x v)) payload started weights) =
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput (ReferenceActivePhysicalStep.prepare (ReferenceLaterAssignmentFibreStep.withAssignment x w)) payload started weights) := by
    simp only [ReferenceActivePhysicalStep.collectionRecordingInput, ReferenceLaterAssignmentFibreStep.withAssignment_row]
    change CoordinatorRecorderComplementBridge.run {input with row := ReferenceLaterAssignmentFibreStep.rowWithAssignment x v} = _
    rw [recorder_bridge_row x v payload input rfl]
    have hw := recorder_bridge_row x w payload input rfl
    dsimp only [input] at hw
    rw [ha, ho] at hw
    simpa only [input, ha, ho, assignment_time, prepare_arm] using hw.symm
  simp only [ReferenceActivePhysicalStep.collectionPostChoice, hr, receive_up_fibre x v w ha,
    collection_finish_row x v w]
  rfl

private theorem collection_core_row (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (v : CheckedAssignmentSample.AssignmentVector p) (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate) (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T) :
    CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput (ReferenceLaterAssignmentFibreStep.withAssignment x v) payload ledger clock cutoff) ↔
      CoordinatorRoundDispatch.CollectionCoreValid (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff) := by
  constructor <;> intro h <;>
    exact ⟨h.payload_n_eq, h.ledger_valid, h.ledger_ready, h.assignment_eq,
      h.base_score_eq, h.clock_parameter_valid, h.clock_registers_valid,
      h.clock_start_time_valid, h.clock_sigma_eq, h.clock_cutoff_eq,
      h.ledger_sigma_eq, h.ledger_cutoff_eq, h.ledger_freeze_eq,
      h.ledger_cursor_eq, h.decoder_bank_valid⟩

private theorem dispatch_clock_failure (input : CoordinatorRoundDispatch.CollectionInput p)
    (failure : CoordinatorPhaseClock.ClockFailure)
    (hclock : CoordinatorPhaseClock.startRound p input.etaReal input.time
      input.clock input.ledger.pending = .error failure) :
    CoordinatorRoundDispatch.dispatchCollection input = .clockFailure failure hclock := by
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i actual hactual
    have heq : actual = failure := Except.error.inj (hactual.symm.trans hclock)
    subst actual
    rfl
  · rename_i started hstarted
    rw [hclock] at hstarted
    cases hstarted

private theorem dispatch_invalid_core (input : CoordinatorRoundDispatch.CollectionInput p)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hclock : CoordinatorPhaseClock.startRound p input.etaReal input.time
      input.clock input.ledger.pending = .ok started)
    (hcore : ¬ CoordinatorRoundDispatch.CollectionCoreValid input) :
    CoordinatorRoundDispatch.dispatchCollection input =
      .localFailure started hclock hcore .stateDomainFailure := by
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hfailure
    rw [hclock] at hfailure
    cases hfailure
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hclock)
    subst actual
    rw [dite_eq_right hcore]

/-- The actual clock-error branch has no sampler. Its complete physical
evidence still includes fallback actions and all follower continuations. -/
theorem computed_evidence_collection_clock_failure (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)
    (failure : CoordinatorPhaseClock.ClockFailure)
    (hclock : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal ⟨ledger.cutoff - 1, by omega⟩)
      ledger.pending = .error failure)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  have hs (z : CheckedAssignmentSample.AssignmentVector p) :
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x z)).selection = none := by
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let input := ReferenceActivePhysicalStep.collectionInput
      (ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff
    have hcall : CoordinatorPhaseClock.startRound p input.etaReal input.time
        input.clock input.ledger.pending = .error failure := hclock
    have hd := dispatch_clock_failure input failure hcall
    unfold ReferenceActivePhysicalStep.dispatch
    simp only [assignment_state, hphase, dite_eq_left hcutoff]
    change (ReferenceActivePhysicalStep.DispatchCut.collection
      (x := ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger
      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection input)).selection = none
    rw [hd]
    rfl
  exact computedEvidence_of_rejected_collection x payload ledger proposal hphase v w (hs v) (hs w)

/-- An invalid actual collection core rejects before sampling, independently
of every replaced assignment coordinate. No valid-ledger premise is added. -/
theorem computed_evidence_collection_invalid_core (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)
    (hcore : ¬ CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger proposal ⟨ledger.cutoff - 1, by omega⟩)
        ⟨ledger.cutoff - 1, by omega⟩))
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
  have hs (z : CheckedAssignmentSample.AssignmentVector p) :
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x z)).selection = none := by
    have hz : ¬ CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceActivePhysicalStep.collectionInput (ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger clock cutoff) :=
      fun h => hcore ((collection_core_row x z payload ledger clock cutoff).mp h)
    let input := ReferenceActivePhysicalStep.collectionInput
      (ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger clock cutoff
    cases hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending with
    | error failure =>
      have hcall : CoordinatorPhaseClock.startRound p input.etaReal input.time
          input.clock input.ledger.pending = .error failure := hstart
      have hd := dispatch_clock_failure input failure hcall
      unfold ReferenceActivePhysicalStep.dispatch
      simp only [assignment_state, hphase, dite_eq_left hcutoff]
      change (ReferenceActivePhysicalStep.DispatchCut.collection
        (x := ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection input)).selection = none
      rw [hd]
      rfl
    | ok started =>
      have hcall : CoordinatorPhaseClock.startRound p input.etaReal input.time
          input.clock input.ledger.pending = .ok started := hstart
      have hd := dispatch_invalid_core input started hcall hz
      unfold ReferenceActivePhysicalStep.dispatch
      simp only [assignment_state, hphase, dite_eq_left hcutoff]
      change (ReferenceActivePhysicalStep.DispatchCut.collection
        (x := ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection input)).selection = none
      rw [hd]
      rfl
  exact computedEvidence_of_rejected_collection x payload ledger proposal hphase v w (hs v) (hs w)

private theorem dispatch_missing_instruction (input : CoordinatorRoundDispatch.CollectionInput p)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hclock : CoordinatorPhaseClock.startRound p input.etaReal input.time
      input.clock input.ledger.pending = .ok started)
    (hpending : input.ledger.pending = ∅)
    (hinstruction : started.assignmentStart = none) :
    CoordinatorRoundDispatch.dispatchCollection input =
      if core : CoordinatorRoundDispatch.CollectionCoreValid input then
        .coreFailure core started hclock .assignmentInstructionMissing
      else .localFailure started hclock core .stateDomainFailure := by
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hfailure
    rw [hclock] at hfailure
    cases hfailure
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hclock)
    subst actual
    have hn : ¬ input.ledger.pending.Nonempty := by
      rw [hpending]
      exact Finset.not_nonempty_empty
    by_cases hc : CoordinatorRoundDispatch.CollectionCoreValid input
    · rw [dite_eq_left hc, dite_eq_left hc, dite_eq_right hn]
      split
      · rfl
      · rename_i instruction hsome
        rw [hinstruction] at hsome
        cases hsome
    · rw [dite_eq_right hc, dite_eq_right hc]

/-- Empty pending with no actual instruction does not sample. The core may
be valid or invalid, and the full physical follower tail is retained. -/
theorem computed_evidence_collection_missing_instruction (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hphase : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hclock : CoordinatorPhaseClock.startRound p rate.eta.val x.time
      (ReferenceActivePhysicalStep.collectionClock payload ledger proposal ⟨ledger.cutoff - 1, by omega⟩)
      ledger.pending = .ok started)
    (hpending : ledger.pending = ∅)
    (hinstruction : started.assignmentStart = none)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x v) = ReferenceActivePhysicalHorizon.computedEvidence (ReferenceLaterAssignmentFibreStep.withAssignment x w) := by
  have hs (z : CheckedAssignmentSample.AssignmentVector p) :
      (ReferenceActivePhysicalStep.dispatch (ReferenceLaterAssignmentFibreStep.withAssignment x z)).selection = none := by
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
    let input := ReferenceActivePhysicalStep.collectionInput (ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger clock cutoff
    have hcall : CoordinatorPhaseClock.startRound p input.etaReal input.time
        input.clock input.ledger.pending = .ok started := hclock
    have hd := dispatch_missing_instruction input started hcall hpending hinstruction
    unfold ReferenceActivePhysicalStep.dispatch
    simp only [assignment_state, hphase, dite_eq_left hcutoff]
    change (ReferenceActivePhysicalStep.DispatchCut.collection (x := ReferenceLaterAssignmentFibreStep.withAssignment x z) payload ledger clock cutoff
      (CoordinatorRoundDispatch.dispatchCollection input)).selection = none
    rw [hd]
    split_ifs <;> rfl
  exact computedEvidence_of_rejected_collection x payload ledger proposal hphase v w (hs v) (hs w)

end Bandits.Support.ReferenceAssignmentEffectCongruence

end
