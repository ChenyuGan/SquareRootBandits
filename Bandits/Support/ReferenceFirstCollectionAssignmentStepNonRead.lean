/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPrecallOverflowBound

/-!
# Original-round assignment non-read comparisons

Internal deterministic comparisons on the existing physical round and its
whole continuous assignment vector. Sources: `06_interruptions.tex:38-100,376-408`,
`04_slow_fast_learner.tex:157-188`, and `appendix_b_communication.tex:25-58`
under `sources/zip4/manuscript/`. No source law or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceLaterAssignmentFibreStep
open Bandits.Support.ReferenceActiveDispatchTemporal

namespace Bandits.Support.ReferenceFirstCollectionAssignmentStepNonRead

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

/-- Restoring the original entire assignment vector restores the input. -/
theorem withAssignment_original (x : RoundInput p rate) :
    withAssignment x (ContinuousControlSlice.assignmentVector (x.row.2 x.time).1) = x := by
  have hc : controlWithAssignment x
      (ContinuousControlSlice.assignmentVector (x.row.2 x.time).1) = x.row.2 x.time := by
    exact (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply _
  have hr : rowWithAssignment x
      (ContinuousControlSlice.assignmentVector (x.row.2 x.time).1) = x.row := by
    unfold rowWithAssignment
    rw [hc, Function.update_eq_self]
  unfold withAssignment
  rw [hr]
  have hu : Function.update x.rows x.selected x.row = x.rows := Function.update_eq_self _ _
  rw [hu]

/-- The observation consumer is exactly the literal dispatch continuation.
This compares its physical arguments, rather than dependent dispatch outcomes. -/
theorem observeCoordinator_eq_tailArgs {x : RoundInput p rate} (prepared : PreparedRound x) :
    prepared.observeCoordinator =
      match tailArgs prepared.coordinator with
      | .inl _ => ⟨.dagger, x.state.upDecoderBank, none, none, none⟩
      | .inr (.inl _) => coordinatorFailure x.state.upDecoderBank .dispatchRejected none none
      | .inr (.inr (.inl args)) =>
          livePostChoice prepared args.1 args.2.1 args.2.2.1 args.2.2.2
      | .inr (.inr (.inr args)) =>
          collectionPostChoice prepared args.1 args.2.1 args.2.2.1 args.2.2.2 := by
  classical
  cases hc : prepared.coordinator with
  | first out =>
      cases out <;>
        simp only [PreparedRound.observeCoordinator, hc, tailArgs] <;>
        split_ifs <;> rfl
  | live r q base out =>
      cases out <;>
        simp only [PreparedRound.observeCoordinator, hc, tailArgs] <;>
        split_ifs <;> rfl
  | collection payload ledger clock cutoff out =>
      cases out <;>
        simp only [PreparedRound.observeCoordinator, hc, tailArgs] <;>
        split_ifs <;> rfl
  | invalidCollectionCutoff =>
      simp [PreparedRound.observeCoordinator, hc, tailArgs, DispatchCut.selection]
  | dagger =>
      simp [PreparedRound.observeCoordinator, hc, tailArgs, DispatchCut.selection]

/-- Equal actual dispatcher data suffice to assemble every physical effect
under the existing one-coordinate replacement. -/
theorem computedEvidence_eq_of_assignment_dispatchData
    (x : RoundInput p rate) (v w : CheckedAssignmentSample.AssignmentVector p)
    (hd : dispatchData (withAssignment x v) = dispatchData (withAssignment x w)) :
    computedEvidence (withAssignment x v) = computedEvidence (withAssignment x w) := by
  have ha := congrArg Prod.fst hd
  have hv := congrArg (fun d => d.2.1) hd
  have ht := congrArg (fun d => d.2.2) hd
  apply ReferenceAssignmentEffectCongruence.computed_evidence_fibre x v w ha hv
  rw [observeCoordinator_eq_tailArgs, observeCoordinator_eq_tailArgs]
  have ht' : tailArgs (prepare (withAssignment x v)).coordinator =
      tailArgs (prepare (withAssignment x w)).coordinator := ht
  rw [← ht']
  cases tailArgs (prepare (withAssignment x v)).coordinator with
  | inl u => rfl
  | inr rest =>
      cases rest with
      | inl u => rfl
      | inr args =>
          cases args with
          | inl a =>
              exact ReferenceAssignmentEffectCongruence.live_post_choice_fibre
                x v w ha a.1 a.2.1 a.2.2.1 a.2.2.2
          | inr a =>
              exact ReferenceAssignmentEffectCongruence.collection_post_choice_fibre
                x v w ha a.1 a.2.1 a.2.2.1 a.2.2.2

private theorem liveOutcomeData_eq_of_choice
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (row otherRow : CompletePublicTable.CompleteRow p)
    (hchoice : ∀ (pending : Finset (Fin (p.m - 1)))
      (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)),
      CoordinatorLocalArmChoice.coordinatorArmChoice r.payload pending cutoff r.time
        r.complementWeights row =
      CoordinatorLocalArmChoice.coordinatorArmChoice r.payload pending cutoff r.time
        r.complementWeights otherRow) :
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
      have heq := hchoice dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
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
      have heq := hchoice dispatched.startResult.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
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

/-- LIVE dispatch, including the actual cutoff head, does not read assignment
coordinates. Initialization, clock and domain failures remain literal. -/
theorem dispatchData_live_assignment
    (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hphase : x.state.coordinator = .live r q base)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    dispatchData (withAssignment x v) = dispatchData (withAssignment x w) := by
  unfold dispatchData
  have hd (u : CheckedAssignmentSample.AssignmentVector p) :
      dispatch (withAssignment x u) = .live r q base
        (CoordinatorRoundDispatch.dispatchLive (liveInput (withAssignment x u) r q base)) := by
    simp only [dispatch, withAssignment, hphase, CoordinatorRoundDispatch.dispatch]
    rfl
  rw [hd v, hd w, cutData_live, cutData_live]
  apply liveOutcomeData_eq_of_choice
  intro pending cutoff
  change CoordinatorLocalArmChoice.coordinatorArmChoice r.payload pending cutoff x.time
    (liveRegistersAt r x.time).complementWeights (withAssignment x v).row =
    CoordinatorLocalArmChoice.coordinatorArmChoice r.payload pending cutoff x.time
      (liveRegistersAt r x.time).complementWeights (withAssignment x w).row
  rw [withAssignment_row, withAssignment_row]
  exact (coordinatorArmChoice_row x v x.time _ pending cutoff _).trans
    (coordinatorArmChoice_row x w x.time _ pending cutoff _).symm

/-- Every computed physical effect agrees in LIVE, with no validity premise. -/
theorem computedEvidence_live_assignment
    (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hphase : x.state.coordinator = .live r q base)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    computedEvidence (withAssignment x v) = computedEvidence (withAssignment x w) :=
  computedEvidence_eq_of_assignment_dispatchData x v w
    (dispatchData_live_assignment x r q base hphase v w)

/-- The actual selected view, start result and arm are determined by the
physical dispatch projections, including option absence. -/
theorem selection_eq_of_cutData {x y : RoundInput p rate}
    (left : DispatchCut x) (right : DispatchCut y)
    (hd : cutData left = cutData right) :
    left.selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection =
      right.selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
  have formula {z : RoundInput p rate} (cut : DispatchCut z) :
      cut.selection.map ReferenceLiveDispatchOutputMeasurability.encodeSelection =
        cut.downView.bind (fun view =>
          match tailArgs cut with
          | .inr (.inr (.inl args)) => some (view, args.2.2.2, cut.arm)
          | .inr (.inr (.inr args)) => some (view, args.2.2.1, cut.arm)
          | _ => none) := by
    classical
    cases cut with
    | first out =>
        cases out <;>
          simp [DispatchCut.selection, DispatchCut.downView, DispatchCut.arm,
            selectionAt, tailArgs, ReferenceLiveDispatchOutputMeasurability.encodeSelection]
        all_goals split_ifs <;> simp_all
    | live r q base out =>
        cases out <;>
          simp [DispatchCut.selection, DispatchCut.downView, DispatchCut.arm,
            selectionAt, tailArgs, ReferenceLiveDispatchOutputMeasurability.encodeSelection]
    | collection payload ledger clock cutoff out =>
        cases out <;>
          simp [DispatchCut.selection, DispatchCut.downView, DispatchCut.arm,
            selectionAt, tailArgs, ReferenceLiveDispatchOutputMeasurability.encodeSelection]
        all_goals split_ifs <;> simp_all
    | invalidCollectionCutoff => rfl
    | dagger => rfl
  rw [formula left, formula right]
  have ha := congrArg Prod.fst hd
  have hv := congrArg (fun d => d.2.1) hd
  have ht := congrArg (fun d => d.2.2) hd
  change left.arm = right.arm at ha
  change left.downView = right.downView at hv
  change tailArgs left = tailArgs right at ht
  rw [ha, hv, ht]

/-- Evidence on a retained record is its actual computed evidence. -/
theorem evidence_eq_computed (r : RoundRecord (p := p) (rate := rate)) :
    r.evidence = computedEvidence r.input := by
  cases r with
  | mk input output h => cases h; rfl

/-- Local full-current comparison. Strictly past reads are only proposals;
the entire original reward tables are retained as the comparison input. -/
theorem evidence_eq_of_current
    (left right : RoundRecord (p := p) (rate := rate))
    (hstate : left.input.state = right.input.state)
    (hselected : left.input.selected = right.input.selected)
    (htime : left.input.time = right.input.time)
    (hrewards : left.input.rewards = right.input.rewards)
    (hcurrent : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hpast : ∀ t : Fin p.T, t.val < left.input.time.val →
      (left.input.row.2 t).1 ContinuousControlSlice.Label.prop =
        (right.input.row.2 t).1 ContinuousControlSlice.Label.prop) :
    left.evidence = right.evidence := by
  have aux (x y : RoundInput p rate)
      (hs : x.state = y.state) (hi : x.selected = y.selected)
      (ht : x.time = y.time) (hw : x.rewards = y.rewards)
      (hc : x.row.2 x.time = y.row.2 y.time)
      (hp : ∀ t : Fin p.T, t.val < x.time.val →
        (x.row.2 t).1 ContinuousControlSlice.Label.prop =
          (y.row.2 t).1 ContinuousControlSlice.Label.prop) :
      computedEvidence x = computedEvidence y := by
    cases x with
    | mk xs xr xi xt xa xw =>
      cases y with
      | mk ys yr yi yt ya yw =>
        dsimp only at hs hi ht hw hc hp
        cases hs
        cases hi
        cases ht
        cases hw
        exact ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
          xs xr yr xi xt xa xw xw hc hp rfl
  rw [evidence_eq_computed, evidence_eq_computed]
  exact aux left.input right.input hstate hselected htime hrewards hcurrent hpast

private def liveCutoffTag
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) : Bool :=
  match out with
  | .cutoffChosen _ _ _ _ _ _ _ _ _ _ => true
  | _ => false

private theorem liveCutoffTag_eq_projection
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (row : CompletePublicTable.CompleteRow p)
    (out : CoordinatorRoundDispatch.LiveOutcome
      { eta := rate.eta, registers := r, ownedRegisters := owned,
        followerBaseScore := base, row := row }) :
    liveCutoffTag r owned base row out =
      (match (ReferenceActiveDispatchTemporal.liveOutcomeData r owned base row out).2.2 with
      | .inr (.inr (.inr _)) => true
      | _ => false) := by
  cases out <;> rfl

private theorem cutoffChosen_live
    (input : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hphase : input.state.coordinator = .live r owned base) :
    ReferenceCollectionPhaseHistory.cutoffChosen input =
      liveCutoffTag (ReferenceActivePhysicalStep.liveRegistersAt r input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r owned input.time) base input.row
        (CoordinatorRoundDispatch.dispatchLive
          (ReferenceActivePhysicalStep.liveInput input r owned base)) := by
  dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen,
    ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch]
  simp only [hphase, CoordinatorRoundDispatch.dispatch]
  cases CoordinatorRoundDispatch.dispatchLive
    (ReferenceActivePhysicalStep.liveInput input r owned base) <;> rfl

/-- The LIVE cutoff boolean itself is unchanged by a complete assignment
replacement, including at the head of the collection interval. -/
theorem cutoffChosen_live_assignment
    (x : RoundInput p rate) (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (hphase : x.state.coordinator = .live r q base)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    ReferenceCollectionPhaseHistory.cutoffChosen (withAssignment x v) =
      ReferenceCollectionPhaseHistory.cutoffChosen (withAssignment x w) := by
  have hv : (withAssignment x v).state.coordinator = .live r q base := hphase
  have hw : (withAssignment x w).state.coordinator = .live r q base := hphase
  rw [cutoffChosen_live _ r q base hv, cutoffChosen_live _ r q base hw]
  dsimp only [liveInput]
  rw [liveCutoffTag_eq_projection, liveCutoffTag_eq_projection]
  have hd := liveOutcomeData_eq_of_choice (liveRegistersAt r x.time)
    (liveOwnedAt r q x.time) base (withAssignment x v).row (withAssignment x w).row
    (fun pending cutoff => by
      rw [withAssignment_row, withAssignment_row]
      exact (coordinatorArmChoice_row x v x.time _ pending cutoff _).trans
        (coordinatorArmChoice_row x w x.time _ pending cutoff _).symm)
  exact congrArg (fun data =>
    match data.2.2 with | .inr (.inr (.inr _)) => true | _ => false) hd

private theorem livePostChoice_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared registers owned base started).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
      | error reason => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
      | ok serviced =>
          cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
              started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              x.time x.row prepared.coordinatorObservation with
          | none => simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure]
          | some pending =>
              cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                  started.clock pending x.row with
              | error reason => simp [hservice, hfinish,
                  ReferenceActivePhysicalStep.coordinatorFailure]
              | ok finished => simp [hservice, hfinish]

private theorem collectionFinish_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases hresult : cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | success pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock, ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]
  | rejected pair =>
      rcases pair with ⟨ledger, bank⟩
      cases hledger : CoordinatorCollectionLedger.finishRound ledger with
      | invalid => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure]
      | success finishedLedger =>
          cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
              started.clock finishedLedger.pending x.row with
          | error reason => simp [hledger, hclock, ReferenceActivePhysicalStep.coordinatorFailure]
          | ok finishedClock => simp [hledger, hclock]

private theorem collectionPostChoice_configuration_ne_first
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    (ReferenceActivePhysicalStep.collectionPostChoice prepared payload ledger started weights).configuration ≠
      .first := by
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases hrecord : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure]
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | rejected rejected => simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure]
      | success startedLedger =>
          simpa [hrecord, hstart] using
            (collectionFinish_configuration_ne_first (x := x) payload started recording
              (ReferenceActivePhysicalStep.receiveUp prepared startedLedger))

/-- Every actual step leaves the distinguished first constructor, including
all local failures. No sampler or domain premise is required. -/
theorem step_coordinator_ne_first (x : RoundInput p rate) :
    (step x).next.coordinator ≠ .first := by
  rw [(step_next_fields x).1, observeCoordinator_eq_tailArgs]
  cases tailArgs (prepare x).coordinator with
  | inl u => simp
  | inr rest =>
      cases rest with
      | inl u => simp [coordinatorFailure]
      | inr args =>
          cases args with
          | inl a =>
              exact livePostChoice_configuration_ne_first (prepare x)
                a.1 a.2.1 a.2.2.1 a.2.2.2
          | inr a =>
              exact collectionPostChoice_configuration_ne_first (prepare x)
                a.1 a.2.1 a.2.2.1 a.2.2.2

/-- Actual pre-call minimality supplies the absent parameter selector, with
no invocation-success or physical-domain assumption. -/
theorem source_parameters_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hbefore : (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.time.val <
      ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
        rate rewards C_star C_h z) :
    ReferenceLaterSamplerParameterMeasurability.parameters?
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input = none := by
  exact ReferenceFirstCollectionPrecallCalendarSupport.parameters_none_before_cut
    rate rewards C_star C_h z k.val _ (List.getElem?_eq_getElem k.isLt) hbefore

/-- The canonical call cell retains selection and recorder absence as well
as successful numerical diagnostics. -/
theorem traceCell_eq_of_dispatchData
    (left right : RoundRecord (p := p) (rate := rate))
    (hd : dispatchData left.input = dispatchData right.input)
    (he : left.evidence = right.evidence) :
    ReferenceCoordinatorRecorderCallTrace.cell
        (ReferenceActiveHorizonMeasurability.roundRecordCode left) =
      ReferenceCoordinatorRecorderCallTrace.cell
        (ReferenceActiveHorizonMeasurability.roundRecordCode right) := by
  have hs : ReferenceCoordinatorRecorderCallTrace.selection
      (ReferenceActiveHorizonMeasurability.roundRecordCode left) =
      ReferenceCoordinatorRecorderCallTrace.selection
        (ReferenceActiveHorizonMeasurability.roundRecordCode right) := by
    rw [ReferenceCoordinatorRecorderCallTrace.selection,
      ReferenceCoordinatorRecorderCallTrace.selection,
      (ReferenceActiveHorizonMeasurability.roundRecordCode_front left).1,
      (ReferenceActiveHorizonMeasurability.roundRecordCode_front right).1]
    exact selection_eq_of_cutData _ _ hd
  have hr : ReferenceCoordinatorRecorderCallTrace.recording
      (ReferenceActiveHorizonMeasurability.roundRecordCode left) =
      ReferenceCoordinatorRecorderCallTrace.recording
        (ReferenceActiveHorizonMeasurability.roundRecordCode right) := by
    rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics,
      ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
    exact congrArg (fun e => e.coordinator.recording) he
  have ht : (ReferenceActiveHorizonMeasurability.roundRecordCode left).1 =
      (ReferenceActiveHorizonMeasurability.roundRecordCode right).1 :=
    congrArg (fun e => e.time.val) he
  unfold ReferenceCoordinatorRecorderCallTrace.cell ReferenceCoordinatorRecorderCallTrace.live
    ReferenceCoordinatorRecorderCallTrace.enabled
  rw [hs, hr, ht]

private theorem roundInput_ext {K : ℕ} (left right : RecordedQueueRun.RoundInput K)
    (he : left.enabled = right.enabled) (ha : left.recordedArm = right.recordedArm)
    (hw : left.reward = right.reward) (hr : left.rate = right.rate) : left = right := by
  cases left
  cases right
  simp_all

private theorem sourceCell_eq_of_nonAssignment
    (left right : RoundRecord (p := p) (rate := rate))
    (lv rv : ReferenceDownReception.ChoiceTimeView p rate.eta) (hv : lv = rv)
    (ls rs : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) (hs : ls = rs)
    (hl : CoordinatorLocalArmChoice.ChoiceInputsValid lv.payload lv.cutoff
      left.input.time lv.complementWeights)
    (hr : CoordinatorLocalArmChoice.ChoiceInputsValid rv.payload rv.cutoff
      right.input.time rv.complementWeights)
    (hw : left.input.rewards left.input.time = right.input.rewards right.input.time)
    (hc : ∀ l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (left.input.row.2 left.input.time).1 l.val =
        (right.input.row.2 right.input.time).1 l.val) :
    ReferenceFirstWindowNumericalStream.sourceCell left lv.payload lv.pendingAtChoice ls
        lv.complementWeights lv.cutoff hl =
      ReferenceFirstWindowNumericalStream.sourceCell right rv.payload rv.pendingAtChoice rs
        rv.complementWeights rv.cutoff hr := by
  cases hv
  cases hs
  apply roundInput_ext
  · rfl
  · unfold ReferenceFirstWindowNumericalStream.sourceCell ReferenceFirstWindowNumericalStream.sourceArm
    exact ReferenceFirstCollectionCurrentRemainderLaw.recordingMap_eq_of_nonAssignment
      rate _ _ _ _ _ _ _ _ _ hc
  · exact congrArg (fun w => fun a => ((w a).val : ℝ) / (D p : ℝ)) hw
  · rfl

/-- Literal LIVE numerical options agree from the actual selected view,
prepared configurations and non-assignment scalars. No domain is supplied. -/
theorem laterLiveReadout_eq
    (s : ℕ) (left right : RoundRecord (p := p) (rate := rate))
    (ht : left.input.time = right.input.time)
    (hw : left.input.rewards left.input.time = right.input.rewards right.input.time)
    (hsel : left.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection =
      right.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection)
    (hconfig : ∀ i, (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration)
    (hc : ∀ l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (left.input.row.2 left.input.time).1 l.val =
        (right.input.row.2 right.input.time).1 l.val) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout s left =
      ReferenceLaterLiveNumericalReadout.laterLiveReadout s right := by
  classical
  have ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary left ↔
      ReferenceLaterLiveNumericalReadout.preparedOrdinary right := by
    unfold ReferenceLaterLiveNumericalReadout.preparedOrdinary
    simp only [hconfig]
  unfold ReferenceLaterLiveNumericalReadout.laterLiveReadout
  cases hl : left.output.preparation.coordinator.selection with
  | none =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => rfl
      | some selected => simp [hl, hr] at hsel
  | some lselected =>
      cases hr : right.output.preparation.coordinator.selection with
      | none => simp [hl, hr] at hsel
      | some rselected =>
          dsimp only
          have hs : some (ReferenceLiveDispatchOutputMeasurability.encodeSelection lselected) =
              some (ReferenceLiveDispatchOutputMeasurability.encodeSelection rselected) := by
            simpa only [hl, hr, Option.map_some] using hsel
          have hv : lselected.view = rselected.view :=
            congrArg Prod.fst (Option.some.inj hs)
          have hg : (s < lselected.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive lselected.view.payload
                lselected.view.cutoff left.input.time) ↔
              (s < rselected.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive rselected.view.payload
                rselected.view.cutoff right.input.time) := by rw [hv, ht]
          by_cases hguard : s < lselected.view.payload.sigma.val ∧
              CoordinatorLocalArmChoice.assignmentIsLive lselected.view.payload
                lselected.view.cutoff left.input.time
          · rw [ite_eq_left hguard, ite_eq_left (hg.mp hguard)]
            by_cases hol : ReferenceLaterLiveNumericalReadout.preparedOrdinary left
            · rw [dite_eq_left hol, dite_eq_left (ho.mp hol)]
              apply congrArg some
              refine sourceCell_eq_of_nonAssignment left right _ _ hv _ _ ?_ _ _ hw hc
              funext i
              simp only [ReferenceLaterLiveNumericalReadout.preparedStates, hconfig]
            · rw [dite_eq_right hol, dite_eq_right (fun h => hol (ho.mpr h))]
          · rw [ite_eq_right hguard, ite_eq_right (fun h => hguard (hg.mpr h))]

/-- The domain of the actual collection cell is a projection of the actual
continuation and cutoff tag, including failed and absent branches. -/
theorem laterCollectionReadout_domain_projection
    (s : ℕ) (record : RoundRecord (p := p) (rate := rate)) :
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record).isSome =
      match tailArgs record.output.preparation.coordinator with
      | .inr (.inr (.inr args)) =>
          decide (ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record ∧
            (ReferenceCollectionPhaseHistory.cutoffChosen record.input = true →
              s < args.1.sigma.val))
      | _ => false := by
  classical
  have htag : ReferenceCollectionPhaseHistory.cutoffChosen record.input =
      match record.output.preparation.coordinator with
      | .live _ _ _ (.cutoffChosen ..) => true
      | _ => false := by
        rw [record.output_eq]
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        dsimp only [step]
        cases (prepare record.input).coordinator with
        | first out => rfl
        | live r q base out => cases out <;> rfl
        | collection payload ledger clock cutoff out => rfl
        | invalidCollectionCutoff => rfl
        | dagger => rfl
  apply Bool.eq_iff_iff.mpr
  rw [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain, htag]
  cases hc : record.output.preparation.coordinator with
  | first out =>
      cases out <;> simp [tailArgs, DispatchCut.selection, selectionAt]
      all_goals split_ifs <;> simp_all
  | live r q base out =>
      cases out <;> simp [tailArgs, DispatchCut.selection, selectionAt]
  | collection payload ledger clock cutoff out =>
      cases out <;> simp [tailArgs, DispatchCut.selection, selectionAt]
      all_goals split_ifs <;> simp_all
  | invalidCollectionCutoff => simp [tailArgs, DispatchCut.selection]
  | dagger => simp [tailArgs, DispatchCut.selection]

/-- The collection numerical option is fixed by its actual domain and the
canonical call cell, including every reward and rate field. -/
theorem laterCollectionReadout_eq
    (s : ℕ) (left right : RoundRecord (p := p) (rate := rate))
    (hw : left.input.rewards left.input.time = right.input.rewards right.input.time)
    (hcall : ReferenceCoordinatorRecorderCallTrace.cell
        (ReferenceActiveHorizonMeasurability.roundRecordCode left) =
      ReferenceCoordinatorRecorderCallTrace.cell
        (ReferenceActiveHorizonMeasurability.roundRecordCode right))
    (htail : tailArgs left.output.preparation.coordinator =
      tailArgs right.output.preparation.coordinator)
    (htag : ReferenceCollectionPhaseHistory.cutoffChosen left.input =
      ReferenceCollectionPhaseHistory.cutoffChosen right.input)
    (hconfig : ∀ i, (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s left =
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s right := by
  have hfollowers : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied left ↔
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied right := by
    unfold ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
    simp only [hconfig]
  have hdomain :
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s left).isSome =
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s right).isSome := by
    rw [laterCollectionReadout_domain_projection, laterCollectionReadout_domain_projection,
      htail, htag]
    simp only [hfollowers]
  have hnum := ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization
    s left
  have hnumR := ReferenceLaterCollectionSourceReadoutMeasurability.readout_numerical_factorization
    s right
  have hcoords :
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s left).map
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates =
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s right).map
        ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates := by
    rw [hnum, hnumR, hdomain]
    unfold ReferenceLaterCollectionSourceReadoutMeasurability.numericalFromRecordCode
    rw [hcall, hw]
  cases hl : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s left with
  | none =>
      cases hr : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s right with
      | none => rfl
      | some c => simp [hl, hr] at hdomain
  | some l =>
      cases hr : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s right with
      | none => simp [hl, hr] at hdomain
      | some r =>
          simp only [hl, hr, Option.map_some] at hcoords
          have hc := Option.some.inj hcoords
          apply congrArg some
          exact roundInput_ext l r (congrArg Prod.fst hc)
            (congrArg (fun d => d.2.1) hc)
            (congrArg (fun d => d.2.2.1) hc) (congrArg (fun d => d.2.2.2) hc)

private theorem firstOutcome_is_chosen (input : CoordinatorRoundDispatch.FirstInput p) :
    ∃ selected,
      CoordinatorRoundDispatch.dispatchFirst input =
        .chosen (CoordinatorAssignmentRegisterInstall.installFirst
          (CoordinatorRoundDispatch.firstLaunchInput input)) selected := by
  classical
  unfold CoordinatorRoundDispatch.dispatchFirst
  extract_lets launch installed started payload weights cutoff hpayload hstarted hcutoff
    hweights hchoice hboundary hnonempty
  split
  · exact False.elim (hnonempty ‹CoordinatorLocalArmChoice.coordinatorArmChoice
      payload started.pending cutoff installed.registers.time weights input.row = none›)
  · rename_i arm hselected
    exact ⟨{
      arm := arm
      choiceInputsValid := hchoice
      recorderBoundaryValid := hboundary
      armChoice_eq := hselected }, rfl⟩

private def firstTailArgs
    (launch : FirstAssignmentLaunch.Input p rate.eta) :
    Bandits.Support.ReferenceActiveDispatchTemporal.LiveArgs p rate :=
  ⟨(CoordinatorAssignmentRegisterInstall.installFirst launch).registers,
    (CoordinatorAssignmentRegisterInstall.installFirst launch).ownedRegisters,
    ((CoordinatorAssignmentRegisterInstall.installFirst launch).followerBaseScore,
      (CoordinatorAssignmentRegisterInstall.installFirst launch).startRoundResult)⟩

private theorem first_dispatch_tailArgs
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hfirst : x.state.coordinator = .first) :
    Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
        (ReferenceActivePhysicalStep.dispatch x) =
      .inr (.inr (.inl (firstTailArgs
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x)))) ) := by
  rw [ReferenceActivePhysicalStep.dispatch_first x hfirst]
  obtain ⟨selection, hchosen⟩ := firstOutcome_is_chosen
    (ReferenceActivePhysicalStep.firstInput x)
  rw [hchosen]
  have htime :
      (CoordinatorAssignmentRegisterInstall.installFirst
        (CoordinatorRoundDispatch.firstLaunchInput
          (ReferenceActivePhysicalStep.firstInput x))).registers.time = x.time := rfl
  simp only [Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs,
    ReferenceActivePhysicalStep.DispatchCut.selection,
    ReferenceActivePhysicalStep.selectionAt, htime, dite_true,
    Option.some_ne_none]
  rfl

private theorem shared_dispatchData_eq_of_current
    (state : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (time : Fin p.T)
    (active : ∀ i, (state.activations i).val ≤ time.val + 1)
    (rewards otherRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcurrent : (rows selected).2 time = (otherRows selected).2 time) :
    let x : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, rows, selected, time, active, rewards⟩
    let y : ReferenceActivePhysicalStep.RoundInput p rate :=
      ⟨state, otherRows, selected, time, active, otherRewards⟩
    Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData x =
      Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData y := by
  let x : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, rows, selected, time, active, rewards⟩
  let y : ReferenceActivePhysicalStep.RoundInput p rate :=
    ⟨state, otherRows, selected, time, active, otherRewards⟩
  cases hphase : state.coordinator with
  | first =>
      have hlaunch := ReferenceActiveTemporalAssembly.firstLaunchInput_eq_of_current state rows otherRows selected
        time active rewards otherRewards hcurrent
      have hpair := Bandits.Support.ReferenceActiveTemporalCausality.first_dispatch_projections_eq_of_current state rows otherRows
        selected active rewards otherRewards hphase hcurrent
      have htail : Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
            (ReferenceActivePhysicalStep.dispatch x) =
          Bandits.Support.ReferenceActiveDispatchTemporal.tailArgs
            (ReferenceActivePhysicalStep.dispatch y) := by
        rw [first_dispatch_tailArgs x hphase, first_dispatch_tailArgs y hphase]
        exact congrArg (fun args => Sum.inr (Sum.inr (Sum.inl args)))
          (congrArg firstTailArgs hlaunch)
      unfold Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData
        Bandits.Support.ReferenceActiveDispatchTemporal.cutData
      exact congrArg₂ (fun head tail => (head.1, head.2, tail)) hpair htail
  | live registers owned base =>
      exact Bandits.Support.ReferenceActiveDispatchTemporal.live_dispatch_data_eq_of_current state rows otherRows selected time active
        rewards otherRewards registers owned base hphase hcurrent
  | collection payload ledger proposal =>
      exact Bandits.Support.ReferenceActiveDispatchTemporal.collection_dispatch_data_eq_of_current state rows otherRows selected time
        active rewards otherRewards payload ledger proposal hphase hcurrent
  | dagger =>
      change Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData x =
        Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData y
      unfold Bandits.Support.ReferenceActiveDispatchTemporal.dispatchData
        Bandits.Support.ReferenceActiveDispatchTemporal.cutData
      rw [ReferenceActivePhysicalStep.dispatch_dagger x hphase,
        ReferenceActivePhysicalStep.dispatch_dagger y hphase]
      rfl

/-- Full current-control equality compares the actual pre-choice physical
projections even when earlier unread assignment coordinates differ. -/
theorem dispatchData_eq_of_current
    (x y : RoundInput p rate) (hs : x.state = y.state)
    (hi : x.selected = y.selected) (ht : x.time = y.time)
    (hc : x.row.2 x.time = y.row.2 y.time) : dispatchData x = dispatchData y := by
  cases x with
  | mk xs xr xi xt xa xw =>
    cases y with
    | mk ys yr yi yt ya yw =>
      dsimp only at hs hi ht hc
      cases hs
      cases hi
      cases ht
      exact shared_dispatchData_eq_of_current xs xr yr xi xt xa xw yw hc

/-- A shared incoming coordinator and actual continuation fix the cutoff tag. -/
theorem cutoffChosen_eq_of_dispatchData (x y : RoundInput p rate)
    (hs : x.state = y.state) (hd : dispatchData x = dispatchData y) :
    ReferenceCollectionPhaseHistory.cutoffChosen x =
      ReferenceCollectionPhaseHistory.cutoffChosen y := by
  have hycoord := congrArg State.coordinator hs
  cases hp : x.state.coordinator with
  | live r q base =>
      have hy : y.state.coordinator = .live r q base := hycoord.symm.trans hp
      have hdx : dispatch x = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput x r q base)) := by
        simp only [dispatch, hp, CoordinatorRoundDispatch.dispatch]; rfl
      have hdy : dispatch y = .live r q base
          (CoordinatorRoundDispatch.dispatchLive (liveInput y r q base)) := by
        simp only [dispatch, hy, CoordinatorRoundDispatch.dispatch]; rfl
      unfold dispatchData at hd
      rw [hdx, hdy, cutData_live, cutData_live] at hd
      rw [cutoffChosen_live x r q base hp, cutoffChosen_live y r q base hy]
      dsimp only [liveInput]
      rw [liveCutoffTag_eq_projection, liveCutoffTag_eq_projection]
      exact congrArg (fun d =>
        match d.2.2 with | .inr (.inr (.inr _)) => true | _ => false) hd
  | first =>
      have hy : y.state.coordinator = .first := hycoord.symm.trans hp
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      change (match dispatch x with | .live _ _ _ (.cutoffChosen ..) => true | _ => false) =
        (match dispatch y with | .live _ _ _ (.cutoffChosen ..) => true | _ => false)
      rw [dispatch_first x hp, dispatch_first y hy]
  | collection payload ledger proposal =>
      have hy : y.state.coordinator = .collection payload ledger proposal := hycoord.symm.trans hp
      have zero (z : RoundInput p rate)
          (hz : z.state.coordinator = .collection payload ledger proposal) :
          ReferenceCollectionPhaseHistory.cutoffChosen z = false := by
        unfold ReferenceCollectionPhaseHistory.cutoffChosen
        change (match dispatch z with | .live _ _ _ (.cutoffChosen ..) => true | _ => false) = false
        by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          have hdz : dispatch z = .collection payload ledger
              (collectionClock payload ledger proposal cutoff) cutoff
              (CoordinatorRoundDispatch.dispatchCollection (collectionInput z payload ledger
                (collectionClock payload ledger proposal cutoff) cutoff)) := by
            simp only [dispatch, hz, dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hdz]
        · rw [(dispatch_collection_invalid_cutoff z payload ledger proposal hz hc).1]
      rw [zero x hp, zero y hy]
  | dagger =>
      have hy : y.state.coordinator = .dagger := hycoord.symm.trans hp
      unfold ReferenceCollectionPhaseHistory.cutoffChosen
      change (match dispatch x with | .live _ _ _ (.cutoffChosen ..) => true | _ => false) =
        (match dispatch y with | .live _ _ _ (.cutoffChosen ..) => true | _ => false)
      rw [dispatch_dagger x hp, dispatch_dagger y hy]

private theorem collection_tailArgs_none {x : RoundInput p rate}
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (out : CoordinatorRoundDispatch.CollectionOutcome (collectionInput x payload ledger clock cutoff))
    (hn : (DispatchCut.collection payload ledger clock cutoff out).selection = none) :
    tailArgs (DispatchCut.collection payload ledger clock cutoff out) = .inr (.inl ()) := by
  simp only [tailArgs, hn, dite_true]

/-- Actual COLLECTION dispatch data agree in the absent-parameter branch.
All reconstruction and checked-sampler failures remain in the existing cut. -/
theorem dispatchData_collection_assignment
    (x : RoundInput p rate) (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hp : x.state.coordinator = .collection payload ledger proposal)
    (hn : parameters? x = none) (v w : CheckedAssignmentSample.AssignmentVector p) :
    dispatchData (withAssignment x v) = dispatchData (withAssignment x w) := by
  have hf : (match parameters? x with
      | none => True
      | some theta => AssignmentParameterFibreKernel.successfulSlowSet p theta v =
        AssignmentParameterFibreKernel.successfulSlowSet p theta w) := by simp only [hn]
  have hpair := ReferenceLaterDispatchFibre.dispatch_collection_arm_downView_fibre
    x payload ledger proposal hp v w hf
  have hcont := ReferenceLaterDispatchFibre.dispatch_collection_continuations_fibre
    x payload ledger proposal hp v w hf
  have ht : tailArgs (dispatch (withAssignment x v)) =
      tailArgs (dispatch (withAssignment x w)) := by
    by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock payload ledger proposal cutoff
      have hd (u : CheckedAssignmentSample.AssignmentVector p) :
          dispatch (withAssignment x u) = .collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (collectionInput (withAssignment x u) payload ledger clock cutoff)) := by
        simp only [dispatch, withAssignment, hp, dite_eq_left hc, CoordinatorRoundDispatch.dispatch]
        rfl
      rw [hd v, hd w] at hcont ⊢
      cases hl : CoordinatorRoundDispatch.dispatchCollection
          (collectionInput (withAssignment x v) payload ledger clock cutoff) <;>
        cases hr : CoordinatorRoundDispatch.dispatchCollection
          (collectionInput (withAssignment x w) payload ledger clock cutoff) <;>
        rw [hl, hr] at hcont
      all_goals try
        exact (collection_tailArgs_none _ _ _ _ _ hcont.1).trans
          (collection_tailArgs_none _ _ _ _ _ hcont.2).symm
      · rename_i coreL snapshotL boundaryL scoresL coreR snapshotR boundaryR scoresR
        rcases hcont with ⟨_, _, _, _, hs, _, hw⟩
        have hw' := eq_of_heq hw
        have hlSel : (DispatchCut.collection payload ledger clock cutoff
            (.continuing coreL snapshotL boundaryL scoresL)).selection ≠ none := by
          intro h
          exact Option.some_ne_none _ h
        have hrSel : (DispatchCut.collection payload ledger clock cutoff
            (.continuing coreR snapshotR boundaryR scoresR)).selection ≠ none := by
          intro h
          exact Option.some_ne_none _ h
        unfold tailArgs
        rw [dite_eq_right hlSel, dite_eq_right hrSel]
        change (Sum.inr (Sum.inr (Sum.inr
          (⟨payload, ledger, snapshotL.clockStarted,
            CoordinatorCollectionInteractive.PreObservationInputs.weights
              (collectionInput (withAssignment x v) payload ledger clock cutoff)
              snapshotL.inputsValid.ledger_valid snapshotL.inputsValid.assignment_eq⟩ :
            CollectionArgs p rate))) : Unit ⊕ (Unit ⊕ (LiveArgs p rate ⊕ CollectionArgs p rate))) =
          Sum.inr (Sum.inr (Sum.inr
            (⟨payload, ledger, snapshotR.clockStarted,
              CoordinatorCollectionInteractive.PreObservationInputs.weights
                (collectionInput (withAssignment x w) payload ledger clock cutoff)
                snapshotR.inputsValid.ledger_valid snapshotR.inputsValid.assignment_eq⟩ :
              CollectionArgs p rate)))
        rw [hs, hw']
      · rename_i coreL consistentL startedL startEqL instructionL instructionEqL
          outputL localEqL clockDataL installationL selectionL
          coreR consistentR startedR startEqR instructionR instructionEqR
          outputR localEqR clockDataR installationR selectionR
        rcases hcont with ⟨hta, htb, _, _, hs, _, hregs, howned, hbase, _⟩
        have hpairs : (⟨installationL.registers, installationL.ownedRegisters⟩ :
            Σ r, CoordinatorLiveServiceFinish.OwnedRegisters r) =
          ⟨installationR.registers, installationR.ownedRegisters⟩ := Sigma.ext hregs howned
        have hargs : (⟨installationL.registers, installationL.ownedRegisters,
            installationL.retainedBaseScore, startedL⟩ : LiveArgs p rate) =
          ⟨installationR.registers, installationR.ownedRegisters,
            installationR.retainedBaseScore, startedR⟩ :=
          congrArg₂ (fun (pair : Σ r, CoordinatorLiveServiceFinish.OwnedRegisters r)
              (rest : (Fin (p.m - 1) → ℕ) × CoordinatorPhaseClock.StartRoundResult p) =>
            (⟨pair.1, pair.2, rest⟩ : LiveArgs p rate)) hpairs (Prod.ext hbase hs)
        have htv : (withAssignment x v).time = x.time := rfl
        have htw : (withAssignment x w).time = x.time := rfl
        simp only [tailArgs, DispatchCut.selection, selectionAt, hta, htb, htv, htw,
          dite_true, Option.some_ne_none, dite_false]
        exact congrArg (fun args => Sum.inr (Sum.inr (Sum.inl args))) hargs
    · have hv : (withAssignment x v).state.coordinator = .collection payload ledger proposal := hp
      have hw : (withAssignment x w).state.coordinator = .collection payload ledger proposal := hp
      rw [(dispatch_collection_invalid_cutoff _ payload ledger proposal hv hc).1,
        (dispatch_collection_invalid_cutoff _ payload ledger proposal hw hc).1]
      simp [tailArgs, DispatchCut.selection]
  exact Prod.ext hpair.1 (Prod.ext hpair.2 ht)

/-- Non-firstness is essential: the first dispatcher reads assignment
coordinates even when its later sampler selector is absent. -/
theorem dispatchData_assignment_of_nonfirst
    (x : RoundInput p rate) (hnf : x.state.coordinator ≠ .first)
    (hn : ReferenceLaterSamplerParameterMeasurability.parameters? x = none)
    (v w : CheckedAssignmentSample.AssignmentVector p) :
    dispatchData (withAssignment x v) = dispatchData (withAssignment x w) := by
  cases hp : x.state.coordinator with
  | first => exact False.elim (hnf hp)
  | live r q base => exact dispatchData_live_assignment x r q base hp v w
  | collection payload ledger proposal =>
      exact dispatchData_collection_assignment x payload ledger proposal hp hn v w
  | dagger =>
      unfold dispatchData cutData
      have hv : (withAssignment x v).state.coordinator = .dagger := hp
      have hw : (withAssignment x w).state.coordinator = .dagger := hp
      rw [dispatch_dagger _ hv, dispatch_dagger _ hw]
      rfl

open ReferenceActiveHorizonMeasurability (roundRecordCode)
open ReferenceCoordinatorRecorderCallTrace (cell)
open ReferenceFirstCollectionCurrentRetainedGate (cell0)
local notation "tag" => ReferenceCollectionPhaseHistory.cutoffChosen

private theorem cell0_eq_of_projections
    (left right : RoundRecord (p := p) (rate := rate))
    (ht : left.input.time = right.input.time)
    (hw : left.input.rewards left.input.time = right.input.rewards right.input.time)
    (hd : dispatchData left.input = dispatchData right.input)
    (he : left.evidence = right.evidence)
    (hg : tag left.input = tag right.input)
    (hconfig : ∀ i, (left.output.preparation.followers.followers i).configuration =
      (right.output.preparation.followers.followers i).configuration)
    (hc : ∀ l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      (left.input.row.2 left.input.time).1 l.val =
        (right.input.row.2 right.input.time).1 l.val) :
    cell0 rate left = cell0 rate right := by
  have hs : left.output.preparation.coordinator.selection.map
      ReferenceLiveDispatchOutputMeasurability.encodeSelection =
      right.output.preparation.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
    rw [left.output_eq, right.output_eq]
    exact selection_eq_of_cutData _ _ hd
  have htail : tailArgs left.output.preparation.coordinator =
      tailArgs right.output.preparation.coordinator := by
    rw [left.output_eq, right.output_eq]
    exact congrArg (fun d => d.2.2) hd
  unfold cell0
  rw [laterLiveReadout_eq 0 left right ht hw hs hconfig hc,
    laterCollectionReadout_eq 0 left right hw
      (traceCell_eq_of_dispatchData left right hd he) htail hg hconfig]

private theorem configuration_eq_of_current (x y : RoundInput p rate)
    (hs : x.state = y.state) (hi : x.selected = y.selected) (ht : x.time = y.time)
    (hc : x.row.2 x.time = y.row.2 y.time) (i : Fin (p.m - 1)) :
    ((prepare x).followers.followers i).configuration =
      ((prepare y).followers.followers i).configuration := by
  cases x with
  | mk xs xr xi xt xa xw =>
    cases y with
    | mk ys yr yi yt ya yw =>
      dsimp only at hs hi ht hc
      cases hs
      cases hi
      cases ht
      exact congrArg Prod.snd
        (ReferenceActiveTemporalCausality.prepare_projections_eq_of_current
          (row := xr xi) (otherRow := yr xi) (t := xt)
          i (xs.activations i) (xa i) (xs.followers i) hc)

/-- Full-current local comparison on actual records, jointly retaining all
physical evidence, canonical call cells, cutoff tags and numerical options. -/
theorem compare_of_current
    (left right : RoundRecord (p := p) (rate := rate))
    (hs : left.input.state = right.input.state)
    (hi : left.input.selected = right.input.selected)
    (ht : left.input.time = right.input.time)
    (hw : left.input.rewards = right.input.rewards)
    (hc : left.input.row.2 left.input.time = right.input.row.2 right.input.time)
    (hp : ∀ t : Fin p.T, t.val < left.input.time.val →
      (left.input.row.2 t).1 ContinuousControlSlice.Label.prop =
        (right.input.row.2 t).1 ContinuousControlSlice.Label.prop) :
    left.evidence = right.evidence ∧ cell (roundRecordCode left) = cell (roundRecordCode right) ∧
      tag left.input = tag right.input ∧ cell0 rate left = cell0 rate right := by
  have he := evidence_eq_of_current left right hs hi ht hw hc hp
  have hd := dispatchData_eq_of_current left.input right.input hs hi ht hc
  have hg := cutoffChosen_eq_of_dispatchData left.input right.input hs hd
  refine ⟨he, traceCell_eq_of_dispatchData left right hd he, hg, ?_⟩
  apply cell0_eq_of_projections left right ht (by rw [hw, ht]) hd he hg
  · intro i
    rw [left.output_eq, right.output_eq]
    exact configuration_eq_of_current _ _ hs hi ht hc i
  · intro l
    exact congrArg (fun c => c.1 l.val) hc

/-- A canonical single-date replacement of an actual record preserves the
four observations in every non-first absent-parameter branch. -/
theorem compare_withAssignment
    (r : RoundRecord (p := p) (rate := rate))
    (hnf : r.input.state.coordinator ≠ .first)
    (hn : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none)
    (replacement : CheckedAssignmentSample.AssignmentVector p) :
    let rv : RoundRecord (p := p) (rate := rate) :=
      ⟨withAssignment r.input replacement, step (withAssignment r.input replacement), rfl⟩
    r.evidence = rv.evidence ∧ cell (roundRecordCode r) = cell (roundRecordCode rv) ∧
      tag r.input = tag rv.input ∧ cell0 rate r = cell0 rate rv := by
  cases r with
  | mk x output hout =>
    cases hout
    let original := ContinuousControlSlice.assignmentVector (x.row.2 x.time).1
    have hd := dispatchData_assignment_of_nonfirst x hnf hn original replacement
    have he := computedEvidence_eq_of_assignment_dispatchData x original replacement hd
    rw [withAssignment_original] at hd he
    let l : RoundRecord (p := p) (rate := rate) := ⟨x, step x, rfl⟩
    let r : RoundRecord (p := p) (rate := rate) :=
      ⟨withAssignment x replacement, step (withAssignment x replacement), rfl⟩
    change l.evidence = r.evidence ∧ cell (roundRecordCode l) = cell (roundRecordCode r) ∧
      tag l.input = tag r.input ∧ cell0 rate l = cell0 rate r
    have hg := cutoffChosen_eq_of_dispatchData x (withAssignment x replacement) rfl hd
    refine ⟨he, traceCell_eq_of_dispatchData l r hd he, hg, ?_⟩
    apply cell0_eq_of_projections l r rfl rfl hd he hg
    · intro i
      exact (ReferenceAssignmentEffectCongruence.prepared_follower_configuration
        x replacement i).symm
    · intro label
      change (x.row.2 x.time).1 label.val =
        ((withAssignment x replacement).row.2 x.time).1 label.val
      rw [withAssignment_row]
      exact (rowWithAssignment_scalar x replacement x.time label).symm

/-- The original K+1 split supplies the whole-current bridge to a second
actual record. Strictly past proposal coordinates are retained. -/
theorem compare_of_remainder
    (left right : RoundRecord (p := p) (rate := rate))
    (hs : left.input.state = right.input.state)
    (hi : left.input.selected = right.input.selected)
    (ht : left.input.time = right.input.time)
    (hw : left.input.rewards = right.input.rewards)
    (hc : (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (left.input.row.2 left.input.time)).2 =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (right.input.row.2 right.input.time)).2)
    (hp : ∀ t : Fin p.T, t.val < left.input.time.val →
      (left.input.row.2 t).1 ContinuousControlSlice.Label.prop =
        (right.input.row.2 t).1 ContinuousControlSlice.Label.prop)
    (hnf : left.input.state.coordinator ≠ .first)
    (hn : ReferenceLaterSamplerParameterMeasurability.parameters? left.input = none) :
    left.evidence = right.evidence ∧ cell (roundRecordCode left) = cell (roundRecordCode right) ∧
      tag left.input = tag right.input ∧ cell0 rate left = cell0 rate right := by
  let v := (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
    (right.input.row.2 right.input.time)).1
  let mid : RoundRecord (p := p) (rate := rate) :=
    ⟨withAssignment left.input v, step (withAssignment left.input v), rfl⟩
  have hlm := compare_withAssignment left hnf hn v
  have hcurrent : mid.input.row.2 mid.input.time = right.input.row.2 right.input.time := by
    change (withAssignment left.input v).row.2 left.input.time = _
    rw [withAssignment_row]
    change Function.update left.input.row.2 left.input.time
      (controlWithAssignment left.input v) left.input.time = _
    rw [Function.update_self]
    unfold controlWithAssignment
    rw [hc]
    exact (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply _
  have hmr := compare_of_current mid right hs hi ht hw hcurrent (by
    intro t hbefore
    change ((withAssignment left.input v).row.2 t).1 ContinuousControlSlice.Label.prop = _
    rw [withAssignment_row, rowWithAssignment_scalar left.input v t
      ⟨ContinuousControlSlice.Label.prop, by rintro ⟨j, hj⟩; cases hj⟩]
    exact hp t hbefore)
  exact ⟨hlm.1.trans hmr.1, hlm.2.1.trans hmr.2.1,
    hlm.2.2.1.trans hmr.2.2.1, hlm.2.2.2.trans hmr.2.2.2⟩

private theorem connected_nonfirst
    (records : List (RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (hc : Connected initial records final)
    (hnf : initial.coordinator ≠ .first) :
    ∀ r ∈ records, r.input.state.coordinator ≠ .first := by
  induction records generalizing initial with
  | nil => simp
  | cons head tail ih =>
      intro r hr
      rcases List.mem_cons.mp hr with heq | hmem
      · subst r
        rw [hc.1]
        exact hnf
      · apply ih head.output.next hc.2 _ r hmem
        rw [head.output_eq]
        exact step_coordinator_ne_first head.input

private theorem connected_positive_nonfirst
    (records : List (RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (hc : Connected initial records final)
    (k : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (hk : 0 < k) (hr : records[k]? = some r) : r.input.state.coordinator ≠ .first := by
  cases records with
  | nil => simp at hr
  | cons head tail =>
      cases k with
      | zero => omega
      | succ k =>
          apply connected_nonfirst tail head.output.next final hc.2 _ r
            (List.mem_of_getElem? (by simpa only [List.getElem?_cons_succ] using hr))
          rw [head.output_eq]
          exact step_coordinator_ne_first head.input

private theorem firstLiveWindow_pos
    (records : List (RoundRecord (p := p) (rate := rate)))
    (initial final : ReferenceActivePhysicalStep.State p rate) (hc : Connected initial records final)
    (hf : initial.coordinator = .first) (hpos : 0 < records.length) :
    0 < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length := by
  cases records with
  | nil => simp at hpos
  | cons head tail =>
      have hh : head.input.state.coordinator = .first := by rw [hc.1, hf]
      have htag : tag head.input = false := by
        dsimp only [ReferenceCollectionPhaseHistory.cutoffChosen, ReferenceActivePhysicalStep.prepare]
        rw [dispatch_first head.input hh]
      simp [ReferenceFirstLiveConfirmationHistory.firstLiveWindow, htag]

/-- On an actual original suffix date at or beyond the first cutoff boundary,
the coordinator is non-first. The first physical record has false cutoff tag,
and every actual successor is structurally non-first. -/
theorem source_coordinator_ne_first
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (hleft : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time.val) :
    (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val].input.state.coordinator ≠ .first := by
  by_cases hn : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none
  · have hk := k.isLt
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hn] at hk
  · let initial := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate z rewards C_star C_h hn
    let E := ReferenceCompletePhysicalHistory.correctedSuffixRun rate z rewards C_star C_h hn
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some initial :=
      ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload rate z rewards C_star C_h hn
    have hcross := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
    obtain ⟨a, ⟨ha, hfa, _⟩, _⟩ :=
      ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
        rate z rewards C_star C_h hcross
    have hai : a = initial := Option.some.inj (ha.symm.trans hlaunch)
    have hf : initial.coordinator = .first := by simpa only [hai] using hfa
    have hrecords : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h = E.records := by
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, dite_eq_right hn]
      rfl
    have hc : Connected initial
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
        E.finalState := by rw [hrecords]; exact E.connected
    have hwpos := firstLiveWindow_pos _ initial E.finalState hc hf
      (Nat.zero_lt_of_lt k.isLt)
    have hr := List.getElem?_eq_getElem k.isLt
    have ht := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h k.val _ hr
    have hkpos : 0 < k.val := by omega
    exact connected_positive_nonfirst _ initial E.finalState hc k.val _ hkpos hr

/-- Actual original-source producer. Its only branch bounds are the real
first-live-window boundary and the original first-invocation boundary. All
local comparison, phase and parameter premises are discharged here. -/
theorem actual_source_assignment
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (replacement : CheckedAssignmentSample.AssignmentVector p)
    (hleft : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)).length ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time.val)
    (hbefore : (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val].input.time.val <
      ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
    let rv : RoundRecord (p := p) (rate := rate) :=
      ⟨withAssignment r.input replacement, step (withAssignment r.input replacement), rfl⟩
    ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none ∧
      r.input.state.coordinator ≠ .first ∧ r.evidence = rv.evidence ∧
      cell (roundRecordCode r) = cell (roundRecordCode rv) ∧ tag r.input = tag rv.input ∧
      cell0 rate r = cell0 rate rv := by
  have hn := source_parameters_none rate rewards C_star C_h z k hbefore
  have hnf := source_coordinator_ne_first rate rewards C_star C_h z k hleft
  exact ⟨hn, hnf, compare_withAssignment _ hnf hn replacement⟩

end Bandits.Support.ReferenceFirstCollectionAssignmentStepNonRead
