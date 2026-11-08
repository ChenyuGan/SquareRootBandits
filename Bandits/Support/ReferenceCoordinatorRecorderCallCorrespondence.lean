/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCoordinatorRecorderCallTrace

/-!
# Operational correspondence for the actual coordinator recorder calls

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-295,355-426`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:16-64`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

These are internal identities on the existing actual round records. The
intended consumer is the physical common calendar-arrival/queue realization.
Recorder rejection produces `none`. A successful output with no gate is
`some output` with `output.gateArm = none`; its armwise raw projection is
`some 0`. The full output retains this distinction through later failures.
No reward-truth, follower-arrival, queue, totality, overflow-law or regret
claim is made here.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence

open ConstructorDimensions ReferenceActivePhysicalStep
open ReferenceActiveHorizonMeasurability

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private theorem preparation_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record.output.preparation = prepare record.input := by
  exact congrArg RoundOutput.preparation record.output_eq

/-- The literal selection at an aligned arm-choice coordinate. This is only
the existing selection's exposed fields, with no additional state or run. -/
def selectionOfArm (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (htime : time = x.time) : Selection x := {
  view := {
    payload := payload
    pendingAtChoice := started.pending
    cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
    complementWeights := weights }
  started := started
  pending_eq := rfl
  cutoff_eq := rfl
  arm := arm.arm
  choice_eq := by simpa only [htime] using arm.armChoice_eq }

theorem selectionAt_eq (x : RoundInput p rate) (payload : Payload rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights x.row)
    (htime : time = x.time) :
    selectionAt x payload started time weights arm =
      some (selectionOfArm x payload started time weights arm htime) := by
  simp only [selectionAt, dite_eq_left htime, selectionOfArm]

/-- The exact local telescope for the live bit: it needs the payload's stored
start and the cutoff of this same original clock result. -/
theorem live_selectionOfArm
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights record.input.row)
    (htime : time = record.input.time) :
    ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection (selectionOfArm record.input payload started time weights arm htime)) =
      decide (CoordinatorLocalArmChoice.assignmentIsLive payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        record.input.time) := by
  exact ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive (roundRecordCode record)
    (ReferenceLiveDispatchOutputMeasurability.encodeSelection
      (selectionOfArm record.input payload started time weights arm htime)) record.input.time rfl

/-- The enable telescope uses the actual clock boundary, without presuming
any relation between an arbitrary payload and a clock. -/
theorem enabled_selectionOfArm
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights record.input.row)
    (htime : time = record.input.time) :
    ReferenceCoordinatorRecorderCallTrace.enabled (roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection (selectionOfArm record.input payload started time weights arm htime)) =
      decide (record.input.time.val + 1 < started.clock.g) :=
  ReferenceCoordinatorRecorderCallTrace.enabled_eq_time_before_startGrid _ _

private theorem feedback_eq
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    roundRecordCodeFeedback (roundRecordCode record)
        (ActiveRoundActions.coordinator p.two_le_m) =
      record.output.preparation.coordinatorObservation :=
  congrFun (roundRecordCode_front record).2.2.2 _

/-- Conditional local input identity, before the actual dispatch discharges
the live test. The only selector is the given preparation's actual choice. -/
theorem inputFromSelection_live
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta) (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (arm : CoordinatorRoundDispatch.ArmSelection r.payload started time r.complementWeights record.input.row)
    (htime : time = record.input.time)
    (hselected : record.output.preparation.coordinator.selection =
      some (selectionOfArm record.input r.payload started time r.complementWeights arm htime))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      record.input.time) :
    ReferenceCoordinatorRecorderCallTrace.inputFromSelection record (ReferenceLiveDispatchOutputMeasurability.encodeSelection
        (selectionOfArm record.input r.payload started time r.complementWeights arm htime)) =
      CoordinatorRecorderComplementBridge.recorderInput (liveRecordingInput record.output.preparation r started) := by
  have harm : record.output.preparation.coordinator.arm = arm.arm := by
    rw [DispatchCut.arm, hselected]
    rfl
  have hbit := live_selectionOfArm record r.payload started time r.complementWeights arm htime
  rw [decide_eq_true hlive] at hbit
  unfold ReferenceCoordinatorRecorderCallTrace.inputFromSelection
  rw [hbit]
  simp only [ite_true, ReferenceLiveDispatchOutputMeasurability.encodeSelection,
    selectionOfArm, liveRecordingInput, harm, feedback_eq, RoundInput.row]
  rfl

/-- Collection has its own literal input mode. This local telescope exposes
the non-live fact which the actual cutoff/collection branch must supply. -/
theorem inputFromSelection_collection
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection payload started time weights record.input.row)
    (htime : time = record.input.time)
    (hselected : record.output.preparation.coordinator.selection =
      some (selectionOfArm record.input payload started time weights arm htime))
    (hlive : ¬ CoordinatorLocalArmChoice.assignmentIsLive payload (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      record.input.time) :
    ReferenceCoordinatorRecorderCallTrace.inputFromSelection record (ReferenceLiveDispatchOutputMeasurability.encodeSelection
        (selectionOfArm record.input payload started time weights arm htime)) =
      CoordinatorRecorderComplementBridge.recorderInput (collectionRecordingInput record.output.preparation payload started weights) := by
  have harm : record.output.preparation.coordinator.arm = arm.arm := by
    rw [DispatchCut.arm, hselected]
    rfl
  have hbit := live_selectionOfArm record payload started time weights arm htime
  rw [decide_eq_false hlive] at hbit
  unfold ReferenceCoordinatorRecorderCallTrace.inputFromSelection
  rw [hbit]
  simp only [Bool.false_eq_true, ite_false,
    ReferenceLiveDispatchOutputMeasurability.encodeSelection, selectionOfArm, collectionRecordingInput, harm, feedback_eq]
  rfl

/-- A successful unchanged clock call on a live assignment is strictly
before its grid boundary. At equality the actual clock takes the cutoff
branch, so the original result cannot have an unchanged clock. -/
theorem startRound_live_before_grid
    (payload : Payload rate) (clock : CoordinatorPhaseClock.ClockRegisters p)
    (pending : Finset (Fin (p.m - 1))) (time : Fin p.T)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time clock pending = .ok started)
    (hsigma : clock.sigma = some payload.sigma)
    (hframe : started.clock = clock)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) time) :
    time.val + 1 < started.clock.g := by
  have hvalid : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock ∧
      CoordinatorPhaseClock.startRoundTimeValid p time clock := by
    unfold CoordinatorPhaseClock.startRound at hstart
    split at hstart
    · split at hstart
      · split at hstart
        · exact ⟨‹_›, ‹_›⟩
        · contradiction
      · contradiction
    · contradiction
  have hu : clock.u = none := by
    cases hcutoff : clock.u with
    | none => rfl
    | some cutoff =>
        have ht := hvalid.2
        simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hcutoff] at ht
        have hlt := hlive.2
        rw [hframe, hcutoff] at hlt
        change time.val + 1 < cutoff.val + 1 at hlt
        omega
  have htime := hvalid.2
  simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu,
    FollowerCutoffScan.calendarRound] at htime
  have hne : time.val + 1 ≠ clock.g := by
    intro heq
    obtain ⟨result, hrun, hclock, _, _, _⟩ := CoordinatorPhaseClock.startRound_grid_cutoff
      p rate.eta.val time payload.sigma clock pending
      (by
        unfold CoordinatorPhaseClock.startRound at hstart
        split at hstart
        · assumption
        · contradiction)
      hvalid.1 hvalid.2 hsigma hu heq
    have he : result = started := Except.ok.inj (hrun.symm.trans hstart)
    have hc := congrArg CoordinatorPhaseClock.ClockRegisters.u
      (hframe.symm.trans (he ▸ hclock))
    simp only [hu] at hc
    cases hc
  rw [hframe]
  omega

private theorem dispatchLive_live (x : CoordinatorRoundDispatch.LiveInput p) :
    match CoordinatorRoundDispatch.dispatchLive x with
    | .continuingChosen dispatched _ _ _ =>
        CoordinatorLocalArmChoice.assignmentIsLive x.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          x.registers.time ∧
        CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame x.registers dispatched.startResult ∧
        x.registers.priorClock.sigma = some x.registers.payload.sigma
    | _ => True := by
  generalize hcomputed : CoordinatorRoundDispatch.dispatchLive x = outcome
  unfold CoordinatorRoundDispatch.dispatchLive at hcomputed
  repeat' first
    | (split at hcomputed)
    | (extract_lets at hcomputed)
    | (subst outcome; trivial)
  all_goals
    dsimp +zetaDelta only at hcomputed
    split at hcomputed
    · contradiction
    · subst outcome
      trivial

private theorem dispatch_first_computed (x : RoundInput p rate)
    (outcome : CoordinatorRoundDispatch.FirstOutcome (firstInput x))
    (hcut : dispatch x = .first outcome) :
    CoordinatorRoundDispatch.dispatchFirst (firstInput x) = outcome := by
  cases hs : x.state.coordinator with
  | first =>
      rw [dispatch_first x hs] at hcut
      exact DispatchCut.first.inj hcut
  | live r q base =>
      simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch] at hcut
      contradiction
  | collection payload ledger saved =>
      simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch] at hcut
      split at hcut <;> contradiction
  | dagger =>
      simp only [dispatch, hs] at hcut
      contradiction

private theorem dispatch_live_computed (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome (liveInput x r q base))
    (hcut : dispatch x = .live r q base outcome) :
    CoordinatorRoundDispatch.dispatchLive (liveInput x r q base) = outcome := by
  cases hs : x.state.coordinator with
  | first =>
      simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch] at hcut
      contradiction
  | live r' q' base' =>
      simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch] at hcut
      cases hcut
      rfl
  | collection payload ledger saved =>
      simp only [dispatch, hs, CoordinatorRoundDispatch.dispatch] at hcut
      split at hcut <;> contradiction
  | dagger =>
      simp only [dispatch, hs] at hcut
      contradiction

/-- The first branch's original installed call is aligned and live. Both
facts follow from the computed first dispatcher and its checked start. -/
theorem first_call_frame (x : RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)))
    (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hcut : dispatch x = .first (.chosen installed arm)) :
    installed.registers.time = x.time ∧
      CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
        x.time ∧ x.time.val + 1 < installed.startRoundResult.clock.g := by
  have hcomputed := dispatch_first_computed x _ hcut
  have ht := dispatchFirst_chosen_time x installed arm hcomputed
  have hresult : installed.startRoundResult =
      CoordinatorAssignmentRegisterInstall.firstStartRoundResult
        (CoordinatorRoundDispatch.firstLaunchInput (firstInput x)) :=
    Except.ok.inj (installed.startRound_eq.symm.trans
      (CoordinatorAssignmentRegisterInstall.first_start_round_success _))
  have hlo := arm.choiceInputsValid.time.assignment_started
  rw [ht] at hlo
  have hu : installed.startRoundResult.clock.u = none := by rw [hresult]; rfl
  have hgrid : x.time.val + 1 < installed.startRoundResult.clock.g := by
    rw [hresult]
    exact (CoordinatorAssignmentRegisterInstall.first_new_grid_boundary_valid
      (CoordinatorRoundDispatch.firstLaunchInput (firstInput x))).1
  refine ⟨ht, ⟨hlo, ?_⟩, hgrid⟩
  rw [hu]
  change x.time.val + 1 < p.T + 1
  omega

/-- The cutoff telescope uses the newly initialized ledger's literal sigma,
cutoff and freeze fields. The initializer's checked grid frame is essential;
it is not an assumption about arbitrary selection data. -/
theorem cutoff_call_frame (x : RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger (liveRegistersAt r x.time))
    (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time)
    (hdomains : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (liveRegistersAt r x.time) (liveOwnedAt r q x.time) base x.time)
    (hclock : started.clock = { r.priorClock with u := some x.time }) :
    (¬ CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time) ∧
      decide (x.time.val + 1 < started.clock.g) = collectionEnabled (sharedLedger ledger) x.time := by
  constructor
  · rw [hclock]
    change ¬ (_ ∧ x.time.val + 1 < x.time.val + 1)
    omega
  · unfold collectionEnabled
    rw [(sharedLedger_fields ledger).2.1, (sharedLedger_fields ledger).2.2.1,
      (sharedLedger_fields ledger).2.2.2.1, hledger, hclock]
    change decide (x.time.val + 1 < r.priorClock.g) =
      decide (0 < r.payload.sigma.val + 1 ∧ x.time.val + 1 ≤ x.time.val + 1 ∧
        x.time.val + 1 < r.gridBoundary)
    have hg : r.gridBoundary = r.priorClock.g := hdomains.2.1
    rw [hg]
    apply Bool.decide_congr
    omega

/-- The incoming collection telescope derives the reached cutoff and all
ledger/clock matching fields from the prepared snapshot's own checked input.
It includes rounds at and beyond freeze, where the enable bit is false. -/
theorem collection_call_frame (x : RoundInput p rate) (payload : Payload rate)
    (ledger : Ledger rate) (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (collectionInput x payload ledger clock cutoff)) :
    (¬ CoordinatorLocalArmChoice.assignmentIsLive payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u) x.time) ∧
      decide (x.time.val + 1 < snapshot.clockStarted.clock.g) = collectionEnabled ledger x.time := by
  have ht : payload.sigma.val < x.time.val ∧ cutoff.val ≤ x.time.val := by
    have htime := snapshot.inputsValid.clock_start_time_valid
    change CoordinatorPhaseClock.startRoundTimeValid p x.time clock at htime
    have hsigma : clock.sigma = some payload.sigma := snapshot.inputsValid.clock_sigma_eq
    have hcutoff : clock.u = some cutoff := snapshot.inputsValid.clock_cutoff_eq
    simpa only [CoordinatorPhaseClock.startRoundTimeValid,
      hsigma, hcutoff] using htime
  have hu : snapshot.clockStarted.clock.u = some cutoff := by
    rw [snapshot.clockStarted_frame.1]
    exact snapshot.inputsValid.clock_cutoff_eq
  have hs : ledger.sigma = payload.sigma.val + 1 := snapshot.inputsValid.ledger_sigma_eq
  have hc : ledger.cutoff = cutoff.val + 1 := snapshot.inputsValid.ledger_cutoff_eq
  have hg : snapshot.clockStarted.clock.g = ledger.freezeAt := by
    rw [snapshot.clockStarted_frame.1]
    exact snapshot.inputsValid.ledger_freeze_eq.symm
  constructor
  · rw [hu]
    change ¬ (_ ∧ x.time.val + 1 < cutoff.val + 1)
    omega
  · unfold collectionEnabled
    rw [hs, hc, hg]
    apply Bool.decide_congr
    omega

/-- Later-start clock effects supply same-round alignment, sentinel cutoff,
and a new boundary strictly after this round. The checked arm supplies the
actual installed payload's lower time bound, with no truth invariant. -/
theorem later_call_frame (x : RoundInput p rate) (payload : Payload rate)
    (ledger : Ledger rate) (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid (collectionInput x payload ledger clock cutoff))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending = .ok started)
    (hinstruction : started.assignmentStart = some instruction)
    (installedPayload : Payload rate)
    (weights : CanonicalFastSampling.FastArm installedPayload.slowSet → ℝ)
    (arm : CoordinatorRoundDispatch.ArmSelection installedPayload started instruction.time weights x.row) :
    instruction.time = x.time ∧
      CoordinatorLocalArmChoice.assignmentIsLive installedPayload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time ∧
      x.time.val + 1 < started.clock.g := by
  have ht := later_instruction_time x payload ledger clock cutoff core started instruction
    hstart hinstruction
  have hclock := CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
    x.time clock ledger.pending started instruction core.clock_parameter_valid
    core.clock_registers_valid core.clock_start_time_valid hstart hinstruction
  rcases hclock with ⟨_, _, hsigma, hu, _, _, _, _⟩
  have hlo := arm.choiceInputsValid.time.assignment_started
  rw [ht] at hlo
  have hg := started.gridDomain
  simp only [CoordinatorPhaseClock.clockGridDomain, hsigma] at hg
  refine ⟨ht, ⟨hlo, ?_⟩, hg.1⟩
  rw [hu]
  change x.time.val + 1 < p.T + 1
  omega

/-- Complete phase frames on the actual preparation. Failure constructors
need no extra premise. The five successful branches use their own payload,
original clock result, and, for collection, their actual ledger. -/
theorem actual_call_frames
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    match record.output.preparation.coordinator with
    | .first (.chosen installed _) =>
        installed.registers.time = record.input.time ∧
        CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
          record.input.time ∧ record.input.time.val + 1 < installed.startRoundResult.clock.g
    | .live r _ _ (.continuingChosen dispatched _ _ _) =>
        CoordinatorLocalArmChoice.assignmentIsLive r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          record.input.time ∧ record.input.time.val + 1 < dispatched.startResult.clock.g
    | .live r _ _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
        (¬ CoordinatorLocalArmChoice.assignmentIsLive r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u)
          record.input.time) ∧
        decide (record.input.time.val + 1 < dispatched.startResult.clock.g) =
          collectionEnabled (sharedLedger ledger) record.input.time
    | .collection payload ledger _ _ (.continuing _ snapshot _ _) =>
        (¬ CoordinatorLocalArmChoice.assignmentIsLive payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p snapshot.clockStarted.clock.u)
          record.input.time) ∧
        decide (record.input.time.val + 1 < snapshot.clockStarted.clock.g) =
          collectionEnabled ledger record.input.time
    | .collection _ _ _ _ (.laterChosen _ _ started _ instruction _ _ _ _ installed _) =>
        instruction.time = record.input.time ∧
        CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) record.input.time ∧
        record.input.time.val + 1 < started.clock.g
    | _ => True := by
  have hactual : dispatch record.input = record.output.preparation.coordinator :=
    (congrArg PreparedRound.coordinator (preparation_eq record)).symm
  generalize hcut : record.output.preparation.coordinator = cut at *
  cases cut with
  | first outcome =>
      cases outcome with
      | chosen installed arm => exact first_call_frame record.input installed arm hactual
      | _ => trivial
  | live r q base outcome =>
      have hcomputed := dispatch_live_computed record.input r q base outcome hactual
      have hframes := dispatchLive_live (liveInput record.input r q base)
      rw [hcomputed] at hframes
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          exact ⟨hframes.1, startRound_live_before_grid r.payload r.priorClock
            (liveRegistersAt r record.input.time).clockPending record.input.time
            dispatched.startResult hstart hframes.2.2 hframes.2.1.1 hframes.1⟩
      | cutoffChosen dispatched _ ledger _ hledger hdomains hclock _ _ _ =>
          exact cutoff_call_frame record.input r q base dispatched.startResult ledger
            hledger hdomains hclock
      | _ => trivial
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          exact collection_call_frame record.input payload ledger clock cutoff snapshot
      | laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed arm =>
          exact later_call_frame record.input payload ledger clock cutoff core started
            instruction hstart hinstruction installed.registers.payload installed.registers.complementWeights arm
      | _ => trivial
  | invalidCollectionCutoff => trivial
  | dagger => trivial

/-- The collection input identity for any actual local selection, with its
non-live test exposed. The selected arm and feedback are the physical ones. -/
theorem inputFromSelection_collection_selected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hnotLive : ¬ CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time) :
    ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
      CoordinatorRecorderComplementBridge.recorderInput
        (collectionRecordingInput record.output.preparation selected.view.payload selected.started
          selected.view.complementWeights) := by
  have harm : record.output.preparation.coordinator.arm = selected.arm := by
    rw [DispatchCut.arm, hselected]
  have hbit := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
    (roundRecordCode record) (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
    record.input.time rfl
  change ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
    (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
    decide (CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time) at hbit
  rw [decide_eq_false hnotLive] at hbit
  unfold ReferenceCoordinatorRecorderCallTrace.inputFromSelection
  rw [hbit]
  simp only [Bool.false_eq_true, ite_false, ReferenceLiveDispatchOutputMeasurability.encodeSelection,
    collectionRecordingInput, harm, feedback_eq]
  rfl

/-- Unconditional operational input identity on every actual round record.
The original selection guard is discharged for each chosen constructor;
every other constructor has no recorder call. -/
theorem inputFromCode_eq_actualBranchInput
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCoordinatorRecorderCallTrace.inputFromCode record =
      ReferenceCoordinatorRecorderCallTrace.actualBranchInput record := by
  rw [ReferenceCoordinatorRecorderCallTrace.inputFromCode_actualSelection]
  unfold ReferenceCoordinatorRecorderCallTrace.actualBranchInput
  dsimp only
  have hframes := actual_call_frames record
  generalize hcut : record.output.preparation.coordinator = cut at hframes ⊢
  cases cut with
  | first outcome =>
      cases outcome with
      | chosen installed arm =>
          have hs := selectionAt_eq record.input installed.registers.payload installed.startRoundResult
            installed.registers.time installed.registers.complementWeights arm hframes.1
          have hselected : record.output.preparation.coordinator.selection =
              some (selectionOfArm record.input installed.registers.payload installed.startRoundResult
                installed.registers.time installed.registers.complementWeights arm hframes.1) := by
            rw [hcut]
            exact hs
          change (selectionAt _ _ _ _ _ _).map _ = _
          rw [hs, Option.map_some]
          exact congrArg some (inputFromSelection_live record installed.registers installed.startRoundResult
            installed.registers.time arm hframes.1 hselected hframes.2.1)
      | _ => rfl
  | live r q base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          have hs := selectionAt_eq record.input r.payload dispatched.startResult record.input.time
            (liveRegistersAt r record.input.time).complementWeights arm rfl
          have hselected : record.output.preparation.coordinator.selection =
              some (selectionOfArm record.input r.payload dispatched.startResult record.input.time
                (liveRegistersAt r record.input.time).complementWeights arm rfl) := by
            rw [hcut]
            exact hs
          change (selectionAt _ _ _ _ _ _).map _ = _
          rw [hs, Option.map_some]
          exact congrArg some (inputFromSelection_live record (liveRegistersAt r record.input.time)
            dispatched.startResult record.input.time arm rfl hselected hframes.1)
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
          have hs := selectionAt_eq record.input r.payload dispatched.startResult record.input.time
            (liveRegistersAt r record.input.time).complementWeights arm rfl
          have hselected : record.output.preparation.coordinator.selection =
              some (selectionOfArm record.input r.payload dispatched.startResult record.input.time
                (liveRegistersAt r record.input.time).complementWeights arm rfl) := by
            rw [hcut]
            exact hs
          change (selectionAt _ _ _ _ _ _).map _ = _
          rw [hs, Option.map_some]
          exact congrArg some (inputFromSelection_collection record r.payload dispatched.startResult
            record.input.time (liveRegistersAt r record.input.time).complementWeights arm rfl
            hselected hframes.1)
      | _ => rfl
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simp only [DispatchCut.selection, Option.map_some]
          apply congrArg some
          apply inputFromSelection_collection_selected record
          · rw [hcut]
            rfl
          · exact hframes.1
      | laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed arm =>
          have hs := selectionAt_eq record.input installed.registers.payload started instruction.time
            installed.registers.complementWeights arm hframes.1
          have hselected : record.output.preparation.coordinator.selection =
              some (selectionOfArm record.input installed.registers.payload started instruction.time
                installed.registers.complementWeights arm hframes.1) := by
            rw [hcut]
            exact hs
          change (selectionAt _ _ _ _ _ _).map _ = _
          rw [hs, Option.map_some]
          exact congrArg some (inputFromSelection_live record installed.registers started instruction.time
            arm hframes.1 hselected hframes.2.1)
      | _ => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- The recorded result is the physical recorder operation on the actual
optional branch input. This consumes the live and collection tail equations:
service, confirmation, UP, ledger and clock failures do not erase a result.
Dispatch failure has no call, and recorder rejection remains `none`. -/
theorem recording_eq_actualBranchRun
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCoordinatorRecorderCallTrace.recording (roundRecordCode record) =
      (ReferenceCoordinatorRecorderCallTrace.actualBranchInput record).bind CoordinatorRecordingOperation.run := by
  rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
  have hobs : record.coordinatorDiagnostics = record.output.preparation.observeCoordinator := by
    rw [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics, record.output_eq]
    rfl
  rw [hobs]
  have hguard : ReferenceCoordinatorRecorderCallTrace.actualBranchInput record = none ↔
      record.output.preparation.coordinator.selection = none := by
    rw [← inputFromCode_eq_actualBranchInput, ReferenceCoordinatorRecorderCallTrace.inputFromCode_actualSelection]
    exact Option.map_eq_none_iff
  by_cases hnone : record.output.preparation.coordinator.selection = none
  · rw [hguard.mpr hnone]
    simp only [Option.bind_none, PreparedRound.observeCoordinator, hnone]
    cases record.output.preparation.coordinator <;> rfl
  · unfold PreparedRound.observeCoordinator
    simp only [hnone, dite_false]
    unfold ReferenceCoordinatorRecorderCallTrace.actualBranchInput
    dsimp only
    generalize hcut : record.output.preparation.coordinator = cut
    cases cut with
    | first outcome =>
        cases outcome with
        | chosen installed arm =>
            exact ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run _ _ _ _ _
        | _ => rfl
    | live r q base outcome =>
        cases outcome with
        | continuingChosen dispatched hstart continuation arm =>
            exact ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run _ _ _ _ _
        | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
            exact ReferenceCoordinatorCollectionRecording.collectionPostChoice_recording_eq_run _ _ _ _ _
        | _ => rfl
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            exact ReferenceCoordinatorCollectionRecording.collectionPostChoice_recording_eq_run _ _ _ _ _
        | laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed arm =>
            exact ReferenceCoordinatorLiveRecording.livePostChoice_recording_eq_run _ _ _ _ _
        | _ => rfl
    | invalidCollectionCutoff => rfl
    | dagger => rfl

/-- The requested selected-call producer. Its sole branch premise identifies
the original dispatch selection; no recorder or subsequent success is assumed.
All rows, the original selected index, grid feedback and incoming banks remain
those of `record.input`. A successful no-gate output is retained as `some`,
whereas a rejected recorder is `none`. -/
theorem recording_eq_run_of_selected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : (dispatch record.input).selection = some selected) :
    ReferenceCoordinatorRecorderCallTrace.recording (roundRecordCode record) =
      CoordinatorRecordingOperation.run (ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)) := by
  rw [recording_eq_actualBranchRun, ← inputFromCode_eq_actualBranchInput,
    ReferenceCoordinatorRecorderCallTrace.inputFromCode_of_selected record selected hselected]
  rfl

/-- The retained enable bit is exactly the freeze test used by the literal
recorder input. This identity imposes no payload/clock alignment; the actual
phase theorem below derives the additional live and ledger facts. -/
theorem enabled_eq_not_isFrozen_input
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input) :
    ReferenceCoordinatorRecorderCallTrace.enabled (roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
      decide (¬ CoordinatorRecordingOperation.isFrozen
        (ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected))) := by
  unfold ReferenceCoordinatorRecorderCallTrace.enabled
  apply Bool.decide_congr
  rfl

private theorem live_selected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input) :
    ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
      decide (CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
        selected.view.cutoff record.input.time) :=
  ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
    (roundRecordCode record) (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
    record.input.time rfl

private theorem enabled_selected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input) :
    ReferenceCoordinatorRecorderCallTrace.enabled (roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
      decide (record.input.time.val + 1 < selected.started.clock.g) :=
  ReferenceCoordinatorRecorderCallTrace.enabled_eq_time_before_startGrid _ _

/-- Operational schedule and enable bits for the actual selected call.
First, continuing-live and later-start calls are live and enabled. Cutoff
and continuing-collection calls are non-live and use exactly the enable test
of their new or incoming ledger. Non-call constructors cannot select a call.
No alignment or success premise is supplied beyond the actual selector. -/
theorem actual_phase_bits
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : (dispatch record.input).selection = some selected) :
    match record.output.preparation.coordinator with
    | .first (.chosen _ _) | .live _ _ _ (.continuingChosen _ _ _ _)
        | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) =>
        ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true ∧
        ReferenceCoordinatorRecorderCallTrace.enabled (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true
    | .live _ _ _ (.cutoffChosen _ _ ledger _ _ _ _ _ _ _) =>
        ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false ∧
        ReferenceCoordinatorRecorderCallTrace.enabled (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
          collectionEnabled (sharedLedger ledger) record.input.time
    | .collection _ ledger _ _ (.continuing _ _ _ _) =>
        ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false ∧
        ReferenceCoordinatorRecorderCallTrace.enabled (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) =
          collectionEnabled ledger record.input.time
    | _ => False := by
  have hsel : record.output.preparation.coordinator.selection = some selected := by
    rw [preparation_eq]
    exact hselected
  have hframes := actual_call_frames record
  generalize hcut : record.output.preparation.coordinator = cut at hsel hframes ⊢
  cases cut with
  | first outcome =>
      cases outcome with
      | chosen installed arm =>
          change selectionAt _ _ _ _ _ _ = some selected at hsel
          rw [selectionAt_eq record.input installed.registers.payload installed.startRoundResult
            installed.registers.time installed.registers.complementWeights arm hframes.1] at hsel
          cases hsel
          constructor
          · exact (live_selectionOfArm record installed.registers.payload installed.startRoundResult
              installed.registers.time installed.registers.complementWeights arm hframes.1).trans
              (decide_eq_true hframes.2.1)
          · exact (enabled_selectionOfArm record installed.registers.payload installed.startRoundResult
              installed.registers.time installed.registers.complementWeights arm hframes.1).trans
              (decide_eq_true hframes.2.2)
      | _ => cases hsel
  | live r q base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          change selectionAt _ _ _ _ _ _ = some selected at hsel
          rw [selectionAt_eq record.input r.payload dispatched.startResult record.input.time
            (liveRegistersAt r record.input.time).complementWeights arm rfl] at hsel
          cases hsel
          constructor
          · exact (live_selectionOfArm record r.payload dispatched.startResult record.input.time
              (liveRegistersAt r record.input.time).complementWeights arm rfl).trans
              (decide_eq_true hframes.1)
          · exact (enabled_selectionOfArm record r.payload dispatched.startResult record.input.time
              (liveRegistersAt r record.input.time).complementWeights arm rfl).trans
              (decide_eq_true hframes.2)
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
          change selectionAt _ _ _ _ _ _ = some selected at hsel
          rw [selectionAt_eq record.input r.payload dispatched.startResult record.input.time
            (liveRegistersAt r record.input.time).complementWeights arm rfl] at hsel
          cases hsel
          constructor
          · exact (live_selectionOfArm record r.payload dispatched.startResult record.input.time
              (liveRegistersAt r record.input.time).complementWeights arm rfl).trans
              (decide_eq_false hframes.1)
          · exact (enabled_selectionOfArm record r.payload dispatched.startResult record.input.time
              (liveRegistersAt r record.input.time).complementWeights arm rfl).trans hframes.2
      | _ => cases hsel
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simp only [DispatchCut.selection, Option.some.injEq] at hsel
          subst selected
          constructor
          · exact (live_selected record _).trans (decide_eq_false hframes.1)
          · exact (enabled_selected record _).trans hframes.2
      | laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed arm =>
          change selectionAt _ _ _ _ _ _ = some selected at hsel
          rw [selectionAt_eq record.input installed.registers.payload started instruction.time
            installed.registers.complementWeights arm hframes.1] at hsel
          cases hsel
          constructor
          · exact (live_selectionOfArm record installed.registers.payload started instruction.time
              installed.registers.complementWeights arm hframes.1).trans (decide_eq_true hframes.2.1)
          · exact (enabled_selectionOfArm record installed.registers.payload started instruction.time
              installed.registers.complementWeights arm hframes.1).trans (decide_eq_true hframes.2.2)
      | _ => cases hsel
  | invalidCollectionCutoff => cases hsel
  | dagger => cases hsel

/-- Absence of a branch input is exactly absence of the actual selection.
This includes malformed collection cutoffs, dagger and all dispatch failures. -/
theorem actualBranchInput_eq_none_iff
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCoordinatorRecorderCallTrace.actualBranchInput record = none ↔
      (dispatch record.input).selection = none := by
  rw [← inputFromCode_eq_actualBranchInput,
    ReferenceCoordinatorRecorderCallTrace.inputFromCode_actualSelection, Option.map_eq_none_iff,
    preparation_eq]
  rfl

/-- A non-call record has no recorder result. This does not identify recorder
rejection with successful no-gate output on a selected call. -/
theorem recording_eq_none_of_no_selection
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hnone : (dispatch record.input).selection = none) :
    ReferenceCoordinatorRecorderCallTrace.recording (roundRecordCode record) = none := by
  rw [recording_eq_actualBranchRun, (actualBranchInput_eq_none_iff record).mpr hnone]
  rfl

/-- The scalar raw diagnostic of a selected call is the original operation's
gate-indexed projection. Successful `gateArm = none` gives `some 0`; only
operation rejection gives `none`. Enabled zero-arrival service remains a
separate downstream operation from disabled preservation. -/
theorem coordinatorRaw_eq_run_of_selected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection record.input)
    (hselected : (dispatch record.input).selection = some selected) (arm : Fin p.K) :
    ReferenceCoordinatorRecorderCallTrace.coordinatorRaw (roundRecordCode record) arm =
      (CoordinatorRecordingOperation.run (ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected))).map
          (fun output => if output.gateArm = some arm then output.rawArrival else 0) := by
  rw [ReferenceCoordinatorRecorderCallTrace.coordinatorRaw, recording_eq_run_of_selected record selected hselected]

end Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence

end
