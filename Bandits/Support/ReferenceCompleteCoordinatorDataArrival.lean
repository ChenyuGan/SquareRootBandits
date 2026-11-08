/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteDataOwnerFeedback

/-!
# Complete-source selected live coordinator DATA arrival

Sources: `sources/zip4/manuscript/05_binary_transport.tex:60-124,354-429`,
`sources/zip4/manuscript/06_interruptions.tex:110-163,246-299`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-177`.

At one actually selected live coordinator call, this theorem constructs the
accepted recorder's runtime-valid local input from the original selected
dispatch. It identifies the literal DATA/source/freeze/ownership/mask/thinning
gate, the original grid-reward floor, and the retained coordinator diagnostic.
The result is pointwise at the original record and carries no service-pass or
whole-run success claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceCoordinatorRecorderCallTrace
open Bandits.Support.ReferenceCoordinatorRecorderCallCorrespondence
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.ReferenceCoordinatorLiveRecording
open Bandits.Support.ReferenceActiveDataOwnership
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount

namespace Bandits.Support.ReferenceCompleteCoordinatorDataArrival

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private theorem selected_live_call_arrival
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (arm : CoordinatorRoundDispatch.ArmSelection registers.payload started time
      registers.complementWeights record.input.row)
    (htime : time = record.input.time)
    (hselectedCall : selected =
      ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
        record.input registers.payload started time registers.complementWeights arm htime)
    (hselected : record.output.preparation.coordinator.selection =
      some (ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
        record.input registers.payload started time registers.complementWeights arm htime))
    (hcallLive : CoordinatorLocalArmChoice.assignmentIsLive registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      record.input.time)
    (htraceLive : ReferenceCoordinatorRecorderCallTrace.live
      (roundRecordCode record)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hprepare : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input)
    (_hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hownerGeometry :
      ∀ (_hlive : CoordinatorLocalArmChoice.assignmentIsLive
          selected.view.payload selected.view.cutoff record.input.time)
        (_hdata : PublicDiscreteDraws.slotDraw
          (record.input.row.2 record.input.time).1 = dataSlot),
        ∀ (owner : Fin p.m) (j : Fin p.K)
          (_haction : (ReferenceActivePhysicalStep.prepare record.input).arms.actions owner = j)
          (_howns : SnapshotRecordingKernel.owns p
            (.live selected.view.payload.assignment
              (ReferenceActiveDataOwnership.choiceSnapshot selected states)) owner j)
          (_hmask : CanonicalRecordingSlice.recordingMask (K_pos p) owner j
            (record.input.row.2 record.input.time).1),
          FiniteBanditModel.collisionFreeFor
              (ReferenceActivePhysicalStep.prepare record.input).arms.actions owner ∧
            (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback owner =
              rewards record.input.time j ∧
            ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations owner).val.val =
              ((rewards record.input.time j).val : ℝ) / (D p : ℝ)) :
    ∃ (valid : CoordinatorRecordingOperation.InputsValid
        (ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected))),
      let a := ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
      let j := selected.arm
      let F0 := Nat.floor ((D p : ℝ) * rate.eta.val *
        (((rewards record.input.time j).val : ℝ) / (D p : ℝ)) /
        CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor j)
      let G0 : Prop :=
        CoordinatorRecordingOperation.selectedSlot a = dataSlot ∧
        CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m ∧
        ¬ CoordinatorRecordingOperation.isFrozen a ∧
        CoordinatorRecordingOperation.ownsArm a.mode a.ownArm ∧
        CoordinatorRecordingOperation.ownMaskPasses a ∧
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          ((record.input.row.2 record.input.time).1)).val ≤
            CoordinatorRecordingOperation.coordinatorThreshold a valid
      ∃ out : CoordinatorRecordingOperation.Output p,
        CoordinatorRecordingOperation.run a = some out ∧
        record.output.coordinator.recording = some out ∧
        out.gateArm = (if G0 then some j else none) ∧
        out.rawArrival = (if G0 then F0 else 0) ∧
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (roundRecordCode record) j = some (if G0 then F0 else 0) := by
  classical
  subst selected
  let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
    record.input registers.payload started time registers.complementWeights arm htime
  let a := ReferenceCoordinatorRecorderCallTrace.inputFromSelection record
    (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
  let j := selected.arm
  let F0 := Nat.floor ((D p : ℝ) * rate.eta.val *
    (((rewards record.input.time j).val : ℝ) / (D p : ℝ)) /
    CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor j)
  let liveInput := ReferenceActivePhysicalStep.liveRecordingInput
    record.output.preparation registers started
  have hinput : a = CoordinatorRecorderComplementBridge.recorderInput liveInput := by
    dsimp [a]
    exact ReferenceCoordinatorRecorderCallCorrespondence.inputFromSelection_live
      record registers started time arm htime hselected hcallLive
  have hlocalValid : CoordinatorRecorderComplementBridge.LocalInputsValid liveInput :=
    ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
      record.output.preparation registers started time arm
  have valid : CoordinatorRecordingOperation.InputsValid a := by
    rw [hinput]
    exact CoordinatorRecorderComplementBridge.recorderInput_inputsValid liveInput hlocalValid
  let G0 : Prop :=
    CoordinatorRecordingOperation.selectedSlot a = dataSlot ∧
    CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m ∧
    ¬ CoordinatorRecordingOperation.isFrozen a ∧
    CoordinatorRecordingOperation.ownsArm a.mode a.ownArm ∧
    CoordinatorRecordingOperation.ownMaskPasses a ∧
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
      ((record.input.row.2 record.input.time).1)).val ≤
        CoordinatorRecordingOperation.coordinatorThreshold a valid
  have hselectedPrepared :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    simpa only [hprepare] using hselected
  have hselectedDispatch :
      (ReferenceActivePhysicalStep.dispatch record.input).selection = some selected := by
    change (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected
    exact hselectedPrepared
  have hcodeGrid :
      ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback (roundRecordCode record)
          (coordinator p.two_le_m) =
        record.output.preparation.feedback.feedback (coordinator p.two_le_m) := by
    have hfront := ReferenceActiveHorizonMeasurability.roundRecordCode_front record
    simpa only [ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback] using
      congrFun hfront.2.2.2 (coordinator p.two_le_m)
  have hprepCoordinator : record.output.preparation.coordinator.arm = selected.arm := by
    rw [ReferenceActivePhysicalStep.DispatchCut.arm, hselected]
  have harm : a.ownArm = selected.arm := by
    rw [hinput]
    change record.output.preparation.coordinator.arm = selected.arm
    exact hprepCoordinator
  have heta : a.eta = rate.eta.val := by
    rw [hinput]
    rfl
  have hanchor : a.anchor = selected.view.payload.anchor := by
    rw [hinput]
    rfl
  have hmode : a.mode = .live selected.view.payload.assignment
      (decide (selected.started.pending = ∅)) := by
    have htraceLive' : ReferenceCoordinatorRecorderCallTrace.live
        (roundRecordCode record) (selected.view, selected.started, selected.arm) = true := by
      simpa only [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using htraceLive
    simp [a, ReferenceCoordinatorRecorderCallTrace.inputFromSelection,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection,
      CoordinatorRecorderComplementBridge.recorderInput,
      CoordinatorRecorderComplementBridge.recorderInputWithWeights,
      CoordinatorRecorderComplementBridge.operationMode, htraceLive']
    rfl
  have hrunEq : CoordinatorRecordingOperation.run a =
      CoordinatorRecordingOperation.executeValid a valid := by
    simp [CoordinatorRecordingOperation.run, valid]
  have htraceEqRun :=
    ReferenceCoordinatorRecorderCallCorrespondence.recording_eq_run_of_selected
      record selected hselectedDispatch
  have htraceEqDiagnostic :=
    ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics record
  have hdiagnosticEqTrace : record.output.coordinator.recording =
      ReferenceCoordinatorRecorderCallTrace.recording (roundRecordCode record) := by
    simpa [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics] using
      htraceEqDiagnostic.symm
  have hownSnapshot (hown : CoordinatorRecordingOperation.ownsArm a.mode a.ownArm) :
      SnapshotRecordingKernel.owns p
        (.live selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot selected states))
        (coordinator p.two_le_m) selected.arm := by
    have hownMode : CoordinatorRecordingOperation.ownsArm
        (.live selected.view.payload.assignment (decide (selected.started.pending = ∅)))
        selected.arm := by
      rw [← harm, ← hmode]
      exact hown
    simpa [CoordinatorRecordingOperation.ownsArm, SnapshotRecordingKernel.owns,
      SnapshotRecordingKernel.assignmentSlowSet] using hownMode
  have hmaskSnapshot (hmask : CoordinatorRecordingOperation.ownMaskPasses a) :
      CanonicalRecordingSlice.recordingMask (K_pos p) (coordinator p.two_le_m)
        selected.arm (record.input.row.2 record.input.time).1 := by
    change CanonicalRecordingSlice.recordingMask (K_pos p) (coordinator p.two_le_m)
      selected.arm (ContinuousLearningRows.sliceAt record.input.time
        (record.input.rows record.input.selected).2)
    exact hmask
  have hdataSlot (hslot : CoordinatorRecordingOperation.selectedSlot a = dataSlot) :
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 = dataSlot := by
    change PublicDiscreteDraws.slotDraw
      ((record.input.rows record.input.selected).2 record.input.time).1 = dataSlot
    exact hslot
  have hrunOfExec (out : CoordinatorRecordingOperation.Output p)
      (hExec : CoordinatorRecordingOperation.executeValid a valid = some out) :
      CoordinatorRecordingOperation.run a = some out := by
    rw [hrunEq]
    exact hExec
  have hstoredOfRun (out : CoordinatorRecordingOperation.Output p)
      (hRun : CoordinatorRecordingOperation.run a = some out) :
      record.output.coordinator.recording = some out := by
    calc
      record.output.coordinator.recording =
          ReferenceCoordinatorRecorderCallTrace.recording (roundRecordCode record) :=
        hdiagnosticEqTrace
      _ = CoordinatorRecordingOperation.run a := htraceEqRun
      _ = some out := hRun
  have zeroResult (hnotG0 : ¬ G0)
      (hexec : CoordinatorRecordingOperation.executeValid a valid =
        some (CoordinatorRecordingOperation.zeroOutput p)) :
      ∃ out : CoordinatorRecordingOperation.Output p,
        CoordinatorRecordingOperation.run a = some out ∧
        record.output.coordinator.recording = some out ∧
        out.gateArm = (if G0 then some j else none) ∧
        out.rawArrival = (if G0 then F0 else 0) ∧
        ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (roundRecordCode record) j = some (if G0 then F0 else 0) := by
    refine ⟨CoordinatorRecordingOperation.zeroOutput p, ?_, ?_, ?_, ?_, ?_⟩
    · exact hrunOfExec _ hexec
    · exact hstoredOfRun _ (hrunOfExec _ hexec)
    · simp [hnotG0, CoordinatorRecordingOperation.zeroOutput]
    · simp [hnotG0, CoordinatorRecordingOperation.zeroOutput]
    · have hraw : ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
          (roundRecordCode record) j = some 0 := by
        rw [ReferenceCoordinatorRecorderCallTrace.coordinatorRaw, htraceEqRun,
          hrunEq, hexec]
        simp [CoordinatorRecordingOperation.zeroOutput]
      simpa [hnotG0] using hraw
  by_cases hdata : CoordinatorRecordingOperation.selectedSlot a = dataSlot
  · by_cases hsource : CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m
    · by_cases hfrozen : CoordinatorRecordingOperation.isFrozen a
      · refine ⟨valid, ?_⟩
        apply zeroResult
        · intro h
          exact h.2.2.1 hfrozen
        · exact CoordinatorRecordingOperation.executeValid_zero_of_frozen
            a valid hdata hsource hfrozen
      · by_cases howns : CoordinatorRecordingOperation.ownsArm a.mode a.ownArm
        · by_cases hmask : CoordinatorRecordingOperation.ownMaskPasses a
          · by_cases hthin :
              (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
                ((record.input.row.2 record.input.time).1)).val ≤
                CoordinatorRecordingOperation.coordinatorThreshold a valid
            · have hdata' := hdataSlot hdata
              have howns' := hownSnapshot howns
              have hmask' := hmaskSnapshot hmask
              have haction : (ReferenceActivePhysicalStep.prepare record.input).arms.actions
                  (coordinator p.two_le_m) = selected.arm := by
                rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator,
                  ReferenceActivePhysicalStep.DispatchCut.arm, hselectedPrepared]
              have hcallLive' : CoordinatorLocalArmChoice.assignmentIsLive
                  selected.view.payload selected.view.cutoff record.input.time := by
                simpa [selected,
                  ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using hcallLive
              have howner := hownerGeometry hcallLive' hdata'
                (coordinator p.two_le_m) selected.arm haction howns' hmask'
              have hfeedback : record.output.preparation.feedback.feedback
                  (coordinator p.two_le_m) = rewards record.input.time selected.arm := by
                rw [hprepare]
                exact howner.2.1
              have _htypedObservation := howner.2.2
              have hroundGrid : a.observation = rewards record.input.time selected.arm := by
                have hcodeObs : a.observation =
                    ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
                      (roundRecordCode record) (coordinator p.two_le_m) := by
                  dsimp [a, ReferenceCoordinatorRecorderCallTrace.inputFromSelection,
                    ReferenceLiveDispatchOutputMeasurability.encodeSelection]
                  rfl
                calc
                  a.observation =
                      ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
                        (roundRecordCode record) (coordinator p.two_le_m) := hcodeObs
                  _ = record.output.preparation.feedback.feedback (coordinator p.two_le_m) := hcodeGrid
                  _ = rewards record.input.time selected.arm := hfeedback
              have hfloor' : CoordinatorRecordingOperation.floorArrival a = F0 := by
                rw [CoordinatorRecordingOperation.floorArrival_eq_literal]
                unfold CoordinatorRecordingOperation.observationValue
                rw [heta, hanchor, harm, hroundGrid]
                rfl
              obtain ⟨out, hexec, hgate, harrival⟩ :=
                CoordinatorRecordingOperation.executeValid_gate_and_floor a valid
                  hdata hsource hfrozen howns hmask hthin
              have hrun := hrunOfExec out hexec
              have hG0 : G0 := ⟨hdata, hsource, hfrozen, howns, hmask, hthin⟩
              have hfloorEq : out.rawArrival = F0 := by
                rw [harrival]
                exact hfloor'
              refine ⟨valid, ?_⟩
              refine ⟨out, hrun, hstoredOfRun out hrun, ?_, ?_, ?_⟩
              · have harmA : a.ownArm = selected.arm := harm
                change out.gateArm = (if G0 then some j else none)
                simpa [hG0, harmA] using hgate
              ·
                change out.rawArrival = (if G0 then F0 else 0)
                simpa [hG0] using hfloorEq
              · change ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
                    (roundRecordCode record) j = some (if G0 then F0 else 0)
                rw [ReferenceCoordinatorRecorderCallTrace.coordinatorRaw, htraceEqRun, hrun]
                have hgateOut : out.gateArm = some selected.arm := by
                  simpa [harm] using hgate
                simp [hG0, hgateOut, hfloorEq, j]
            · refine ⟨valid, ?_⟩
              apply zeroResult
              · intro h
                exact hthin h.2.2.2.2.2
              · exact CoordinatorRecordingOperation.executeValid_zero_of_thinning_rejected
                  a valid hdata hsource hfrozen howns hmask hthin
          · refine ⟨valid, ?_⟩
            apply zeroResult
            · intro h
              exact hmask h.2.2.2.2.1
            · exact CoordinatorRecordingOperation.executeValid_zero_of_mask_rejected
                a valid hdata hsource hfrozen howns hmask
        · refine ⟨valid, ?_⟩
          apply zeroResult
          · intro h
            exact howns h.2.2.2.1
          · exact CoordinatorRecordingOperation.executeValid_zero_of_unowned
              a valid hdata hsource hfrozen howns
    · refine ⟨valid, ?_⟩
      apply zeroResult
      · intro h
        exact hsource h.2.1
      · exact CoordinatorRecordingOperation.executeValid_zero_of_other_source
          a valid hdata hsource
  · refine ⟨valid, ?_⟩
    apply zeroResult
    · intro h
      exact hdata h.1
    · exact CoordinatorRecordingOperation.executeValid_zero_of_not_data a valid hdata

/-- The accepted complete-source DATA coordinator call, including every
literal rejection gate and the retained actual recorder diagnostic. -/
theorem complete_selected_live_coordinator_arrival
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin R.length),
      let r := R[k.val]'k.isLt
      ∀ (v : ReferenceActivePhysicalStep.Selection r.input),
        r.output.preparation.coordinator.selection = some v →
        CoordinatorLocalArmChoice.assignmentIsLive v.view.payload v.view.cutoff
          r.input.time →
        ∃ (valid : CoordinatorRecordingOperation.InputsValid
            (ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection v))),
          let a := ReferenceCoordinatorRecorderCallTrace.inputFromSelection r
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection v)
          let j := v.arm
          let F0 := Nat.floor ((D p : ℝ) * rate.eta.val *
            (((rewards r.input.time j).val : ℝ) / (D p : ℝ)) /
            CanonicalRecordingRates.xi p rate.eta.val v.view.payload.anchor j)
          let G0 : Prop :=
            CoordinatorRecordingOperation.selectedSlot a = dataSlot ∧
            CoordinatorRecordingOperation.selectedRecorder a = coordinator p.two_le_m ∧
            ¬ CoordinatorRecordingOperation.isFrozen a ∧
            CoordinatorRecordingOperation.ownsArm a.mode a.ownArm ∧
            CoordinatorRecordingOperation.ownMaskPasses a ∧
            (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
              ((r.input.row.2 r.input.time).1)).val ≤
                CoordinatorRecordingOperation.coordinatorThreshold a valid
          ∃ out : CoordinatorRecordingOperation.Output p,
            CoordinatorRecordingOperation.run a = some out ∧
            r.output.coordinator.recording = some out ∧
            out.gateArm = (if G0 then some j else none) ∧
            out.rawArrival = (if G0 then F0 else 0) ∧
            ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (roundRecordCode r) j = some (if G0 then F0 else 0) := by
  classical
  dsimp only
  intro k v hselected hlive
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  obtain ⟨states, memories, hprepare, _hactualOrdinary, hordinary, hfields, hgeometry⟩ :=
    ReferenceCompleteDataOwnerFeedback.complete_selected_source_data_owner_geometry
      rewards C_star C_h source k v hselected
  have hdispatch :
      (ReferenceActivePhysicalStep.dispatch record.input).selection = some v := by
    change (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some v
    rw [← hprepare]
    exact hselected
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
  have hphase := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits
    record v hdispatch
  generalize hcut : record.output.preparation.coordinator = cut at hframes hphase ⊢
  cases cut with
  | first outcome =>
      cases outcome with
      | chosen installed arm =>
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input installed.registers.payload installed.startRoundResult
            installed.registers.time installed.registers.complementWeights arm hframes.1
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              installed.registers.payload installed.startRoundResult installed.registers.time
              installed.registers.complementWeights arm hframes.1
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          exact selected_live_call_arrival record rewards selectedCall installed.registers
            installed.startRoundResult installed.registers.time arm hframes.1 rfl hshape
            hframes.2.1 hphase.1 states memories hprepare hordinary hfields
            (fun hcall hdata => (hgeometry hcall hdata).1)
      | _ => exact False.elim hphase
  | live registers owned base outcome =>
      cases outcome with
      | continuingChosen dispatched hstart continuation arm =>
          let localRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input registers.payload dispatched.startResult record.input.time
            localRegisters.complementWeights arm rfl
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              registers.payload dispatched.startResult record.input.time
              localRegisters.complementWeights arm rfl
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          exact selected_live_call_arrival record rewards selectedCall localRegisters
            dispatched.startResult record.input.time arm rfl rfl hshape hframes.1 hphase.1
            states memories hprepare hordinary hfields
            (fun hcall hdata => (hgeometry hcall hdata).1)
      | cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
          let localRegisters := ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input registers.payload dispatched.startResult record.input.time
            localRegisters.complementWeights arm rfl
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              registers.payload dispatched.startResult record.input.time
              localRegisters.complementWeights arm rfl
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          exact False.elim (hframes.1 hlive)
      | _ => exact False.elim hphase
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          have hbit := ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
            (roundRecordCode record)
            (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) record.input.time rfl
          change ReferenceCoordinatorRecorderCallTrace.live (roundRecordCode record)
              (ReferenceLiveDispatchOutputMeasurability.encodeSelection v) =
            decide (CoordinatorLocalArmChoice.assignmentIsLive
              v.view.payload v.view.cutoff record.input.time) at hbit
          rw [decide_eq_true hlive] at hbit
          rw [hphase.1] at hbit
          simp at hbit
      | laterChosen core consistent started hstart instruction hinstruction output hcons
          clockData installed arm =>
          let selectedCall := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
            record.input installed.registers.payload started instruction.time
            installed.registers.complementWeights arm hframes.1
          have hshape : record.output.preparation.coordinator.selection = some selectedCall := by
            rw [hcut]
            exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input
              installed.registers.payload started instruction.time
              installed.registers.complementWeights arm hframes.1
          have hv : v = selectedCall := Option.some.inj (hselected.symm.trans hshape)
          subst v
          exact selected_live_call_arrival record rewards selectedCall installed.registers
            started instruction.time arm hframes.1 rfl hshape hframes.2.1 hphase.1
            states memories hprepare hordinary hfields
            (fun hcall hdata => (hgeometry hcall hdata).1)
      | _ => exact False.elim hphase
  | invalidCollectionCutoff => exact False.elim hphase
  | dagger => exact False.elim hphase

end Bandits.Support.ReferenceCompleteCoordinatorDataArrival

end
