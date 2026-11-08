/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveDataOwnership

/-!
# The actual coordinator's live recording

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-396,408-423`,
`sources/zip4/manuscript/06_interruptions.tex:246-269,391-397`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The local ordinary configurations and occupied fields below concern this
round's current payload. They are not invariants of a whole execution.
Recording diagnostics survive every later service, confirmation and finish
failure. A successful gate with zero arrival is retained as such.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCoordinatorLiveRecording

open ConstructorDimensions ActiveRoundActions PublicDiscreteDraws
open ContinuousControlSlice
open ContinuousLearningRows (sliceAt)


local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Recorder output is retained even when a subsequent local operation fails.
No successful service, confirmation or FinishRound hypothesis is needed. -/
theorem livePostChoice_recording_eq_run {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ) (started : CoordinatorPhaseClock.StartRoundResult p) :
    (ReferenceActivePhysicalStep.livePostChoice prepared r q base started).recording =
      CoordinatorRecorderComplementBridge.run (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) := by
  unfold ReferenceActivePhysicalStep.livePostChoice
  split
  · rename_i hrecord
    exact hrecord.symm
  · rename_i recording hrecord
    split
    · exact hrecord.symm
    · split
      · exact hrecord.symm
      · split <;> exact hrecord.symm

/-- The checked choice supplies exactly the recorder's boundary and local
complement envelope. Its choice coordinate need not be rewritten first. -/
theorem liveRecordingInput_valid {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload started time r.complementWeights x.row) :
    CoordinatorRecorderComplementBridge.LocalInputsValid (ReferenceActivePhysicalStep.liveRecordingInput prepared r started) :=
  ⟨selection.recorderBoundaryValid, fun j =>
    ⟨selection.choiceInputsValid.anchor_le_current j,
      selection.choiceInputsValid.current_le_twice_anchor j⟩⟩

private def chosenSelection (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload started time r.complementWeights x.row)
    (htime : time = x.time) : ReferenceActivePhysicalStep.Selection x := {
  view := {
    payload := r.payload, pendingAtChoice := started.pending
    cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
    complementWeights := r.complementWeights }
  started := started, pending_eq := rfl, cutoff_eq := rfl
  arm := selection.arm
  choice_eq := by simpa only [htime] using selection.armChoice_eq }

private theorem selectionAt_eq (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload started time r.complementWeights x.row)
    (htime : time = x.time) :
    ReferenceActivePhysicalStep.selectionAt x r.payload started time r.complementWeights selection =
      some (chosenSelection x r started time selection htime) := by
  simp only [ReferenceActivePhysicalStep.selectionAt, dite_eq_left htime, chosenSelection]

private theorem selected_dataAction (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload started time r.complementWeights x.row)
    (htime : time = x.time)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some (chosenSelection x r started time selection htime))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time)
    (hdata : CoordinatorRecorderComplementBridge.selectedSlot (ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) r started) = dataSlot) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) r started
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
      (liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x) r started time selection)
    SnapshotRecordingKernel.dataAction p (.live r.payload.assignment
      { missing := started.pending, status := fun i => (states i).status })
      rate.eta.val v.eta_pos v.eta_source_cap r.payload.anchor
      (CoordinatorRecorderComplementBridge.extendedCurrentWeights I) v.anchor_pos v.current_pos
      v.anchor_le_current v.current_le_twice_anchor
      (sliceAt x.time x.row.2) (coordinator p.two_le_m) = I.ownArm := by
  dsimp only
  let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) r started
  have hv := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
    (liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x) r started time selection)
  have hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time r.complementWeights := by
    simpa only [htime] using selection.choiceInputsValid
  have harm : I.ownArm = selection.arm := by
    change (ReferenceActivePhysicalStep.prepare x).coordinator.arm = selection.arm
    rw [ReferenceActivePhysicalStep.DispatchCut.arm, hselected]
    rfl
  have hslot : slotDraw (x.row.2 x.time).1 = dataSlot := hdata
  by_cases hempty : started.pending = ∅
  · have hc := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_live_empty r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time r.complementWeights (x.row.2 x.time) hchoice hlive hempty
    have ha : selection.arm = (CoordinatorLocalArmChoice.localFastDraw r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time r.complementWeights hchoice (x.row.2 x.time)).1 :=
      Option.some.inj ((chosenSelection x r started time selection htime).choice_eq.symm.trans hc)
    have hrestrict : r.complementWeights = fun j => CoordinatorRecorderComplementBridge.extendedCurrentWeights I j.1 := by
      funext j
      exact (CoordinatorRecorderComplementBridge.extendedCurrentWeights_eq_complement I j).symm
    have hdraw := CoordinatorLocalArmChoice.localFastDraw_eq_canonical r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time r.complementWeights hchoice (CoordinatorRecorderComplementBridge.extendedCurrentWeights I)
      hv.current_pos hv.anchor_le_current hv.current_le_twice_anchor hrestrict (x.row.2 x.time)
    rw [harm, ha, hdraw]
    dsimp only [SnapshotRecordingKernel.dataAction, PublicDiscreteDraws.followerCount]
    rw [dite_eq_left rfl]
    split
    · rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload]
      rfl
    · contradiction
  · have hn : ¬ (CoordinatorLocalArmChoice.assignmentIsLive r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time ∧
        started.pending = ∅) := fun h => hempty h.2
    have hc := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_data r.payload started.pending
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      x.time r.complementWeights (x.row.2 x.time) hchoice hn hslot
    have ha : selection.arm = pilotDraw (K_pos p) (coordinator p.two_le_m)
        (x.row.2 x.time).1 :=
      Option.some.inj ((chosenSelection x r started time selection htime).choice_eq.symm.trans hc)
    rw [harm, ha]
    dsimp only [SnapshotRecordingKernel.dataAction, PublicDiscreteDraws.followerCount]
    rw [dite_eq_left rfl]
    split
    · contradiction
    · rfl

private theorem identify (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload started time r.complementWeights x.row)
    (htime : time = x.time)
    (hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some (chosenSelection x r started time selection htime))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) r started
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
      (liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x) r started time selection)
    let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment
      { missing := started.pending, status := fun i => (states i).status }
      (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
    ∃ out, CoordinatorRecorderComplementBridge.run I = some out ∧ out.gateArm = E ∧
      out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)) E := by
  dsimp only
  let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) r started
  let valid := liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x) r started time selection
  let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I valid
  let snap : Snapshot r.payload.assignment :=
    { missing := started.pending, status := fun i => (states i).status }
  let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment snap
    (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
  change ∃ out, CoordinatorRecorderComplementBridge.run I = some out ∧ out.gateArm = E ∧
    out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)) E
  have hzero (hrun : CoordinatorRecorderComplementBridge.run I = some (CoordinatorRecordingOperation.zeroOutput p)) (he : E = none) :
      ∃ out, CoordinatorRecorderComplementBridge.run I = some out ∧ out.gateArm = E ∧ out.rawArrival =
        SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
          (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)) E := by
    exact ⟨CoordinatorRecordingOperation.zeroOutput p, hrun, he.symm, by rw [he]; rfl⟩
  by_cases hdata : CoordinatorRecorderComplementBridge.selectedSlot I = dataSlot
  · by_cases hsource : CoordinatorRecorderComplementBridge.selectedRecorder I = coordinator p.two_le_m
    · by_cases hfrozen : CoordinatorRecorderComplementBridge.isFrozen I
      · apply hzero (CoordinatorRecorderComplementBridge.run_zero_of_frozen I valid hdata hsource hfrozen)
        simp only [E, CoordinatorRecordingOperation.liveCoordinatorSourceMapPart,
          show decide (¬ CoordinatorRecorderComplementBridge.isFrozen I) = false from
            decide_eq_false (not_not.mpr hfrozen),
          SnapshotRecordingKernel.recordingMap_disabled, ite_self]
      · have ha := selected_dataAction x r started time selection htime hselected states hlive hdata
        have ht := CoordinatorRecordingOperation.liveThreshold_eq_snapshot (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment
          (decide (started.pending = ∅)) snap rfl (by
            change (started.pending = ∅ ↔ decide (started.pending = ∅) = true)
            exact ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩)
        have ho : SnapshotRecordingKernel.owns p (.live r.payload.assignment snap)
            (coordinator p.two_le_m) I.ownArm ↔ CoordinatorRecorderComplementBridge.ownsArm I := by
          dsimp only [SnapshotRecordingKernel.owns]
          rw [dite_eq_left rfl]
          rfl
        have hmap : E = if CoordinatorRecorderComplementBridge.ownsArm I ∧
            CoordinatorRecorderComplementBridge.ownMaskPasses I ∧
            CoordinatorRecorderComplementBridge.thinScalar I ≤ CoordinatorRecorderComplementBridge.threshold I valid
            then some I.ownArm else none := by
          have hd : CanonicalRecordingSlice.slotFromScalar (coordinate Label.slot
              (sliceAt (CoordinatorRecorderComplementBridge.recorderInput I).time
                (CoordinatorRecorderComplementBridge.recorderInput I).row.2)) = dataSlot := hdata
          have hs : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m (coordinate Label.rec
              (sliceAt (CoordinatorRecorderComplementBridge.recorderInput I).time
                (CoordinatorRecorderComplementBridge.recorderInput I).row.2)) = coordinator p.two_le_m := hsource
          have ha' : SnapshotRecordingKernel.dataAction p (.live r.payload.assignment snap)
              (CoordinatorRecorderComplementBridge.recorderInput I).eta v.eta_pos v.eta_source_cap
              (CoordinatorRecorderComplementBridge.recorderInput I).anchor
              (CoordinatorRecorderComplementBridge.recorderInput I).currentWeights
              v.anchor_pos v.current_pos v.anchor_le_current v.current_le_twice_anchor
              (sliceAt (CoordinatorRecorderComplementBridge.recorderInput I).time
                (CoordinatorRecorderComplementBridge.recorderInput I).row.2)
              (coordinator p.two_le_m) = I.ownArm := ha
          have ht' : SnapshotRecordingKernel.thinningThreshold p (.live r.payload.assignment snap)
              (CoordinatorRecorderComplementBridge.recorderInput I).eta v.eta_pos v.eta_source_cap
              (CoordinatorRecorderComplementBridge.recorderInput I).anchor
              (CoordinatorRecorderComplementBridge.recorderInput I).currentWeights
              v.anchor_pos v.current_pos v.anchor_le_current v.current_le_twice_anchor
              (coordinator p.two_le_m) I.ownArm = CoordinatorRecorderComplementBridge.threshold I valid := ht.symm
          simp only [E, CoordinatorRecordingOperation.liveCoordinatorSourceMapPart,
            show CoordinatorRecordingOperation.selectedRecorder (CoordinatorRecorderComplementBridge.recorderInput I) =
              coordinator p.two_le_m from hsource, ite_true]
          unfold SnapshotRecordingKernel.recordingMap
          simp only [show decide (¬ CoordinatorRecorderComplementBridge.isFrozen I) = true from
            decide_eq_true hfrozen, eq_self, hd, hs, ha', ho, ht', dite_eq_ite]
          change (if CoordinatorRecorderComplementBridge.ownsArm I then
            if CoordinatorRecorderComplementBridge.ownMaskPasses I then
              if CoordinatorRecorderComplementBridge.thinScalar I ≤ CoordinatorRecorderComplementBridge.threshold I valid
                then some I.ownArm else none else none else none) = _
          by_cases hown : CoordinatorRecorderComplementBridge.ownsArm I
          · by_cases hm : CoordinatorRecorderComplementBridge.ownMaskPasses I
            · by_cases hth : CoordinatorRecorderComplementBridge.thinScalar I ≤ CoordinatorRecorderComplementBridge.threshold I valid
              · simp only [hown, hm, hth, and_self, ite_true]
              · simp only [hown, hm, hth, and_false, ite_true, ite_false]
            · simp only [hown, hm, false_and, and_false, ite_true, ite_false]
          · simp only [hown, false_and, ite_false]
        by_cases howns : CoordinatorRecorderComplementBridge.ownsArm I
        · by_cases hmask : CoordinatorRecorderComplementBridge.ownMaskPasses I
          · by_cases hthin : CoordinatorRecorderComplementBridge.thinScalar I ≤ CoordinatorRecorderComplementBridge.threshold I valid
            · obtain ⟨out, hout, hgate, hraw⟩ := CoordinatorRecorderComplementBridge.run_gate_and_floor I valid hdata hsource
                hfrozen howns hmask hthin
              have he : E = some I.ownArm := by simp only [hmap, howns, hmask, hthin, and_self, ite_true]
              have hown : SnapshotRecordingKernel.owns p (.live r.payload.assignment
                  (ReferenceActiveDataOwnership.choiceSnapshot (chosenSelection x r started time selection htime) states))
                  (coordinator p.two_le_m) I.ownArm := by
                exact ho.mpr howns
              have feedback := ReferenceActiveDataOwnership.actual_data_owner_feedback x
                (chosenSelection x r started time selection htime) hselected states memories
                hordinary hfields hlive hdata (coordinator p.two_le_m) I.ownArm
                (ReferenceActivePhysicalStep.PreparedRound.action_coordinator (ReferenceActivePhysicalStep.prepare x)) hown hmask
              refine ⟨out, hout, hgate.trans he.symm, ?_⟩
              rw [he, hraw]
              change Nat.floor ((D p : ℝ) * rate.eta.val *
                RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                  (ReferenceActivePhysicalStep.prepare x).coordinatorObservation / _) = _
              rw [show (ReferenceActivePhysicalStep.prepare x).coordinatorObservation = x.rewards x.time I.ownArm from feedback.1]
              rfl
            · apply hzero (CoordinatorRecorderComplementBridge.run_zero_of_thinning_rejected I valid hdata hsource hfrozen howns hmask hthin)
              simp only [hmap, hthin, and_false, ite_false]
          · apply hzero (CoordinatorRecorderComplementBridge.run_zero_of_mask_rejected I valid hdata hsource hfrozen howns hmask)
            simp only [hmap, hmask, false_and, and_false, ite_false]
        · apply hzero (CoordinatorRecorderComplementBridge.run_zero_of_unowned I valid hdata hsource hfrozen howns)
          simp only [hmap, howns, false_and, ite_false]
    · apply hzero (CoordinatorRecorderComplementBridge.run_zero_of_other_source I valid hdata hsource)
      simp only [E, CoordinatorRecordingOperation.liveCoordinatorSourceMapPart, show ¬ CoordinatorRecordingOperation.selectedRecorder (CoordinatorRecorderComplementBridge.recorderInput I) =
        coordinator p.two_le_m from hsource, ite_false]
  · apply hzero (CoordinatorRecorderComplementBridge.run_zero_of_not_data I valid hdata)
    unfold E CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
    split
    · have hd : ¬ CanonicalRecordingSlice.slotFromScalar (coordinate Label.slot
          (sliceAt (CoordinatorRecorderComplementBridge.recorderInput I).time
            (CoordinatorRecorderComplementBridge.recorderInput I).row.2)) = dataSlot := hdata
      dsimp only [SnapshotRecordingKernel.recordingMap]
      split
      · rfl
      · rfl
    · rfl

private theorem computed_first_eq (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload installed.startRoundResult
      installed.registers.time installed.registers.complementWeights x.row)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .first (.chosen installed selection)) :
    CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selection := by
  have hd : ReferenceActivePhysicalStep.dispatch x = .first (.chosen installed selection) := hcut
  cases hs : x.state.coordinator with
  | first =>
      rw [ReferenceActivePhysicalStep.dispatch_first x hs] at hd
      exact ReferenceActivePhysicalStep.DispatchCut.first.inj hd
  | live r q base =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at hd
      contradiction
  | collection payload ledger saved =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at hd
      split at hd <;> contradiction
  | dagger =>
      simp only [ReferenceActivePhysicalStep.dispatch, hs] at hd
      contradiction

/-- Continuing live choice: actual checked recorder, actual stored diagnostic,
coordinator-source marker and literal reward floor agree. The ordinary and
current-payload fields are local physical data, not history assumptions. -/
theorem continuing_recording_identification (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).clockPending = .ok dispatched.startResult)
    (continuation : CoordinatorLiveChoiceRecorderStep.Continuation (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (selection : CoordinatorRoundDispatch.ArmSelection r.payload dispatched.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .live r q base
      (.continuingChosen dispatched hstart continuation selection))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u) x.time) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) (ReferenceActivePhysicalStep.liveRegistersAt r x.time) dispatched.startResult
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I (liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x)
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) dispatched.startResult x.time selection)
    let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart (CoordinatorRecorderComplementBridge.recorderInput I) v r.payload.assignment
      { missing := dispatched.startResult.pending, status := fun i => (states i).status }
      (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
    ∃ out, CoordinatorRecorderComplementBridge.run I = some out ∧ (ReferenceActivePhysicalStep.step x).coordinator.recording = some out ∧
      out.gateArm = E ∧ out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val r.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)) E := by
  dsimp only
  have hs : (ReferenceActivePhysicalStep.DispatchCut.live r q base
      (.continuingChosen dispatched hstart continuation selection)).selection =
      some (chosenSelection x (ReferenceActivePhysicalStep.liveRegistersAt r x.time) dispatched.startResult x.time selection rfl) :=
    selectionAt_eq x (ReferenceActivePhysicalStep.liveRegistersAt r x.time) dispatched.startResult x.time selection rfl
  have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some (chosenSelection x (ReferenceActivePhysicalStep.liveRegistersAt r x.time) dispatched.startResult x.time selection rfl) := by
    rw [hcut]
    exact hs
  obtain ⟨out, hout, hgate, hraw⟩ := identify x (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
    dispatched.startResult x.time selection rfl hselected states memories hordinary hfields hlive
  refine ⟨out, hout, ?_, hgate, hraw⟩
  have ho := ReferenceActivePhysicalStep.observeCoordinator_live_equation (ReferenceActivePhysicalStep.prepare x) r q base
    (.continuingChosen dispatched hstart continuation selection) hcut
  simp only [hs, Option.some_ne_none, ite_false] at ho
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some out
  rw [ho]
  exact (livePostChoice_recording_eq_run (ReferenceActivePhysicalStep.prepare x)
    (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
    (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base dispatched.startResult).trans hout

/-- First installed assignment, at the calendar coordinate derived from its
computed first-dispatch equation. No initialization or sampler law is assumed. -/
theorem first_recording_identification (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload installed.startRoundResult
      installed.registers.time installed.registers.complementWeights x.row)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .first (.chosen installed selection))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (installed.registers.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u) x.time) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) installed.registers installed.startRoundResult
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I (liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x)
      installed.registers installed.startRoundResult installed.registers.time selection)
    let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart (CoordinatorRecorderComplementBridge.recorderInput I) v installed.registers.payload.assignment
      { missing := installed.startRoundResult.pending, status := fun i => (states i).status }
      (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
    ∃ out, CoordinatorRecorderComplementBridge.run I = some out ∧ (ReferenceActivePhysicalStep.step x).coordinator.recording = some out ∧
      out.gateArm = E ∧ out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val installed.registers.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)) E := by
  dsimp only
  have ht := ReferenceActivePhysicalStep.dispatchFirst_chosen_time x installed selection (computed_first_eq x installed selection hcut)
  have hs : (ReferenceActivePhysicalStep.DispatchCut.first (.chosen installed selection)).selection =
      some (chosenSelection x installed.registers installed.startRoundResult installed.registers.time selection ht) :=
    selectionAt_eq x installed.registers installed.startRoundResult installed.registers.time selection ht
  have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some (chosenSelection x installed.registers installed.startRoundResult installed.registers.time selection ht) := by
    rw [hcut]
    exact hs
  obtain ⟨out, hout, hgate, hraw⟩ := identify x installed.registers installed.startRoundResult
    installed.registers.time selection ht hselected states memories hordinary hfields hlive
  refine ⟨out, hout, ?_, hgate, hraw⟩
  have ho := ReferenceActivePhysicalStep.observeCoordinator_first_equation (ReferenceActivePhysicalStep.prepare x) (.chosen installed selection) hcut
  simp only [hs, Option.some_ne_none, ite_false] at ho
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some out
  rw [ho]
  exact (livePostChoice_recording_eq_run (ReferenceActivePhysicalStep.prepare x)
    installed.registers installed.ownedRegisters installed.followerBaseScore installed.startRoundResult).trans hout

/-- Later installed assignment, retaining every original constructor proof and
using its checked StartRound instruction to derive same-round alignment. -/
theorem later_recording_identification (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (old : ReferenceActivePhysicalStep.Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid (ReferenceActivePhysicalStep.collectionInput x old ledger clock cutoff))
    (consistent : LaterAssignmentStartOperation.LocalConsistency old
      (CoordinatorRoundDispatch.collectionOperationLedger (ReferenceActivePhysicalStep.collectionInput x old ledger clock cutoff) core.payload_n_eq))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hinstruction : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart old
      (CoordinatorRoundDispatch.collectionOperationLedger (ReferenceActivePhysicalStep.collectionInput x old ledger clock cutoff) core.payload_n_eq)
      instruction x.row)
    (hcons : output.localConsistency = consistent)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload started instruction.time
      installed.registers.complementWeights x.row)
    (hcut : (ReferenceActivePhysicalStep.prepare x).coordinator = .collection old ledger clock cutoff
      (.laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed selection))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hfields : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (installed.registers.payload.downRecord i))
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u) x.time) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput (ReferenceActivePhysicalStep.prepare x) installed.registers started
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I (liveRecordingInput_valid (ReferenceActivePhysicalStep.prepare x)
      installed.registers started instruction.time selection)
    let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart (CoordinatorRecorderComplementBridge.recorderInput I) v installed.registers.payload.assignment
      { missing := started.pending, status := fun i => (states i).status }
      (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
    ∃ out, CoordinatorRecorderComplementBridge.run I = some out ∧ (ReferenceActivePhysicalStep.step x).coordinator.recording = some out ∧
      out.gateArm = E ∧ out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val installed.registers.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (x.rewards x.time j)) E := by
  dsimp only
  have ht := ReferenceActivePhysicalStep.later_instruction_time x old ledger clock cutoff core started instruction hstart hinstruction
  have hs : (ReferenceActivePhysicalStep.DispatchCut.collection old ledger clock cutoff
      (.laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed selection)).selection =
      some (chosenSelection x installed.registers started instruction.time selection ht) :=
    selectionAt_eq x installed.registers started instruction.time selection ht
  have hselected : (ReferenceActivePhysicalStep.prepare x).coordinator.selection =
      some (chosenSelection x installed.registers started instruction.time selection ht) := by
    rw [hcut]
    exact hs
  obtain ⟨out, hout, hgate, hraw⟩ := identify x installed.registers started instruction.time selection ht
    hselected states memories hordinary hfields hlive
  refine ⟨out, hout, ?_, hgate, hraw⟩
  have ho := ReferenceActivePhysicalStep.observeCoordinator_collection_equation (ReferenceActivePhysicalStep.prepare x) old ledger clock cutoff
    (.laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed selection) hcut
  simp only [hs, Option.some_ne_none, ite_false] at ho
  change (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some out
  rw [ho]
  exact (livePostChoice_recording_eq_run (ReferenceActivePhysicalStep.prepare x)
    installed.registers installed.ownedRegisters installed.retainedBaseScore started).trans hout

end Bandits.Support.ReferenceCoordinatorLiveRecording
