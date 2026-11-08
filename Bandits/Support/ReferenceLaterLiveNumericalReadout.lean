/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation

/-!
# Partial numerical readout of actual later live assignments

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/06_interruptions.tex:192-233,355-408`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-188`,
`sources/zip4/manuscript/08_main_theorem.tex:26-75`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-157`.

The option below tests actual structural branches. Absence is outside its
displayed domain; it is never a zero arrival or an operational default.
These internal results do not supply total dispatch or ordinary preparation
preservation, a queue coupling, an overflow identity, or manuscript closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.SnapshotRecordingKernel

namespace Bandits.Support.ReferenceLaterLiveNumericalReadout

local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- Constructor extraction, retaining both actual registers and actual memory. -/
def ordinaryData (c : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    Option (ReferencePrelaunchFollower.State p rate.eta × ActiveFollowerLifecycle.LocalMemory p) :=
  match c with
  | .dagger => none
  | .ordinary state memory => some (state, memory)

/-- Every actual PREPARE configuration is ordinary. No replacement family is chosen. -/
def preparedOrdinary (r : RoundRecord (p := p) (rate := rate)) : Prop :=
  ∀ i, (ordinaryData (r.output.preparation.followers.followers i).configuration).isSome = true

def preparedStates (r : RoundRecord (p := p) (rate := rate)) (h : preparedOrdinary r) :=
  fun i => ((ordinaryData (r.output.preparation.followers.followers i).configuration).get (h i)).1

def preparedMemories (r : RoundRecord (p := p) (rate := rate)) (h : preparedOrdinary r) :=
  fun i => ((ordinaryData (r.output.preparation.followers.followers i).configuration).get (h i)).2

theorem prepared_configuration (r : RoundRecord (p := p) (rate := rate))
    (h : preparedOrdinary r) (i : Fin (p.m - 1)) :
    (r.output.preparation.followers.followers i).configuration =
      .ordinary (preparedStates r h i) (preparedMemories r h i) := by
  have hi := h i
  cases hc : (r.output.preparation.followers.followers i).configuration with
  | dagger => simp [ordinaryData, hc] at hi
  | ordinary state memory => simp [preparedStates, preparedMemories, ordinaryData, hc]

/-- A retained actual arm choice already passes its literal input check. -/
theorem selection_choiceValid {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : Selection x) :
    ChoiceInputsValid selected.view.payload selected.view.cutoff x.time
      selected.view.complementWeights := by
  classical
  by_contra h
  have hc := selected.choice_eq
  simp [coordinatorArmChoice, coordinatorArmChoiceCore, h] at hc

/-- Literal later/live/ordinary structural domain. -/
def laterLiveDomain (s : ℕ) (r : RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ selected : Selection r.input,
    r.output.preparation.coordinator.selection = some selected ∧
    s < selected.view.payload.sigma.val ∧
    assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧ preparedOrdinary r

/-- Canonical numerical input computed from the actual selected payload,
pending set, complement weights, cutoff, and current prepared statuses. -/
def laterLiveReadout (s : ℕ) (r : RoundRecord (p := p) (rate := rate)) :
    Option (RecordedQueueRun.RoundInput p.K) := by
  classical
  exact match r.output.preparation.coordinator.selection with
  | none => none
  | some selected =>
      if s < selected.view.payload.sigma.val ∧
          assignmentIsLive selected.view.payload selected.view.cutoff r.input.time then
        if ho : preparedOrdinary r then
          some (ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
            selected.view.pendingAtChoice (preparedStates r ho) selected.view.complementWeights
            selected.view.cutoff (selection_choiceValid selected))
        else none
      else none

theorem laterLiveReadout_domain (s : ℕ) (r : RoundRecord (p := p) (rate := rate)) :
    (laterLiveReadout s r).isSome = true ↔ laterLiveDomain s r := by
  classical
  unfold laterLiveReadout laterLiveDomain
  cases hs : r.output.preparation.coordinator.selection with
  | none => simp
  | some selected => simp only [Option.some.injEq, exists_eq_left']
                     split_ifs <;> simp_all

theorem laterLiveReadout_eq_none_iff (s : ℕ) (r : RoundRecord (p := p) (rate := rate)) :
    laterLiveReadout s r = none ↔ ¬ laterLiveDomain s r := by
  rw [← laterLiveReadout_domain]
  cases laterLiveReadout s r <;> simp

/-- Dagger is an absent structural readout, not a numerical zero. -/
theorem laterLiveReadout_eq_none_of_dagger (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (hi : (r.output.preparation.followers.followers i).configuration = .dagger) :
    laterLiveReadout s r = none := by
  apply (laterLiveReadout_eq_none_iff s r).2
  rintro ⟨_, _, _, _, ho⟩
  have h := ho i
  simp only [hi, ordinaryData, Option.isSome_none, Bool.false_eq_true] at h

/-- Exact data on SOME, including the actual family extracted by constructors. -/
theorem laterLiveReadout_some (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K) (hc : laterLiveReadout s r = some c) :
    ∃ (selected : Selection r.input) (ho : preparedOrdinary r),
      r.output.preparation.coordinator.selection = some selected ∧
      s < selected.view.payload.sigma.val ∧
      assignmentIsLive selected.view.payload selected.view.cutoff r.input.time ∧
      c = ReferenceFirstWindowNumericalStream.sourceCell r selected.view.payload
        selected.view.pendingAtChoice (preparedStates r ho) selected.view.complementWeights
        selected.view.cutoff (selection_choiceValid selected) := by
  classical
  unfold laterLiveReadout at hc
  cases hs : r.output.preparation.coordinator.selection with
  | none => simp [hs] at hc
  | some selected =>
      simp only [hs] at hc
      split_ifs at hc with hl ho
      exact ⟨selected, ho, rfl, hl.1, hl.2, (Option.some.inj hc).symm⟩

/-- SOME is enabled and has the literal floor, including the zero/nonmarker branch. -/
theorem laterLiveReadout_numerical (s : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K) (hc : laterLiveReadout s r = some c) :
    c.enabled = true ∧ ∃ selected : Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      c.reward = (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      c.rate = selected.view.payload.rate ∧
      ∀ a, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a =
        if c.recordedArm = some a then
          Nat.floor ((D p : ℝ) * rate.eta.val *
            (((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) /
              selected.view.payload.rate a) else 0 := by
  classical
  obtain ⟨selected, ho, hs, _, _, heq⟩ := laterLiveReadout_some s r c hc
  subst c
  refine ⟨rfl, selected, hs, rfl, rfl, ?_⟩
  intro a
  rw [ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival]
  simp only [ReferenceFirstWindowNumericalStream.sourceCell]
  rw [rate.n_scale, mul_comm rate.eta.val (D p : ℝ)]
  split_ifs <;> simp_all

private theorem run_record_eq
    (initial : ReferenceActivePhysicalStep.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (span : start + total ≤ p.T)
    (active : allActiveAtStart initial start) (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows J rewards start total span active).records[n]'(by
      rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hn) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start n
        (by omega) active := by
  have he : total = (n + 1) + (total - (n + 1)) := by omega
  obtain ⟨suffix, hsuffix⟩ := ReferenceCollectionPhaseHistory.run_records_prefix initial rows J rewards
    start (n + 1) (total - (n + 1)) (by omega) active
  simp only [← he] at hsuffix
  simp only [hsuffix, ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
  have hlen := ReferenceActivePhysicalHorizon.run_record_count initial rows J rewards start n
    (by omega) active
  rw [List.getElem_append_left (by simp only [List.length_append, List.length_singleton, hlen]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero]

/-- Reconstruct the indexed record from the SAME original corrected launch.
No-crossing gives an empty suffix; terminal launch cannot have an index. -/
theorem source_record_prefix (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length) :
    ∃ (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h +
        (k.val + 1) ≤ p.T),
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k =
        ReferenceAssignmentPayloadChronology.actualRunRecordAt
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) k.val hspan
          (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc).activeAtStart := by
  classical
  by_cases hn : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h = none
  · have hk := k.isLt
    simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hn] at hk
  · have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h).isSome = true := by
      cases h : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h with
      | none => exact False.elim (hn h)
      | some active => rfl
    have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mp hsome
    let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hc
    have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch rate source rewards
      C_star C_h (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState rate source rewards C_star C_h hc)
    have hk : k.val < p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
      simpa [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using k.isLt
    have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T rate source rewards C_star C_h
    refine ⟨hc, by omega, ?_⟩
    simp only [List.get_eq_getElem]
    simpa only [hrecords] using run_record_eq
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hc)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (by omega) seed.activeAtStart k.val hk

private theorem record_preparation (r : RoundRecord (p := p) (rate := rate)) :
    r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
  rw [r.output_eq]
  rfl

private theorem current_fields
    (initial : ReferenceActivePhysicalStep.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start n : ℕ) (span : start + (n + 1) ≤ p.T)
    (seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed initial start)
    (selected : Selection (ReferenceContinuingDataCandidateLogging.candidateInput
      initial rows J rewards start n span seed.activeAtStart))
    (hs : (ReferenceActivePhysicalStep.prepare
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards start n span
        seed.activeAtStart)).coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards start n span
        seed.activeAtStart)).followers.followers i).configuration = .ordinary (states i) (memories i)) :
    ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i) := by
  have hseed : ∀ i s memory, initial.followers i = .ordinary s memory → s.status = .unoccupied := by
    intro i s memory h
    have he := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj ((seed.configuration i).symm.trans h)
    simpa [← he.1] using seed.unoccupied i
  let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start n span seed.activeAtStart
  have hr : r ∈ (ReferenceActivePhysicalHorizon.run initial rows J rewards start (n + 1) span
      seed.activeAtStart).records := by
    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
    exact List.mem_append_right _ (by simp [r])
  have hf := (ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history initial rows J rewards
    start (n + 1) span seed.activeAtStart seed.coordinatorFirst hseed (n + 1) le_rfl).2 r hr selected hs
  intro i hi
  have hfi := hf.2.1 i
  change ReferenceActiveDataOwnership.occupiedFields selected.view.payload i
    ((ReferenceActivePhysicalStep.prepare (ReferenceContinuingDataCandidateLogging.candidateInput
      initial rows J rewards start n span seed.activeAtStart)).followers.followers i).configuration at hfi
  rw [ho i] at hfi
  exact hfi hi

private theorem sourcePart_normalize
    (record : RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (arm : CoordinatorRoundDispatch.ArmSelection registers.payload started time
      registers.complementWeights record.input.row)
    (htime : time = record.input.time)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hgrid : record.input.time.val + 1 < started.clock.g) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation registers started
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
      (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid record.output.preparation
        registers started time arm)
    CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
        (CoordinatorRecorderComplementBridge.recorderInput I) v registers.payload.assignment
        { missing := started.pending, status := fun i => (states i).status }
        (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I)) =
      if recorderSourceFromScalar p.two_le_m (coordinate Label.rec (record.input.row.2 record.input.time).1) =
          coordinator p.two_le_m then
        ReferenceFirstWindowNumericalStream.sourceArm record registers.payload started.pending states
          registers.complementWeights (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          (by simpa [htime] using arm.choiceInputsValid)
      else none := by
  classical
  dsimp only
  have henabled : decide (¬ CoordinatorRecorderComplementBridge.isFrozen
      (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation registers started)) = true := by
    apply decide_eq_true
    intro hf
    have hge : record.input.time.val + 1 ≥ started.clock.g := hf.2
    omega
  rw [henabled]
  rfl

private theorem selected_live_phase_bits
    (record : RoundRecord (p := p) (rate := rate)) (selected : Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected)
    (hlive : assignmentIsLive selected.view.payload selected.view.cutoff record.input.time) :
    ReferenceCoordinatorRecorderCallTrace.live (ReferenceActiveHorizonMeasurability.roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true ∧
      ReferenceCoordinatorRecorderCallTrace.enabled (ReferenceActiveHorizonMeasurability.roundRecordCode record)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
  have hcoord : record.output.preparation.coordinator = dispatch record.input :=
    (congrArg PreparedRound.coordinator (record_preparation record)).trans
      (ReferenceActivePhysicalStep.prepare record.input).coordinator_eq
  have hsD : (dispatch record.input).selection = some selected := by rw [← hcoord]; exact hs
  have hl : ReferenceCoordinatorRecorderCallTrace.live (ReferenceActiveHorizonMeasurability.roundRecordCode record)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
    rw [ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive _ _ record.input.time rfl]
    exact decide_eq_true hlive
  have hphase := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits record selected hsD
  generalize he : record.output.preparation.coordinator = cut at hphase
  cases cut with
  | first outcome => cases outcome <;> first | exact hphase | exact False.elim hphase
  | live registers owned base outcome =>
      cases outcome <;> first
      | exact hphase
      | exact False.elim hphase
      | exact False.elim (Bool.noConfusion (hphase.1.symm.trans hl))
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> first
      | exact hphase
      | exact False.elim hphase
      | exact False.elim (Bool.noConfusion (hphase.1.symm.trans hl))
  | invalidCollectionCutoff => exact False.elim hphase
  | dagger => exact False.elim hphase

private theorem branch_recorder
    (record : RoundRecord (p := p) (rate := rate)) (selected : Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, (record.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (selected.view.payload.downRecord i))
    (hlive : assignmentIsLive selected.view.payload selected.view.cutoff record.input.time) :
    ∃ out : CoordinatorRecordingOperation.Output p,
      record.output.coordinator.recording = some out ∧
      out.gateArm = (if recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec (record.input.row.2 record.input.time).1) = coordinator p.two_le_m then
        ReferenceFirstWindowNumericalStream.sourceArm record selected.view.payload
          selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
          (selection_choiceValid selected) else none) ∧
      out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val selected.view.payload.anchor
        (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
          (record.input.rewards record.input.time j)) out.gateArm := by
  classical
  have hp := record_preparation record
  have hoi : ∀ i, ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
      .ordinary (states i) (memories i) := by simpa only [← hp] using ho
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
  generalize he : record.output.preparation.coordinator = cut at hselected hframes
  cases cut with
  | first outcome =>
      cases outcome <;> try cases hselected
      rename_i installed arm
      have hs : selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm record.input
          installed.registers.payload installed.startRoundResult installed.registers.time
          installed.registers.complementWeights arm hframes.1 := by
        change selectionAt _ _ _ _ _ _ = some selected at hselected
        rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input installed.registers.payload
          installed.startRoundResult installed.registers.time installed.registers.complementWeights arm hframes.1] at hselected
        exact (Option.some.inj hselected).symm
      subst selected
      obtain ⟨out, _, hout, hgate, hraw⟩ := ReferenceCoordinatorLiveRecording.first_recording_identification
        record.input installed arm (by simpa only [← hp] using he) states memories hoi hf hlive
      have hn := sourcePart_normalize record installed.registers installed.startRoundResult
        installed.registers.time arm hframes.1 states hframes.2.2
      rw [← hp] at hgate hraw
      refine ⟨out, ?_, hgate.trans hn, ?_⟩
      · simpa only [record.output_eq] using hout
      · simpa only [← hgate, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using hraw
  | live registers owned base outcome =>
      cases outcome <;> try cases hselected
      case continuingChosen dispatched hstart continuation arm =>
        have hs : selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm record.input
            registers.payload dispatched.startResult record.input.time
            (liveRegistersAt registers record.input.time).complementWeights arm rfl := by
          change selectionAt _ _ _ _ _ _ = some selected at hselected
          rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input registers.payload
            dispatched.startResult record.input.time (liveRegistersAt registers record.input.time).complementWeights arm rfl] at hselected
          exact (Option.some.inj hselected).symm
        subst selected
        obtain ⟨out, _, hout, hgate, hraw⟩ := ReferenceCoordinatorLiveRecording.continuing_recording_identification
          record.input registers owned base dispatched hstart continuation arm
          (by simpa only [← hp] using he) states memories hoi hf hlive
        have hn := sourcePart_normalize record (liveRegistersAt registers record.input.time)
          dispatched.startResult record.input.time arm rfl states hframes.2
        rw [← hp] at hgate hraw
        refine ⟨out, ?_, hgate.trans hn, ?_⟩
        · simpa only [record.output_eq] using hout
        · simpa only [← hgate, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using hraw
      case cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
        change selectionAt _ _ _ _ _ _ = some selected at hselected
        rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input registers.payload
            dispatched.startResult record.input.time (liveRegistersAt registers record.input.time).complementWeights arm rfl] at hselected
        cases hselected
        exact False.elim (hframes.1 hlive)
  | collection old ledger clock cutoff outcome =>
      cases outcome <;> try cases hselected
      case continuing.refl =>
        exact False.elim (hframes.1 hlive)
      case laterChosen core consistent started hstart instruction hinstruction output hcons clockData installed arm =>
        have hs : selected = ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm record.input
            installed.registers.payload started instruction.time installed.registers.complementWeights arm
            hframes.1 := by
          change selectionAt _ _ _ _ _ _ = some selected at hselected
          rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input installed.registers.payload
            started instruction.time installed.registers.complementWeights arm hframes.1] at hselected
          exact (Option.some.inj hselected).symm
        subst selected
        obtain ⟨out, _, hout, hgate, hraw⟩ := ReferenceCoordinatorLiveRecording.later_recording_identification
          record.input old ledger clock cutoff core consistent started hstart instruction hinstruction
          output hcons clockData installed arm (by simpa only [← hp] using he) states memories hoi hf hlive
        have hn := sourcePart_normalize record installed.registers started instruction.time arm
          hframes.1 states hframes.2.2
        rw [← hp] at hgate hraw
        refine ⟨out, ?_, hgate.trans hn, ?_⟩
        · simpa only [record.output_eq] using hout
        · simpa only [← hgate, ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm] using hraw
  | invalidCollectionCutoff => cases hselected
  | dagger => cases hselected

private def cellFromRecorder
    (record : RoundRecord (p := p) (rate := rate)) (selected : Selection record.input)
    (hs : record.output.preparation.coordinator.selection = some selected)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, (record.output.preparation.followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hlive : assignmentIsLive selected.view.payload selected.view.cutoff record.input.time)
    (hdata : ReferenceFirstWindowRecordingTruth.actual_window_follower_data_claim
      record selected states record.input.rewards)
    (out : CoordinatorRecordingOperation.Output p)
    (hout : record.output.coordinator.recording = some out)
    (hraw : out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val selected.view.payload.anchor
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.input.rewards record.input.time j)) out.gateArm) :
    ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record where
  states := states
  memories := memories
  ordinary := ho
  selected := selected
  selection_actual := hs
  assignment_live := hlive
  choiceInputsValid := selection_choiceValid selected
  input := ReferenceFirstWindowNumericalStream.sourceCell record selected.view.payload
    selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
    (selection_choiceValid selected)
  input_eq := rfl
  enabled := rfl
  recordedArm_eq := rfl
  quantizedArrival_eq := ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival record
    selected.view.payload selected.view.pendingAtChoice states selected.view.complementWeights
    selected.view.cutoff (selection_choiceValid selected)
  coordinatorProjection := by
    refine ⟨out, out.gateArm, hout, rfl, hraw, ?_⟩
    intro j
    unfold ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
    rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
    change (record.output.coordinator.recording).map _ = _
    simp only [hout, Option.map_some]
  followerDataClaim := hdata
  followerRawArrivalGate := fun i h => ActiveFollowerQueueOperation.rawArrival_eq_floor_of_gate
    rate.eta i record.input.row record.input.time (selected.view.payload.downRecord i) _ h
  followerRawArrivalNoGate := by
    intro i h
    simp [ActiveFollowerQueueOperation.rawArrival, h]

private theorem candidate_actual
    (initial : ReferenceActivePhysicalStep.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start n : ℕ) (span : start + (n + 1) ≤ p.T) (active : allActiveAtStart initial start) :
    let x := ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards start n span active
    ReferenceContinuingDataCandidateLogging.candidateRecord initial rows J rewards start n span active
      (x.row.2 x.time) =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start n span active := by
  exact congrArg (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
    (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ : RoundRecord))
      (ReferenceContinuingLiveSlicePreparation.inputAtControl_actual _)

private theorem current_logging
    (initial : ReferenceActivePhysicalStep.State p rate) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start n : ℕ) (span : start + (n + 1) ≤ p.T)
    (seed : ReferenceFirstWindowNumericalStream.FirstLiveSeed initial start)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare
      (ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards start n span
        seed.activeAtStart)).followers.followers i).configuration = .ordinary (states i) (memories i))
    (i : Fin (p.m - 1)) (hu : (states i).status = .unoccupied)
    (hd : slotDraw ((ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards
      start n span seed.activeAtStart).row.2
        (ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards
          start n span seed.activeAtStart).time).1 = dataSlot) :
    let r := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows J rewards start n span seed.activeAtStart
    ∃ logged,
      ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i) r.input.time
        (r.output.ownEntries (followerPlayer p.two_le_m i)) (states i) = .ok logged ∧
      (r.output.followers i).downInput = some logged ∧
      logged.buffer = (states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i r := by
  let x := ReferenceContinuingDataCandidateLogging.candidateInput initial rows J rewards start n span seed.activeAtStart
  have hg := ReferenceContinuingDataCandidateLogging.continuing_data_candidate_logging initial rows J rewards
    start n span seed.activeAtStart i (seed.followers i) (seed.memory i) (seed.configuration i)
    (seed.bufferValid i) (seed.chronologicalBuffer i) (seed.bufferStamps i) states memories ho hu
  obtain ⟨logged, hcheck, hdown, happend, _⟩ := hg.2.2.2.2 (x.row.2 x.time) hd
  rw [candidate_actual] at hcheck hdown happend
  exact ⟨logged, hcheck, hdown, happend⟩

private theorem unoccupied_current_marker
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hu : (cell.states i).status = .unoccupied)
    (hsourceActual : recorderSourceFromScalar p.two_le_m
      (coordinate Label.rec (record.input.row.2 record.input.time).1) = followerPlayer p.two_le_m i)
    (hlogging : ∃ logged,
      ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i) record.input.time
        (record.output.ownEntries (followerPlayer p.two_le_m i)) (cell.states i) = .ok logged ∧
      (record.output.followers i).downInput = some logged ∧
      logged.buffer = (cell.states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i record) :
    ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record cell.selected.view.payload i
        (cell.states i) = cell.input.recordedArm := by
  classical
  let P := cell.selected.view.payload
  let own := record.output.ownEntries (followerPlayer p.two_le_m i)
  have hown : own.1 = record.output.preparation.arms.actions (followerPlayer p.two_le_m i) :=
    by simpa only [own, record.output_eq, ReferenceActivePhysicalStep.step] using (congrArg Prod.fst
      (ReferenceActivePhysicalStep.step_own_entry record.input (followerPlayer p.two_le_m i)))
  let emission := ReferenceFollowerBufferProvenance.logEmission i record
  let tests := SparseCalendarReplay.loggingTestsPass
    (ReferencePrelaunchFollower.loggingRound i record.input.row (record.input.state.activations i) record.input.time own)
  obtain ⟨logged, hcheck, hdown, happend⟩ := hlogging
  have hemission : emission = ReferencePrelaunchFollower.logAt i record.input.row
      (record.input.state.activations i) record.input.time own := by
    exact ReferenceFirstLiveUnoccupiedEmission.logEmission_eq_logAt_unoccupied record cell i hu
  have hsource := ReferenceFirstLiveUnoccupiedEmission.sourceArm_eq_some_iff_unoccupied record cell i hu
  have hiff : ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record P i (cell.states i) =
      some (P.assignment.assigned i) ↔ cell.input.recordedArm = some (P.assignment.assigned i) := by
    rw [cell.recordedArm_eq, hsource]
    have hpilot := fun hd => (cell.followerDataClaim i hd).1
    have hactive := record.input.active i
    have hdyadic := P.dyadicRate_eq_rate (P.assignment.assigned i)
    have hthin : ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold P (P.assignment.assigned i) =
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * P.rate (P.assignment.assigned i)) /
          CanonicalRecordingSlice.recordingZeta p.m p.K := by
      rw [ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold,
        CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
      exact congrArg (fun z : ℝ => (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) * z) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)) hdyadic
    by_cases ht : tests
    · have he : ReferenceFollowerBufferProvenance.logEmission i record = [SparseCalendarReplay.recordAt (record.input.time.val + 1)
          (ReferencePrelaunchFollower.loggingRound i record.input.row
            (record.input.state.activations i) record.input.time own)] := by
        change emission = _
        rw [hemission]
        exact ActiveFollowerLogging.logAt_eq_singleton_of_tests _ _ _ _ _ ht
      have htt := (ReferencePrelaunchFollower.loggingTestsPass_iff i record.input.row
        (record.input.state.activations i) record.input.time own).mp ht
      have ha : own.1 = pilotDraw (K_pos p) (followerPlayer p.two_le_m i)
          (record.input.row.2 record.input.time).1 := by
        rw [hown]
        simpa only [hu, ite_eq_left] using hpilot htt.2.1
      simp only [ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker, hdown,
        hcheck, happend, true_and]
      simp only [he, List.mem_singleton, exists_eq_left, List.mem_append,
        List.mem_singleton, or_true, true_and]
      simp [SparseCalendarReplay.recordAt, ReferencePrelaunchFollower.loggingRound, hthin,
        ReferenceFirstLaunchNumericalCell.firstFollowerEvent, htt.2.1, htt.2.2.1, ← ha,
        own, P, eq_comm]
      intro hpa _ player hp
      have hmask := htt.2.2.2 player hp
      change pilotDraw (K_pos p) player (record.input.row.2 record.input.time).1 ≠ own.1 at hmask
      rw [hpa] at hmask
      exact Ne.symm hmask
    · have he : ReferenceFollowerBufferProvenance.logEmission i record = [] := by
        change emission = _
        rw [hemission]
        exact ActiveFollowerLogging.logAt_eq_nil_of_not_tests _ _ _ _ _ ht
      have hn : ¬ (recorderSourceDraw p.two_le_m p.m_lt_K (record.input.row.2 record.input.time).1 =
          followerPlayer p.two_le_m i ∧ ReferenceFirstLaunchNumericalCell.firstFollowerEvent i
            record.input.row record.input.time (P.assignment.assigned i) (P.rate (P.assignment.assigned i))) := by
        rintro ⟨hs, hd, ha, hm, _⟩
        apply ht
        apply (ReferencePrelaunchFollower.loggingTestsPass_iff i record.input.row
          (record.input.state.activations i) record.input.time own).mpr
        have hp : own.1 = P.assignment.assigned i := by
          rw [hown]
          simpa only [hu, ite_eq_left, ha] using hpilot hd
        exact ⟨hactive, hd, hs, by simpa [hp] using hm⟩
      simp [ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker, hdown,
        hcheck, happend, he]
      exact fun hs hevent => hn ⟨hs, hevent⟩
  have hcanonRange : ∀ a, cell.input.recordedArm = some a → a = P.assignment.assigned i := by
    intro a hm
    rw [cell.recordedArm_eq] at hm
    rcases (recordingMap_some_iff p _ _ _ _ _ _ _ _ _ _ _ a).mp hm with ⟨_, _, howns, _, _⟩
    have hn := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
    have hi := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hn
    simpa only [owns, hsourceActual, dite_eq_right hn, hi, P] using howns
  have hphysicalRange : ∀ a,
      ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record P i (cell.states i) = some a →
        a = P.assignment.assigned i := by
    intro a ha
    simp only [ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker, hdown] at ha
    split_ifs at ha
    simp_all
  cases hp : ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record P i (cell.states i) with
  | none =>
      cases hm : cell.input.recordedArm with
      | none => rfl
      | some a =>
          have ha := hcanonRange a hm
          subst a
          have := hiff.mpr hm
          simp [hp] at this
  | some a =>
      have ha := hphysicalRange a hp
      subst a
      exact (hiff.mp hp).symm

private theorem occupied_arrival
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (i : Fin (p.m - 1)) (hu : (cell.states i).status ≠ .unoccupied) :
    (cell.input.recordedArm = some (cell.selected.view.payload.assignment.assigned i) ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time
        (cell.selected.view.payload.downRecord i)) ∧
    ActiveFollowerQueueOperation.rawArrival rate.eta i record.input.row record.input.time
        (cell.selected.view.payload.downRecord i)
        (record.output.ownEntries (followerPlayer p.two_le_m i)).2 =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input (cell.selected.view.payload.assignment.assigned i) := by
  classical
  let P := cell.selected.view.payload
  let snapshot := ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states
  let W := ReferenceFirstWindowNumericalStream.sourceWeights P cell.selected.view.complementWeights
  have hp := ReferenceFirstWindowNumericalStream.sourceWeights_pos P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hl := ReferenceFirstWindowNumericalStream.sourceWeights_lower P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hh := ReferenceFirstWindowNumericalStream.sourceWeights_upper P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hn := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hi := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hn
  have hstatus : snapshot.status i ≠ .unoccupied := hu
  have howns : owns p (.live P.assignment snapshot) (followerPlayer p.two_le_m i) (P.assignment.assigned i) := by
    simp only [owns, dite_eq_right hn, hi]
  have hanchorUpper : ∀ j, P.anchor j ≤ 2 * P.anchor j := by
    intro j
    rw [two_mul]
    exact le_add_of_nonneg_right (le_of_lt (P.anchor_pos j))
  have hW := recordingMap_fixed_event_eq p (.live P.assignment snapshot) rate.eta.val rate.eta.property
    rate.sourceCap P.anchor W P.anchor_pos hp hl hh (followerPlayer p.two_le_m i)
    (P.assignment.assigned i) howns
    (by intro z; simp [dataAction, hn, hi, hstatus])
    (by simp [actionProbability, hn, hi, hstatus])
  have hA := recordingMap_fixed_event_eq p (.live P.assignment snapshot) rate.eta.val rate.eta.property
    rate.sourceCap P.anchor P.anchor P.anchor_pos P.anchor_pos (fun _ => le_rfl) hanchorUpper
    (followerPlayer p.two_le_m i) (P.assignment.assigned i) howns
    (by intro z; simp [dataAction, hn, hi, hstatus])
    (by simp [actionProbability, hn, hi, hstatus])
  have hsame := Set.ext_iff.mp (hW.trans hA.symm) (record.input.row.2 record.input.time).1
  have hoccupied : (cell.states i).status.occupied := by
    cases h : (cell.states i).status <;> simp_all [FollowerStatus.occupied]
  have hv := ReferenceFollowerOccupiedRecorderEvent.occupiedGate_eq_canonicalRecordingMap
    P snapshot i record.input.row record.input.time (cell.states i) rfl hoccupied
  have hmap : cell.input.recordedArm = some (P.assignment.assigned i) ↔
      ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time (P.downRecord i) := by
    rw [cell.recordedArm_eq]
    simpa only [ReferenceFirstWindowNumericalStream.sourceArm, snapshot,
      ReferenceActiveDataOwnership.choiceSnapshot, cell.selected.pending_eq, W, P, Set.mem_ofPred_eq] using hsame.trans hv.symm
  refine ⟨hmap, ?_⟩
  rw [ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula, cell.quantizedArrival_eq]
  by_cases hg : ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time (P.downRecord i)
  · have hm := hmap.mpr hg
    rw [cell.recordedArm_eq] at hm
    rw [ite_eq_left hg, ite_eq_left hm]
    have hmask := hg.2.2.1
    rw [ReferenceActiveDataOwnership.downRecord_arm] at hmask
    have hy := ((cell.followerDataClaim i hg.1).2 hu hmask).2
    change (record.output.ownEntries (followerPlayer p.two_le_m i)).2.val.val = _ at hy
    unfold ActiveFollowerQueueOperation.sourceArrivalFloor
    rw [cell.selected.view.payload.downRecord_rate i, hy, rate.n_scale,
      cell.selected.view.payload.rate_eq_canonical]
    congr 1
    ring
  · have hm : ReferenceFirstWindowNumericalStream.sourceArm record P cell.selected.view.pendingAtChoice
        cell.states cell.selected.view.complementWeights cell.selected.view.cutoff cell.choiceInputsValid ≠
        some (P.assignment.assigned i) := by
      intro hm
      exact hg (hmap.mp (cell.recordedArm_eq.trans hm))
    rw [ite_eq_right hg, ite_eq_right hm]

private theorem marker_from_cell
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hf : ∀ i, (cell.states i).status ≠ .unoccupied →
      (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i))
    (out : CoordinatorRecordingOperation.Output p)
    (hout : record.output.coordinator.recording = some out)
    (hgate : out.gateArm = if recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (record.input.row.2 record.input.time).1) = coordinator p.two_le_m then
      cell.input.recordedArm else none)
    (hlogging : ∀ i, (cell.states i).status = .unoccupied →
      slotDraw (record.input.row.2 record.input.time).1 = dataSlot → ∃ logged,
        ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i)) (cell.states i) = .ok logged ∧
        (record.output.followers i).downInput = some logged ∧
        logged.buffer = (cell.states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i record) :
    cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord record
      cell.selected.view.payload true := by
  classical
  let source := recorderSourceFromScalar p.two_le_m (coordinate Label.rec (record.input.row.2 record.input.time).1)
  by_cases hd : slotDraw (record.input.row.2 record.input.time).1 = dataSlot
  · simp only [ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord,
      dite_true, dite_eq_left hd]
    by_cases hc : source = coordinator p.two_le_m
    · simp only [source, hc, ite_eq_left] at hgate
      simp only [ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord,
        show recorderSourceFromScalar p.two_le_m (coordinate Label.rec (record.input.row.2 record.input.time).1) =
          coordinator p.two_le_m from hc, hout, Option.bind_some]
      exact hgate.symm
    · let i := followerIndex p.two_le_m source hc
      have hplayer : followerPlayer p.two_le_m i = source := followerPlayer_followerIndex p.two_le_m source hc
      have hphys : ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record cell.selected.view.payload source =
          if (cell.states i).status = .unoccupied then
            ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record cell.selected.view.payload i (cell.states i)
          else if ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time
              (cell.selected.view.payload.downRecord i) then
            some (cell.selected.view.payload.assignment.assigned i) else none := by
        unfold ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
        rw [dite_eq_right hc]
        dsimp only
        rw [cell.ordinary i]
        by_cases hu : (cell.states i).status = .unoccupied
        · simp only [dite_eq_left hu, ite_eq_left hu]
          rfl
        · simp only [dite_eq_right hu, ite_eq_right hu, hf i hu]
          rw [ReferenceActiveDataOwnership.downRecord_arm cell.selected.view.payload i]
          rfl
      change cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord record
        cell.selected.view.payload source
      rw [hphys]
      by_cases hu : (cell.states i).status = .unoccupied
      · rw [ite_eq_left hu]
        exact (unoccupied_current_marker record cell i hu hplayer.symm (hlogging i hu hd)).symm
      · rw [ite_eq_right hu]
        have hg := (occupied_arrival record cell i hu).1
        cases hm : cell.input.recordedArm with
        | none =>
            have hn : ¬ ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row record.input.time
                (cell.selected.view.payload.downRecord i) := by
              intro h
              have := hg.mpr h
              rw [hm] at this
              cases this
            simp only [ite_eq_right hn]
        | some a =>
            have hrange : a = cell.selected.view.payload.assignment.assigned i := by
              have hmap := hm
              rw [cell.recordedArm_eq] at hmap
              rcases (recordingMap_some_iff p _ _ _ _ _ _ _ _ _ _ _ a).mp hmap with ⟨_, _, howns, _, _⟩
              simpa only [owns, show recorderSourceFromScalar p.two_le_m
                (coordinate Label.rec (record.input.row.2 record.input.time).1) = source from rfl,
                dite_eq_right hc] using howns
            subst a
            simp only [ite_eq_left (hg.mp hm)]
  · have hm : cell.input.recordedArm = none := by
      rw [cell.recordedArm_eq]
      unfold ReferenceFirstWindowNumericalStream.sourceArm
      simp [recordingMap, hd]
    simp [ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord, hd, hm]

private theorem cell_owner_feedback
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hf : ∀ i, (cell.states i).status ≠ .unoccupied →
      (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i))
    (a : Fin p.K) (hm : cell.input.recordedArm = some a) :
    let snapshot := ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states
    ∃ owner : Fin p.m,
      owns p (.live cell.selected.view.payload.assignment snapshot) owner a ∧
      (∀ other, owns p (.live cell.selected.view.payload.assignment snapshot) other a → other = owner) ∧
      record.output.preparation.arms.actions owner = a ∧
      record.gridFeedback owner = record.input.rewards record.input.time a ∧
      (record.output.ownEntries owner).2.val.val = ((record.input.rewards record.input.time a).val : ℝ) / (D p : ℝ) := by
  classical
  let P := cell.selected.view.payload
  let snapshot := ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states
  let W := ReferenceFirstWindowNumericalStream.sourceWeights P cell.selected.view.complementWeights
  have hp := ReferenceFirstWindowNumericalStream.sourceWeights_pos P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hl := ReferenceFirstWindowNumericalStream.sourceWeights_lower P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hh := ReferenceFirstWindowNumericalStream.sourceWeights_upper P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  let source := recorderSourceFromScalar p.two_le_m (coordinate Label.rec (record.input.row.2 record.input.time).1)
  rw [cell.recordedArm_eq] at hm
  rcases (recordingMap_some_iff p _ _ _ _ _ _ _ _ _ _ _ a).mp hm with ⟨hd, ha, ho, hmask, _⟩
  have haction : record.output.preparation.arms.actions source = a := by
    by_cases hc : source = coordinator p.two_le_m
    · rw [hc]
      rw [record.output.preparation.action_coordinator, DispatchCut.arm, cell.selection_actual]
      change cell.selected.arm = a
      by_cases he : cell.selected.view.pendingAtChoice = ∅
      · have hchoice := cell.selected.choice_eq.symm.trans
          (coordinatorArmChoiceCore_live_empty P cell.selected.view.pendingAtChoice cell.selected.view.cutoff
            record.input.time cell.selected.view.complementWeights (record.input.row.2 record.input.time)
            cell.choiceInputsValid cell.assignment_live he)
        have hrestrict : cell.selected.view.complementWeights = fun j => W j.1 := by
          funext j
          dsimp only [W, ReferenceFirstWindowNumericalStream.sourceWeights]
          split_ifs with h
          · exact False.elim ((Finset.mem_sdiff.mp j.property).2 h)
          · rfl
        have hdraw := localFastDraw_eq_canonical P cell.selected.view.cutoff record.input.time
          cell.selected.view.complementWeights cell.choiceInputsValid W hp hl hh hrestrict
          (record.input.row.2 record.input.time)
        rw [Option.some.inj hchoice, hdraw]
        simp only [dataAction] at ha
        rw [CoordinatorRecorderComplementBridge.assignmentSlowSet_eq_payload cell.selected.view.payload] at ha
        simpa [snapshot, ReferenceActiveDataOwnership.choiceSnapshot,
          ← cell.selected.pending_eq, he, source, hc, P, W] using ha
      · have hchoice := cell.selected.choice_eq.symm.trans
          (coordinatorArmChoiceCore_data P cell.selected.view.pendingAtChoice cell.selected.view.cutoff
            record.input.time cell.selected.view.complementWeights (record.input.row.2 record.input.time)
            cell.choiceInputsValid (fun h => he h.2) hd)
        rw [Option.some.inj hchoice]
        simpa [dataAction, snapshot, ReferenceActiveDataOwnership.choiceSnapshot,
          ← cell.selected.pending_eq, he, source, hc] using ha
    · have hcExpr : recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec (record.input.row.2 record.input.time).1) ≠ coordinator p.two_le_m := hc
      let i : Fin (p.m - 1) := followerIndex p.two_le_m source hc
      have hplayer := followerPlayer_followerIndex p.two_le_m source hc
      rw [← hplayer]
      rw [(cell.followerDataClaim i hd).1]
      simp only [dataAction, dite_eq_right hcExpr] at ha
      change (dite ((cell.states i).status = .unoccupied)
        (fun _ => pilotDraw (K_pos p) source (record.input.row.2 record.input.time).1)
        (fun _ => P.assignment.assigned i)) = a at ha
      by_cases hu : (cell.states i).status = .unoccupied
      · rw [ite_eq_left hu, hplayer]
        exact (dite_eq_left hu).symm.trans ha
      · rw [ite_eq_right hu]
        exact (dite_eq_right hu).symm.trans ha
  have hprep := record_preparation record
  have hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some cell.selected := by
    simpa only [← hprep] using cell.selection_actual
  have hordinary : ∀ i, ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
      .ordinary (cell.states i) (cell.memories i) := by simpa only [← hprep] using cell.ordinary
  have hfeedback := ReferenceActiveDataOwnership.actual_data_owner_feedback record.input cell.selected hselected
    cell.states cell.memories hordinary hf cell.assignment_live hd source a
    (by simpa only [← hprep] using haction)
    (by simpa only [snapshot, ReferenceActiveDataOwnership.choiceSnapshot, cell.selected.pending_eq] using ho) hmask
  refine ⟨source, ?_, ?_, haction, ?_, ?_⟩
  · simpa only [snapshot, ReferenceActiveDataOwnership.choiceSnapshot, cell.selected.pending_eq] using ho
  · intro other hother
    exact owns_unique p (.live P.assignment snapshot) a other source hother
      (by simpa only [snapshot, ReferenceActiveDataOwnership.choiceSnapshot, cell.selected.pending_eq] using ho)
  · change record.output.preparation.feedback.feedback source = _
    rw [hprep]
    exact hfeedback.1
  · have hown := ReferenceActivePhysicalStep.step_own_entry record.input source
    have hobservation : (record.output.ownEntries source).2.val.val =
        ((ReferenceActivePhysicalStep.prepare record.input).feedback.observations source).val.val := by
      rw [record.output_eq, ReferenceActivePhysicalStep.step_own_entry]
      rfl
    exact hobservation.trans hfeedback.2

private theorem coordinator_arrival
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (out : CoordinatorRecordingOperation.Output p)
    (hgate : out.gateArm = if recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (record.input.row.2 record.input.time).1) = coordinator p.two_le_m then
      cell.input.recordedArm else none)
    (hraw : out.rawArrival = recordedIncrement p rate.eta.val cell.selected.view.payload.anchor
      (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        (record.input.rewards record.input.time j)) out.gateArm)
    (a : Fin p.K) (ha : a ∉ cell.selected.view.payload.slowSet.1) :
    (if out.gateArm = some a then out.rawArrival else 0) =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a := by
  classical
  rw [cell.quantizedArrival_eq]
  by_cases hm : cell.input.recordedArm = some a
  · have hsource : recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (record.input.row.2 record.input.time).1) = coordinator p.two_le_m := by
      by_contra hn
      have hmap := hm
      rw [cell.recordedArm_eq] at hmap
      rcases (recordingMap_some_iff p _ _ _ _ _ _ _ _ _ _ _ a).mp hmap with ⟨_, _, ho, _, _⟩
      simp only [owns, dite_eq_right hn] at ho
      apply ha
      rw [← cell.selected.view.payload.assignment_image, ho]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    have hg : out.gateArm = some a := by simp only [hgate, ite_eq_left hsource, hm]
    have hmap := cell.recordedArm_eq.symm.trans hm
    rw [ite_eq_left hg, ite_eq_left hmap, hraw, hg]
    simp only [recordedIncrement, RealRewardGridCount.realRewardGridValue,
      cell.selected.view.payload.rate_eq_canonical, rate.n_scale]
    congr 1
    ring
  · have hg : out.gateArm ≠ some a := by
      rw [hgate]
      split_ifs <;> simp_all
    rw [ite_eq_right hg, ite_eq_right (fun h => hm (cell.recordedArm_eq.trans h))]

private theorem unoccupied_arrival
    (record : RoundRecord (p := p) (rate := rate))
    (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell record)
    (hf : ∀ i, (cell.states i).status ≠ .unoccupied →
      (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i))
    (i : Fin (p.m - 1)) (hu : (cell.states i).status = .unoccupied) :
    ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution record cell.selected.view.payload i =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input
        (cell.selected.view.payload.assignment.assigned i) := by
  classical
  let P := cell.selected.view.payload
  let snapshot : Snapshot P.assignment :=
    { missing := cell.selected.view.pendingAtChoice, status := fun j => (cell.states j).status }
  let W := ReferenceFirstWindowNumericalStream.sourceWeights P cell.selected.view.complementWeights
  have hp := ReferenceFirstWindowNumericalStream.sourceWeights_pos P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hl := ReferenceFirstWindowNumericalStream.sourceWeights_lower P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hh := ReferenceFirstWindowNumericalStream.sourceWeights_upper P cell.selected.view.complementWeights
    cell.selected.view.cutoff record.input.time cell.choiceInputsValid
  have hs : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some cell.selected := by
    rw [← record_preparation record]
    exact cell.selection_actual
  have he := ReferenceSelectedCandidateRecorderEvent.current_selected_candidate_eq_marker record cell.selected hs
    i snapshot (cell.states i) (cell.memories i) (cell.ordinary i) hu rfl W hp hl hh
  have hemits := ReferenceFirstLiveUnoccupiedEmission.logEmission_eq_logAt_unoccupied record cell i hu
  have hcontribution : ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution record P i =
      if ReferenceFirstWindowNumericalStream.sourceArm record P cell.selected.view.pendingAtChoice cell.states
          cell.selected.view.complementWeights cell.selected.view.cutoff cell.choiceInputsValid =
            some (P.assignment.assigned i) then
        Nat.floor ((D p : ℝ) * rate.eta.val * (record.output.ownEntries (followerPlayer p.two_le_m i)).2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val P.anchor (P.assignment.assigned i)) else 0 := by
    unfold ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
    rw [hemits]
    exact he
  rw [hcontribution, cell.quantizedArrival_eq]
  by_cases hm : ReferenceFirstWindowNumericalStream.sourceArm record P cell.selected.view.pendingAtChoice cell.states
      cell.selected.view.complementWeights cell.selected.view.cutoff cell.choiceInputsValid = some (P.assignment.assigned i)
  · rw [ite_eq_left hm, ite_eq_left hm]
    have hy := ReferenceFirstLiveUnoccupiedEmission.unoccupied_feedback_of_sourceArm record cell hf i hu hm
    rw [hy.2.2, rate.n_scale, cell.selected.view.payload.rate_eq_canonical]
    congr 1
    ring
  · rw [ite_eq_right hm, ite_eq_right hm]

/-- Original-source SOME cells identify the actual recorder and all three
unique-owner raw readouts. All branch/seed/logging facts are produced here.
A raw identity makes no assertion that a checked service was applied. -/
theorem laterLiveReadout_physical
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : laterLiveReadout (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k) = some c) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      cell.input = c ∧ c.enabled = true ∧
      ReferenceCoordinatorRecorderCallTrace.live (ReferenceActiveHorizonMeasurability.roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection cell.selected) = true ∧
      ReferenceCoordinatorRecorderCallTrace.enabled (ReferenceActiveHorizonMeasurability.roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection cell.selected) = true ∧
      r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧ r.input.rewards = rewards ∧
      c.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r cell.selected.view.payload true ∧
      (∀ i, (cell.states i).status ≠ .unoccupied →
        (cell.states i).lastDown = some (cell.selected.view.payload.downRecord i)) ∧
      (∀ a, c.recordedArm = some a →
        ∃ owner : Fin p.m,
          owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a ∧
          (∀ other, owns p (.live cell.selected.view.payload.assignment
            (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) other a → other = owner) ∧
          r.output.preparation.arms.actions owner = a ∧ r.gridFeedback owner = rewards r.input.time a ∧
          (r.output.ownEntries owner).2.val.val = ((rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      (∀ i, (cell.states i).status ≠ .unoccupied →
        (c.recordedArm = some (cell.selected.view.payload.assignment.assigned i) ↔
          ActiveFollowerQueueOperation.recorderGate rate.eta i r.input.row r.input.time
            (cell.selected.view.payload.downRecord i)) ∧
        ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
            (cell.selected.view.payload.downRecord i) (r.output.ownEntries (followerPlayer p.two_le_m i)).2 =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            (cell.selected.view.payload.assignment.assigned i)) ∧
      (∀ i, (cell.states i).status = .unoccupied →
        ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c
            (cell.selected.view.payload.assignment.assigned i)) ∧
      (∀ i, (cell.states i).status = .unoccupied → slotDraw (r.input.row.2 r.input.time).1 = dataSlot →
        ∃ logged, ActiveFollowerLogging.checkedLogging i r.input.row (r.input.state.activations i) r.input.time
            (r.output.ownEntries (followerPlayer p.two_le_m i)) (cell.states i) = .ok logged ∧
          (r.output.followers i).downInput = some logged ∧
          logged.buffer = (cell.states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i r) ∧
      (∃ out, r.output.coordinator.recording = some out ∧
        ∀ a, a ∉ cell.selected.view.payload.slowSet.1 →
          ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
            some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∧
      (match r.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ _ _) => ∀ i, (cell.states i).status = .unoccupied
      | _ => True) := by
  classical
  dsimp only
  obtain ⟨hcross, span, hr⟩ := source_record_prefix rate rewards C_star C_h source k
  rw [hr] at hc ⊢
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed rate source rewards C_star C_h hcross
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val span seed.activeAtStart
  obtain ⟨selected, ho, hs, _, hlive, heq⟩ := laterLiveReadout_some start record c hc
  let states := preparedStates record ho
  let memories := preparedMemories record ho
  have hordinary := prepared_configuration record ho
  have hp := record_preparation record
  have hsInput : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    simpa only [← hp] using hs
  have hoInput : ∀ i, ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
      .ordinary (states i) (memories i) := by simpa only [← hp] using hordinary
  have hf := current_fields initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start k.val span seed selected hsInput states memories hoInput
  obtain ⟨out, hout, hgate, hraw⟩ := branch_recorder record selected hs states memories hordinary hf hlive
  have hmember : record ∈ (ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1) span seed.activeAtStart).records := by
    rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val span seed.activeAtStart]
    exact List.mem_append_right _ (by simp [record])
  have hdata := ReferenceFirstWindowRecordingTruth.actual_window_follower_data_truth initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start (k.val + 1) span seed.activeAtStart
    record hmember selected hs states memories hordinary hf hlive
  let cell := cellFromRecorder record selected hs states memories hordinary hlive hdata out hout hraw
  have hcell : cell.input = c := heq.symm
  have hlogging : ∀ i, (cell.states i).status = .unoccupied →
      slotDraw (record.input.row.2 record.input.time).1 = dataSlot → ∃ logged,
        ActiveFollowerLogging.checkedLogging i record.input.row (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i)) (cell.states i) = .ok logged ∧
        (record.output.followers i).downInput = some logged ∧
        logged.buffer = (cell.states i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i record := by
    intro i hu hd
    exact current_logging initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start k.val span seed states memories hoInput i hu hd
  have hmarkerLocal := marker_from_cell record cell hf out hout hgate hlogging
  have hmarker : cell.input.recordedArm = ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
      record cell.selected.view.payload true := by
    cases he : record.output.preparation.coordinator with
    | live registers owned base outcome =>
        cases outcome with
        | continuingChosen dispatched hstart continuation arm =>
            have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames record
            rw [he] at hframes
            have hsSel := hs
            rw [he] at hsSel
            change selectionAt record.input registers.payload dispatched.startResult record.input.time
              (liveRegistersAt registers record.input.time).complementWeights arm = some selected at hsSel
            rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq record.input registers.payload
              dispatched.startResult record.input.time (liveRegistersAt registers record.input.time).complementWeights
              arm rfl] at hsSel
            have hselEq := (Option.some.inj hsSel).symm
            have hq := ReferenceContinuingRecordingPhysicalReward.prefix_continuing_recording_physical_reward
              initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val
              span seed.activeAtStart seed.followers seed.memory seed.coordinatorFirst seed.configuration
              seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps
              registers owned base dispatched hstart continuation arm
              (by
                change (ReferenceActivePhysicalStep.prepare record.input).coordinator = _
                rw [← hp]
                exact he) states memories hoInput hframes.2
            have hpair := congrArg Prod.fst (hq.1 (record.input.row.2 record.input.time))
            simp only [ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair,
              ReferenceContinuingRecordingFastPair.candidatePhysicalMarker,
              FastRewardSliceLaw.liveRecordingFastPair] at hpair
            have hcand : ReferenceContinuingDataCandidateLogging.candidateRecord initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val span
                seed.activeAtStart (record.input.row.2 record.input.time) = record :=
              candidate_actual initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
                rewards start k.val span seed.activeAtStart
            rw [hcand] at hpair
            change ReferenceFirstWindowNumericalStream.sourceArm record selected.view.payload
              selected.view.pendingAtChoice states selected.view.complementWeights selected.view.cutoff
              (selection_choiceValid selected) =
                ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord record selected.view.payload true
            rw [hselEq]
            have hW : ReferenceFirstWindowNumericalStream.sourceWeights registers.payload
                (liveRegistersAt registers record.input.time).complementWeights =
                ReferenceContinuingLiveSlicePreparation.liveSliceWeights registers record.input.time := by
              funext j
              rfl
            simp only [ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm,
              ReferenceFirstWindowNumericalStream.sourceArm, hW]
            have ht : (ReferenceContinuingDataCandidateLogging.candidateInput initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val span
                seed.activeAtStart).time = record.input.time := rfl
            simpa only [ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot, ht] using hpair.symm
        | _ => exact hmarkerLocal
    | _ => exact hmarkerLocal
  have hphase := selected_live_phase_bits record selected hs hlive
  refine ⟨cell, hcell, ?_, hphase.1, hphase.2, rfl, rfl, rfl, ?_, hf, ?_, ?_, ?_, hlogging, ?_, ?_⟩
  · rw [← hcell]
    exact cell.enabled
  · simpa only [hcell] using hmarker
  · intro a ha
    exact cell_owner_feedback record cell hf a (by simpa only [hcell] using ha)
  · intro i hu
    simpa only [hcell] using occupied_arrival record cell i hu
  · intro i hu
    simpa only [hcell] using unoccupied_arrival record cell hf i hu
  · refine ⟨out, hout, ?_⟩
    intro a ha
    unfold ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
    rw [ReferenceCoordinatorRecorderCallTrace.recording_eq_actualDiagnostics]
    change (record.output.coordinator.recording).map _ = _
    rw [hout, Option.map_some]
    congr 1
    simpa only [hcell] using coordinator_arrival record cell out hgate hraw a ha
  · cases he : record.output.preparation.coordinator with
    | collection old ledger clock cutoff outcome =>
        cases outcome <;> try trivial
        rename_i core consistent started hstart instruction hinstruction output hcons clockData installed arm
        have hlater : ReferenceCollectionPhaseHistory.laterChosen record.input = true := by
          simp only [ReferenceCollectionPhaseHistory.laterChosen, ← hp, he]
        intro i
        exact ReferenceLaterStartUnoccupiedChoice.run_laterChosen_ordinary_choice_unoccupied initial
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start k.val span
          seed.activeAtStart seed.coordinatorFirst hlater i (states i) (memories i) (hoInput i)
    | _ => trivial

/-- Every arm is in exactly one actual ownership branch. An assigned arm's
readout uses its current emission while unoccupied and its raw occupied gate
otherwise. This is a raw-arrival partition, with no service-success claim. -/
theorem laterLiveReadout_all_arm_numerical
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : laterLiveReadout (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k) = some c)
    (a : Fin p.K) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k
    ∃ cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r,
      cell.input = c ∧
      (∃! owner : Fin p.m, owns p (.live cell.selected.view.payload.assignment
        (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) owner a) ∧
      ((a ∉ cell.selected.view.payload.slowSet.1 ∧
        ∃ out, r.output.coordinator.recording = some out ∧
          ReferenceCoordinatorRecorderCallTrace.coordinatorRaw
              (ReferenceActiveHorizonMeasurability.roundRecordCode r) a =
            some (RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a)) ∨
        ∃ i : Fin (p.m - 1), cell.selected.view.payload.assignment.assigned i = a ∧
          (∀ j, cell.selected.view.payload.assignment.assigned j = a → j = i) ∧
          (if (cell.states i).status = .unoccupied then
            ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution r cell.selected.view.payload i
          else ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
            (cell.selected.view.payload.downRecord i) (r.output.ownEntries (followerPlayer p.two_le_m i)).2) =
            RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  classical
  obtain ⟨cell, hcell, _, _, _, _, _, _, _, _, _, hoccupied, hunoccupied, _, hcoordinator, _⟩ :=
    laterLiveReadout_physical rate rewards C_star C_h source k c hc
  refine ⟨cell, hcell, ?_, ?_⟩
  · obtain ⟨owner, ho⟩ := exists_ownerSource p (.live cell.selected.view.payload.assignment
      (ReferenceActiveDataOwnership.choiceSnapshot cell.selected cell.states)) a
    exact ⟨owner, ho, fun other hother => owns_unique p _ a other owner hother ho⟩
  · by_cases ha : a ∈ cell.selected.view.payload.slowSet.1
    · rw [← cell.selected.view.payload.assignment_image] at ha
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      refine Or.inr ⟨i, hi, ?_, ?_⟩
      · intro j hj
        exact cell.selected.view.payload.assignment.injective (hj.trans hi.symm)
      · split_ifs with hu
        · simpa only [hi] using hunoccupied i hu
        · simpa only [hi] using (hoccupied i hu).2
    · obtain ⟨out, hout, hraw⟩ := hcoordinator
      exact Or.inl ⟨ha, out, hout, hraw a ha⟩

/-- Original-source calendar, preserving every absent cell and physical time. -/
def laterLivePartialCalendar (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).map
    fun r => (r.input.time, laterLiveReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) r)

theorem laterLivePartialCalendar_length (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (laterLivePartialCalendar rate rewards C_star C_h source).length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
  simp [laterLivePartialCalendar, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]

theorem laterLivePartialCalendar_length_le (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (laterLivePartialCalendar rate rewards C_star C_h source).length ≤ p.T := by
  rw [laterLivePartialCalendar_length]
  exact Nat.sub_le _ _

theorem laterLivePartialCalendar_get (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).length) :
    (laterLivePartialCalendar rate rewards C_star C_h source)[k.val]'(by
      simp [laterLivePartialCalendar]) =
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k |>.input.time,
        laterLiveReadout (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h).get k)) := by
  simp [laterLivePartialCalendar]

theorem laterLivePartialCalendar_times (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    (laterLivePartialCalendar rate rewards C_star C_h source).map (fun c => c.1.val) =
      ReferenceActivePhysicalHorizon.calendar
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  simpa [laterLivePartialCalendar, List.map_map, Function.comp_def] using
    ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate source rewards C_star C_h

end Bandits.Support.ReferenceLaterLiveNumericalReadout
