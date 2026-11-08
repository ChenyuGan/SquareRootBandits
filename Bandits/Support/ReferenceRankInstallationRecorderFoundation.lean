/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceChronologicalCollectionPhysicalMarginalInduction
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

/-!
# Arbitrary-rank installation recorder foundation

At the literal rank-`k` invocation on its actual date, this module retains the
original source, analytical strict prefix, every earlier rank mark, and the
complete current assignment vector. It derives the checked installation data
and selected view from the actual invocation, then proves the Borel
history/marker cylinder for the accepted optional cell-0 readout under the
original source law.

The current-remainder calculation fixes the whole assignment vector and keeps
the original nonassignment coordinates.

Source evidence: ZIP4 `06_interruptions.tex:381-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`appendix_a_local_protocol.tex:28-79`.
-/
@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceRankInstallationRecorderFoundation

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {Y : Type*} [MeasurableSpace Y] :
    MeasurableSpace (Option Y) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance optionSingleton {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y] :
    MeasurableSingletonClass (Option Y) := by
  constructor
  intro o
  let e := Equiv.optionEquivSumPUnit Y
  have hset : e ⁻¹' {e o} = {o} := by
    ext x
    exact e.injective.eq_iff
  rw [← hset]
  apply comap_measurable e
  cases he : e o with
  | inl y => simpa only [Set.image_singleton] using
      (measurableSet_singleton y).inl_image (β := PUnit)
  | inr u => simpa only [Set.image_singleton] using
      (measurableSet_singleton u).inr_image (α := Y)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

abbrev Mark (p : ConstructorDimensions.Parameters) :=
  ReferenceChronologicalCollectionPhysicalMarginalInduction.Mark p

abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  ReferenceFirstCollectionSamplerOutputLaw.AssignmentVector p

local instance outcomeMeasurableSpace :
    MeasurableSpace (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p) := ⟨fun _ => trivial⟩
local instance outcomeOptionMeasurableSpace :
    MeasurableSpace (Option (ReferenceFirstCollectionPastSamplerFibreLaw.Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The exact source history and complete current assignment vector exposed at
an original calendar date. -/
abbrev History (p : ConstructorDimensions.Parameters) :=
  SourceInput p × (List (Mark p) × AssignmentVector p)

local notation "records" =>
  (fun z : SourceInput p =>
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)
local notation "recordAt" =>
  ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
local notation "prefix" => ReferenceSourcePrefixHistoryFiltration.sourcePrefix
local notation "replaceControl" => ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
local notation "currentControl" => ReferenceSourceCurrentControlFreshness.u_t p
local notation "vectorAt" => ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector
local notation "View" => ReferenceDownReception.ChoiceTimeView p rate.eta
local notation "Remainder" => ReferenceLaterOptionalControlResampling.ControlRemainder p
local notation "remainderLaw" => ReferenceLaterOptionalControlResampling.controlRemainderLaw p
local notation "controlSplit" => LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
local notation "sliceSplit" => LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
local notation "mu" => BootstrapPrivateRoundStreams.sourceInputLaw p

/-- The literal `k`th actual sampler invocation is present at date `t`.
Checked sampler success is deliberately not part of this event. -/
def installationEvent (k : ℕ) (t : Fin p.T) : Set (SourceInput p) :=
  ⋃ u : Fin p.T,
    ReferenceCollectionRankCellPhysicalTransport.rankCell rate rewards C_star C_h k u t

/-- The requested history triple, with all source coordinates retained in its
strict prefix and all earlier rank marks retained as a list. -/
def history (control0 : TimeControl p) (k : ℕ) (t : Fin p.T) :
    SourceInput p → History p :=
  fun z =>
    (prefix control0 t.val z,
      (ReferenceCollectionRankResamplingKernel.markedPrefix
        rate rewards C_star C_h k control0 z,
        vectorAt t z))

local notation "installEvent" => installationEvent rate rewards C_star C_h

local notation "historyAt" => history rate rewards C_star C_h

/-- The actual invocation event is Borel on the original source. -/
theorem measurableSet_installationEvent (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) :
    MeasurableSet (installEvent k t) := by
  exact MeasurableSet.iUnion fun u =>
    ReferenceCollectionRankCellPhysicalTransport.rankCell_borel
      rate rewards C_star C_h control0 k u t

/-- The actual rank/date invocation is measurable from the original strict
pre-date source prefix, before splitting the current control. -/
theorem measurableSet_installationEvent_m_t (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (installEvent k t) := by
  rw [← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
  exact MeasurableSet.iUnion fun u =>
    ReferenceCollectionRankCellPhysicalTransport.rankCell_measurable
      rate rewards C_star C_h control0 k u t

/-- At the actual `k`th invocation on date `t`, its full stored rank prefix is
the genuine list of all earlier-date marks. -/
theorem markedPrefix_eq_earlierMarkedCalls_of_installation
    (control0 : TimeControl p) (k : ℕ) (t : Fin p.T)
    (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ReferenceCollectionRankResamplingKernel.markedPrefix
        rate rewards C_star C_h k control0 z =
      ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls
        rate rewards C_star C_h control0 t.val z := by
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp (by simpa [installationEvent] using hz)
  obtain ⟨theta, hcall⟩ :=
    (ReferenceCollectionRankCellPhysicalTransport.mem_rankCell_iff_exists_call
      rate rewards C_star C_h k u t z).mp hu
  exact (ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls_eq_mapped_take_of_present_rank
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      control0 k u t theta z hcall).symm

/-- The genuine current-control split law at an arbitrary original ranked
collection installation. The adapted prefix and all earlier marks stay
jointly observed, while the complete assignment vector, every other scalar,
and all affine samples retain their original product law. -/
theorem installation_controlSplit_cylinder (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (Aset : Set (SourceInput p))
    (hA : MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t] Aset)
    (Cset : Set (AssignmentVector p × Remainder)) (hC : MeasurableSet Cset) :
    mu ({z | z ∈ installEvent k t ∧ z ∈ Aset} ∩
      (fun z => controlSplit (currentControl t z)) ⁻¹' Cset) =
      mu {z | z ∈ installEvent k t ∧ z ∈ Aset} *
        ((ContinuousControlSlice.assignmentLaw p.K).prod remainderLaw) Cset := by
  have hP := (measurableSet_installationEvent_m_t rate rewards C_star C_h control0 k t).inter hA
  have hsplit := LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p
  have hc := ReferenceSourceCurrentControlFreshness.source_control_cylinder control0 t
    {z | z ∈ installEvent k t ∧ z ∈ Aset} hP
    ((controlSplit) ⁻¹' Cset) (hC.preimage (controlSplit).measurable)
  rw [hsplit.measure_preimage hC.nullMeasurableSet] at hc
  exact hc

/-- Current-control replacement preserves the event while retaining the full
original source and without adding an assignment-success condition. -/
theorem installationEvent_replaceSourceControl (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p) (c : TimeControl p) :
    replaceControl t z c ∈ installEvent k t ↔
      z ∈ installEvent k t := by
  unfold installationEvent
  rw [Set.mem_iUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (ReferenceCollectionRankCellPhysicalTransport.rankCell_replaceSourceControl_iff
      rate rewards C_star C_h control0 k u t z c).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (ReferenceCollectionRankCellPhysicalTransport.rankCell_replaceSourceControl_iff
      rate rewards C_star C_h control0 k u t z c).mpr hu⟩

/-- The current assignment vector is exactly the assignment coordinate of the
replacement `TimeControl`; all other source coordinates remain in place. -/
theorem currentAssignmentVector_replaceSourceControl (t : Fin p.T)
    (z : SourceInput p) (c : TimeControl p) :
    vectorAt t
      (replaceControl t z c) = ContinuousControlSlice.assignmentVector c.1 := by
  simp only [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector, ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]

/-- The actual accepted optional cell-0 readout, retaining outer absence,
present bottom, and a recorded arm as distinct values. -/
def actualMarker (q : Fin p.T) (z : SourceInput p) : Option (Option (Fin p.K)) :=
  ((recordAt q z).bind
    (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map fun c => c.recordedArm

local notation "markerAt" => actualMarker rate rewards C_star C_h

/-- The whole-source cell-0 marker is Borel, with both numerical branches. -/
theorem measurable_actualMarker (q : Fin p.T) :
    Measurable (markerAt q) := by
  have heq : markerAt q = fun z =>
      (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualMarker rate rewards C_star C_h q z).or
        (ReferenceFirstCollectionOldRecorderFoundation.oldMarker? rate rewards C_star C_h q z) := by
    funext z
    unfold actualMarker ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualMarker
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      ReferenceFirstCollectionOldRecorderFoundation.oldMarker?
      ReferenceFirstCollectionOldRecorderFoundation.oldCell?
    cases recordAt q z <;>
      simp only [Option.bind_none, Option.bind_some, Option.map_none,
        ReferenceFirstCollectionCurrentRetainedGate.cell0, Option.map_or, Option.none_or]
  rw [heq]
  exact (measurable_of_countable (fun x : Option (Option (Fin p.K)) × Option (Option (Fin p.K)) =>
    x.1.or x.2)).comp
      ((ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualMarker
        rate rewards C_star C_h q).prodMk
          (ReferenceFirstCollectionOldRecorderFoundation.oldMarker_measurable rate rewards C_star C_h q))

open ReferenceActivePhysicalStep
open ReferenceLaterLiveNumericalReadout
open ReferenceFirstWindowNumericalStream
open scoped Classical

/-- A literal prechoice invocation has empty incoming pending set. This is a
consequence of the selector's own checks, before the checked sample is read. -/
theorem collectionCall_pending_empty
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (u : Fin p.T) (theta : AssignmentParameterFibreKernel.Theta p)
    (hc : ReferenceFirstCollectionSamplerCall.collectionCallAt r = some (u, theta)) :
    ∃ payload ledger saved,
      r.input.state.coordinator = .collection payload ledger saved ∧
      ledger.cutoff = u.val + 1 ∧ ledger.pending = ∅ := by
  obtain ⟨payload, ledger, saved, hs, hu, hp⟩ :=
    (ReferenceFirstCollectionSamplerCall.collectionCallAt_spec r u theta).mp hc
  refine ⟨payload, ledger, saved, hs, hu, ?_⟩
  by_contra hn
  have hne : ledger.pending.Nonempty := Finset.nonempty_iff_ne_empty.mpr hn
  have hbound : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    rw [hu]
    exact ⟨Nat.succ_pos _, u.isLt⟩
  change ReferenceLaterAssignmentFibreStep.parameters? r.input = some theta at hp
  simp only [ReferenceLaterAssignmentFibreStep.parameters?, hs, dite_eq_left hbound] at hp
  unfold ReferenceLaterAssignmentFibreStep.collectionParameters? at hp
  split at hp
  · cases hp
  · split at hp
    · simp only [collectionInput, hne, ite_true] at hp
      cases hp
    · cases hp

/-- Actual installation recording data, on the same record and payload as
its sampler invocation. All followers are unoccupied at CHOICE; the actual
readout is present, enabled, and uses the emitted payload's rate vector. -/
theorem installationEvent_recordingData (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ (b : Fin (records z).length)
      (native : ActualLiveSourceCell (records z)[b.val]),
      recordAt t z = some (records z)[b.val] ∧
      (records z)[b.val].input.time = t ∧
      ReferenceCollectionPhaseHistory.laterChosen
        (records z)[b.val].input = true ∧
      0 < native.selected.view.payload.sigma.val ∧
      native.selected.view.pendingAtChoice = Finset.univ ∧
      (∀ i, (native.states i).status = .unoccupied) ∧
      laterLiveReadout 0 (records z)[b.val] = some native.input ∧
      markerAt t z = some native.input.recordedArm ∧
      native.input.enabled = true ∧
      native.input.rate = native.selected.view.payload.rate := by
  let R := records z
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hz
  obtain ⟨theta, n, r, _o, _hcall, hlookup, hr, ht, hc, _⟩ :=
    ReferenceCollectionRankCellPhysicalTransport.rankCell_actualSamplerTrace
      rate rewards C_star C_h k u t z hu
  obtain ⟨hn, heq⟩ := List.getElem?_eq_some_iff.mp hlookup
  let b : Fin R.length := ⟨n, hn⟩
  subst r
  obtain ⟨P, l, saved, hstate, _hcutoff, hpending⟩ :=
    collectionCall_pending_empty rate R[b.val] u theta hc
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z b
  dsimp only at hstep
  rw [hstate] at hstep
  dsimp only at hstep
  obtain ⟨u, _hu, core, started, hstart, instruction, hassignment, htime, _hkind,
    consistent, output, hlocal, _hsuccess, clockData, installed, arm, _hinstall,
    _hresult, _hdispatch, hprepared, _hpayload, _hvector, _hassignmentVector,
    _hbase, _hqueues, _hanchor, v, hselection, hvpayload, _hvcutoff, _hlive,
    hstrict, c, ho, native, _hreadout, _hcell, hcellSelected, _hstates, _hmemories,
    hunoccupied, _henabled, _hrate, _⟩ := hstep hpending
  have hb : ReferenceCollectionPhaseHistory.laterChosen R[b.val].input = true := by
    have hprep : R[b.val].output.preparation = prepare R[b.val].input := by
      rw [R[b.val].output_eq]
      rfl
    unfold ReferenceCollectionPhaseHistory.laterChosen
    rw [← hprep, hprepared]
  have hpositive : 0 < native.selected.view.payload.sigma.val := by
    rw [hcellSelected, hvpayload]
    omega
  have hread : laterLiveReadout 0 R[b.val] = some native.input := by
    unfold laterLiveReadout
    have hsel : R[b.val].output.preparation.coordinator.selection =
        some native.selected := native.selection_actual
    rw [hsel]
    dsimp only
    rw [ite_eq_left ⟨hpositive, native.assignment_live⟩, dite_eq_left ho]
    have hstates : preparedStates R[b.val] ho = native.states := by
      funext i
      exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        ((prepared_configuration R[b.val] ho i).symm.trans (native.ordinary i))).1
    rw [hstates, native.input_eq]
  have hstarted : v.started = started := by
    rw [hprepared] at hselection
    change selectionAt R[b.val].input installed.registers.payload started instruction.time
      installed.registers.complementWeights arm = some v at hselection
    rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
      R[b.val].input installed.registers.payload started instruction.time
      installed.registers.complementWeights arm htime] at hselection
    cases hselection
    rfl
  have hfull := (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
    R[b.val].input.time (collectionClock P l saved u) l.pending started instruction
    core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid
    hstart hassignment).2.2.2.2.2.2.1
  refine ⟨b, native, hr, ht, hb, hpositive, ?_, hunoccupied, hread, ?_, native.enabled, ?_⟩
  · rw [hcellSelected, v.pending_eq, hstarted, hfull]
    rfl
  · change ((recordAt t z).bind (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map _ = _
    rw [hr]
    change (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate R[b.val]).map _ = _
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread]
    rfl
  · rw [native.input_eq]
    rfl

/-- An original invocation chooses its installation without a supplied
successful checked outcome or numerical-alignment premise. -/
theorem installationEvent_chosen (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ b : Fin (records z).length, recordAt t z = some (records z)[b.val] ∧
      (records z)[b.val].input.time = t ∧
      ReferenceCollectionPhaseHistory.laterChosen (records z)[b.val].input = true := by
  obtain ⟨b, _native, hr, ht, hb, _⟩ :=
    installationEvent_recordingData rate rewards C_star C_h k t z hz
  exact ⟨b, hr, ht, hb⟩

/-- The invocation event has no outer-absent marker. Present bottom remains a
separate possible observation, including a zero recorded reward. -/
theorem actualMarker_ne_none_of_installation (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    markerAt t z ≠ none := by
  obtain ⟨b, native, _hr, _ht, _hb, _hpos, _hpending, _hstates, _hread, hm, _⟩ :=
    installationEvent_recordingData rate rewards C_star C_h k t z hz
  rw [hm]
  exact Option.some_ne_none _

open ReferenceCollectionDispatchMeasurability
open ReferenceCollectionInstallOutputMeasurability

/-- The view emitted by the actual checked later-installation producer,
before exposing its chosen arm. Absence is the producer's literal absence. -/
def installationPrechoiceView (z : LocalInput p rate) : Option View :=
  (laterInstalledObservation? z).map fun c => c.2.1

theorem measurable_installationPrechoiceView : Measurable (installationPrechoiceView rate) :=
  LaterAssignmentFullOutputMeasurability.measurable_optionMap _
    (measurable_fst.comp measurable_snd) _ measurable_laterInstalledObservation?

/-- The checked installation view reads only the complete assignment vector
from the current row. This includes every absent producer branch. -/
theorem installationPrechoiceView_row (z : LocalInput p rate)
    (row : CompletePublicTable.CompleteRow p)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector z.1.2 z.2.2.2.2.1 =
      LaterAssignmentStartOperation.ownAssignmentVector row z.2.2.2.2.1) :
    installationPrechoiceView rate z = installationPrechoiceView rate ((z.1.1, row), z.2) := by
  let z' : LocalInput p rate := ((z.1.1, row), z.2)
  change installationPrechoiceView rate z = installationPrechoiceView rate z'
  have hclock : clockObservation z' = clockObservation z := rfl
  have hcore : CoordinatorRoundDispatch.CollectionCoreValid (assemble z) ↔
      CoordinatorRoundDispatch.CollectionCoreValid (assemble z') := by
    rw [← coreChecks_iff z, ← coreChecks_iff z']
    rfl
  by_cases hc : CoordinatorRoundDispatch.CollectionCoreValid (assemble z)
  · have hc' := hcore.mp hc
    unfold installationPrechoiceView laterInstalledObservation?
    rw [dite_eq_left hc, dite_eq_left hc']
    rw [hclock]
    unfold laterInstalledAtClock clockObservation
    cases hs : CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
        (assemble z).clock (assemble z).ledger.pending with
    | error reason => rfl
    | ok started =>
      change ((if z.2.1.pending.Nonempty then none else
          match requestedInstructionAt z (.inr started) with
          | none => none
          | some instruction => laterInstalledObservation ⟨z, hc⟩ instruction started).map
            (fun c => c.2.1)) =
        ((if z'.2.1.pending.Nonempty then none else
          match requestedInstructionAt z' (.inr started) with
          | none => none
          | some instruction => laterInstalledObservation ⟨z', hc'⟩ instruction started).map
            (fun c => c.2.1))
      by_cases hp : z.2.1.pending.Nonempty
      · simp only [show z'.2.1 = z.2.1 from rfl, hp, ite_true]
      · simp only [show z'.2.1 = z.2.1 from rfl, hp, ite_false,
          requestedInstructionAt]
        cases hi : started.assignmentStart with
        | none => rfl
        | some instruction =>
          have ht := (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
            (assemble z).time (assemble z).clock (assemble z).ledger.pending
            started instruction hc.clock_parameter_valid hc.clock_registers_valid
            hc.clock_start_time_valid hs hi).1
          have hv' : LaterAssignmentStartOperation.ownAssignmentVector z.1.2 instruction.time =
              LaterAssignmentStartOperation.ownAssignmentVector row instruction.time := by
            rw [ht]
            exact hv
          have hps : laterPayloadScore? ⟨z, hc⟩ instruction =
              laterPayloadScore? ⟨z', hc'⟩ instruction := by
            exact LaterAssignmentStartMeasurability.laterAssignmentStart_payloadAndBaseScore?_eq_of_ownAssignmentVector_eq
              z.1.1 ⟨operationLedger ⟨z, hc⟩, instruction, localConsistency ⟨z, hc⟩⟩
              z.1.2 row hv'
          simp only [laterInstalledObservation, Option.map_map]
          change (laterPayloadScore? ⟨z, hc⟩ instruction).map
              (fun ps => installedView (installationCoordinates ps z.2.1 instruction started) started) =
            (laterPayloadScore? ⟨z', hc'⟩ instruction).map
              (fun ps => installedView (installationCoordinates ps z.2.1 instruction started) started)
          rw [hps]
  · have hc' : ¬ CoordinatorRoundDispatch.CollectionCoreValid (assemble z') :=
      mt hcore.mpr hc
    simp only [installationPrechoiceView, laterInstalledObservation?,
      dite_eq_right hc, dite_eq_right hc', Option.map_none]

open ReferenceCollectionOutcomeMeasurability

local instance clockObservationMeasurableSpace : MeasurableSpace (ClockObservation p) := ⊤
local instance startResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤

/-- The literal installation-view projection of the existing complete
collection observation. The invalid-cutoff and absent branches stay absent. -/
def installationViewOnInput (x : RoundInput p rate) : Option View :=
  optionalElim none
    (Sum.elim (fun _ => none) (fun o => o.2.1.map fun c => c.2.1))
    (canonicalCollectionFullObservation x)

theorem measurable_installationViewOnInput : Measurable (installationViewOnInput rate) := by
  let f : InstalledObservation p rate → View :=
    fun c => c.2.1
  have hf : Measurable f := measurable_fst.comp measurable_snd
  have hmap : Measurable (fun c : Option (InstalledObservation p rate) => c.map f) :=
    LaterAssignmentFullOutputMeasurability.measurable_optionMap f hf id measurable_id
  have hm : Measurable (fun o : FullObservation p rate => o.2.1.map f) :=
    hmap.comp (measurable_fst.comp measurable_snd)
  have hsum : Measurable (Sum.elim (fun _ : Unit =>
      (none : Option View))
        (fun o : FullObservation p rate => o.2.1.map f)) :=
    measurable_const.sumElim hm
  have helim := measurable_optionalElim none _ hsum
  exact helim.comp measurable_canonicalCollectionFullObservation

/-- On a valid actual collection cutoff the projection is exactly the
existing local checked installation producer. -/
theorem installationViewOnInput_collection (x : RoundInput p rate)
    (P : Payload rate) (l : Ledger rate) (saved : Option (Fin p.T × Bool))
    (hs : x.state.coordinator = .collection P l saved) (u : Fin p.T)
    (hu : u.val + 1 = l.cutoff) :
    installationViewOnInput rate x = installationPrechoiceView rate
      ((P, x.row), l, saved, x.state.upDecoderBank, x.time, u) := by
  have hb : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T := by
    constructor <;> have := u.isLt <;> omega
  have he : (⟨l.cutoff - 1, by omega⟩ : Fin p.T) = u := Fin.ext (by dsimp only; omega)
  have hb' : cutoffValid ((P, x.row), l, saved, x.state.upDecoderBank, x.time) := hb
  rw [installationViewOnInput, canonicalCollectionFullObservation_collection x P l saved hs]
  simp only [optionalElim, boundaryFullObservation, dite_eq_left hb', Sum.elim_inr]
  change installationPrechoiceView rate
      ((P, x.row), l, saved, x.state.upDecoderBank, x.time, ⟨l.cutoff - 1, _⟩) = _
  rw [he]

/-- On the collection carrier, equal incoming state, date, and full assignment
vector give the same checked installation view. Other row fields are free. -/
theorem installationViewOnInput_eq_of_reads (x y : RoundInput p rate)
    (hs : x.state = y.state) (ht : x.time = y.time)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector x.row x.time =
      LaterAssignmentStartOperation.ownAssignmentVector y.row y.time) :
    installationViewOnInput rate x = installationViewOnInput rate y := by
  cases hphase : x.state.coordinator with
  | first =>
    simp only [installationViewOnInput, canonicalCollectionFullObservation,
      hphase, ← hs, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      collectionCoordinates?, mapOptional, Option.map_none, optionalElim]
  | live registers owned base =>
    simp only [installationViewOnInput, canonicalCollectionFullObservation,
      hphase, ← hs, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      collectionCoordinates?, mapOptional, Option.map_none, optionalElim]
  | dagger =>
    simp only [installationViewOnInput, canonicalCollectionFullObservation,
      hphase, ← hs, ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
      collectionCoordinates?, mapOptional, Option.map_none, optionalElim]
  | collection P l saved =>
    have hy : y.state.coordinator = .collection P l saved := by rw [← hs]; exact hphase
    by_cases hb : 1 ≤ l.cutoff ∧ l.cutoff ≤ p.T
    · let u : Fin p.T := ⟨l.cutoff - 1, by omega⟩
      have hu : u.val + 1 = l.cutoff := by dsimp only [u]; omega
      rw [installationViewOnInput_collection rate x P l saved hphase u hu,
        installationViewOnInput_collection rate y P l saved hy u hu]
      rw [← hs, ← ht]
      exact installationPrechoiceView_row rate
        ((P, x.row), l, saved, x.state.upDecoderBank, x.time, u) y.row
        (by simpa only [← ht] using hv)
    · have hx : ¬ cutoffValid ((P, x.row), l, saved, x.state.upDecoderBank, x.time) := hb
      have hy' : ¬ cutoffValid ((P, y.row), l, saved, y.state.upDecoderBank, y.time) := hb
      rw [installationViewOnInput, installationViewOnInput,
        canonicalCollectionFullObservation_collection x P l saved hphase,
        canonicalCollectionFullObservation_collection y P l saved hy]
      simp only [optionalElim, boundaryFullObservation, dite_eq_right hx,
        dite_eq_right hy', Sum.elim_inl]

/-- The actual optional installation view at an original calendar date. -/
def actualInstallationView (t : Fin p.T) (z : SourceInput p) : Option View :=
  (recordAt t z).bind fun r => installationViewOnInput rate r.input

local notation "viewAt" => actualInstallationView rate rewards C_star C_h

theorem measurable_actualInstallationView (t : Fin p.T) :
    Measurable (viewAt t) := by
  apply ReferenceOriginalCalendarContinuingLiveRecorderLaw.measurable_actualReadout
    rate rewards C_star C_h (fun r => installationViewOnInput rate r.input)
  intro n
  exact (measurable_installationViewOnInput rate).comp
    (ReferenceCompleteSuffixInputMeasurability.measurable_actualRoundInputAt
      rate rewards C_star C_h n)

/-- The Borel prechoice projection is the selected view of the same actual
installation. Successful output and all local consistency data are derived. -/
private theorem installationViewOnInput_actual (z : SourceInput p)
    (b : Fin (records z).length)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (records z)[b.val].input = true)
    (selected : Selection (records z)[b.val].input)
    (hs : (records z)[b.val].output.preparation.coordinator.selection = some selected) :
    installationViewOnInput rate (records z)[b.val].input = some selected.view := by
  let R := records z
  obtain ⟨P, l, saved, hstate, hpending⟩ :=
    ReferenceCollectionPhaseHistory.laterChosen_pending_empty R[b.val].input hb
  have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
    rate rewards C_star C_h z b
  dsimp only at hstep
  rw [hstate] at hstep
  dsimp only at hstep
  obtain ⟨u, hu, core, started, hstart, instruction, hassignment, htime, _hkind,
    consistent, output, hlocal, hsuccess, clockData, installed, arm, hinstall,
    hresult, _hdispatch, hprepared, _⟩ := hstep hpending
  subst installed
  let localInput : LocalInput p rate :=
    ((P, R[b.val].input.row), l, saved, R[b.val].input.state.upDecoderBank,
      R[b.val].input.time, u)
  let checked : CoreInput p rate := ⟨localInput, core⟩
  have hcons : consistent = localConsistency checked := by
    cases consistent with
    | mk hstart hassignment oldFreeze hfreeze =>
      have he : oldFreeze = l.freezeAt := hfreeze
      subst oldFreeze
      rfl
  have hlocal' : output.localConsistency = localConsistency checked := hlocal.trans hcons
  have hsuccess' : LaterAssignmentStartOperation.laterAssignmentStart P
      (operationLedger checked) instruction R[b.val].input.row (localConsistency checked) =
        .success output hlocal' := by
    cases hcons
    exact hsuccess
  have hobs := laterInstalledObservation?_of_actual_success checked started hstart
    (by rw [hpending]; exact Finset.not_nonempty_empty) instruction hassignment
    output hlocal' hsuccess'
  have hv := congrArg (Option.map (fun c : InstalledObservation p rate => c.2.1)) hobs
  change installationPrechoiceView rate localInput = some
    (installedView (installationCoordinates (output.payload, output.baseScore) l instruction started)
      started) at hv
  have hvactual := installedView_eq_actual checked instruction output clockData
  dsimp only at hvactual
  rw [hresult] at hvactual
  rw [hvactual] at hv
  have hsel : selected.view =
      ({ payload := (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload
         pendingAtChoice := started.pending
         cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
         complementWeights := (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights } :
        View) := by
    rw [hprepared] at hs
    change selectionAt R[b.val].input (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload started instruction.time
      (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights arm = some selected at hs
    rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
      R[b.val].input (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.payload started instruction.time
      (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights arm htime] at hs
    cases hs
    rfl
  rw [installationViewOnInput_collection rate R[b.val].input P l saved hstate u hu]
  exact hv.trans (congrArg some hsel.symm)

private theorem actualRecord_assignmentVector (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (hr : recordAt t z = some r) :
    LaterAssignmentStartOperation.ownAssignmentVector r.input.row r.input.time =
      vectorAt t z := by
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z r hr
  simp only [LaterAssignmentStartOperation.ownAssignmentVector, RoundInput.row,
    hf.1, hf.2.1, hf.2.2.1,
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
    ReferenceSourceCurrentControlFreshness.u_t]

/-- Replacing the other current controls, while keeping the whole assignment
vector, preserves the checked installation view on every branch. -/
theorem actualInstallationView_replace (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) (c : TimeControl p)
    (hv : ContinuousControlSlice.assignmentVector c.1 =
      vectorAt t z) :
    viewAt t
      (replaceControl t (prefix control0 t.val z) c) =
      viewAt t z := by
  let z' := replaceControl t (prefix control0 t.val z) c
  have hin := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualIncoming_replace
    rate rewards C_star C_h control0 t z c
  change ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' at hin
  change viewAt t z' =
    viewAt t z
  unfold actualInstallationView
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hin
  cases hr : recordAt t z with
  | none =>
    cases hr' : recordAt t z' with
    | none => rfl
    | some r' =>
      simp only [hr, hr', Option.map_none, Option.map_some] at hin
      cases hin
  | some r =>
    cases hr' : recordAt t z' with
    | none =>
      simp only [hr, hr', Option.map_none, Option.map_some] at hin
      cases hin
    | some r' =>
      have hstate := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecords_state_congr
        rate rewards C_star C_h t z z' r r' hr hr' hin
      have ht := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
        rate rewards C_star C_h t z r hr).2.2.1.trans
          (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
            rate rewards C_star C_h t z' r' hr').2.2.1.symm
      have hv' : LaterAssignmentStartOperation.ownAssignmentVector r.input.row r.input.time =
          LaterAssignmentStartOperation.ownAssignmentVector r'.input.row r'.input.time := by
        rw [actualRecord_assignmentVector rate rewards C_star C_h t z r hr,
          actualRecord_assignmentVector rate rewards C_star C_h t z' r' hr',
          currentAssignmentVector_replaceSourceControl]
        exact hv.symm
      simp only [Option.bind_some]
      change installationViewOnInput rate r'.input = installationViewOnInput rate r.input
      exact (installationViewOnInput_eq_of_reads rate r.input r'.input hstate ht hv').symm

/-- Restore an assignment vector with the original scalar labels and a fixed
remaining control. No alternate sampler or alternate state is introduced. -/
def controlWithVector (control0 : TimeControl p) (v : AssignmentVector p) : TimeControl p :=
  (controlSplit).symm
    (v, (controlSplit control0).2)

theorem controlWithVector_assignment (control0 : TimeControl p) (v : AssignmentVector p) :
    ContinuousControlSlice.assignmentVector (controlWithVector control0 v).1 = v := by
  change (controlSplit
    (controlWithVector control0 v)).1 = v
  rw [controlWithVector, (controlSplit).apply_symm_apply]

/-- The installation view computed from the exact requested history triple.
The full earlier-mark list and complete assignment vector stay on its carrier. -/
def viewFromHistory (control0 : TimeControl p) (t : Fin p.T) (h : History p) :
    Option View :=
  viewAt t
    (replaceControl t h.1
      (controlWithVector control0 h.2.2))

local notation "historyView" => viewFromHistory rate rewards C_star C_h

theorem measurable_viewFromHistory (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (historyView control0 t) := by
  have hc : Measurable (fun h : History p => controlWithVector control0 h.2.2) :=
    (controlSplit).symm.measurable.comp
      ((measurable_snd.comp measurable_snd).prodMk measurable_const)
  exact (measurable_actualInstallationView rate rewards C_star C_h t).comp
    ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
      (measurable_fst.prodMk hc))

/-- Genuine Borel factorization through the source prefix, all earlier rank
marks, and the complete current assignment vector. -/
theorem actualInstallationView_eq_history (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p) :
    viewAt t z =
      historyView control0 t (historyAt control0 k t z) := by
  exact (actualInstallationView_replace rate rewards C_star C_h control0 t z
    (controlWithVector control0
      (vectorAt t z))
    (controlWithVector_assignment _ _)).symm

/-- All followers are pending and unoccupied at the chosen installation. -/
def installationSnapshot (a : ActiveRoundActions.Assignment p.m p.K) :
    ActiveRoundActions.Snapshot a :=
  ⟨Finset.univ, fun _ => .unoccupied⟩

/-- The optional enabled/rate data are a Borel readout of the actual view,
with literal absence retained. -/
def parametersFromHistory (control0 : TimeControl p) (t : Fin p.T) (h : History p) :
    Option (Bool × (Fin p.K → ℝ)) :=
  (historyView control0 t h).map
    fun v => (true, v.payload.rate)

local notation "historyParameters" => parametersFromHistory rate rewards C_star C_h

theorem measurable_parametersFromHistory (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (historyParameters control0 t) := by
  have hp : Measurable (fun v : View =>
      v.payload) := measurable_fst.comp
    (comap_measurable ReferenceDownReceptionMeasurability.choiceTimeViewObservation)
  have hr : Measurable (fun v : View =>
      (true, v.payload.rate)) := measurable_const.prodMk
    (AssignmentPayloadDerivedMeasurability.measurable_inputRate.comp hp)
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap _ hr _
    (measurable_viewFromHistory rate rewards C_star C_h control0 t)

/-- The genuine recording map of the emitted installation view. Validity is
used only for the actual weight-envelope proofs in the existing map. -/
def installationRecordingMap (s : Fin p.T)
    (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff s
      v.complementWeights) : ContinuousControlSlice.Slice p.m p.K → Option (Fin p.K) :=
  SnapshotRecordingKernel.recordingMap p
    (.live v.payload.assignment (installationSnapshot v.payload.assignment)) true
    rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
    (sourceWeights v.payload v.complementWeights) v.payload.anchor_pos
    (sourceWeights_pos _ _ _ _ valid) (sourceWeights_lower _ _ _ _ valid)
    (sourceWeights_upper _ _ _ _ valid)

local notation "recording" => installationRecordingMap rate

/-- The actual installation's accepted marker is the genuine snapshot
recording map. Its selected payload and complete rates are Borel data of H. -/
theorem installationEvent_marker_formula (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ (b : Fin (records z).length)
      (native : ActualLiveSourceCell (records z)[b.val]),
      recordAt t z = some (records z)[b.val] ∧
      (records z)[b.val].input.time = t ∧
      historyView control0 t (historyAt control0 k t z) = some native.selected.view ∧
      historyParameters control0 t (historyAt control0 k t z) =
        some (true, native.selected.view.payload.rate) ∧
      markerAt t z = some
        (recording (records z)[b.val].input.time native.selected.view native.choiceInputsValid
          (currentControl t z).1) := by
  obtain ⟨b, native, hr, ht, hb, _hpos, hpending, hstates, _hread, hm, _henabled, _hrate⟩ :=
    installationEvent_recordingData rate rewards C_star C_h k t z hz
  have hv := installationViewOnInput_actual rate rewards C_star C_h z b hb
    native.selected native.selection_actual
  have hview : historyView control0 t (historyAt control0 k t z) = some native.selected.view := by
    rw [← actualInstallationView_eq_history]
    change (recordAt t z).bind _ = _
    rw [hr]
    exact hv
  refine ⟨b, native, hr, ht, hview, ?_, ?_⟩
  · simp only [parametersFromHistory, hview, Option.map_some]
  · rw [hm, native.recordedArm_eq]
    have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h t z _ hr
    dsimp only [installationRecordingMap]
    simp only [sourceArm, hpending]
    have hrow : ((records z)[b.val].input.row.2
          (records z)[b.val].input.time).1 =
        (currentControl t z).1 := by
      simp only [RoundInput.row, hf.1, hf.2.1, ht,
        ReferenceSourceCurrentControlFreshness.u_t]
    rw [hrow]
    have hsnap : ({ missing := Finset.univ, status := fun i => (native.states i).status } :
        ActiveRoundActions.Snapshot native.selected.view.payload.assignment) =
          installationSnapshot native.selected.view.payload.assignment := by
      apply congrArg (fun status : ActiveRoundActions.Follower p.m →
          ActiveRoundActions.FollowerStatus =>
        ({ missing := Finset.univ, status := status } :
          ActiveRoundActions.Snapshot native.selected.view.payload.assignment))
      funext i
      exact hstates i
    change some (SnapshotRecordingKernel.recordingMap p _ _ _ _ _ _ _ _ _ _ _ _) =
      some (recording (records z)[b.val].input.time native.selected.view
        native.choiceInputsValid (currentControl t z).1)
    rw [hsnap]
    rfl


private theorem installationRecordingMap_congr (s s' : Fin p.T)
    (v v' : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff s v.complementWeights)
    (valid' : CoordinatorLocalArmChoice.ChoiceInputsValid v'.payload v'.cutoff s' v'.complementWeights)
    (hv : v = v') :
    installationRecordingMap rate s v valid = installationRecordingMap rate s' v' valid' := by
  subst v'
  rfl

/-- Truncating at the actual invocation date preserves the invocation event;
this follows from the actual rank observer, without a success test. -/
theorem installationEvent_sourcePrefix (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p) :
    prefix control0 t.val z ∈ installEvent k t ↔
      z ∈ installEvent k t := by
  have hcell (u : Fin p.T) :
      prefix control0 t.val z ∈
          ReferenceCollectionRankCellPhysicalTransport.rankCell rate rewards C_star C_h k u t ↔
        z ∈ ReferenceCollectionRankCellPhysicalTransport.rankCell rate rewards C_star C_h k u t := by
    change (ReferenceCollectionSamplerChronology.nthAt rate rewards C_star C_h k t
        (prefix control0 t.val z)).map Prod.fst = some u ↔ _
    rw [← ReferenceCollectionSamplerChronology.nthAt_factor rate rewards C_star C_h
      control0 k t z]
    rfl
  simp only [installationEvent, Set.mem_iUnion, hcell]

/-- On an arbitrary original installation, every replacement of the current
remainder uses this same installed view and actual snapshot map. The whole
assignment vector is retained; all other coordinates remain unrestricted. -/
theorem actualMarker_all_remaining_controls (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ (s : Fin p.T) (v : View)
      (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff s v.complementWeights),
      s = t ∧ viewAt t z = some v ∧
      markerAt t z =
        some (recording s v valid (currentControl t z).1) ∧
      ∀ c : TimeControl p,
        ContinuousControlSlice.assignmentVector c.1 =
          vectorAt t z →
        markerAt t (replaceControl t (prefix control0 t.val z) c) =
          some (recording s v valid c.1) := by
  obtain ⟨b, native, _hr, ht, hview, _hparams, hm⟩ :=
    installationEvent_marker_formula rate rewards C_star C_h control0 k t z hz
  let s := (records z)[b.val].input.time
  have hv : viewAt t z = some native.selected.view := by
    rw [actualInstallationView_eq_history rate rewards C_star C_h control0 k t z, hview]
  refine ⟨s, native.selected.view, native.choiceInputsValid, ht, hv, hm, ?_⟩
  intro c hc
  let z' := replaceControl t (prefix control0 t.val z) c
  have hz' : z' ∈ installEvent k t :=
    (installationEvent_replaceSourceControl rate rewards C_star C_h control0 k t _ c).mpr
      ((installationEvent_sourcePrefix rate rewards C_star C_h control0 k t z).mpr hz)
  obtain ⟨b', native', _hr', _ht', hview', _hparams', hm'⟩ :=
    installationEvent_marker_formula rate rewards C_star C_h control0 k t z' hz'
  have hv' : native'.selected.view = native.selected.view := by
    apply Option.some.inj
    calc
      some native'.selected.view = viewAt t z' := by
        rw [actualInstallationView_eq_history rate rewards C_star C_h control0 k t z', hview']
      _ = viewAt t z :=
        actualInstallationView_replace rate rewards C_star C_h control0 t z c hc
      _ = some native.selected.view := hv
  have hmap := installationRecordingMap_congr rate
    (records z')[b'.val].input.time s
    native'.selected.view native.selected.view native'.choiceInputsValid native.choiceInputsValid hv'
  change markerAt t z' = _
  have hcontrol : currentControl t z' = c := by
    simp only [z', ReferenceSourceCurrentControlFreshness.u_t,
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  change markerAt t z' =
    some (recording s native.selected.view native.choiceInputsValid c.1)
  change markerAt t z' = some
    (recording _ native'.selected.view native'.choiceInputsValid
      (currentControl t z').1) at hm'
  rw [hm', hcontrol, hmap]

private theorem splitSlice_nonassignment (v : AssignmentVector p)
    (d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p)
    (l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((sliceSplit).symm (v, d)) l.val = d l := by
  have h := congrArg (fun z => z.2 l)
    ((sliceSplit).apply_symm_apply (v, d))
  exact h

private theorem installationRecordingMap_nonassignment (s : Fin p.T)
    (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff s v.complementWeights)
    (x y : ContinuousControlSlice.Slice p.m p.K)
    (h : ∀ l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p, x l.val = y l.val) :
    recording s v valid x = recording s v valid y := by
  have hn (l : ContinuousControlSlice.NamedLabel) :
      ContinuousControlSlice.coordinate (Sum.inl l) x =
        ContinuousControlSlice.coordinate (Sum.inl l) y :=
    h ⟨Sum.inl l, by rintro ⟨r, hr⟩; cases hr⟩
  have hp (i : Fin p.m) : PublicDiscreteDraws.pilotDraw (K_pos p) i x =
      PublicDiscreteDraws.pilotDraw (K_pos p) i y := by
    unfold PublicDiscreteDraws.pilotDraw ContinuousControlSlice.coordinate
    rw [h ⟨ContinuousControlSlice.Label.pilot i, by rintro ⟨r, hr⟩; cases hr⟩]
  have hnonempty : (Finset.univ : Finset (ActiveRoundActions.Follower p.m)) ≠ ∅ := by
    have hm : 0 < p.m - 1 := by have := p.two_le_m; omega
    intro he
    have hi : (⟨0, hm⟩ : Fin (p.m - 1)) ∈
        (Finset.univ : Finset (ActiveRoundActions.Follower p.m)) := Finset.mem_univ _
    rw [he] at hi
    exact Finset.notMem_empty _ hi
  have haction (a : ContinuousControlSlice.Slice p.m p.K) (i : Fin p.m) :
      SnapshotRecordingKernel.dataAction p
        (.live v.payload.assignment (installationSnapshot v.payload.assignment))
        rate.eta.val rate.eta.property rate.sourceCap v.payload.anchor
        (sourceWeights v.payload v.complementWeights) v.payload.anchor_pos
        (sourceWeights_pos _ _ _ _ valid) (sourceWeights_lower _ _ _ _ valid)
        (sourceWeights_upper _ _ _ _ valid) a i =
          PublicDiscreteDraws.pilotDraw (K_pos p) i a := by
    by_cases hi : i = ActiveRoundActions.coordinator p.two_le_m <;>
      simp [SnapshotRecordingKernel.dataAction, installationSnapshot, hi, hnonempty]
  have hmask (i : Fin p.m) (j : Fin p.K) :
      CanonicalRecordingSlice.recordingMask (K_pos p) i j x ↔
        CanonicalRecordingSlice.recordingMask (K_pos p) i j y := by
    simp only [CanonicalRecordingSlice.recordingMask, hp]
  simp only [installationRecordingMap, SnapshotRecordingKernel.recordingMap,
    haction, hmask, hp, ContinuousControlSlice.Label.slot,
    ContinuousControlSlice.Label.rec, ContinuousControlSlice.Label.thin, hn]

private theorem map_nonassignment {Y : Type*} [MeasurableSpace Y]
    (f : ContinuousControlSlice.Slice p.m p.K → Y) (hf : Measurable f)
    (hdep : ∀ x y, (∀ l : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      x l.val = y l.val) → f x = f y) (vector : AssignmentVector p) :
    (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).map
        (fun d => f ((sliceSplit).symm (vector, d))) =
      (ContinuousControlSlice.sliceLaw p.m p.K).map f := by
  let g := fun d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
    f ((sliceSplit).symm (vector, d))
  have hg : Measurable g := hf.comp ((sliceSplit).symm.measurable.comp
    (measurable_const.prodMk measurable_id))
  have hfactor : f = g ∘ (fun a => (sliceSplit a).2) := by
    funext a
    apply hdep
    intro l
    rw [splitSlice_nonassignment]
    rfl
  have hprojection : (ContinuousControlSlice.sliceLaw p.m p.K).map
      (fun a => (sliceSplit a).2) = LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p := by
    change (ContinuousControlSlice.sliceLaw p.m p.K).map (Prod.snd ∘ sliceSplit) = _
    rw [← Measure.map_map measurable_snd (sliceSplit).measurable,
      (LaunchAssignmentCoordinateSplit.measurePreserving_sliceAssignmentSplitEquiv p).map_eq,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hprojection]
  change ((ContinuousControlSlice.sliceLaw p.m p.K).map (Prod.snd ∘ sliceSplit)).map g = _
  rw [Measure.map_map hg (measurable_snd.comp (sliceSplit).measurable)]
  exact congrArg (fun f => (ContinuousControlSlice.sliceLaw p.m p.K).map f) hfactor.symm

/-- Fixing every assignment coordinate preserves the literal snapshot law. -/
theorem installationRecordingMap_nonassignment_pushforward (s : Fin p.T) (v : View)
    (valid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff s v.complementWeights)
    (vector : AssignmentVector p) :
    (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).map
        (fun d => recording s v valid ((sliceSplit).symm (vector, d))) =
      (RecordedRoundMoments.recordingOutcomePMF
        (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
          v.payload.anchor v.payload.anchor_pos)).toMeasure := by
  exact (map_nonassignment (recording s v valid)
    (SnapshotRecordingKernel.measurable_recordingMap p _ _ _ _ _ _ _ _ _ _ true)
    (installationRecordingMap_nonassignment rate s v valid) vector).trans
      (SnapshotRecordingKernel.map_recordingMap p _ _ _ _ _ _ _ _ _ _)

private theorem splitControl_assignment (vector : AssignmentVector p) (d : Remainder) :
    ContinuousControlSlice.assignmentVector ((controlSplit).symm (vector, d)).1 = vector := by
  change (controlSplit ((controlSplit).symm (vector, d))).1 = vector
  rw [(controlSplit).apply_symm_apply]

/-- Replace only the current remainder after retaining the strict original
prefix and the entire original assignment vector. -/
def withRemainder (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p)
    (d : Remainder) : SourceInput p :=
  replaceControl t (prefix control0 t.val z) ((controlSplit).symm (vectorAt t z, d))

theorem measurable_withRemainder (control0 : TimeControl p) (t : Fin p.T) (z : SourceInput p) :
    Measurable (withRemainder control0 t z) :=
  (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
    (measurable_const.prodMk ((controlSplit).symm.measurable.comp
      (measurable_const.prodMk measurable_id)))

/-- The actual installed complement uses the unique whole original numerical
word, with every arm's physical pre-round score at this same installation. -/
theorem installationEvent_originalComplementWeights (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K)) (b : Fin (records z).length) (v : View),
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h p.T z = some L ∧
      recordAt t z = some (records z)[b.val] ∧ viewAt t z = some v ∧
      ∀ j, v.complementWeights j = AssignmentScoreReconstruction.sourceWeightBase p ^
        (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L j.val b.val).1 := by
  obtain ⟨b, hr, _ht, hb⟩ := installationEvent_chosen rate rewards C_star C_h k t z hz
  let R := records z
  have hwhole := ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
    rate rewards C_star C_h z
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
    simp only [hlaunch] at hwhole
    exact Fin.elim0 (Fin.cast (congrArg List.length hwhole.1) b)
  | some _active =>
    simp only [hlaunch] at hwhole
    obtain ⟨L, _hlen, _hprefix, hfull, _hunique, _hbirths, hbranches, _⟩ := hwhole
    obtain ⟨P, l, saved, hstate, hpending⟩ :=
      ReferenceCollectionPhaseHistory.laterChosen_pending_empty R[b.val].input hb
    have hstep := ReferenceCompleteEmptyInstallationNumericalStep.complete_empty_installation_current_numerical_step
      rate rewards C_star C_h z b
    dsimp only at hstep
    rw [hstate] at hstep
    dsimp only at hstep
    obtain ⟨u, _hu, _core, started, _hstart, instruction, _hassignment, htime, _hkind,
      _consistent, output, _hlocal, _hsuccess, clockData, installed, arm, hinstall,
      _hresult, _hdispatch, hprepared, _hpayload, _hvector, _hassignmentVector,
      _hbase, _hqueues, _hanchor, v, hselection, _hvpayload, _⟩ := hstep hpending
    have hcurrent := hbranches b
    rw [hprepared] at hcurrent
    dsimp only at hcurrent
    obtain ⟨_a, _e, _seg, _hae, _heb, _hbirth, _hseg, _hindex, _hfinal, _hempty,
      _htime, _hcutoff, _hregisters, hweights, _⟩ := hcurrent
    have hview : viewAt t z = some v.view := by
      unfold actualInstallationView
      rw [hr]
      exact installationViewOnInput_actual rate rewards C_star C_h z b hb v hselection
    refine ⟨L, b, v.view, hfull, hr, hview, ?_⟩
    rw [hprepared] at hselection
    change selectionAt R[b.val].input installed.registers.payload started instruction.time
      installed.registers.complementWeights arm = some v at hselection
    rw [ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq
      R[b.val].input installed.registers.payload started instruction.time
      installed.registers.complementWeights arm htime] at hselection
    cases hselection
    subst installed
    intro j
    change AssignmentScoreReconstruction.currentWeight output.reconstruction j.val = _
    exact congrFun hweights j.val

/-- The actual remaining-control marker pushforward at any original ranked
installation, retaining H, the complete assignment vector, and all affine
samples. The optional readout is never replaced by a successful-sampler input. -/
theorem actualMarker_remaining_pushforward (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    ∃ v : View, historyView control0 t (historyAt control0 k t z) = some v ∧
      historyParameters control0 t (historyAt control0 k t z) = some (true, v.payload.rate) ∧
      (remainderLaw).map (fun d => markerAt t (withRemainder control0 t z d)) =
        (RecordedRoundMoments.recordingOutcomePMF
          (SnapshotRecordingKernel.recordingRates p rate.eta.val rate.eta.property rate.sourceCap
            v.payload.anchor v.payload.anchor_pos)).toMeasure.map some := by
  obtain ⟨s, v, valid, _hs, hv, _hm, hall⟩ :=
    actualMarker_all_remaining_controls rate rewards C_star C_h control0 k t z hz
  have hview : historyView control0 t (historyAt control0 k t z) = some v := by
    rw [← actualInstallationView_eq_history]
    exact hv
  refine ⟨v, hview, ?_, ?_⟩
  · simp only [parametersFromHistory, hview, Option.map_some]
  let vector := vectorAt t z
  let split := controlSplit
  let scalarSplit := sliceSplit
  let g := fun d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
    recording s v valid (scalarSplit.symm (vector, d))
  have hf : Measurable (recording s v valid) :=
    SnapshotRecordingKernel.measurable_recordingMap p _ _ _ _ _ _ _ _ _ _ true
  have hg : Measurable g := hf.comp (scalarSplit.symm.measurable.comp
    (measurable_const.prodMk measurable_id))
  have hsome : Measurable (some : Option (Fin p.K) → Option (Option (Fin p.K))) :=
    measurable_of_countable _
  have hpoint (d : Remainder) : markerAt t
        (replaceControl t
          (prefix control0 t.val z)
          (split.symm (vector, d))) = some (g d.1) := by
    apply hall
    change (split (split.symm (vector, d))).1 = vector
    rw [split.apply_symm_apply]
  have hmap := installationRecordingMap_nonassignment_pushforward rate s v valid vector
  calc
    _ = (remainderLaw).map (fun d => some (g d.1)) := Measure.map_congr (Filter.Eventually.of_forall hpoint)
    _ = (((remainderLaw).map Prod.fst).map g).map some := by
      rw [Measure.map_map hsome hg, Measure.map_map (hsome.comp hg) measurable_fst]
      rfl
    _ = _ := by
      rw [ReferenceLaterOptionalControlResampling.controlRemainderLaw, Measure.map_fst_prod,
        measure_univ, one_smul, hmap]

/-- Literal optional-marker coefficient of the Borel installation data.
The inherited formula retains absent, disabled, bottom, and arm cases. -/
def markerCoefficient (control0 : TimeControl p) (t : Fin p.T)
    (o : Option (Option (Fin p.K))) (h : History p) : ℝ :=
  ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters o
    (historyParameters control0 t h)

local notation "markerMass" => markerCoefficient rate rewards C_star C_h

theorem measurable_markerCoefficient (control0 : TimeControl p) (t : Fin p.T)
    (o : Option (Option (Fin p.K))) :
    Measurable (markerMass control0 t o) :=
  (ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_coefficientOfParameters o).comp
    (measurable_parametersFromHistory rate rewards C_star C_h control0 t)

/-- Exact arm and present-bottom masses of the actual source remainder,
with the complete original assignment vector fixed and H retained. On this
event the coefficient is the actual xi, or one minus its complete sum. -/
theorem actualMarker_remaining_atom (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t)
    (o : Option (Fin p.K)) :
    remainderLaw
        {d | markerAt t (withRemainder control0 t z d) = some o} =
      ENNReal.ofReal (markerMass control0 t (some o)
        (historyAt control0 k t z)) := by
  obtain ⟨v, _hview, hparams, hpush⟩ :=
    actualMarker_remaining_pushforward rate rewards C_star C_h control0 k t z hz
  let f := fun d : Remainder => markerAt t (withRemainder control0 t z d)
  have hf : Measurable f := (measurable_actualMarker rate rewards C_star C_h t).comp
    (measurable_withRemainder control0 t z)
  have hsome : Measurable (some : Option (Fin p.K) → Option (Option (Fin p.K))) :=
    measurable_of_countable _
  have hpre : (some : Option (Fin p.K) → Option (Option (Fin p.K))) ⁻¹' {some o} = {o} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Option.some.injEq]
  have hmass := congrArg (fun ν : Measure (Option (Option (Fin p.K))) => ν {some o}) hpush
  rw [Measure.map_apply hf (measurableSet_singleton _),
    Measure.map_apply hsome (measurableSet_singleton _), hpre] at hmass
  change remainderLaw (f ⁻¹' {some o}) = _
  rw [hmass, markerCoefficient, hparams]
  cases o with
  | none =>
    rw [RecordedRoundMoments.recordingOutcomePMF_toMeasure_none]
    simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
      SnapshotRecordingKernel.recordingRates]
    simp_rw [v.payload.rate_eq_canonical]
  | some a =>
    rw [RecordedRoundMoments.recordingOutcomePMF_toMeasure_some]
    simp only [ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters,
      SnapshotRecordingKernel.recordingRates, v.payload.rate_eq_canonical]

/-- Restoring this same current control after prefixing reproduces the
actual accepted marker on the invocation event. -/
theorem actualMarker_restore_of_installation (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    markerAt t (replaceControl t (prefix control0 t.val z) (currentControl t z)) =
      markerAt t z := by
  obtain ⟨s, v, valid, _hs, _hv, hm, hall⟩ :=
    actualMarker_all_remaining_controls rate rewards C_star C_h control0 k t z hz
  exact (hall _ rfl).trans hm.symm

/-- Literal assembly in the same H carrier from its analytical prefix and
complete assignment vector. Earlier physical marks are retained, not resampled. -/
def prefixVectorHistory (control0 : TimeControl p) (t : Fin p.T)
    (x : SourceInput p × AssignmentVector p) : History p :=
  (x.1, (ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls
    rate rewards C_star C_h control0 t.val x.1, x.2))

local notation "prefixHistory" => prefixVectorHistory rate rewards C_star C_h

theorem measurable_prefixVectorHistory (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (prefixHistory control0 t) :=
  measurable_fst.prodMk
    (((ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls_measurable
      rate rewards C_star C_h control0 t.val).comp measurable_fst).prodMk measurable_snd)

theorem history_eq_prefixVectorHistory_of_installation (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ installEvent k t) :
    historyAt control0 k t z =
      prefixHistory control0 t (prefix control0 t.val z, vectorAt t z) := by
  unfold history prefixVectorHistory
  rw [markedPrefix_eq_earlierMarkedCalls_of_installation rate rewards C_star C_h
    control0 k t z hz, ReferenceCollectionEarlierMarkedPrefix.earlierMarkedCalls_factor
      rate rewards C_star C_h control0 t.val t.isLt.le z]

theorem measurable_history (control0 : TimeControl p) (k : ℕ) (t : Fin p.T) :
    Measurable (historyAt control0 k t) :=
  (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val).prodMk
    ((ReferenceCollectionRankResamplingKernel.markedPrefix_measurable
      rate rewards C_star C_h k control0).prodMk
      ((ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
        (measurable_fst.comp (ReferenceSourceCurrentControlFreshness.measurable_u_t t))))

private theorem history_remainder_product (control0 : TimeControl p) (k : ℕ) (t : Fin p.T) :
    ((mu).restrict (installEvent k t)).map
        (fun z => (historyAt control0 k t z,
          (controlSplit
            (currentControl t z)).2)) =
      (((mu).restrict (installEvent k t)).map
          (historyAt control0 k t)).prod
        (remainderLaw) := by
  let E := installEvent k t
  let μ := (mu).restrict E
  let P := prefix control0 t.val
  let U := fun z : SourceInput p => controlSplit
    (currentControl t z)
  let F := fun z : SourceInput p => (P z, U z)
  let V := ContinuousControlSlice.assignmentLaw p.K
  let R := remainderLaw
  let H := historyAt control0 k t
  let h := prefixHistory control0 t
  let G := fun q : SourceInput p × (AssignmentVector p × Remainder) =>
    (h (q.1, q.2.1), q.2.2)
  have hp : Measurable P := ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val
  have hu : Measurable U := (controlSplit).measurable.comp
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t)
  have hf : Measurable F := hp.prodMk hu
  have hh : Measurable h := measurable_prefixVectorHistory rate rewards C_star C_h control0 t
  have hg : Measurable G := (hh.comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hH : Measurable H := measurable_history rate rewards C_star C_h control0 k t
  have hsplit : μ.map F = (μ.map P).prod (V.prod R) := by
    apply Measure.ext_prod
    intro A C hA hC
    rw [Measure.map_apply hf (hA.prod hC), Measure.prod_prod, Measure.map_apply hp hA,
      Measure.restrict_apply ((hA.prod hC).preimage hf), Measure.restrict_apply (hA.preimage hp)]
    have hpast : MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t] (P ⁻¹' A) := by
      have hct : ReferenceSourceCurrentControlFreshness.c_t p control0 t = P :=
        funext (ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t)
      change MeasurableSet[(inferInstance : MeasurableSpace (SourceInput p)).comap
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t)] (P ⁻¹' A)
      rw [hct]
      exact hA.preimage (comap_measurable P)
    have hs := installation_controlSplit_cylinder rate rewards C_star C_h control0 k t
      (P ⁻¹' A) hpast C hC
    have he1 : F ⁻¹' (A ×ˢ C) ∩ E =
        {z | z ∈ E ∧ z ∈ P ⁻¹' A} ∩ U ⁻¹' C := by
      ext z
      change ((P z ∈ A ∧ U z ∈ C) ∧ z ∈ E) ↔ ((z ∈ E ∧ P z ∈ A) ∧ U z ∈ C)
      exact ⟨fun ⟨⟨ha, hc⟩, he⟩ => ⟨⟨he, ha⟩, hc⟩,
        fun ⟨⟨he, ha⟩, hc⟩ => ⟨⟨ha, hc⟩, he⟩⟩
    have he2 : P ⁻¹' A ∩ E = {z | z ∈ E ∧ z ∈ P ⁻¹' A} := by
      ext z
      exact and_comm
    rw [he1, he2]
    exact hs
  have hgraph : μ.map (fun z => (H z, (U z).2)) = (((μ.map P).prod V).map h).prod R := by
    calc
      _ = (μ.map F).map G := by
        rw [Measure.map_map hg hf]
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (measurableSet_installationEvent rate rewards C_star C_h control0 k t)] with z hz
        exact congrArg (fun x => (x, (U z).2))
          (history_eq_prefixVectorHistory_of_installation rate rewards C_star C_h control0 k t z hz)
      _ = _ := by
        rw [hsplit, ← (measurePreserving_prodAssoc (μ.map P) V R).map_eq,
          Measure.map_map hg (measurePreserving_prodAssoc (μ.map P) V R).measurable]
        change (((μ.map P).prod V).prod R).map (Prod.map h id) = _
        rw [← Measure.map_prod_map _ _ hh measurable_id, Measure.map_id]
  have hmarg := congrArg (Measure.map Prod.fst) hgraph
  rw [Measure.map_map measurable_fst
      (show Measurable (fun z => (H z, (U z).2)) from hH.prodMk (measurable_snd.comp hu)),
    Measure.map_fst_prod, measure_univ, one_smul] at hmarg
  change μ.map H = ((μ.map P).prod V).map h at hmarg
  rw [← hmarg] at hgraph
  exact hgraph

/-- Original-source Borel cylinders for the actual accepted optional marker,
conditioned on the physical H field and the literal invocation event. -/
theorem actualMarker_installation_cylinder (control0 : TimeControl p)
    (k : ℕ) (t : Fin p.T) (Aset : Set (History p)) (hA : MeasurableSet Aset)
    (o : Option (Fin p.K)) :
    ((mu).restrict (installEvent k t))
        {z | historyAt control0 k t z ∈ Aset ∧
          markerAt t z = some o} =
      ∫⁻ z in installEvent k t ∩
          (historyAt control0 k t) ⁻¹' Aset,
        ENNReal.ofReal (markerMass control0 t (some o)
          (historyAt control0 k t z))
          ∂mu := by
  let E := installEvent k t
  let μ := (mu).restrict E
  let H := historyAt control0 k t
  let R := remainderLaw
  let split := controlSplit
  let U := fun z => (split (currentControl t z)).2
  let B : Set (History p × Remainder) :=
    {q | q.1 ∈ Aset ∧ markerAt t
      (replaceControl t q.1.1
        (split.symm (q.1.2.2, q.2))) = some o}
  have hH : Measurable H := measurable_history rate rewards C_star C_h control0 k t
  have hU : Measurable U := measurable_snd.comp (split.measurable.comp
    (ReferenceSourceCurrentControlFreshness.measurable_u_t t))
  have hc : Measurable (fun q : History p × Remainder =>
      split.symm (q.1.2.2, q.2)) := split.symm.measurable.comp
    ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hb : MeasurableSet B := (hA.preimage measurable_fst).inter
    ((measurableSet_singleton (some o)).preimage
      ((measurable_actualMarker rate rewards C_star C_h t).comp
        ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
          ((measurable_fst.comp measurable_fst).prodMk hc))))
  have hm := congrArg (fun ν : Measure (History p ×
      Remainder) => ν B)
    (history_remainder_product rate rewards C_star C_h control0 k t)
  rw [Measure.map_apply (hH.prodMk hU) hb, Measure.prod_apply hb,
    lintegral_map (measurable_measure_prodMk_left hb) hH] at hm
  have hE := measurableSet_installationEvent rate rewards C_star C_h control0 k t
  calc
    _ = μ ((fun z => (H z, U z)) ⁻¹' B) := by
      apply measure_congr
      filter_upwards [ae_restrict_mem hE] with z hz
      have hr := actualMarker_restore_of_installation rate rewards C_star C_h control0 k t z hz
      have hu : split.symm (vectorAt t z, U z) = currentControl t z := split.symm_apply_apply _
      apply propext
      change (H z ∈ Aset ∧ markerAt t z = some o) ↔
        (H z ∈ Aset ∧ markerAt t
          (replaceControl t
            (prefix control0 t.val z)
            (split.symm (vectorAt t z, U z))) = some o)
      rw [hu, hr]
    _ = ∫⁻ z, R (Prod.mk (H z) ⁻¹' B) ∂μ := hm
    _ = ∫⁻ z, (H ⁻¹' Aset).indicator (fun z => ENNReal.ofReal
        (markerMass control0 t (some o) (H z))) z ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hE] with z hz
      by_cases ha : H z ∈ Aset
      · rw [Set.indicator_of_mem (show z ∈ H ⁻¹' Aset from ha)]
        change R {d | H z ∈ Aset ∧ _} = _
        simp only [ha, true_and]
        exact actualMarker_remaining_atom rate rewards C_star C_h control0 k t z hz o
      · rw [Set.indicator_of_notMem (show z ∉ H ⁻¹' Aset from ha)]
        simp only [B, Set.preimage_ofPred_eq, ha, false_and, Set.ofPred_false, measure_empty]
    _ = _ := by
      rw [lintegral_indicator (hA.preimage hH), Measure.restrict_restrict (hA.preimage hH)]
      congr 1
      exact congrArg (mu).restrict (Set.inter_comm _ _)

end Bandits.Support.ReferenceRankInstallationRecorderFoundation

end
