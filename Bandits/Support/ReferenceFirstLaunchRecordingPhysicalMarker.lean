/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstAssignmentPhysicalFibre
public import Bandits.Support.ReferenceTotalSourceDisintegration
public import Bandits.Support.ReferenceFirstLiveStoppedQueueComparison

/-!
# Actual first-launch physical recording

Sources: `sources/zip4/manuscript/06_interruptions.tex:41-64,391-397,408-423`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58,794-798`.

These internal pointwise results retain the original source, its full assignment
vector, and the actual first physical record. They assert no probability law,
adapted-history statement, stopped coupling, or manuscript closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceFirstLaunchRecordingPhysicalMarker

open ConstructorDimensions ContinuousLearningRows ContinuousControlSlice
open ReferenceActivePhysicalStep ReferenceActivePhysicalHorizon
open PublicDiscreteDraws

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev AssignmentVector := LaunchAssignmentCoordinateSplit.AssignmentVector
abbrev NonAssignmentControl (p : Parameters) :=
  LaunchAssignmentCoordinateSplit.NonAssignmentScalars p × AffineSamples p

/-- The original retained source fibre at calendar offset literally zero. -/
abbrev RetainedStart {p : Parameters}
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (control0 : TimeControl p) :=
  ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
    rate rewards C_star C_h q t t.val le_rfl control0

/-- All original assignment coordinates, including orientation, with the same
rate and actual calendar time. -/
def coordinateLaunch {p : Parameters} (rate : RateInput p)
    (t : Fin p.T) (v : AssignmentVector p) : FirstAssignmentLaunch.Input p rate.eta where
  eta_le_source_cap := rate.sourceCap
  n := rate.n
  n_eq_eta_mul_D := rate.n_scale
  sigma := t
  coordinates := v

/-- The first snapshot has all confirmations missing and all followers unoccupied. -/
def unoccupiedSnapshot {p : Parameters} (a : ActiveRoundActions.Assignment p.m p.K) :
    ActiveRoundActions.Snapshot a where
  missing := Finset.univ
  status := fun _ => .unoccupied

private theorem assignment_ext {m K : ℕ} {a b : ActiveRoundActions.Assignment m K}
    (ha : a.assigned = b.assigned) (he : a.auxiliary = b.auxiliary) : a = b := by
  cases a
  cases b
  cases ha
  cases he
  rfl

/-- Whole assignment equality uses the proved auxiliary minimum and label tie
rule, through `assignment_auxiliary_eq_first_start`; it is not definitional. -/
theorem first_payload_assignment (p : Parameters)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : FirstAssignmentLaunch.Input p eta) :
    (AssignmentStartPayload.Input.ofFirstAssignment s).assignment = s.start.assignment := by
  exact assignment_ext
    (AssignmentStartPayload.Input.assignment_map_eq_first_start s)
    (AssignmentStartPayload.Input.assignment_auxiliary_eq_first_start s)

private theorem finishFollower_downInput {p : Parameters} {rate : RateInput p}
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (prepared : DeclaredFollowerLocalRound.PreparedRound p rate)
    (observation : ReferencePrelaunchFollower.Observation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration : prepared.configuration = .ordinary state memory) :
    (ReferenceActivePhysicalStep.finishFollower view prepared observation).downInput =
      (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
        prepared.activation prepared.time prepared.active prepared.arm observation state).downInput := by
  unfold ReferenceActivePhysicalStep.finishFollower
  rw [hconfiguration]
  cases hr : (ReferenceActivePhysicalStep.recordFollower view prepared.follower prepared.row
      prepared.activation prepared.time prepared.active prepared.arm observation state).result with
  | error failure => simp only [hr]
  | ok postRecord =>
      cases hf : DeclaredFollowerLocalRound.releaseAndFinish rate prepared.follower prepared.row
        prepared.time observation state memory postRecord <;> simp only [hr, hf]

/-- The deterministic first-snapshot recorder with unit anchor and current weights. -/
def unitRecordingMap {p : Parameters} (rate : RateInput p)
    (assignment : ActiveRoundActions.Assignment p.m p.K)
    (slice : ContinuousControlSlice.Slice p.m p.K) : Option (Fin p.K) :=
  SnapshotRecordingKernel.recordingMap p (.live assignment (unoccupiedSnapshot assignment))
    true rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
    (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) slice

private theorem unoccupied_missing_nonempty (p : Parameters) :
    (Finset.univ : Finset (ActiveRoundActions.Follower p.m)) ≠ ∅ := by
  have hm := p.two_le_m
  let i : ActiveRoundActions.Follower p.m := ⟨0, by
    simp only [followerCount]
    omega⟩
  exact Finset.ne_empty_of_mem (Finset.mem_univ i)

private theorem unit_data_action {p : Parameters} (rate : RateInput p)
    (assignment : ActiveRoundActions.Assignment p.m p.K)
    (slice : ContinuousControlSlice.Slice p.m p.K) (player : Fin p.m) :
    SnapshotRecordingKernel.dataAction p (.live assignment (unoccupiedSnapshot assignment))
      rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) slice player = pilotDraw (K_pos p) player slice := by
  by_cases hc : player = ActiveRoundActions.coordinator p.two_le_m <;>
    simp [SnapshotRecordingKernel.dataAction, unoccupiedSnapshot, hc,
      unoccupied_missing_nonempty p]

private theorem record_preparation_eq {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
  rw [record.output_eq]
  rfl

private theorem unoccupied_marker_iff {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (hcheck : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (followerPlayer p.two_le_m i)) state = .ok logged)
    (hdown : (record.output.followers i).downInput = some logged)
    (happend : logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record)
    (hemission : ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row (record.input.state.activations i)
        record.input.time (record.output.ownEntries (followerPlayer p.two_le_m i))) :
    ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record payload i state =
        some (payload.assignment.assigned i) ↔
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (followerPlayer p.two_le_m i))) ∧
      (record.output.ownEntries (followerPlayer p.two_le_m i)).1 = payload.assignment.assigned i ∧
      ((record.input.row.2 record.input.time).1 Label.thin).val ≤
        ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold payload
          (payload.assignment.assigned i) := by
  classical
  let own := record.output.ownEntries (followerPlayer p.two_le_m i)
  let emission := ReferenceFollowerBufferProvenance.logEmission i record
  let arm := payload.assignment.assigned i
  have hphysical :
      ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record payload i state =
          some arm ↔
        ∃ saved, saved ∈ emission ∧ saved ∈ logged.buffer ∧
          saved.calendarRound = record.input.time.val + 1 ∧ saved.pilot = arm ∧
          saved.thinScalar ≤
            ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold payload arm := by
    simp [ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker, hdown,
      hcheck, happend, emission, arm]
  rw [hphysical]
  constructor
  · rintro ⟨saved, hmem, _, _, hpilot, hthin⟩
    change saved ∈ ReferenceFollowerBufferProvenance.logEmission i record at hmem
    rw [hemission, ReferencePrelaunchFollower.mem_logAt_iff] at hmem
    rcases hmem with ⟨htests, rfl⟩
    exact ⟨htests, hpilot, hthin⟩
  · rintro ⟨htests, hownArm, hthin⟩
    let saved := SparseCalendarReplay.recordAt (record.input.time.val + 1)
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time own)
    have hmem : saved ∈ emission := by
      change saved ∈ ReferenceFollowerBufferProvenance.logEmission i record
      rw [hemission, ReferencePrelaunchFollower.mem_logAt_iff]
      exact ⟨htests, rfl⟩
    refine ⟨saved, hmem, ?_, rfl, hownArm, hthin⟩
    rw [happend]
    exact List.mem_append_right _ hmem

private theorem unoccupied_marker_eq_map {p : Parameters} {rate : RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1))
    (state logged : ReferencePrelaunchFollower.State p rate.eta)
    (hcheck : ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (followerPlayer p.two_le_m i)) state = .ok logged)
    (hdown : (record.output.followers i).downInput = some logged)
    (happend : logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record)
    (hemission : ReferenceFollowerBufferProvenance.logEmission i record =
      ReferencePrelaunchFollower.logAt i record.input.row (record.input.state.activations i)
        record.input.time (record.output.ownEntries (followerPlayer p.two_le_m i)))
    (hsource : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (coordinate Label.rec (record.input.row.2 record.input.time).1) = followerPlayer p.two_le_m i)
    (hownData : slotDraw (record.input.row.2 record.input.time).1 = dataSlot →
      (record.output.ownEntries (followerPlayer p.two_le_m i)).1 =
        pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (record.input.row.2 record.input.time).1)
    (hdyadic : OrdinaryMessageCodec.dyadicRate (payload.exponent (payload.assignment.assigned i)) =
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) (payload.assignment.assigned i)) :
    ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record payload i state =
      unitRecordingMap rate payload.assignment (record.input.row.2 record.input.time).1 := by
  classical
  let player := followerPlayer p.two_le_m i
  let arm := payload.assignment.assigned i
  let slice := (record.input.row.2 record.input.time).1
  let regime := SnapshotRecordingKernel.Regime.live payload.assignment
    (unoccupiedSnapshot payload.assignment)
  have hne : player ≠ ActiveRoundActions.coordinator p.two_le_m :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hne
  have haction : ∀ slice, SnapshotRecordingKernel.dataAction p regime rate.eta.val
      rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) slice player = pilotDraw (K_pos p) player slice := by
    intro slice
    simp [SnapshotRecordingKernel.dataAction, regime, unoccupiedSnapshot, player, hne]
  have howner : SnapshotRecordingKernel.owns p regime player arm := by
    simp [SnapshotRecordingKernel.owns, regime, player, arm, hne, hindex]
  have hprob : SnapshotRecordingKernel.actionProbability p regime rate.eta.val
      rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) player arm = 1 / (p.K : ℝ) := by
    simp [SnapshotRecordingKernel.actionProbability, regime, unoccupiedSnapshot, player, hne]
  have hmapGate := SnapshotRecordingKernel.recordingMap_pilot_event_eq p regime
    rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
    (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) player arm howner haction hprob
  have hmapIff : unitRecordingMap rate payload.assignment slice = some arm ↔
      CanonicalRecordingSlice.pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) player arm
        (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) arm /
          CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K) player) slice :=
    Iff.of_eq (congrArg (fun set : Set (ContinuousControlSlice.Slice p.m p.K) => slice ∈ set) hmapGate)
  have hthreshold : CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) arm /
      CanonicalRecordingSlice.pilotRecordingGateRawProbability (K := p.K) player =
      ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold payload arm := by
    rw [CanonicalRecordingSlice.unoccupiedFollower_savedThreshold_eq p (fun _ => 1) i arm,
      CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability, ← hdyadic]
    rfl
  have hgate : ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker
      record payload i state = some arm ↔ unitRecordingMap rate payload.assignment slice = some arm := by
    rw [unoccupied_marker_iff record payload i state logged hcheck hdown happend hemission, hmapIff]
    rw [ActiveFollowerLogging.loggingTestsPass_iff_source_mask]
    have hrec : recorderSourceDraw p.two_le_m p.m_lt_K slice = player := by
      rw [← CanonicalRecordingSlice.recorderSourceFromScalar_coordinate]
      exact hsource
    rw [hthreshold]
    constructor
    · rintro ⟨⟨_, hdata, _, hmask⟩, hown, hthin⟩
      refine ⟨hdata, hrec, (hownData hdata).symm.trans hown, ?_, hthin⟩
      change ∀ ell : Fin p.m, ell ≠ player → pilotDraw (K_pos p) ell slice ≠ arm
      simpa only [hown] using hmask
    · rintro ⟨hdata, _, hpilot, hmask, hthin⟩
      have hown := (hownData hdata).trans hpilot
      refine ⟨⟨record.input.active i, hdata, hrec, ?_⟩, hown, hthin⟩
      change ∀ ell : Fin p.m, ell ≠ player → pilotDraw (K_pos p) ell slice ≠ arm at hmask
      simpa only [hown] using hmask
  apply Option.ext
  intro j
  have hphysicalRange :
      ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker record payload i state =
          some j → j = arm := by
    intro hj
    simp [ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker, hdown] at hj
    exact hj.2.symm
  have hmapRange : unitRecordingMap rate payload.assignment slice = some j → j = arm := by
    intro hj
    have howns := (SnapshotRecordingKernel.recordingMap_some_iff p regime
      rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) slice j).mp hj |>.2.2.1
    have hsource' : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec slice) = player := hsource
    simpa [SnapshotRecordingKernel.owns, regime, hsource', player, hne, hindex] using howns
  constructor
  · intro hj
    have hid := hphysicalRange hj
    subst j
    exact hgate.mp hj
  · intro hj
    have hid := hmapRange hj
    subst j
    exact hgate.mpr hj

section OriginalSource

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
variable (q : Fin (M p)) (t : Fin p.T) (control0 : TimeControl p)
variable (x : RetainedStart rate rewards C_star C_h q t control0)
variable (v : AssignmentVector p) (d : NonAssignmentControl p)

/-- Invert the existing full assignment/nonassignment split, retaining every affine sample. -/
def currentControl : TimeControl p :=
  (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm (v, d)

/-- Restore the original IDs, full rows, private arrays and private selected index. -/
def source : BootstrapPrivateRoundStreams.SourceInput p :=
  ReferenceGeneratedActivePrefixFactor.splitSource q t (currentControl v d) x.val

local notation "z" => source rate rewards C_star C_h q t control0 x v d
local notation "u" => currentControl v d

/-- The crossing and exact elapsed time are consequences of the retained fibre. -/
theorem source_crossing :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = t.val := by
  have hstart :=
    (ReferenceRetainedBoundaryMeasurability.launchStart_control_independent_on_remainder
      rate rewards C_star C_h q t t.val x.val x.property.1 control0 u).mp x.property.2
  exact ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t u x.val x.property.1 t.val le_rfl hstart

/-- The original selected row's whole current control is exactly the reconstructed control. -/
theorem source_current_control : (z.1.2 q).2 t = u :=
  ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_control p q t u x.val

theorem source_elapsed_lt :
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed < p.T := by
  rw [(source_crossing rate rewards C_star C_h q t control0 x v d).2]
  exact t.isLt

/-- The literal actual first physical record, at offset zero, on the original source. -/
def record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
  ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z rewards C_star C_h
    (source_crossing rate rewards C_star C_h q t control0 x v d).1
    (source_elapsed_lt rate rewards C_star C_h q t control0 x v d)

local notation "r" => record rate rewards C_star C_h q t control0 x v d

/-- The launch input read by the actual first dispatcher. -/
def launchInput : FirstAssignmentLaunch.Input p rate.eta :=
  CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput (r).input)

/-- The literal payload of that same first launch. -/
def payload : ReferenceActivePhysicalStep.Payload rate :=
  AssignmentStartPayload.Input.ofFirstAssignment
    (launchInput rate rewards C_star C_h q t control0 x v d)

local notation "P" => payload rate rewards C_star C_h q t control0 x v d

/-- The carried ordinary source states; buffers and failure flags are preserved. -/
def states (i : Fin (p.m - 1)) : ReferencePrelaunchFollower.State p rate.eta :=
  let init := ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate
  ReferenceInitializationRun.ordinary init (ReferenceInitializationRun.output init)
    (ActualReferenceInitializationBlock.refFollower i)

local notation "s₀" => states rate rewards C_star C_h q t control0 x v d

/-- The source's original J, whole row array, time and reward table are the
actual record inputs. Its state is the genuine corrected first-launch seed. -/
theorem record_source_inputs :
    (r).input.state = ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
        (source_crossing rate rewards C_star C_h q t control0 x v d).1 ∧
      (r).input.rows = z.1.2 ∧ (r).input.selected = q ∧ (r).input.time = t ∧
      (r).input.rewards = rewards := by
  have hindex : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t u x.val x.property.1
  obtain ⟨hstate, htime, hrows, hselected, hrewards⟩ :=
    ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_source_inputs rate z rewards C_star C_h
      (source_crossing rate rewards C_star C_h q t control0 x v d).1
      (source_elapsed_lt rate rewards C_star C_h q t control0 x v d)
  refine ⟨hstate, hrows, hselected.trans hindex, ?_, hrewards⟩
  apply Fin.ext
  exact htime.trans (source_crossing rate rewards C_star C_h q t control0 x v d).2

/-- The actual first input retains the entire original assignment vector. -/
theorem launchInput_eq_coordinates :
    launchInput rate rewards C_star C_h q t control0 x v d = coordinateLaunch rate t v := by
  obtain ⟨_, hrows, hselected, htime, _⟩ :=
    record_source_inputs rate rewards C_star C_h q t control0 x v d
  have hcontrol := source_current_control rate rewards C_star C_h q t control0 x v d
  have hcoordinates : LaterAssignmentStartOperation.ownAssignmentVector (z.1.2 q) t = v := by
    funext i
    rw [LaterAssignmentStartOperation.ownAssignmentVector_apply]
    have hsplit := congrArg Prod.fst
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply (v, d))
    change ContinuousControlSlice.assignmentVector u.1 = v at hsplit
    change ((z.1.2 q).2 t).1 (Label.assign i) = v i
    rw [hcontrol]
    exact congrFun hsplit i
  have hrow : (r).input.row = z.1.2 q := by
    simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected]
  simp only [launchInput, CoordinatorRoundDispatch.firstLaunchInput,
    ReferenceActivePhysicalStep.firstInput, htime, hrow, hcoordinates, coordinateLaunch]

theorem payload_assignment : (P).assignment = (coordinateLaunch rate t v).start.assignment := by
  rw [payload, first_payload_assignment, launchInput_eq_coordinates]

/-- The current slice of the actual record is exactly the original reconstructed slice. -/
theorem record_slice : ((r).input.row.2 (r).input.time).1 = u.1 := by
  obtain ⟨_, hrows, hselected, htime, _⟩ :=
    record_source_inputs rate rewards C_star C_h q t control0 x v d
  simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hselected, htime,
    source_current_control rate rewards C_star C_h q t control0 x v d]

/-- Full ordinary zero seed facts, with genuine carried buffer, memory and flags. -/
theorem record_seed :
    (r).input.state.coordinator = .first ∧
      (r).input.state.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      (∀ i, (r).input.state.followers i =
        .ordinary (s₀ i) (ActiveFollowerLifecycle.initialMemory p)) ∧
      (∀ i, (s₀ i).lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart (s₀ i) = 0 ∧
        (s₀ i).S = 0 ∧ (s₀ i).delta = 0 ∧ (s₀ i).backlog = 0 ∧
        (s₀ i).status = .unoccupied ∧ ActiveFollowerLifecycle.localStateDomainValid (s₀ i) ∧
        ActiveFollowerLifecycle.localBufferValid (s₀ i) ∧
        (s₀ i).buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound) ∧
        ∀ saved ∈ (s₀ i).buffer, saved.calendarRound ≤ t.val) := by
  obtain ⟨_, _, _, hcoord, hbank, _, _, hf⟩ :=
    ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h
      (source_crossing rate rewards C_star C_h q t control0 x v d).1
  have hstate := (record_source_inputs rate rewards C_star C_h q t control0 x v d).1
  refine ⟨hstate ▸ hcoord, hstate ▸ hbank, ?_, ?_⟩
  · intro i
    rw [hstate]
    exact (hf i).1
  · intro i
    rcases (hf i).2 with ⟨hlast, haccept, hS, hdelta, hbacklog, hu, hdomain, hv, hp, ht⟩
    refine ⟨hlast, haccept, hS, hdelta, hbacklog, hu, hdomain, hv, hp, ?_⟩
    intro saved hmem
    have hle := ht saved hmem
    rw [(source_crossing rate rewards C_star C_h q t control0 x v d).2] at hle
    exact hle

/-- PREPARE preserves the genuine unoccupied ordinary seed on every slot and affine sample. -/
theorem record_prepared (i : Fin (p.m - 1)) :
    ((r).output.preparation.followers.followers i).configuration =
      .ordinary (s₀ i) (ActiveFollowerLifecycle.initialMemory p) :=
  ReferenceFirstLaunchNumericalCell.firstPhysicalRecord_prepared_seed
    rate z rewards C_star C_h
    (source_crossing rate rewards C_star C_h q t control0 x v d).1
    (source_elapsed_lt rate rewards C_star C_h q t control0 x v d) i

/-- The real first dispatcher always produces an installation and arm selection. -/
theorem dispatch_chosen_exists :
    ∃ (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (launchInput rate rewards C_star C_h q t control0 x v d))
      (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
        installed.startRoundResult installed.registers.time installed.registers.complementWeights
        (r).input.row),
      CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput (r).input) =
        .chosen installed arm ∧
      (r).output.preparation.coordinator = .first (.chosen installed arm) ∧
      installed.registers.time = (r).input.time ∧
      CoordinatorLocalArmChoice.assignmentIsLive installed.registers.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p installed.startRoundResult.clock.u)
        (r).input.time ∧
      (r).input.time.val + 1 < installed.startRoundResult.clock.g ∧
      installed.registers.payload.sigma.val = (r).input.time.val := by
  obtain ⟨installed, arm, hchosen⟩ := ReferenceFirstAssignmentFibreStep.dispatchFirst_chosen_exists
    (ReferenceActivePhysicalStep.firstInput (r).input)
  obtain ⟨hdispatch, htime, hlive, hstrict, hsigma⟩ :=
    ReferenceFirstLaunchNumericalCell.first_launch_call_frame rate z rewards C_star C_h
      (source_crossing rate rewards C_star C_h q t control0 x v d).1
      (source_elapsed_lt rate rewards C_star C_h q t control0 x v d) installed arm hchosen
  refine ⟨installed, arm, hchosen, ?_, htime, hlive, hstrict, hsigma⟩
  rw [(r).output_eq]
  exact hdispatch

/-- This is the existing generated corrected seed, obtained from equality of
its actual nonempty corrected-launch option. -/
theorem seed_eq_generated :
    let hstart := (ReferenceRetainedBoundaryMeasurability.launchStart_control_independent_on_remainder
      rate rewards C_star C_h q t t.val x.val x.property.1 control0 u).mp x.property.2
    ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h
        (source_crossing rate rewards C_star C_h q t control0 x v d).1 =
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
        rate rewards C_star C_h q t u x.val x.property.1 t.val le_rfl hstart := by
  intro hstart
  exact Option.some.inj
    ((ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z rewards C_star C_h
      (source_crossing rate rewards C_star C_h q t control0 x v d).1).symm.trans
      (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t u x.val x.property.1 t.val le_rfl hstart).1)

private theorem roundInput_ext {p : Parameters} {rate : RateInput p}
    {a b : ReferenceActivePhysicalStep.RoundInput p rate}
    (hs : a.state = b.state) (hr : a.rows = b.rows) (hj : a.selected = b.selected)
    (ht : a.time = b.time) (hw : a.rewards = b.rewards) : a = b := by
  cases a
  cases b
  simp_all

/-- Whole current-input identity at n=0; no supplied matching-history premise. -/
theorem record_eq_generated_next_input :
    (r).input = ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t t.val le_rfl control0 x u := by
  obtain ⟨hstate, hrows, _, htime, hrewards⟩ :=
    record_source_inputs rate rewards C_star C_h q t control0 x v d
  apply roundInput_ext
  · rw [hstate]
    simpa only [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput,
      Nat.sub_self, ReferenceActivePhysicalHorizon.roundInputAt,
      ReferenceActivePhysicalHorizon.run_zero_final] using
      seed_eq_generated rate rewards C_star C_h q t control0 x v d
  · exact hrows
  · rfl
  · exact htime
  · exact hrewards

/-- Restoring the original full rows and J in B's incoming boundary gives
exactly this actual first physical input. -/
theorem record_eq_roundInputAtSource :
    (r).input = ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t t.val le_rfl control0 x) z := by
  rw [record_eq_generated_next_input]
  exact ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_roundInputAtSource
    rate rewards C_star C_h q t t.val le_rfl control0 x u

/-- Every actual logging call succeeds on this initial chronological buffer.
The retained DOWN input is the same checked logged state, even on finish errors. -/
theorem record_logged (i : Fin (p.m - 1)) :
    ∃ logged,
      ActiveFollowerLogging.checkedLogging i (r).input.row
        ((r).input.state.activations i) (r).input.time
        ((r).output.ownEntries (followerPlayer p.two_le_m i)) (s₀ i) = .ok logged ∧
      ((r).output.followers i).downInput = some logged ∧
      logged.buffer = (s₀ i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i r ∧
      ReferenceFollowerBufferProvenance.logEmission i r =
        ReferencePrelaunchFollower.logAt i (r).input.row
          ((r).input.state.activations i) (r).input.time
          ((r).output.ownEntries (followerPlayer p.two_le_m i)) ∧
      ActiveFollowerLifecycle.localBufferValid logged := by
  classical
  have hprepared := record_prepared rate rewards C_star C_h q t control0 x v d i
  have hfields := (record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i
  rcases hfields with ⟨_, _, _, _, _, hstatus, _, hvalid, _, hstamps⟩
  have hbefore : ∀ saved ∈ (s₀ i).buffer,
      saved.calendarRound < (r).input.time.val + 1 := by
    intro saved hmem
    have hle := hstamps saved hmem
    rw [(record_source_inputs rate rewards C_star C_h q t control0 x v d).2.2.2.1]
    omega
  obtain ⟨logged, hcheck, _, happend, hvalid'⟩ :=
    ReferenceFollowerBufferProvenance.actualPreparedLogging_success
      i r (s₀ i) (ActiveFollowerLifecycle.initialMemory p) hprepared hvalid hbefore hstatus
  have halign := (r).output.preparation.follower_alignment i
  have hown := ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared i r
  have hcheckPrepared : ActiveFollowerLogging.checkedLogging
      ((r).output.preparation.followers.followers i).follower
      ((r).output.preparation.followers.followers i).row
      ((r).output.preparation.followers.followers i).activation
      ((r).output.preparation.followers.followers i).time
      (((r).output.preparation.followers.followers i).arm,
        (r).output.preparation.feedback.observations (followerPlayer p.two_le_m i))
      (s₀ i) = .ok logged := by
    rw [halign.2.1, halign.1, halign.2.2.2, halign.2.2.1, ← hown]
    exact hcheck
  have hlogged := ReferenceActivePhysicalStep.recordFollower_logged
    (r).output.preparation.coordinator.downView
    ((r).output.preparation.followers.followers i).follower
    ((r).output.preparation.followers.followers i).row
    ((r).output.preparation.followers.followers i).activation
    ((r).output.preparation.followers.followers i).time
    ((r).output.preparation.followers.followers i).active
    ((r).output.preparation.followers.followers i).arm
    ((r).output.preparation.feedback.observations (followerPlayer p.two_le_m i))
    (s₀ i) logged hstatus hcheckPrepared
  have hdown : ((r).output.followers i).downInput = some logged := by
    rw [ReferenceFollowerBufferProvenance.roundRecord_follower_eq_finishFollower i r,
      finishFollower_downInput _ _ _ _ _ hprepared]
    exact hlogged.1
  refine ⟨logged, hcheck, hdown, happend, ?_, hvalid'⟩
  simp only [ReferenceFollowerBufferProvenance.logEmission, hprepared, hstatus, dite_true]

/-- The actual first selection, with all first-snapshot and current-weight
conditions proved at the unrestricted source root. -/
theorem selection_exists :
    ∃ selected : ReferenceActivePhysicalStep.Selection (r).input,
      (r).output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = P ∧
      selected.view.pendingAtChoice = Finset.univ ∧
      selected.view.cutoff = none ∧
      (∀ j, selected.view.complementWeights j = 1) ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff (r).input.time ∧
      CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload selected.view.cutoff
        (r).input.time selected.view.complementWeights := by
  obtain ⟨installed, arm, hchosen, hbranch, htime, hlive, _, _⟩ :=
    dispatch_chosen_exists rate rewards C_star C_h q t control0 x v d
  have hu : ∀ i, (s₀ i).status = .unoccupied := fun i =>
    ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
  obtain ⟨_, selected, hselected, hselection, _, _, _⟩ :=
    ReferenceFirstWindowRecordingTruth.first_branch_recording_truth r installed arm hbranch
      s₀ (fun _ => ActiveFollowerLifecycle.initialMemory p)
      (record_prepared rate rewards C_star C_h q t control0 x v d)
      (fun i hi => False.elim (hi (hu i)))
  have hi := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    (r).input installed arm hchosen
  subst selected
  subst installed
  refine ⟨_, hselected, rfl, rfl, rfl, ?_, hlive, arm.choiceInputsValid⟩
  intro j
  exact CoordinatorAssignmentRegisterInstall.first_complementWeight_one _ j

/-- The actual whole marker: coordinator recording or the unoccupied source's
current saved-log candidate. -/
def physicalMarker : Option (Fin p.K) :=
  ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord r P true

local notation "Iphys" => physicalMarker rate rewards C_star C_h q t control0 x v d

/-- On DATA, every actual unoccupied follower uses its own pilot. -/
theorem follower_data_pilot (i : Fin (p.m - 1))
    (hdata : slotDraw ((r).input.row.2 (r).input.time).1 = dataSlot) :
    ((r).output.ownEntries (followerPlayer p.two_le_m i)).1 =
      pilotDraw (K_pos p) (followerPlayer p.two_le_m i) ((r).input.row.2 (r).input.time).1 := by
  have hprepared := record_prepared rate rewards C_star C_h q t control0 x v d i
  have hu := ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
  have hlocal : (r).output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i (r).input.row ((r).input.state.activations i)
        (r).input.time ((r).input.active i) ((r).input.state.followers i) := by
    rw [(r).output_eq]
    rfl
  have hconfig : (DeclaredFollowerLocalRound.prepare rate i (r).input.row
      ((r).input.state.activations i) (r).input.time ((r).input.active i)
      ((r).input.state.followers i)).configuration =
        .ordinary (s₀ i) (ActiveFollowerLifecycle.initialMemory p) := by
    rw [← hlocal]
    exact hprepared
  have ha := ReferenceActiveDataOwnership.ordinary_data_arm P i (r).input.row
    ((r).input.state.activations i) (r).input.time ((r).input.active i)
    ((r).input.state.followers i) (s₀ i) (ActiveFollowerLifecycle.initialMemory p)
    hconfig (fun h => False.elim (h hu)) hdata
  rw [ReferenceFollowerBufferProvenance.round_ownEntry_eq_prepared i r, hlocal]
  simpa only [hu, ite_true] using ha

theorem payload_anchor : (P).anchor = fun _ => 1 := rfl

theorem payload_rate (j : Fin p.K) :
    (P).rate j = CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j :=
  (P).rate_eq_canonical j

/-- The entire actual physical marker equals the canonical first-snapshot
map, including current saved candidates from unoccupied followers. -/
theorem physical_marker_eq :
    Iphys = unitRecordingMap rate (coordinateLaunch rate t v).start.assignment u.1 := by
  classical
  suffices h : Iphys = unitRecordingMap rate (P).assignment
      ((r).input.row.2 (r).input.time).1 by
    rw [h, payload_assignment, record_slice]
  let slice := ((r).input.row.2 (r).input.time).1
  let src := CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
    (coordinate Label.rec slice)
  by_cases hdata : slotDraw slice = dataSlot
  · by_cases hcoord : src = ActiveRoundActions.coordinator p.two_le_m
    · obtain ⟨installed, arm, hchosen, hbranch, _, _, hstrict, _⟩ :=
        dispatch_chosen_exists rate rewards C_star C_h q t control0 x v d
      have hu : ∀ i, (s₀ i).status = .unoccupied := fun i =>
        ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
      obtain ⟨_, _, _, _, _, _, out, hrecording, hrun, hgate, _⟩ :=
        ReferenceFirstWindowRecordingTruth.first_branch_recording_truth r installed arm hbranch
          s₀ (fun _ => ActiveFollowerLifecycle.initialMemory p)
          (record_prepared rate rewards C_star C_h q t control0 x v d)
          (fun i hi => False.elim (hi (hu i)))
      let input := ReferenceActivePhysicalStep.liveRecordingInput
        (ReferenceActivePhysicalStep.prepare (r).input) installed.registers installed.startRoundResult
      have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen input := by
        intro hfrozen
        have hlate : (r).input.time.val + 1 ≥ installed.startRoundResult.clock.g := by
          exact hfrozen.2
        exact (not_le_of_gt hstrict) hlate
      have henabled : decide (¬ CoordinatorRecorderComplementBridge.isFrozen input) = true :=
        decide_eq_true hnotFrozen
      have hsourceI : CoordinatorRecordingOperation.selectedRecorder
          (CoordinatorRecorderComplementBridge.recorderInput input) = src := rfl
      have hi := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
        (r).input installed arm hchosen
      have hP : installed.registers.payload = P := by rw [hi]; rfl
      have hcomp : ∀ j, installed.registers.complementWeights j = 1 := by
        subst installed
        exact CoordinatorAssignmentRegisterInstall.first_complementWeight_one _
      have hweights : CoordinatorRecorderComplementBridge.extendedCurrentWeights input =
          fun _ => 1 := by
        funext j
        dsimp only [CoordinatorRecorderComplementBridge.extendedCurrentWeights, input,
          ReferenceActivePhysicalStep.liveRecordingInput]
        split
        · rw [hP]
          rfl
        · exact hcomp _
      have hpending : installed.startRoundResult.pending = Finset.univ := by rw [hi]; rfl
      have hsnapshot :
          (⟨installed.startRoundResult.pending, fun i => (s₀ i).status⟩ :
            ActiveRoundActions.Snapshot installed.registers.payload.assignment) =
          unoccupiedSnapshot installed.registers.payload.assignment := by
        exact congrArg₂ (fun missing status =>
          (⟨missing, status⟩ : ActiveRoundActions.Snapshot installed.registers.payload.assignment))
          hpending (funext hu)
      have hregime := congrArg (fun a : ActiveRoundActions.Assignment p.m p.K =>
        SnapshotRecordingKernel.Regime.live a (unoccupiedSnapshot a))
        (congrArg AssignmentStartPayload.Input.assignment hP)
      have hmap : out.gateArm = unitRecordingMap rate (P).assignment slice := by
        let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid input
          (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
            (ReferenceActivePhysicalStep.prepare (r).input) installed.registers
            installed.startRoundResult installed.registers.time arm)
        have hgate' : out.gateArm = CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
            (CoordinatorRecorderComplementBridge.recorderInput input) valid
            installed.registers.payload.assignment
            { missing := installed.startRoundResult.pending, status := fun i => (s₀ i).status }
            (decide (¬ CoordinatorRecorderComplementBridge.isFrozen input)) := hgate
        rw [hgate']
        simp only [CoordinatorRecordingOperation.liveCoordinatorSourceMapPart,
          hsourceI, hcoord, ite_true, henabled]
        simp only [CoordinatorRecorderComplementBridge.recorderInput,
          CoordinatorRecorderComplementBridge.recorderInputWithWeights]
        change SnapshotRecordingKernel.recordingMap p
          (.live installed.registers.payload.assignment
            { missing := installed.startRoundResult.pending, status := fun i => (s₀ i).status })
          true rate.eta.val rate.eta.property rate.sourceCap installed.registers.payload.anchor
          (CoordinatorRecorderComplementBridge.extendedCurrentWeights input) _ _ _ _ slice = _
        rw [hsnapshot, hregime]
        simp only [hweights, hP, payload_anchor, unitRecordingMap]
      calc
        Iphys = out.gateArm := by
          simp [physicalMarker, ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord,
            ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord,
            slice, src, hdata, hcoord, hrecording]
        _ = unitRecordingMap rate (P).assignment slice := hmap
    · let i := ActiveRoundActions.followerIndex p.two_le_m src hcoord
      have hplayer : followerPlayer p.two_le_m i = src :=
        ActiveRoundActions.followerPlayer_followerIndex p.two_le_m src hcoord
      obtain ⟨logged, hcheck, hdown, happend, hemits, _⟩ :=
        record_logged rate rewards C_star C_h q t control0 x v d i
      have hdyadic : OrdinaryMessageCodec.dyadicRate ((P).exponent ((P).assignment.assigned i)) =
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) ((P).assignment.assigned i) :=
        ((P).dyadicRate_eq_rate _).trans (payload_rate rate rewards C_star C_h q t control0 x v d _)
      have hmap := unoccupied_marker_eq_map r P i (s₀ i) logged hcheck hdown happend hemits
        hplayer.symm (follower_data_pilot rate rewards C_star C_h q t control0 x v d i) hdyadic
      have hprepared := record_prepared rate rewards C_star C_h q t control0 x v d i
      have hu := ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
      calc
        Iphys = ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker r P i (s₀ i) := by
          have hphys : Iphys = ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
              r P src := by
            simp only [physicalMarker, ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord,
              show slotDraw ((r).input.row.2 (r).input.time).1 = dataSlot from hdata,
              dite_true]
            rfl
          rw [hphys]
          unfold ReferenceContinuingRecordingFastPair.physicalDataMarkerOnRecord
          rw [dite_eq_right hcoord]
          change (match ((r).output.preparation.followers.followers i).configuration with
            | .dagger => none
            | .ordinary state _ =>
                if state.status = ActiveRoundActions.FollowerStatus.unoccupied then
                  ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker r P i state
                else
                  match state.lastDown with
                  | none => none
                  | some down => if ActiveFollowerQueueOperation.recorderGate rate.eta i
                      (r).input.row (r).input.time down then
                      some (PrelaunchBufferRecovery.downArm rate.eta down) else none) = _
          rw [hprepared]
          simp only [hu, ite_true]

        _ = unitRecordingMap rate (P).assignment slice := hmap
  · simp [physicalMarker, ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord,
      unitRecordingMap, SnapshotRecordingKernel.recordingMap,
      CanonicalRecordingSlice.slotFromScalar_coordinate, slice, hdata]

/-- All actual first-round DATA actions are the original individual pilots. -/
theorem data_actions (hdata : slotDraw ((r).input.row.2 (r).input.time).1 = dataSlot)
    (player : Fin p.m) :
    (ReferenceActivePhysicalStep.prepare (r).input).arms.actions player =
      pilotDraw (K_pos p) player ((r).input.row.2 (r).input.time).1 := by
  obtain ⟨selected, hselected, _, hpending, _, _, hlive, _⟩ :=
    selection_exists rate rewards C_star C_h q t control0 x v d
  have hprep := record_preparation_eq r
  by_cases hc : player = ActiveRoundActions.coordinator p.two_le_m
  · subst player
    rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator, ← hprep,
      ReferenceActivePhysicalStep.DispatchCut.arm, hselected]
    exact (ReferenceActiveDataOwnership.selected_data_coordinator selected hlive hdata).1 (by
      rw [← selected.pending_eq, hpending]
      exact unoccupied_missing_nonempty p)
  · let i := ActiveRoundActions.followerIndex p.two_le_m player hc
    have hi : followerPlayer p.two_le_m i = player :=
      ActiveRoundActions.followerPlayer_followerIndex p.two_le_m player hc
    rw [← hi]
    have hown : ((r).output.ownEntries (followerPlayer p.two_le_m i)).1 =
        (ReferenceActivePhysicalStep.prepare (r).input).arms.actions
          (followerPlayer p.two_le_m i) := by
      rw [(r).output_eq, ReferenceActivePhysicalStep.step_own_entry]
    rw [← hown]
    exact follower_data_pilot rate rewards C_star C_h q t control0 x v d i hdata

/-- The actual recorder-source coordinate, on the same original whole slice. -/
def sourceOwner : Fin p.m := CanonicalRecordingSlice.recorderSourceFromScalar
  p.two_le_m (coordinate Label.rec u.1)

/-- A present marker identifies its actual owner, actual action, grid feedback
and normalized own observation. Zero own rewards are included. -/
theorem owner_feedback (j : Fin p.K) (hmarker : Iphys = some j) :
    let owner := sourceOwner v d
    SnapshotRecordingKernel.owns p
        (.live (coordinateLaunch rate t v).start.assignment
          (unoccupiedSnapshot (coordinateLaunch rate t v).start.assignment)) owner j ∧
      (r).output.preparation.arms.actions owner = j ∧
      (r).gridFeedback owner = rewards t j ∧
      ((r).output.ownEntries owner).1 = j ∧
      ((r).output.ownEntries owner).2.val.val = ((rewards t j).val : ℝ) / (D p : ℝ) := by
  classical
  intro owner
  obtain ⟨selected, hselected, hP, hpending, _, _, hlive, _⟩ :=
    selection_exists rate rewards C_star C_h q t control0 x v d
  let slice := ((r).input.row.2 (r).input.time).1
  have howner : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (coordinate Label.rec slice) = owner := by
    dsimp only [slice, owner, sourceOwner]
    rw [record_slice]
  have hm : unitRecordingMap rate selected.view.payload.assignment slice = some j := by
    dsimp only [slice]
    rw [congrArg AssignmentStartPayload.Input.assignment hP, payload_assignment,
      record_slice, ← physical_marker_eq]
    exact hmarker
  obtain ⟨hslot, haction, howns, hmask, _⟩ :=
    (SnapshotRecordingKernel.recordingMap_some_iff p
      (.live selected.view.payload.assignment (unoccupiedSnapshot selected.view.payload.assignment))
      rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
      (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
      (by intro _; norm_num) slice j).mp hm
  rw [howner] at haction howns hmask
  rw [unit_data_action] at haction
  have hdata : slotDraw slice = dataSlot := by
    simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
  have ha : (ReferenceActivePhysicalStep.prepare (r).input).arms.actions owner = j :=
    (data_actions rate rewards C_star C_h q t control0 x v d hdata owner).trans haction
  have hu : ∀ i, (s₀ i).status = .unoccupied := fun i =>
    ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
  have hsnapshot : ReferenceActiveDataOwnership.choiceSnapshot selected s₀ =
      unoccupiedSnapshot selected.view.payload.assignment := by
    exact congrArg₂ (fun missing status =>
      (⟨missing, status⟩ : ActiveRoundActions.Snapshot selected.view.payload.assignment))
      (selected.pending_eq.symm.trans hpending) (funext hu)
  have hprep := record_preparation_eq r
  have hfeedback := ReferenceActiveDataOwnership.actual_data_owner_feedback
    (r).input selected (by rw [← hprep]; exact hselected) s₀
    (fun _ => ActiveFollowerLifecycle.initialMemory p)
    (by intro i; rw [← hprep]; exact record_prepared rate rewards C_star C_h q t control0 x v d i)
    (fun i hi => False.elim (hi (hu i))) hlive hdata owner j ha
    (by rw [hsnapshot]; exact howns) hmask
  obtain ⟨_, _, _, htime, hrewards⟩ :=
    record_source_inputs rate rewards C_star C_h q t control0 x v d
  have hown : (r).output.ownEntries owner =
      ((ReferenceActivePhysicalStep.prepare (r).input).arms.actions owner,
        (ReferenceActivePhysicalStep.prepare (r).input).feedback.observations owner) := by
    rw [(r).output_eq]
    change (ReferenceActivePhysicalStep.prepare (r).input).feedback.ownEntries owner = _
    rw [ReferenceActiveFeedbackCut.FeedbackCut.ownEntries_eq]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [congrArg AssignmentStartPayload.Input.assignment hP, payload_assignment] at howns
    exact howns
  · rw [hprep]
    exact ha
  · change (r).output.preparation.feedback.feedback owner = _
    rw [hprep, hfeedback.1, hrewards, htime]
  · rw [hown]
    exact ha
  · rw [hown]
    simpa only [hrewards, htime] using hfeedback.2

/-- Validity of the actual initial choice with its literal unit complement
weights and absent cutoff is produced by the actual first dispatcher. -/
theorem first_choice_valid : CoordinatorLocalArmChoice.ChoiceInputsValid P none
    (r).input.time (fun _ => 1) := by
  obtain ⟨installed, arm, hchosen, _, _, _, _, _⟩ :=
    dispatch_chosen_exists rate rewards C_star C_h q t control0 x v d
  have hi := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    (r).input installed arm hchosen
  subst installed
  have hw : (CoordinatorAssignmentRegisterInstall.installFirst
      (launchInput rate rewards C_star C_h q t control0 x v d)).registers.complementWeights =
      fun _ => 1 :=
    funext (CoordinatorAssignmentRegisterInstall.first_complementWeight_one _)
  have hv : CoordinatorLocalArmChoice.ChoiceInputsValid P none (r).input.time
      (CoordinatorAssignmentRegisterInstall.installFirst
        (launchInput rate rewards C_star C_h q t control0 x v d)).registers.complementWeights :=
    arm.choiceInputsValid
  rw [hw] at hv
  exact hv

/-- N's all-arm numerical readout for this actual n=0 record. -/
def numericalArm : Option (Fin p.K) := ReferenceFirstWindowNumericalStream.sourceArm
  r P Finset.univ s₀ (fun _ => 1) none
  (first_choice_valid rate rewards C_star C_h q t control0 x v d)

/-- The actual first-window all-arm cell; this is not the follower-specialized
`firstCellInput`. Its reward table and rate come from the same original record. -/
def numericalCell : RecordedQueueRun.RoundInput p.K := ReferenceFirstWindowNumericalStream.sourceCell
  r P Finset.univ s₀ (fun _ => 1) none
  (first_choice_valid rate rewards C_star C_h q t control0 x v d)

/-- N's whole-arm source marker is the same actual physical marker. -/
theorem numerical_arm_eq_physical :
    numericalArm rate rewards C_star C_h q t control0 x v d = Iphys := by
  classical
  have hu : ∀ i, (s₀ i).status = .unoccupied := fun i =>
    ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
  have hweights : ReferenceFirstWindowNumericalStream.sourceWeights P (fun _ => 1) =
      fun _ => 1 := by
    funext j
    dsimp only [ReferenceFirstWindowNumericalStream.sourceWeights]
    split <;> rfl
  have hsnapshot :
      (⟨Finset.univ, fun i => (s₀ i).status⟩ : ActiveRoundActions.Snapshot (P).assignment) =
      unoccupiedSnapshot (P).assignment :=
    congrArg (fun status => (⟨Finset.univ, status⟩ : ActiveRoundActions.Snapshot (P).assignment))
      (funext hu)
  unfold numericalArm ReferenceFirstWindowNumericalStream.sourceArm
  rw [hsnapshot]
  simp only [hweights, payload_anchor]
  change unitRecordingMap rate (P).assignment ((r).input.row.2 (r).input.time).1 = Iphys
  rw [payload_assignment, record_slice, ← physical_marker_eq]

/-- The enabled all-arm cell uses the actual marker and true grid rewards;
on the selected arm its raw arrival is the exact floor with xi at unit anchor. -/
theorem numerical_cell_readout :
    (numericalCell rate rewards C_star C_h q t control0 x v d).enabled = true ∧
      (numericalCell rate rewards C_star C_h q t control0 x v d).recordedArm = Iphys ∧
      ∀ j, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (numericalCell rate rewards C_star C_h q t control0 x v d) j =
        if Iphys = some j then
          Nat.floor ((rate.n : ℝ) * (((rewards t j).val : ℝ) / (D p : ℝ)) /
            CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
        else 0 := by
  classical
  refine ⟨rfl, numerical_arm_eq_physical rate rewards C_star C_h q t control0 x v d, ?_⟩
  intro j
  have h := ReferenceFirstWindowNumericalStream.sourceCell_quantizedArrival r P Finset.univ s₀
    (fun _ => 1) none (first_choice_valid rate rewards C_star C_h q t control0 x v d) j
  change RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      (numericalCell rate rewards C_star C_h q t control0 x v d) j =
    (if numericalArm rate rewards C_star C_h q t control0 x v d = some j then
      Nat.floor ((rate.n : ℝ) * ((((r).input.rewards (r).input.time j).val : ℝ) / (D p : ℝ)) /
        (P).rate j) else 0) at h
  obtain ⟨_, _, _, ht, hr⟩ := record_source_inputs rate rewards C_star C_h q t control0 x v d
  simpa only [numerical_arm_eq_physical, payload_rate, ht, hr] using h

/-- The actual current checked emission contributes the virtual first arrival,
using its true own observation and the same saved thin scalar. This assertion
does not service or update an unoccupied follower's local queue. -/
theorem current_saved_contribution (i : Fin (p.m - 1)) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
        ((P).exponent ((P).assignment.assigned i)) ((P).assignment.assigned i)
        ((r).input.time.val + 1) (ReferenceFollowerBufferProvenance.logEmission i r) =
      if Iphys = some ((P).assignment.assigned i) then
        Nat.floor ((rate.n : ℝ) * ((r).output.ownEntries (followerPlayer p.two_le_m i)).2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) ((P).assignment.assigned i))
      else 0 := by
  classical
  obtain ⟨selected, hselected, hP, _, _, _, _, _⟩ :=
    selection_exists rate rewards C_star C_h q t control0 x v d
  have hanchor : selected.view.payload.anchor = fun _ => 1 := by rw [hP]; rfl
  have hu := ((record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i).2.2.2.2.2.1
  have h := ReferenceSelectedCandidateRecorderEvent.current_selected_candidate_eq_marker r selected
    (by rw [← record_preparation_eq r]; exact hselected) i
    (unoccupiedSnapshot selected.view.payload.assignment) (s₀ i) (ActiveFollowerLifecycle.initialMemory p)
    (record_prepared rate rewards C_star C_h q t control0 x v d i) hu hu.symm (fun _ => 1)
    (by intro _; norm_num) (by intro j; rw [hanchor]) (by intro j; rw [hanchor]; norm_num)
  simp only [hanchor] at h
  change SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
      (selected.view.payload.exponent (selected.view.payload.assignment.assigned i))
      (selected.view.payload.assignment.assigned i) ((r).input.time.val + 1)
      (ReferencePrelaunchFollower.logAt i (r).input.row ((r).input.state.activations i)
        (r).input.time ((r).output.ownEntries (followerPlayer p.two_le_m i))) =
    (if unitRecordingMap rate selected.view.payload.assignment ((r).input.row.2 (r).input.time).1 =
        some (selected.view.payload.assignment.assigned i) then
      Nat.floor ((D p : ℝ) * rate.eta.val *
        ((r).output.ownEntries (followerPlayer p.two_le_m i)).2.val.val /
        CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1)
          (selected.view.payload.assignment.assigned i)) else 0) at h
  have hmap : unitRecordingMap rate selected.view.payload.assignment
      ((r).input.row.2 (r).input.time).1 = Iphys := by
    rw [congrArg AssignmentStartPayload.Input.assignment hP, payload_assignment,
      record_slice, ← physical_marker_eq]
  have hscale : (D p : ℝ) * rate.eta.val = (rate.n : ℝ) := by
    rw [mul_comm]
    exact rate.n_scale.symm
  rw [hmap, hP, hscale] at h
  obtain ⟨_, _, _, _, hemission, _⟩ :=
    record_logged rate rewards C_star C_h q t control0 x v d i
  rw [hemission]
  exact h

/-- Before real DOWN decoding, checked logging preserves the initial zero
score, increment and queue, the DOWN batch and the initialization failure flag. -/
theorem logged_seed_fields (i : Fin (p.m - 1)) :
    ∃ logged,
      ((r).output.followers i).downInput = some logged ∧
      ActiveFollowerLogging.checkedLogging i (r).input.row ((r).input.state.activations i)
        (r).input.time ((r).output.ownEntries (followerPlayer p.two_le_m i)) (s₀ i) = .ok logged ∧
      logged.S = 0 ∧ logged.delta = 0 ∧ logged.backlog = 0 ∧ logged.lastDown = none ∧
      logged.status = .unoccupied ∧ logged.downBatch = (s₀ i).downBatch ∧
      logged.initializationFailure = (s₀ i).initializationFailure := by
  obtain ⟨logged, hcheck, hdown, _, _, _⟩ :=
    record_logged rate rewards C_star C_h q t control0 x v d i
  obtain ⟨hlast, hS, hd, hb, hu, hbatch, hfailure⟩ :=
    ActiveFollowerLogging.checkedLogging_success_frame i (r).input.row
      ((r).input.state.activations i) (r).input.time
      ((r).output.ownEntries (followerPlayer p.two_le_m i)) (s₀ i) logged hcheck
  obtain ⟨hsLast, _, hsS, hsD, hsB, hsU, _⟩ :=
    (record_seed rate rewards C_star C_h q t control0 x v d).2.2.2 i
  exact ⟨logged, hdown, hcheck, hS.trans hsS, hd.trans hsD, hb.trans hsB,
    hlast.trans hsLast, hu.trans hsU, hbatch, hfailure⟩

/-- A first-marker follower owner has a genuine current saved record in the
same checked logged buffer. Its own reward, calendar key and thin scalar are
those of this actual physical round; the thinning test is inclusive. -/
theorem follower_owner_saved (j : Fin p.K) (hmarker : Iphys = some j)
    (i : Fin (p.m - 1)) (howner : sourceOwner v d = followerPlayer p.two_le_m i) :
    j = (P).assignment.assigned i ∧
      ∃ logged saved,
        ActiveFollowerLogging.checkedLogging i (r).input.row ((r).input.state.activations i)
          (r).input.time ((r).output.ownEntries (followerPlayer p.two_le_m i)) (s₀ i) = .ok logged ∧
        ((r).output.followers i).downInput = some logged ∧
        logged.buffer = (s₀ i).buffer ++ ReferenceFollowerBufferProvenance.logEmission i r ∧
        saved ∈ ReferenceFollowerBufferProvenance.logEmission i r ∧ saved ∈ logged.buffer ∧
        saved.calendarRound = t.val + 1 ∧ saved.pilot = j ∧
        saved.observation.val = ((rewards t j).val : ℝ) / (D p : ℝ) ∧
        saved.thinScalar = u.1 Label.thin ∧
        saved.thinScalar.val ≤ ReferenceContinuingRecordingFastPair.savedInclusiveThinThreshold P j := by
  classical
  have hf := owner_feedback rate rewards C_star C_h q t control0 x v d j hmarker
  dsimp only at hf
  rw [howner] at hf
  have hne := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hne
  have hj : j = (P).assignment.assigned i := by
    have howns := hf.1
    rw [← payload_assignment rate rewards C_star C_h q t control0 x v d] at howns
    simpa only [SnapshotRecordingKernel.owns, dite_eq_right hne, hindex] using howns
  refine ⟨hj, ?_⟩
  obtain ⟨logged, hcheck, hdown, happend, hemits, _⟩ :=
    record_logged rate rewards C_star C_h q t control0 x v d i
  have hsource : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
      (coordinate Label.rec ((r).input.row.2 (r).input.time).1) = followerPlayer p.two_le_m i := by
    rw [record_slice]
    exact howner
  have hdyadic : OrdinaryMessageCodec.dyadicRate ((P).exponent ((P).assignment.assigned i)) =
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) ((P).assignment.assigned i) :=
    ((P).dyadicRate_eq_rate _).trans (payload_rate rate rewards C_star C_h q t control0 x v d _)
  have hmap := unoccupied_marker_eq_map r P i (s₀ i) logged hcheck hdown happend hemits hsource
    (follower_data_pilot rate rewards C_star C_h q t control0 x v d i) hdyadic
  have hcurrent : ReferenceContinuingRecordingFastPair.currentUnoccupiedCandidateMarker
      r P i (s₀ i) = some ((P).assignment.assigned i) := by
    have hm : unitRecordingMap rate (P).assignment ((r).input.row.2 (r).input.time).1 = some j := by
      rw [payload_assignment, record_slice,
        ← physical_marker_eq rate rewards C_star C_h q t control0 x v d]
      exact hmarker
    exact hmap.trans (hm.trans (congrArg some hj))
  obtain ⟨htests, hownArm, hthin⟩ :=
    (unoccupied_marker_iff r P i (s₀ i) logged hcheck hdown happend hemits).mp hcurrent
  let saved := SparseCalendarReplay.recordAt ((r).input.time.val + 1)
    (ReferencePrelaunchFollower.loggingRound i (r).input.row ((r).input.state.activations i)
      (r).input.time ((r).output.ownEntries (followerPlayer p.two_le_m i)))
  have hmem : saved ∈ ReferenceFollowerBufferProvenance.logEmission i r := by
    rw [hemits, ReferencePrelaunchFollower.mem_logAt_iff]
    exact ⟨htests, rfl⟩
  have htime := (record_source_inputs rate rewards C_star C_h q t control0 x v d).2.2.2.1
  refine ⟨logged, saved, hcheck, hdown, happend, hmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [happend]
    exact List.mem_append_right _ hmem
  · change (r).input.time.val + 1 = t.val + 1
    rw [htime]
  · exact hf.2.2.2.1
  · exact hf.2.2.2.2
  · change ((r).input.row.2 (r).input.time).1 Label.thin = u.1 Label.thin
    rw [record_slice]
  · change (((r).input.row.2 (r).input.time).1 Label.thin).val ≤ _
    rw [hj]
    exact hthin

/-- The same actual first installation exposes its sampled payload, all zero
numerical registers, unit weights, true assigned DOWN records and dyadic rates.
The final playable round still has the genuine boundary g=T+1. -/
theorem installation_exists :
    ∃ (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
        (launchInput rate rewards C_star C_h q t control0 x v d))
      (arm : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
        installed.startRoundResult installed.registers.time installed.registers.complementWeights
        (r).input.row),
      CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput (r).input) =
        .chosen installed arm ∧
      (r).output.preparation.coordinator = .first (.chosen installed arm) ∧
      installed.registers.payload = P ∧
      installed.start.coordinates = v ∧
      installed.registers.payload.assignment = (coordinateLaunch rate t v).start.assignment ∧
      installed.registers.payload.sigma = t ∧
      (∀ a, installed.registers.payload.anchor a = 1) ∧
      (∀ a, installed.registers.complementWeights a = 1) ∧
      (∀ i, installed.registers.payload.assignment.assigned i = installed.start.assignment.assigned i ∧
        installed.registers.payload.downRecord i = installed.start.outgoing i ∧
        installed.registers.payload.rate (installed.registers.payload.assignment.assigned i) =
          OrdinaryMessageCodec.dyadicRate (installed.registers.payload.downRecord i).val.h) ∧
      (∀ a, installed.registers.payload.queues a = 0) ∧
      installed.registers.pendingAtChoice = Finset.univ ∧
      (∀ a, installed.registers.complementScores a = 0) ∧
      (∀ a, installed.ownedRegisters.queue a = 0) ∧
      (∀ a, installed.ownedRegisters.previousService a = 0) ∧
      (∀ i, installed.followerBaseScore i = 0) ∧
      t.val + 1 < installed.startRoundResult.clock.g ∧
      installed.startRoundResult.clock.g ≤ p.T + 1 ∧
      (t.val + 1 = p.T → installed.startRoundResult.clock.g = p.T + 1) := by
  obtain ⟨installed, arm, hchosen, hbranch, _, _, hstrict, _⟩ :=
    dispatch_chosen_exists rate rewards C_star C_h q t control0 x v d
  obtain ⟨hsigma, hanchor, hdown, hqueues, hpending, hscores, hqueue, hservice, hbase⟩ :=
    ReferenceFirstLaunchNumericalCell.first_installation_payload_facts rate z rewards C_star C_h
      (source_crossing rate rewards C_star C_h q t control0 x v d).1
      (source_elapsed_lt rate rewards C_star C_h q t control0 x v d) installed arm hchosen
  have hi := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    (r).input installed arm hchosen
  have hP : installed.registers.payload = P := by rw [hi]; rfl
  have hcoordinates : installed.start.coordinates = v := by
    rw [installed.start_eq, FirstAssignmentLaunch.Input.start_coordinates, launchInput_eq_coordinates]
    rfl
  have htime := (record_source_inputs rate rewards C_star C_h q t control0 x v d).2.2.2.1
  have hsigma' : installed.registers.payload.sigma = t := by
    apply Fin.ext
    exact hsigma.trans (congrArg Fin.val htime)
  have hcomp : ∀ a, installed.registers.complementWeights a = 1 := by
    subst installed
    exact CoordinatorAssignmentRegisterInstall.first_complementWeight_one _
  have hupper : installed.startRoundResult.clock.g ≤ p.T + 1 := by
    rw [hi]
    exact (CoordinatorAssignmentRegisterInstall.first_new_grid_boundary_valid _).2
  rw [htime] at hstrict
  refine ⟨installed, arm, hchosen, hbranch, hP, hcoordinates, ?_, hsigma', hanchor, hcomp,
    hdown, hqueues, hpending, hscores, hqueue, hservice, hbase, hstrict, hupper, ?_⟩
  · rw [hP, payload_assignment]
  · intro hlast
    omega

/-- The actual initialization learner has zero scores and queues, empty saved
numerical records, and a false incoming overflow flag. -/
theorem initial_coordinator_learner :
    ReferenceInitializationRun.coordinatorLearner
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)) =
      some (RecordedQueueRun.initialState p.K) ∧
      ∀ a : Fin p.K,
        (RecordedQueueRun.initialState p.K).registers a = (0, 0) ∧
        (RecordedQueueRun.initialState p.K).records a = [] ∧
        (RecordedQueueRun.initialState p.K).overflow = false := by
  obtain ⟨_, _, _, _, _, hlearner, hzero, _⟩ :=
    ReferenceFirstLaunchNumericalCell.actual_launch_seed rate z rewards C_star C_h
      (source_crossing rate rewards C_star C_h q t control0 x v d).1
  exact ⟨hlearner, hzero⟩

/-- Literal source, action, true-ownership, mask and inclusive thinning tests
for the actual whole first marker. Every failed test gives bottom by this iff. -/
theorem physical_marker_some_iff (j : Fin p.K) :
    Iphys = some j ↔
      slotDraw u.1 = dataSlot ∧
      pilotDraw (K_pos p) (sourceOwner v d) u.1 = j ∧
      SnapshotRecordingKernel.owns p
        (.live (coordinateLaunch rate t v).start.assignment
          (unoccupiedSnapshot (coordinateLaunch rate t v).start.assignment)) (sourceOwner v d) j ∧
      CanonicalRecordingSlice.recordingMask (K_pos p) (sourceOwner v d) j u.1 ∧
      (coordinate Label.thin u.1).val ≤
        SnapshotRecordingKernel.thinningThreshold p
          (.live (coordinateLaunch rate t v).start.assignment
            (unoccupiedSnapshot (coordinateLaunch rate t v).start.assignment))
          rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
          (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
          (by intro _; norm_num) (sourceOwner v d) j := by
  rw [physical_marker_eq]
  have h := SnapshotRecordingKernel.recordingMap_some_iff p
    (.live (coordinateLaunch rate t v).start.assignment
      (unoccupiedSnapshot (coordinateLaunch rate t v).start.assignment))
    rate.eta.val rate.eta.property rate.sourceCap (fun _ => 1) (fun _ => 1)
    (by intro _; norm_num) (by intro _; norm_num) (by intro _; norm_num)
    (by intro _; norm_num) u.1 j
  simpa only [unitRecordingMap, sourceOwner,
    CanonicalRecordingSlice.slotFromScalar_coordinate, unit_data_action] using h

/-- Every true assigned arm's current saved contribution is exactly N's
virtual all-arm arrival, without performing local service before decoding. -/
theorem current_saved_eq_numerical_arrival (i : Fin (p.m - 1)) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
        ((P).exponent ((P).assignment.assigned i)) ((P).assignment.assigned i)
        ((r).input.time.val + 1) (ReferenceFollowerBufferProvenance.logEmission i r) =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (numericalCell rate rewards C_star C_h q t control0 x v d) ((P).assignment.assigned i) := by
  classical
  rw [current_saved_contribution,
    (numerical_cell_readout rate rewards C_star C_h q t control0 x v d).2.2]
  by_cases hm : Iphys = some ((P).assignment.assigned i)
  · simp only [hm, ite_true]
    have hf := owner_feedback rate rewards C_star C_h q t control0 x v d
      ((P).assignment.assigned i) hm
    dsimp only at hf
    have hne := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
    have hindex := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hne
    have howns : SnapshotRecordingKernel.owns p
        (.live (coordinateLaunch rate t v).start.assignment
          (unoccupiedSnapshot (coordinateLaunch rate t v).start.assignment))
        (followerPlayer p.two_le_m i) ((P).assignment.assigned i) := by
      rw [← payload_assignment rate rewards C_star C_h q t control0 x v d]
      simp only [SnapshotRecordingKernel.owns, dite_eq_right hne, hindex]
    have howner := SnapshotRecordingKernel.owns_unique p
      (.live (coordinateLaunch rate t v).start.assignment
        (unoccupiedSnapshot (coordinateLaunch rate t v).start.assignment))
      ((P).assignment.assigned i) (sourceOwner v d) (followerPlayer p.two_le_m i) hf.1 howns
    have hy := hf.2.2.2.2
    rw [howner] at hy
    rw [hy]
  · simp only [hm, ite_false]

/-- Coherent deterministic producer at the unrestricted retained-source root:
the actual record, actual first payload/selection and whole physical marker
are the ones used by N's enabled all-arm numerical cell. -/
theorem actual_first_launch_recording :
    (r).input = ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t t.val le_rfl control0 x) z ∧
      launchInput rate rewards C_star C_h q t control0 x v d = coordinateLaunch rate t v ∧
      (P).assignment = (coordinateLaunch rate t v).start.assignment ∧
      Iphys = unitRecordingMap rate (coordinateLaunch rate t v).start.assignment u.1 ∧
      numericalArm rate rewards C_star C_h q t control0 x v d = Iphys ∧
      (numericalCell rate rewards C_star C_h q t control0 x v d).enabled = true ∧
      (numericalCell rate rewards C_star C_h q t control0 x v d).recordedArm = Iphys ∧
      (∀ j, RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (numericalCell rate rewards C_star C_h q t control0 x v d) j =
        if Iphys = some j then
          Nat.floor ((rate.n : ℝ) * (((rewards t j).val : ℝ) / (D p : ℝ)) /
            CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) else 0) ∧
      ∃ selected : ReferenceActivePhysicalStep.Selection (r).input,
        (r).output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = P ∧ selected.view.pendingAtChoice = Finset.univ ∧
        selected.view.cutoff = none ∧ (∀ a, selected.view.complementWeights a = 1) ∧
        CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff (r).input.time ∧
        CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload selected.view.cutoff
          (r).input.time selected.view.complementWeights := by
  obtain ⟨henabled, harm, hraw⟩ := numerical_cell_readout rate rewards C_star C_h q t control0 x v d
  exact ⟨record_eq_roundInputAtSource rate rewards C_star C_h q t control0 x v d,
    launchInput_eq_coordinates rate rewards C_star C_h q t control0 x v d,
    payload_assignment rate rewards C_star C_h q t control0 x v d,
    physical_marker_eq rate rewards C_star C_h q t control0 x v d,
    numerical_arm_eq_physical rate rewards C_star C_h q t control0 x v d,
    henabled, harm, hraw, selection_exists rate rewards C_star C_h q t control0 x v d⟩

end OriginalSource

/-- A crossing at elapsed T has a genuine zero-record active run, not a
fabricated current action at a Fin T sentinel. -/
theorem terminal_zero_records {p : Parameters} (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hterminal : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T) :
    ∃ active, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h = some active ∧
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T 0
        (by omega) hmode).finalState = active ∧
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T 0
        (by omega) hmode).records = [] :=
  ReferenceCorrectedInitializationLaunch.correctedLaunch_terminal_run_zero
    rate source rewards C_star C_h hcross hterminal

end Bandits.Support.ReferenceFirstLaunchRecordingPhysicalMarker
