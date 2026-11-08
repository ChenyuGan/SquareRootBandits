/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon

/-!
# Occupied follower recorder event and local service

The occupied follower's inclusive DATA/source/mask/thinning gate and raw
increment are from `sources/zip4/manuscript/05_binary_transport.tex:354-396,411-429`.
The actual post-choice service and queue update are from
`sources/zip4/manuscript/06_interruptions.tex:256-261`.

These results identify one actual prepared occupied follower's recorder event
with the canonical map event for its selected payload. The observation is the
one computed by the physical preparation. The statements preserve checked
service failure and make no claim about reward equality, snapshot freshness,
or a complete execution's recording law.

The logical inputs are explicit: the pointwise gate lemma uses a typed payload,
a snapshot agreeing with this follower's local status, and local occupancy.
The service-arrival lemma additionally uses a successful checked-service record
and the exact local `lastDown` agreement. The physical-round identification
keeps the actual selected payload, live branch, ordinary prepared configuration,
status agreement, occupancy, current DOWN agreement, and the equality identifying
the successful `checkedService` call. Its service record carries the checked
input/output domains, source rate cap, natural scale, and literal service action;
none of these checks is inferred merely from occupancy. The horizon wrapper
also retains literal `run` membership and the all-active boundary input.
Non-DATA service remains conditional on successful checking; failed checking
is preserved as `.service` through the actual `finishFollower`. The final
success lemma explicitly requires success of the actual release/finish tail.

The snapshot's other statuses and missing set are unrestricted: this identifies
only the selected follower-arm event with both weight inputs equal to the
payload anchor. DATA collision/reward geometry, preservation of current DOWN
agreement, domain-check success, buffer chronology, full queue truth, and the
common recording history are separate obligations. No unoccupied-candidate
result or pending provider is consumed here.
-/

@[expose] public section

noncomputable section

local instance recorderPropDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

namespace Bandits.Support.ReferenceFollowerOccupiedRecorderEvent

open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveRoundActions
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SnapshotRecordingKernel

/- The local identity is stated for any typed payload and snapshot. The
status equality is the only relation used to choose the occupied follower
branch of the canonical map. -/
theorem occupiedGate_eq_canonicalRecordingMap
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : AssignmentStartPayload.Input p rate.eta)
    (snapshot : ActiveRoundActions.Snapshot payload.assignment)
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hstatus : snapshot.status i = state.status)
    (hoccupied : state.status.occupied) :
    ActiveFollowerQueueOperation.recorderGate rate.eta i row t
        (payload.downRecord i) ↔
      SnapshotRecordingKernel.recordingMap p (.live payload.assignment snapshot)
        true rate.eta.val rate.eta.property payload.eta_le_source_cap
        payload.anchor payload.anchor payload.anchor_pos payload.anchor_pos
        (fun _ => le_rfl) (fun j => by
          rw [two_mul]
          exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j)))
        ((row.2 t).1) = some (payload.assignment.assigned i) := by
  let source := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let arm := payload.assignment.assigned i
  let slice := (row.2 t).1
  have hsource : source ≠ ActiveRoundActions.coordinator p.two_le_m :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hsourceIndex :
      ActiveRoundActions.followerIndex p.two_le_m source hsource = i :=
    ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hsource
  have hstateNe : state.status ≠ .unoccupied := by
    intro h
    rw [h] at hoccupied
    simp [FollowerStatus.occupied] at hoccupied
  have hsnapshotNe : snapshot.status i ≠ .unoccupied := by
    intro h
    exact hstateNe (hstatus.symm.trans h)
  have howner : SnapshotRecordingKernel.owns p
      (.live payload.assignment snapshot) source arm := by
    simp [SnapshotRecordingKernel.owns, hsource, hsourceIndex, arm]
  have haction : ∀ z : CanonicalRecordingSlice.Slice p.m p.K,
      SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
        rate.eta.val rate.eta.property payload.eta_le_source_cap
        payload.anchor payload.anchor payload.anchor_pos payload.anchor_pos
        (fun _ => le_rfl) (fun j => by
          rw [two_mul]
          exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) z source = arm := by
    intro z
    simp [SnapshotRecordingKernel.dataAction, hsource, hsourceIndex, hsnapshotNe, arm]
  have hprob : SnapshotRecordingKernel.actionProbability p
      (.live payload.assignment snapshot) rate.eta.val rate.eta.property
      payload.eta_le_source_cap payload.anchor payload.anchor payload.anchor_pos
      payload.anchor_pos (fun _ => le_rfl) (fun j => by
        rw [two_mul]
        exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) source arm = 1 := by
    simp [SnapshotRecordingKernel.actionProbability, hsource, hsourceIndex, hsnapshotNe, arm]
  have harm : PrelaunchBufferRecovery.downArm rate.eta (payload.downRecord i) = arm := by
    apply Fin.ext
    have h := PrelaunchBufferRecovery.down_arm_one_based rate.eta (payload.downRecord i)
    rw [payload.downRecord_fields i] at h
    exact Nat.add_right_cancel h
  have hrate := payload.downRecord_rate i
  have hzeta := CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability
    p.m p.K
  have hmd : p.m - 1 < p.K := by
    have hmk := p.m_lt_K
    omega
  have hmaskPos : 0 < SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) :=
    SparseCalendarReplay.sparseMaskProbability_pos p.K (p.m - 1)
      (ConstructorDimensions.K_pos p) hmd
  have hthin : ActiveFollowerQueueOperation.thinningProbability rate.eta
        (payload.downRecord i) =
      SnapshotRecordingKernel.thinningThreshold p
        (.live payload.assignment snapshot) rate.eta.val rate.eta.property
        payload.eta_le_source_cap payload.anchor payload.anchor payload.anchor_pos
        payload.anchor_pos (fun _ => le_rfl) (fun j => by
          rw [two_mul]
          exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) source arm := by
    unfold ActiveFollowerQueueOperation.thinningProbability
      SnapshotRecordingKernel.thinningThreshold SnapshotRecordingKernel.rawGateMass
    rw [hprob, hrate, hzeta, PublicDiscreteDraws.recorderMass_follower p.two_le_m i]
    simp only [PublicDiscreteDraws.followerCount]
    have hdpos : (0 : ℝ) < ((p.m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < p.m - 1 by omega)
    field_simp [ne_of_gt hdpos, ne_of_gt hmaskPos]
    ring
  have hevent := SnapshotRecordingKernel.recordingMap_owner_event_eq p
    (.live payload.assignment snapshot) rate.eta.val rate.eta.property
    payload.eta_le_source_cap payload.anchor payload.anchor payload.anchor_pos
    payload.anchor_pos (fun _ => le_rfl) (fun j => by
      rw [two_mul]
      exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) source arm howner
  have hpoint :
      SnapshotRecordingKernel.recordingMap p (.live payload.assignment snapshot)
          true rate.eta.val rate.eta.property payload.eta_le_source_cap
          payload.anchor payload.anchor payload.anchor_pos payload.anchor_pos
          (fun _ => le_rfl) (fun j => by
            rw [two_mul]
            exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) slice = some arm ↔
        PublicDiscreteDraws.slotDraw slice = PublicDiscreteDraws.dataSlot ∧
          PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K slice = source ∧
          SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
            rate.eta.val rate.eta.property payload.eta_le_source_cap
            payload.anchor payload.anchor payload.anchor_pos payload.anchor_pos
            (fun _ => le_rfl) (fun j => by
              rw [two_mul]
              exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) slice source = arm ∧
          CanonicalRecordingSlice.recordingMask (ConstructorDimensions.K_pos p) source arm slice ∧
          (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin slice).val ≤
            SnapshotRecordingKernel.thinningThreshold p
              (.live payload.assignment snapshot) rate.eta.val rate.eta.property
              payload.eta_le_source_cap payload.anchor payload.anchor payload.anchor_pos
              payload.anchor_pos (fun _ => le_rfl) (fun j => by
                rw [two_mul]
                exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j))) source arm := by
    have hmem := Iff.of_eq (congrArg (fun events : Set _ => slice ∈ events) hevent)
    simpa only [Set.mem_ofPred_eq] using hmem
  unfold ActiveFollowerQueueOperation.recorderGate
  simpa [harm, haction slice, hthin, source, arm, slice] using hpoint.symm

/-- A successful checked service uses the exact occupied DOWN record's gate
and its inclusive source floor. The carried service action supplies the
record; this does not assume successful service or any domain check. -/
theorem serviceSuccess_arrival_eq_gate
    {p : Parameters} {eta : ReferenceActivePhysicalStep.RateInput p}
    {i : Fin (p.m - 1)} {row : CompletePublicTable.CompleteRow p}
    {alpha : ReferencePrelaunchFollower.Activation p} {t : Fin p.T}
    {observation : ReferencePrelaunchFollower.Observation p}
    {state : ReferencePrelaunchFollower.State p eta.eta}
    (record : ActiveFollowerQueueOperation.ServiceSuccess p eta.eta eta.n i row
      alpha t observation state)
    (M : OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p eta.eta))
    (hoccupied : state.status.occupied)
    (hlastDown : state.lastDown = some M) :
    record.arrival =
      if ActiveFollowerQueueOperation.recorderGate eta.eta i row t M then
        ActiveFollowerQueueOperation.sourceArrivalFloor eta.eta M observation
      else 0 := by
  cases hstatus : state.status with
  | unoccupied =>
      simp [FollowerStatus.occupied, hstatus] at hoccupied
  | pending =>
      have haction := record.action
      simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
      rcases haction with ⟨_, M', hM', _, harrival, _⟩
      have hM : M' = M := Option.some.inj (hM'.symm.trans hlastDown)
      rw [hM] at harrival
      calc
        record.arrival = ActiveFollowerQueueOperation.rawArrival eta.eta i row t M observation :=
          harrival
        _ = if ActiveFollowerQueueOperation.recorderGate eta.eta i row t M then
              ActiveFollowerQueueOperation.sourceArrivalFloor eta.eta M observation else 0 :=
          ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula eta.eta i row t M observation
  | released =>
      have haction := record.action
      simp only [ActiveFollowerQueueOperation.serviceAction, hstatus] at haction
      rcases haction with ⟨_, M', hM', _, harrival, _⟩
      have hM : M' = M := Option.some.inj (hM'.symm.trans hlastDown)
      rw [hM] at harrival
      calc
        record.arrival = ActiveFollowerQueueOperation.rawArrival eta.eta i row t M observation :=
          harrival
        _ = if ActiveFollowerQueueOperation.recorderGate eta.eta i row t M then
              ActiveFollowerQueueOperation.sourceArrivalFloor eta.eta M observation else 0 :=
          ActiveFollowerQueueOperation.rawArrival_eq_sourceFormula eta.eta i row t M observation

/-- The exact service update equations for an actual occupied follower in a
literal physical round record. The `observation` below is always the follower
component computed by `record.output.preparation.feedback`. -/
theorem roundRecord_occupied_service_identification
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (_hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (_hconfiguration :
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (hstatus : snapshot.status i = state.status)
    (hoccupied : state.status.occupied)
    (hlastDown : state.lastDown = some (selected.view.payload.downRecord i))
    (result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state)
    (hchecked : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .success result) :
    (result.arrival =
        if SnapshotRecordingKernel.recordingMap p
          (.live selected.view.payload.assignment snapshot) true rate.eta.val
          rate.eta.property selected.view.payload.eta_le_source_cap
          selected.view.payload.anchor selected.view.payload.anchor
          selected.view.payload.anchor_pos selected.view.payload.anchor_pos
          (fun _ => le_rfl) (fun j => by
            rw [two_mul]
            exact le_add_of_nonneg_right
              (le_of_lt (selected.view.payload.anchor_pos j)))
          ((record.input.row.2 record.input.time).1) =
            some (selected.view.payload.assignment.assigned i) then
          ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta
            (selected.view.payload.downRecord i)
            (record.output.preparation.feedback.observations
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        else 0) ∧
      result.output = ActiveFollowerQueueOperation.serviceUpdate rate.n state
        result.arrival ∧
      result.output.S = state.S +
        ActiveFollowerQueueOperation.localService rate.n state.backlog result.arrival ∧
      result.output.delta =
        ActiveFollowerQueueOperation.localService rate.n state.backlog result.arrival ∧
      result.output.backlog +
        ActiveFollowerQueueOperation.localService rate.n state.backlog result.arrival =
        state.backlog + result.arrival ∧
      (result.output.S, result.output.backlog) =
        QueueReplay.transition (ActiveFollowerQueueOperation.serviceCapacity rate.n)
          (state.S, state.backlog) (true, result.arrival) ∧
      (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView
        (record.output.preparation.followers.followers i).follower
        (record.output.preparation.followers.followers i).row
        (record.output.preparation.followers.followers i).activation
        (record.output.preparation.followers.followers i).time
        (record.output.preparation.followers.followers i).active
        (record.output.preparation.followers.followers i).arm
        (record.output.preparation.feedback.observations
          (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state).result =
        .ok result.output := by
  let payload := selected.view.payload
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  let follower := record.output.preparation.followers.followers i
  have hgate := occupiedGate_eq_canonicalRecordingMap payload snapshot i
    follower.row follower.time state hstatus hoccupied
  have harrival := serviceSuccess_arrival_eq_gate result (payload.downRecord i)
    hoccupied hlastDown
  have harrivalMap : result.arrival =
      if SnapshotRecordingKernel.recordingMap p (.live payload.assignment snapshot)
        true rate.eta.val rate.eta.property payload.eta_le_source_cap
        payload.anchor payload.anchor payload.anchor_pos payload.anchor_pos
        (fun _ => le_rfl) (fun j => by
          rw [two_mul]
          exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j)))
        ((follower.row.2 follower.time).1) = some (payload.assignment.assigned i) then
        ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta (payload.downRecord i)
          observation
      else 0 := by
    simpa only [follower, observation, hgate] using harrival
  have hsuccess := ActiveFollowerQueueOperation.serviceSuccess_equations result
  have hupdate : result.output =
      ActiveFollowerQueueOperation.serviceUpdate rate.n state result.arrival := by
    calc
      result.output = ActiveFollowerQueueOperation.serviceOutput rate.n state result.arrival :=
        hsuccess.1
      _ = ActiveFollowerQueueOperation.serviceUpdate rate.n state result.arrival := by
        simp [ActiveFollowerQueueOperation.serviceOutput, hoccupied]
  have hregisters := ActiveFollowerQueueOperation.serviceUpdate_register_equations
    rate.n state result.arrival
  have hqueue := ActiveFollowerQueueOperation.serviceUpdate_eq_queueTransition
    rate.n state result.arrival
  have hprepared : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hselectedPrepared :
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    rw [← hprepared]
    exact hselected
  have hfields := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    record.output.preparation i
  have hview : record.output.preparation.coordinator.downView = some selected.view := by
    have hviewPrepared :
        (ReferenceActivePhysicalStep.prepare record.input).coordinator.downView = some selected.view := by
      unfold ReferenceActivePhysicalStep.DispatchCut.downView
      rw [hselectedPrepared]
      rfl
    rw [hprepared]
    exact hviewPrepared
  have hrecordService := hchecked
  have hstateNe : state.status ≠ .unoccupied := by
    intro h
    rw [h] at hoccupied
    simp [FollowerStatus.occupied] at hoccupied
  have hrecord :
      (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView follower.follower follower.row
        follower.activation follower.time follower.active follower.arm observation state).result =
        .ok result.output := by
    rw [hview]
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hstateNe]
    rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
      rate follower.follower follower.row follower.activation follower.time follower.active
      follower.arm observation state hstateNe]
    rw [hfields.2.1]
    rw [hrecordService]
  have harrivalInput : result.arrival =
      if SnapshotRecordingKernel.recordingMap p (.live payload.assignment snapshot)
        true rate.eta.val rate.eta.property payload.eta_le_source_cap
        payload.anchor payload.anchor payload.anchor_pos payload.anchor_pos
        (fun _ => le_rfl) (fun j => by
          rw [two_mul]
          exact le_add_of_nonneg_right (le_of_lt (payload.anchor_pos j)))
        ((record.input.row.2 record.input.time).1) = some (payload.assignment.assigned i) then
        ActiveFollowerQueueOperation.sourceArrivalFloor rate.eta (payload.downRecord i)
          observation
      else 0 := by
    simpa only [follower, hfields.1, hfields.2.2.1] using harrivalMap
  refine ⟨harrivalInput, hupdate, ?_, ?_, ?_, ?_, hrecord⟩
  · rw [hupdate]
    exact hregisters.1
  · rw [hupdate]
    exact hregisters.2.1
  · rw [hupdate]
    exact hregisters.2.2
  · rw [hupdate]
    exact hqueue

/-- The occupied gate identity is available for a record in the literal
`H.run` calendar, retaining the original row family, selected row, complete
reward table, interval, and boundary mode. -/
theorem run_record_occupied_gate_eq_canonicalRecordingMap
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selectedRow : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hmember : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow
      rewards start count hspan hmode).records)
    (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (_hselected : record.output.preparation.coordinator.selection = some selected)
    (_hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (_hconfiguration :
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (hstatus : snapshot.status i = state.status)
    (hoccupied : state.status.occupied)
    (_hlastDown : state.lastDown = some (selected.view.payload.downRecord i))
    : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selectedRow
        rewards start count hspan hmode).records ∧
      (ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
        record.input.time (selected.view.payload.downRecord i) ↔
        SnapshotRecordingKernel.recordingMap p
          (.live selected.view.payload.assignment snapshot) true rate.eta.val
          rate.eta.property selected.view.payload.eta_le_source_cap
          selected.view.payload.anchor selected.view.payload.anchor
          selected.view.payload.anchor_pos selected.view.payload.anchor_pos
          (fun _ => le_rfl) (fun j => by
            rw [two_mul]
            exact le_add_of_nonneg_right (le_of_lt (selected.view.payload.anchor_pos j)))
          ((record.input.row.2 record.input.time).1) =
            some (selected.view.payload.assignment.assigned i)) := by
  exact ⟨hmember, occupiedGate_eq_canonicalRecordingMap selected.view.payload snapshot i
    record.input.row record.input.time state hstatus hoccupied⟩

/-- A successful non-DATA service on the actual prepared occupied follower
has zero arrival and still applies the ordinary bounded service amount. -/
theorem prepared_occupied_nonData_service_fields
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (_hconfiguration :
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state)
    (hchecked : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .success result)
    (hoccupied : state.status.occupied)
    (hslot : PublicDiscreteDraws.slotDraw
      ((record.output.preparation.followers.followers i).row.2
        (record.output.preparation.followers.followers i).time).1 ≠
      PublicDiscreteDraws.dataSlot) :
    ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .success result ∧
    result.arrival = 0 ∧
    result.service = min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog ∧
    result.output.S = state.S + min (ActiveFollowerQueueOperation.serviceCapacity rate.n)
      state.backlog ∧
    result.output.delta = min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog ∧
    result.output.backlog = state.backlog -
      min (ActiveFollowerQueueOperation.serviceCapacity rate.n) state.backlog := by
  exact ⟨hchecked,
    ActiveFollowerQueueOperation.serviceSuccess_nonData_update result hoccupied hslot⟩

/-- A checked service failure remains the `.service` failure in the actual
post-record follower result, and `finishFollower` records it separately. -/
theorem prepared_occupied_service_failure_is_preserved
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration :
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (hoccupied : state.status.occupied)
    (hchecked : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .failure) :
    (ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration = .dagger ∧
    (ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).failure =
      some DeclaredFollowerLocalRound.RoundFailure.service := by
  let follower := record.output.preparation.followers.followers i
  let observation := record.output.preparation.feedback.observations
    (PublicDiscreteDraws.followerPlayer p.two_le_m i)
  have hfields := ReferenceActivePhysicalStep.PreparedRound.follower_alignment
    record.output.preparation i
  have hstateNe : state.status ≠ .unoccupied := by
    intro h
    rw [h] at hoccupied
    simp [FollowerStatus.occupied] at hoccupied
  have hrecord :
      (ReferenceActivePhysicalStep.recordFollower
        record.output.preparation.coordinator.downView follower.follower follower.row
        follower.activation follower.time follower.active follower.arm observation state).result =
        .error .service := by
    simp only [ReferenceActivePhysicalStep.recordFollower, dite_eq_right hstateNe]
    rw [DeclaredFollowerLocalRound.recordOrServiceThenDown_occupied
      rate follower.follower follower.row follower.activation follower.time follower.active
      follower.arm observation state hstateNe]
    rw [hfields.2.1, hchecked]
  simp only [ReferenceActivePhysicalStep.finishFollower, hconfiguration]
  rw [hrecord]
  simp

/-- On a successful actual checked service, the true post-record tail exposes
exactly the real `finishFollower` ordinary state when release/finish succeeds. -/
theorem prepared_occupied_finishFollower_success
    {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : record.output.preparation.coordinator.selection = some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration :
      (record.output.preparation.followers.followers i).configuration = .ordinary state memory)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (hstatus : snapshot.status i = state.status)
    (hoccupied : state.status.occupied)
    (hlastDown : state.lastDown = some (selected.view.payload.downRecord i))
    (result : ActiveFollowerQueueOperation.ServiceSuccess p rate.eta rate.n i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state)
    (hchecked : ActiveFollowerQueueOperation.checkedService rate.eta rate.sourceCap
      rate.n rate.n_scale i
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).activation
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state = .success result)
    (next : ReferencePrelaunchFollower.State p rate.eta)
    (nextMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hfinish : DeclaredFollowerLocalRound.releaseAndFinish rate
      (record.output.preparation.followers.followers i).follower
      (record.output.preparation.followers.followers i).row
      (record.output.preparation.followers.followers i).time
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) state memory result.output =
        .ok (next, nextMemory)) :
    (ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).configuration =
        .ordinary next nextMemory ∧
    (ReferenceActivePhysicalStep.finishFollower
      record.output.preparation.coordinator.downView
      (record.output.preparation.followers.followers i)
      (record.output.preparation.feedback.observations
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))).failure = none := by
  have hservice := roundRecord_occupied_service_identification record i selected hselected
    hlive state memory hconfiguration snapshot hstatus hoccupied hlastDown result hchecked
  rcases hservice with ⟨_, _, _, _, _, _, hrecord⟩
  exact ReferenceActivePhysicalStep.finishFollower_success
    record.output.preparation.coordinator.downView
    (record.output.preparation.followers.followers i)
    (record.output.preparation.feedback.observations
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    state result.output next memory nextMemory hconfiguration hrecord hfinish

end Bandits.Support.ReferenceFollowerOccupiedRecorderEvent
