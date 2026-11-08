/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceContinuingDataCandidateLogging
public import Bandits.Support.ReferenceSelectedCandidateRecorderEvent
public import Bandits.Support.ReferenceFollowerOccupiedRecorderEvent
public import Bandits.Support.ReferenceCoordinatorLiveRecording
public import Bandits.Support.FastRewardSliceLaw

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The continuing-live physical recording and fast-arm pair

Sources: `sources/zip4/manuscript/05_binary_transport.tex:354-429`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:140-187,329-382`, and
`sources/zip4/manuscript/06_interruptions.tex:195-233,246-295`.

This module identifies one actual continuing DATA control's physical marker
and auxiliary fast draw on the same complete slice. The prefix theorem below
derives occupied fields and checked candidate logs from the actual run prefix;
the launch specialization consumes the existing source-derived launch
witnesses. The final laws are local fixed-boundary slice pushforwards, not
adaptive conditional laws or source/regret closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceContinuingLiveSlicePreparation
open Bandits.Support.ReferenceContinuingDataCandidateLogging
open Bandits.Support.ReferenceFollowerBufferProvenance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalRecordingSlice
open Bandits.Support.SnapshotRecordingKernel
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.CanonicalFastSampling
open MeasureTheory

namespace Bandits.Support.ReferenceContinuingRecordingFastPair

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- Literal saved inclusive thinning threshold. -/
def savedInclusiveThinThreshold (payload : ReferenceActivePhysicalStep.Payload rate)
    (arm : Fin p.K) : ℝ :=
  (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
    (((2 : ℝ) ^ payload.exponent arm)⁻¹)) /
      SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)

/-- Current unoccupied marker; a current `logEmission` member is required. -/
def currentUnoccupiedCandidateMarker
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1))
    (state : ReferencePrelaunchFollower.State p rate.eta) : Option (Fin p.K) := by
  classical
  match (record.output.followers i).downInput with
  | none => exact none
  | some logged =>
      let own := record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)
      let emission := ReferenceFollowerBufferProvenance.logEmission i record
      let arm := payload.assignment.assigned i
      if hphysical :
          ActiveFollowerLogging.checkedLogging i record.input.row
            (record.input.state.activations i) record.input.time own state = .ok logged ∧
          logged.buffer = state.buffer ++ emission ∧
          ∃ saved, saved ∈ emission ∧ saved ∈ logged.buffer ∧
            saved.calendarRound = record.input.time.val + 1 ∧
            saved.pilot = arm ∧
            saved.thinScalar ≤ savedInclusiveThinThreshold payload arm then
        exact some arm
      else exact none

/-- The source-dispatched physical marker on a DATA control. -/
def physicalDataMarkerOnRecord
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (source : Fin p.m) :
    Option (Fin p.K) := by
  classical
  if hcoordinator : source = ActiveRoundActions.coordinator p.two_le_m then
    exact (record.output.coordinator.recording).bind fun out => out.gateArm
  else
    let i := ActiveRoundActions.followerIndex p.two_le_m source hcoordinator
    match (record.output.preparation.followers.followers i).configuration with
    | .dagger => exact none
    | .ordinary state _ =>
        if state.status = .unoccupied then
          exact currentUnoccupiedCandidateMarker record payload i state
        else
          match state.lastDown with
          | none => exact none
          | some down =>
              if ActiveFollowerQueueOperation.recorderGate rate.eta i record.input.row
                  record.input.time down then
                exact some (PrelaunchBufferRecovery.downArm rate.eta down)
              else exact none

/-- Source-dispatched coordinator, occupied-DOWN, or current-log marker. -/
def physicalMarkerOnRecord
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate) (enabled : Bool) :
    Option (Fin p.K) := by
  classical
  let slice := (record.input.row.2 record.input.time).1
  if enabled = true then
    if slotDraw slice = dataSlot then
      exact physicalDataMarkerOnRecord record payload
        (recorderSourceFromScalar p.two_le_m (coordinate Label.rec slice))
    else exact none
  else exact none

/-- The same physical marker evaluated on each actual candidate control. -/
def candidatePhysicalMarker
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (enabled : Bool) (u : ContinuousLearningRows.TimeControl p) : Option (Fin p.K) :=
  physicalMarkerOnRecord (candidateRecord initial rows selected rewards start count hspan hmode u)
    payload enabled

/-- Reconstruct the canonical iff from source/mask, pilot, and saved threshold. -/
private theorem unoccupiedCanonicalGate_iff
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (snapshot : ActiveRoundActions.Snapshot payload.assignment)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hsnapshot : snapshot.status i = state.status)
    (W : Fin p.K → ℝ) (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * payload.anchor j) :
    SnapshotRecordingKernel.recordingMap p (.live payload.assignment snapshot) true
      rate.eta.val rate.eta.property payload.eta_le_source_cap payload.anchor W
      payload.anchor_pos hWpos hWlower hWupper (record.input.row.2 record.input.time).1 =
        some (payload.assignment.assigned i) ↔
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).1 =
        payload.assignment.assigned i ∧
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
        ((record.input.row.2 record.input.time).1)).val ≤
        savedInclusiveThinThreshold payload (payload.assignment.assigned i) := by
  classical
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let arm := payload.assignment.assigned i
  let slice := (record.input.row.2 record.input.time).1
  let own := record.output.ownEntries player
  have hplayerNe : player ≠ ActiveRoundActions.coordinator p.two_le_m :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
  have hindex : ActiveRoundActions.followerIndex p.two_le_m player hplayerNe = i :=
    ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hplayerNe
  have hactualArm (hslot : slotDraw slice = dataSlot) :
      own.1 = PublicDiscreteDraws.pilotDraw
        (ConstructorDimensions.K_pos p) player slice := by
    have hprepared := record.output.preparation
    have hlocalEq : record.output.preparation.followers.followers i =
        DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i) := by
      rw [record.output_eq]
      rfl
    have hconfig : (DeclaredFollowerLocalRound.prepare rate i record.input.row
        (record.input.state.activations i) record.input.time (record.input.active i)
        (record.input.state.followers i)).configuration = .ordinary state memory := by
      rw [← hlocalEq]
      exact hchoice
    have hownArm : own.1 = (record.output.preparation.followers.followers i).arm := by
      dsimp [own]
      calc
        (record.output.ownEntries player).1 =
            (record.output.preparation.feedback.ownEntries player).1 := by
              rw [record.output_eq]
              rfl
        _ = record.output.preparation.arms.actions player := by
              rw [ReferenceActivePhysicalStep.PreparedRound.own_entry]
        _ = (DeclaredFollowerLocalRound.prepare rate i record.input.row
              (record.input.state.activations i) record.input.time
              (record.input.active i) (record.input.state.followers i)).arm :=
              ReferenceActivePhysicalStep.PreparedRound.action_follower
                record.output.preparation i
        _ = (record.output.preparation.followers.followers i).arm := by
              exact congrArg DeclaredFollowerLocalRound.PreparedRound.arm hlocalEq.symm
    have hdata := ReferenceActiveDataOwnership.ordinary_data_arm payload i record.input.row
      (record.input.state.activations i) record.input.time (record.input.active i)
      (record.input.state.followers i) state memory hconfig (fun hu => False.elim (hu hunoccupied))
      (by simpa [slice] using hslot)
    have hdataArmPilot :
        (DeclaredFollowerLocalRound.prepare rate i record.input.row
          (record.input.state.activations i) record.input.time (record.input.active i)
          (record.input.state.followers i)).arm =
          PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player slice := by
      simpa [slice, hunoccupied] using hdata
    calc
      own.1 = (record.output.preparation.followers.followers i).arm := hownArm
      _ = (DeclaredFollowerLocalRound.prepare rate i record.input.row
            (record.input.state.activations i) record.input.time (record.input.active i)
            (record.input.state.followers i)).arm := by
            exact congrArg DeclaredFollowerLocalRound.PreparedRound.arm hlocalEq
      _ = PublicDiscreteDraws.pilotDraw (ConstructorDimensions.K_pos p) player slice :=
        hdataArmPilot
  have howner : SnapshotRecordingKernel.owns p
      (.live payload.assignment snapshot) player arm := by
    simp [SnapshotRecordingKernel.owns, player, hplayerNe, hindex, arm]
  have hmass : PublicDiscreteDraws.recorderMass p.m player =
      1 / (2 * ((p.m - 1 : ℕ) : ℝ)) := by
    simpa [player, PublicDiscreteDraws.followerCount] using
      PublicDiscreteDraws.recorderMass_follower p.two_le_m i
  have hprob : SnapshotRecordingKernel.actionProbability p
      (.live payload.assignment snapshot) rate.eta.val rate.eta.property
      payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
      player arm = 1 / (p.K : ℝ) := by
    simp [SnapshotRecordingKernel.actionProbability, player, hplayerNe, hindex,
      hsnapshot, hunoccupied]
  have hthreshold : SnapshotRecordingKernel.thinningThreshold p
      (.live payload.assignment snapshot) rate.eta.val rate.eta.property
      payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
      player arm =
      (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
        CanonicalRecordingRates.xi p rate.eta.val payload.anchor arm) /
        SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
    have hdpos : 0 < ((p.m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < p.m - 1 by omega)
    have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hmK := p.m_lt_K
    have hmd : p.m - 1 < p.K := by omega
    have hzpos : 0 < SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) :=
      SparseCalendarReplay.sparseMaskProbability_pos p.K (p.m - 1)
        (ConstructorDimensions.K_pos p) hmd
    unfold SnapshotRecordingKernel.thinningThreshold SnapshotRecordingKernel.rawGateMass
    rw [hprob, hmass, CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
    field_simp [ne_of_gt hdpos, ne_of_gt hKpos, ne_of_gt hzpos]
    ring
  have hdyadic : OrdinaryMessageCodec.dyadicRate (payload.exponent arm) =
      CanonicalRecordingRates.xi p rate.eta.val payload.anchor arm := by
    calc
      OrdinaryMessageCodec.dyadicRate (payload.exponent arm) = payload.rate arm :=
        payload.dyadicRate_eq_rate arm
      _ = CanonicalRecordingRates.xi p rate.eta.val payload.anchor arm :=
        payload.rate_eq_canonical arm
  have hthresholdSaved : SnapshotRecordingKernel.thinningThreshold p
      (.live payload.assignment snapshot) rate.eta.val rate.eta.property
      payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
      player arm = savedInclusiveThinThreshold payload arm := by
    rw [hthreshold, ← hdyadic]
    rfl
  have hgate :
      SnapshotRecordingKernel.recordingMap p (.live payload.assignment snapshot) true
        rate.eta.val rate.eta.property payload.eta_le_source_cap payload.anchor W
        payload.anchor_pos hWpos hWlower hWupper slice = some arm ↔
      SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i record.input.row
            (record.input.state.activations i) record.input.time own) ∧
        own.1 = arm ∧
        (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin slice).val ≤
          savedInclusiveThinThreshold payload arm := by
    constructor
    · intro hrecord
      rcases (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live payload.assignment snapshot) rate.eta.val rate.eta.property
        payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
        slice arm).mp hrecord with ⟨hslot, haction, howns, hmask, hthin⟩
      have hsource := SnapshotRecordingKernel.owns_unique p
        (.live payload.assignment snapshot) arm
        (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec slice)) player howns howner
      have hslotRow : slotDraw slice = dataSlot := by
        simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
      have hsourceRow : recorderSourceDraw p.two_le_m p.m_lt_K slice = player := by
        rw [← CanonicalRecordingSlice.recorderSourceFromScalar_coordinate
          p.two_le_m p.m_lt_K slice]
        exact hsource
      have hpilotArm : pilotDraw (ConstructorDimensions.K_pos p) player slice = arm := by
        rw [hsource] at haction
        rw [show SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
            rate.eta.val rate.eta.property payload.eta_le_source_cap payload.anchor W
            payload.anchor_pos hWpos hWlower hWupper slice player =
              pilotDraw (ConstructorDimensions.K_pos p) player slice by
                simp [SnapshotRecordingKernel.dataAction, player, hplayerNe, hindex,
                  hsnapshot, hunoccupied]] at haction
        exact haction
      have hownArm : own.1 = arm := (hactualArm hslotRow).trans hpilotArm
      rw [hsource] at hmask
      change ∀ j : Fin p.m, j ≠ player →
        pilotDraw (ConstructorDimensions.K_pos p) j slice ≠ arm at hmask
      have hmaskOwn : ∀ j : Fin p.m, j ≠ player →
          pilotDraw (ConstructorDimensions.K_pos p) j slice ≠ own.1 := by
        simpa [hownArm] using hmask
      have htests := (ActiveFollowerLogging.loggingTestsPass_iff_source_mask
          i record.input.row (record.input.state.activations i) record.input.time own).2
        ⟨record.input.active i, hslotRow, hsourceRow, hmaskOwn⟩
      have hthin' := hthin
      rw [hsource, hthresholdSaved] at hthin'
      exact ⟨htests, hownArm, hthin'⟩
    · rintro ⟨htests, hownArm, hthin⟩
      rcases (ActiveFollowerLogging.loggingTestsPass_iff_source_mask
        i record.input.row (record.input.state.activations i) record.input.time own).1
          htests with ⟨_, hslotRow, hsourceRow, hmaskOwn⟩
      have hsource : CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec slice) = player := by
        rw [CanonicalRecordingSlice.recorderSourceFromScalar_coordinate
          p.two_le_m p.m_lt_K slice]
        exact hsourceRow
      have hslot : CanonicalRecordingSlice.slotFromScalar
          (coordinate Label.slot slice) = dataSlot := by
        simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslotRow
      have hpilotArm : pilotDraw (ConstructorDimensions.K_pos p) player slice = arm := by
        calc
          pilotDraw (ConstructorDimensions.K_pos p) player slice = own.1 :=
            (hactualArm hslotRow).symm
          _ = arm := hownArm
      have hmask : CanonicalRecordingSlice.recordingMask
          (ConstructorDimensions.K_pos p) player arm slice := by
        change ∀ ell : Fin p.m, ell ≠ player →
          pilotDraw (ConstructorDimensions.K_pos p) ell slice ≠ arm
        simpa [hownArm] using hmaskOwn
      have hthinMap : (coordinate Label.thin slice).val ≤
          SnapshotRecordingKernel.thinningThreshold p (.live payload.assignment snapshot)
            rate.eta.val rate.eta.property payload.eta_le_source_cap payload.anchor W
            payload.anchor_pos hWpos hWlower hWupper player arm := by
        rw [hthresholdSaved]
        exact hthin
      have hthinSource := hthinMap
      rw [← hsource] at hthinSource
      have haction : SnapshotRecordingKernel.dataAction p
          (.live payload.assignment snapshot) rate.eta.val rate.eta.property
          payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
          slice player = arm := by
        rw [show SnapshotRecordingKernel.dataAction p (.live payload.assignment snapshot)
              rate.eta.val rate.eta.property payload.eta_le_source_cap payload.anchor W
              payload.anchor_pos hWpos hWlower hWupper slice player =
                pilotDraw (ConstructorDimensions.K_pos p) player slice by
                  simp [SnapshotRecordingKernel.dataAction, player, hplayerNe, hindex,
                    hsnapshot, hunoccupied], hpilotArm]
      have hactionSource : SnapshotRecordingKernel.dataAction p
          (.live payload.assignment snapshot) rate.eta.val rate.eta.property
          payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
          slice (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) = arm := by
        simpa only [← hsource] using haction
      have hownerSource : SnapshotRecordingKernel.owns p
          (.live payload.assignment snapshot)
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) arm := by
        simpa only [← hsource] using howner
      have hmaskSource : CanonicalRecordingSlice.recordingMask
          (ConstructorDimensions.K_pos p)
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) arm slice := by
        simpa only [← hsource] using hmask
      exact (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live payload.assignment snapshot) rate.eta.val rate.eta.property
        payload.eta_le_source_cap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
        slice arm).2 ⟨hslot, hactionSource, hownerSource, hmaskSource, hthinSource⟩
  simpa [player, arm, own, slice] using hgate

/-- Checked logger evidence identifies the current unoccupied projection. -/
private theorem currentUnoccupiedCandidateMarker_iff
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hlogging : ∃ logged,
      ActiveFollowerLogging.checkedLogging i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        state = .ok logged ∧
      (record.output.followers i).downInput = some logged ∧
      logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record ∧
      (SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
        ReferenceFollowerBufferProvenance.logEmission i record =
          [SparseCalendarReplay.recordAt (record.input.time.val + 1)
            (ReferencePrelaunchFollower.loggingRound i record.input.row
              (record.input.state.activations i) record.input.time
              (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))]) ∧
      (¬ SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
        ReferenceFollowerBufferProvenance.logEmission i record = [])) :
    currentUnoccupiedCandidateMarker record payload i state =
        some (payload.assignment.assigned i) ↔
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).1 =
        payload.assignment.assigned i ∧
      (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
        ((record.input.row.2 record.input.time).1)).val ≤
        savedInclusiveThinThreshold payload (payload.assignment.assigned i) := by
  classical
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let own := record.output.ownEntries player
  let emission := ReferenceFollowerBufferProvenance.logEmission i record
  let tests := SparseCalendarReplay.loggingTestsPass
    (ReferencePrelaunchFollower.loggingRound i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
  let arm := payload.assignment.assigned i
  rcases hlogging with ⟨logged, hcheck, hdown, happend, htestsEmit, hnotEmit⟩
  have hmemberFields (saved : SparseCalendarReplay.SparseCalendarRecord p.K)
      (hsaved : saved ∈ emission) :
      ∃ own', saved.calendarRound = record.input.time.val + 1 ∧
        saved.pilot = own'.1 ∧ saved.observation = own'.2.val ∧
        saved.thinScalar = (record.input.row.2 record.input.time).1 Label.thin ∧
        own' = record.output.ownEntries player := by
    rcases ReferenceFollowerBufferProvenance.logEmission_member_fields i record saved hsaved with
      ⟨own', ht, hpilot, hobs, hthin, hown⟩
    exact ⟨own', ht, hpilot, hobs, hthin, by simpa [player] using hown⟩
  have hphysicalIff : currentUnoccupiedCandidateMarker record payload i state =
      some arm ↔
      ActiveFollowerLogging.checkedLogging i record.input.row
          (record.input.state.activations i) record.input.time own state = .ok logged ∧
        logged.buffer = state.buffer ++ emission ∧
        ∃ saved, saved ∈ emission ∧ saved ∈ logged.buffer ∧
          saved.calendarRound = record.input.time.val + 1 ∧ saved.pilot = arm ∧
          saved.thinScalar ≤ savedInclusiveThinThreshold payload arm := by
    simp [currentUnoccupiedCandidateMarker, hdown, player, own, emission, arm]
  apply hphysicalIff.trans
  constructor
  · rintro ⟨hcheck', happend', ⟨saved, hsaved, _, hcalendar, hpilot, hthin⟩⟩
    have htests : tests := by
      by_contra hnot
      have hempty := hnotEmit hnot
      have hempty' : emission = [] := by simpa [emission] using hempty
      rw [hempty'] at hsaved
      exact (by simpa using hsaved)
    rcases hmemberFields saved hsaved with ⟨own', _, hpilotOwn, _, hthinSlice, hown⟩
    rw [hown] at hpilotOwn
    refine ⟨htests, hpilotOwn.symm.trans hpilot, ?_⟩
    have hthinEq : (saved.thinScalar : ℝ) =
        (record.input.row.2 record.input.time).1 Label.thin :=
      congrArg Subtype.val hthinSlice
    change (saved.thinScalar : ℝ) ≤ savedInclusiveThinThreshold payload arm at hthin
    rw [hthinEq] at hthin
    exact hthin
  · rintro ⟨htests, hownArm, hthin⟩
    have hemits := htestsEmit htests
    let saved := SparseCalendarReplay.recordAt (record.input.time.val + 1)
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    have hsaved : saved ∈ ReferenceFollowerBufferProvenance.logEmission i record := by
      simp [saved, hemits]
    have hrecordFields :=
      ReferenceFollowerBufferProvenance.logEmission_member_fields i record saved hsaved
    rcases hrecordFields with ⟨own', hcalendar, hpilot, _, hthinSlice, hown⟩
    rw [hown] at hpilot
    have hpilotArm : saved.pilot = arm := hpilot.trans hownArm
    have hthinArm : saved.thinScalar ≤ savedInclusiveThinThreshold payload arm := by
      change (saved.thinScalar : ℝ) ≤ savedInclusiveThinThreshold payload arm
      rw [show (saved.thinScalar : ℝ) =
          (record.input.row.2 record.input.time).1 Label.thin from
            congrArg Subtype.val hthinSlice]
      exact hthin
    have hbuffer : saved ∈ logged.buffer := by
      rw [happend]
      exact List.mem_append_right _ hsaved
    exact ⟨hcheck, happend, saved, hsaved, hbuffer, hcalendar, hpilotArm, hthinArm⟩

/-- Complete checked-logger evidence for one actual DATA control. -/
private def currentLoggerEvidence
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta) : Prop :=
  ∃ logged,
    ActiveFollowerLogging.checkedLogging i record.input.row
      (record.input.state.activations i) record.input.time
      (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      state = .ok logged ∧
    (record.output.followers i).downInput = some logged ∧
    logged.buffer = state.buffer ++ ReferenceFollowerBufferProvenance.logEmission i record ∧
    (SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
      ReferenceFollowerBufferProvenance.logEmission i record =
        [SparseCalendarReplay.recordAt (record.input.time.val + 1)
          (ReferencePrelaunchFollower.loggingRound i record.input.row
            (record.input.state.activations i) record.input.time
            (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))]) ∧
    (¬ SparseCalendarReplay.loggingTestsPass
      (ReferencePrelaunchFollower.loggingRound i record.input.row
        (record.input.state.activations i) record.input.time
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) →
      ReferenceFollowerBufferProvenance.logEmission i record = [])

/-- The enabled continuing DATA marker equals the canonical map. -/
private theorem actual_live_outcome_of_selector
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a)) :
    x.state.coordinator = .live r q base ∧
      CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput x r q base) =
        .continuingChosen d hs c a := by
  have hdispatch : ReferenceActivePhysicalStep.dispatch x =
      .live r q base (.continuingChosen d hs c a) := by
    calc
      ReferenceActivePhysicalStep.dispatch x = (ReferenceActivePhysicalStep.prepare x).coordinator :=
        (ReferenceActivePhysicalStep.prepare x).coordinator_eq.symm
      _ = .live r q base (.continuingChosen d hs c a) := hc
  cases hstate : x.state.coordinator with
  | first =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch
      cases hdispatch
  | live r' q' base' =>
      simp only [ReferenceActivePhysicalStep.dispatch, hstate,
        CoordinatorRoundDispatch.dispatch] at hdispatch
      injection hdispatch with hr hq hbase hout
      subst r'
      have hqEq : q' = q := eq_of_heq hq
      subst q'
      subst base'
      exact ⟨rfl, eq_of_heq hout⟩
  | collection payload ledger proposal =>
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff
        cases hcollection : CoordinatorRoundDispatch.dispatch
            (.collection (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
        all_goals
          simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff, cutoff, clock,
            hcollection] at hdispatch
          cases hdispatch
      · simp [ReferenceActivePhysicalStep.dispatch, hstate, hcutoff] at hdispatch
  | dagger => simp [ReferenceActivePhysicalStep.dispatch, hstate] at hdispatch

private theorem continuing_actual_invariants
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a)) :
    CoordinatorStartRoundCutoffDispatch.dispatch
        (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base = .ok d ∧
      d.collectionInitialization = .success none ∧
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).queueDomainValid ∧
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).previousServiceDomainValid ∧
      (∀ i, base i ≤ p.T * D p) ∧
      CoordinatorLocalArmChoice.assignmentIsLive r.payload
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) x.time ∧
      c.startRoundResult = d.startResult := by
  classical
  have hout := actual_live_outcome_of_selector x r q base d hs c a hc
  let actualOutcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput x r q base) :=
    .continuingChosen (x := ReferenceActivePhysicalStep.liveInput x r q base) d hs c a
  have hcode : ReferenceLiveDispatchOutputMeasurability.dataFormula
      (ReferenceActivePhysicalStep.liveInput x r q base) =
        ReferenceLiveDispatchOutputMeasurability.outcomeData
          actualOutcome := by
    calc
      _ = ReferenceLiveDispatchOutputMeasurability.outcomeData
          (CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput x r q base)) :=
          (ReferenceLiveDispatchOutputMeasurability.outcomeData_dispatchLive _).symm
      _ = _ := congrArg
        (ReferenceLiveDispatchOutputMeasurability.outcomeData
          (x := ReferenceActivePhysicalStep.liveInput x r q base)) hout.2
  -- The proof-free formula preserves the real cutoff dispatch and exposes
  -- every row-independent condition used by the actual continuing branch.
  change ReferenceLiveDispatchOutputMeasurability.dataFormula
      (ReferenceActivePhysicalStep.liveInput x r q base) = _ at hcode
  dsimp only [ReferenceActivePhysicalStep.liveInput] at hcode
  simp only [ReferenceLiveDispatchOutputMeasurability.outcomeData, actualOutcome] at hcode
  cases hcall : CoordinatorStartRoundCutoffDispatch.dispatch
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base with
  | error failure => simp [ReferenceLiveDispatchOutputMeasurability.dataFormula, hcall] at hcode
  | ok out =>
      cases hinitialization : out.collectionInitialization with
      | invalid =>
          simp [ReferenceLiveDispatchOutputMeasurability.dataFormula, hcall,
            hinitialization] at hcode
      | rejected value =>
          simp [ReferenceLiveDispatchOutputMeasurability.dataFormula, hcall,
            hinitialization] at hcode
      | success value =>
          cases value with
          | some ledger =>
              unfold ReferenceLiveDispatchOutputMeasurability.dataFormula at hcode
              simp only [hcall, hinitialization] at hcode
              simp only [ReferenceLiveDispatchOutputMeasurability.choiceData] at hcode
              split_ifs at hcode
          | none =>
              unfold ReferenceLiveDispatchOutputMeasurability.dataFormula at hcode
              simp only [hcall, hinitialization] at hcode
              unfold ReferenceLiveDispatchOutputMeasurability.choiceData at hcode
              by_cases hframe : CoordinatorLiveChoiceRecorderStep.unchangedLiveClockFrame
                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time) out.startResult
              · simp only [ite_eq_left hframe] at hcode
                by_cases hsigma : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock.sigma =
                    some (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload.sigma
                · simp only [ite_eq_left hsigma] at hcode
                  by_cases hgrid : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).gridBoundary =
                      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).priorClock.g
                  · simp only [ite_eq_left hgrid] at hcode
                    by_cases hscore : (ReferenceActivePhysicalStep.liveRegistersAt r x.time).scoreDomainValid
                    · simp only [ite_eq_left hscore] at hcode
                      by_cases hqueue :
                          (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).queueDomainValid
                      · simp only [ite_eq_left hqueue] at hcode
                        by_cases hprevious :
                            (ReferenceActivePhysicalStep.liveOwnedAt r q x.time).previousServiceDomainValid
                        · simp only [ite_eq_left hprevious] at hcode
                          by_cases hbase : ∀ i, base i ≤ p.T * D p
                          · simp only [ite_eq_left hbase] at hcode
                            by_cases hlive : CoordinatorLocalArmChoice.assignmentIsLive
                                (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
                                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                  out.startResult.clock.u)
                                (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
                            · simp only [ite_eq_left hlive] at hcode
                              by_cases hchoice : CoordinatorLocalArmChoice.ChoiceInputsValid
                                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload
                                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
                                    out.startResult.clock.u)
                                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).time
                                  (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights
                              · simp only [ite_eq_left hchoice] at hcode
                                by_cases hboundary : out.startResult.clock.g ≤ p.T + 1
                                · simp only [ite_eq_left hboundary] at hcode
                                  by_cases henvelope :
                                      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementEnvelopeValid
                                  · simp only [ite_eq_left henvelope] at hcode
                                    have hinj := ReferenceLiveDispatchOutputMeasurability.OutcomeData.continuingChosen.inj hcode
                                    rcases hinj with ⟨hdata, hstarted, _⟩
                                    have hout := ReferenceLiveDispatchOutputMeasurability.dispatchData_injective hdata
                                    have hstarted' : c.startRoundResult = d.startResult := by
                                      simpa [hout] using hstarted.symm
                                    subst out
                                    exact ⟨by simp, hinitialization, hqueue, hprevious,
                                      hbase, hlive, hstarted'⟩
                                  · simp only [ite_eq_right henvelope] at hcode
                                    cases hcode
                                · simp only [ite_eq_right hboundary] at hcode
                                  cases hcode
                              · simp only [ite_eq_right hchoice] at hcode
                                cases hcode
                            · simp only [ite_eq_right hlive] at hcode
                              cases hcode
                          · simp only [ite_eq_right hbase] at hcode
                            cases hcode
                        · simp only [ite_eq_right hprevious] at hcode
                          cases hcode
                      · simp only [ite_eq_right hqueue] at hcode
                        cases hcode
                    · simp only [ite_eq_right hscore] at hcode
                      cases hcode
                  · simp only [ite_eq_right hgrid] at hcode
                    cases hcode
                · simp only [ite_eq_right hsigma] at hcode
                  cases hcode
              · simp only [ite_eq_right hframe] at hcode
                cases hcode

private theorem continuingDataMarkerOnRecord_eq_map
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i))
    (henabled : x.time.val + 1 < d.startResult.clock.g)
    (W : Fin p.K → ℝ)
    (hWactual : W = ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time)
    (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, r.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * r.payload.anchor j)
    (hlogs : ∀ i, (states i).status = .unoccupied →
      currentLoggerEvidence (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ :
        ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) i (states i)) :
    physicalDataMarkerOnRecord
      (⟨x, ReferenceActivePhysicalStep.step x, rfl⟩ :
        ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      r.payload (recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec ((x.row.2 x.time).1))) =
    SnapshotRecordingKernel.recordingMap p
      (.live r.payload.assignment
        (ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot r q base x.time d states))
      true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
      r.payload.anchor_pos hWpos hWlower hWupper (x.row.2 x.time).1 := by
  classical
  let record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩
  let snapshot : ActiveRoundActions.Snapshot r.payload.assignment :=
    ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot r q base x.time d states
  let slice := (x.row.2 x.time).1
  let source := recorderSourceFromScalar p.two_le_m (coordinate Label.rec slice)
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) x.time := by
    rcases continuing_actual_invariants x r q base d hs c a hc with
      ⟨_, _, _, _, _, hlive, _⟩
    exact hlive
  by_cases hcoordinator : source = ActiveRoundActions.coordinator p.two_le_m
  · let I := ReferenceActivePhysicalStep.liveRecordingInput
      (ReferenceActivePhysicalStep.prepare x)
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) d.startResult
    let localValid := ReferenceCoordinatorLiveRecording.liveRecordingInput_valid
      (ReferenceActivePhysicalStep.prepare x)
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) d.startResult x.time a
    let valid := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
      localValid
    let E := CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
      (CoordinatorRecorderComplementBridge.recorderInput I) valid r.payload.assignment snapshot
      (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I))
    obtain ⟨out, hrun, hrecording, hgate, _hraw⟩ :=
      ReferenceCoordinatorLiveRecording.continuing_recording_identification
        x r q base d
        (by
          change CoordinatorPhaseClock.startRound p rate.eta.val x.time
            r.priorClock r.clockPending = .ok d.startResult
          exact hs)
        c a hc
        states memories ho hf hlive
    have hnotFrozen : ¬ CoordinatorRecorderComplementBridge.isFrozen I := by
      intro hfrozen
      have hround : x.time.val + 1 ≥ d.startResult.clock.g := by
        simpa [I, CoordinatorRecorderComplementBridge.isFrozen,
          CoordinatorRecordingOperation.isFrozen,
          CoordinatorRecorderComplementBridge.recorderInput,
          CoordinatorRecorderComplementBridge.recorderInputWithWeights,
          ReferenceActivePhysicalStep.liveRecordingInput,
          CoordinatorRecordingOperation.sourceCalendarRound] using hfrozen.2
      omega
    have henabledMap :
        decide (¬ CoordinatorRecorderComplementBridge.isFrozen I) = true :=
      decide_eq_true hnotFrozen
    have hweights :
        CoordinatorRecorderComplementBridge.extendedCurrentWeights I =
          ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time := by
      funext j
      rfl
    have hsourceI : CoordinatorRecordingOperation.selectedRecorder
        (CoordinatorRecorderComplementBridge.recorderInput I) = source := by
      change recorderSourceFromScalar p.two_le_m
        (coordinate Label.rec (ContinuousLearningRows.sliceAt x.time x.row.2)) = _
      rfl
    have hE : E = SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot)
        true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
        r.payload.anchor_pos hWpos hWlower hWupper slice := by
      simp only [E, CoordinatorRecordingOperation.liveCoordinatorSourceMapPart,
        hsourceI, hcoordinator, henabledMap]
      simp only [CoordinatorRecorderComplementBridge.recorderInput,
        CoordinatorRecorderComplementBridge.recorderInputWithWeights]
      change SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor
          (CoordinatorRecorderComplementBridge.extendedCurrentWeights I)
          valid.anchor_pos valid.current_pos valid.anchor_le_current valid.current_le_twice_anchor
          (ContinuousLearningRows.sliceAt x.time x.row.2) = _
      simp only [hweights, hWactual, ContinuousLearningRows.sliceAt, slice]
    have hphysical : physicalDataMarkerOnRecord record r.payload source = out.gateArm := by
      simp [physicalDataMarkerOnRecord, record, source, hcoordinator, hrecording]
    calc
      physicalDataMarkerOnRecord record r.payload source = out.gateArm := hphysical
      _ = E := hgate
      _ = SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos hWpos hWlower hWupper slice := hE
  · let i := ActiveRoundActions.followerIndex p.two_le_m source hcoordinator
    have hplayer : PublicDiscreteDraws.followerPlayer p.two_le_m i = source :=
      ActiveRoundActions.followerPlayer_followerIndex p.two_le_m source hcoordinator
    have hindex : ActiveRoundActions.followerIndex p.two_le_m source hcoordinator = i := rfl
    have hconfig := ho i
    have hstatusEq : snapshot.status i = (states i).status := rfl
    have howner (arm : Fin p.K) (hassigned : arm = r.payload.assignment.assigned i) :
        SnapshotRecordingKernel.owns p (.live r.payload.assignment snapshot) source arm := by
      subst arm
      simp [SnapshotRecordingKernel.owns, hcoordinator, hplayer, hindex]
    have hmapRange (arm : Fin p.K)
        (hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
          rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos hWpos hWlower hWupper slice = some arm) :
        arm = r.payload.assignment.assigned i := by
      rcases (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
        r.payload.anchor W r.payload.anchor_pos hWpos hWlower hWupper slice arm).mp hmap with
        ⟨_, _, howns, _, _⟩
      simp [SnapshotRecordingKernel.owns, hcoordinator, hindex, i, source] at howns
      exact howns
    have hphysicalData : physicalDataMarkerOnRecord record r.payload source =
        match ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration with
        | .dagger => none
        | .ordinary state _ =>
            if state.status = .unoccupied then
              currentUnoccupiedCandidateMarker record r.payload i state
            else
              match state.lastDown with
              | none => none
              | some down =>
                  if ActiveFollowerQueueOperation.recorderGate rate.eta i x.row x.time down then
                    some (PrelaunchBufferRecovery.downArm rate.eta down)
                  else none := by
      simp [physicalDataMarkerOnRecord, record, source, hcoordinator, i, hplayer] <;> rfl
    cases hconfiguration : ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration with
    | dagger =>
        rw [hconfiguration] at hconfig
        cases hconfig
    | ordinary state memory =>
      rw [hconfiguration] at hconfig
      simp [hconfiguration] at hphysicalData
      rw [hphysicalData]
      injection hconfig with hstate hmemory
      subst state
      subst memory
      have hstatus : (states i).status = (states i).status := rfl
      by_cases hunoccupied : (states i).status = .unoccupied
      · have hchoice : (record.output.preparation.followers.followers i).configuration =
            .ordinary (states i) (memories i) := by
          change ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration = _
          exact ho i
        have hlogsI := hlogs i hunoccupied
        rcases hlogsI with ⟨logged, hcheck, hdown, happend, htestsEmit, hnotEmit⟩
        have hlogger : currentLoggerEvidence record i (states i) := by
          refine ⟨logged, ?_, ?_, ?_, htestsEmit, hnotEmit⟩
          · simpa [record] using hcheck
          · simpa [record] using hdown
          · simpa [record] using happend
        have hphysicalIff := currentUnoccupiedCandidateMarker_iff record r.payload i (states i)
          (memories i) hchoice hunoccupied hlogger
        have hcanonicalIff := unoccupiedCanonicalGate_iff record r.payload snapshot i (states i)
          (memories i) hchoice hunoccupied (by rfl) W hWpos hWlower hWupper
        have hiff : currentUnoccupiedCandidateMarker record r.payload i (states i) =
            some (r.payload.assignment.assigned i) ↔
          SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
            rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
            r.payload.anchor_pos hWpos hWlower hWupper slice =
              some (r.payload.assignment.assigned i) := hphysicalIff.trans hcanonicalIff.symm
        have hcurrentRange (arm : Fin p.K)
            (hcurrent : currentUnoccupiedCandidateMarker record r.payload i (states i) = some arm) :
            arm = r.payload.assignment.assigned i := by
          rcases hlogger with ⟨logged, hcheck, hdown', happend, _, _⟩
          simp [currentUnoccupiedCandidateMarker, hdown', hcheck, happend] at hcurrent
          rcases hcurrent with ⟨_, harm⟩
          exact harm.symm
        cases hcurrent : currentUnoccupiedCandidateMarker record r.payload i (states i) with
        | none =>
            cases hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
                rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
                r.payload.anchor_pos hWpos hWlower hWupper slice with
            | none => simp [hunoccupied, hcurrent, hmap]
            | some arm =>
                have harm := hmapRange arm hmap
                subst arm
                have hcontra := hiff.mpr hmap
                rw [hcurrent] at hcontra
                cases hcontra
        | some arm =>
            have harm := hcurrentRange arm hcurrent
            subst arm
            cases hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
                rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
                r.payload.anchor_pos hWpos hWlower hWupper slice with
            | none =>
                have hcontra := hiff.mp hcurrent
                rw [hmap] at hcontra
                cases hcontra
            | some arm =>
                have harm := hmapRange arm hmap
                subst arm
                simp [hunoccupied, hcurrent, hmap]
      · have hoccupied : (states i).status.occupied := by
          cases hstate : (states i).status <;>
            simp [hstate, ActiveRoundActions.FollowerStatus.occupied] at hunoccupied ⊢
        have hfields := hf i hunoccupied
        have hlast : (states i).lastDown = some (r.payload.downRecord i) := hfields
        have hdownArm : PrelaunchBufferRecovery.downArm rate.eta (r.payload.downRecord i) =
            r.payload.assignment.assigned i := by
          apply Fin.ext
          have h := PrelaunchBufferRecovery.down_arm_one_based rate.eta (r.payload.downRecord i)
          rw [r.payload.downRecord_fields i] at h
          exact Nat.add_right_cancel h
        have hownerAssigned := howner (r.payload.assignment.assigned i) rfl
        have hsnapshotOccupied : snapshot.status i ≠ .unoccupied := by
          simpa [hstatusEq] using hunoccupied
        have haction : ∀ z : CanonicalRecordingSlice.Slice p.m p.K,
            SnapshotRecordingKernel.dataAction p (.live r.payload.assignment snapshot)
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
              r.payload.anchor_pos hWpos hWlower hWupper z source =
                r.payload.assignment.assigned i := by
          intro z
          simp [SnapshotRecordingKernel.dataAction, hcoordinator, hplayer, hindex,
            hsnapshotOccupied]
        have hprob : SnapshotRecordingKernel.actionProbability p
            (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
            r.payload.anchor W r.payload.anchor_pos hWpos hWlower hWupper source
            (r.payload.assignment.assigned i) = 1 := by
          simp [SnapshotRecordingKernel.actionProbability, hcoordinator, hplayer, hindex,
            hsnapshotOccupied]
        have hWEvent := SnapshotRecordingKernel.recordingMap_fixed_event_eq p
          (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
          r.payload.anchor W r.payload.anchor_pos hWpos hWlower hWupper source
          (r.payload.assignment.assigned i) hownerAssigned haction hprob
        have hanchorUpper : ∀ j, r.payload.anchor j ≤ 2 * r.payload.anchor j := by
          intro j
          calc
            r.payload.anchor j = 1 * r.payload.anchor j := (one_mul _).symm
            _ ≤ 2 * r.payload.anchor j := by
              exact mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt (r.payload.anchor_pos j))
        have hanchorEvent := SnapshotRecordingKernel.recordingMap_fixed_event_eq p
          (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
          r.payload.anchor r.payload.anchor r.payload.anchor_pos r.payload.anchor_pos
          (fun _ => le_rfl) hanchorUpper source (r.payload.assignment.assigned i)
          hownerAssigned
          (by intro z; simp [SnapshotRecordingKernel.dataAction, hcoordinator, hplayer, hindex,
            hsnapshotOccupied])
          (by simp [SnapshotRecordingKernel.actionProbability, hcoordinator, hplayer,
            hindex, hsnapshotOccupied])
        have hanchorRange (arm : Fin p.K)
            (hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor r.payload.anchor
              r.payload.anchor_pos r.payload.anchor_pos (fun _ => le_rfl) hanchorUpper slice = some arm) :
            arm = r.payload.assignment.assigned i := by
          rcases (SnapshotRecordingKernel.recordingMap_some_iff p
            (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
            r.payload.anchor r.payload.anchor r.payload.anchor_pos r.payload.anchor_pos
            (fun _ => le_rfl) hanchorUpper slice arm).mp hmap with
            ⟨_, _, howns, _, _⟩
          simp [SnapshotRecordingKernel.owns, hcoordinator, hindex, i, source] at howns
          exact howns
        have hWiff :
            SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
              r.payload.anchor_pos hWpos hWlower hWupper slice =
                some (r.payload.assignment.assigned i) ↔
            SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor r.payload.anchor
              r.payload.anchor_pos r.payload.anchor_pos (fun _ => le_rfl) hanchorUpper slice =
                some (r.payload.assignment.assigned i) := by
          have hset := hWEvent.trans hanchorEvent.symm
          have hmem := congrArg (fun s : Set (CanonicalRecordingSlice.Slice p.m p.K) =>
            slice ∈ s) hset
          exact Iff.of_eq (by simpa only [Set.mem_setOf_eq] using hmem)
        have hmapWAnchor :
            SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
              r.payload.anchor_pos hWpos hWlower hWupper slice =
            SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor r.payload.anchor
              r.payload.anchor_pos r.payload.anchor_pos (fun _ => le_rfl) hanchorUpper slice := by
          cases hW : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
              r.payload.anchor_pos hWpos hWlower hWupper slice with
          | none =>
              cases hA : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
                  rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor r.payload.anchor
                  r.payload.anchor_pos r.payload.anchor_pos (fun _ => le_rfl) hanchorUpper slice with
              | none => rfl
              | some arm =>
                  have hrange := hanchorRange arm hA
                  subst arm
                  have hcontra := hWiff.mpr hA
                  rw [hW] at hcontra
                  cases hcontra
          | some arm =>
              have hrange := hmapRange arm hW
              subst arm
              cases hA : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
                  rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor r.payload.anchor
                  r.payload.anchor_pos r.payload.anchor_pos (fun _ => le_rfl) hanchorUpper slice with
              | none =>
                  have hcontra := hWiff.mp hW
                  rw [hA] at hcontra
                  cases hcontra
              | some arm =>
                  have hrange := hanchorRange arm hA
                  subst arm
                  rfl
        have hF := ReferenceFollowerOccupiedRecorderEvent.occupiedGate_eq_canonicalRecordingMap
          r.payload snapshot i x.row x.time (states i) (by rfl) hoccupied
        have hgateMap :
            ActiveFollowerQueueOperation.recorderGate rate.eta i x.row x.time
                (r.payload.downRecord i) ↔
              SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
                rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
                r.payload.anchor_pos hWpos hWlower hWupper slice =
                  some (r.payload.assignment.assigned i) := by
          constructor
          · intro hgate
            exact hWiff.mpr (hF.mp hgate)
          · intro hmap
            exact hF.mpr (hWiff.mp hmap)
        have hresult : (if ActiveFollowerQueueOperation.recorderGate rate.eta i x.row x.time
              (r.payload.downRecord i) then
              some (PrelaunchBufferRecovery.downArm rate.eta (r.payload.downRecord i)) else none) =
            SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot) true
              rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
              r.payload.anchor_pos hWpos hWlower hWupper slice := by
          cases hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot)
              true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
              r.payload.anchor_pos hWpos hWlower hWupper slice with
          | none =>
              have hnot : ¬ ActiveFollowerQueueOperation.recorderGate rate.eta i x.row x.time
                  (r.payload.downRecord i) := by
                intro hg
                have := hgateMap.mp hg
                rw [hmap] at this
                cases this
              simp [hnot]
          | some arm =>
              have harm := hmapRange arm hmap
              subst arm
              have hg : ActiveFollowerQueueOperation.recorderGate rate.eta i x.row x.time
                  (r.payload.downRecord i) := hgateMap.mpr hmap
              simp [hg, hdownArm]
        simpa [hconfiguration, hunoccupied, hlast, hdownArm] using hresult

/-- Rewrite C’s selected-candidate equation through this record’s marker identity. -/
theorem currentCandidateContribution_eq_physicalMarker
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected)
    (i : Fin (p.m - 1))
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice : (record.output.preparation.followers.followers i).configuration =
      .ordinary state memory)
    (hunoccupied : state.status = .unoccupied)
    (hsnapshot : snapshot.status i = state.status)
    (W : Fin p.K → ℝ) (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, selected.view.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * selected.view.payload.anchor j)
    (source : Fin p.m)
    (hmarker : physicalDataMarkerOnRecord record selected.view.payload source =
      SnapshotRecordingKernel.recordingMap p (.live selected.view.payload.assignment snapshot)
        true rate.eta.val rate.eta.property rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper
        (record.input.row.2 record.input.time).1) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1) (D p : ℝ) rate.eta.val
        (selected.view.payload.exponent (selected.view.payload.assignment.assigned i))
        (selected.view.payload.assignment.assigned i) (record.input.time.val + 1)
        (ReferencePrelaunchFollower.logAt i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) =
      if physicalDataMarkerOnRecord record selected.view.payload source =
          some (selected.view.payload.assignment.assigned i) then
        Nat.floor ((D p : ℝ) * rate.eta.val *
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val /
            CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor
              (selected.view.payload.assignment.assigned i))
      else 0 := by
  have hcontribution := ReferenceSelectedCandidateRecorderEvent.current_selected_candidate_eq_marker
    record selected hselected i snapshot state memory hchoice hunoccupied hsnapshot W
    hWpos hWlower hWupper
  rw [← hmarker] at hcontribution
  exact hcontribution

/-- Pair the marker with the same-slice fast draw, including pending pilots. -/
@[expose] def candidatePhysicalFastPair
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (payload : ReferenceActivePhysicalStep.Payload rate) (enabled : Bool)
    (W : Fin p.K → ℝ) (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * payload.anchor j) :
    ContinuousLearningRows.TimeControl p →
      Option (Fin p.K) × FastArm (assignmentSlowSet p payload.assignment) :=
  fun u =>
    (candidatePhysicalMarker initial rows selected rewards start count hspan hmode
        payload enabled u,
      fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
        payload.anchor W payload.anchor_pos hWpos hWlower hWupper
        payload.assignment u.1)

/-- All-controls joint law at one fixed candidate boundary and actual weights. -/
def prefixPhysicalFastPairLaw
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (W : Fin p.K → ℝ) (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * payload.anchor j)
    (snapshot : ActiveRoundActions.Snapshot payload.assignment) : Prop :=
  ∀ u : ContinuousLearningRows.TimeControl p,
    candidatePhysicalFastPair initial rows selected rewards start count hspan hmode
      payload true W hWpos hWlower hWupper u =
    FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
      rate.sourceCap payload.anchor W payload.anchor_pos hWpos hWlower hWupper
      payload.assignment snapshot u.1

/-- All-control identity on one prefix; occupied fields and DATA logs are derived. -/
theorem prefix_physical_fast_pair_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + (count + 1) ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (seed : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (seedMemory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hfirst : initial.coordinator = .first)
    (hseed : ∀ i, initial.followers i = .ordinary (seed i) (seedMemory i))
    (hseedUnoccupied : ∀ i, (seed i).status = .unoccupied)
    (hseedValid : ∀ i, ActiveFollowerLifecycle.localBufferValid (seed i))
    (hseedPairwise : ∀ i, (seed i).buffer.Pairwise
      (fun a b => a.calendarRound < b.calendarRound))
    (hseedTime : ∀ i saved, saved ∈ (seed i).buffer → saved.calendarRound ≤ start)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q
        (candidateInput initial rows selected rewards start count hspan hmode).time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val
      (candidateInput initial rows selected rewards start count hspan hmode).time
      r.priorClock r.clockPending = .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time)
      (candidateInput initial rows selected rewards start count hspan hmode).row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time).payload
      d.startResult (candidateInput initial rows selected rewards start count hspan hmode).time
      (ReferenceActivePhysicalStep.liveRegistersAt r
        (candidateInput initial rows selected rewards start count hspan hmode).time).complementWeights
      (candidateInput initial rows selected rewards start count hspan hmode).row)
    (hc : (ReferenceActivePhysicalStep.prepare
      (candidateInput initial rows selected rewards start count hspan hmode)).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare
      (candidateInput initial rows selected rewards start count hspan hmode)).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (henabled : (candidateInput initial rows selected rewards start count hspan hmode).time.val + 1 <
      d.startResult.clock.g) :
    let x := candidateInput initial rows selected rewards start count hspan hmode
    let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
    let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
      r q base x.time d states
    prefixPhysicalFastPairLaw initial rows selected rewards start count hspan hmode r.payload W
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid) snapshot := by
  classical
  let x := candidateInput initial rows selected rewards start count hspan hmode
  let W := ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time
  let snapshot := ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot
    r q base x.time d states
  have hseedHistory : ∀ i s memory, initial.followers i = .ordinary s memory →
      s.status = .unoccupied := by
    intro i s memory hconfiguration
    have heq : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
        (seed i) (seedMemory i) = .ordinary s memory :=
      Eq.trans (Eq.symm (hseed i)) hconfiguration
    rcases DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj heq with
      ⟨hstate, _⟩
    simpa [hstate] using hseedUnoccupied i
  have hhistory := ReferenceOccupiedFieldHistory.run_prefix_occupied_field_history
    initial rows selected rewards start (count + 1) hspan hmode hfirst hseedHistory count
    (by omega)
  have hliveState := actual_live_outcome_of_selector x r q base d hs c a hc
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload x.state.coordinator =
      some r.payload := by
    rw [hliveState.1]
    rfl
  have hcarried : ReferenceActiveDataOwnership.carriedOccupiedFields r.payload x.state := by
    have hstoredRun : ReferenceAssignmentPayloadPersistence.storedPayload
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count
          (by omega) hmode).finalState.coordinator = some r.payload := by
      simpa [x, candidateInput, ReferenceActivePhysicalHorizon.roundInputAt] using hstored
    have h := hhistory.1 r.payload hstoredRun
    simpa [x, candidateInput, ReferenceActivePhysicalHorizon.roundInputAt] using h
  have hpreparedFields : ∀ i,
      ReferenceActiveDataOwnership.occupiedFields r.payload i
        ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration := by
    intro i
    exact ReferenceActiveDataOwnership.choice_occupied_fields_preserved r.payload i x.row
      (x.state.activations i) x.time (x.active i) (x.state.followers i) (hcarried i)
  have hf : ∀ i, (states i).status ≠ .unoccupied →
      (states i).lastDown = some (r.payload.downRecord i) := by
    intro i hoccupied
    have hi := hpreparedFields i
    rw [ho i] at hi
    exact hi hoccupied
  have hloggingAll (i : Fin (p.m - 1)) (hunoccupied : (states i).status = .unoccupied) :=
    ReferenceContinuingDataCandidateLogging.continuing_data_candidate_logging
      initial rows selected rewards start count hspan hmode i (seed i) (seedMemory i)
      (hseed i) (hseedValid i) (hseedPairwise i) (hseedTime i) states memories ho hunoccupied
  have hpointwise (u : ContinuousLearningRows.TimeControl p) :
      candidatePhysicalFastPair initial rows selected rewards start count hspan hmode
        r.payload true W
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid) u =
      FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property
        rate.sourceCap r.payload.anchor W r.payload.anchor_pos
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        r.payload.assignment snapshot u.1 := by
    by_cases hdata : slotDraw u.1 = dataSlot
    · rcases ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
        x r q base d hs c a hc u with ⟨c_u, a_u, hctor⟩
      have hordinary := ReferenceContinuingLiveSlicePreparation.data_preparation_at_control
        x states memories ho u hdata
      let y := ReferenceContinuingLiveSlicePreparation.inputAtControl x u
      let record := candidateRecord initial rows selected rewards start count hspan hmode u
      have hlogs : ∀ i, (states i).status = .unoccupied →
          currentLoggerEvidence record i (states i) := by
        intro i hunoccupied
        rcases hloggingAll i hunoccupied with ⟨_, _, _, _, hall⟩
        rcases hall u hdata with
          ⟨logged, hcheck, hdown, happend, _, _, htests, hnot, _, _⟩
        exact ⟨logged, hcheck, hdown, happend, htests, hnot⟩
      have hWactual : W =
          ReferenceContinuingLiveSlicePreparation.liveSliceWeights r y.time := by
        simp [W, y]
      have hmap := continuingDataMarkerOnRecord_eq_map y r q base d
        (by simpa [y] using hs) c_u a_u hctor states memories
        (by simpa [y] using hordinary) hf henabled W hWactual
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
          a.choiceInputsValid)
        (by simpa [record, candidateRecord, y] using hlogs)
      apply Prod.ext
      · simpa [candidatePhysicalFastPair, candidatePhysicalMarker, physicalMarkerOnRecord,
          FastRewardSliceLaw.liveRecordingFastPair, candidateRecord, x, hdata, record, y,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
          ReferenceContinuingLiveSlicePreparation.rowAtControl_time] using hmap
      · simp only [candidatePhysicalFastPair, FastRewardSliceLaw.liveRecordingFastPair]
    · have hnone : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot)
          true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
          r.payload.anchor_pos
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid)
          (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
            (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
            a.choiceInputsValid) u.1 = none := by
        cases hmap : SnapshotRecordingKernel.recordingMap p (.live r.payload.assignment snapshot)
            true rate.eta.val rate.eta.property rate.sourceCap r.payload.anchor W
            r.payload.anchor_pos
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid)
            (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
              a.choiceInputsValid) u.1 with
        | none => rfl
        | some arm =>
            rcases (SnapshotRecordingKernel.recordingMap_some_iff p
              (.live r.payload.assignment snapshot) rate.eta.val rate.eta.property rate.sourceCap
              r.payload.anchor W r.payload.anchor_pos
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid)
              (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
                a.choiceInputsValid) u.1 arm).mp hmap with
                ⟨hslot, _, _, _, _⟩
            have hdata' : slotDraw u.1 = dataSlot := by
              simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
            exact (hdata hdata').elim
      apply Prod.ext
      · simp [candidatePhysicalFastPair, candidatePhysicalMarker, physicalMarkerOnRecord,
          FastRewardSliceLaw.liveRecordingFastPair, candidateRecord, x, hdata, hnone,
          ReferenceContinuingLiveSlicePreparation.inputAtControl_row,
          ReferenceContinuingLiveSlicePreparation.rowAtControl_time]
      · simp only [candidatePhysicalFastPair, FastRewardSliceLaw.liveRecordingFastPair]
  simpa only [prefixPhysicalFastPairLaw] using hpointwise

/-- Actual-launch specialization on the source arrays and selected row. -/
theorem actualLaunchedBoundary_physical_fast_pair_eq
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ i,
      ∀ hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed,
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)
    (count : ℕ)
    (span : BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) +
      (count + 1) ≤ p.T) :
    let initial := ReferenceContinuingDataCandidateLogging.actualLaunchState source rewards rate
      C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let active := ReferenceContinuingDataCandidateLogging.actualLaunch_allActiveAtStart
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
    let seedWitness := fun i : Fin (p.m - 1) =>
      ReferenceContinuingDataCandidateLogging.actualLaunchSeedWitness source rewards rate
        C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
    let boundary := ReferenceOccupiedFieldHistory.ofActualLaunchedBoundary_occupied_field_history
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched count span
    let x := candidateInput initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards start count span active
    (∀ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (d : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q x.time) base)
    (hs : CoordinatorPhaseClock.startRound p rate.eta.val x.time r.priorClock r.clockPending =
      .ok d.startResult)
    (c : CoordinatorLiveChoiceRecorderStep.Continuation
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time) x.row)
    (a : CoordinatorRoundDispatch.ArmSelection
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).payload d.startResult x.time
      (ReferenceActivePhysicalStep.liveRegistersAt r x.time).complementWeights x.row)
    (hc : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .live r q base (.continuingChosen d hs c a))
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (ho : ∀ i, ((ReferenceActivePhysicalStep.prepare x).followers.followers i).configuration =
      .ordinary (states i) (memories i))
    (henabled : x.time.val + 1 < d.startResult.clock.g),
    prefixPhysicalFastPairLaw initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
      r.payload (ReferenceContinuingLiveSlicePreparation.liveSliceWeights r x.time)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_pos r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_lower_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceWeights_upper_payload r x.time
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u)
        a.choiceInputsValid)
      (ReferenceContinuingLiveSlicePreparation.liveSliceSnapshot r q base x.time d states)) := by
  classical
  intro initial start active seedWitness boundary x r q base d hs c a hc states memories ho henabled
  have hunoccupied : ∀ i, (seedWitness i).state.status = .unoccupied := by
    intro i
    obtain ⟨s, memory, hordinary, _, hunoccupied⟩ := boundary.2.1 i
    have hstate : s = (seedWitness i).state :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
        (hordinary.symm.trans (seedWitness i).ordinary)).1
    simpa [hstate] using hunoccupied
  exact prefix_physical_fast_pair_eq initial source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards start count span active
    (fun i => (seedWitness i).state) (fun i => (seedWitness i).memory)
    boundary.1 (fun i => (seedWitness i).ordinary)
    hunoccupied
    (fun i => (seedWitness i).valid) (fun i => (seedWitness i).pairwise)
    (fun i saved hsaved => (seedWitness i).saved_before_start saved hsaved)
    r q base d hs c a hc states memories ho henabled

/-- Fixed-family slice transport by `Measure.map_congr` preserves dependence. -/
theorem fixedFamily_joint_pushforward_of_identity
    {β : Type*} [MeasurableSpace β]
    (actual : ContinuousLearningRows.TimeControl p → β)
    (canonical : CanonicalRecordingSlice.Slice p.m p.K → β)
    (hcanonical : Measurable canonical)
    (hidentity : ∀ u, actual u = canonical u.1)
    (family : ContinuousLearningRows.AffineSamples p) :
    Measurable (fun slice : CanonicalRecordingSlice.Slice p.m p.K =>
      actual (slice, family)) ∧
    (ContinuousControlSlice.sliceLaw p.m p.K).map
      (fun slice : CanonicalRecordingSlice.Slice p.m p.K => actual (slice, family)) =
      (ContinuousControlSlice.sliceLaw p.m p.K).map canonical := by
  have heq : (fun slice : CanonicalRecordingSlice.Slice p.m p.K => actual (slice, family)) =
      canonical := funext fun slice => hidentity (slice, family)
  constructor
  · rw [heq]
    exact hcanonical
  · apply Measure.map_congr
    exact Filter.Eventually.of_forall fun slice => hidentity (slice, family)

end Bandits.Support.ReferenceContinuingRecordingFastPair

end
