/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerCandidateRecorderEvent
public import Bandits.Support.ReferenceActiveDataOwnership

/-!
# A selected payload and one current unoccupied follower candidate

The local logging and thinning rules follow
`sources/zip4/manuscript/05_binary_transport.tex:354-396,408-431` and
`sources/zip4/manuscript/06_interruptions.tex:195-230,246-269`.
This module identifies one actual prepared follower's current `logAt` sparse
contribution with the corresponding arm event of the selected payload's
recording map. The physical round and successful selection are explicit, while
the algebraic identity itself needs only the follower's ordinary unoccupied
branch and matching snapshot status. Whole current weights remain explicit and
obey the payload anchor envelope; the follower event is independent of their
values. A separate selector records when the payload assignment is locally
live. No history, joint recording law, replay, or physical success theorem is
asserted.
-/

@[expose] public section

namespace Bandits.Support.ReferenceSelectedCandidateRecorderEvent

open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.SparseCalendarReplay

/-- For this selected assignment, the arm marker is present exactly when the
actual follower's saved source/mask/DATA/arm gates and inclusive thinning test
pass. The thinning event uses the original continuous slice and is independent
of the supplied whole current-weight vector. -/
private theorem selected_candidate_gate_iff
    {p : ReferenceActivePhysicalHorizon.Parameters}
    {rate : ReferenceActivePhysicalHorizon.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (i : Fin (p.m - 1))
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      (record.output.preparation.followers.followers i).configuration = .ordinary s memory)
    (hstatus : s.status = .unoccupied)
    (hsnapshot : snapshot.status i = s.status)
    (W : Fin p.K → ℝ)
    (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, selected.view.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * selected.view.payload.anchor j) :
    SnapshotRecordingKernel.recordingMap p
        (.live selected.view.payload.assignment snapshot) true rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W selected.view.payload.anchor_pos
        hWpos hWlower hWupper (record.input.row.2 record.input.time).1 =
          some (selected.view.payload.assignment.assigned i) ↔
      SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i record.input.row
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) ∧
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).1 =
          selected.view.payload.assignment.assigned i ∧
        ((ContinuousControlSlice.coordinate ContinuousControlSlice.Label.thin
          (record.input.row.2 record.input.time).1).val ≤
          (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
            (((2 : ℝ) ^ selected.view.payload.exponent
              (selected.view.payload.assignment.assigned i))⁻¹)) /
            SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)) := by
  classical
  let row := record.input.row
  let activation := record.input.state.activations i
  let t := record.input.time
  let slice := (row.2 t).1
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let arm := selected.view.payload.assignment.assigned i
  let own := record.output.ownEntries player
  let marker := SnapshotRecordingKernel.recordingMap p
    (.live selected.view.payload.assignment snapshot) true rate.eta.val rate.eta.property
    rate.sourceCap selected.view.payload.anchor W
    selected.view.payload.anchor_pos hWpos hWlower hWupper slice

  have hlocalEq : record.output.preparation.followers.followers i =
      DeclaredFollowerLocalRound.prepare rate i row activation t (record.input.active i)
        (record.input.state.followers i) := by
    rw [record.output_eq]
    rfl

  have hlocalConfiguration :
      (DeclaredFollowerLocalRound.prepare rate i row activation t (record.input.active i)
        (record.input.state.followers i)).configuration = .ordinary s memory := by
    rw [← hlocalEq]
    exact hchoice

  have hactualArm (hslot : slotDraw slice = dataSlot) :
      own.1 = pilotDraw (ConstructorDimensions.K_pos p) player slice := by
    have hownArm : own.1 = (record.output.preparation.followers.followers i).arm := by
      dsimp [own]
      calc
        (record.output.ownEntries player).1 =
            (record.output.preparation.feedback.ownEntries player).1 := by
              rw [record.output_eq]
              rfl
        _ = (record.output.preparation.arms.actions player) := by
              rw [ReferenceActivePhysicalStep.PreparedRound.own_entry]
        _ = (DeclaredFollowerLocalRound.prepare rate i row activation t
              (record.input.active i) (record.input.state.followers i)).arm :=
              ReferenceActivePhysicalStep.PreparedRound.action_follower
                record.output.preparation i
        _ = (record.output.preparation.followers.followers i).arm := by
              exact congrArg DeclaredFollowerLocalRound.PreparedRound.arm hlocalEq.symm
    have hdataArm := ReferenceActiveDataOwnership.ordinary_data_arm
      selected.view.payload i row activation t (record.input.active i)
      (record.input.state.followers i) s memory hlocalConfiguration
      (fun hunoccupied => False.elim (hunoccupied hstatus)) hslot
    have hdataArmPilot :
        (DeclaredFollowerLocalRound.prepare rate i row activation t (record.input.active i)
          (record.input.state.followers i)).arm =
          pilotDraw (ConstructorDimensions.K_pos p) player slice := by
      simpa [row, activation, t, slice, hstatus] using hdataArm
    calc
      own.1 = (record.output.preparation.followers.followers i).arm := hownArm
      _ = (DeclaredFollowerLocalRound.prepare rate i row activation t
            (record.input.active i) (record.input.state.followers i)).arm := by
            exact congrArg DeclaredFollowerLocalRound.PreparedRound.arm hlocalEq
      _ = pilotDraw (ConstructorDimensions.K_pos p) player slice := hdataArmPilot

  have hplayerNe : player ≠ ActiveRoundActions.coordinator p.two_le_m :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i

  have hindex : ActiveRoundActions.followerIndex p.two_le_m player hplayerNe = i :=
    ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hplayerNe

  have hdataAction :
      SnapshotRecordingKernel.dataAction p
        (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper slice player =
          pilotDraw (ConstructorDimensions.K_pos p) player slice := by
    simp [SnapshotRecordingKernel.dataAction, player, hplayerNe, hindex,
      hsnapshot, hstatus]

  have hownerPlayer : SnapshotRecordingKernel.owns p
      (.live selected.view.payload.assignment snapshot) player arm := by
    simp [SnapshotRecordingKernel.owns, player, arm, hplayerNe, hindex]

  have hmass : PublicDiscreteDraws.recorderMass p.m player =
      1 / (2 * ((p.m - 1 : ℕ) : ℝ)) := by
    simpa [player, PublicDiscreteDraws.followerCount] using
      PublicDiscreteDraws.recorderMass_follower p.two_le_m i

  have hdpos : 0 < ((p.m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p.m - 1 by omega)
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hmd : p.m - 1 < p.K := by
    have hmK := p.m_lt_K
    omega
  have hzpos : 0 < SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) :=
    SparseCalendarReplay.sparseMaskProbability_pos p.K (p.m - 1)
      (ConstructorDimensions.K_pos p) hmd

  have hactionProbability :
      SnapshotRecordingKernel.actionProbability p
        (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper player arm = 1 / (p.K : ℝ) := by
    simp [SnapshotRecordingKernel.actionProbability, player, hplayerNe, hindex,
      hsnapshot, hstatus]

  have hthreshold :
      SnapshotRecordingKernel.thinningThreshold p
        (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper player arm =
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
    unfold SnapshotRecordingKernel.thinningThreshold SnapshotRecordingKernel.rawGateMass
    rw [hactionProbability, hmass,
      CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
    field_simp [ne_of_gt hdpos, ne_of_gt hKpos, ne_of_gt hzpos]
    ring

  have hdyadic : OrdinaryMessageCodec.dyadicRate
      (selected.view.payload.exponent arm) =
        CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm := by
    calc
      OrdinaryMessageCodec.dyadicRate (selected.view.payload.exponent arm) =
          selected.view.payload.rate arm := selected.view.payload.dyadicRate_eq_rate arm
      _ = CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm :=
        selected.view.payload.rate_eq_canonical arm

  have hthresholdSaved :
      SnapshotRecordingKernel.thinningThreshold p
        (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper player arm =
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          (((2 : ℝ) ^ selected.view.payload.exponent arm)⁻¹)) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
    rw [hthreshold, ← hdyadic]
    rfl

  let thinGate : Prop :=
      (coordinate Label.thin slice).val ≤
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          (((2 : ℝ) ^ selected.view.payload.exponent arm)⁻¹)) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)

  have hgate : marker = some arm ↔
      SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row activation t own) ∧
        own.1 = arm ∧ thinGate := by
    constructor
    · intro hrecord
      rcases (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper slice arm).mp hrecord with
        ⟨hslot, haction, howns, hmask, hthin⟩
      have hsource := SnapshotRecordingKernel.owns_unique p
        (.live selected.view.payload.assignment snapshot) arm
        (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec slice)) player howns hownerPlayer
      have hslotRow : slotDraw slice = dataSlot := by
        simpa only [CanonicalRecordingSlice.slotFromScalar_coordinate] using hslot
      have hsourceRow : recorderSourceDraw p.two_le_m p.m_lt_K slice = player := by
        rw [← CanonicalRecordingSlice.recorderSourceFromScalar_coordinate
          p.two_le_m p.m_lt_K slice]
        exact hsource
      have hpilotArm : pilotDraw (ConstructorDimensions.K_pos p) player slice = arm := by
        rw [hsource] at haction
        rw [hdataAction] at haction
        exact haction
      have hownArm : own.1 = arm := (hactualArm hslotRow).trans hpilotArm
      rw [hsource] at hmask
      change ∀ j : Fin p.m, j ≠ player →
        pilotDraw (ConstructorDimensions.K_pos p) j slice ≠ arm at hmask
      have hmaskOwn : ∀ j : Fin p.m, j ≠ player →
          pilotDraw (ConstructorDimensions.K_pos p) j slice ≠ own.1 := by
        simpa [hownArm] using hmask
      have htests : SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row activation t own) :=
        (ActiveFollowerLogging.loggingTestsPass_iff_source_mask i row activation t own).2
          ⟨record.input.active i, hslotRow, hsourceRow, hmaskOwn⟩
      have hthin' := hthin
      rw [hsource, hthresholdSaved] at hthin'
      exact ⟨htests, hownArm, hthin'⟩
    · rintro ⟨htests, hownArm, hthin⟩
      rcases (ActiveFollowerLogging.loggingTestsPass_iff_source_mask i row activation t own).1
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
      have hthinMap :
          (coordinate Label.thin slice).val ≤
            SnapshotRecordingKernel.thinningThreshold p
              (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
              rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper player arm := by
        rw [hthresholdSaved]
        exact hthin
      have hthinSource := hthinMap
      rw [← hsource] at hthinSource
      have haction : SnapshotRecordingKernel.dataAction p
          (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
          rate.sourceCap selected.view.payload.anchor W
          selected.view.payload.anchor_pos hWpos hWlower hWupper slice player = arm := by
        rw [hdataAction, hpilotArm]
      have hactionSource : SnapshotRecordingKernel.dataAction p
          (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
          rate.sourceCap selected.view.payload.anchor W
          selected.view.payload.anchor_pos hWpos hWlower hWupper slice
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) = arm := by
        simpa only [← hsource] using haction
      have hownerSource : SnapshotRecordingKernel.owns p
          (.live selected.view.payload.assignment snapshot)
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) arm := by
        simpa only [← hsource] using hownerPlayer
      have hmaskSource : CanonicalRecordingSlice.recordingMask
          (ConstructorDimensions.K_pos p)
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) arm slice := by
        simpa only [← hsource] using hmask
      exact (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live selected.view.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W
        selected.view.payload.anchor_pos hWpos hWlower hWupper slice arm).2
        ⟨hslot, hactionSource, hownerSource, hmaskSource, hthinSource⟩

  exact hgate

/-- The current saved contribution is exactly the selected payload's live
arm-event floor, with the observation taken from this round's literal step
output. The only follower-state premise is the actual ordinary unoccupied
choice branch and matching snapshot status. The actual successful selection is
kept explicit, but no incoming coordinator-live state is required.

Failed logging gates, absent `logAt`, failed thinning, zero feedback, and a zero
floor are all covered. The thinning comparison is inclusive, and the floor
uses the actual quantized own feedback. -/
theorem current_selected_candidate_eq_marker
    {p : ReferenceActivePhysicalHorizon.Parameters}
    {rate : ReferenceActivePhysicalHorizon.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (_hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected)
    (i : Fin (p.m - 1))
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      (record.output.preparation.followers.followers i).configuration = .ordinary s memory)
    (hstatus : s.status = .unoccupied)
    (hsnapshot : snapshot.status i = s.status)
    (W : Fin p.K → ℝ)
    (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, selected.view.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * selected.view.payload.anchor j) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1)
        (ConstructorDimensions.D p : ℝ) rate.eta.val
        (selected.view.payload.exponent (selected.view.payload.assignment.assigned i))
        (selected.view.payload.assignment.assigned i) (record.input.time.val + 1)
        (ReferencePrelaunchFollower.logAt i (record.input.row)
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) =
      if SnapshotRecordingKernel.recordingMap p
          (.live selected.view.payload.assignment snapshot) true rate.eta.val rate.eta.property
          rate.sourceCap selected.view.payload.anchor W selected.view.payload.anchor_pos
          hWpos hWlower hWupper (record.input.row.2 record.input.time).1 =
            some (selected.view.payload.assignment.assigned i)
      then Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor
            (selected.view.payload.assignment.assigned i))
      else 0 := by
  classical
  let row := record.input.row
  let activation := record.input.state.activations i
  let t := record.input.time
  let slice := (row.2 t).1
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let arm := selected.view.payload.assignment.assigned i
  let own := record.output.ownEntries player
  let marker := SnapshotRecordingKernel.recordingMap p
    (.live selected.view.payload.assignment snapshot) true rate.eta.val rate.eta.property
    rate.sourceCap selected.view.payload.anchor W
    selected.view.payload.anchor_pos hWpos hWlower hWupper slice
  let thinGate : Prop :=
      (coordinate Label.thin slice).val ≤
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          (((2 : ℝ) ^ selected.view.payload.exponent arm)⁻¹)) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)
  have hgate : marker = some arm ↔
      SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row activation t own) ∧
        own.1 = arm ∧ thinGate := by
    exact selected_candidate_gate_iff record selected i snapshot s memory
      hchoice hstatus hsnapshot W hWpos hWlower hWupper

  have hdyadic : OrdinaryMessageCodec.dyadicRate
      (selected.view.payload.exponent arm) =
        CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm := by
    calc
      OrdinaryMessageCodec.dyadicRate (selected.view.payload.exponent arm) =
          selected.view.payload.rate arm := selected.view.payload.dyadicRate_eq_rate arm
      _ = CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm :=
        selected.view.payload.rate_eq_canonical arm

  have hfloor :
      Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        (2 : ℝ) ^ selected.view.payload.exponent arm * own.2.val.val) =
      Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val /
        CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm) := by
    congr 1
    calc
      (ConstructorDimensions.D p : ℝ) * rate.eta.val *
          (2 : ℝ) ^ selected.view.payload.exponent arm * own.2.val.val =
        ((ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val) *
          (2 : ℝ) ^ selected.view.payload.exponent arm := by ring
      _ = (ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm := by
        rw [← hdyadic, OrdinaryMessageCodec.dyadicRate]
        have hpow : (2 : ℝ) ^ selected.view.payload.exponent arm ≠ 0 := by positivity
        field_simp [hpow]

  change SparseCalendarReplay.sparseBufferContribution (p.m - 1)
      (ConstructorDimensions.D p : ℝ)
      rate.eta.val (selected.view.payload.exponent arm) arm (t.val + 1)
      (ReferencePrelaunchFollower.logAt i row activation t own) =
    if marker = some arm then
      Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val /
        CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor arm)
    else 0

  have hsingle :
      SparseCalendarReplay.sparseBufferContribution (p.m - 1)
        (ConstructorDimensions.D p : ℝ) rate.eta.val
        (selected.view.payload.exponent arm) arm (t.val + 1)
        [SparseCalendarReplay.recordAt (t.val + 1)
          (ReferencePrelaunchFollower.loggingRound i row activation t own)] =
      if own.1 = arm then
        SparseCalendarReplay.savedContribution p.K (p.m - 1)
          (ConstructorDimensions.D p : ℝ) rate.eta.val
          (selected.view.payload.exponent arm) own.2.val
          ((row.2 t).1 Label.thin)
      else 0 := by
    simp [SparseCalendarReplay.sparseBufferContribution, SparseCalendarReplay.recordAt,
      ReferencePrelaunchFollower.loggingRound]

  by_cases hrecord : marker = some arm
  · have ⟨htests, hownArm, hthin⟩ := hgate.mp hrecord
    have hthinSavedScalar :
        ((row.2 t).1 Label.thin).val ≤
          (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
            (((2 : ℝ) ^ selected.view.payload.exponent arm)⁻¹)) /
            SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
      change (coordinate Label.thin slice).val ≤ _ at hthin
      simpa [ContinuousControlSlice.coordinate, slice] using hthin
    rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation t own htests]
    rw [hsingle]
    simp only [ite_eq_left hownArm]
    rw [SparseCalendarReplay.savedContribution_eq_floor_of_le p.K (p.m - 1)
      (ConstructorDimensions.D p : ℝ) rate.eta.val
      (selected.view.payload.exponent arm) own.2.val ((row.2 t).1 Label.thin)
      hthinSavedScalar, hfloor, hrecord]
    simp
  · have hnot : ¬ (SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i row activation t own) ∧
      own.1 = arm ∧ thinGate) := by
      intro h
      exact hrecord (hgate.mpr h)
    by_cases htests : SparseCalendarReplay.loggingTestsPass
        (ReferencePrelaunchFollower.loggingRound i row activation t own)
    · by_cases hownArm : own.1 = arm
      · by_cases hthin : thinGate
        · exact False.elim (hnot ⟨htests, hownArm, hthin⟩)
        · have hthinNotSaved :
              ¬ ((row.2 t).1 Label.thin).val ≤
                (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
                  (((2 : ℝ) ^ selected.view.payload.exponent arm)⁻¹)) /
                  SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
            intro hthinSaved
            apply hthin
            change (coordinate Label.thin slice).val ≤ _
            simpa [ContinuousControlSlice.coordinate, slice] using hthinSaved
          rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation t own htests]
          rw [hsingle]
          simp only [ite_eq_left hownArm]
          simp [SparseCalendarReplay.savedContribution, hthinNotSaved, hrecord]
      · rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation t own htests]
        rw [hsingle]
        simp [hownArm, hrecord]
    · rw [ActiveFollowerLogging.logAt_eq_nil_of_not_tests i row activation t own htests]
      simp [SparseCalendarReplay.sparseBufferContribution, hrecord]


/-- The selected follower's arm event is unchanged when the whole current
weight vector in the marker is replaced by the payload anchor. The statement
compares only this assigned-arm event; it gives no joint marker or fast-arm
identity. -/
theorem selected_candidate_arm_event_independent_of_weights
    {p : ReferenceActivePhysicalHorizon.Parameters}
    {rate : ReferenceActivePhysicalHorizon.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (_hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected)
    (i : Fin (p.m - 1))
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      (record.output.preparation.followers.followers i).configuration = .ordinary s memory)
    (hstatus : s.status = .unoccupied)
    (hsnapshot : snapshot.status i = s.status)
    (W : Fin p.K → ℝ)
    (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, selected.view.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * selected.view.payload.anchor j) :
    SnapshotRecordingKernel.recordingMap p
        (.live selected.view.payload.assignment snapshot) true rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor W selected.view.payload.anchor_pos
        hWpos hWlower hWupper (record.input.row.2 record.input.time).1 =
          some (selected.view.payload.assignment.assigned i) ↔
      SnapshotRecordingKernel.recordingMap p
        (.live selected.view.payload.assignment snapshot) true rate.eta.val rate.eta.property
        rate.sourceCap selected.view.payload.anchor selected.view.payload.anchor
        selected.view.payload.anchor_pos selected.view.payload.anchor_pos (fun _ => le_rfl)
        (fun j => by
          rw [two_mul]
          exact le_add_of_nonneg_right
            (le_of_lt (selected.view.payload.anchor_pos j)))
        (record.input.row.2 record.input.time).1 =
          some (selected.view.payload.assignment.assigned i) := by
  have hW := selected_candidate_gate_iff record selected i snapshot s memory
    hchoice hstatus hsnapshot W hWpos hWlower hWupper
  have hanchor := selected_candidate_gate_iff record selected i snapshot s memory
    hchoice hstatus hsnapshot selected.view.payload.anchor
    selected.view.payload.anchor_pos (fun _ => le_rfl)
    (fun j => by
      rw [two_mul]
      exact le_add_of_nonneg_right
        (le_of_lt (selected.view.payload.anchor_pos j)))
  exact hW.trans hanchor.symm

/-- The honest local selector for using a selected payload's recording map as
a live marker. This is a selected-time predicate; it does not assert that the
physical coordinator state has already entered `.live`. -/
noncomputable def selectedLiveCandidateMarker
    {p : ReferenceActivePhysicalHorizon.Parameters}
    {rate : ReferenceActivePhysicalHorizon.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (enabled : Bool)
    (W : Fin p.K → ℝ)
    (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, selected.view.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * selected.view.payload.anchor j) :
    Option (Fin p.K) := by
  classical
  exact if CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time then
    SnapshotRecordingKernel.recordingMap p
      (.live selected.view.payload.assignment snapshot) enabled rate.eta.val rate.eta.property
      rate.sourceCap selected.view.payload.anchor W selected.view.payload.anchor_pos
      hWpos hWlower hWupper (record.input.row.2 record.input.time).1
  else none

/-- For an actually selected payload whose local assignment-live selector
holds, the enabled candidate contribution agrees with its marker floor. When
recording is disabled the contribution side is explicitly zero, even though
physical candidate logging may still have produced a `logAt` record. -/
theorem enabled_current_candidate_eq_selected_live_marker
    {p : ReferenceActivePhysicalHorizon.Parameters}
    {rate : ReferenceActivePhysicalHorizon.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (_hselected : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection =
      some selected)
    (i : Fin (p.m - 1))
    (snapshot : ActiveRoundActions.Snapshot selected.view.payload.assignment)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      (record.output.preparation.followers.followers i).configuration = .ordinary s memory)
    (hstatus : s.status = .unoccupied)
    (hsnapshot : snapshot.status i = s.status)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff record.input.time)
    (enabled : Bool)
    (W : Fin p.K → ℝ)
    (hWpos : ∀ j, 0 < W j)
    (hWlower : ∀ j, selected.view.payload.anchor j ≤ W j)
    (hWupper : ∀ j, W j ≤ 2 * selected.view.payload.anchor j) :
    (if enabled then
      SparseCalendarReplay.sparseBufferContribution (p.m - 1)
        (ConstructorDimensions.D p : ℝ) rate.eta.val
        (selected.view.payload.exponent (selected.view.payload.assignment.assigned i))
        (selected.view.payload.assignment.assigned i) (record.input.time.val + 1)
        (ReferencePrelaunchFollower.logAt i (record.input.row)
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
     else 0) =
      if selectedLiveCandidateMarker record selected snapshot enabled W hWpos hWlower hWupper =
          some (selected.view.payload.assignment.assigned i)
      then Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor
            (selected.view.payload.assignment.assigned i))
      else 0 := by
  cases enabled with
  | false =>
      classical
      simp [selectedLiveCandidateMarker, SnapshotRecordingKernel.recordingMap]
  | true =>
      simpa [selectedLiveCandidateMarker, hlive] using
        current_selected_candidate_eq_marker record selected _hselected i snapshot s memory
          hchoice hstatus hsnapshot W hWpos hWlower hWupper

end Bandits.Support.ReferenceSelectedCandidateRecorderEvent

end
