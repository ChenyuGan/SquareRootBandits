/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon

/-!
# One current unoccupied follower candidate and its marker event

The local logging and thinning rules follow
`sources/zip4/manuscript/05_binary_transport.tex:354-396,411-429` and
`sources/zip4/manuscript/06_interruptions.tex:195-230,256-261`.
This module identifies one current `logAt` contribution in an actual prepared
round with the corresponding arm event of the existing live recording map.
It assumes no history for the carried buffer and proves no whole-run recording
law or chronology statement. The floor uses the actual own feedback, without
identifying it with a collision-free reward. The supplied snapshot is constrained
only at this follower's status; both weight arguments are the payload anchor.
The run membership and live-phase premises retain the intended consumer scope,
although this current-emission identity already follows from the literal round
and local prepared branch.
-/

@[expose] public section

namespace Bandits.Support.ReferenceFollowerCandidateRecorderEvent

open Bandits.Support.ActiveRoundActions
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.SparseCalendarReplay

private theorem localPreparedArm_eq_pilot_of_data
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (activation : ReferencePrelaunchFollower.Activation p) (t : Fin p.T)
    (hactive : activation.val ≤ t.val + 1)
    (input : DeclaredFollowerLocalRound.LocalConfiguration p rate)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hconfiguration :
      (DeclaredFollowerLocalRound.prepare rate i row activation t hactive input).configuration =
        .ordinary s memory)
    (hstatus : s.status = .unoccupied)
    (hslot : slotDraw (row.2 t).1 = dataSlot) :
    (DeclaredFollowerLocalRound.prepare rate i row activation t hactive input).arm =
      pilotDraw (ConstructorDimensions.K_pos p)
        (followerPlayer p.two_le_m i) (row.2 t).1 := by
  classical
  cases input with
  | dagger =>
      simp [DeclaredFollowerLocalRound.prepare] at hconfiguration
  | ordinary initialState initialMemory =>
      simp only [DeclaredFollowerLocalRound.prepare] at hconfiguration ⊢
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta t initialState initialMemory with
      | error reason =>
          simp [hstart] at hconfiguration
      | ok pair =>
          rcases pair with ⟨choiceState, choiceMemory⟩
          cases hoff : ActiveFollowerQueueOperation.checkedUpOffer rate.eta i row activation t
              choiceState with
          | failure =>
              simp [hstart, hoff] at hconfiguration
          | noOffer =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i none with
              | none =>
                  simp [hstart, hoff, hchoice] at hconfiguration
              | some chosen =>
                  simp [hstart, hoff, hchoice] at hconfiguration
                  rcases hconfiguration with ⟨rfl, rfl⟩
                  have hpilot :
                      ActiveFollowerArmChoice.followerArmChoice choiceState row t i none =
                        some (pilotDraw (ConstructorDimensions.K_pos p)
                          (followerPlayer p.two_le_m i) (row.2 t).1) := by
                    simpa [ActiveFollowerArmChoice.followerArmChoice] using
                      ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
                        choiceState (row.2 t) i none hstatus hslot
                  have hchosen : chosen =
                      pilotDraw (ConstructorDimensions.K_pos p)
                        (followerPlayer p.two_le_m i) (row.2 t).1 := by
                    have heq := hchoice.symm.trans hpilot
                    exact Option.some.inj heq
                  simpa [hstart, hoff, hchoice] using hchosen
          | offer offered =>
              cases hchoice : ActiveFollowerArmChoice.followerArmChoice choiceState row t i
                  (some offered) with
              | none =>
                  simp [hstart, hoff, hchoice] at hconfiguration
              | some chosen =>
                  simp [hstart, hoff, hchoice] at hconfiguration
                  rcases hconfiguration with ⟨rfl, rfl⟩
                  have hpilot :
                      ActiveFollowerArmChoice.followerArmChoice choiceState row t i
                          (some offered) =
                        some (pilotDraw (ConstructorDimensions.K_pos p)
                          (followerPlayer p.two_le_m i) (row.2 t).1) := by
                    simpa [ActiveFollowerArmChoice.followerArmChoice] using
                      ActiveFollowerArmChoice.followerArmChoiceCore_unoccupied_data
                        choiceState (row.2 t) i (some offered) hstatus hslot
                  have hchosen : chosen =
                      pilotDraw (ConstructorDimensions.K_pos p)
                        (followerPlayer p.two_le_m i) (row.2 t).1 := by
                    have heq := hchoice.symm.trans hpilot
                    exact Option.some.inj heq
                  simpa [hstart, hoff, hchoice] using hchosen

/-- The current saved contribution is exactly the canonical live marker's
arm-event floor, with the observation taken from this round's literal step
output. The follower choice snapshot is the actual ordinary choice state in
`record.output.preparation`; the only status premise is its unoccupied branch
and the matching status field in the supplied assignment snapshot.

The statement covers failed logging gates and failed thinning by returning
zero, retains the inclusive source comparison, and uses the actual quantized
own feedback even when it is zero. It identifies this one emission only.
-/
theorem current_candidate_eq_marker
    {p : ReferenceActivePhysicalHorizon.Parameters}
    {rate : ReferenceActivePhysicalHorizon.RateInput p}
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (initial : ReferenceActivePhysicalHorizon.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (_hrecord : record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected
      rewards start count hspan hmode).records)
    (i : Fin (p.m - 1))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (baseScores : Fin (p.m - 1) → ℕ)
    (_hphase : record.input.state.coordinator = .live registers owned baseScores)
    (snapshot : ActiveRoundActions.Snapshot registers.payload.assignment)
    (s : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hchoice :
      (record.output.preparation.followers.followers i).configuration = .ordinary s memory)
    (hstatus : s.status = .unoccupied)
    (hsnapshot : snapshot.status i = s.status) :
    SparseCalendarReplay.sparseBufferContribution (p.m - 1)
        (ConstructorDimensions.D p : ℝ) rate.eta.val
        (registers.payload.exponent (registers.payload.assignment.assigned i))
        (registers.payload.assignment.assigned i) (record.input.time.val + 1)
        (ReferencePrelaunchFollower.logAt i (record.input.row)
          (record.input.state.activations i) record.input.time
          (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i))) =
      if SnapshotRecordingKernel.recordingMap p
          (.live registers.payload.assignment snapshot) true rate.eta.val rate.eta.property
          rate.sourceCap registers.payload.anchor registers.payload.anchor
          registers.payload.anchor_pos registers.payload.anchor_pos
          (fun _ => le_rfl) (fun j => by
            rw [two_mul]
            exact le_add_of_nonneg_right
              (le_of_lt (registers.payload.anchor_pos j)))
          (record.input.row.2 record.input.time).1 =
            some (registers.payload.assignment.assigned i)
      then Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        (record.output.ownEntries (PublicDiscreteDraws.followerPlayer p.two_le_m i)).2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor
            (registers.payload.assignment.assigned i))
      else 0 := by
  classical
  let row := record.input.row
  let activation := record.input.state.activations i
  let t := record.input.time
  let slice := (row.2 t).1
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  let arm := registers.payload.assignment.assigned i
  let own := record.output.ownEntries player
  have hanchorTwice : ∀ j, registers.payload.anchor j ≤ 2 * registers.payload.anchor j := by
    intro j
    rw [two_mul]
    exact le_add_of_nonneg_right (le_of_lt (registers.payload.anchor_pos j))
  let marker := SnapshotRecordingKernel.recordingMap p
    (.live registers.payload.assignment snapshot) true rate.eta.val rate.eta.property
    rate.sourceCap registers.payload.anchor registers.payload.anchor
    registers.payload.anchor_pos registers.payload.anchor_pos
    (fun _ => le_rfl) hanchorTwice slice

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
    have hdataArm := localPreparedArm_eq_pilot_of_data i row activation t
      (record.input.active i) (record.input.state.followers i) s memory
      hlocalConfiguration hstatus hslot
    calc
      own.1 = (record.output.preparation.followers.followers i).arm := hownArm
      _ = (DeclaredFollowerLocalRound.prepare rate i row activation t
            (record.input.active i) (record.input.state.followers i)).arm := by
            exact congrArg DeclaredFollowerLocalRound.PreparedRound.arm hlocalEq
      _ = pilotDraw (ConstructorDimensions.K_pos p) player slice := by
            simpa [row, activation, t, slice] using hdataArm

  have hplayerNe : player ≠ ActiveRoundActions.coordinator p.two_le_m :=
    ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i

  have hindex : ActiveRoundActions.followerIndex p.two_le_m player hplayerNe = i :=
    ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hplayerNe

  have hdataAction :
      SnapshotRecordingKernel.dataAction p
        (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap registers.payload.anchor registers.payload.anchor
        registers.payload.anchor_pos registers.payload.anchor_pos
        (fun _ => le_rfl) hanchorTwice slice player =
          pilotDraw (ConstructorDimensions.K_pos p) player slice := by
    simp [SnapshotRecordingKernel.dataAction, player, hplayerNe, hindex,
      hsnapshot, hstatus]

  have hownerPlayer : SnapshotRecordingKernel.owns p
      (.live registers.payload.assignment snapshot) player arm := by
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
        (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap registers.payload.anchor registers.payload.anchor
        registers.payload.anchor_pos registers.payload.anchor_pos
        (fun _ => le_rfl) hanchorTwice player arm = 1 / (p.K : ℝ) := by
    simp [SnapshotRecordingKernel.actionProbability, player, hplayerNe, hindex,
      hsnapshot, hstatus]

  have hthreshold :
      SnapshotRecordingKernel.thinningThreshold p
        (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap registers.payload.anchor registers.payload.anchor
        registers.payload.anchor_pos registers.payload.anchor_pos
        (fun _ => le_rfl) hanchorTwice player arm =
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor arm) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
    unfold SnapshotRecordingKernel.thinningThreshold SnapshotRecordingKernel.rawGateMass
    rw [hactionProbability, hmass,
      CanonicalRecordingSlice.recordingZeta_eq_sparseMaskProbability]
    field_simp [ne_of_gt hdpos, ne_of_gt hKpos, ne_of_gt hzpos]
    ring

  have hdyadic : OrdinaryMessageCodec.dyadicRate
      (registers.payload.exponent arm) =
        CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor arm := by
    calc
      OrdinaryMessageCodec.dyadicRate (registers.payload.exponent arm) =
          registers.payload.rate arm := registers.payload.dyadicRate_eq_rate arm
      _ = CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor arm :=
        registers.payload.rate_eq_canonical arm

  have hthresholdSaved :
      SnapshotRecordingKernel.thinningThreshold p
        (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap registers.payload.anchor registers.payload.anchor
        registers.payload.anchor_pos registers.payload.anchor_pos
        (fun _ => le_rfl) hanchorTwice player arm =
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          (((2 : ℝ) ^ registers.payload.exponent arm)⁻¹)) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
    rw [hthreshold, ← hdyadic]
    rfl

  let thinGate : Prop :=
      (coordinate Label.thin slice).val ≤
        (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
          (((2 : ℝ) ^ registers.payload.exponent arm)⁻¹)) /
          SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1)

  have hfloor :
      Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val *
        (2 : ℝ) ^ registers.payload.exponent arm * own.2.val.val) =
      Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val /
        CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor arm) := by
    congr 1
    calc
      (ConstructorDimensions.D p : ℝ) * rate.eta.val *
          (2 : ℝ) ^ registers.payload.exponent arm *
          own.2.val.val =
        ((ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val) *
          (2 : ℝ) ^ registers.payload.exponent arm := by ring
      _ = (ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val /
          CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor arm := by
        rw [← hdyadic, OrdinaryMessageCodec.dyadicRate]
        have hpow : (2 : ℝ) ^ registers.payload.exponent arm ≠ 0 := by positivity
        field_simp [hpow]

  have hgate : marker = some arm ↔
      SparseCalendarReplay.loggingTestsPass
          (ReferencePrelaunchFollower.loggingRound i row activation t own) ∧
        own.1 = arm ∧ thinGate := by
    constructor
    · intro hrecord
      rcases (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap registers.payload.anchor registers.payload.anchor
        registers.payload.anchor_pos registers.payload.anchor_pos
        (fun _ => le_rfl) hanchorTwice slice arm).mp hrecord with
        ⟨hslot, haction, howns, hmask, hthin⟩
      have hsource := SnapshotRecordingKernel.owns_unique p
        (.live registers.payload.assignment snapshot) arm
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
              (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
              rate.sourceCap registers.payload.anchor registers.payload.anchor
              registers.payload.anchor_pos registers.payload.anchor_pos
              (fun _ => le_rfl) hanchorTwice player arm := by
        rw [hthresholdSaved]
        exact hthin
      have hthinSource := hthinMap
      rw [← hsource] at hthinSource
      have haction : SnapshotRecordingKernel.dataAction p
          (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
          rate.sourceCap registers.payload.anchor registers.payload.anchor
          registers.payload.anchor_pos registers.payload.anchor_pos
          (fun _ => le_rfl) hanchorTwice slice player = arm := by
        rw [hdataAction, hpilotArm]
      have hactionSource : SnapshotRecordingKernel.dataAction p
          (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
          rate.sourceCap registers.payload.anchor registers.payload.anchor
          registers.payload.anchor_pos registers.payload.anchor_pos
          (fun _ => le_rfl) hanchorTwice slice
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) = arm := by
        simpa only [← hsource] using haction
      have hownerSource : SnapshotRecordingKernel.owns p
          (.live registers.payload.assignment snapshot)
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) arm := by
        simpa only [← hsource] using hownerPlayer
      have hmaskSource : CanonicalRecordingSlice.recordingMask
          (ConstructorDimensions.K_pos p)
          (CanonicalRecordingSlice.recorderSourceFromScalar p.two_le_m
            (coordinate Label.rec slice)) arm slice := by
        simpa only [← hsource] using hmask
      exact (SnapshotRecordingKernel.recordingMap_some_iff p
        (.live registers.payload.assignment snapshot) rate.eta.val rate.eta.property
        rate.sourceCap registers.payload.anchor registers.payload.anchor
        registers.payload.anchor_pos registers.payload.anchor_pos
        (fun _ => le_rfl) hanchorTwice slice arm).2
        ⟨hslot, hactionSource, hownerSource, hmaskSource, hthinSource⟩

  change SparseCalendarReplay.sparseBufferContribution (p.m - 1)
      (ConstructorDimensions.D p : ℝ)
      rate.eta.val (registers.payload.exponent arm) arm (t.val + 1)
      (ReferencePrelaunchFollower.logAt i row activation t own) =
    if marker = some arm then
      Nat.floor ((ConstructorDimensions.D p : ℝ) * rate.eta.val * own.2.val.val /
        CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor arm)
    else 0

  have hsingle :
      SparseCalendarReplay.sparseBufferContribution (p.m - 1)
        (ConstructorDimensions.D p : ℝ) rate.eta.val
        (registers.payload.exponent arm) arm (t.val + 1)
        [SparseCalendarReplay.recordAt (t.val + 1)
          (ReferencePrelaunchFollower.loggingRound i row activation t own)] =
      if own.1 = arm then
        SparseCalendarReplay.savedContribution p.K (p.m - 1)
          (ConstructorDimensions.D p : ℝ) rate.eta.val
          (registers.payload.exponent arm) own.2.val
          ((row.2 t).1 Label.thin)
      else 0 := by
    simp [SparseCalendarReplay.sparseBufferContribution, SparseCalendarReplay.recordAt,
      ReferencePrelaunchFollower.loggingRound]

  by_cases hrecord : marker = some arm
  · have ⟨htests, hownArm, hthin⟩ := hgate.mp hrecord
    have hthinSavedScalar :
        ((row.2 t).1 Label.thin).val ≤
          (4 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) *
            (((2 : ℝ) ^ registers.payload.exponent arm)⁻¹)) /
            SparseCalendarReplay.sparseMaskProbability p.K (p.m - 1) := by
      change (coordinate Label.thin slice).val ≤ _ at hthin
      simpa [ContinuousControlSlice.coordinate, slice] using hthin
    rw [ActiveFollowerLogging.logAt_eq_singleton_of_tests i row activation t own htests]
    rw [hsingle]
    simp only [ite_eq_left hownArm]
    rw [SparseCalendarReplay.savedContribution_eq_floor_of_le p.K (p.m - 1)
      (ConstructorDimensions.D p : ℝ) rate.eta.val
      (registers.payload.exponent arm) own.2.val ((row.2 t).1 Label.thin)
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
                  (((2 : ℝ) ^ registers.payload.exponent arm)⁻¹)) /
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

end Bandits.Support.ReferenceFollowerCandidateRecorderEvent

end
