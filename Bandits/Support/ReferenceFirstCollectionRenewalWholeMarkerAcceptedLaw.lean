/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# The actual renewal whole marker and its accepted queue arrival

The source, pair measure, retained field, whole reward table, and incoming
queue are the existing first-renewal objects. The marker includes the current
saved observation of an unoccupied follower. In particular it is not the
coordinator complement gate.

Sources: `04_slow_fast_learner.tex:93-168,182-188,245-290`,
`06_interruptions.tex:355-426`, and
`appendix_a_local_protocol.tex:44-64,100-108`, under
`sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw


abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : TimeControl p)

local notation "Z" => ReferenceFirstCollectionRenewalSourceCurrentPrefix.Source rate rewards C_star C_h u t
local notation "B" => ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
local notation "mu" => ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "R" => ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap R
  (inferInstance : MeasurableSpace (ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p))
local notation "qp" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "cell" => ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell rate rewards C_star C_h u t
local notation "incoming" => ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite rate rewards C_star C_h u t

/-- Indicator of the full actual current marker at the second source. -/
def markerTest (j : Fin p.K) (b : B) : ℝ :=
  {b : B | (cell b.2).recordedArm = some j}.indicator (fun _ => 1) b

/-- Indicator of the actual bottom outcome, including a present cell with
no recorded arm. -/
def noneTest (b : B) : ℝ :=
  {b : B | (cell b.2).recordedArm = none}.indicator (fun _ => 1) b

/-- The literal normalized arrival accepted by the existing stopped run. -/
def fullAcceptedA (j : Fin p.K) (b : B) : ℝ :=
  ((RecordedQueueRun.acceptedRecord qp (incoming b.2) (cell b.2) j).2 : ℝ) /
    (rate.n : ℝ)

private theorem measurable_marker : Measurable (fun b : B => (cell b.2).recordedArm) := by
  exact (measurable_fst.comp (measurable_snd.comp
    (ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholeCellNumericalCoordinates rate rewards C_star C_h u t))).comp
      measurable_snd

theorem measurable_markerTest (j : Fin p.K) :
    Measurable (markerTest rate rewards C_star C_h u t j) :=
  measurable_const.indicator
    ((measurable_marker rate rewards C_star C_h u t) (measurableSet_singleton _))

theorem measurable_noneTest : Measurable (noneTest rate rewards C_star C_h u t) :=
  measurable_const.indicator
    ((measurable_marker rate rewards C_star C_h u t) (measurableSet_singleton _))

theorem markerTest_bounds (j : Fin p.K) (b : B) :
    0 ≤ markerTest rate rewards C_star C_h u t j b ∧
      markerTest rate rewards C_star C_h u t j b ≤ 1 := by
  by_cases h : (cell b.2).recordedArm = some j <;> simp [markerTest, h]

theorem noneTest_bounds (b : B) :
    0 ≤ noneTest rate rewards C_star C_h u t b ∧
      noneTest rate rewards C_star C_h u t b ≤ 1 := by
  by_cases h : (cell b.2).recordedArm = none <;> simp [noneTest, h]

private theorem integrable_of_bounds {f : B → ℝ} (hf : Measurable f)
    (c : ℝ) (hb : ∀ b, 0 ≤ f b ∧ f b ≤ c) : Integrable f mu := by
  refine (integrable_const c).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with b
  rw [Real.norm_of_nonneg (hb b).1]
  exact (hb b).2

theorem integrable_markerTest (j : Fin p.K) :
    Integrable (markerTest rate rewards C_star C_h u t j) mu :=
  integrable_of_bounds rate rewards C_star C_h u t
    (measurable_markerTest rate rewards C_star C_h u t j) 1
    (markerTest_bounds rate rewards C_star C_h u t j)

theorem integrable_noneTest : Integrable (noneTest rate rewards C_star C_h u t) mu :=
  integrable_of_bounds rate rewards C_star C_h u t
    (measurable_noneTest rate rewards C_star C_h u t) 1
    (noneTest_bounds rate rewards C_star C_h u t)

/-- Exactly one arm or bottom occurs in the present whole cell. -/
theorem noneTest_eq_one_sub_sum (b : B) :
    noneTest rate rewards C_star C_h u t b =
      1 - ∑ j, markerTest rate rewards C_star C_h u t j b := by
  cases h : (cell b.2).recordedArm with
  | none => simp [noneTest, markerTest, h]
  | some j => simp [noneTest, markerTest, Set.indicator_apply, h]

/-- Enabled zero arrivals still produce an enabled queue record. The old
overflow flag alone suppresses the actual renewal update. -/
theorem fullAcceptedA_eq (j : Fin p.K) (b : B) :
    fullAcceptedA rate rewards C_star C_h u t j b =
      if (incoming b.2).overflow then 0
      else (RecordedQueueRun.quantizedArrival qp (cell b.2) j : ℝ) / rate.n := by
  unfold fullAcceptedA
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_acceptedRecord]
  cases (incoming b.2).overflow <;> simp

private theorem measurable_overflow : Measurable (fun b : B => (incoming b.2).overflow) :=
  (measurable_fst.comp (measurable_snd.comp
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout rate rewards C_star C_h u t))).comp measurable_snd

theorem measurable_fullAcceptedA (j : Fin p.K) :
    Measurable (fullAcceptedA rate rewards C_star C_h u t j) := by
  have ha : Measurable (fun b : B => RecordedQueueRun.quantizedArrival qp (cell b.2) j) :=
    ((measurable_pi_apply j).comp (measurable_snd.comp
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholeCellArrivalCoordinates rate rewards C_star C_h u t))).comp
        measurable_snd
  change Measurable (fun b : B => fullAcceptedA rate rewards C_star C_h u t j b)
  simp_rw [fullAcceptedA_eq]
  exact Measurable.ite
    ((measurable_overflow rate rewards C_star C_h u t) (measurableSet_singleton true))
    measurable_const ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp ha |>.div_const _)

private theorem wholeCell_feasible (z : Z) :
    ∀ j, (rate.n : ℝ) ≤ (D p : ℝ) * (cell z).rate j := by
  obtain ⟨_, selected, _, _, hrate⟩ := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_numerical rate rewards C_star C_h u t z
  intro j
  rw [hrate, rate.n_scale, mul_comm rate.eta.val]
  exact mul_le_mul_of_nonneg_left
    ((AssignmentStartPayload.Input.eta_le_beta (p := p) (eta := rate.eta)).trans
      (selected.view.payload.beta_le_rate j)) (Nat.cast_nonneg _)

/-- A uniform finite bound uses the source integer arrival bound, with no
integrability or conditional-law premise. -/
theorem fullAcceptedA_bounds (j : Fin p.K) (b : B) :
    0 ≤ fullAcceptedA rate rewards C_star C_h u t j b ∧
      fullAcceptedA rate rewards C_star C_h u t j b ≤ (D p : ℝ) / rate.n := by
  have hn : 0 < (rate.n : ℝ) := Nat.cast_pos.mpr (qp).n_pos
  have hle := RecordedQueueRun.acceptedRecord_arrival_le_D qp
    (incoming b.2) (cell b.2) (wholeCell_feasible rate rewards C_star C_h u t b.2) j
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hn.le
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) hn.le

theorem integrable_fullAcceptedA (j : Fin p.K) :
    Integrable (fullAcceptedA rate rewards C_star C_h u t j) mu :=
  integrable_of_bounds rate rewards C_star C_h u t
    (measurable_fullAcceptedA rate rewards C_star C_h u t j) _
    (fullAcceptedA_bounds rate rewards C_star C_h u t j)

theorem integrable_fullAcceptedA_sq (j : Fin p.K) :
    Integrable (fun b => (fullAcceptedA rate rewards C_star C_h u t j b) ^ 2) mu := by
  apply integrable_of_bounds rate rewards C_star C_h u t
    ((measurable_fullAcceptedA rate rewards C_star C_h u t j).pow_const 2)
    (((D p : ℝ) / rate.n) ^ 2)
  intro b
  exact ⟨sq_nonneg _, pow_le_pow_left₀
    (fullAcceptedA_bounds rate rewards C_star C_h u t j b).1
    (fullAcceptedA_bounds rate rewards C_star C_h u t j b).2 2⟩

open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalGateCoefficient

open ContinuousControlSlice CanonicalRecordingSlice PublicDiscreteDraws

/-- The actual owner in the canonical ordered follower assignment: the
inverse sorted rank on the slow set, and the coordinator on its complement. -/
def sourceOwner (U : SlowSet p) (j : Fin p.K) : Fin p.m :=
  if hj : j ∈ U.val then
    followerPlayer p.two_le_m
      ((U.val.orderIsoOfFin (CanonicalAssignmentVector.slowSet_card_eq_sub_one
        p.two_le_m U)).symm ⟨j, hj⟩)
  else ActiveRoundActions.coordinator p.two_le_m

private theorem owns_sourceOwner (payload : ReferenceActivePhysicalStep.Payload rate)
    (snapshot : ActiveRoundActions.Snapshot payload.assignment) (j : Fin p.K) :
    SnapshotRecordingKernel.owns p (.live payload.assignment snapshot)
      (sourceOwner payload.slowSet j) j := by
  classical
  by_cases hj : j ∈ payload.slowSet.val
  · let e := payload.slowSet.val.orderIsoOfFin
      (CanonicalAssignmentVector.slowSet_card_eq_sub_one p.two_le_m payload.slowSet)
    let i : ActiveRoundActions.Follower p.m := e.symm ⟨j, hj⟩
    have hi : payload.assignment.assigned i = j :=
      congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)
    have hnot := ActiveRoundActions.followerPlayer_ne_coordinator p.two_le_m i
    rw [sourceOwner, dite_eq_left hj]
    change SnapshotRecordingKernel.owns p (.live payload.assignment snapshot)
      (followerPlayer p.two_le_m i) j
    simp only [SnapshotRecordingKernel.owns, hnot, dite_false]
    have hidx := ActiveRoundActions.followerIndex_followerPlayer p.two_le_m i hnot
    exact hi.symm.trans (congrArg payload.assignment.assigned hidx.symm)
  · rw [sourceOwner, dite_eq_right hj]
    change j ∉ Finset.univ.image payload.assignment.assigned
    have himage : Finset.univ.image payload.assignment.assigned = payload.slowSet.val :=
      CanonicalAssignmentVector.followerArm_image p.two_le_m payload.slowSet
    exact himage.symm ▸ hj

private theorem univ_missing_nonempty :
    (Finset.univ : Finset (ActiveRoundActions.Follower p.m)) ≠ ∅ := by
  let i : ActiveRoundActions.Follower p.m := ⟨0, by
    have hm := p.two_le_m
    simp only [followerCount]
    omega⟩
  exact Finset.ne_empty_of_mem (Finset.mem_univ i)

/-- At renewal every owner uses its pilot. This includes the saved-arm
owner among the actual unoccupied followers. -/
private theorem sourceArm_iff_pilotGate
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff record.input.time selected.view.complementWeights)
    (hmissing : selected.view.pendingAtChoice = Finset.univ)
    (hstates : ∀ i, (states i).status = .unoccupied) (j : Fin p.K) :
    ReferenceFirstWindowNumericalStream.sourceArm record selected.view.payload
        selected.view.pendingAtChoice states selected.view.complementWeights
        selected.view.cutoff hvalid = some j ↔
      pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p)
        (sourceOwner selected.view.payload.slowSet j) j
        (CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor j /
          pilotRecordingGateRawProbability (K := p.K)
            (sourceOwner selected.view.payload.slowSet j))
        (record.input.row.2 record.input.time).1 := by
  let payload := selected.view.payload
  let snap : ActiveRoundActions.Snapshot payload.assignment :=
    { missing := selected.view.pendingAtChoice, status := fun i => (states i).status }
  let w := ReferenceFirstWindowNumericalStream.sourceWeights payload selected.view.complementWeights
  have hpos := ReferenceFirstWindowNumericalStream.sourceWeights_pos payload
    selected.view.complementWeights selected.view.cutoff record.input.time hvalid
  have hlo := ReferenceFirstWindowNumericalStream.sourceWeights_lower payload
    selected.view.complementWeights selected.view.cutoff record.input.time hvalid
  have hhi := ReferenceFirstWindowNumericalStream.sourceWeights_upper payload
    selected.view.complementWeights selected.view.cutoff record.input.time hvalid
  let owner := sourceOwner payload.slowSet j
  have haction (x) : SnapshotRecordingKernel.dataAction p (.live payload.assignment snap)
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor w
      payload.anchor_pos hpos hlo hhi x owner = pilotDraw (K_pos p) owner x := by
    by_cases hc : owner = ActiveRoundActions.coordinator p.two_le_m
    · simp [SnapshotRecordingKernel.dataAction, snap, hc, hmissing,
        univ_missing_nonempty (p := p)]
    · have hu := hstates (ActiveRoundActions.followerIndex p.two_le_m owner hc)
      simp [SnapshotRecordingKernel.dataAction, snap, hc, hu]
  have hprob : SnapshotRecordingKernel.actionProbability p (.live payload.assignment snap)
      rate.eta.val rate.eta.property rate.sourceCap payload.anchor w
      payload.anchor_pos hpos hlo hhi owner j = 1 / (p.K : ℝ) := by
    by_cases hc : owner = ActiveRoundActions.coordinator p.two_le_m
    · simp [SnapshotRecordingKernel.actionProbability, snap, hc, hmissing,
        univ_missing_nonempty (p := p)]
    · have hu := hstates (ActiveRoundActions.followerIndex p.two_le_m owner hc)
      simp [SnapshotRecordingKernel.actionProbability, snap, hc, hu]
  exact Iff.of_eq (congrArg (fun s : Set (ContinuousControlSlice.Slice p.m p.K) =>
    (record.input.row.2 record.input.time).1 ∈ s)
      (SnapshotRecordingKernel.recordingMap_pilot_event_eq p (.live payload.assignment snap)
        rate.eta.val rate.eta.property rate.sourceCap payload.anchor w payload.anchor_pos
        hpos hlo hhi owner j (owns_sourceOwner rate payload snap j) haction hprob))

/-- The actual source-selected map has the installed renewal anchor and
current weights on every arm, and the actual all-missing, unoccupied snapshot.
The existential selection is the existing selected option; no call witness
is chosen to define a new source or registers. -/
theorem ae_wholeCell_renewal_readout :
    ∀ᵐ b : B ∂mu,
      ∃ selected : ReferenceActivePhysicalStep.Selection
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).input,
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t b.2).output.preparation.coordinator.selection = some selected ∧
        selected.view.payload.anchor =
          ReferenceFirstCollectionRenewalComplementMoments.v rate rewards C_star C_h u t b ∧
        ReferenceFirstWindowNumericalStream.sourceWeights selected.view.payload
          selected.view.complementWeights =
            ReferenceFirstCollectionRenewalComplementMoments.v rate rewards C_star C_h u t b ∧
        selected.view.pendingAtChoice = Finset.univ ∧
        selected.view.payload.slowSet =
          renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2 ∧
        AssignmentParameterFibreKernel.successfulSlowSet p
          (renewalCallParameter rate rewards C_star C_h u t b.1.1)
          (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val) =
            some (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2) ∧
        ∃ ho : ReferenceLaterLiveNumericalReadout.preparedOrdinary
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
              rate rewards C_star C_h u t b.2),
          (∀ i, (ReferenceLaterLiveNumericalReadout.preparedStates
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
              rate rewards C_star C_h u t b.2) ho i).status = .unoccupied) ∧
          cell b.2 = ReferenceFirstWindowNumericalStream.sourceCell
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
              rate rewards C_star C_h u t b.2) selected.view.payload
            selected.view.pendingAtChoice
            (ReferenceLaterLiveNumericalReadout.preparedStates
              (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
                rate rewards C_star C_h u t b.2) ho)
            selected.view.complementWeights selected.view.cutoff
            (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) := by
  classical
  filter_upwards [ReferenceFirstCollectionRenewalRecordingFeedback.ae_pairLaw_actual_recording_feedback
    rate rewards C_star C_h u t,
    ReferenceFirstCollectionRenewalInstallationCoupling.ae_pairLaw_chronological_support
      rate rewards C_star C_h u t] with b hb hc
  dsimp only at hb hc
  rcases hb with ⟨d, consistent, output, hlocal, clockData, installed, selection,
    recording, serviced, _hstart, hvector, hreconstruction, hsample, hslow,
    hpayloadSlow, _hclock, hinstalled, hanchor, _hdispatch, hprep, hcut,
    _hcoord, _hrun, _hservice, _hrecording, states, memories, hstates, _hlive,
    hpending, _hunone, _hsigma, _⟩
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, hparameter, _⟩
  have hw : (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 =
      AssignmentScoreReconstruction.currentWeight d.out :=
    (congrArg Prod.snd hparameter).trans
      ((congrArg Prod.snd d.parameter_eq).trans
        (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
          d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1)
  have hread := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_readout
    rate rewards C_star C_h u t b.2
  have hrecord := ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_call_record_eq
    rate rewards C_star C_h u t b.2 d
  rw [← hrecord] at hread
  obtain ⟨selected, ho, hs, _, _, heq⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some _ _ _ hread
  have hview : selected.view =
      { payload := installed.registers.payload, pendingAtChoice := d.started.pending,
        cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u,
        complementWeights := installed.registers.complementWeights } := by
    rw [hprep, hcut] at hs
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, d.instruction_time] at hs
    rw [← hs]
  have hmissing : selected.view.pendingAtChoice = Finset.univ := by
    rw [hview, hpending]
    rfl
  have hunoccupied (i) : (ReferenceLaterLiveNumericalReadout.preparedStates d.record ho i).status =
      .unoccupied := by
    simpa [ReferenceLaterLiveNumericalReadout.preparedStates,
      ReferenceLaterLiveNumericalReadout.ordinaryData, hprep, (hstates i).2.2]
      using (hstates i).2.1
  have hcomp (j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet) :
      installed.registers.complementWeights j =
        AssignmentScoreReconstruction.currentWeight d.out j.val := by
    subst installed
    change ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (AssignmentScoreReconstruction.sourceScore output.reconstruction j.val) = _
    rw [hreconstruction]
    rfl
  have hweight : ReferenceFirstWindowNumericalStream.sourceWeights selected.view.payload
      selected.view.complementWeights =
        ReferenceFirstCollectionRenewalComplementMoments.v rate rewards C_star C_h u t b := by
    rw [hview]
    funext j
    change ReferenceFirstWindowNumericalStream.sourceWeights installed.registers.payload
      installed.registers.complementWeights j = _
    unfold ReferenceFirstWindowNumericalStream.sourceWeights
    split
    · rw [hanchor, ← hw]
      rfl
    · rw [hcomp, ← hw]
      rfl
  have hslice : (d.record.input.row.2 d.record.input.time).1 =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 := by
    obtain ⟨_, _, _, hrows, hselected, _, _⟩ :=
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_physical
        rate rewards C_star C_h u t b.2
    rw [← hrecord] at hrows hselected
    change ((d.record.input.rows d.record.input.selected).2 d.record.input.time).1 = _
    rw [hrows, hselected, d.time_eq]
  have hvec : output.assignmentVector = ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val := by
    rw [← hvector, d.instruction_time]
    change ContinuousControlSlice.assignmentVector (d.record.input.row.2 d.record.input.time).1 = _
    rw [hslice]
    rfl
  have hsampleActual : AssignmentParameterFibreKernel.successfulSlowSet p
      (renewalCallParameter rate rewards C_star C_h u t b.1.1)
      (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val) =
        some (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2) := by
    rw [hparameter, d.parameter_eq, ← hvec, ← hslow]
    exact hsample
  rw [← hrecord]
  refine ⟨selected, hs, ?_, hweight, hmissing, ?_, hsampleActual, ho, hunoccupied, heq⟩
  · rw [hview, hanchor, ← hw]
    rfl
  · rw [hview, hpayloadSlow]

/-- The whole actual rate vector is the first source's canonical renewal
rate on the unchanged insertion-pair law. -/
theorem ae_wholeCell_rate :
    ∀ᵐ b : B ∂mu, (cell b.2).rate =
      fun j => ReferenceFirstCollectionRenewalComplementMoments.xi
        rate rewards C_star C_h u t b j := by
  filter_upwards [ae_wholeCell_renewal_readout rate rewards C_star C_h u t] with b hb
  rcases hb with ⟨selected, hactual, hanchor, _⟩
  obtain ⟨_, selected', hselected', _, hrate⟩ :=
    ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_numerical
      rate rewards C_star C_h u t b.2
  have heq : selected = selected' := Option.some.inj (hactual.symm.trans hselected')
  subst selected'
  rw [hrate]
  funext j
  change CanonicalRecordingRates.xi p rate.eta.val selected.view.payload.anchor j = _
  rw [hanchor]
  rfl

/-- The whole accepted arrival is the full marker times the literal REAL
quantized floor, before the incoming overflow stop. -/
theorem ae_fullAcceptedA_eq (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      fullAcceptedA rate rewards C_star C_h u t j b =
        if (incoming b.2).overflow then 0 else
          markerTest rate rewards C_star C_h u t j b *
            ReferenceFirstCollectionRenewalComplementMoments.q
              rate rewards C_star C_h u t b j := by
  filter_upwards [ae_wholeCell_rate rate rewards C_star C_h u t] with b hrate
  rw [fullAcceptedA_eq]
  split
  · rfl
  · have hr := (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_numerical
      rate rewards C_star C_h u t b.2).2
    obtain ⟨_, _, hreward, _⟩ := hr
    change (RecordedQueueRun.quantizedArrival qp (cell b.2) j : ℝ) / rate.n = _
    unfold RecordedQueueRun.quantizedArrival
    by_cases hm : (cell b.2).recordedArm = some j
    · simp only [hm, ite_true, markerTest, Set.indicator_of_mem
        (show b ∈ {b : B | (cell b.2).recordedArm = some j} from hm), one_mul]
      rw [hreward, hrate]
      unfold ReferenceFirstCollectionRenewalComplementMoments.q
        QuantizedRecordingMoments.quantizedValue QuantizedRecordingMoments.quantizedIndex
        ReferenceFirstCollectionRenewalComplementMoments.r
        RealRewardGridCount.realRewardGridValue
      dsimp only [ReferenceFirstLaunchNumericalCell.queueParameters]
      rw [rate.n_scale, mul_comm rate.eta.val (D p : ℝ)]
    · simp [hm, markerTest]

/-- The actual incoming flag has the same retained-field representative used
by the accepted prefix comparison. The current first crossing is included. -/
theorem ae_fullAcceptedA_eq_retained_indicator (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      fullAcceptedA rate rewards C_star C_h u t j b =
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
          rate rewards C_star C_h u t control0).indicator
          (fun b => markerTest rate rewards C_star C_h u t j b *
            ReferenceFirstCollectionRenewalComplementMoments.q
              rate rewards C_star C_h u t b j) b := by
  filter_upwards [ae_fullAcceptedA_eq rate rewards C_star C_h u t j,
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.ae_incomingReadout_eq_retained
      rate rewards C_star C_h u t control0] with b ha hb
  have ho := congrArg (fun x => x.2.1) hb
  change (incoming b.2).overflow =
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
      rate rewards C_star C_h u t control0 b).overflow at ho
  rw [ha]
  cases h : (incoming b.2).overflow <;>
    simp [ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R, ← ho, h]

/-- Every arm's full marker is its actual ordered owner's pilot gate. The
whole second-source slice is retained, rather than replaced by a fresh row. -/
theorem ae_wholeCell_marker_gate :
    ∀ᵐ b : B ∂mu, ∀ j : Fin p.K,
      (cell b.2).recordedArm = some j ↔
        pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p)
          (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2) j) j
          (ReferenceFirstCollectionRenewalComplementMoments.xi
              rate rewards C_star C_h u t b j /
            pilotRecordingGateRawProbability (K := p.K)
              (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2) j))
          (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 := by
  classical
  filter_upwards [ae_wholeCell_renewal_readout rate rewards C_star C_h u t] with b hb
  rcases hb with ⟨selected, _hactual, hanchor, _hweight, hmissing, hslow, _hsample, ho, hstatus, heq⟩
  let record := ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
    rate rewards C_star C_h u t b.2
  have hslice : (record.input.row.2 record.input.time).1 =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 := by
    obtain ⟨_, _, _, hrows, hselected, _, _⟩ :=
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_physical
        rate rewards C_star C_h u t b.2
    change ((record.input.rows record.input.selected).2 record.input.time).1 = _
    rw [hrows, hselected, ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord_time]
  intro j
  rw [heq]
  change ReferenceFirstWindowNumericalStream.sourceArm record selected.view.payload
    selected.view.pendingAtChoice (ReferenceLaterLiveNumericalReadout.preparedStates record ho)
    selected.view.complementWeights selected.view.cutoff
    (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected) = some j ↔ _
  rw [sourceArm_iff_pilotGate rate record selected _ _ hmissing hstatus j]
  rw [hslow, hanchor, hslice]
  rfl

local notation "H" => ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p
local notation "O" => ReferenceFirstCollectionRenewalControlFactor.Remainder p

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

private theorem measurable_xi_weight (j : Fin p.K) : Measurable
    (fun w : Fin p.K → ℝ => CanonicalRecordingRates.xi p rate.eta.val w j) := by
  have hprod (S : Finset (Fin p.K)) : Measurable
      (fun w : Fin p.K → ℝ => ProductSetLaw.setWeight w S) := by
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun w : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight w)) :=
    Finset.measurable_fun_sum _ (fun S _ => hprod S)
  have htheta : Measurable (fun w : Fin p.K → ℝ => ProductSetLaw.theta p.m w j) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    exact (hprod S).div htotal
  have hf : Measurable (fun w : Fin p.K → ℝ => CanonicalRecordingRates.f p w j) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  exact AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
    (measurable_const.max hf)

private theorem measurable_pilot_gate {α : Type*} [MeasurableSpace α]
    (j : Fin p.K) (owner : α → Fin p.m) (a : α → ℝ)
    (x : α → ContinuousControlSlice.Slice p.m p.K)
    (ho : Measurable owner) (ha : Measurable a) (hx : Measurable x) :
    MeasurableSet {z | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p)
      (owner z) j (a z) (x z)} := by
  have hslot := (measurable_slotDraw (m := p.m) (K := p.K)).comp hx
  have hrec := (measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp hx
  have hpilot (i : Fin p.m) := (measurable_pilotDraw (K_pos p) i).comp hx
  have hownPilot : Measurable (fun z => pilotDraw (K_pos p) (owner z) (x z)) :=
    (measurable_from_prod_countable_right (f := fun z : Fin p.m × α =>
      pilotDraw (K_pos p) z.1 (x z.2)) hpilot).comp (ho.prodMk measurable_id)
  have hmask : MeasurableSet {z | recordingMask (K_pos p) (owner z) j (x z)} := by
    simp only [recordingMask, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    convert (measurableSet_eq_fun measurable_const ho).union
      ((measurableSet_singleton j).preimage (hpilot i)).compl using 1
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  exact (hslot (measurableSet_singleton _)).inter
    ((measurableSet_eq_fun hrec ho).inter
      ((hownPilot (measurableSet_singleton j)).inter
        (hmask.inter (measurableSet_le
          (measurable_subtype_coe.comp ((measurable_coordinate Label.thin).comp hx)) ha))))

private theorem gate_eq_of_nonAssignment (i : Fin p.m) (j : Fin p.K) (a : ℝ)
    (x y : ContinuousControlSlice.Slice p.m p.K)
    (h : ∀ label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p,
      x label.val = y label.val) :
    pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j a x ↔
      pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j a y := by
  have hs : x Label.slot = y Label.slot := h ⟨Label.slot, by simp [Label.slot, Label.assign]⟩
  have hr : x Label.rec = y Label.rec := h ⟨Label.rec, by simp [Label.rec, Label.assign]⟩
  have ht : x Label.thin = y Label.thin := h ⟨Label.thin, by simp [Label.thin, Label.assign]⟩
  have hp (k : Fin p.m) : x (Label.pilot k) = y (Label.pilot k) :=
    h ⟨Label.pilot k, by simp [Label.pilot, Label.assign]⟩
  simp only [pilotRecordingGate, recordingMask, slotDraw, recorderSourceDraw,
    pilotDraw, coordinate, hs, hr, ht, hp]

private theorem split_symm_nonAssignment (v : CheckedAssignmentSample.AssignmentVector p)
    (o : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p)
    (label : LaunchAssignmentCoordinateSplit.NonAssignmentLabel p) :
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, o)) label.val =
      o label := by
  change ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p)
    ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, o))).2 label = _
  rw [(LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).apply_symm_apply]

/-- The recording projection of the scalar/affine remainder has its original
pilot-gate marginal. Both complete assignment vectors may be held fixed. -/
private theorem remainder_gate_mass (z : Z) (i : Fin p.m) (j : Fin p.K)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
      (ContinuousLearningRows.affineSamplesLaw p))
      {o : O | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j
        (CanonicalRecordingRates.xi p rate.eta.val
          (renewalCallParameter rate rewards C_star C_h u t z).2 j /
          pilotRecordingGateRawProbability (K := p.K) i)
        ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, o.1))} =
      ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t z).2 j) := by
  let a := CanonicalRecordingRates.xi p rate.eta.val
    (renewalCallParameter rate rewards C_star C_h u t z).2 j /
      pilotRecordingGateRawProbability (K := p.K) i
  let G : Set (LaunchAssignmentCoordinateSplit.NonAssignmentScalars p) :=
    {o | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j a
      ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, o))}
  have hG : MeasurableSet G :=
    (measurableSet_pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j a).preimage
      ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm.measurable.comp
        (measurable_const.prodMk measurable_id))
  have hpre : (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p) ⁻¹'
      (Set.univ ×ˢ G) =
      {x | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j a x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    apply gate_eq_of_nonAssignment
    intro label
    rw [split_symm_nonAssignment]
    rfl
  have hmass : (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p) G =
      ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t z).2 j) := by
    have hmap := (LaunchAssignmentCoordinateSplit.measurePreserving_sliceAssignmentSplitEquiv p).map_eq
    have heval := congrArg (fun ν => ν (Set.univ ×ˢ G)) hmap
    rw [Measure.map_apply (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).measurable
      (MeasurableSet.univ.prod hG), hpre, Measure.prod_prod] at heval
    simpa only [measure_univ, one_mul] using heval.symm.trans
      (canonical_pilotRecordingGate_mass p rate.eta.property rate.sourceCap _
        (renewal_parameter_spec rate rewards C_star C_h u t z).1 i j)
  have hevent : {o : O | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) i j a
      ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm (v, o.1))} =
      G ×ˢ Set.univ := by
    ext o
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    rfl
  change ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p))
    {o : O | pilotRecordingGate _ _ _ i j a _} = _
  rw [hevent, Measure.prod_prod, measure_univ, mul_one, hmass]

private def ownerGateEvent (j : Fin p.K) : Set B :=
  {b | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p)
    (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2) j) j
    (ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j /
      pilotRecordingGateRawProbability (K := p.K)
        (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2) j))
    (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1}

-- The subtype supplies only membership in the actual renewal source event.
-- No source or register value is manufactured outside that event.
private def validCoordinates : Set (H × O) :=
  {w | w.1.1.1.1 ∈ renewalCallEvent rate rewards C_star C_h u t}

private def coordinateSource (w : validCoordinates rate rewards C_star C_h u t) : Z :=
  ⟨w.val.1.1.1.1, w.property⟩

private def coordinateGate (j : Fin p.K) :
    Set (validCoordinates rate rewards C_star C_h u t) :=
  {w | let z := coordinateSource rate rewards C_star C_h u t w
       let owner := sourceOwner
         (renewalAuxiliarySample rate rewards C_star C_h u t z w.val.1.1.1.2) j
       pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p) owner j
         (CanonicalRecordingRates.xi p rate.eta.val
           (renewalCallParameter rate rewards C_star C_h u t z).2 j /
             pilotRecordingGateRawProbability (K := p.K) owner)
         ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
           (w.val.1.2, w.val.2.1))}

private def jointGate (j : Fin p.K) : Set (H × O) :=
  Subtype.val '' coordinateGate rate rewards C_star C_h u t j

private theorem measurableSet_validCoordinates :
    MeasurableSet (validCoordinates rate rewards C_star C_h u t) :=
  (measurableSet_renewalCallEvent rate rewards C_star C_h u t).preimage
    (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))

private theorem measurableSet_jointGate (j : Fin p.K) :
    MeasurableSet (jointGate rate rewards C_star C_h u t j) := by
  have hz : Measurable (coordinateSource rate rewards C_star C_h u t) := by
    apply Measurable.subtype_mk
    exact (measurable_fst.comp (measurable_fst.comp
      (measurable_fst.comp measurable_fst))).comp measurable_subtype_coe
  have ha : Measurable (fun w : validCoordinates rate rewards C_star C_h u t =>
      w.val.1.1.1.2) := by fun_prop
  have hU := (measurable_renewalAuxiliarySample rate rewards C_star C_h u t).comp (hz.prodMk ha)
  have ho := (Measurable.of_discrete : Measurable (fun U : SlowSet p => sourceOwner U j)).comp hU
  have hw := measurable_snd.comp
    ((measurable_renewalCallParameter rate rewards C_star C_h u t).comp hz)
  have hxi := (measurable_xi_weight rate j).comp hw
  have hraw := (Measurable.of_discrete :
    Measurable (pilotRecordingGateRawProbability (K := p.K) : Fin p.m → ℝ)).comp ho
  have hx : Measurable (fun w : validCoordinates rate rewards C_star C_h u t =>
      (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
        (w.val.1.2, w.val.2.1)) := by fun_prop
  exact (MeasurableEmbedding.subtype_coe
    (measurableSet_validCoordinates rate rewards C_star C_h u t)).measurableSet_image.mpr
      (measurable_pilot_gate j _ _ _ ho (hxi.div hraw) hx)

private theorem jointGate_mem_iff (j : Fin p.K) (w : H × O)
    (hw : w ∈ validCoordinates rate rewards C_star C_h u t) :
    w ∈ jointGate rate rewards C_star C_h u t j ↔
      (⟨w, hw⟩ : validCoordinates rate rewards C_star C_h u t) ∈
        coordinateGate rate rewards C_star C_h u t j := by
  constructor
  · rintro ⟨a, ha, heq⟩
    have he : a = ⟨w, hw⟩ := Subtype.ext heq
    exact he ▸ ha
  · intro h
    exact ⟨⟨w, hw⟩, h, rfl⟩

private theorem retained_valid (b : B) (o : O) :
    (R b, o) ∈ validCoordinates rate rewards C_star C_h u t :=
  (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
    rate rewards C_star C_h u t b.1.1 (fun _ => control0)).property

private theorem ownerGateEvent_eq_joint_preimage (j : Fin p.K) :
    ownerGateEvent rate rewards C_star C_h u t j =
      (fun b : B => (R b, ReferenceFirstCollectionRenewalControlFactor.insertedControlRemainder
        rate rewards C_star C_h u t b)) ⁻¹' jointGate rate rewards C_star C_h u t j := by
  ext b
  rw [Set.mem_preimage, jointGate_mem_iff rate rewards C_star C_h u t j _
    (retained_valid rate rewards C_star C_h u t control0 b _)]
  have hs : (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
      ((R b).2, (ReferenceFirstCollectionRenewalControlFactor.insertedControlRemainder
        rate rewards C_star C_h u t b).1) =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 := by
    change (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm
      ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p)
        (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1) = _
    exact (LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm_apply_apply _
  rcases erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2
    with ⟨hv, hU⟩
  change pilotRecordingGate _ _ _ _ _ _ _ ↔ pilotRecordingGate _ _ _ _ _ _ _
  dsimp only [coordinateSource]
  rw [hs]
  change pilotRecordingGate _ _ _ _ _ _ _ ↔
    pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p)
      (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
          rate rewards C_star C_h u t b.1.1 (fun _ => control0)) b.1.2) j) j
      (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
            rate rewards C_star C_h u t b.1.1 (fun _ => control0))).2 j /
        pilotRecordingGateRawProbability (K := p.K)
          (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t
            (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
              rate rewards C_star C_h u t b.1.1 (fun _ => control0)) b.1.2) j))
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1
  rw [← hU, ← hv]
  rfl

private theorem jointGate_section_mass (j : Fin p.K) (b : B) :
    ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
      (ContinuousLearningRows.affineSamplesLaw p))
      {o : O | (R b, o) ∈ jointGate rate rewards C_star C_h u t j} =
      ENNReal.ofReal (ReferenceFirstCollectionRenewalComplementMoments.xi
        rate rewards C_star C_h u t b j) := by
  have he : {o : O | (R b, o) ∈ jointGate rate rewards C_star C_h u t j} =
      {o : O | (⟨(R b, o), retained_valid rate rewards C_star C_h u t control0 b o⟩ :
        validCoordinates rate rewards C_star C_h u t) ∈
          coordinateGate rate rewards C_star C_h u t j} := by
    ext o
    exact jointGate_mem_iff rate rewards C_star C_h u t j _ _
  rw [he]
  rcases erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2
    with ⟨hv, hU⟩
  change ((LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p))
    {o : O | pilotRecordingGate p.two_le_m p.m_lt_K (K_pos p)
      (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
          rate rewards C_star C_h u t b.1.1 (fun _ => control0)) b.1.2) j) j
      (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
            rate rewards C_star C_h u t b.1.1 (fun _ => control0))).2 j /
        pilotRecordingGateRawProbability (K := p.K)
          (sourceOwner (renewalAuxiliarySample rate rewards C_star C_h u t
            (ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
              rate rewards C_star C_h u t b.1.1 (fun _ => control0)) b.1.2) j))
      ((LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p).symm ((R b).2, o.1))} = _
  rw [← hU, ← hv]
  exact remainder_gate_mass rate rewards C_star C_h u t b.1.1 _ j _

/-- The complete canonical rate is measurable on the same retained field;
there is no complement indicator in this assertion. -/
theorem measurable_xi_retained (j : Fin p.K) : Measurable[F_R]
    (fun b : B => ReferenceFirstCollectionRenewalComplementMoments.xi
      rate rewards C_star C_h u t b j) := by
  have hz := ReferenceFirstCollectionRenewalIncomingQueuePrefix.measurable_erasedSource_retained
    rate rewards C_star C_h u t control0
  have hw := measurable_snd.comp
    ((measurable_renewalCallParameter rate rewards C_star C_h u t).comp hz)
  convert (measurable_xi_weight rate j).comp hw using 1
  funext b
  change CanonicalRecordingRates.xi p rate.eta.val
    (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 j = _
  rw [(erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2).1]
  rfl

private theorem measurable_xi (j : Fin p.K) : Measurable
    (fun b : B => ReferenceFirstCollectionRenewalComplementMoments.xi
      rate rewards C_star C_h u t b j) :=
  (measurable_xi_weight rate j).comp (measurable_snd.comp
    ((measurable_renewalCallParameter rate rewards C_star C_h u t).comp
      (measurable_fst.comp measurable_fst)))

private theorem xi_bounds (j : Fin p.K) (b : B) :
    0 ≤ ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j ∧
      ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j ≤ 1 := by
  let w := (renewalCallParameter rate rewards C_star C_h u t b.1.1).2
  have hw := (renewal_parameter_spec rate rewards C_star C_h u t b.1.1).1
  have hn (k : Fin p.K) : 0 ≤ CanonicalRecordingRates.xi p rate.eta.val w k :=
    (CanonicalRecordingRates.xi_pos p rate.eta.property w k).le
  exact ⟨hn j, (Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ j)).trans
    (CanonicalRecordingRates.sum_xi_le_one p rate.eta.property rate.sourceCap w hw)⟩

private theorem integrable_xi (j : Fin p.K) : Integrable
    (fun b : B => ReferenceFirstCollectionRenewalComplementMoments.xi
      rate rewards C_star C_h u t b j) mu :=
  integrable_of_bounds rate rewards C_star C_h u t
    (measurable_xi rate rewards C_star C_h u t j) 1
    (xi_bounds rate rewards C_star C_h u t j)

/-- Every Borel retained-coordinate test sees the whole arm atom with its
canonical mass, on the original finite, possibly zero, pair measure. -/
theorem marker_cylinder (j : Fin p.K) (Hset : Set H) (hHset : MeasurableSet Hset) :
    mu {b : B | R b ∈ Hset ∧ (cell b.2).recordedArm = some j} =
      ∫⁻ b in {b : B | R b ∈ Hset}, ENNReal.ofReal
        (ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j) ∂mu := by
  let joint := fun b : B => (R b,
    ReferenceFirstCollectionRenewalControlFactor.insertedControlRemainder rate rewards C_star C_h u t b)
  let rho := (LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p).prod
    (ContinuousLearningRows.affineSamplesLaw p)
  let Dset : Set (H × O) := (Hset ×ˢ Set.univ) ∩ jointGate rate rewards C_star C_h u t j
  have hR : Measurable R := measurable_retainedControlCoordinates rate rewards C_star C_h u t control0
  have hjoint : Measurable joint := hR.prodMk
    (measurable_insertedControlRemainder rate rewards C_star C_h u t)
  have hD : MeasurableSet Dset := (hHset.prod MeasurableSet.univ).inter
    (measurableSet_jointGate rate rewards C_star C_h u t j)
  have hevent : {b : B | R b ∈ Hset ∧ b ∈ ownerGateEvent rate rewards C_star C_h u t j} =
      joint ⁻¹' Dset := by
    rw [ownerGateEvent_eq_joint_preimage rate rewards C_star C_h u t control0 j]
    ext b
    simp only [Dset, joint, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_ofPred_eq]
  have hsection : Measurable (fun h : H => rho (Prod.mk h ⁻¹' Dset)) :=
    measurable_measure_prodMk_left hD
  calc
    _ = mu {b : B | R b ∈ Hset ∧ b ∈ ownerGateEvent rate rewards C_star C_h u t j} := by
      apply measure_congr
      filter_upwards [ae_wholeCell_marker_gate rate rewards C_star C_h u t] with b hb
      exact propext (and_congr_right (fun _ => hb j))
    _ = ((mu).map joint) Dset := by
      rw [Measure.map_apply hjoint hD]
      exact congrArg mu hevent
    _ = (((mu).map R).prod rho) Dset := by
      rw [ReferenceFirstCollectionRenewalControlFactor.pairLaw_retained_nonAssignment_product
        rate rewards C_star C_h u t control0]
    _ = ∫⁻ h, rho (Prod.mk h ⁻¹' Dset) ∂((mu).map R) := Measure.prod_apply hD
    _ = ∫⁻ b, rho (Prod.mk (R b) ⁻¹' Dset) ∂mu := lintegral_map hsection hR
    _ = ∫⁻ b, {b : B | R b ∈ Hset}.indicator (fun b => ENNReal.ofReal
        (ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j)) b ∂mu := by
      apply lintegral_congr
      intro b
      by_cases hb : R b ∈ Hset
      · rw [Set.indicator_of_mem (show b ∈ {b : B | R b ∈ Hset} from hb)]
        have he : Prod.mk (R b) ⁻¹' Dset =
            {o : O | (R b, o) ∈ jointGate rate rewards C_star C_h u t j} := by
          ext o
          simp only [Dset, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
            hb, Set.mem_univ, true_and, Set.mem_ofPred_eq]
        rw [he]
        exact jointGate_section_mass rate rewards C_star C_h u t control0 j b
      · rw [Set.indicator_of_notMem (show b ∉ {b : B | R b ∈ Hset} from hb)]
        have he : Prod.mk (R b) ⁻¹' Dset = ∅ := by
          ext o
          simp only [Dset, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
            hb, false_and, Set.notMem_empty]
        rw [he, measure_empty]
    _ = _ := lintegral_indicator (hHset.preimage hR) _

theorem marker_setIntegral (j : Fin p.K) (Hset : Set H) (hHset : MeasurableSet Hset) :
    ∫ b in {b : B | R b ∈ Hset}, markerTest rate rewards C_star C_h u t j b ∂mu =
      ∫ b in {b : B | R b ∈ Hset},
        ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j ∂mu := by
  have hmarker : MeasurableSet {b : B | (cell b.2).recordedArm = some j} :=
    (measurable_marker rate rewards C_star C_h u t) (measurableSet_singleton _)
  change (∫ b in {b : B | R b ∈ Hset},
    {b : B | (cell b.2).recordedArm = some j}.indicator (fun _ => (1 : ℝ)) b ∂mu) = _
  rw [integral_indicator_const (1 : ℝ) hmarker, smul_eq_mul, mul_one,
    measureReal_restrict_apply hmarker]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun b => (xi_bounds rate rewards C_star C_h u t j b).1))
    ((measurable_xi rate rewards C_star C_h u t j).aestronglyMeasurable)]
  have he : {b : B | (cell b.2).recordedArm = some j} ∩ {b : B | R b ∈ Hset} =
      {b : B | R b ∈ Hset ∧ (cell b.2).recordedArm = some j} := by
    ext b
    exact and_comm
  rw [he]
  exact congrArg ENNReal.toReal
    (marker_cylinder rate rewards C_star C_h u t control0 j Hset hHset)

/-- The full marker law, without a complement indicator, on exactly the
existing pair measure and retained-coordinate field. -/
theorem condExp_markerTest (j : Fin p.K) :
    mu[markerTest rate rewards C_star C_h u t j | F_R] =ᵐ[mu]
      fun b => ReferenceFirstCollectionRenewalComplementMoments.xi
        rate rewards C_star C_h u t b j := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq
    (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
      rate rewards C_star C_h u t control0)
    (integrable_markerTest rate rewards C_star C_h u t j)
  · intro s _ _
    exact (integrable_xi rate rewards C_star C_h u t j).integrableOn
  · intro s hs _
    obtain ⟨Hset, hHset, he⟩ := MeasurableSpace.measurableSet_comap.mp hs
    rw [← he]
    exact (marker_setIntegral rate rewards C_star C_h u t control0 j Hset hHset).symm
  · exact (measurable_xi_retained rate rewards C_star C_h u t control0 j).aestronglyMeasurable

/-- Bottom has the residual whole-marker mass on the same field and law. -/
theorem condExp_noneTest :
    mu[noneTest rate rewards C_star C_h u t | F_R] =ᵐ[mu]
      fun b => 1 - ∑ j, ReferenceFirstCollectionRenewalComplementMoments.xi
        rate rewards C_star C_h u t b j := by
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have he : noneTest rate rewards C_star C_h u t =
      (fun _ : B => (1 : ℝ)) - ∑ j, markerTest rate rewards C_star C_h u t j := by
    funext b
    simpa only [Pi.sub_apply, Finset.sum_apply] using
      noneTest_eq_one_sub_sum rate rewards C_star C_h u t b
  have hsum : Integrable (∑ j, markerTest rate rewards C_star C_h u t j) mu :=
    integrable_finsetSum' _ (fun j _ => integrable_markerTest rate rewards C_star C_h u t j)
  have hs := condExp_finsetSum (μ := mu) (fun j (_ : j ∈ Finset.univ) =>
    integrable_markerTest rate rewards C_star C_h u t j) F_R
  rw [he]
  have hsub := condExp_sub (integrable_const (1 : ℝ)) hsum F_R
  rw [condExp_const hdom] at hsub
  filter_upwards [hsub, hs, Filter.eventually_all.mpr
    (fun j => condExp_markerTest rate rewards C_star C_h u t control0 j)] with b hb hs hmarkers
  simp only [Pi.sub_apply, Finset.sum_apply] at hb hs ⊢
  rw [hb, hs]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hmarkers j)

local notation "G" => ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
  rate rewards C_star C_h u t control0

/-- First whole accepted moment, with the literal incoming-overflow mask.
The first overflowing update is included because the flag is incoming. -/
theorem condExp_fullAcceptedA (j : Fin p.K) :
    mu[fullAcceptedA rate rewards C_star C_h u t j | F_R] =ᵐ[mu]
      fun b => (G).indicator (fun _ => (1 : ℝ)) b *
        ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j *
        ReferenceFirstCollectionRenewalComplementMoments.q rate rewards C_star C_h u t b j := by
  let f : B → ℝ := (G).indicator
    (fun b => ReferenceFirstCollectionRenewalComplementMoments.q rate rewards C_star C_h u t b j)
  let marker := markerTest rate rewards C_star C_h u t j
  have hf : Measurable[F_R] f :=
    (ReferenceFirstCollectionRenewalComplementMoments.measurable_q_retained
      rate rewards C_star C_h u t control0 j).indicator
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
        rate rewards C_star C_h u t control0)
  have he : fullAcceptedA rate rewards C_star C_h u t j =ᵐ[mu] f * marker := by
    filter_upwards [ae_fullAcceptedA_eq_retained_indicator
      rate rewards C_star C_h u t control0 j] with b hb
    rw [hb]
    by_cases hg : b ∈ G <;> simp [f, marker, hg, mul_comm]
  have hprod : Integrable (f * marker) mu :=
    (integrable_fullAcceptedA rate rewards C_star C_h u t j).congr he
  calc
    _ =ᵐ[mu] mu[f * marker | F_R] := condExp_congr_ae he
    _ =ᵐ[mu] f * mu[marker | F_R] := condExp_mul_of_stronglyMeasurable_left
      hf.stronglyMeasurable hprod (integrable_markerTest rate rewards C_star C_h u t j)
    _ =ᵐ[mu] _ := by
      filter_upwards [condExp_markerTest rate rewards C_star C_h u t control0 j] with b hb
      change f b * mu[marker | F_R] b = _
      rw [hb]
      by_cases hg : b ∈ G <;> simp [f, hg, mul_comm]

/-- Second whole accepted moment. The square retains the same single marker
and the square of the literal quantized REAL floor. -/
theorem condExp_fullAcceptedA_sq (j : Fin p.K) :
    mu[(fun b => (fullAcceptedA rate rewards C_star C_h u t j b) ^ 2) | F_R] =ᵐ[mu]
      fun b => (G).indicator (fun _ => (1 : ℝ)) b *
        ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j *
        (ReferenceFirstCollectionRenewalComplementMoments.q rate rewards C_star C_h u t b j) ^ 2 := by
  let f : B → ℝ := (G).indicator (fun b =>
    (ReferenceFirstCollectionRenewalComplementMoments.q rate rewards C_star C_h u t b j) ^ 2)
  let marker := markerTest rate rewards C_star C_h u t j
  have hf : Measurable[F_R] f :=
    ((ReferenceFirstCollectionRenewalComplementMoments.measurable_q_retained
      rate rewards C_star C_h u t control0 j).pow_const 2).indicator
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
        rate rewards C_star C_h u t control0)
  have he : (fun b => (fullAcceptedA rate rewards C_star C_h u t j b) ^ 2) =ᵐ[mu]
      f * marker := by
    filter_upwards [ae_fullAcceptedA_eq_retained_indicator
      rate rewards C_star C_h u t control0 j] with b hb
    rw [hb]
    by_cases hg : b ∈ G <;> by_cases hm : (cell b.2).recordedArm = some j <;>
      simp [f, marker, markerTest, hg, hm]
  have hprod : Integrable (f * marker) mu :=
    (integrable_fullAcceptedA_sq rate rewards C_star C_h u t j).congr he
  calc
    _ =ᵐ[mu] mu[f * marker | F_R] := condExp_congr_ae he
    _ =ᵐ[mu] f * mu[marker | F_R] := condExp_mul_of_stronglyMeasurable_left
      hf.stronglyMeasurable hprod (integrable_markerTest rate rewards C_star C_h u t j)
    _ =ᵐ[mu] _ := by
      filter_upwards [condExp_markerTest rate rewards C_star C_h u t control0 j] with b hb
      change f b * mu[marker | F_R] b = _
      rw [hb]
      by_cases hg : b ∈ G <;> simp [f, hg, mul_comm]

/-- Literal whole-marker source map, with the very same actual installed
ordered assignment, all-missing snapshot, renewed weights and second slice. -/
theorem ae_wholeCell_recordingMap :
    ∀ᵐ b : B ∂mu,
      let w := ReferenceFirstCollectionRenewalComplementMoments.v rate rewards C_star C_h u t b
      let hw := (renewal_parameter_spec rate rewards C_star C_h u t b.1.1).1
      ∃ selected : ReferenceActivePhysicalStep.Selection
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2).input,
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
          rate rewards C_star C_h u t b.2).output.preparation.coordinator.selection = some selected ∧
        let recorder := SnapshotRecordingKernel.recordingMap p
          (.live selected.view.payload.assignment
            { missing := Finset.univ, status := fun _ => .unoccupied })
          true rate.eta.val rate.eta.property rate.sourceCap w w hw hw
          (fun _ => le_rfl) (fun j => by
            have hj : 0 < w j := hw j
            linarith only [hj])
        (cell b.2).recordedArm = recorder
          (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 ∧
        (∀ j : Fin p.K, (ContinuousControlSlice.sliceLaw p.m p.K)
          {x | recorder x = some j} = ENNReal.ofReal
            (ReferenceFirstCollectionRenewalComplementMoments.xi rate rewards C_star C_h u t b j)) ∧
        (ContinuousControlSlice.sliceLaw p.m p.K) {x | recorder x = none} =
          ENNReal.ofReal (1 - ∑ j, ReferenceFirstCollectionRenewalComplementMoments.xi
            rate rewards C_star C_h u t b j) := by
  filter_upwards [ae_wholeCell_renewal_readout rate rewards C_star C_h u t] with b hb
  rcases hb with ⟨selected, hactual, hanchor, hweight, hmissing, _hslow, _hsample, ho, hstatus, heq⟩
  let record := ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
    rate rewards C_star C_h u t b.2
  have hslice : (record.input.row.2 record.input.time).1 =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 := by
    obtain ⟨_, _, _, hrows, hselected, _, _⟩ :=
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_physical
        rate rewards C_star C_h u t b.2
    change ((record.input.rows record.input.selected).2 record.input.time).1 = _
    rw [hrows, hselected, ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord_time]
  refine ⟨selected, hactual, ?_, ?_, ?_⟩
  · rw [heq]
    dsimp only [ReferenceFirstWindowNumericalStream.sourceCell,
      ReferenceFirstWindowNumericalStream.sourceArm]
    have hstatusfun : (fun i : ActiveRoundActions.Follower p.m =>
        (ReferenceLaterLiveNumericalReadout.preparedStates
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
            rate rewards C_star C_h u t b.2) ho i).status) = fun _ =>
              ActiveRoundActions.FollowerStatus.unoccupied := by
      funext i
      exact hstatus i
    dsimp only [record] at hslice
    simp only [hmissing, hstatusfun, hanchor, hweight, hslice]
  · intro j
    exact SnapshotRecordingKernel.recordingMap_atom_mass p _ rate.eta.val rate.eta.property
      rate.sourceCap _ _ _ _ _ _ j
  · exact SnapshotRecordingKernel.recordingMap_none_mass p _ rate.eta.val rate.eta.property
      rate.sourceCap _ _ _ _ _ _

local instance checkedResultMeasurableSpace : MeasurableSpace (CheckedAssignmentSample.Result p) := ⊤

/-- The entire checked assignment output, including orientation and both
failure tags, factors through the retained coordinates without totalizing
registers or selecting a call witness on arbitrary retained tuples. -/
theorem measurable_checkedAssignment_retained : Measurable[F_R]
    (fun b : B => CheckedAssignmentSample.checkedAssignmentSample p
      (renewalCallParameter rate rewards C_star C_h u t b.1.1).1
      (renewalCallParameter rate rewards C_star C_h u t b.1.1).2
      (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val)) := by
  have hp : Measurable[F_R]
      (fun b : B => renewalCallParameter rate rewards C_star C_h u t b.1.1) := by
    convert (measurable_renewalCallParameter rate rewards C_star C_h u t).comp
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.measurable_erasedSource_retained
        rate rewards C_star C_h u t control0) using 1
    funext b
    exact (erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2).1
  have hv : Measurable[F_R]
      (fun b : B => ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val) :=
    measurable_snd.comp (comap_measurable R)
  exact (CheckedAssignmentJointMeasurability.measurable_checkedAssignmentSample_joint p).comp
    (hp.prodMk hv)

/-- At the produced positive renewal parameter the checked full-vector
sampler is exactly its lawful canonical sampler, pointwise on the source. -/
theorem checkedAssignment_eq_canonical (b : B) :
    let w := (renewalCallParameter rate rewards C_star C_h u t b.1.1).2
    let hw := (renewal_parameter_spec rate rewards C_star C_h u t b.1.1).1
    CheckedAssignmentSample.checkedAssignmentSample p
      (renewalCallParameter rate rewards C_star C_h u t b.1.1).1 w
      (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val) =
      .sampled (CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K w w hw hw
        (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val)) := by
  dsimp only
  let w := (renewalCallParameter rate rewards C_star C_h u t b.1.1).2
  have hw := (renewal_parameter_spec rate rewards C_star C_h u t b.1.1).1
  have hmass : (renewalCallParameter rate rewards C_star C_h u t b.1.1).1 =
      (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight :=
    (renewal_parameter_spec rate rewards C_star C_h u t b.1.1).2
  calc
    _ = CheckedAssignmentSample.checkedAssignmentSample p
        (CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K w hw).weight w
        (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val) :=
      congrArg (fun mass => CheckedAssignmentSample.checkedAssignmentSample p mass w
        (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val)) hmass
    _ = _ := CheckedAssignmentSample.productQ_checkedAssignmentSample_eq_sampler p w w hw hw _

/-- Accepted records use the strict past-overflow test on the actual
appended prefix, retaining the update at its first crossing. -/
theorem acceptedRecord_firstOverflow (z : Z) (j : Fin p.K) :
    (RecordedQueueRun.acceptedRecord qp (incoming z) (cell z) j).1 =
      decide (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
        rate rewards C_star C_h u t z <
          UnstoppedRecordedQueueComparison.firstOverflowPrefix qp
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
              rate rewards C_star C_h u t z ++ [cell z])) := by
  have hc := ReferenceFirstCollectionRenewalSourceCurrentPrefix.incoming_noOverflow_iff_wholeCell_firstOverflow
    rate rewards C_star C_h u t z
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_acceptedRecord]
  cases ho : (incoming z).overflow
  · simp [hc.mp ho]
  · have hnot : ¬ ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
        rate rewards C_star C_h u t z <
          UnstoppedRecordedQueueComparison.firstOverflowPrefix qp
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
              rate rewards C_star C_h u t z ++ [cell z]) := by
      intro h
      have hf := hc.mpr h
      simp [ho] at hf
    simp [hnot]

/-- An enabled zero arrival still serves the existing backlog, even when a
recorded reward quantizes to zero. Earlier overflow preserves the registers. -/
theorem wholeCell_zero_arrival_service (z : Z) (j : Fin p.K) :
    RecordedQueueRun.quantizedArrival qp (cell z) j = 0 →
      (RecordedQueueRun.step qp (incoming z) (cell z)).registers j =
        if (incoming z).overflow then (incoming z).registers j else
          (((incoming z).registers j).1 + min (4 * rate.n) ((incoming z).registers j).2,
            ((incoming z).registers j).2 - min (4 * rate.n) ((incoming z).registers j).2) := by
  intro hzero
  change QueueReplay.transition (4 * rate.n) ((incoming z).registers j)
    (RecordedQueueRun.acceptedRecord qp (incoming z) (cell z) j) = _
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_acceptedRecord,
    hzero]
  cases (incoming z).overflow
  · simp only [Bool.false_eq_true, ite_false]
    exact QueueReplay.transition_enabled_zero_arrival _ _ _
  · simp only [ite_true]
    rfl

end Bandits.Support.ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw

end
