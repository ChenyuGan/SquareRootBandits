/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveBirthChronologicalReadout

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Tactic

/-!
# Actual first-live birth joint source law

The first chronological birth retains the original source remainder, the whole
assignment vector and auxiliary array, and the same-slice recorder/FAST pair.
The current proposal bit is factored only after forming the actual zero-state
all-arm update. These are scoped source laws, not a finite prefix induction or
a manuscript closure claim.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceFirstLiveBirthChronologicalReadout
open Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation
open Bandits.Support.ReferenceFirstLaunchCommonUpdateSource
open Bandits.Support.ReferenceFirstLaunchRecordingPhysicalMarker
open Bandits.Support.ReferenceFirstLaunchRecordingSourceLaw
open Bandits.Support.ReferenceFirstLaunchOriginalAuxiliaryReward
open Bandits.Support.ReferenceFirstLivePostUpdateProposalLaw
open Bandits.Support.ReferenceRankInstallationRecorderFastLaw

namespace Bandits.Support.ReferenceFirstLiveBirthJointSourceLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p))
  (t : Fin p.T) (control0 : ContinuousLearningRows.TimeControl p)

abbrev BirthSource (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :=
  ReferenceFirstLiveBirthChronologicalReadout.SourceStratum rate rewards C_star C_h q t
abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  ReferenceFirstLaunchRecordingPhysicalMarker.AssignmentVector p
abbrev BirthPair (p : ConstructorDimensions.Parameters) := Option (Fin p.K) × Fin p.K
abbrev AuxiliaryArray (p : ConstructorDimensions.Parameters) :=
  ReferenceFirstLiveChronologicalPrefixFoundation.AuxiliaryArray p

local notation "coords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h q t control0

/-- The unit-anchor birth view used by the actual first-launch recorder and
reserved FAST coordinate. -/
def birthView (v : AssignmentVector p) :=
  ReferenceFirstLiveBirthChronologicalReadout.unitBirthView rate t v

theorem birthView_valid (v : AssignmentVector p) :
    CoordinatorLocalArmChoice.ChoiceInputsValid (birthView rate t v).payload
      (birthView rate t v).cutoff t (birthView rate t v).complementWeights :=
  ReferenceFirstLiveBirthChronologicalReadout.unitBirthView_valid rate t v

/-- The joint recorder/FAST kernel on one original scalar slice. Its two
coordinates share the slice and are not asserted independent. -/
def birthPairOnSlice (v : AssignmentVector p)
    (slice : ContinuousControlSlice.Slice p.m p.K) : BirthPair p :=
  ReferenceFirstLiveBirthChronologicalReadout.unitBirthPair rate t v
    (birthView_valid rate t v) slice

/-- The fixed-view same-slice law, also expressed as the pushforward of all
original nonassignment scalar and affine coordinates. -/
def birthPairKernel (v : AssignmentVector p) : Measure (BirthPair p) :=
  (ContinuousControlSlice.sliceLaw p.m p.K).map (birthPairOnSlice rate t v)

private theorem measurable_birthPairOnSlice (v : AssignmentVector p) :
    Measurable (birthPairOnSlice rate t v) := by
  unfold birthPairOnSlice
  unfold ReferenceFirstLiveBirthChronologicalReadout.unitBirthPair
  unfold ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair
  have hrec : Measurable
      (ReferenceRankInstallationRecorderFoundation.installationRecordingMap
        rate t (birthView rate t v) (birthView_valid rate t v)) := by
    unfold ReferenceRankInstallationRecorderFoundation.installationRecordingMap
    exact SnapshotRecordingKernel.measurable_recordingMap p
      (.live (birthView rate t v).payload.assignment
        (ReferenceRankInstallationRecorderFoundation.installationSnapshot
          (birthView rate t v).payload.assignment))
      rate.eta.val rate.eta.property rate.sourceCap (birthView rate t v).payload.anchor
      (ReferenceFirstWindowNumericalStream.sourceWeights (birthView rate t v).payload
        (birthView rate t v).complementWeights)
      (birthView rate t v).payload.anchor_pos
      (ReferenceFirstWindowNumericalStream.sourceWeights_pos (birthView rate t v).payload
        (birthView rate t v).complementWeights (birthView rate t v).cutoff t
        (birthView_valid rate t v))
      (ReferenceFirstWindowNumericalStream.sourceWeights_lower (birthView rate t v).payload
        (birthView rate t v).complementWeights (birthView rate t v).cutoff t
        (birthView_valid rate t v))
      (ReferenceFirstWindowNumericalStream.sourceWeights_upper (birthView rate t v).payload
        (birthView rate t v).complementWeights (birthView rate t v).cutoff t
        (birthView_valid rate t v)) true
  exact hrec.prodMk
    (measurable_subtype_coe.comp
      (ReferenceRankInstallationRecorderFastLaw.measurable_reservedFastAtView
        rate t (birthView rate t v) (birthView_valid rate t v)))

/-- The existing fixed-view nonassignment pushforward applies at the actual
birth view and gives exactly the same correlated kernel. -/
theorem birthPairKernel_eq_nonassignment (v : AssignmentVector p) :
    (ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p).map
      (fun d => birthPairOnSlice rate t v
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl v d).1) =
      birthPairKernel rate t v := by
  let scalarSplit := LaunchAssignmentCoordinateSplit.sliceAssignmentSplitEquiv p
  let scalars := LaunchAssignmentCoordinateSplit.nonAssignmentScalarLaw p
  let affine := ContinuousLearningRows.affineSamplesLaw p
  let slicePair := birthPairOnSlice rate t v
  have hfst : (scalars.prod affine).map (fun d :
      ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p => slicePair
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl v d).1) =
      birthPairKernel rate t v := by
    have hg : Measurable (fun d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
        slicePair (scalarSplit.symm (v, d))) :=
      (measurable_birthPairOnSlice rate t v).comp
        (scalarSplit.symm.measurable.comp (measurable_const.prodMk measurable_id))
    change (scalars.prod affine).map
        ((fun d : LaunchAssignmentCoordinateSplit.NonAssignmentScalars p =>
          slicePair (scalarSplit.symm (v, d))) ∘ Prod.fst) = _
    rw [← Measure.map_map hg measurable_fst]
    rw [(measurePreserving_fst (μ := scalars) (ν := affine)).map_eq]
    exact ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair_nonassignment_pushforward
      rate t (birthView rate t v) (birthView_valid rate t v) v
  change (scalars.prod affine).map (fun d :
    ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p => slicePair
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl v d).1) = _
  exact hfst

/-- The literal enabled, unit-anchor numerical birth round determined by the
whole assignment vector and the recorder coordinate of the same-slice pair.
The FAST coordinate remains in the pair but does not change all-arm arrivals. -/
def birthRound (pair : BirthPair p) :
    RecordedQueueRun.RoundInput p.K where
  enabled := true
  recordedArm := pair.1
  reward := fun j => ((rewards t j).val : ℝ) / (D p : ℝ)
  rate := fun j => CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  reward_nonneg := by
    intro j
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  reward_le_one := by
    intro j
    have hj := Nat.le_of_lt_succ (rewards t j).isLt
    apply (div_le_one (Nat.cast_pos.mpr (D_pos p))).2
    exact_mod_cast hj
  rate_pos := by
    intro j
    exact CanonicalRecordingRates.xi_pos p rate.eta.property (fun _ => 1) j

/-- The actual zero-state queue update determined by the birth recorder/FAST
pair and the original reward row. -/
def birthUpdate (_v : AssignmentVector p) (pair : BirthPair p) :
    RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (RecordedQueueRun.initialState p.K) (birthRound rate rewards t pair)

/-- The actual first update agrees with the literal deterministic update from
the actual same-slice pair, including every arm and the first overflow update. -/
theorem actual_birth_update_eq (z : BirthSource p rate rewards C_star C_h q t) :
    ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z =
      birthUpdate rate rewards t (coords z).2.1
        (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z,
          (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
            rate rewards C_star C_h q t control0 z).val) := by
  classical
  let c := coords z
  let pair := (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z,
    (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
      rate rewards C_star C_h q t control0 z).val)
  have hread := ReferenceFirstLaunchRecordingPhysicalMarker.numerical_cell_readout
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have hstep := ReferenceFirstLaunchCommonUpdateSource.source_first_update
    rate rewards C_star C_h q t control0 z
  have harrival (j : Fin p.K) :
      ReferenceFirstLaunchCommonUpdateSource.firstArrival rate rewards C_star C_h q t control0 z j =
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (birthRound rate rewards t pair) j := by
    change RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstLaunchRecordingPhysicalMarker.numericalCell rate rewards C_star C_h q t control0
          c.1 c.2.1 c.2.2) j = _
    have hmarker :
        ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 = pair.1 := by
      rfl
    rw [hread.2.2 j, hmarker]
    simp [pair, birthRound, ReferenceFirstLaunchNumericalCell.queueParameters,
      RecordedQueueRun.quantizedArrival]
    rfl
  have hregs :
        (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z).registers =
        (birthUpdate rate rewards t c.2.1 pair).registers := by
      funext j
      rw [(hstep.1 j).2.1]
      rw [harrival j]
      simp [birthUpdate, birthRound, RecordedQueueRun.step,
        RecordedQueueRun.initialState, RecordedQueueRun.acceptedRecord,
        QueueReplay.transition, ReferenceFirstLaunchNumericalCell.queueParameters]

  have hoverflow :
        (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z).overflow =
      (birthUpdate rate rewards t c.2.1 pair).overflow := by
    have hthreshold :
        (∃ j : Fin p.K, 32 *
          ((ReferenceFirstLaunchCommonUpdateSource.firstUpdate
            rate rewards C_star C_h q t control0 z).registers j).2 > D p) ↔
        (∃ j : Fin p.K, 32 *
          ((birthUpdate rate rewards t c.2.1 pair).registers j).2 > D p) := by
      rw [hregs]
    have hbirth : (birthUpdate rate rewards t c.2.1 pair).overflow = true ↔
        ∃ j : Fin p.K, 32 * ((birthUpdate rate rewards t c.2.1 pair).registers j).2 > D p := by
      simp [birthUpdate, RecordedQueueRun.step, RecordedQueueRun.initialState,
        ReferenceFirstLaunchNumericalCell.queueParameters]
    have hbool := hstep.2.1.trans (hthreshold.trans hbirth.symm)
    cases ha : (ReferenceFirstLaunchCommonUpdateSource.firstUpdate
        rate rewards C_star C_h q t control0 z).overflow <;>
      cases hb : (birthUpdate rate rewards t c.2.1 pair).overflow <;>
      simp_all
  have hrecords :
        (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z).records =
        (birthUpdate rate rewards t c.2.1 pair).records := by
    funext j
    rw [(hstep.1 j).1]
    simp [birthUpdate, birthRound, RecordedQueueRun.step,
      RecordedQueueRun.initialState, RecordedQueueRun.acceptedRecord,
      QueueReplay.transition, harrival]
  cases hleft : ReferenceFirstLaunchCommonUpdateSource.firstUpdate
      rate rewards C_star C_h q t control0 z with
  | mk lregs loverflow lrecords =>
    cases hright : birthUpdate rate rewards t c.2.1 pair with
    | mk rregs roverflow rrecords =>
      have hregs' : lregs = rregs := by simpa [hleft, hright] using hregs
      have hoverflow' : loverflow = roverflow := by simpa [hleft, hright] using hoverflow
      have hrecords' : lrecords = rrecords := by simpa [hleft, hright] using hrecords
      cases hregs'
      cases hoverflow'
      cases hrecords'
      rfl

/-- The first chronological entry's stored proposal is the original physical
proposal bit of the same current control. -/
theorem actual_birth_proposal_eq_physical
    (z : BirthSource p rate rewards C_star C_h q t)
    (aux : AuxiliaryArray p) :
    let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
    let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
      rate rewards C_star C_h (z.val, aux))[0]'(by
        rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
        exact hpositive)
    entry.proposal = physicalProposalBit rate
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
        (coords z).2.1 (coords z).2.2) := by
  let c := coords z
  let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
  let record := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h z.val)[0]'hpositive
  let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
    rate rewards C_star C_h (z.val, aux))[0]'(by
      rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
      exact hpositive)
  rcases ReferenceFirstLiveBirthChronologicalReadout.actual_birth_chronological_entry_readout
      rate rewards C_star C_h q t control0 z aux with
    ⟨_, _, _, _, _, _, _, _, _, hproposal, _⟩
  obtain ⟨tail, hwindow⟩ := actual_birth_whole_window_first rate rewards C_star C_h q t z
  have hrecord : record = ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 := by
    calc
      record = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord rate z.val rewards
          C_star C_h z.property.2.1 (by
            rw [ReferenceFirstLaunchCommonUpdateSource.source_elapsed_eq rate rewards C_star C_h q t z]
            exact t.isLt) := by
        simp only [record, hwindow, List.getElem_cons_zero]
      _ = ReferenceFirstLaunchRecordingPhysicalMarker.record
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2 :=
        (ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
          rate rewards C_star C_h q t control0 z).symm
  have hcurrent := ReferenceFirstLaunchRecordingPhysicalMarker.record_slice
    rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2
  have hprop :
      (CompletePublicTable.completeRowLearning p record.input.row record.input.time).1
        (ReferenceFirstLivePostUpdateProposalLaw.propLabel p) =
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1
        (ReferenceFirstLivePostUpdateProposalLaw.propLabel p) := by
    change (record.input.row.2 record.input.time).1
        (ReferenceFirstLivePostUpdateProposalLaw.propLabel p) = _
    rw [hrecord]
    exact congrArg (fun s : ContinuousControlSlice.Slice p.m p.K =>
      s (ReferenceFirstLivePostUpdateProposalLaw.propLabel p)) hcurrent
  have hbit := ReferenceFirstLivePostUpdateProposalLaw.completeRowProposalBit_eq_physicalProposalBit
    rate record.input.row record.input.time
    (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2) hprop
  change entry.proposal = FollowerCutoffScan.completeRowProposalBit p rate.eta
    record.input.row record.input.time at hproposal
  change entry.proposal = _
  rw [hrecord] at hproposal
  calc
    entry.proposal = FollowerCutoffScan.completeRowProposalBit p rate.eta
        (ReferenceFirstLaunchRecordingPhysicalMarker.record
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).input.row
        (ReferenceFirstLaunchRecordingPhysicalMarker.record
          rate rewards C_star C_h q t control0 c.1 c.2.1 c.2.2).input.time := hproposal
    _ = physicalProposalBit rate
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2) := by
      simpa [hrecord, c] using hbit
    _ = physicalProposalBit rate
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
          (coords z).2.1 (coords z).2.2) := rfl

/-- The literal actual birth observation, retaining the original source
remainder, whole assignment vector, independent auxiliary array, correlated
same-slice recorder/FAST pair, zero-state all-arm update, and proposal. -/
def actualBirthTuple (z : BirthSource p rate rewards C_star C_h q t)
    (aux : AuxiliaryArray p) :
    ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart rate rewards C_star C_h q t control0 ×
    (AssignmentVector p × (AuxiliaryArray p ×
        (BirthPair p × (RecordedQueueRun.RunState p.K × Bool)))) := by
  let c := coords z
  let hpositive := actual_birth_chronological_prefix_positive rate rewards C_star C_h q t z
  let entry := (ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix
    rate rewards C_star C_h (z.val, aux))[0]'(by
      rw [ReferenceFirstLiveChronologicalPrefixFoundation.firstLiveChronologicalPrefix_length]
      exact hpositive)
  exact (c.1, (c.2.1, (aux,
    ((ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h q t control0 z,
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val),
      (ReferenceFirstLaunchCommonUpdateSource.firstUpdate rate rewards C_star C_h q t control0 z,
        entry.proposal)))))

/-- On the birth stratum, the exposed tuple is exactly the fixed-view map of
the retained source coordinates, auxiliary array, same-slice pair, update,
and original physical proposal bit. -/
theorem actual_birth_tuple_eq_coordinates
    (z : BirthSource p rate rewards C_star C_h q t) (aux : AuxiliaryArray p) :
    actualBirthTuple rate rewards C_star C_h q t control0 z aux =
      let c := coords z
      let pair := birthPairOnSlice rate t c.2.1
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1
      (c.1, (c.2.1, (aux, (pair,
        (birthUpdate rate rewards t c.2.1 pair,
          ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate
            (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2)))))) := by
  let c := coords z
  let actualPair : BirthPair p :=
    (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
      rate rewards C_star C_h q t control0 z,
      (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
        rate rewards C_star C_h q t control0 z).val)
  let pair := birthPairOnSlice rate t c.2.1
    (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2).1
  have hpair : actualPair = pair := by
    simpa [actualPair, pair, birthPairOnSlice] using
      (ReferenceFirstLiveBirthChronologicalReadout.actual_birth_pair_eq_unitBirthPair
        rate rewards C_star C_h q t control0 z)
  have hpairConcrete :
      (ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
        rate rewards C_star C_h q t control0 z,
        (ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstFastArm
          rate rewards C_star C_h q t control0 z).val) = pair := by
    simpa [actualPair] using hpair
  have hupdate := actual_birth_update_eq rate rewards C_star C_h q t control0 z
  have hproposal := actual_birth_proposal_eq_physical rate rewards C_star C_h q t control0 z aux
  dsimp [actualBirthTuple]
  rw [hupdate]
  rw [hpairConcrete]
  rw [hproposal]

local notation "X" => ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
  rate rewards C_star C_h q t control0
local notation "μZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "μC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "νA" => ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p
local notation "split" => LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p

/-- Erasing the proposal scalar leaves the same-slice birth pair unchanged. -/
theorem birthPairOnSlice_replaceProposal (v : AssignmentVector p)
    (u : ContinuousLearningRows.TimeControl p) (a : ContinuousControlSlice.Scalar) :
    birthPairOnSlice rate t v (replaceProposalScalar p u a).1 =
      birthPairOnSlice rate t v u.1 := by
  let view := birthView rate t v
  let valid := birthView_valid rate t v
  have h := liveRecordingFastPair_replaceProposal rate view.payload.anchor
    (ReferenceFirstWindowNumericalStream.sourceWeights view.payload view.complementWeights)
    view.payload.anchor_pos
    (ReferenceFirstWindowNumericalStream.sourceWeights_pos view.payload
      view.complementWeights view.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_lower view.payload
      view.complementWeights view.cutoff t valid)
    (ReferenceFirstWindowNumericalStream.sourceWeights_upper view.payload
      view.complementWeights view.cutoff t valid)
    view.payload.assignment
    (ReferenceRankInstallationRecorderFoundation.installationSnapshot view.payload.assignment) u a
  apply Prod.ext
  · simpa only [view, birthView, birthPairOnSlice,
      ReferenceFirstLiveBirthChronologicalReadout.unitBirthPair,
      ReferenceRankInstallationRecorderFastLaw.installationRecorderFastPair,
      ReferenceRankInstallationRecorderFoundation.installationRecordingMap,
      FastRewardSliceLaw.liveRecordingFastPair] using congrArg Prod.fst h
  · have hfast := replaceProposalScalar_other p u a
      ContinuousControlSlice.Label.fast (by
        simp [propLabel, ContinuousControlSlice.Label.fast, ContinuousControlSlice.Label.prop])
    change (ReferenceRankInstallationRecorderFastLaw.reservedFastAtView
      rate t view valid (replaceProposalScalar p u a).1).val =
      (ReferenceRankInstallationRecorderFastLaw.reservedFastAtView rate t view valid u.1).val
    simp only [ReferenceRankInstallationRecorderFastLaw.reservedFastAtView,
      ContinuousControlSlice.coordinate, hfast]

private theorem assignment_replaceProposal (u : ContinuousLearningRows.TimeControl p)
    (a : ContinuousControlSlice.Scalar) :
    (split (replaceProposalScalar p u a)).1 = (split u).1 := by
  funext r
  change (replaceProposalScalar p u a).1 (ContinuousControlSlice.Label.assign r) =
    u.1 (ContinuousControlSlice.Label.assign r)
  exact replaceProposalScalar_other p u a _ (by
    simp [propLabel, ContinuousControlSlice.Label.assign, ContinuousControlSlice.Label.prop])

/-- Pre-proposal observation of the same original source reconstructed from
its retained remainder and current control. -/
def birthObservation (y : X × ContinuousLearningRows.TimeControl p) : X × (AssignmentVector p × BirthPair p) :=
  (y.1, ((split y.2).1, birthPairOnSlice rate t (split y.2).1 y.2.1))

private theorem coordinates_restore (y : X × ContinuousLearningRows.TimeControl p) :
    coords (restoreSource rate rewards C_star C_h q t control0 y) =
      (y.1, split y.2) := by
  have h := sourceControlCoordinates_restoreSource rate rewards C_star C_h q t control0 y
  change ((sourceControlCoordinates rate rewards C_star C_h q t control0
      (restoreSource rate rewards C_star C_h q t control0 y)).1,
    split (sourceControlCoordinates rate rewards C_star C_h q t control0
      (restoreSource rate rewards C_star C_h q t control0 y)).2) = _
  rw [h]

private theorem birthObservation_pair_eq_actual (y : X × ContinuousLearningRows.TimeControl p) :
    (birthObservation rate rewards C_star C_h q t control0 y).2.2 =
      (sourceMarker rate rewards C_star C_h q t control0
        (restoreSource rate rewards C_star C_h q t control0 y),
      (actualFirstFastArm rate rewards C_star C_h q t control0
        (restoreSource rate rewards C_star C_h q t control0 y)).val) := by
  rw [actual_birth_pair_eq_unitBirthPair rate rewards C_star C_h q t control0]
  rw [coordinates_restore]
  change birthPairOnSlice rate t (split y.2).1 y.2.1 =
    birthPairOnSlice rate t (split y.2).1 ((split).symm (split y.2)).1
  rw [(split).symm_apply_apply]

/-- Borel dependence on the actual retained source and the whole current
control, using the existing original-source Borel readouts. -/
theorem measurable_birthObservation :
    Measurable (birthObservation rate rewards C_star C_h q t control0) := by
  have hr := measurable_restoreSource rate rewards C_star C_h q t control0
  have hp := ((measurable_sourceMarker rate rewards C_star C_h q t control0).comp hr).prodMk
    ((measurable_actualFirstFastArmValue rate rewards C_star C_h q t control0).comp hr)
  have hp' : Measurable (fun y : X × ContinuousLearningRows.TimeControl p =>
      (birthObservation rate rewards C_star C_h q t control0 y).2.2) := by
    convert hp using 1
    funext y
    exact birthObservation_pair_eq_actual rate rewards C_star C_h q t control0 y
  exact measurable_fst.prodMk
    ((measurable_fst.comp ((split).measurable.comp measurable_snd)).prodMk hp')

/-- Proposal replacement preserves the whole retained observation. -/
theorem birthObservation_replaceProposal (x : X) (u : ContinuousLearningRows.TimeControl p)
    (a : ContinuousControlSlice.Scalar) :
    birthObservation rate rewards C_star C_h q t control0 (x, replaceProposalScalar p u a) =
      birthObservation rate rewards C_star C_h q t control0 (x, u) := by
  unfold birthObservation
  rw [assignment_replaceProposal, birthPairOnSlice_replaceProposal]

/-- Factor only the original proposal bit, retaining the actual pair and all
assignment coordinates. The source measure is finite and unnormalized. -/
theorem birthObservation_proposal_joint_map :
    ((μC).prod (timeControlLaw p)).map (fun y : X × ContinuousLearningRows.TimeControl p =>
      (birthObservation rate rewards C_star C_h q t control0 y, physicalProposalBit rate y.2)) =
      (((μC).prod (timeControlLaw p)).map
        (birthObservation rate rewards C_star C_h q t control0)).prod (proposalBitLaw rate) := by
  let zero : ContinuousControlSlice.Scalar := ⟨0, by constructor <;> norm_num⟩
  let H := birthObservation rate rewards C_star C_h q t control0
  let g : X × PropRestControl p → X × (AssignmentVector p × BirthPair p) := fun y =>
    H (y.1, (proposalControlSplit p).symm (zero, y.2))
  have hg : Measurable g :=
    (measurable_birthObservation rate rewards C_star C_h q t control0).comp
      (measurable_fst.prodMk ((proposalControlSplit p).symm.measurable.comp
        (measurable_const.prodMk measurable_snd)))
  have heq (y : X × ContinuousLearningRows.TimeControl p) :
      g (y.1, (proposalControlSplit p y.2).2) = H y := by
    have hreplace := proposalControlSplit_symm_replace p zero
      (proposalControlSplit p y.2).1 (proposalControlSplit p y.2).2
    rw [(proposalControlSplit p).symm_apply_apply] at hreplace
    change H (y.1, (proposalControlSplit p).symm (zero, (proposalControlSplit p y.2).2)) = H y
    rw [hreplace]
    exact birthObservation_replaceProposal rate rewards C_star C_h q t control0 _ _ _
  have hfactor := proposalSplit_joint_pushforward μC g hg rate
  simp_rw [heq] at hfactor
  have hmarg := congrArg (Measure.map Prod.fst) hfactor
  have hH : Measurable (fun y : X × ContinuousLearningRows.TimeControl p =>
      (H y, physicalProposalBit rate y.2)) :=
    (measurable_birthObservation rate rewards C_star C_h q t control0).prodMk
      ((measurable_physicalProposalBit rate).comp measurable_snd)
  rw [Measure.map_map measurable_fst hH,
    (measurePreserving_fst (μ := ((μC).prod (proposalRestControlLaw p)).map g)
      (ν := proposalBitLaw rate)).map_eq] at hmarg
  rw [← hmarg] at hfactor
  exact hfactor

local instance birthRetainedStartMeasurableSpace : MeasurableSpace X :=
  inferInstanceAs (MeasurableSpace
    (ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t t.val le_rfl control0))

local instance birthAuxiliaryMeasurableSpace : MeasurableSpace (AuxiliaryArray p) :=
  inferInstanceAs (MeasurableSpace (ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p))

local instance birthRunStateMeasurableSpace : MeasurableSpace (RecordedQueueRun.RunState p.K) :=
  ReferenceFirstLiveChronologicalPrefixMeasurability.firstLiveRunStateMeasurableSpace p.K

/-- Adjoin the literal zero-state all-arm update after the pair is read. -/
def birthOutput (aux : AuxiliaryArray p)
    (y : (X × (AssignmentVector p × BirthPair p)) × Bool) :
    (X × (AssignmentVector p × (AuxiliaryArray p ×
      (BirthPair p × (RecordedQueueRun.RunState p.K × Bool))))) :=
  (y.1.1, (y.1.2.1, (aux, (y.1.2.2,
    (birthUpdate rate rewards t y.1.2.1 y.1.2.2, y.2)))))

private theorem measurable_birthOutput (aux : AuxiliaryArray p) :
    Measurable (birthOutput rate rewards C_star C_h q t control0 aux) := by
  let zeroVector : AssignmentVector p := fun _ => ⟨0, by constructor <;> norm_num⟩
  have hu : Measurable (fun y : (X × (AssignmentVector p × BirthPair p)) × Bool =>
      birthUpdate rate rewards t y.1.2.1 y.1.2.2) := by
    exact (measurable_of_finite (birthUpdate rate rewards t zeroVector)).comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (measurable_const.prodMk
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
          (hu.prodMk measurable_snd))))

private theorem actualBirthTuple_eq_output
    (z : BirthSource p rate rewards C_star C_h q t) (aux : AuxiliaryArray p) :
    actualBirthTuple rate rewards C_star C_h q t control0 z aux =
      birthOutput rate rewards C_star C_h q t control0 aux
        (birthObservation rate rewards C_star C_h q t control0
          (sourceControlCoordinates rate rewards C_star C_h q t control0 z),
        physicalProposalBit rate
          (sourceControlCoordinates rate rewards C_star C_h q t control0 z).2) := by
  rw [actual_birth_tuple_eq_coordinates]
  have hc : ReferenceFirstLaunchRecordingPhysicalMarker.currentControl
      (coords z).2.1 (coords z).2.2 =
      (sourceControlCoordinates rate rewards C_star C_h q t control0 z).2 :=
    (split).symm_apply_apply _
  simp only [hc]
  rfl

private theorem integrable_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hB)

private theorem norm_integral_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : ‖∫ x, f x ∂μ‖ ≤ B := by
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ _ : α, B ∂μ :=
      norm_integral_le_of_norm_le (integrable_const B) (Filter.Eventually.of_forall hB)
    _ = B := by simp

/-- Bounded Borel tests of the actual birth on each fixed auxiliary array.
The recorder and reserved FAST remain one correlated kernel depending on the
whole assignment vector; only the original proposal bit factors from it. -/
theorem actual_birth_fixed_aux_integral
    (aux : AuxiliaryArray p)
    (F : (X × (AssignmentVector p × (AuxiliaryArray p ×
      (BirthPair p × (RecordedQueueRun.RunState p.K × Bool))))) → ℝ)
    (hF : Measurable F) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B) :
    (∫ z, F (actualBirthTuple rate rewards C_star C_h q t control0 z aux) ∂μZ) =
      ∫ x, ∫ v, ∫ pair, ∫ b,
        F (x, (v, (aux, (pair, (birthUpdate rate rewards t v pair, b)))))
          ∂proposalBitLaw rate ∂birthPairKernel rate t v
          ∂assignmentLaw p.K ∂μC := by
  let H := birthObservation rate rewards C_star C_h q t control0
  let O := birthOutput rate rewards C_star C_h q t control0 aux
  let μ := (μC).prod (timeControlLaw p)
  let test : (X × (AssignmentVector p × BirthPair p)) × Bool → ℝ := F ∘ O
  have ht : Measurable test := hF.comp
    (measurable_birthOutput rate rewards C_star C_h q t control0 aux)
  have htB : ∀ y, ‖test y‖ ≤ B := fun y => hB (O y)
  let g : X × (AssignmentVector p × BirthPair p) → ℝ := fun o =>
    ∫ b, test (o, b) ∂proposalBitLaw rate
  have hg : Measurable g := ht.stronglyMeasurable.integral_prod_right'.measurable
  have hgB : ∀ o, ‖g o‖ ≤ B := fun o =>
    norm_integral_bounded (proposalBitLaw rate) _ B (fun b => htB (o, b))
  have hH : Measurable H := measurable_birthObservation rate rewards C_star C_h q t control0
  have hobs : Measurable (fun y : X × ContinuousLearningRows.TimeControl p =>
      (H y, physicalProposalBit rate y.2)) :=
    hH.prodMk ((measurable_physicalProposalBit rate).comp measurable_snd)
  have hsource := measurable_sourceControlCoordinates rate rewards C_star C_h q t control0
  have hstart :
      (∫ z, F (actualBirthTuple rate rewards C_star C_h q t control0 z aux) ∂μZ) =
      ∫ y, test (H y, physicalProposalBit rate y.2) ∂μ := by
    calc
      _ = ∫ z, test (H (sourceControlCoordinates rate rewards C_star C_h q t control0 z),
          physicalProposalBit rate
            (sourceControlCoordinates rate rewards C_star C_h q t control0 z).2) ∂μZ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => congrArg F
          (actualBirthTuple_eq_output rate rewards C_star C_h q t control0 z aux)
      _ = ∫ y, test (H y, physicalProposalBit rate y.2)
          ∂(μZ).map (sourceControlCoordinates rate rewards C_star C_h q t control0) :=
        (integral_map hsource.aemeasurable (ht.comp hobs).aestronglyMeasurable).symm
      _ = _ := by rw [map_sourceControlCoordinates]
  have hfactor :
      (∫ y, test (H y, physicalProposalBit rate y.2) ∂μ) =
        ∫ y, g (H y) ∂μ := by
    calc
      _ = ∫ o, test o ∂μ.map (fun y => (H y, physicalProposalBit rate y.2)) :=
        (integral_map hobs.aemeasurable ht.aestronglyMeasurable).symm
      _ = ∫ o, test o ∂(μ.map H).prod (proposalBitLaw rate) := by
        rw [birthObservation_proposal_joint_map]
      _ = ∫ o, g o ∂μ.map H :=
        integral_prod test (integrable_bounded _ test ht B htB)
      _ = _ := integral_map hH.aemeasurable hg.aestronglyMeasurable
  rw [hstart, hfactor]
  change (∫ y, (g ∘ H) y ∂(μC).prod (timeControlLaw p)) = _
  rw [integral_prod (g ∘ H) (integrable_bounded μ (g ∘ H) (hg.comp hH) B (fun y => hgB (H y)))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change (∫ u, g (H (x, u)) ∂timeControlLaw p) = _
  have hsplit := (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).symm
  rw [← hsplit.integral_comp' (fun u => g (H (x, u)))]
  have hsplitM : Measurable (fun vd : AssignmentVector p ×
      ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p =>
      g (H (x, (split).symm vd))) :=
    hg.comp (hH.comp (measurable_const.prodMk (split).symm.measurable))
  rw [integral_prod _ (integrable_bounded _ _ hsplitM B (fun vd => hgB _))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  have hp : Measurable (fun d : ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p =>
      birthPairOnSlice rate t v
        (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl v d).1) :=
    (measurable_birthPairOnSlice rate t v).comp
      (measurable_fst.comp ((split).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  have hpairTest : Measurable (fun pair : BirthPair p => g (x, (v, pair))) :=
    hg.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  simp only [H, birthObservation, (split).apply_symm_apply]
  change (∫ d, g (x, (v, birthPairOnSlice rate t v
      (ReferenceFirstLaunchRecordingPhysicalMarker.currentControl v d).1))
      ∂ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p) = _
  rw [← integral_map hp.aemeasurable hpairTest.aestronglyMeasurable,
    birthPairKernel_eq_nonassignment]
  rfl

/-- Joint Borel readout of the actual birth and the entire independent
auxiliary array. This is a pre-refresh observable. -/
theorem measurable_actualBirthTuple :
    Measurable (fun za : BirthSource p rate rewards C_star C_h q t × AuxiliaryArray p =>
      actualBirthTuple rate rewards C_star C_h q t control0 za.1 za.2) := by
  let H := birthObservation rate rewards C_star C_h q t control0
  let c := sourceControlCoordinates rate rewards C_star C_h q t control0
  have hc : Measurable (fun za : BirthSource p rate rewards C_star C_h q t × AuxiliaryArray p =>
      c za.1) :=
    (measurable_sourceControlCoordinates rate rewards C_star C_h q t control0).comp measurable_fst
  have ho := (measurable_birthObservation rate rewards C_star C_h q t control0).comp hc
  have hp : Measurable (fun za : BirthSource p rate rewards C_star C_h q t × AuxiliaryArray p =>
      (H (c za.1)).2.2) := measurable_snd.comp (measurable_snd.comp ho)
  let zeroVector : AssignmentVector p := fun _ => ⟨0, by constructor <;> norm_num⟩
  have hu : Measurable (fun za : BirthSource p rate rewards C_star C_h q t × AuxiliaryArray p =>
      birthUpdate rate rewards t (H (c za.1)).2.1 (H (c za.1)).2.2) :=
    (measurable_of_finite (birthUpdate rate rewards t zeroVector)).comp hp
  have hb : Measurable (fun za : BirthSource p rate rewards C_star C_h q t × AuxiliaryArray p =>
      physicalProposalBit rate (c za.1).2) :=
    (measurable_physicalProposalBit rate).comp (measurable_snd.comp hc)
  have hout := (measurable_fst.comp ho).prodMk
    ((measurable_fst.comp (measurable_snd.comp ho)).prodMk
      (measurable_snd.prodMk (hp.prodMk (hu.prodMk hb))))
  convert hout using 1
  funext za
  exact actualBirthTuple_eq_output rate rewards C_star C_h q t control0 za.1 za.2

/-- The actual birth joint source law tested by an arbitrary bounded Borel
real function. The source stratum is the original unnormalized measure, and
all auxiliary coordinates are retained. The right side is the product of the
original auxiliary law, retained remainder law and whole assignment law,
followed by the same-slice correlated pair kernel and original proposal law.
No post-update survival or positive-mass condition is imposed. -/
theorem actual_birth_joint_integral
    (F : (X × (AssignmentVector p × (AuxiliaryArray p ×
      (BirthPair p × (RecordedQueueRun.RunState p.K × Bool))))) → ℝ)
    (hF : Measurable F) (B : ℝ) (hB : ∀ y, ‖F y‖ ≤ B) :
    (∫ za, F (actualBirthTuple rate rewards C_star C_h q t control0 za.1 za.2)
      ∂(μZ).prod νA) =
      ∫ aux, ∫ x, ∫ v, ∫ pair, ∫ b,
        F (x, (v, (aux, (pair, (birthUpdate rate rewards t v pair, b)))))
          ∂proposalBitLaw rate ∂birthPairKernel rate t v
          ∂assignmentLaw p.K ∂μC ∂νA := by
  have hm := hF.comp (measurable_actualBirthTuple rate rewards C_star C_h q t control0)
  have hi : Integrable (fun za : BirthSource p rate rewards C_star C_h q t × AuxiliaryArray p =>
      F (actualBirthTuple rate rewards C_star C_h q t control0 za.1 za.2)) ((μZ).prod νA) :=
    integrable_bounded ((μZ).prod νA) _ hm B
      (fun za => hB (actualBirthTuple rate rewards C_star C_h q t control0 za.1 za.2))
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun aux =>
    actual_birth_fixed_aux_integral rate rewards C_star C_h q t control0 aux F hF B hB

end Bandits.Support.ReferenceFirstLiveBirthJointSourceLaw

end
