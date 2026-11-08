/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePostInvocationPrefixLocality
public import Bandits.Support.ReferencePostInvocationGeneratedAlignment
public import Bandits.Support.ReferenceFirstNextLiftFutureControl
public import Bandits.Support.ReferenceFirstNextLiftFutureAuxiliaryPairLaw

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Actual continuing LIVE source law

The current whole control varies in the original source. The retained payload,
ordinary follower snapshot and numerical PRE are produced from source causality.
The recorder and reserved FAST remain their correlated native pair.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, `08_main_theorem.tex:78-109`.
This internal component does not assert manuscript or main-regret closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFixedTimeSourceControlCoupling
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstWindowNumericalStream ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceOriginalCalendarContinuingLiveRecorderLaw
open ReferenceActivePhysicalStep ReferenceContinuingLiveSlicePreparation
open ReferenceContinuingDataCandidateLogging ReferenceCoordinatorRecorderCallCorrespondence
open ReferenceFirstLivePostUpdateProposalLaw
  (physicalProposalBit proposalBitLaw replaceProposalScalar proposalControlSplit PropRestControl
    measurable_physicalProposalBit proposalControlSplit_symm_replace proposalSplit_joint_pushforward
    proposalRestControlLaw proposalBitLaw_true physicalProposalThreshold_bounds
    completeRowProposalBit_eq_physicalProposalBit liveRecordingFastPair_replaceProposal)

namespace Bandits.Support.ReferencePostInvocationLiveNativeLaw

variable {p : ConstructorDimensions.Parameters}

abbrev Source := BootstrapPrivateRoundStreams.SourceInput
abbrev Auxiliary := ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray
abbrev Control := ContinuousLearningRows.TimeControl
abbrev Scalar := ContinuousControlSlice.Scalar

local instance sourceMeasurableSpace : MeasurableSpace (Source p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Option X) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) := ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : Control p) (q : Fin p.T)

local notation "LiveSource" =>
  ReferencePostInvocationNoncallGeometry.ContinuingLiveSource rate rewards C_star C_h q
local notation "liveRecord" =>
  ReferencePostInvocationNoncallGeometry.continuingRecord rate rewards C_star C_h q
local notation "liveCell" =>
  ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q
local notation "liveBefore" =>
  ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "logicalCellAt" =>
  ReferencePostInvocationNoncallGeometry.continuingLogicalCell rate rewards C_star C_h q

/-- The literal current physical record with only its whole control replaced. -/
def controlledRecord (r : Record rate) (c : Control p) : Record rate :=
  ⟨inputAtControl r.input c, ReferenceActivePhysicalStep.step (inputAtControl r.input c), rfl⟩

private theorem roundInput_eq {x y : ReferenceActivePhysicalStep.RoundInput p rate}
    (hs : x.state = y.state) (hr : x.rows = y.rows) (hj : x.selected = y.selected)
    (ht : x.time = y.time) (hw : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  cases hs
  cases hr
  cases hj
  cases ht
  cases hw
  rfl

include control0 in
/-- Whole-source current-control replacement produces this exact physical
record. Every other row, date and private coordinate remains in the source. -/
theorem actualRecord_replace_control
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : Record rate)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) (c : Control p) :
    actualRecordAt rate rewards C_star C_h q (replaceSourceControl p q z c) =
      some (controlledRecord rate r c) := by
  obtain ⟨r', hr', hs⟩ :=
    ReferenceFirstCorrectedCollectionCausalReadout.actualIncoming_replaceSourceControl
      rate rewards C_star C_h control0 q z r hr c
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q z r hr
  have hf' := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h q _ r' hr'
  have hx : r'.input = inputAtControl r.input c := by
    apply roundInput_eq rate
    · exact hs
    · simp only [inputAtControl, rowsAtControl, rowAtControl, RoundInput.row,
        hf.1, hf.2.1, hf.2.2.1, hf'.1, replaceSourceControl,
        sourceCoordinatorIndex_eq_selectedRowIndex]
    · exact hf'.2.1.trans hf.2.1.symm
    · exact hf'.2.2.1.trans hf.2.2.1.symm
    · exact hf'.2.2.2.trans hf.2.2.2.symm
  have he : r' = controlledRecord rate r c := by
    cases r' with
    | mk input output hout =>
      dsimp only at hx
      cases hout
      cases hx
      rfl
  exact he ▸ hr'

/-- Recorder and reserved FAST on the SAME physical control. -/
def livePhysicalPair (r : Record rate) (selected : Selection r.input) :
    Control p → Option (Fin p.K) × CanonicalFastSampling.FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p selected.view.payload.assignment) :=
  fun c => (ReferenceContinuingRecordingFastPair.physicalMarkerOnRecord
      (controlledRecord rate r c) selected.view.payload true,
    SnapshotRecordingKernel.fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
      selected.view.payload.anchor
      (sourceWeights selected.view.payload selected.view.complementWeights)
      selected.view.payload.anchor_pos
      (sourceWeights_pos _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
      (sourceWeights_lower _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
      (sourceWeights_upper _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
      selected.view.payload.assignment c.1)

/-- The canonical SAME-slice pair at the actual later-installation snapshot. -/
def liveCanonicalPair (r : Record rate) (selected : Selection r.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) :
    Control p → Option (Fin p.K) × CanonicalFastSampling.FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p selected.view.payload.assignment) :=
  fun c => FastRewardSliceLaw.liveRecordingFastPair p rate.eta.val rate.eta.property rate.sourceCap
    selected.view.payload.anchor (sourceWeights selected.view.payload selected.view.complementWeights)
    selected.view.payload.anchor_pos
    (sourceWeights_pos _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
    (sourceWeights_lower _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
    (sourceWeights_upper _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
    selected.view.payload.assignment (ReferenceActiveDataOwnership.choiceSnapshot selected states) c.1

/-- The prescribed correlated native law, at the actual prepared snapshot. -/
def liveNativePairLaw (r : Record rate) (selected : Selection r.input)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta) :=
  FastRewardSliceLaw.liveRecordingFastPushforward p rate.eta.val rate.eta.property rate.sourceCap
    selected.view.payload.anchor
    (sourceWeights selected.view.payload selected.view.complementWeights)
    selected.view.payload.anchor_pos
    (sourceWeights_pos _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
    (sourceWeights_lower _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
    (sourceWeights_upper _ _ _ _ (ReferenceLaterLiveNumericalReadout.selection_choiceValid selected))
    selected.view.payload.assignment (ReferenceActiveDataOwnership.choiceSnapshot selected states)

/-- Produce the full continuing operational telescope from an actual original
record. In particular no prepared-follower or successful-recorder premise is
added to the source domain. The physical pair stays correlated. -/
theorem actual_livePhysicalPair_law
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ actualDomain rate rewards C_star C_h q)
    (r : Record rate) (cell : ActualLiveSourceCell r)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r) :
    (∀ c, livePhysicalPair rate r cell.selected c = liveCanonicalPair rate r cell.selected cell.states c) ∧
    Measurable (livePhysicalPair rate r cell.selected) ∧
      (ContinuousLearningRows.timeControlLaw p).map (livePhysicalPair rate r cell.selected) =
        liveNativePairLaw rate r cell.selected cell.states := by
  obtain ⟨k, hk⟩ := actualRecord_suffix_index rate rewards C_star C_h q z r hr
  obtain ⟨hcross, span, hpref⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z k
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross
  let seed := actualFirstLiveSeed rate z rewards C_star C_h hcross
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  have heq : r = ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span seed.activeAtStart :=
    hk.symm.trans hpref
  obtain ⟨r0, hr0, ⟨regs, owned, base, hcoord⟩, _⟩ := hz
  have he : r0 = r := Option.some.inj (hr0.symm.trans hr)
  subst r0
  let record := ReferenceAssignmentPayloadChronology.actualRunRecordAt initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span seed.activeAtStart
  change r = record at heq
  clear hk hpref
  subst r
  have hp : record.output.preparation = prepare record.input := by rw [record.output_eq]; rfl
  have hordinary : ∀ i, ((prepare record.input).followers.followers i).configuration =
      .ordinary (cell.states i) (cell.memories i) := by rw [← hp]; exact cell.ordinary
  have hsel := cell.selection_actual
  have hd : record.output.preparation.coordinator = .live regs owned base
      (CoordinatorRoundDispatch.dispatchLive (liveInput record.input regs owned base)) := by
    rw [hp]
    exact ReferenceLiveDispatchMeasurability.canonicalDispatch_live_reconstruction _ _ _ _ hcoord
  have hframes := actual_call_frames record
  rw [hd] at hsel hframes
  generalize houtcome : CoordinatorRoundDispatch.dispatchLive
    (liveInput record.input regs owned base) = outcome at hd hsel hframes
  cases outcome <;> try cases hsel
  case cutoffChosen dispatched hstart ledger hinit hledger hdomains hclock hpending hno arm =>
    change ReferenceActivePhysicalStep.selectionAt _ _ _ _ _ _ = some cell.selected at hsel
    rw [selectionAt_eq record.input regs.payload dispatched.startResult record.input.time
      (liveRegistersAt regs record.input.time).complementWeights arm rfl] at hsel
    have hl := cell.assignment_live
    rw [(Option.some.inj hsel).symm] at hl
    exact False.elim (hframes.1 hl)
  case continuingChosen dispatched hstart continuation arm =>
    change ReferenceActivePhysicalStep.selectionAt _ _ _ _ _ _ = some cell.selected at hsel
    rw [selectionAt_eq record.input regs.payload dispatched.startResult record.input.time
      (liveRegistersAt regs record.input.time).complementWeights arm rfl] at hsel
    have he := (Option.some.inj hsel).symm
    have hactual := ReferenceContinuingRecordingFastLaw.actual_continuing_live_joint_law
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val
      span seed.activeAtStart seed.followers seed.memory seed.coordinatorFirst seed.configuration
      seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps
      regs owned base dispatched hstart continuation arm (by
        change (prepare record.input).coordinator = _
        rw [← hp]; exact hd) cell.states cell.memories hordinary hframes.2
    have hpoint := ReferenceContinuingRecordingFastPair.prefix_physical_fast_pair_eq
      initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val
      span seed.activeAtStart seed.followers seed.memory seed.coordinatorFirst seed.configuration
      seed.unoccupied seed.bufferValid seed.chronologicalBuffer seed.bufferStamps
      regs owned base dispatched hstart continuation arm (by
        change (prepare record.input).coordinator = _
        rw [← hp]; exact hd) cell.states cell.memories hordinary hframes.2
    dsimp only [ReferenceContinuingRecordingFastPair.prefixPhysicalFastPairLaw] at hpoint
    have hW : sourceWeights regs.payload (liveRegistersAt regs record.input.time).complementWeights =
        liveSliceWeights regs record.input.time := rfl
    have htime : (candidateInput initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span
        seed.activeAtStart).time = record.input.time := rfl
    have hcand (c : Control p) : candidateRecord initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards start k.val span
        seed.activeAtStart c = controlledRecord rate record c := rfl
    dsimp only at hactual
    have hresult := And.intro hpoint (And.intro hactual.1 hactual.2.1)
    unfold ReferenceContinuingRecordingFastPair.candidatePhysicalFastPair
      ReferenceContinuingRecordingFastPair.candidatePhysicalMarker at hresult
    rw [he]
    unfold livePhysicalPair liveCanonicalPair liveNativePairLaw
    simp only [selectionOfArm, hW, liveSliceSnapshot,
      ReferenceActiveDataOwnership.choiceSnapshot, htime, hcand] at hresult ⊢
    (convert hresult using 1; rfl)

/-- No current physical proposal scalar is used by the ENTIRE correlated
recorder/FAST pair on an actual continuing source. -/
theorem livePhysicalPair_replaceProposal
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ actualDomain rate rewards C_star C_h q)
    (r : Record rate) (cell : ActualLiveSourceCell r)
    (hr : actualRecordAt rate rewards C_star C_h q z = some r)
    (c : Control p) (a : Scalar) :
    livePhysicalPair rate r cell.selected
        (replaceProposalScalar p c a) =
      livePhysicalPair rate r cell.selected c := by
  have he := (actual_livePhysicalPair_law rate rewards C_star C_h q z hz r cell hr).1
  rw [he, he]
  exact liveRecordingFastPair_replaceProposal
    rate _ _ _ _ _ _ _ _ c a

/-- The source-root LIVE pair law uses the actual cell producer, with no
supplied trace, prepared state, matching seed or operational-law premise. -/
theorem continuingSource_physical_pair_law
    (z : LiveSource) :
    let r := liveRecord z
    let cell := liveCell z
    (∀ c, livePhysicalPair rate r cell.selected c = liveCanonicalPair rate r cell.selected cell.states c) ∧
      Measurable (livePhysicalPair rate r cell.selected) ∧
      (ContinuousLearningRows.timeControlLaw p).map (livePhysicalPair rate r cell.selected) =
        liveNativePairLaw rate r cell.selected cell.states := by
  dsimp only
  exact actual_livePhysicalPair_law rate rewards C_star C_h q z.val z.property _ _
    (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec rate rewards C_star C_h q z).1


include control0 in
/-- The actual continuing domain uses no current or future selected control. -/
theorem continuingDomain_replace (z : Source p) (c : Control p) :
    replaceSourceControl p q z c ∈
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q ↔
      z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q := by
  have hi : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h q
        (replaceSourceControl p q z c) := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q z,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor rate rewards C_star C_h control0 q
        (replaceSourceControl p q z c),
      ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl]
  exact ⟨actualDomain_of_incoming_eq rate rewards C_star C_h q _ z hi.symm,
    actualDomain_of_incoming_eq rate rewards C_star C_h q z _ hi⟩

/-- Replace the whole current control of the original source, preserving its
published output, all other dates and rows, original private arrays and J. -/
def sourceAt (z : LiveSource) (c : Control p) :
    LiveSource :=
  ⟨replaceSourceControl p q z.val c,
    (continuingDomain_replace rate rewards C_star C_h control0 q z.val c).mpr z.property⟩

/-- Whole-control replacement is Borel into the actual continuing domain. -/
theorem measurable_sourceAt (z : LiveSource) :
    Measurable (sourceAt rate rewards C_star C_h control0 q z) :=
  ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p q).comp
    (measurable_const.prodMk measurable_id)).subtype_mk

/-- The source family's current record is the literal controlled record. -/
theorem sourceAt_record (z : LiveSource) (c : Control p) :
    liveRecord (sourceAt rate rewards C_star C_h control0 q z c) =
      controlledRecord rate (liveRecord z) c := by
  apply Option.some.inj
  exact (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec rate rewards C_star C_h q
    (sourceAt rate rewards C_star C_h control0 q z c)).1.symm.trans
      (actualRecord_replace_control rate rewards C_star C_h control0 q z.val _
        (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec rate rewards C_star C_h q z).1 c)

/-- Source-prefix causality fixes the entire numerical PRE, including disabled
physical dates and all previous queue records. -/
theorem sourceAt_before (z : LiveSource) (c : Control p) :
    liveBefore (sourceAt rate rewards C_star C_h control0 q z c) =
      liveBefore z := by
  apply Option.some.inj
  rw [← ReferencePostInvocationPrefixLocality.continuingBefore_spec rate rewards C_star C_h q _,
    ← ReferencePostInvocationPrefixLocality.continuingBefore_spec rate rewards C_star C_h q z,
    ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h control0
      q.castSucc q.val le_rfl
      (sourceAt rate rewards C_star C_h control0 q z c).val]
  change ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h q.castSucc
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 q.val
      (replaceSourceControl p q z.val c)) = _
  rw [ReferenceFirstCollectionOldRecorderFoundation.sourcePrefix_replaceCurrent control0 q q.val le_rfl,
    ← ReferencePostInvocationPrefixLocality.prefixNumerical_sourcePrefix rate rewards C_star C_h control0
      q.castSucc q.val le_rfl]

/-- The actual selected view is fixed by incoming state and date. The chosen
physical arm may vary with the current control. -/
theorem sourceAt_view (z : LiveSource) (c : Control p) :
    (liveCell
      (sourceAt rate rewards C_star C_h control0 q z c)).selected.view =
      (liveCell z).selected.view := by
  let r := liveRecord z
  let r' := liveRecord (sourceAt rate rewards C_star C_h control0 q z c)
  let cell := liveCell z
  let cell' := liveCell (sourceAt rate rewards C_star C_h control0 q z c)
  have hr : r' = controlledRecord rate r c := sourceAt_record rate rewards C_star C_h control0 q z c
  have hs : r.input.state = r'.input.state := by rw [hr]; rfl
  have ht : r.input.time = r'.input.time := by rw [hr]; rfl
  have hl : ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
    obtain ⟨r0, hr0, hl, _⟩ := z.property
    have he : r0 = r := Option.some.inj (hr0.symm.trans
      (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec rate rewards C_star C_h q z).1)
    exact he ▸ hl
  have hv := ReferenceFirstCollectionRenewalNextRecordingPriorView.downView_congr r.input r'.input hs ht
    (by obtain ⟨_, _, _, h⟩ := hl; rw [h]; trivial)
  have hsel : (dispatch r.input).selection = some cell.selected := by
    have h := cell.selection_actual
    change r.output.preparation.coordinator.selection = _ at h
    rw [r.output_eq] at h
    exact h
  have hsel' : (dispatch r'.input).selection = some cell'.selected := by
    have h := cell'.selection_actual
    change r'.output.preparation.coordinator.selection = _ at h
    rw [r'.output_eq] at h
    exact h
  simpa only [DispatchCut.downView, hsel, hsel', Option.map_some, Option.some.injEq] using hv.symm

/-- Ordinary preparation uses no current row coordinates. Both the full states
and local memories are the actual prepared follower outputs. -/
theorem sourceAt_followers (z : LiveSource) (c : Control p) :
    let cell := liveCell z
    let cell' := liveCell (sourceAt rate rewards C_star C_h control0 q z c)
    cell'.states = cell.states ∧ cell'.memories = cell.memories := by
  dsimp only
  let r := liveRecord z
  let r' := liveRecord (sourceAt rate rewards C_star C_h control0 q z c)
  let cell := liveCell z
  let cell' := liveCell (sourceAt rate rewards C_star C_h control0 q z c)
  have hr : r' = controlledRecord rate r c := sourceAt_record rate rewards C_star C_h control0 q z c
  have he (i) := ReferenceFirstCollectionRenewalNextRecordingPriorView.ordinary_preparation_congr r'.input r.input
    (by rw [hr]; rfl) (by rw [hr]; rfl) i (cell'.states i) (cell.states i)
    (cell'.memories i) (cell.memories i)
    (by
      have h := cell'.ordinary i
      change (r'.output.preparation.followers.followers i).configuration = _ at h
      rw [r'.output_eq] at h
      exact h)
    (by
      have h := cell.ordinary i
      change (r.output.preparation.followers.followers i).configuration = _ at h
      rw [r.output_eq] at h
      exact h)
  exact ⟨funext (fun i => (he i).1), funext (fun i => (he i).2)⟩

private theorem controlledRecord_control (r : Record rate) (c : Control p) :
    (controlledRecord rate r c).input.row.2 (controlledRecord rate r c).input.time = c := by
  simp only [controlledRecord, inputAtControl, RoundInput.row, rowsAtControl,
    rowAtControl, Function.update_self]

/-- Literal finite recorder/FAST coordinates; subtype erasure retains its
original slow-set domain in the defining correlated native law. -/
def physicalPair (z : LiveSource) (c : Control p) :
    Option (Fin p.K) × Fin p.K :=
  let r := liveRecord z
  let cell := liveCell z
  let v := livePhysicalPair rate r cell.selected c
  (v.1, v.2.val)

/-- The native mass is the admitted correlated pair at this actual retained
payload, source weights and prepared choice snapshot, transported to Fin K. -/
def nativePairLaw (z : LiveSource) :
    Measure (Option (Fin p.K) × Fin p.K) :=
  (liveNativePairLaw rate (liveRecord z)
    (liveCell z).selected
    (liveCell z).states).map
      (fun v => (v.1, v.2.val))

theorem physicalPair_law (z : LiveSource) :
    Measurable (physicalPair rate rewards C_star C_h q z) ∧
    (ContinuousLearningRows.timeControlLaw p).map (physicalPair rate rewards C_star C_h q z) =
      nativePairLaw rate rewards C_star C_h q z := by
  have h := continuingSource_physical_pair_law rate rewards C_star C_h q z
  have he : Measurable (fun v : Option (Fin p.K) × CanonicalFastSampling.FastArm
      (SnapshotRecordingKernel.assignmentSlowSet p
        (liveCell z).selected.view.payload.assignment) =>
        (v.1, v.2.val)) := measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  exact ⟨he.comp h.2.1, by
    rw [nativePairLaw, ← h.2.2, Measure.map_map he h.2.1]
    rfl⟩

theorem physicalPair_replaceProposal (z : LiveSource)
    (c : Control p) (x : Scalar) :
    physicalPair rate rewards C_star C_h q z (replaceProposalScalar p c x) =
      physicalPair rate rewards C_star C_h q z c := by
  dsimp only [physicalPair]
  rw [livePhysicalPair_replaceProposal rate rewards C_star C_h q z.val z.property _ _
    (ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec rate rewards C_star C_h q z).1]

/-- The actual numerical input with marker replaced, keeping the whole reward
row, enabled service and the retained assignment's actual recording rates. -/
def inputForMarker (z : LiveSource) (i : Option (Fin p.K)) :
    RecordedQueueRun.RoundInput p.K :=
  { (liveCell z).input with recordedArm := i }

private theorem sourceArm_at_control (z : LiveSource)
    (c : Control p) :
    let r := liveRecord z
    let cell := liveCell z
    sourceArm (controlledRecord rate r c) cell.selected.view.payload
      cell.selected.view.pendingAtChoice cell.states cell.selected.view.complementWeights
      cell.selected.view.cutoff cell.choiceInputsValid =
        (physicalPair rate rewards C_star C_h q z c).1 := by
  dsimp only
  have hp := congrArg Prod.fst
    ((continuingSource_physical_pair_law rate rewards C_star C_h q z).1 c)
  dsimp only [physicalPair, liveCanonicalPair, FastRewardSliceLaw.liveRecordingFastPair,
    ReferenceActiveDataOwnership.choiceSnapshot] at hp ⊢
  rw [← (liveCell z).selected.pending_eq] at hp
  rw [hp]
  simp only [sourceArm, controlledRecord_control]

private theorem sourceArm_congr (r s : Record rate)
    (v w : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (states states' : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hv : w = v) (hs : states' = states)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff r.input.time v.complementWeights)
    (hvalid' : CoordinatorLocalArmChoice.ChoiceInputsValid w.payload w.cutoff s.input.time w.complementWeights)
    (hu : (s.input.row.2 s.input.time).1 = (r.input.row.2 r.input.time).1) :
    sourceArm s w.payload w.pendingAtChoice states' w.complementWeights w.cutoff hvalid' =
      sourceArm r v.payload v.pendingAtChoice states v.complementWeights v.cutoff hvalid := by
  cases hv
  cases hs
  unfold sourceArm
  rw [hu]

private theorem numericalInput_ext (x y : RecordedQueueRun.RoundInput p.K)
    (he : x.enabled = y.enabled) (hi : x.recordedArm = y.recordedArm)
    (hw : x.reward = y.reward) (hr : x.rate = y.rate) : x = y := by
  cases x
  cases y
  cases he
  cases hi
  cases hw
  cases hr
  rfl

/-- All-controls numerical input identity, with no supplied preparation,
matching-history, complement or nonuse hypothesis. -/
theorem sourceAt_input (z : LiveSource) (c : Control p) :
    (liveCell
      (sourceAt rate rewards C_star C_h control0 q z c)).input =
      inputForMarker rate rewards C_star C_h q z (physicalPair rate rewards C_star C_h q z c).1 := by
  let r := liveRecord z
  let r' := liveRecord (sourceAt rate rewards C_star C_h control0 q z c)
  let cell := liveCell z
  let cell' := liveCell (sourceAt rate rewards C_star C_h control0 q z c)
  have hv : cell'.selected.view = cell.selected.view := sourceAt_view rate rewards C_star C_h control0 q z c
  have hstates : cell'.states = cell.states := (sourceAt_followers rate rewards C_star C_h control0 q z c).1
  have hr : r' = controlledRecord rate r c := sourceAt_record rate rewards C_star C_h control0 q z c
  apply numericalInput_ext
  · exact cell'.enabled.trans cell.enabled.symm
  · change cell'.input.recordedArm = (physicalPair rate rewards C_star C_h q z c).1
    rw [cell'.recordedArm_eq]
    exact (sourceArm_congr rate (controlledRecord rate r c) r' cell.selected.view cell'.selected.view
      cell.states cell'.states hv hstates cell.choiceInputsValid cell'.choiceInputsValid
      (by rw [hr])).trans (sourceArm_at_control rate rewards C_star C_h q z c)
  · change cell'.input.reward = cell.input.reward
    rw [cell'.input_eq, cell.input_eq]
    dsimp only [sourceCell]
    change (fun arm => ((r'.input.rewards r'.input.time arm).val : ℝ) / (D p : ℝ)) = _
    rw [hr]
    rfl
  · change cell'.input.rate = cell.input.rate
    rw [cell'.input_eq, cell.input_eq]
    exact congrArg (fun v => v.payload.rate) hv

/-- The current physical proposal is the same deterministic bit in the same
whole control, even on the first detecting numerical update. -/
theorem sourceAt_proposal (z : LiveSource) (c : Control p) :
    let r := liveRecord (sourceAt rate rewards C_star C_h control0 q z c)
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time =
      physicalProposalBit rate c := by
  dsimp only
  apply completeRowProposalBit_eq_physicalProposalBit
  change ((liveRecord
    (sourceAt rate rewards C_star C_h control0 q z c)).input.row.2
    (liveRecord
      (sourceAt rate rewards C_star C_h control0 q z c)).input.time).1 _ = _
  rw [sourceAt_record, controlledRecord_control]

private theorem reservedFastArm_eq_draw (r : Record rate) (cell : ActualLiveSourceCell r) :
    (reservedFastArm r cell).val =
      (SnapshotRecordingKernel.fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
        cell.selected.view.payload.anchor
        (sourceWeights cell.selected.view.payload cell.selected.view.complementWeights)
        cell.selected.view.payload.anchor_pos
        (sourceWeights_pos _ _ _ _ cell.choiceInputsValid)
        (sourceWeights_lower _ _ _ _ cell.choiceInputsValid)
        (sourceWeights_upper _ _ _ _ cell.choiceInputsValid)
        cell.selected.view.payload.assignment (r.input.row.2 r.input.time).1).val := by
  let W := sourceWeights cell.selected.view.payload cell.selected.view.complementWeights
  have hw : cell.selected.view.complementWeights = fun j => W j.val := by
    funext j
    dsimp only [W, sourceWeights]
    rw [dite_eq_right (Finset.mem_sdiff.mp j.property).2]
  have hl := FastComplementLocality.sampleLocalFast_eq_of_weights_eq p rate.eta.property rate.sourceCap
    cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos cell.selected.view.payload.slowSet
    cell.selected.view.complementWeights (fun j => W j.val)
    cell.choiceInputsValid.current_weight_pos (fun j => sourceWeights_pos _ _ _ _ cell.choiceInputsValid j.val)
    cell.choiceInputsValid.anchor_le_current (fun j => sourceWeights_lower _ _ _ _ cell.choiceInputsValid j.val)
    cell.choiceInputsValid.current_le_twice_anchor (fun j => sourceWeights_upper _ _ _ _ cell.choiceInputsValid j.val)
    hw (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast (r.input.row.2 r.input.time).1)
  have hc := FastComplementLocality.sampleLocalFast_eq_sampleFast p rate.eta.property rate.sourceCap
    cell.selected.view.payload.anchor W cell.selected.view.payload.anchor_pos
    (sourceWeights_pos _ _ _ _ cell.choiceInputsValid)
    (sourceWeights_lower _ _ _ _ cell.choiceInputsValid)
    (sourceWeights_upper _ _ _ _ cell.choiceInputsValid)
    cell.selected.view.payload.slowSet
    (ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast (r.input.row.2 r.input.time).1)
  have hset : SnapshotRecordingKernel.assignmentSlowSet p cell.selected.view.payload.assignment =
      cell.selected.view.payload.slowSet := by
    apply Subtype.ext
    exact cell.selected.view.payload.assignment_image
  unfold reservedFastArm SnapshotRecordingKernel.fastArmDraw
  rw [hset]
  exact congrArg Subtype.val (hl.trans hc)

private theorem fastDraw_view_congr
    (v w : ReferenceDownReception.ChoiceTimeView p rate.eta) (hv : w = v)
    (tv tw : Fin p.T)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid v.payload v.cutoff tv v.complementWeights)
    (hvalid' : CoordinatorLocalArmChoice.ChoiceInputsValid w.payload w.cutoff tw w.complementWeights)
    (x : ContinuousControlSlice.Slice p.m p.K) :
    (SnapshotRecordingKernel.fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
      w.payload.anchor (sourceWeights w.payload w.complementWeights) w.payload.anchor_pos
      (sourceWeights_pos _ _ _ _ hvalid') (sourceWeights_lower _ _ _ _ hvalid')
      (sourceWeights_upper _ _ _ _ hvalid') w.payload.assignment x).val =
    (SnapshotRecordingKernel.fastArmDraw p rate.eta.val rate.eta.property rate.sourceCap
      v.payload.anchor (sourceWeights v.payload v.complementWeights) v.payload.anchor_pos
      (sourceWeights_pos _ _ _ _ hvalid) (sourceWeights_lower _ _ _ _ hvalid)
      (sourceWeights_upper _ _ _ _ hvalid) v.payload.assignment x).val := by
  cases hv
  rfl

/-- Reserved FAST is transported with the actual retained slow set, rather
than by substituting a fresh or first-LIVE assignment. -/
theorem sourceAt_fast (z : LiveSource) (c : Control p) :
    (reservedFastArm
      (liveRecord (sourceAt rate rewards C_star C_h control0 q z c))
      (liveCell (sourceAt rate rewards C_star C_h control0 q z c))).val =
        (physicalPair rate rewards C_star C_h q z c).2 := by
  let r' := liveRecord (sourceAt rate rewards C_star C_h control0 q z c)
  let cell' := liveCell (sourceAt rate rewards C_star C_h control0 q z c)
  have hv : cell'.selected.view = (liveCell z).selected.view :=
    sourceAt_view rate rewards C_star C_h control0 q z c
  have hu : r'.input.row.2 r'.input.time = c := by
    rw [show r' = _ from sourceAt_record rate rewards C_star C_h control0 q z c, controlledRecord_control]
  rw [reservedFastArm_eq_draw]
  have h := fastDraw_view_congr rate
    (liveCell z).selected.view
    cell'.selected.view hv
    (liveRecord z).input.time r'.input.time
    (liveCell z).choiceInputsValid
    cell'.choiceInputsValid c.1
  dsimp only [r'] at hu
  simpa only [physicalPair, livePhysicalPair, hu] using h

/-- The full recorder/reserved-FAST/numerical-update data before the proposal.
This uses canonical queue states and the actual full numerical input. -/
def preProposalData (z : LiveSource) (c : Control p) :=
  let S := liveBefore z
  let v := physicalPair rate rewards C_star C_h q z c
  let input := inputForMarker rate rewards C_star C_h q z v.1
  (v, input, RecordedQueueRun.step (Q) S input,
    RecordedQueueRun.acceptedRecord (Q) S input,
    fun j => RecordedQueueRun.recordService (4 * (Q).n)
      (S.registers j) (RecordedQueueRun.acceptedRecord (Q) S input j))

/-- The physical prop scalar is unused by the entire actual pre-proposal data,
including all-arm queue update, enabled zero arrivals and service. -/
theorem preProposalData_replaceProposal (z : LiveSource)
    (c : Control p) (x : Scalar) :
    preProposalData rate rewards C_star C_h q z (replaceProposalScalar p c x) =
      preProposalData rate rewards C_star C_h q z c := by
  dsimp only [preProposalData]
  rw [physicalPair_replaceProposal]

/-- The complete canonical logical cell expressed using the fixed actual PRE,
retained old anchor and same-control physical pair. -/
def controlledCell (z : LiveSource)
    (c : Control p) (x : Scalar) : LogicalCell p rate :=
  let S := liveBefore z
  let cell := liveCell z
  let v := physicalPair rate rewards C_star C_h q z c
  let input := inputForMarker rate rewards C_star C_h q z v.1
  let proposed := !S.overflow && physicalProposalBit rate c
  { time := q
    physical := ReferenceActiveHorizonMeasurability.roundRecordCode
      (controlledRecord rate (liveRecord z) c)
    numerical := ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates input
    before := S
    after := RecordedQueueRun.step (Q) S input
    arrivals := RecordedQueueRun.acceptedRecord (Q) S input
    service := fun j => RecordedQueueRun.recordService (4 * (Q).n)
      (S.registers j) (RecordedQueueRun.acceptedRecord (Q) S input j)
    slowSet := if S.overflow then frozenSlowSet p else cell.selected.view.payload.slowSet
    fastArm := if S.overflow then frozenFastArm p else v.2
    proposal := proposed
    nextSlowSet := if S.overflow then frozenSlowSet p else
      if proposed then residualDraw rate S input cell.selected.view.payload.anchor
        cell.selected.view.payload.anchor_pos x else cell.selected.view.payload.slowSet }

/-- All-controls, all-auxiliary readout equality to the literal continuing
logical cell. Label zero and every other original auxiliary coordinate are unused. -/
theorem sourceAt_logicalCell (z : LiveSource)
    (a : Auxiliary p) (c : Control p) (x : Scalar × Scalar) :
    logicalCellAt (sourceAt rate rewards C_star C_h control0 q z c)
      (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a x) =
        controlledCell rate rewards C_star C_h q z c x.2 := by
  have ht := ReferencePostInvocationNoncallGeometry.continuingRecord_time rate rewards C_star C_h q
    (sourceAt rate rewards C_star C_h control0 q z c)
  have hp := sourceAt_proposal rate rewards C_star C_h control0 q z c
  have hf := sourceAt_fast rate rewards C_star C_h control0 q z c
  have hv := sourceAt_view rate rewards C_star C_h control0 q z c
  unfold ReferencePostInvocationNoncallGeometry.continuingLogicalCell appendLogicalCell controlledCell
  dsimp only
  rw [sourceAt_before, sourceAt_input, hp]
  simp only [hv, hf, ht, ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair, Function.update_self]
  simp only [sourceAt_record, ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates]

/-- The literal full logical-cell readout is Borel on the whole innovation
space, before projecting to the finite outcome. -/
theorem measurable_sourceAt_logicalCell
    (z : LiveSource) (a : Auxiliary p) :
    Measurable (fun y : Control p × (Scalar × Scalar) =>
      logicalCellAt
        (sourceAt rate rewards C_star C_h control0 q z y.1)
        (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2)) := by
  let f : Control p × (Scalar × Scalar) →
      LiveSource × Auxiliary p :=
    fun y => (sourceAt rate rewards C_star C_h control0 q z y.1,
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2)
  have hs : Measurable (fun y : Control p × (Scalar × Scalar) =>
      sourceAt rate rewards C_star C_h control0 q z y.1) :=
    (measurable_sourceAt rate rewards C_star C_h control0 q z).comp measurable_fst
  have ha : Measurable (fun y : Control p × (Scalar × Scalar) =>
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2) :=
    (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.measurable_fillAuxiliaryPair q).comp
      (measurable_const.prodMk measurable_snd)
  have hf : Measurable f := hs.prodMk ha
  have hg := ReferencePostInvocationPrefixLocality.measurable_continuingLogicalCell rate rewards C_star C_h q
  have hcomp := hg.comp hf
  simpa only [Function.comp_def, f] using hcomp

/-- The actual non-proposal pair and the deterministic same-control proposal
have their product law. Nonuse is proved above for the entire numerical update. -/
theorem physicalPair_proposal_law (z : LiveSource) :
    (ContinuousLearningRows.timeControlLaw p).map
      (fun c => (physicalPair rate rewards C_star C_h q z c, physicalProposalBit rate c)) =
        (nativePairLaw rate rewards C_star C_h q z).prod (proposalBitLaw rate) := by
  let zero : Scalar := ⟨0, by norm_num⟩
  let g : Unit × PropRestControl p → Option (Fin p.K) × Fin p.K := fun y =>
    physicalPair rate rewards C_star C_h q z ((proposalControlSplit p).symm (zero, y.2))
  have hg : Measurable g := (physicalPair_law rate rewards C_star C_h q z).1.comp
    ((proposalControlSplit p).symm.measurable.comp (measurable_const.prodMk measurable_snd))
  have hout : Measurable (fun c => (physicalPair rate rewards C_star C_h q z c, physicalProposalBit rate c)) :=
    (physicalPair_law rate rewards C_star C_h q z).1.prodMk (measurable_physicalProposalBit rate)
  have he (c : Control p) : (proposalControlSplit p).symm (zero, (proposalControlSplit p c).2) =
      replaceProposalScalar p c zero := by
    simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
      proposalControlSplit_symm_replace p zero (proposalControlSplit p c).1 (proposalControlSplit p c).2
  have hpoint : (fun y : Unit × Control p =>
      (g (y.1, (proposalControlSplit p y.2).2), physicalProposalBit rate y.2)) =
      (fun c => (physicalPair rate rewards C_star C_h q z c, physicalProposalBit rate c)) ∘ Prod.snd := by
    funext y
    dsimp only [g, Function.comp_apply]
    rw [he, physicalPair_replaceProposal]
  have h := proposalSplit_joint_pushforward (Measure.dirac ()) g hg rate
  rw [hpoint, ← Measure.map_map hout measurable_snd,
    (measurePreserving_snd (μ := Measure.dirac ()) (ν := ContinuousLearningRows.timeControlLaw p)).map_eq] at h
  have hm := congrArg (Measure.map (Prod.fst : (Option (Fin p.K) × Fin p.K) × Bool → _)) h
  rw [Measure.map_map measurable_fst hout,
    (measurePreserving_fst (μ := ((Measure.dirac ()).prod (proposalRestControlLaw p)).map g)
      (ν := proposalBitLaw rate)).map_eq] at hm
  change (ContinuousLearningRows.timeControlLaw p).map (physicalPair rate rewards C_star C_h q z) = _ at hm
  rw [← hm, (physicalPair_law rate rewards C_star C_h q z).2] at h
  exact h

/-- Exactly the parent consumer's finite outcome carrier. -/
abbrev Outcome (p : ConstructorDimensions.Parameters) :=
  Unit ⊕ (Option (Fin p.K) × Fin p.K × Bool × SlowSet p)

local instance outcomeMeasurableSpace : MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscrete : DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩

/-- Effective finite coordinates; raw physical numerical records remain in
LogicalCell even on PRE-overflow continuation. -/
def cellOutcome (e : LogicalCell p rate) : Outcome p :=
  Sum.inr (if e.before.overflow then none else e.numerical.2.1,
    e.fastArm, e.proposal, e.nextSlowSet)

/-- The same actual source family and original auxiliary array. -/
def sourceOutcome (z : LiveSource) (a : Auxiliary p)
    (y : Control p × (Scalar × Scalar)) : Outcome p :=
  cellOutcome rate (logicalCellAt
    (sourceAt rate rewards C_star C_h control0 q z y.1)
    (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q a y.2))

/-- Fixed old-anchor residual at the actual PRE and marker-specific numerical
update. Its PMF retains all zero atoms. -/
def residualLaw (z : LiveSource) (i : Option (Fin p.K)) :=
  (RecordedSlowRefresh.residualPMF p (Q)
    (liveBefore z)
    (inputForMarker rate rewards C_star C_h q z i)
    (liveCell z).selected.view.payload.anchor
    (liveCell z).selected.view.payload.anchor_pos).toMeasure

/-- Native finite readout of correlated pair, physical proposal, and fresh
label-one scalar. There is no POST-clear gate. -/
def nativeOutcome (z : LiveSource)
    (y : ((Option (Fin p.K) × Fin p.K) × Bool) × Scalar) : Outcome p :=
  let S := liveBefore z
  let cell := liveCell z
  if S.overflow then Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) else
    Sum.inr (y.1.1.1, y.1.1.2, y.1.2,
      if y.1.2 then residualDraw rate S (inputForMarker rate rewards C_star C_h q z y.1.1.1)
        cell.selected.view.payload.anchor cell.selected.view.payload.anchor_pos y.2
      else cell.selected.view.payload.slowSet)

private theorem measurable_residual (z : LiveSource)
    (i : Option (Fin p.K)) :
    Measurable (residualDraw rate (liveBefore z)
      (inputForMarker rate rewards C_star C_h q z i)
      (liveCell z).selected.view.payload.anchor
      (liveCell z).selected.view.payload.anchor_pos) :=
  (measurable_residualDraw_of_measurable_residualMass rate _ _ _ _ id measurable_id
    (fun _ => measurable_const)).mono le_rfl le_top

theorem measurable_nativeOutcome (z : LiveSource) :
    Measurable (nativeOutcome rate rewards C_star C_h q z) := by
  apply measurable_from_prod_countable_right
  rintro ⟨⟨i, j⟩, B⟩
  by_cases ho : (liveBefore z).overflow = true
  · simp only [nativeOutcome, ho, ite_true]
    exact measurable_const
  · cases B
    · simp only [nativeOutcome, ho, Bool.false_eq_true, ite_false]
      exact measurable_const
    · simp only [nativeOutcome, ho, ite_true]
      exact (measurable_of_countable (fun V : SlowSet p =>
        (Sum.inr (i, j, true, V) : Outcome p))).comp (measurable_residual rate rewards C_star C_h q z i)

/-- Literal readout identity, simultaneously for every whole control and both
auxiliary labels of the original array. -/
theorem sourceOutcome_eq_native (z : LiveSource)
    (a : Auxiliary p) (c : Control p) (x : Scalar × Scalar) :
    sourceOutcome rate rewards C_star C_h control0 q z a (c, x) =
      nativeOutcome rate rewards C_star C_h q z
        ((physicalPair rate rewards C_star C_h q z c, physicalProposalBit rate c), x.2) := by
  rw [sourceOutcome, sourceAt_logicalCell]
  cases ho : (liveBefore z).overflow <;>
    simp only [cellOutcome, controlledCell, nativeOutcome, ho, Bool.not_false, Bool.not_true,
      Bool.true_and, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
      ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates, inputForMarker]

/-- The prescribed native law, built from the correlated pair law and the
separate proposal and residual coordinates, rather than an outcome fibre. -/
def nativeLaw (z : LiveSource) : Measure (Outcome p) :=
  (((nativePairLaw rate rewards C_star C_h q z).prod (proposalBitLaw rate)).prod
    ContinuousControlSlice.scalarLaw).map (nativeOutcome rate rewards C_star C_h q z)

/-- Complete whole-control / two-auxiliary-label law at an actual continuing
LIVE source. All current physical and numerical premise producers are internal. -/
theorem sourceOutcome_law (z : LiveSource) (a : Auxiliary p) :
    Measurable (sourceOutcome rate rewards C_star C_h control0 q z a) ∧
    ((ContinuousLearningRows.timeControlLaw p).prod
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
        (sourceOutcome rate rewards C_star C_h control0 q z a) =
          nativeLaw rate rewards C_star C_h q z := by
  let f := fun c => (physicalPair rate rewards C_star C_h q z c, physicalProposalBit rate c)
  have hf : Measurable f := (physicalPair_law rate rewards C_star C_h q z).1.prodMk
    (measurable_physicalProposalBit rate)
  let read := fun y : Control p × (Scalar × Scalar) => (f y.1, y.2.2)
  have hread : Measurable read := (hf.comp measurable_fst).prodMk measurable_snd.snd
  have hmap : ((ContinuousLearningRows.timeControlLaw p).prod
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map read =
      ((nativePairLaw rate rewards C_star C_h q z).prod (proposalBitLaw rate)).prod
        ContinuousControlSlice.scalarLaw := by
    have h := Measure.map_prod_map (ContinuousLearningRows.timeControlLaw p)
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw) hf measurable_snd
    rw [(physicalPair_proposal_law rate rewards C_star C_h q z),
      (measurePreserving_snd (μ := ContinuousControlSlice.scalarLaw)
        (ν := ContinuousControlSlice.scalarLaw)).map_eq] at h
    exact h.symm
  have he : sourceOutcome rate rewards C_star C_h control0 q z a =
      nativeOutcome rate rewards C_star C_h q z ∘ read := by
    funext y
    exact sourceOutcome_eq_native rate rewards C_star C_h control0 q z a y.1 y.2
  have hn := measurable_nativeOutcome rate rewards C_star C_h q z
  refine ⟨he ▸ hn.comp hread, ?_⟩
  rw [he, ← Measure.map_map hn hread, hmap]
  rfl

instance nativePairLaw_probability (z : LiveSource) :
    IsProbabilityMeasure (nativePairLaw rate rewards C_star C_h q z) := by
  rw [← (physicalPair_law rate rewards C_star C_h q z).2]
  exact (Measure.isProbabilityMeasure_map_iff
    (physicalPair_law rate rewards C_star C_h q z).1.aemeasurable).mpr inferInstance

instance nativeLaw_probability (z : LiveSource) :
    IsProbabilityMeasure (nativeLaw rate rewards C_star C_h q z) := by
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_nativeOutcome rate rewards C_star C_h q z).aemeasurable).mpr inferInstance

private theorem proposalBitLaw_false :
    proposalBitLaw rate {false} = ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) := by
  have he : ({false} : Set Bool) = {true}ᶜ := by
    ext B
    cases B <;> simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Bool.false_eq_true,
      Bool.true_eq_false, not_false_eq_true, not_true_eq_false]
  rw [he, prob_compl_eq_one_sub (measurableSet_singleton true), proposalBitLaw_true,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (physicalProposalThreshold_bounds rate).1.le]
  rfl

private theorem residual_fibre_mass (z : LiveSource)
    (i : Option (Fin p.K)) (V : SlowSet p) :
    ContinuousControlSlice.scalarLaw {x | residualDraw rate
      (liveBefore z) (inputForMarker rate rewards C_star C_h q z i)
      (liveCell z).selected.view.payload.anchor
      (liveCell z).selected.view.payload.anchor_pos x = V} =
      residualLaw rate rewards C_star C_h q z i {V} := by
  let S := liveBefore z
  let input := inputForMarker rate rewards C_star C_h q z i
  let P := (liveCell z).selected.view.payload
  let masses := fun k => RecordedSlowRefresh.residualMass p
    (Q) S input P.anchor P.anchor_pos (slowSetEnumeration p k)
  have hsum : ∑ k, masses k = 1 := by
    dsimp only [masses]
    rw [Equiv.sum_comp]
    exact RecordedSlowRefresh.residualMass_sum_eq_one p _ _ _ _ _
  have hfibre : {x | residualDraw rate S input P.anchor P.anchor_pos x = V} =
      ContinuousCategorical.sample (slowSet_card_pos p) masses hsum ⁻¹' {(slowSetEnumeration p).symm V} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, residualDraw, masses]
    exact ((slowSetEnumeration p).eq_symm_apply).symm
  change ContinuousControlSlice.scalarLaw {x | residualDraw rate S input P.anchor P.anchor_pos x = V} = _
  rw [hfibre, residualLaw, PMF.toMeasure_apply_singleton _ V (measurableSet_singleton V),
    RecordedSlowRefresh.residualPMF_apply]
  rw [PublicDiscreteDraws.ContinuousControlSlice.scalarLaw_eq_categorical_uniform]
  simpa only [Equiv.apply_symm_apply] using
    ContinuousCategorical.uniform_sample_singleton (slowSet_card_pos p)
      (fun k => RecordedSlowRefresh.residualMass_nonneg p _ _ _ _ _ (slowSetEnumeration p k))
      hsum ((slowSetEnumeration p).symm V)

/-- The precise native clear-PRE atom formula. `J(i,j)` is the correlated
pair mass above; the same marker's complete numerical input defines rho_i.
All i, j, B, V are retained, including bottom markers and zero/null atoms. -/
theorem nativeLaw_atom_clear (z : LiveSource)
    (hpre : (liveBefore z).overflow = false)
    (i : Option (Fin p.K)) (j : Fin p.K) (B : Bool) (V : SlowSet p) :
    nativeLaw rate rewards C_star C_h q z {Sum.inr (i, j, B, V)} =
      nativePairLaw rate rewards C_star C_h q z {(i, j)} *
        (if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
          residualLaw rate rewards C_star C_h q z i {V}
        else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
          if V = (liveCell z).selected.view.payload.slowSet then 1 else 0) := by
  let draw := residualDraw rate (liveBefore z)
    (inputForMarker rate rewards C_star C_h q z i)
    (liveCell z).selected.view.payload.anchor
    (liveCell z).selected.view.payload.anchor_pos
  let U := (liveCell z).selected.view.payload.slowSet
  have he : nativeOutcome rate rewards C_star C_h q z ⁻¹' {Sum.inr (i, j, B, V)} =
      {((i, j), B)} ×ˢ {x | (if B then draw x else U) = V} := by
    ext y
    rcases y with ⟨⟨⟨i', j'⟩, B'⟩, x⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq,
      nativeOutcome, hpre, Bool.false_eq_true, ite_false, Sum.inr.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨hi, hj, hB, hV⟩
      subst i'
      subst j'
      subst B'
      exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, hV⟩
    · rintro ⟨⟨⟨hi, hj⟩, hB⟩, hV⟩
      subst i'
      subst j'
      subst B'
      exact ⟨rfl, rfl, rfl, hV⟩
  have hp : ((nativePairLaw rate rewards C_star C_h q z).prod (proposalBitLaw rate)) {((i, j), B)} =
      nativePairLaw rate rewards C_star C_h q z {(i, j)} * proposalBitLaw rate {B} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [nativeLaw, Measure.map_apply (measurable_nativeOutcome rate rewards C_star C_h q z)
    (measurableSet_singleton _), he, Measure.prod_prod, hp, mul_assoc]
  cases B
  · rw [proposalBitLaw_false]
    simp only [Bool.false_eq_true, ite_false]
    change _ = nativePairLaw rate rewards C_star C_h q z {(i, j)} *
      (ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) * if V = U then 1 else 0)
    by_cases hV : V = U
    · have hset : {x : Scalar | U = V} = Set.univ := by
        ext x
        simp only [hV, Set.mem_ofPred_eq, Set.mem_univ]
      rw [hset, measure_univ, ite_eq_left hV]
    · have hset : {x : Scalar | U = V} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact Ne.symm hV
      rw [hset, measure_empty, ite_eq_right hV]
  · rw [proposalBitLaw_true]
    simp only [ite_true]
    have hm := residual_fibre_mass rate rewards C_star C_h q z i V
    change ContinuousControlSlice.scalarLaw {x | draw x = V} = _ at hm
    rw [hm]
    rfl

/-- PRE overflow has its unique effective frozen outcome. The literal
physical numerical record is still given by sourceAt_logicalCell. -/
theorem nativeLaw_overflow (z : LiveSource)
    (hpre : (liveBefore z).overflow = true) :
    nativeLaw rate rewards C_star C_h q z =
      Measure.dirac (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p) := by
  have he : nativeOutcome rate rewards C_star C_h q z =
      fun _ => (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p) := by
    funext y
    simp only [nativeOutcome, hpre, ite_true]
  rw [nativeLaw, he, Measure.map_const, measure_univ, one_smul]

/-- The LIVE branch has no absent-cell atom, including after PRE overflow. -/
theorem nativeLaw_absent (z : LiveSource) :
    nativeLaw rate rewards C_star C_h q z {Sum.inl ()} = 0 := by
  have he : nativeOutcome rate rewards C_star C_h q z ⁻¹' {Sum.inl ()} = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, nativeOutcome]
    split <;> simp only [Sum.inr_ne_inl]
  rw [nativeLaw, Measure.map_apply (measurable_nativeOutcome rate rewards C_star C_h q z)
    (measurableSet_singleton _), he, measure_empty]

/-- Source-root coefficient theorem for the parent same-ID assembly. Its
only logical condition is the actual PRE-clear branch being characterized. -/
theorem sourceOutcome_atom_clear (z : LiveSource)
    (a : Auxiliary p)
    (hpre : (liveBefore z).overflow = false)
    (i : Option (Fin p.K)) (j : Fin p.K) (B : Bool) (V : SlowSet p) :
    (((ContinuousLearningRows.timeControlLaw p).prod
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
      (sourceOutcome rate rewards C_star C_h control0 q z a)) {Sum.inr (i, j, B, V)} =
      nativePairLaw rate rewards C_star C_h q z {(i, j)} *
        (if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
          residualLaw rate rewards C_star C_h q z i {V}
        else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
          if V = (liveCell z).selected.view.payload.slowSet then 1 else 0) := by
  rw [(sourceOutcome_law rate rewards C_star C_h control0 q z a).2]
  exact nativeLaw_atom_clear rate rewards C_star C_h q z hpre i j B V

/-- The same source-root law covers frozen continuation without discarding
its ongoing physical record or numerical calendar date. -/
theorem sourceOutcome_overflow (z : LiveSource)
    (a : Auxiliary p)
    (hpre : (liveBefore z).overflow = true) :
    ((ContinuousLearningRows.timeControlLaw p).prod
      (ContinuousControlSlice.scalarLaw.prod ContinuousControlSlice.scalarLaw)).map
      (sourceOutcome rate rewards C_star C_h control0 q z a) =
        Measure.dirac (Sum.inr (none, frozenFastArm p, false, frozenSlowSet p) : Outcome p) := by
  rw [(sourceOutcome_law rate rewards C_star C_h control0 q z a).2]
  exact nativeLaw_overflow rate rewards C_star C_h q z hpre

end Bandits.Support.ReferencePostInvocationLiveNativeLaw

end
