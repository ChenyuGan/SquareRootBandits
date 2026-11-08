/-
Copyright (c) 2026 Bandits formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedCalendarFirstLiveSourceSupport

/-!
# First-LIVE episode transition on the original erased prefix experiment

Sources: ZIP4 `04_slow_fast_learner.tex:329-390` and
`06_interruptions.tex:391-426`.

The original full source, private arrays, strict estimate history and actual
incoming set remain joint. The retained joint-test identity covers birth and
both positive-offset original phases on the original erased-prefix experiment,
raw and every fixed-ID law. The old birth set stays inside the whole assignment
vector integral, with the same complete UPDATE residual. No manuscript or
main-regret closure is asserted. Independent review and sealing remain open.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical BigOperators
open Bandits.Support ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstLiveChronologicalPrefixMeasurability
open ReferenceGeneratedCalendarEpisodeHistoryTransport
open ReferenceGeneratedCalendarEpisodeTransitionCore
open ReferenceGeneratedCalendarFirstLiveSourceSupport
open ReferenceGeneratedCalendarPrefixProposalErasure
open ReferenceGeneratedCalendarEpisodePrefixRecombination
open ReferenceFirstCollectionLogicalPrefixExtension
open ReferenceFirstLiveCalendarMarkedTransition
open ReferenceGeneratedCalendarEpisodeSlowLaw
open ReferenceOriginalCalendarEpisodeChronology
open RecordedQuantizedEstimateReplay
open ContinuousControlSlice (Scalar scalarLaw)

namespace Bandits.Support.ReferenceGeneratedCalendarFirstLiveEpisodeTransition

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance optionMeasurableSpace {A : Type*} [MeasurableSpace A] :
    MeasurableSpace (Option A) := LaterAssignmentStartMeasurability.optionMeasurableSpace

local instance slowSetMeasurableSpace : MeasurableSpace (SlowSet p) :=
  Subtype.instMeasurableSpace

attribute [local instance] ReferenceRankInstallationPostUpdateProposalLaw.optionSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.listMeasurableSingleton
  ReferenceRankInstallationPostUpdateProposalLaw.sumMeasurableSingleton

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Obs" => ReferenceFirstLiveCalendarMarkedTransition.Observation p rate
local notation "Innovation" => ContinuousLearningRows.TimeControl p × Scalar
local notation "Aux" => ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p
local notation "Lambda" => ReferenceExhaustiveGeneratedCalendarSourceLaw.terminalLaw
  rate rewards C_star C_h control0
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate


/- Local notation abbreviates the accepted literal expressions only. -/
local notation "S₀" => RecordedQueueRun.initialState p.K
local notation "liveWindow" => ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
local notation "liveCells" => ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h
local notation "nativePRE" => ReferencePostInvocationNoncallGeometry.prefixNumerical rate rewards C_star C_h
local notation "srcHistory" => prefixSourceHistory rate control0
local notation "srcJoint" => prefixSourceJoint rate rewards C_star C_h control0
local notation "sourceReplay" => sourceEpisodeReplay rate rewards C_star C_h
local notation "srcTest" => retainedSourceTest rate rewards C_star C_h
local notation "kerTest" => retainedKernelTest rate rewards C_star C_h
local notation "commonTest" => episodeTransitionTest rate rewards C_star C_h
local notation "episodeInput" => episodeRoundInput rate rewards
local notation "episodeNext" => episodeNextLaw rate rewards
local notation "LiveSource" => LiveCalendarSource rate rewards C_star C_h
local notation "liveEntry" => liveCalendarEntry rate rewards C_star C_h
local notation "liveIndex" => liveCalendarIndex rate rewards C_star C_h
local notation "srcMark" => prefixCurrentMark rate rewards C_star C_h
local notation "insertControl" => ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p
local notation "srcPrefix" => ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0


include control0 in
/-- Every positive-offset first-LIVE source is an actual continuing-LIVE
source. Empty pending and nonempty pending are both retained. -/
def positiveLiveSource (q : Fin p.T)
    (z : LiveSource q)
    (hpos : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h < q.val) :
    ReferencePostInvocationNoncallGeometry.ContinuingLiveSource rate rewards C_star C_h q := ⟨z.val, by
  let k := liveIndex q z
  let W := liveWindow z.val
  let r := W[k.val]
  have hp : W <+: ReferenceCompletePhysicalHistory.completeSuffixRecords rate z.val rewards C_star C_h :=
    List.takeWhile_prefix _
  obtain ⟨hc, _, _⟩ := ReferenceLaterLiveNumericalReadout.source_record_prefix
    rate rewards C_star C_h z.val ⟨k.val, k.isLt.trans_le hp.length_le⟩
  have hs := ((currentCellGate_iff rate rewards C_star C_h q z.val).mp z.property).1
  let row := ActualInitializationPhysicalStep.selectedRowIndex p z.val
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  let z0 : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex row q start hs) :=
    ⟨z.val, rfl, hc, rfl⟩
  have hrecord : r = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h row q start hs control0 z0 :=
    ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveWindow_current
      rate rewards C_star C_h row q start hs control0 z0 k.isLt
  have hcontinuing := ReferenceFirstLiveSourcePhasePartition.source_positive_current_continuing
    rate rewards C_star C_h row q start hs control0 z0 (by dsimp only [start]; omega) k.isLt
  dsimp only at hcontinuing
  rw [← hrecord] at hcontinuing
  obtain ⟨regs, owned, base, d, hsStart, continuation, arm, hprep, _⟩ := hcontinuing
  have hincoming : ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
    cases hstate : r.input.state.coordinator with
    | live regs owned base => exact ⟨regs, owned, base, rfl⟩
    | first =>
        simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate, CoordinatorRoundDispatch.dispatch] at hprep
        cases hprep
    | collection payload ledger saved =>
        simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate] at hprep
        split at hprep
        · simp only [CoordinatorRoundDispatch.dispatch] at hprep
          cases hprep
        · cases hprep
    | dagger =>
        simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
          hstate] at hprep
        cases hprep
  refine ⟨r, liveCalendar_actual_record rate rewards C_star C_h q z, hincoming, ?_⟩
  rw [wholeLiveCell_readout rate rewards C_star C_h z.val k]
  rfl⟩


private theorem appendLogicalCell_congr {r t : Record rate} (hrt : r = t)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell t)
    (S : RecordedQueueRun.RunState p.K) (aux : Aux) :
    appendLogicalCell r a S aux = appendLogicalCell t b S aux := by
  cases hrt
  rw [actualLiveSourceCell_unique r a b]

/-- The first-LIVE and continuing-LIVE constructors agree as complete cells.
The equality keeps the original physical record, rates, reward row, numerical
PRE/UPDATE, arrivals, service, old set, physical proposal and residual draw. -/
theorem liveCalendarEntry_eq_continuing (q : Fin p.T)
    (z : LiveSource q)
    (hpos : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h < q.val)
    (a : Aux) :
    liveEntry q z a =
      ReferencePostInvocationNoncallGeometry.continuingLogicalCell rate rewards C_star C_h q
        (positiveLiveSource rate rewards C_star C_h control0 q z hpos) a := by
  let native := positiveLiveSource rate rewards C_star C_h control0 q z hpos
  let k := liveIndex q z
  let r := (liveWindow z.val)[k.val]
  have hr : ReferencePostInvocationNoncallGeometry.continuingRecord rate rewards C_star C_h q native = r :=
    Option.some.inj ((ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec
      rate rewards C_star C_h q native).1.symm.trans
        (liveCalendar_actual_record rate rewards C_star C_h q z))
  have hb : ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native =
      (liveEntry q z a).before :=
    Option.some.inj ((ReferencePostInvocationPrefixLocality.continuingBefore_spec
      rate rewards C_star C_h q native).symm.trans
        (liveCalendarEntry_prefixNumerical rate rewards C_star C_h q z a))
  have he := firstLiveChronologicalPrefix_get rate rewards C_star C_h z.val a k
  change liveEntry q z a = _ at he
  rw [he] at hb
  change ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native =
    RecordedQueueRun.run Q ((liveCells z.val).take k.val) at hb
  change _ = ReferencePostInvocationNoncallGeometry.continuingLogicalCell rate rewards C_star C_h q native a
  rw [he]
  unfold ReferencePostInvocationNoncallGeometry.continuingLogicalCell
  rw [hb]
  exact appendLogicalCell_congr rate hr.symm _ _ _ a


/-- The literal original history and current mark pull back to the actual
continuing native source on every positive first-LIVE offset. The original
label-zero array is retained and only its current entry is refilled. -/
theorem prefixSourceJoint_positive_native (s q : Fin p.T) (o : Obs)
    (hg : currentCellGate rate rewards C_star C_h q o.1 = true)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (hpos : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h < q.val)
    (x : Scalar) (ux : Innovation) :
    let z : LiveSource q := ⟨o.1, hg⟩
    let native := positiveLiveSource rate rewards C_star C_h control0 q z hpos
    let e := ReferencePostInvocationNoncallGeometry.continuingLogicalCell rate rewards C_star C_h q
      (ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q native ux.1)
      (ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q
        (roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) (x, ux.2))
    srcJoint s q (refillProposal q (o, x), ux) =
      (srcHistory s q o, (sourceOptionalEstimate rate (some e), some e)) := by
  intro z native e
  let zu : LiveSource q :=
    ⟨insertControl q o.1 ux.1,
      (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 ux.1).trans hg⟩
  have hposu : ReferenceCompletePhysicalHistory.physicalStart rate zu.val rewards C_star C_h < q.val := by
    rw [liveCalendar_start_replace_current rate rewards C_star C_h control0 q z ux.1]
    exact hpos
  have hn : positiveLiveSource rate rewards C_star C_h control0 q zu hposu =
      ReferencePostInvocationLiveNativeLaw.sourceAt rate rewards C_star C_h control0 q native ux.1 :=
    Subtype.ext rfl
  have ha : roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2) =
      ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair q
        (roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) (x, ux.2) := by
    funext i
    rcases i with ⟨t, l⟩
    fin_cases l <;> by_cases ht : t = q <;>
      simp [roundAuxiliary, refillProposal,
        ReferenceFirstNextLiftFutureAuxiliaryPairLaw.fillAuxiliaryPair, ht]
  have hm := prefixCurrentMark_live rate rewards C_star C_h control0 q o hg hpast x ux
  change srcMark q (refillProposal q (o, x), ux) =
    some (liveEntry q zu _) at hm
  rw [liveCalendarEntry_eq_continuing rate rewards C_star C_h control0 q zu hposu, hn, ha] at hm
  unfold prefixSourceJoint
  rw [hm, prefixSourceHistory_refillProposal]


private theorem actualCell_anchor_congr {r t : Record rate} (hrt : r = t)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell t) :
    a.selected.view.payload.anchor = b.selected.view.payload.anchor := by
  cases hrt
  rw [actualLiveSourceCell_unique r a b]

private theorem actualCell_input_congr {r t : Record rate} (hrt : r = t)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell t) : a.input = b.input := by
  cases hrt
  rw [actualLiveSourceCell_unique r a b]

private theorem roundInput_ext {c d : RecordedQueueRun.RoundInput p.K}
    (he : c.enabled = d.enabled) (hi : c.recordedArm = d.recordedArm)
    (hw : c.reward = d.reward) (hr : c.rate = d.rate) : c = d := by
  cases c
  cases d
  cases he
  cases hi
  cases hw
  cases hr
  rfl

/-- On the original erased experiment, the positive first-LIVE source's
complete native PRE, incoming clear flag, strict anchor and every full
marker-specific input are produced together. Both pending branches use this
same actual source; no numerical or seed identity is supplied. -/
theorem ae_erased_positive_native_parameters
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      ∀ (hg : currentCellGate rate rewards C_star C_h q o.1 = true),
        noCallAt rate rewards C_star C_h q o.1 →
        (srcHistory s q o).1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
        srcHistory s q o ∈ sourceHistoryRetained rate rewards C_star C_h s q →
        ∀ (hpos : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h < q.val),
        let z : LiveSource q := ⟨o.1, hg⟩
        let native := positiveLiveSource rate rewards C_star C_h control0 q z hpos
        let S := ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native
        let cell := ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q native
        sourceReplay s q
            (srcHistory s q o) = some S ∧
          S.overflow = false ∧
          cell.selected.view.payload.anchor = RecordedQueueRun.scoreWeight Q (S₀) ∧
          ∀ i : Option (Fin p.K),
            ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q native i =
              episodeInput q (S₀) i := by
  filter_upwards [ae_erased_prefix_live_replay rate rewards C_star C_h control0 ids s q hsq] with o ho
  intro hg hn hs hr hpos z native S cell
  obtain ⟨_, hprefix⟩ := ho.2.2 hg hn hs hr
  have hrep : sourceReplay s q
      (srcHistory s q o) = some S :=
    hprefix.symm.trans (ReferencePostInvocationPrefixLocality.continuingBefore_spec
      rate rewards C_star C_h q native)
  have hclear : S.overflow = false := by
    simpa only [hrep, Option.any_some, Bool.not_eq_true'] using hr.2.2
  have hno : NoCallBefore rate rewards C_star C_h q.succ o.1 :=
    (noCallBefore_succ rate rewards C_star C_h q o.1).mpr ⟨ho.2.1, hn⟩
  have hs0 : o.1 ∈ sourceStartEvent rate rewards C_star C_h s :=
    (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 s o.1).mpr hs
  have hc : (nativePRE q.castSucc z.val).any (fun R => !R.overflow) = true := by
    rw [hprefix, hrep, Option.any_some, hclear]
    rfl
  have ha := (liveCalendar_native_anchor rate rewards C_star C_h control0 s q hsq hr.2.1 z hno hs0 hc).2
  let k := liveIndex q z
  have hrecord : ReferencePostInvocationNoncallGeometry.continuingRecord rate rewards C_star C_h q native =
      (liveWindow z.val)[k.val] :=
    Option.some.inj ((ReferencePostInvocationNoncallGeometry.continuingSourceCell_spec
      rate rewards C_star C_h q native).1.symm.trans
        (liveCalendar_actual_record rate rewards C_star C_h q z))
  have hanchor : cell.selected.view.payload.anchor =
      RecordedQueueRun.scoreWeight Q (S₀) :=
    (actualCell_anchor_congr rate hrecord cell
      (wholeLiveCell rate rewards C_star C_h z.val _ (List.getElem_mem k.isLt))).trans ha
  refine ⟨hrep, hclear, hanchor, ?_⟩
  intro i
  have hw : cell.input.reward = fun j => ((rewards q j).val : ℝ) / (D p : ℝ) :=
    ReferenceGeneratedCalendarQuantizedRoundKernel.liveRound_reward rate rewards C_star C_h q native i
  apply roundInput_ext
  · exact cell.enabled
  · rfl
  · exact hw
  · change cell.input.rate = _
    rw [cell.input_eq]
    change CanonicalRecordingRates.xi p rate.eta.val cell.selected.view.payload.anchor =
      CanonicalRecordingRates.xi p rate.eta.val (RecordedQueueRun.scoreWeight Q (S₀))
    rw [hanchor]


private theorem positive_optional_test (s q : Fin p.T) (o : Obs)
    (hg : currentCellGate rate rewards C_star C_h q o.1 = true)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (hpos : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h < q.val)
    (hclear : (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q
      (positiveLiveSource rate rewards C_star C_h control0 q ⟨o.1, hg⟩ hpos)).overflow = false)
    (F : TransitionData rate s q → ℝ≥0∞) (x : Scalar) (ux : Innovation) :
    let native := positiveLiveSource rate rewards C_star C_h control0 q ⟨o.1, hg⟩ hpos
    let S := ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native
    let U := (ReferencePostInvocationNoncallGeometry.continuingSourceCell
      rate rewards C_star C_h q native).selected.view.payload.slowSet
    optionalTransitionTest rate s q F
      (srcJoint s q (refillProposal q (o, x), ux)) =
    ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest rate S
      (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q native)
      (fun y B V => F (srcHistory s q o, (U, (y, (B, V))))) 0
      (ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q native
        (roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) (ux.1, (x, ux.2))) := by
  intro native S U
  change (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native).overflow = false at hclear
  rw [prefixSourceJoint_positive_native rate rewards C_star C_h control0 s q o hg hpast hpos]
  rw [ReferencePostInvocationLiveNativeLaw.sourceAt_logicalCell]
  let e := ReferencePostInvocationLiveNativeLaw.controlledCell rate rewards C_star C_h q native ux.1 ux.2
  let c := ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q native
    (ReferencePostInvocationLiveNativeLaw.physicalPair rate rewards C_star C_h q native ux.1).1
  have hestimate : sourceOptionalEstimate rate (some e) = RecordedRoundMoments.rawEstimate Q S c := by
    funext i
    exact sourceCellEstimate_eq_rawEstimate rate e c rfl i
  change F (srcHistory s q o,
    (e.slowSet, (sourceOptionalEstimate rate (some e), (e.proposal, e.nextSlowSet)))) = _
  rw [hestimate, ReferencePostInvocationLiveNativeLaw.sourceOutcome_eq_native]
  simp only [ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest,
    ReferencePostInvocationLiveNativeLaw.nativeOutcome, ReferencePostInvocationLiveNativeLaw.controlledCell,
    e, S, U, c, hclear, Bool.false_eq_true, ite_false, Bool.not_false, Bool.true_and, Sum.elim_inr]

private theorem anchorRates_congr (w v : Fin p.K → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (h : w = v) :
    ReferenceGeneratedCalendarQuantizedRoundKernel.anchorRates rate w hw =
      ReferenceGeneratedCalendarQuantizedRoundKernel.anchorRates rate v hv := by
  cases h
  rfl

private theorem residualPMF_congr (S : RecordedQueueRun.RunState p.K)
    (c d : RecordedQueueRun.RoundInput p.K) (hcd : c = d)
    (w v : Fin p.K → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) (hwv : w = v) :
    RecordedSlowRefresh.residualPMF p Q S c w hw = RecordedSlowRefresh.residualPMF p Q S d v hv := by
  cases hcd
  cases hwv
  rfl

private theorem live_native_sum_eq_episode (q : Fin p.T)
    (z : ReferencePostInvocationNoncallGeometry.ContinuingLiveSource rate rewards C_star C_h q)
    (A : RecordedQueueRun.RunState p.K)
    (hclear : (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q z).overflow = false)
    (ha : (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor =
      RecordedQueueRun.scoreWeight Q A)
    (hi : ∀ i, ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i =
      episodeInput q A i)
    (f : Estimate p → Bool → SlowSet p → ℝ≥0∞) :
    (∑ i : Option (Fin p.K), ∑ B : Bool, ∑ V : SlowSet p,
      f (RecordedRoundMoments.rawEstimate Q
        (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q z)
        (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q z i)) B V *
        (RecordedRoundMoments.recordingOutcomePMF
          (ReferenceGeneratedCalendarQuantizedRoundKernel.anchorRates rate
            (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor
            (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor_pos) i *
          (if B then ENNReal.ofReal (4 * (p.m : ℝ) * rate.eta.val) *
              ReferencePostInvocationLiveNativeLaw.residualLaw rate rewards C_star C_h q z i {V}
           else ENNReal.ofReal (1 - 4 * (p.m : ℝ) * rate.eta.val) *
             if V = (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet
             then 1 else 0))) =
      episodeRoundTest rate rewards q A
        (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q z)
        (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.slowSet f := by
  unfold episodeRoundTest
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro V _
  rw [hi i, anchorRates_congr rate _ _
    (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor_pos
    (RecordedSlowRefresh.scoreWeight_pos Q A) ha,
    ReferenceGeneratedCalendarQuantizedRoundKernel.proposalBitLaw_mass]
  have hres := residualPMF_congr rate
    (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q z)
    _ _ (hi i)
    (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor
    (RecordedQueueRun.scoreWeight Q A)
    (ReferencePostInvocationNoncallGeometry.continuingSourceCell rate rewards C_star C_h q z).selected.view.payload.anchor_pos
    (RecordedSlowRefresh.scoreWeight_pos Q A) ha
  have hx : RecordedRoundMoments.rawEstimate Q
      (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q z)
      (episodeInput q A i) =
      RecordedQuantizedEstimateReplay.sourceEstimate Q
        (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q z)
        (episodeInput q A i) := by
    funext j
    rfl
  rw [hx]
  cases B with
  | false =>
      by_cases hV : V = (ReferencePostInvocationNoncallGeometry.continuingSourceCell
          rate rewards C_star C_h q z).selected.view.payload.slowSet
      · subst V
        simp only [episodeNextLaw, hclear, Bool.false_eq_true, ite_false, Bool.not_false,
          Bool.true_and, Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, ite_true,
          Pi.one_apply, mul_one, mul_assoc]
        ac_rfl
      · simp only [episodeNextLaw, hclear, Bool.false_eq_true, ite_false, Bool.not_false,
          Bool.true_and, Measure.dirac_apply, Set.indicator_apply, Set.mem_singleton_iff, hV, Ne.symm hV,
          ite_false, mul_zero, zero_mul]
  | true =>
      simp only [episodeNextLaw, hclear, Bool.false_eq_true, ite_false, ite_true,
        Bool.not_false, Bool.true_and]
      unfold ReferencePostInvocationLiveNativeLaw.residualLaw
      rw [hres]
      simp only [PMF.toMeasure_apply_singleton, measurableSet_singleton]
      ac_rfl


omit rate rewards C_star C_h control0 in
private theorem scalar_innovation_lintegral
    (G : ContinuousLearningRows.TimeControl p × (Scalar × Scalar) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x, ∫⁻ ux, G (ux.1, (x, ux.2)) ∂calendarInnovationLaw p ∂scalarLaw) =
      ∫⁻ y, G y ∂(ContinuousLearningRows.timeControlLaw p).prod (scalarLaw.prod scalarLaw) := by
  have hfix (x : Scalar) : Measurable (fun ux : ContinuousLearningRows.TimeControl p × Scalar =>
      G (ux.1, (x, ux.2))) :=
    hG.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hswap : Measurable (fun v : (Scalar × ContinuousLearningRows.TimeControl p) × Scalar =>
      G (v.1.2, (v.1.1, v.2))) :=
    hG.comp (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd))
  calc
    _ = ∫⁻ x, ∫⁻ u, ∫⁻ r, G (u, (x, r)) ∂scalarLaw
        ∂ContinuousLearningRows.timeControlLaw p ∂scalarLaw := by
      apply lintegral_congr
      intro x
      exact lintegral_prod _ (hfix x).aemeasurable
    _ = ∫⁻ u, ∫⁻ x, ∫⁻ r, G (u, (x, r)) ∂scalarLaw ∂scalarLaw
        ∂ContinuousLearningRows.timeControlLaw p :=
      lintegral_lintegral_swap hswap.lintegral_prod_right'.aemeasurable
    _ = _ := by
      rw [lintegral_prod _ hG.aemeasurable]
      apply lintegral_congr
      intro u
      exact (lintegral_prod _ (hG.comp measurable_prodMk_left).aemeasurable).symm

/-- The actual positive-offset FIRST-LIVE retained joint test equals its
common episode kernel for almost every original erased observer, raw and
under every original fixed ID. Both empty and nonempty pending are included.
The whole current control, actual old set, recorder, physical proposal and
same UPDATE residual are consumed together. -/
theorem ae_erased_positive_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      currentCellGate rate rewards C_star C_h q o.1 = true →
      ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h < q.val →
      (∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
        srcTest s q F
          (srcJoint s q (refillProposal q (o, x), ux))
        else 0 ∂calendarInnovationLaw p ∂scalarLaw) =
      ∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
        kerTest s q F
          (srcJoint s q (refillProposal q (o, x), ux))
        else 0 ∂calendarInnovationLaw p ∂scalarLaw := by
  filter_upwards [ae_erased_prefix_live_replay rate rewards C_star C_h control0 ids s q hsq,
    ae_erased_positive_native_parameters rate rewards C_star C_h control0 ids s q hsq] with o ho hp
  intro hg hpos
  by_cases hn : noCallAt rate rewards C_star C_h q o.1
  · simp only [hn, ite_true]
    let h := srcHistory s q o
    let native := positiveLiveSource rate rewards C_star C_h control0 q ⟨o.1, hg⟩ hpos
    let S := ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native
    let U := (ReferencePostInvocationNoncallGeometry.continuingSourceCell
      rate rewards C_star C_h q native).selected.view.payload.slowSet
    have hgate (G : TransitionData rate s q → ℝ≥0∞) (x : Scalar) (ux : Innovation) :
        srcTest s q G
          (srcJoint s q (refillProposal q (o, x), ux)) =
        if h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
            h ∈ sourceHistoryRetained rate rewards C_star C_h s q then
          optionalTransitionTest rate s q G
            (srcJoint s q (refillProposal q (o, x), ux))
        else 0 := rfl
    unfold retainedKernelTest
    simp_rw [hgate]
    by_cases hret : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h ∈ sourceHistoryRetained rate rewards C_star C_h s q
    · simp only [hret, and_self, ite_true]
      obtain ⟨hrep, hclear, ha, hi⟩ := hp hg hn hret.1 hret.2 hpos
      change (ReferencePostInvocationNoncallGeometry.continuingBefore rate rewards C_star C_h q native).overflow = false at hclear
      have hseed := (ho.2.2 hg hn hret.1 hret.2).1
      let f := fun y B V => F (h, (U, (y, (B, V))))
      let a := roundAuxiliary q (o.2.1, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)
      let G := ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest rate S
        (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q native) f 0 ∘
          ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q native a
      have hG : Measurable G := by
        have hj : Measurable (fun y : ContinuousLearningRows.TimeControl p × (Scalar × Scalar) =>
            (refillProposal q (o, y.2.1), (y.1, y.2.2))) :=
          ((measurable_refillProposal q).comp (measurable_const.prodMk measurable_snd.fst)).prodMk
            (measurable_fst.prodMk measurable_snd.snd)
        have hm := (measurable_optionalTransitionTest rate s q F hF).comp
          ((measurable_prefixSourceJoint rate rewards C_star C_h control0 s q).comp hj)
        convert hm using 1
        funext y
        exact (positive_optional_test rate rewards C_star C_h control0 s q o hg ho.1 hpos hclear F y.2.1
          (y.1, y.2.2)).symm
      have hlocal : (∫⁻ x, ∫⁻ ux, optionalTransitionTest rate s q F
          (srcJoint s q (refillProposal q (o, x), ux))
          ∂calendarInnovationLaw p ∂scalarLaw) =
          commonTest s q F h U := by
        simp_rw [positive_optional_test rate rewards C_star C_h control0 s q o hg ho.1 hpos hclear F]
        change (∫⁻ x, ∫⁻ ux, G (ux.1, (x, ux.2)) ∂calendarInnovationLaw p ∂scalarLaw) = _
        rw [scalar_innovation_lintegral G hG]
        dsimp only [G, Function.comp_apply, S]
        rw [ReferenceGeneratedCalendarQuantizedRoundKernel.live_source_quantized_test
          rate rewards C_star C_h q control0 native a hclear f 0]
        rw [live_native_sum_eq_episode rate rewards C_star C_h q native
          (S₀) hclear ha hi]
        unfold episodeTransitionTest
        rw [hseed, hrep]
      rw [hlocal]
      have hk (x : Scalar) (ux : Innovation) :
          optionalTransitionTest rate s q (kernelLiftTest rate rewards C_star C_h s q F)
            (srcJoint s q (refillProposal q (o, x), ux)) =
          commonTest s q F h U := by
        rw [positive_optional_test rate rewards C_star C_h control0 s q o hg ho.1 hpos hclear]
        change ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest rate S
          (ReferencePostInvocationLiveNativeLaw.inputForMarker rate rewards C_star C_h q native)
          (fun _ _ _ => commonTest s q F h U) 0
          (ReferencePostInvocationLiveNativeLaw.sourceOutcome rate rewards C_star C_h control0 q native a
            (ux.1, (x, ux.2))) = _
        rw [ReferencePostInvocationLiveNativeLaw.sourceOutcome_eq_native]
        simp only [ReferenceGeneratedCalendarQuantizedRoundKernel.outcomeTest,
          ReferencePostInvocationLiveNativeLaw.nativeOutcome, hclear, Bool.false_eq_true, ite_false, Sum.elim_inr]
      simp_rw [hk]
      rw [lintegral_const, measure_univ, mul_one, lintegral_const, measure_univ, mul_one]
    · simp only [hret, ite_false, lintegral_zero]
  · simp only [hn, ite_false, lintegral_zero]



/-- Integrated retained source=kernel law on BOTH original positive-offset
FIRST-LIVE phases. This keeps every original source/private coordinate and
uses only the original raw or fixed-ID erased-prefix mass. -/
theorem beforePrefix_positiveLive_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ o, ∫⁻ x, ∫⁻ ux,
      if o.1 ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∨
          o.1 ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4 then
        if noCallAt rate rewards C_star C_h q o.1 then
          srcTest s q F
            (srcJoint s q (refillProposal q (o, x), ux))
        else 0 else 0 ∂calendarInnovationLaw p ∂scalarLaw
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map (eraseProposal q)) =
    ∫⁻ o, ∫⁻ x, ∫⁻ ux,
      if o.1 ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∨
          o.1 ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4 then
        if noCallAt rate rewards C_star C_h q o.1 then
          kerTest s q F
            (srcJoint s q (refillProposal q (o, x), ux))
        else 0 else 0 ∂calendarInnovationLaw p ∂scalarLaw
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map (eraseProposal q) := by
  apply lintegral_congr_ae
  filter_upwards [ae_erased_positive_retained_transition_test
    rate rewards C_star C_h control0 ids s q hsq F hF] with o ho
  by_cases hp : o.1 ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∨
      o.1 ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4
  · simp only [hp, ite_true]
    have hg := (currentCellGate_iff_sourcePhases rate rewards C_star C_h control0 q o.1).mpr
      (Or.inr hp)
    have hpos : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h < q.val := by
      rcases hp with h | h
      · exact h.2.1
      · exact h.2.1
    exact ho hg hpos
  · simp only [hp, ite_false, lintegral_zero]



omit control0 in
/-- The actual birth source in its original selected-row source stratum. -/
def birthLiveSource (q : Fin p.T)
    (z : LiveSource q)
    (hb : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = q.val) :
    ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h q
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) q) :=
  ⟨z.val, rfl, (liveCalendar_launchBy rate rewards C_star C_h q z).1, hb⟩

/-- The literal birth prefix joint readout retains the actual set sampled
from ALL current assignment coordinates. In particular its old set varies
with the current control; the baseline observer does not supply that set. -/
theorem prefixSourceJoint_birth_coordinates (s q : Fin p.T) (o : Obs)
    (hg : currentCellGate rate rewards C_star C_h q o.1 = true)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (hb : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val)
    (x : Scalar) (ux : Innovation) :
    let zu : LiveSource q :=
      ⟨insertControl q o.1 ux.1,
        (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 ux.1).trans hg⟩
    let e := liveEntry q zu
      (roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2))
    srcJoint s q (refillProposal q (o, x), ux) =
        (srcHistory s q o, (sourceOptionalEstimate rate (some e), some e)) ∧
      e.before = S₀ ∧
      e.slowSet = CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
        ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p ux.1).1) := by
  intro zu e
  have hbu : ReferenceCompletePhysicalHistory.physicalStart rate zu.val rewards C_star C_h = q.val :=
    (liveCalendar_start_replace_current rate rewards C_star C_h control0 q ⟨o.1, hg⟩ ux.1).trans hb
  let born := birthLiveSource rate rewards C_star C_h q zu hbu
  let row := ActualInitializationPhysicalStep.selectedRowIndex p zu.val
  let a := roundAuxiliary q ((refillProposal q (o, x)).2.1, ux.2)
  obtain ⟨d, htag, hbefore, hU, _⟩ :=
    ReferenceGeneratedCalendarPrefixLiveFast.actual_birth_tag_fields
      rate rewards C_star C_h control0 row q born a
  have hde : d = e := Sum.inr.inj (htag.symm.trans (currentCellTag_live rate rewards C_star C_h q zu a))
  subst d
  have hcoords : (ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
      rate rewards C_star C_h row q control0 born).2.1 =
      (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p ux.1).1 := by
    change (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p ((zu.val.1.2 row).2 q)).1 = _
    simp only [row, zu, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex,
      ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
  refine ⟨?_, hbefore, ?_⟩
  · unfold prefixSourceJoint
    rw [prefixCurrentMark_live rate rewards C_star C_h control0 q o hg hpast x ux,
      prefixSourceHistory_refillProposal]
  · rw [hU, ReferenceFirstLaunchOriginalAuxiliaryReward.actualFirstSlowSet_eq_canonical, hcoords]


/-- On the actual retained birth experiment, every whole current control
produces the canonical full input and SAME first-UPDATE residual. The source
start, strict seed, complete PRE and anchor are derived from original support.
The actual old set is the selected birth view's assignment image. -/
theorem ae_erased_birth_input_residual
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map
        (eraseProposal q),
      ∀ (hg : currentCellGate rate rewards C_star C_h q o.1 = true),
        ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val →
        noCallAt rate rewards C_star C_h q o.1 →
        (srcHistory s q o).1.1 ∈ sourceStartEvent rate rewards C_star C_h s →
        srcHistory s q o ∈ sourceHistoryRetained rate rewards C_star C_h s q →
        ∀ (u : ContinuousLearningRows.TimeControl p),
        let zu : LiveSource q :=
          ⟨insertControl q o.1 u,
            (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 u).trans hg⟩
        let k := liveIndex q zu
        let r := (liveWindow zu.val)[k.val]
        let cell := wholeLiveCell rate rewards C_star C_h zu.val r (List.getElem_mem k.isLt)
        cell.input = episodeInput q (S₀) cell.input.recordedArm ∧
          liveCalendarResidualLaw rate rewards C_star C_h q zu =
            episodeNext q (S₀) (S₀)
              cell.selected.view.payload.slowSet cell.input.recordedArm
              (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time) := by
  filter_upwards [ae_erased_prefix_live_replay rate rewards C_star C_h control0 ids s q hsq,
    ae_erased_birth_initialization rate rewards C_star C_h control0 ids s q hsq] with o ho hp
  intro hg hb hn hs hr u zu k r cell
  obtain ⟨hsq', _, _, _⟩ := hp hg hb hn hs hr
  subst s
  have hbu : ReferenceCompletePhysicalHistory.physicalStart rate zu.val rewards C_star C_h = q.val :=
    (liveCalendar_start_replace_current rate rewards C_star C_h control0 q ⟨o.1, hg⟩ u).trans hb
  have hno : NoCallBefore rate rewards C_star C_h q.succ o.1 :=
    (noCallBefore_succ rate rewards C_star C_h q o.1).mpr ⟨ho.2.1, hn⟩
  have hnou : NoCallBefore rate rewards C_star C_h q.succ zu.val := by
    apply (ReferenceGeneratedCalendarPrefixLiveFast.noCallThrough_sourcePrefix
      rate rewards C_star C_h control0 q zu.val).mpr
    change NoCallBefore rate rewards C_star C_h q.succ
      (srcPrefix q.val
        (insertControl q o.1 u))
    rw [ReferenceGeneratedCalendarPrefixLiveFast.sourcePrefix_replace_current control0]
    exact (ReferenceGeneratedCalendarPrefixLiveFast.noCallThrough_sourcePrefix
      rate rewards C_star C_h control0 q o.1).mp hno
  have hszu : zu.val ∈ sourceStartEvent rate rewards C_star C_h q := by
    apply (sourceStartEvent_sourcePrefix rate rewards C_star C_h control0 q zu.val).mpr
    change srcPrefix q.val
      (insertControl q o.1 u) ∈ _
    rw [ReferenceGeneratedCalendarPrefixLiveFast.sourcePrefix_replace_current control0]
    exact hs
  let a : Aux := ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
  have hbefore := ReferenceGeneratedCalendarPrefixLiveFast.currentCellTag_birth_before
    rate rewards C_star C_h q zu.val a (liveEntry q zu a)
    (currentCellTag_live rate rewards C_star C_h q zu a) hbu
  have hnum := liveCalendarEntry_prefixNumerical rate rewards C_star C_h q zu a
  rw [hbefore] at hnum
  have hc : (nativePRE q.castSucc zu.val).any (fun R => !R.overflow) = true := by
    rw [hnum]
    rfl
  have ha := (liveCalendar_native_anchor rate rewards C_star C_h control0 q q le_rfl hr.2.1 zu hnou hszu hc).2
  change cell.selected.view.payload.anchor = RecordedQueueRun.scoreWeight Q (S₀) at ha
  have hrecord := liveCalendar_actual_record rate rewards C_star C_h q zu
  have hi := ReferenceGeneratedCalendarQuantizedRoundKernel.actualSourceCell_input
    rate rewards C_star C_h q zu.val r cell hrecord
  have hepisode : episodeInput q (S₀) cell.input.recordedArm =
      ReferenceGeneratedCalendarQuantizedRoundKernel.installationRound
        rate rewards q cell.selected.view cell.input.recordedArm := by
    simp only [episodeRoundInput, ReferenceGeneratedCalendarQuantizedRoundKernel.installationRound, ha]
  refine ⟨hi.trans hepisode.symm, ?_⟩
  have hk : k.val = 0 := by
    dsimp only [k, liveCalendarIndex]
    rw [hbu, Nat.sub_self]
  have hstate : RecordedQueueRun.run Q ((liveCells zu.val).take k.val) = S₀ := by
    rw [hk, List.take_zero]
    rfl
  change logicalCellResidualLaw rate r cell (RecordedQueueRun.run Q
    ((liveCells zu.val).take k.val)) = _
  rw [hstate, ReferenceGeneratedCalendarQuantizedRoundKernel.actualSourceCell_nextLaw
    rate rewards C_star C_h q zu.val r cell hrecord (S₀)]
  exact (episodeNextLaw_eq_installationNextLaw rate rewards q
    (S₀) (S₀) cell.selected.view ha _ _).symm

private theorem birth_restore_source (row : Fin (M p)) (q : Fin p.T)
    (z : ReferenceFirstLiveBirthJointSourceLaw.BirthSource p rate rewards C_star C_h row q)
    (u : ContinuousLearningRows.TimeControl p) :
    (ReferenceFirstLaunchRecordingSourceLaw.restoreSource rate rewards C_star C_h row q control0
      ((ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates
        rate rewards C_star C_h row q control0 z).1, u)).val =
      insertControl q z.val u := by
  change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p row q).symm
    (u, (ReferenceTotalSourceDisintegration.sourceRetainedInput rate rewards C_star C_h q control0
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex row q) z).val) = _
  rw [ReferenceTotalSourceDisintegration.sourceRetainedInput_val]
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p row q z.val u z.property.1

private theorem birth_coordinates_restore (row : Fin (M p)) (q : Fin p.T)
    (x : ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
      rate rewards C_star C_h row q control0) (u : ContinuousLearningRows.TimeControl p) :
    ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates rate rewards C_star C_h row q control0
      (ReferenceFirstLaunchRecordingSourceLaw.restoreSource
        rate rewards C_star C_h row q control0 (x, u)) =
      (x, LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u) :=
  congrArg (fun y => (y.1, LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p y.2))
    (ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates_restoreSource
      rate rewards C_star C_h row q control0 (x, u))

private theorem birth_observation_marker_restore (row : Fin (M p)) (q : Fin p.T)
    (x : ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
      rate rewards C_star C_h row q control0) (u : ContinuousLearningRows.TimeControl p) :
    (ReferenceFirstLiveBirthJointSourceLaw.birthObservation
      rate rewards C_star C_h row q control0 (x, u)).2.2.1 =
      ReferenceFirstLaunchRecordingSourceLaw.sourceMarker rate rewards C_star C_h row q control0
        (ReferenceFirstLaunchRecordingSourceLaw.restoreSource
          rate rewards C_star C_h row q control0 (x, u)) := by
  let z := ReferenceFirstLaunchRecordingSourceLaw.restoreSource
    rate rewards C_star C_h row q control0 (x, u)
  have hc : ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
      rate rewards C_star C_h row q control0 z =
      (x, LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u) := by
    change ((ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates
      rate rewards C_star C_h row q control0 z).1,
      LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
        (ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates
          rate rewards C_star C_h row q control0 z).2) = _
    rw [ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates_restoreSource]
  have hp := congrArg Prod.fst
    (ReferenceFirstLiveBirthChronologicalReadout.actual_birth_pair_eq_unitBirthPair
      rate rewards C_star C_h row q control0 z)
  rw [hc] at hp
  change _ = (ReferenceFirstLiveBirthChronologicalReadout.unitBirthPair rate q
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u).1 _
      ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u)).1).1 at hp
  rw [(LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply] at hp
  exact hp.symm

private theorem birth_observation_marker_split (row : Fin (M p)) (q : Fin p.T)
    (x : ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
      rate rewards C_star C_h row q control0)
    (v : LaunchAssignmentCoordinateSplit.AssignmentVector p)
    (d : ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p) :
    (ReferenceFirstLiveBirthJointSourceLaw.birthObservation rate rewards C_star C_h row q control0
      (x, (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm (v, d))).2.2.1 =
      ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
        rate rewards C_star C_h row q control0 x v d := by
  rw [birth_observation_marker_restore rate rewards C_star C_h control0 row q x]
  unfold ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
  rw [birth_coordinates_restore rate rewards C_star C_h control0 row q x,
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).apply_symm_apply]

private theorem birth_entry_recorder_proposal (q : Fin p.T)
    (z : LiveSource q)
    (hb : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = q.val)
    (a : Aux) :
    let row := ActualInitializationPhysicalStep.selectedRowIndex p z.val
    let born := birthLiveSource rate rewards C_star C_h q z hb
    let k := liveIndex q z
    let r := (liveWindow z.val)[k.val]
    let cell := wholeLiveCell rate rewards C_star C_h z.val r (List.getElem_mem k.isLt)
    cell.input.recordedArm = ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
        rate rewards C_star C_h row q control0 born ∧
      (liveEntry q z a).proposal =
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate ((z.val.1.2 row).2 q) := by
  intro row born k r cell
  let W := liveWindow z.val
  have hpositive := ReferenceFirstLiveBirthChronologicalReadout.actual_birth_chronological_prefix_positive
    rate rewards C_star C_h row q born
  let k0 : Fin W.length := ⟨0, hpositive⟩
  have hkk : k = k0 := by
    apply Fin.ext
    change q.val - ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = 0
    rw [hb, Nat.sub_self]
  have hrec : r = W[k0.val] := congrArg (fun j : Fin W.length => W[j.val]) hkk
  have hc : cell.input = ReferenceFirstLaunchCommonUpdateSource.firstCell
      rate rewards C_star C_h row q control0 born := by
    have hinput := actualCell_input_congr rate hrec cell
      (wholeLiveCell rate rewards C_star C_h z.val W[k0.val] (List.getElem_mem k0.isLt))
    exact hinput.trans (ReferenceFirstLiveBirthChronologicalReadout.actual_birth_whole_first_cell_input_eq
      rate rewards C_star C_h row q control0 born)
  let c := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h row q control0 born
  have hm := (ReferenceFirstLaunchRecordingPhysicalMarker.numerical_cell_readout
    rate rewards C_star C_h row q control0 c.1 c.2.1 c.2.2).2.1
  refine ⟨(congrArg RecordedQueueRun.RoundInput.recordedArm hc).trans hm, ?_⟩
  have hp := ReferenceFirstLiveBirthJointSourceLaw.actual_birth_proposal_eq_physical
    rate rewards C_star C_h row q control0 born a
  have hu : ReferenceFirstLaunchRecordingPhysicalMarker.currentControl c.2.1 c.2.2 =
      ((z.val.1.2 row).2 q) :=
    (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p).symm_apply_apply _
  rw [hu] at hp
  simpa only [liveCalendarEntry, liveCalendarIndex, hb, Nat.sub_self, born, birthLiveSource] using hp

omit rewards C_star C_h control0 in
private theorem proposal_invariant_joint {A : Type*} [MeasurableSpace A]
    (H : ContinuousLearningRows.TimeControl p → A) (hH : Measurable H)
    (hinv : ∀ u a, H (ReferenceFirstLivePostUpdateProposalLaw.replaceProposalScalar p u a) = H u) :
    (ContinuousLearningRows.timeControlLaw p).map (fun u =>
      (H u, ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u)) =
      ((ContinuousLearningRows.timeControlLaw p).map H).prod
        (ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate) := by
  let split := ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit p
  let zero := ReferenceFirstLiveActualRefreshTestLaw.scalarZero
  let g : Unit × ReferenceFirstLivePostUpdateProposalLaw.PropRestControl p → A :=
    fun y => H (split.symm (zero, y.2))
  have hg : Measurable g := hH.comp
    (split.symm.measurable.comp (measurable_const.prodMk measurable_snd))
  have heq (u : ContinuousLearningRows.TimeControl p) : g ((), (split u).2) = H u := by
    have h := ReferenceFirstLivePostUpdateProposalLaw.proposalControlSplit_symm_replace
      p zero (split u).1 (split u).2
    rw [split.symm_apply_apply] at h
    exact (congrArg H h).trans (hinv u zero)
  have hf := ReferenceFirstLivePostUpdateProposalLaw.proposalSplit_joint_pushforward
    (Measure.dirac ()) g hg rate
  have hm : Measurable (fun y : Unit × ContinuousLearningRows.TimeControl p =>
      (g (y.1, (split y.2).2), ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate y.2)) :=
    (hg.comp (measurable_fst.prodMk (split.measurable.comp measurable_snd).snd)).prodMk
      ((ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate).comp measurable_snd)
  rw [Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left] at hf
  simp only [Function.comp_def, heq] at hf
  have hmarg := congrArg (Measure.map Prod.fst) hf
  rw [Measure.map_map measurable_fst
      (hH.prodMk (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate)),
    (measurePreserving_fst (μ := ((Measure.dirac ()).prod
      (ReferenceFirstLivePostUpdateProposalLaw.proposalRestControlLaw p)).map g)
      (ν := ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate)).map_eq] at hmarg
  rw [← hmarg] at hf
  exact hf

omit rewards C_star C_h control0 in
private theorem proposal_invariant_lintegral {A : Type*} [MeasurableSpace A]
    (H : ContinuousLearningRows.TimeControl p → A) (hH : Measurable H)
    (hinv : ∀ u a, H (ReferenceFirstLivePostUpdateProposalLaw.replaceProposalScalar p u a) = H u)
    (g : A × Bool → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ u, g (H u, ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u)
      ∂ContinuousLearningRows.timeControlLaw p) =
    ∫⁻ u, ∫⁻ B, g (H u, B) ∂ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate
      ∂ContinuousLearningRows.timeControlLaw p := by
  rw [← lintegral_map hg
    (hH.prodMk (ReferenceFirstLivePostUpdateProposalLaw.measurable_physicalProposalBit rate)),
    proposal_invariant_joint rate H hH hinv, lintegral_prod _ hg.aemeasurable,
    lintegral_map hg.lintegral_prod_right' hH]

private theorem birth_assignment_lintegral (row : Fin (M p)) (q : Fin p.T)
    (x : ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
      rate rewards C_star C_h row q control0)
    (f : LaunchAssignmentCoordinateSplit.AssignmentVector p × Option (Fin p.K) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ u, f ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u).1,
      (ReferenceFirstLiveBirthJointSourceLaw.birthObservation
        rate rewards C_star C_h row q control0 (x, u)).2.2.1)
      ∂ContinuousLearningRows.timeControlLaw p) =
    ∫⁻ v, ∑ i : Option (Fin p.K), f (v, i) *
      ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate {i}
      ∂ContinuousControlSlice.assignmentLaw p.K := by
  let split := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  have hm : Measurable (fun vd : LaunchAssignmentCoordinateSplit.AssignmentVector p ×
      ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p =>
      ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
        rate rewards C_star C_h row q control0 x vd.1 vd.2) :=
    Measurable.of_uncurry_left (f := fun
      (x : ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart rate rewards C_star C_h row q control0)
      (vd : LaunchAssignmentCoordinateSplit.AssignmentVector p ×
        ReferenceFirstLaunchRecordingPhysicalMarker.NonAssignmentControl p) =>
      ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
        rate rewards C_star C_h row q control0 x vd.1 vd.2)
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_physicalMarker rate rewards C_star C_h row q control0)
  have hskew := (MeasurePreserving.id (ContinuousControlSlice.assignmentLaw p.K)).skew_product hm
    (Filter.Eventually.of_forall (fun v => ReferenceFirstLaunchRecordingSourceLaw.map_physicalMarker
      rate rewards C_star C_h row q control0 x v))
  have hmap : (ContinuousLearningRows.timeControlLaw p).map
      (fun u => ((split u).1, ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
        rate rewards C_star C_h row q control0 x (split u).1 (split u).2)) =
      (ContinuousControlSlice.assignmentLaw p.K).prod
        (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate) :=
    (hskew.comp (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p)).map_eq
  have hread (u : ContinuousLearningRows.TimeControl p) :
      (ReferenceFirstLiveBirthJointSourceLaw.birthObservation
        rate rewards C_star C_h row q control0 (x, u)).2.2.1 =
      ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
        rate rewards C_star C_h row q control0 x (split u).1 (split u).2 := by
    have h := birth_observation_marker_split
      rate rewards C_star C_h control0 row q x (split u).1 (split u).2
    rw [split.symm_apply_apply] at h
    exact h
  simp_rw [hread]
  have hj : Measurable (fun u : ContinuousLearningRows.TimeControl p =>
      ((split u).1, ReferenceFirstLaunchRecordingPhysicalMarker.physicalMarker
        rate rewards C_star C_h row q control0 x (split u).1 (split u).2)) :=
    split.measurable.fst.prodMk (hm.comp split.measurable)
  rw [← lintegral_map hf hj, hmap, lintegral_prod _ hf.aemeasurable]
  exact lintegral_congr fun v => lintegral_fintype _

private theorem birth_control_lintegral (row : Fin (M p)) (q : Fin p.T)
    (x : ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
      rate rewards C_star C_h row q control0)
    (f : LaunchAssignmentCoordinateSplit.AssignmentVector p × (Option (Fin p.K) × Bool) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ u, f ((LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u).1,
      ((ReferenceFirstLiveBirthJointSourceLaw.birthObservation
        rate rewards C_star C_h row q control0 (x, u)).2.2.1,
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u))
      ∂ContinuousLearningRows.timeControlLaw p) =
    ∫⁻ v, ∑ i : Option (Fin p.K), ∑ B : Bool, f (v, (i, B)) *
      (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate {i} *
        ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B})
      ∂ContinuousControlSlice.assignmentLaw p.K := by
  let split := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
  let H := fun u : ContinuousLearningRows.TimeControl p =>
    let y := ReferenceFirstLiveBirthJointSourceLaw.birthObservation
      rate rewards C_star C_h row q control0 (x, u)
    (y.2.1, y.2.2.1)
  have hobs : Measurable (fun u : ContinuousLearningRows.TimeControl p =>
      ReferenceFirstLiveBirthJointSourceLaw.birthObservation
        rate rewards C_star C_h row q control0 (x, u)) :=
    (ReferenceFirstLiveBirthJointSourceLaw.measurable_birthObservation
      rate rewards C_star C_h row q control0).comp (measurable_const.prodMk measurable_id)
  have hH : Measurable H := hobs.snd.fst.prodMk hobs.snd.snd.fst
  have hinv (u : ContinuousLearningRows.TimeControl p) (a : Scalar) :
      H (ReferenceFirstLivePostUpdateProposalLaw.replaceProposalScalar p u a) = H u :=
    congrArg (fun y => (y.2.1, y.2.2.1))
      (ReferenceFirstLiveBirthJointSourceLaw.birthObservation_replaceProposal
        rate rewards C_star C_h row q control0 x u a)
  let g := fun y : (LaunchAssignmentCoordinateSplit.AssignmentVector p × Option (Fin p.K)) × Bool =>
    f (y.1.1, (y.1.2, y.2))
  have hg : Measurable g := hf.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hfactor := proposal_invariant_lintegral rate H hH hinv g hg
  rw [show (fun u => f ((split u).1,
      ((ReferenceFirstLiveBirthJointSourceLaw.birthObservation
        rate rewards C_star C_h row q control0 (x, u)).2.2.1,
        ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u))) =
      (fun u => g (H u, ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u)) from rfl,
    hfactor]
  let test : LaunchAssignmentCoordinateSplit.AssignmentVector p × Option (Fin p.K) → ℝ≥0∞ :=
    fun y => ∫⁻ B, f (y.1, (y.2, B)) ∂ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate
  have ht : Measurable test := hg.lintegral_prod_right'
  change (∫⁻ u, test ((split u).1,
    (ReferenceFirstLiveBirthJointSourceLaw.birthObservation
      rate rewards C_star C_h row q control0 (x, u)).2.2.1)
    ∂ContinuousLearningRows.timeControlLaw p) = _
  rw [birth_assignment_lintegral rate rewards C_star C_h control0 row q x test ht]
  apply lintegral_congr
  intro v
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [test]
  rw [lintegral_fintype, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B _
  ac_rfl

omit rewards C_star C_h control0 in
private theorem optional_initial_append_test (s q : Fin p.T) (h : History rate s q)
    (r : Record rate) (cell : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (a : Aux) (F : TransitionData rate s q → ℝ≥0∞) :
    let e := appendLogicalCell r cell (S₀) a
    optionalTransitionTest rate s q F (h, (sourceOptionalEstimate rate (some e), some e)) =
      F (h, (cell.selected.view.payload.slowSet,
        (sourceEstimate Q (S₀) cell.input,
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time, e.nextSlowSet)))) := by
  intro e
  have hest : sourceOptionalEstimate rate (some e) =
      sourceEstimate Q (S₀) cell.input := by
    funext i
    exact sourceCellEstimate_eq_rawEstimate rate _ cell.input rfl i
  change F (h, (e.slowSet, (sourceOptionalEstimate rate (some e), (e.proposal, e.nextSlowSet)))) = _
  rw [hest]
  rfl

private theorem birth_source_scalar_test (s q : Fin p.T) (o : Obs)
    (hg : currentCellGate rate rewards C_star C_h q o.1 = true)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (hb : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val)
    (F : TransitionData rate s q → ℝ≥0∞)
    (x : Scalar) (u : ContinuousLearningRows.TimeControl p) :
    let zu : LiveSource q :=
      ⟨insertControl q o.1 u,
        (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 u).trans hg⟩
    let k := liveIndex q zu
    let r := (liveWindow zu.val)[k.val]
    let cell := wholeLiveCell rate rewards C_star C_h zu.val r (List.getElem_mem k.isLt)
    (∫⁻ a, optionalTransitionTest rate s q F
      (srcJoint s q (refillProposal q (o, x), (u, a)))
      ∂scalarLaw) =
    ∫⁻ V, F (srcHistory s q o,
      (cell.selected.view.payload.slowSet,
        (sourceEstimate Q (S₀) cell.input,
          (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time, V))))
      ∂liveCalendarResidualLaw rate rewards C_star C_h q zu := by
  intro zu k r cell
  have hbu := (liveCalendar_start_replace_current
    rate rewards C_star C_h control0 q ⟨o.1, hg⟩ u).trans hb
  have hstate : RecordedQueueRun.run Q ((liveCells zu.val).take k.val) = S₀ := by
    change RecordedQueueRun.run Q ((liveCells zu.val).take
      (q.val - ReferenceCompletePhysicalHistory.physicalStart rate zu.val rewards C_star C_h)) = _
    rw [hbu, Nat.sub_self, List.take_zero]
    rfl
  have he (a : Aux) : liveEntry q zu a =
      appendLogicalCell r cell (S₀) a := by
    have h := firstLiveChronologicalPrefix_get rate rewards C_star C_h zu.val a k
    change liveEntry q zu a = appendLogicalCell r cell
      (RecordedQueueRun.run Q ((liveCells zu.val).take k.val)) a at h
    rw [hstate] at h
    exact h
  let test : SlowSet p → ℝ≥0∞ := fun V => F (srcHistory s q o,
    (cell.selected.view.payload.slowSet,
      (sourceEstimate Q (S₀) cell.input,
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time, V))))
  have hread (a : Scalar) : optionalTransitionTest rate s q F
      (srcJoint s q (refillProposal q (o, x), (u, a))) =
      test (liveEntry q zu (innovationAuxiliary q a)).nextSlowSet := by
    unfold prefixSourceJoint
    rw [prefixCurrentMark_live rate rewards C_star C_h control0 q o hg hpast x (u, a),
      prefixSourceHistory_refillProposal]
    have ha : liveEntry q zu
        (roundAuxiliary q ((refillProposal q (o, x)).2.1, a)) =
        liveEntry q zu (innovationAuxiliary q a) := by
      apply Sum.inr.inj
      rw [← currentCellTag_live, ← currentCellTag_live]
      apply currentCellTag_auxiliary_ext
      simp only [roundAuxiliary, innovationAuxiliary, show (1 : Fin 2) ≠ 0 by decide,
        ite_false, ite_true, Function.update_self]
    rw [ha, he]
    exact optional_initial_append_test rate s q (srcHistory s q o)
      r cell (innovationAuxiliary q a) F
  simp_rw [hread]
  have hn : Measurable (fun a : Scalar =>
      (liveEntry q zu (innovationAuxiliary q a)).nextSlowSet) :=
    Measurable.of_uncurry_left (f := fun
      (z : LiveSource q) (a : Scalar) =>
      (liveEntry q z (innovationAuxiliary q a)).nextSlowSet)
        (measurable_liveCalendarNext rate rewards C_star C_h q)
  rw [liveCalendarResidualLaw_eq_map_next]
  exact (lintegral_map (measurable_of_countable test) hn).symm

private theorem birth_inserted_fields (q : Fin p.T) (o : Obs)
    (hg : currentCellGate rate rewards C_star C_h q o.1 = true)
    (hpast : ∀ e ∈ o.2.2, e.time.val < q.val)
    (hb : ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val)
    (u : ContinuousLearningRows.TimeControl p) :
    let row := ActualInitializationPhysicalStep.selectedRowIndex p o.1
    let base := birthLiveSource rate rewards C_star C_h q ⟨o.1, hg⟩ hb
    let x := (ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates
      rate rewards C_star C_h row q control0 base).1
    let zu : LiveSource q :=
      ⟨insertControl q o.1 u,
        (currentCellGate_replace_current rate rewards C_star C_h control0 q o.1 u).trans hg⟩
    let k := liveIndex q zu
    let r := (liveWindow zu.val)[k.val]
    let cell := wholeLiveCell rate rewards C_star C_h zu.val r (List.getElem_mem k.isLt)
    cell.input.recordedArm = (ReferenceFirstLiveBirthJointSourceLaw.birthObservation
      rate rewards C_star C_h row q control0 (x, u)).2.2.1 ∧
    cell.selected.view.payload.slowSet =
      CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
        (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u).1 ∧
    FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row r.input.time =
      ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u := by
  intro row base x zu k r cell
  have hbu := (liveCalendar_start_replace_current
    rate rewards C_star C_h control0 q ⟨o.1, hg⟩ u).trans hb
  let born := birthLiveSource rate rewards C_star C_h q zu hbu
  have hrestore : ReferenceFirstLaunchRecordingSourceLaw.restoreSource
      rate rewards C_star C_h row q control0 (x, u) = born :=
    Subtype.ext (birth_restore_source rate rewards C_star C_h control0 row q base u)
  have hcurrent : ((zu.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p zu.val)).2 q) = u := by
    simp only [zu, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ActualInitializationPhysicalStep.selectedRowIndex,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, Function.update_self]
  obtain ⟨hm, hp⟩ := birth_entry_recorder_proposal
    rate rewards C_star C_h control0 q zu hbu ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection
  change cell.input.recordedArm = ReferenceFirstLaunchRecordingSourceLaw.sourceMarker
    rate rewards C_star C_h row q control0 born at hm
  rw [← hrestore] at hm
  refine ⟨hm.trans (birth_observation_marker_restore
    rate rewards C_star C_h control0 row q x u).symm, ?_, ?_⟩
  · have hU := (prefixSourceJoint_birth_coordinates rate rewards C_star C_h control0 q q o hg hpast hb
      ReferenceFirstLiveActualRefreshTestLaw.scalarZero (u, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)).2.2
    have he := firstLiveChronologicalPrefix_get rate rewards C_star C_h zu.val
      (roundAuxiliary q ((refillProposal q (o, ReferenceFirstLiveActualRefreshTestLaw.scalarZero)).2.1,
        ReferenceFirstLiveActualRefreshTestLaw.scalarZero)) k
    change liveEntry q zu _ = appendLogicalCell r cell
      (RecordedQueueRun.run Q ((liveCells zu.val).take k.val)) _ at he
    have hk : k.val = 0 := by
      change q.val - ReferenceCompletePhysicalHistory.physicalStart rate zu.val rewards C_star C_h = 0
      rw [hbu, Nat.sub_self]
    rw [hk, List.take_zero] at he
    rw [he] at hU
    exact hU
  · rw [hcurrent] at hp
    have he := firstLiveChronologicalPrefix_get rate rewards C_star C_h zu.val
      ReferenceFirstLiveActualRefreshTestLaw.auxiliarySection k
    have hk : k.val = 0 := by
      change q.val - ReferenceCompletePhysicalHistory.physicalStart rate zu.val rewards C_star C_h = 0
      rw [hbu, Nat.sub_self]
    change liveEntry q zu _ = appendLogicalCell r cell
      (RecordedQueueRun.run Q ((liveCells zu.val).take k.val)) _ at he
    rw [hk, List.take_zero] at he
    rw [he] at hp
    exact hp

omit rewards C_star C_h control0 in
private theorem birth_outcomeLaw_mass (i : Option (Fin p.K)) :
    ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate {i} =
      RecordedRoundMoments.recordingOutcomePMF
        (ReferenceGeneratedCalendarQuantizedRoundKernel.anchorRates rate
          (RecordedQueueRun.scoreWeight Q (S₀))
          (RecordedSlowRefresh.scoreWeight_pos Q (S₀))) i := by
  have hw : RecordedQueueRun.scoreWeight Q (S₀) = fun _ => 1 := by
    funext j
    simp only [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState, ScoreWeights.scoreWeight, pow_zero]
  rw [ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change RecordedRoundMoments.recordingOutcomePMF
    (ReferenceGeneratedCalendarQuantizedRoundKernel.anchorRates rate (fun _ => 1) (fun _ => zero_lt_one)) i = _
  rw [anchorRates_congr rate _ _ (fun _ => zero_lt_one)
    (RecordedSlowRefresh.scoreWeight_pos Q (S₀)) hw.symm]

omit rate rewards C_star C_h control0 in
private theorem assignment_control_lintegral
    (g : LaunchAssignmentCoordinateSplit.AssignmentVector p → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ u, g (LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p u).1
      ∂ContinuousLearningRows.timeControlLaw p) =
      ∫⁻ v, g v ∂ContinuousControlSlice.assignmentLaw p.K :=
  ((measurePreserving_fst (μ := ContinuousControlSlice.assignmentLaw p.K)
    (ν := ReferenceFirstLaunchRecordingSourceLaw.nonAssignmentLaw p)).comp
      (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p)).lintegral_comp hg

/-- The birth joint test on the ORIGINAL erased experiment. Its actual old
set remains the image of the whole assignment vector in both integrals. -/
theorem ae_erased_birth_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    ∀ᵐ o ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
      (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map (eraseProposal q),
      currentCellGate rate rewards C_star C_h q o.1 = true →
      ReferenceCompletePhysicalHistory.physicalStart rate o.1 rewards C_star C_h = q.val →
      (∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
        srcTest s q F
          (srcJoint s q (refillProposal q (o, x), ux))
        else 0 ∂calendarInnovationLaw p ∂scalarLaw) =
      ∫⁻ x, ∫⁻ ux, if noCallAt rate rewards C_star C_h q o.1 then
        kerTest s q F
          (srcJoint s q (refillProposal q (o, x), ux))
        else 0 ∂calendarInnovationLaw p ∂scalarLaw := by
  filter_upwards [ae_erased_prefix_live_replay rate rewards C_star C_h control0 ids s q hsq,
    ae_erased_birth_initialization rate rewards C_star C_h control0 ids s q hsq,
    ae_erased_birth_input_residual rate rewards C_star C_h control0 ids s q hsq] with o ho hp hi
  intro hg hb
  by_cases hn : noCallAt rate rewards C_star C_h q o.1
  · simp only [hn, ite_true]
    let h := srcHistory s q o
    have hgate (G : TransitionData rate s q → ℝ≥0∞) (x : Scalar) (ux : Innovation) :
        srcTest s q G
          (srcJoint s q (refillProposal q (o, x), ux)) =
        if h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
            h ∈ sourceHistoryRetained rate rewards C_star C_h s q then
          optionalTransitionTest rate s q G
            (srcJoint s q (refillProposal q (o, x), ux))
        else 0 := rfl
    unfold retainedKernelTest
    simp_rw [hgate]
    by_cases hr : h.1.1 ∈ sourceStartEvent rate rewards C_star C_h s ∧
        h ∈ sourceHistoryRetained rate rewards C_star C_h s q
    · simp only [hr, and_self, ite_true]
      obtain ⟨_, _, hseed, hrep⟩ := hp hg hb hn hr.1 hr.2
      let row := ActualInitializationPhysicalStep.selectedRowIndex p o.1
      let born := birthLiveSource rate rewards C_star C_h q ⟨o.1, hg⟩ hb
      let past := (ReferenceFirstLaunchRecordingSourceLaw.sourceControlCoordinates
        rate rewards C_star C_h row q control0 born).1
      let U := CanonicalAssignmentVector.canonicalSlowSampler p.two_le_m p.m_lt_K
        (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
      let split := LaunchAssignmentCoordinateSplit.controlAssignmentSplitEquiv p
      let marker := fun u => (ReferenceFirstLiveBirthJointSourceLaw.birthObservation
        rate rewards C_star C_h row q control0 (past, u)).2.2.1
      let f0 : SlowSet p × (Option (Fin p.K) × Bool) → ℝ≥0∞ := fun y =>
        ∫⁻ V, F (h, (y.1, (sourceEstimate Q (S₀)
          (episodeInput q (S₀) y.2.1), (y.2.2, V))))
          ∂episodeNext q (S₀)
            (S₀) y.1 y.2.1 y.2.2
      let f := fun y : LaunchAssignmentCoordinateSplit.AssignmentVector p × (Option (Fin p.K) × Bool) =>
        f0 (U y.1, y.2)
      have hU : Measurable U := (CanonicalAssignmentVector.measurable_canonicalSlowSampler
        p.two_le_m p.m_lt_K (fun _ => 1) (fun _ => 1)
          (fun _ => zero_lt_one) (fun _ => zero_lt_one)).mono le_rfl le_top
      have hf : Measurable f := (measurable_of_countable f0).comp
        ((hU.comp measurable_fst).prodMk measurable_snd)
      have hscalar (x : Scalar) (u : ContinuousLearningRows.TimeControl p) :
          (∫⁻ a, optionalTransitionTest rate s q F
            (srcJoint s q (refillProposal q (o, x), (u, a)))
            ∂scalarLaw) = f ((split u).1, (marker u,
              ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u)) := by
        rw [birth_source_scalar_test rate rewards C_star C_h control0 s q o hg ho.1 hb F x u]
        obtain ⟨hinput, hres⟩ := hi hg hb hn hr.1 hr.2 u
        obtain ⟨hm, hset, hbit⟩ := birth_inserted_fields rate rewards C_star C_h control0 q o hg ho.1 hb u
        rw [hres, hinput, hm, hset, hbit]
        rfl
      have hsum (v : LaunchAssignmentCoordinateSplit.AssignmentVector p) :
          (∑ i : Option (Fin p.K), ∑ B : Bool, f (v, (i, B)) *
            (ReferenceFirstLaunchRecordingSourceLaw.outcomeLaw rate {i} *
              ReferenceFirstLivePostUpdateProposalLaw.proposalBitLaw rate {B})) =
          commonTest s q F h (U v) := by
        unfold episodeTransitionTest
        rw [hseed, hrep]
        simp only [f, f0, episodeRoundTest, lintegral_fintype, Finset.sum_mul, mul_assoc,
          birth_outcomeLaw_mass rate]
        rfl
      have hlocal : (∫⁻ x, ∫⁻ ux, optionalTransitionTest rate s q F
          (srcJoint s q (refillProposal q (o, x), ux))
          ∂calendarInnovationLaw p ∂scalarLaw) =
          ∫⁻ v, commonTest s q F h (U v)
            ∂ContinuousControlSlice.assignmentLaw p.K := by
        have heach (x : Scalar) : (∫⁻ ux, optionalTransitionTest rate s q F
            (srcJoint s q (refillProposal q (o, x), ux))
            ∂calendarInnovationLaw p) =
            ∫⁻ u, f ((split u).1, (marker u,
              ReferenceFirstLivePostUpdateProposalLaw.physicalProposalBit rate u))
              ∂ContinuousLearningRows.timeControlLaw p := by
          have hm : Measurable (fun ux : Innovation => optionalTransitionTest rate s q F
              (srcJoint s q (refillProposal q (o, x), ux))) :=
            (measurable_optionalTransitionTest rate s q F hF).comp
              (Measurable.of_uncurry_left (f := fun (o : Obs) (ux : Innovation) =>
                srcJoint s q (o, ux))
                (measurable_prefixSourceJoint rate rewards C_star C_h control0 s q))
          exact (lintegral_prod _ hm.aemeasurable).trans (lintegral_congr (hscalar x))
        simp_rw [heach]
        rw [lintegral_const, measure_univ, mul_one,
          birth_control_lintegral rate rewards C_star C_h control0 row q past f hf]
        exact lintegral_congr hsum
      rw [hlocal]
      have hk (x : Scalar) (ux : Innovation) :
          optionalTransitionTest rate s q (kernelLiftTest rate rewards C_star C_h s q F)
            (srcJoint s q (refillProposal q (o, x), ux)) =
          commonTest s q F h (U (split ux.1).1) := by
        obtain ⟨hj, _, hs⟩ := prefixSourceJoint_birth_coordinates
          rate rewards C_star C_h control0 s q o hg ho.1 hb x ux
        rw [hj]
        change commonTest s q F h _ = _
        rw [hs]
      simp_rw [hk]
      rw [lintegral_const, measure_univ, mul_one]
      have hK : Measurable (fun v => commonTest s q F h (U v)) :=
        (Measurable.of_uncurry_left (f := fun (h : History rate s q) (U : SlowSet p) =>
          commonTest s q F h U)
          (measurable_episodeTransitionTest rate rewards C_star C_h s q F hF)).comp hU
      symm
      calc
        _ = ∫⁻ u, commonTest s q F h (U (split u).1)
            ∂ContinuousLearningRows.timeControlLaw p :=
          (measurePreserving_fst (μ := ContinuousLearningRows.timeControlLaw p)
            (ν := scalarLaw)).lintegral_comp (hK.comp split.measurable.fst)
        _ = _ := assignment_control_lintegral _ hK
    · simp only [hr, ite_false, lintegral_zero]
  · simp only [hn, ite_false, lintegral_zero]

/-- The exhaustive FIRST-LIVE retained joint-test identity on the literal
original erased-prefix experiment, raw and every original fixed-ID law.
Birth and BOTH positive-offset phases are exhausted by the actual gate. -/
theorem beforePrefix_firstLive_retained_transition_test
    (ids : Option (CompletePublicTable.IDArray p)) (s q : Fin p.T)
    (hsq : s.val ≤ q.val) (F : TransitionData rate s q → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ o, ∫⁻ x, ∫⁻ ux,
      if o.1 ∈ {z | currentCellGate rate rewards C_star C_h q z = true} then
        if noCallAt rate rewards C_star C_h q o.1 then
          srcTest s q F
            (srcJoint s q (refillProposal q (o, x), ux))
        else 0 else 0 ∂calendarInnovationLaw p ∂scalarLaw
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map (eraseProposal q)) =
    ∫⁻ o, ∫⁻ x, ∫⁻ ux,
      if o.1 ∈ {z | currentCellGate rate rewards C_star C_h q z = true} then
        if noCallAt rate rewards C_star C_h q o.1 then
          kerTest s q F
            (srcJoint s q (refillProposal q (o, x), ux))
        else 0 else 0 ∂calendarInnovationLaw p ∂scalarLaw
      ∂(ids.elim (betaPre rate rewards C_star C_h control0 q.castSucc)
        (fun id => fixedIDBetaPre rate rewards C_star C_h control0 id q.castSucc)).map (eraseProposal q) := by
  apply lintegral_congr_ae
  filter_upwards [ae_erased_birth_retained_transition_test
      rate rewards C_star C_h control0 ids s q hsq F hF,
    ae_erased_positive_retained_transition_test
      rate rewards C_star C_h control0 ids s q hsq F hF] with o hb hp
  by_cases hg : currentCellGate rate rewards C_star C_h q o.1 = true
  · simp only [hg, ite_true]
    rcases (currentCellGate_iff_sourcePhases rate rewards C_star C_h control0 q o.1).mp hg with h | h | h
    · exact hb hg h.2.symm
    · exact hp hg h.2.1
    · exact hp hg h.2.1
  · simp only [hg, Bool.false_eq_true, ite_false, lintegral_zero]

end Bandits.Support.ReferenceGeneratedCalendarFirstLiveEpisodeTransition
