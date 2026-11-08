/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstNextInstallationTransitionLaw
public import Bandits.Support.ReferenceFirstCollectionLogicalNumericalAlignment

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Actual-source noncall geometry after a produced installation cell

The starting list is the accepted transition's constructed append. Numerical
states count calendar dates, including disabled dates. The interval kill below
excludes the next actual invocation and does not test the boundary date itself.

Sources: ZIP4 `06_interruptions.tex:391-426`,
`04_slow_fast_learner.tex:142-215,323-390`, and
`08_main_theorem.tex:78-109`.

These internal constructors and readouts make no source-facing closure claim.
They start from the actual produced append and prove noncall phase coverage,
physical payload inheritance, numerical provenance and whole-list auxiliary nonuse.
Generated LIVE seed agreement, actual collection segment/envelope, complete-prefix
Borel/physical locality, both native joint kernels and both bounded killed laws
remain open. Full-source observations are readouts, not freshness observers;
the post-cell measures below are unnormalized pushforward definitions.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support
open ConstructorDimensions
open ReferenceFirstLiveChronologicalPrefixFoundation
open ReferenceFirstNextInstallationTransitionLaw
open ReferenceFirstNextInstallationCellFactors
open ReferenceFirstCollectionLogicalNumericalAlignment
open ReferenceActualCollectionHiddenRefreshPath (actualOriginalWord)
open ReferenceFirstLaunchNumericalCell (queueParameters)
open ReferenceCompletePhysicalHistory (physicalStart completeSuffixRecords)
open ReferenceFirstCollectionLogicalPrefixExtension (extendedPast noCallAt)
open ReferenceFirstLiveChronologicalPrefixMeasurability

namespace Bandits.Support.ReferencePostInvocationNoncallGeometry

variable {p : ConstructorDimensions.Parameters}

local instance sourceMeasurableSpace : MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Q" => queueParameters rate
local notation "start " z:max => physicalStart rate z rewards C_star C_h

def insertedPhysicalSource {t : Fin p.T} (d : TransitionData rate t) : BootstrapPrivateRoundStreams.SourceInput p :=
  d.2.2.1

/-- The next logical seed is the produced cell's residual outcome. In the
renewal branch this is the label-zero residual, not its label-one initial draw. -/
def postSeed {t : Fin p.T} (d : TransitionData rate t) : SlowSet p :=
  d.2.2.2.nextSlowSet

def postNumerical {t : Fin p.T} (d : TransitionData rate t) : RecordedQueueRun.RunState p.K :=
  d.2.2.2.after

theorem measurable_insertedPhysicalSource (t : Fin p.T) :
    Measurable (insertedPhysicalSource rate (t := t)) := measurable_snd.snd.fst

theorem measurable_postSeed (t : Fin p.T) :
    Measurable (postSeed rate (t := t)) :=
  (measurable_logicalCell_nextSlowSet.comp measurable_snd.snd.snd).mono le_rfl le_top

theorem measurable_postNumerical (t : Fin p.T) :
    Measurable (postNumerical rate (t := t)) :=
  measurable_logicalCell_after.comp measurable_snd.snd.snd

/-- No actual invocation on `[t+1,n)`. In particular `n` is a PRE-call boundary. -/
def NoCallBetween (t : Fin p.T) (n : Fin (p.T + 1)) (z : BootstrapPrivateRoundStreams.SourceInput p) : Prop :=
  ∀ q : Fin p.T, t.val < q.val → q.val < n.val → noCallAt rate rewards C_star C_h q z

theorem noCallBetween_initial (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    NoCallBetween rate rewards C_star C_h t t.succ z := by
  intro q hq hqn
  have : q.val < t.val + 1 := hqn
  omega

theorem noCallBetween_succ (t q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    NoCallBetween rate rewards C_star C_h t q.succ z ↔
      NoCallBetween rate rewards C_star C_h t q.castSucc z ∧
        (t.val < q.val → noCallAt rate rewards C_star C_h q z) := by
  constructor
  · intro h
    constructor
    · intro v htv hvq
      exact h v htv (by change v.val < q.val + 1; exact hvq.trans (Nat.lt_succ_self _))
    · intro hlt
      exact h q hlt (Nat.lt_succ_self _)
  · rintro ⟨h, hq⟩ v htv hvq
    have hv : v.val ≤ q.val := by simpa only [Fin.val_succ, Nat.lt_succ_iff] using hvq
    rcases Nat.lt_or_eq_of_le hv with hlt | heq
    · exact h v htv hlt
    · have he : v = q := Fin.ext heq
      subst v
      exact hq htv

theorem measurableSet_noCallBetween (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (n : Fin (p.T + 1)) :
    MeasurableSet {z | NoCallBetween rate rewards C_star C_h t n z} := by
  simp only [NoCallBetween, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun q => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ =>
      ReferenceFirstCollectionLogicalPrefixExtension.measurableSet_noCallAt
        rate rewards C_star C_h control0 q)))

/-- Killing at `n` reads no physical coordinate at or after `n`. -/
theorem noCallBetween_sourcePrefix (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (n : Fin (p.T + 1)) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    NoCallBetween rate rewards C_star C_h t n z ↔
      NoCallBetween rate rewards C_star C_h t n
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n.val z) := by
  unfold NoCallBetween
  exact forall_congr' (fun q => imp_congr_right (fun _ => imp_congr_right (fun hqn =>
    ReferenceFirstCollectionLogicalPrefixExtension.noCallAt_sourcePrefix
      rate rewards C_star C_h control0 q n.val hqn.le z)))

private theorem stateReadout_injective : Function.Injective
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (K := p.K)) := by
  intro S R h
  cases S
  cases R
  simp_all only [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, Prod.mk.injEq]

private theorem actualRecord_launch (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active := by
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | some active => exact ⟨active, rfl⟩
  | none =>
      have hs := (ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hl).2.1
      have hn := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_none_iff
        rate rewards C_star C_h q z).mpr (by rw [hs]; exact q.isLt)
      change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = none at hn
      rw [hn] at hr
      cases hr

private theorem actualRecord_originalWord (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate) (c : RecordedQueueRun.RoundInput p.K)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = some active) :
    let W := actualOriginalWord rate rewards C_star C_h z hl
    ∃ hk : q.val - start z < W.length, start z ≤ q.val ∧ c = W[q.val - start z] := by
  have hsq : start z ≤ q.val := by
    by_contra h
    have hn := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_none_iff
      rate rewards C_star C_h q z).mpr (Nat.lt_of_not_ge h)
    change ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = none at hn
    rw [hn] at hr
    cases hr
  have hlookup : (completeSuffixRecords rate z rewards C_star C_h)[q.val - start z]? = some r := by
    simpa only [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hsq] using hr
  have hk : q.val - start z < (actualOriginalWord rate rewards C_star C_h z hl).length := by
    rw [ReferenceActualCollectionHiddenRefreshPath.actualOriginalWord_length]
    exact (List.getElem?_eq_some_iff.mp hlookup).1
  have hm := congrArg (fun L => L[q.val - start z]?)
    (originalWord_record_map rate rewards C_star C_h z hl)
  rw [List.getElem?_map, hlookup, Option.map_some, hc,
    List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some] at hm
  exact ⟨hk, hsq, Option.some.inj (Option.some.inj hm)⟩

/-- The produced native cell's numerical fields are the actual SAME-source
word entry and its complete stopped PRE/POST run. No numerical witness is an
input. The actual first-call event supplies the launch. -/
theorem actualFirstCell_originalWord
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (z : FirstInvocationSource rate rewards C_star C_h t)
    (hz : z.val ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t) (x : ContinuousControlSlice.Scalar) :
    let W := actualOriginalWord rate rewards C_star C_h z.val
      (firstCall_launch rate rewards C_star C_h u t z.val hz)
    let e := actualFirstCell rate rewards C_star C_h control0 t z x
    e.time = t ∧
      e.before = RecordedQueueRun.run Q (W.take (t.val - start z.val)) ∧
      e.after = RecordedQueueRun.run Q (W.take (t.val + 1 - start z.val)) ∧
      ∃ hk : t.val - start z.val < W.length,
        e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
          W[t.val - start z.val] ∧
        e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[t.val - start z.val] ∧
        e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n)
          (e.before.registers j) (e.arrivals j) := by
  dsimp only
  let W := actualOriginalWord rate rewards C_star C_h z.val
    (firstCall_launch rate rewards C_star C_h u t z.val hz)
  let r := firstRecord rate rewards C_star C_h t z
  let c := firstSourceCell rate rewards C_star C_h t z
  have hspec := firstSourceCell_spec rate rewards C_star C_h t z
  have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c.input := by
    change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
      (firstRecord rate rewards C_star C_h t z)).or _ = _
    rw [hspec.2.2, Option.some_or]
  obtain ⟨hk, hst, hc⟩ := actualRecord_originalWord rate rewards C_star C_h t z.val r c.input
    hspec.1 hcell (firstCall_launch rate rewards C_star C_h u t z.val hz)
  change t.val - start z.val < W.length at hk
  change c.input = W[t.val - start z.val] at hc
  have hb := firstBefore_spec rate rewards C_star C_h control0 t z
  have hb' := firstCall_installationNumericalBefore rate rewards C_star C_h control0 u t z.val hz
  have hbefore : firstBefore rate rewards C_star C_h control0 t z =
      RecordedQueueRun.run Q (W.take (t.val - start z.val)) :=
    stateReadout_injective
      (Option.some.inj (hb.symm.trans hb'))
  refine ⟨hspec.2.1, hbefore, ?_, hk, ?_, ?_, rfl⟩
  · change RecordedQueueRun.step Q (firstBefore rate rewards C_star C_h control0 t z) c.input = _
    rw [hbefore, hc, Nat.sub_add_comm hst, ← List.take_append_getElem hk,
      RecordedSlowRefresh.run_append_singleton]
  · change ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c.input = _
    rw [hc]
  · change RecordedQueueRun.acceptedRecord Q _ c.input = _
    rw [hc]
    rfl

theorem postHistory_last (t : Fin p.T) (d : TransitionData rate t) :
    (postHistory d).getLast? = some d.2.2.2 := by
  simp only [postHistory, List.getLast?_append, List.getLast?_singleton, Option.some_or]

theorem nonrenewed_initialization
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (wv : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentParameterFibreKernel.AssignmentVector p) :
    let d := nonrenewedTransition rate rewards C_star C_h control0 u t wv
    let z := nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2
    let hz := firstCall_insertVector_mem rate rewards C_star C_h u t
      wv.1.1.val wv.1.1.property.1 wv.2
    let W := actualOriginalWord rate rewards C_star C_h z.val
      (firstCall_launch rate rewards C_star C_h u t z.val hz)
    insertedPhysicalSource rate d = z.val ∧
      postHistory d = extendedPast rate rewards C_star C_h t.castSucc
        (z.val, wv.1.2) ++ [d.2.2.2] ∧
      (postHistory d).getLast? = some d.2.2.2 ∧ d.2.2.2.time = t ∧
      postNumerical rate d = RecordedQueueRun.run Q
        (W.take (t.val + 1 - start z.val)) ∧
      postSeed rate d = d.2.2.2.nextSlowSet := by
  dsimp only
  have hp := congrArg (fun o => o.2.2)
    (ReferenceFirstNextInvocationJointLift.nextInvocationPrefix_insertVector
      rate rewards C_star C_h t control0 wv.1.1.val wv.1.2 wv.2)
  have hc := actualFirstCell_originalWord rate rewards C_star C_h control0 u t
    (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2)
    (firstCall_insertVector_mem rate rewards C_star C_h u t
      wv.1.1.val wv.1.1.property.1 wv.2) (wv.1.2 (t, 1))
  refine ⟨rfl, ?_, postHistory_last rate t _, hc.1, hc.2.2.1, rfl⟩
  exact congrArg (fun H => H ++ [_]) hp.symm

/-- Exact initial append and numerical state on the literal renewal lift.
The existing renewed cell consumes label zero after the label-one initial draw. -/
theorem renewed_initialization
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t) :
    let d := renewedTransition rate rewards C_star C_h control0 u t wv
    let z := (ReferenceFirstCollectionRenewalInstallationCoupling.pair
      rate rewards C_star C_h u t wv).2
    let W := actualOriginalWord rate rewards C_star C_h z.val
      (firstCall_launch rate rewards C_star C_h u t z.val z.property.1)
    insertedPhysicalSource rate d = z.val ∧
      postHistory d = extendedPast rate rewards C_star C_h t.castSucc
        (z.val, wv.1.2) ++ [d.2.2.2] ∧
      (postHistory d).getLast? = some d.2.2.2 ∧ d.2.2.2.time = t ∧
      postNumerical rate d = RecordedQueueRun.run Q
        (W.take (t.val + 1 - start z.val)) ∧
      postSeed rate d = d.2.2.2.nextSlowSet := by
  dsimp only
  have hp := congrArg (fun o => o.2.2)
    (ReferenceFirstNextInvocationJointLift.renewal_pair_oldObservation
      rate rewards C_star C_h u t control0 wv)
  have hc := actualFirstCell_originalWord rate rewards C_star C_h control0 u t
    (renewedFirstSource rate rewards C_star C_h t u
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2))
    (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t
      wv.1.1 wv.2).property.1 (wv.1.2 (t, 0))
  refine ⟨rfl, ?_, postHistory_last rate t _, hc.1, hc.2.2.1, rfl⟩
  exact congrArg (fun H => H ++ [_]) hp.symm

section LaterCollection

open scoped BigOperators

/-- Explored fast mass at the actual old payload's anchor. -/
def collectionFastMass (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j)
    (U : SlowSet p) (j : CanonicalFastSampling.FastArm U) : ℝ :=
  (1 - CanonicalRecordingRates.gamma p rate.eta.val) *
      FastComplementLocality.localConditionalFastMass anchor U
        (fun j => weight j.val) ha (fun j => hw j.val) j +
    CanonicalRecordingRates.gamma p rate.eta.val / ((p.K - p.m + 1 : ℕ) : ℝ)

theorem collectionFastMass_nonneg (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j)
    (U : SlowSet p) (j : CanonicalFastSampling.FastArm U) :
    0 ≤ collectionFastMass rate anchor weight ha hw U j := by
  have hg := CanonicalRecordingRates.gamma_nonneg_and_le_half p
    rate.eta.property rate.sourceCap
  have hc := FastComplementLocality.localConditionalFastMass_pos anchor ha U
    (fun j => weight j.val) (fun j => hw j.val) j
  exact add_nonneg (mul_nonneg (by linarith only [hg.2]) hc.le)
    (div_nonneg hg.1 (Nat.cast_nonneg _))

theorem collectionFastMass_sum (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j) (U : SlowSet p) :
    (∑ j : CanonicalFastSampling.FastArm U, collectionFastMass rate anchor weight ha hw U j) = 1 := by
  have hc := FastComplementLocality.localConditionalFastMass_sum_eq_one anchor ha U
    (fun j => weight j.val) (fun j => hw j.val)
  have hcard : Fintype.card (CanonicalFastSampling.FastArm U) = p.K - p.m + 1 := by
    rw [Fintype.card_coe, CanonicalFastSampling.fastArmFinset_card]
  have hd : (((p.K - p.m + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ _))
  simp only [collectionFastMass]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hc, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  field_simp [hd]
  ring

/-- Internal comparison under an explicit weight envelope. This does not
establish the envelope on an actual generated collection segment. -/
theorem collectionFastMass_eq_qGamma (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j)
    (hlo : ∀ j, anchor j ≤ weight j) (hhi : ∀ j, weight j ≤ 2 * anchor j)
    (U : SlowSet p) (j : CanonicalFastSampling.FastArm U) :
    collectionFastMass rate anchor weight ha hw U j =
      CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property rate.sourceCap
        anchor weight ha hw hlo hhi U j := by
  exact FastComplementLocality.localFastLaw_eq_qGamma p rate.eta.property rate.sourceCap
    anchor weight ha hw hlo hhi U j

def collectionFastDraw (anchor weight : Fin p.K → ℝ)
    (ha : ∀ j, 0 < anchor j) (hw : ∀ j, 0 < weight j)
    (U : SlowSet p) (x : ContinuousControlSlice.Scalar) : CanonicalFastSampling.FastArm U :=
  CanonicalFastSampling.fastArmOrderIso U (ContinuousCategorical.sample (Nat.zero_lt_succ _)
    (fun k => collectionFastMass rate anchor weight ha hw U (CanonicalFastSampling.fastArmOrderIso U k))
    (by
      calc
        _ = ∑ j : CanonicalFastSampling.FastArm U, collectionFastMass rate anchor weight ha hw U j :=
          Equiv.sum_comp (CanonicalFastSampling.fastArmOrderIso U).toEquiv _
        _ = 1 := collectionFastMass_sum rate anchor weight ha hw U) x)

/-- A literal actual collection date. Both the numerical slot and the
collection-call arguments must be present; no default payload is installed. -/
def collectionDateDomain (q : Fin p.T) : Set (BootstrapPrivateRoundStreams.SourceInput p) :=
  {z | ∃ r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate,
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).isSome = true ∧
      (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r).isSome = true}

abbrev CollectionDateSource (q : Fin p.T) :=
  ↥(collectionDateDomain rate rewards C_star C_h q)

def collectionRecord (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    ReferenceFirstLiveChronologicalPrefixFoundation.Record rate := z.property.choose

theorem collectionRecord_spec (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val =
        some (collectionRecord rate rewards C_star C_h q z) ∧
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (collectionRecord rate rewards C_star C_h q z)).isSome = true ∧
      (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
        (collectionRecord rate rewards C_star C_h q z)).isSome = true := z.property.choose_spec

/-- Produce the domain from the actual record's collection readout. -/
theorem collectionDateDomain_of_readout (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c) :
    z ∈ collectionDateDomain rate rewards C_star C_h q := by
  obtain ⟨_whole, _past, _k, P, ledger, started, weights, _hm, _hp, _hpre, _hr, hnum, hcall, _⟩ :=
    ReferenceFirstCollectionWeightEnvelope.actual_collection_readout_source_prefix
      rewards C_star C_h z q r hr c hc
  refine ⟨r, hr, ?_, ?_⟩
  · rw [hnum]
    rfl
  · rw [hcall]
    rfl

def collectionInput (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    RecordedQueueRun.RoundInput p.K :=
  (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
    (collectionRecord rate rewards C_star C_h q z)).get
      (collectionRecord_spec rate rewards C_star C_h q z).2.1

def collectionArguments (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :=
  (ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
    (collectionRecord rate rewards C_star C_h q z)).get
      (collectionRecord_spec rate rewards C_star C_h q z).2.2

theorem collectionArguments_spec (q : Fin p.T)
    (z : CollectionDateSource rate rewards C_star C_h q) :
    ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
      (collectionRecord rate rewards C_star C_h q z) =
        some (collectionArguments rate rewards C_star C_h q z) := (Option.some_get _).symm

/-- Collection always uses the payload already stored in the actual input.
The cutoff cell and the continuing collection constructor have the same rule. -/
private theorem collectionCall_oldPayload
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (args : (payload : ReferenceActivePhysicalStep.Payload rate) ×
      ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
      (CanonicalFastSampling.FastArm payload.slowSet → ℝ))
    (hc : ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 r = some args) :
    ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator = some args.1 := by
  have hp : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  by_cases ho : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied r
  · simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, ite_eq_left ho, hp] at hc
    cases hs : r.input.state.coordinator with
    | first =>
        have hd := ReferenceActivePhysicalStep.dispatch_first r.input hs
        rw [hd] at hc
        cases he : CoordinatorRoundDispatch.dispatchFirst (ReferenceActivePhysicalStep.firstInput r.input)
          <;> rw [he] at hc <;> cases hc
    | dagger =>
        simp only [ReferenceActivePhysicalStep.dispatch, hs] at hc
        cases hc
    | live regs owned base =>
        have hd : ReferenceActivePhysicalStep.dispatch r.input = .live regs owned base
            (CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput r.input regs owned base)) := by
          simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch]
          rfl
        rw [hd] at hc
        cases he : CoordinatorRoundDispatch.dispatchLive (ReferenceActivePhysicalStep.liveInput r.input regs owned base)
          <;> simp only [he, reduceCtorEq] at hc
        split_ifs at hc with hsig
        exact congrArg some (congrArg Sigma.fst (Option.some.inj hc))
    | collection payload ledger saved =>
        by_cases hrange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
        · let u : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
          let x := ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock u
          have hd : ReferenceActivePhysicalStep.dispatch r.input = .collection payload ledger clock u
              (CoordinatorRoundDispatch.dispatchCollection x) := by
            simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_left hrange,
              CoordinatorRoundDispatch.dispatch]
            rfl
          rw [hd] at hc
          cases he : CoordinatorRoundDispatch.dispatchCollection x <;> simp only [he, reduceCtorEq] at hc
          exact congrArg some (congrArg Sigma.fst (Option.some.inj hc))
        · simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_right hrange] at hc
          cases hc
  · simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, ite_eq_right ho] at hc
    cases hc

/-- No fresh or unit anchor is manufactured on a later collection date. -/
theorem collectionArguments_incoming (q : Fin p.T)
    (z : CollectionDateSource rate rewards C_star C_h q) :
    ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q z.val =
      some (collectionArguments rate rewards C_star C_h q z).1 := by
  rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?,
    (collectionRecord_spec rate rewards C_star C_h q z).1, Option.bind_some]
  exact collectionCall_oldPayload rate _ _ (collectionArguments_spec rate rewards C_star C_h q z)

theorem collection_launch (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z.val rewards C_star C_h = some active :=
  actualRecord_launch rate rewards C_star C_h q z.val _
    (collectionRecord_spec rate rewards C_star C_h q z).1

def collectionNumericalWord (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    List (RecordedQueueRun.RoundInput p.K) :=
  actualOriginalWord rate rewards C_star C_h z.val (collection_launch rate rewards C_star C_h q z)

def collectionBefore (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    RecordedQueueRun.RunState p.K :=
  RecordedQueueRun.run Q ((collectionNumericalWord rate rewards C_star C_h q z).take
    (q.val - start z.val))

theorem collectionInput_word (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q) :
    ∃ hk : q.val - start z.val < (collectionNumericalWord rate rewards C_star C_h q z).length,
      start z.val ≤ q.val ∧
      collectionInput rate rewards C_star C_h q z =
        (collectionNumericalWord rate rewards C_star C_h q z)[q.val - start z.val] :=
  actualRecord_originalWord rate rewards C_star C_h q z.val _ _
    (collectionRecord_spec rate rewards C_star C_h q z).1 (Option.some_get _).symm
    (collection_launch rate rewards C_star C_h q z)

/-- A later collection cell uses the actual old anchor, inherited incoming
set, actual all-arm numerical update and original physical FAST scalar.
Only PRE overflow suppresses a detecting proposal and residual draw. -/
def laterCollectionCell (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) : LogicalCell p rate :=
  let r := collectionRecord rate rewards C_star C_h q z
  let c := collectionInput rate rewards C_star C_h q z
  let S := collectionBefore rate rewards C_star C_h q z
  let P := (collectionArguments rate rewards C_star C_h q z).1
  let proposed := c.enabled && !S.overflow && decide ((a (q, 0)).val < 4 * p.m * rate.eta.val)
  { time := q
    physical := ReferenceActiveHorizonMeasurability.roundRecordCode r
    numerical := ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c
    before := S
    after := RecordedQueueRun.step Q S c
    arrivals := RecordedQueueRun.acceptedRecord Q S c
    service := fun j => RecordedQueueRun.recordService (4 * (Q).n) (S.registers j)
      (RecordedQueueRun.acceptedRecord Q S c j)
    slowSet := if S.overflow then frozenSlowSet p else U
    fastArm := if S.overflow then frozenFastArm p else
      (collectionFastDraw rate P.anchor (RecordedQueueRun.scoreWeight Q S) P.anchor_pos
        (RecordedSlowRefresh.scoreWeight_pos Q S) U
        (ReferenceSourceFastScalarDisintegration.sourceFastScalar p q z.val)).val
    proposal := proposed
    nextSlowSet := if S.overflow then frozenSlowSet p else
      if proposed then residualDraw rate S c P.anchor P.anchor_pos (a (q, 1)) else U }

/-- Append a logical cell exactly on enabled dates. -/
def laterCollectionCell? (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q)
    (U : SlowSet p) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    Option (LogicalCell p rate) :=
  if (collectionInput rate rewards C_star C_h q z).enabled then
    some (laterCollectionCell rate rewards C_star C_h q z U a) else none

theorem laterCollectionCell_auxiliary_ext (q : Fin p.T)
    (z : CollectionDateSource rate rewards C_star C_h q) (U : SlowSet p)
    (a b : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (h0 : a (q, 0) = b (q, 0)) (h1 : a (q, 1) = b (q, 1)) :
    laterCollectionCell rate rewards C_star C_h q z U a =
      laterCollectionCell rate rewards C_star C_h q z U b := by
  simp only [laterCollectionCell, h0, h1]

theorem laterCollectionCell_after (q : Fin p.T)
    (z : CollectionDateSource rate rewards C_star C_h q) (U : SlowSet p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    (laterCollectionCell rate rewards C_star C_h q z U a).after =
      RecordedQueueRun.run Q ((collectionNumericalWord rate rewards C_star C_h q z).take
        (q.val + 1 - start z.val)) := by
  obtain ⟨hk, hsq, hc⟩ := collectionInput_word rate rewards C_star C_h q z
  change RecordedQueueRun.step Q (collectionBefore rate rewards C_star C_h q z)
    (collectionInput rate rewards C_star C_h q z) = _
  rw [collectionBefore, hc, Nat.sub_add_comm hsq, ← List.take_append_getElem hk,
    RecordedSlowRefresh.run_append_singleton]

end LaterCollection

section ContinuingLive

abbrev ContinuingLiveSource (q : Fin p.T) :=
  ↥(ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q)

def continuingRecord (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :=
  (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_physical
    rate rewards C_star C_h q z.val z.property).choose

def continuingInput (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :=
  (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_physical
    rate rewards C_star C_h q z.val z.property).choose_spec.choose

def continuingSourceCell (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :
    ReferenceFirstWindowNumericalStream.ActualLiveSourceCell
      (continuingRecord rate rewards C_star C_h q z) :=
  (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_physical
    rate rewards C_star C_h q z.val z.property).choose_spec.choose_spec.choose

theorem continuingSourceCell_spec (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z.val =
        some (continuingRecord rate rewards C_star C_h q z) ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0
        (continuingRecord rate rewards C_star C_h q z) =
          some (continuingInput rate rewards C_star C_h q z) ∧
      (continuingSourceCell rate rewards C_star C_h q z).input =
        continuingInput rate rewards C_star C_h q z := by
  have hs := (ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_physical
    rate rewards C_star C_h q z.val z.property).choose_spec.choose_spec.choose_spec
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem continuingRecord_time (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q) :
    (continuingRecord rate rewards C_star C_h q z).input.time = q :=
  (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields rate rewards C_star C_h q z.val
    (continuingRecord rate rewards C_star C_h q z)
    (continuingSourceCell_spec rate rewards C_star C_h q z).1).2.2.1

theorem continuing_launch (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :
    ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z.val rewards C_star C_h = some active :=
  actualRecord_launch rate rewards C_star C_h q z.val _
    (continuingSourceCell_spec rate rewards C_star C_h q z).1

def continuingNumericalWord (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :=
  actualOriginalWord rate rewards C_star C_h z.val (continuing_launch rate rewards C_star C_h q z)

/-- Complete calendar PRE, including all disabled dates. -/
def continuingBefore (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q) :=
  RecordedQueueRun.run Q ((continuingNumericalWord rate rewards C_star C_h q z).take
    (q.val - start z.val))

def continuingLogicalCell (q : Fin p.T) (z : ContinuingLiveSource rate rewards C_star C_h q)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) : LogicalCell p rate :=
  appendLogicalCell (continuingRecord rate rewards C_star C_h q z)
    (continuingSourceCell rate rewards C_star C_h q z)
    (continuingBefore rate rewards C_star C_h q z) a

/-- The native continuing cell belongs to its own original calendar word,
including the first detecting update and all-arm accepted arrivals/service. -/
theorem continuingLogicalCell_word (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    let W := continuingNumericalWord rate rewards C_star C_h q z
    let e := continuingLogicalCell rate rewards C_star C_h q z a
    e.time = q ∧ e.before = RecordedQueueRun.run Q (W.take (q.val - start z.val)) ∧
      e.after = RecordedQueueRun.run Q (W.take (q.val + 1 - start z.val)) ∧
      ∃ hk : q.val - start z.val < W.length,
        e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates W[q.val - start z.val] ∧
        e.arrivals = RecordedQueueRun.acceptedRecord Q e.before W[q.val - start z.val] ∧
        e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n)
          (e.before.registers j) (e.arrivals j) := by
  dsimp only
  have hs := continuingSourceCell_spec rate rewards C_star C_h q z
  have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
      (continuingRecord rate rewards C_star C_h q z) =
        some (continuingSourceCell rate rewards C_star C_h q z).input := by
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hs.2.1, Option.some_or, hs.2.2]
  obtain ⟨hk, hsq, hc⟩ := actualRecord_originalWord rate rewards C_star C_h q z.val _ _ hs.1 hcell
    (continuing_launch rate rewards C_star C_h q z)
  change q.val - start z.val < (continuingNumericalWord rate rewards C_star C_h q z).length at hk
  change (continuingSourceCell rate rewards C_star C_h q z).input =
    (continuingNumericalWord rate rewards C_star C_h q z)[q.val - start z.val] at hc
  refine ⟨continuingRecord_time rate rewards C_star C_h q z, rfl, ?_, hk, ?_, ?_, rfl⟩
  · change RecordedQueueRun.step Q (continuingBefore rate rewards C_star C_h q z)
      (continuingSourceCell rate rewards C_star C_h q z).input = _
    rw [continuingBefore, hc, Nat.sub_add_comm hsq, ← List.take_append_getElem hk,
      RecordedSlowRefresh.run_append_singleton]
  · change ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates
      (continuingSourceCell rate rewards C_star C_h q z).input = _
    rw [hc]
  · change RecordedQueueRun.acceptedRecord Q _
      (continuingSourceCell rate rewards C_star C_h q z).input = _
    rw [hc]
    rfl

theorem continuingLogicalCell_auxiliary_ext (q : Fin p.T)
    (z : ContinuingLiveSource rate rewards C_star C_h q)
    (a b : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hab : a (q, 1) = b (q, 1)) :
    continuingLogicalCell rate rewards C_star C_h q z a =
      continuingLogicalCell rate rewards C_star C_h q z b := by
  simp only [continuingLogicalCell, appendLogicalCell,
    continuingRecord_time rate rewards C_star C_h q z, hab]

end ContinuingLive

section ReentryCalendar

/-- The actual same-source cell at a noninvocation date. The inherited seed
is used only during collection; LIVE uses the accepted physical cell producer. -/
def noncallDateCell (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (U : SlowSet p) :
    Option (LogicalCell p rate) :=
  if h : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q then
    some (continuingLogicalCell rate rewards C_star C_h q ⟨z, h⟩ a)
  else if h : z ∈ collectionDateDomain rate rewards C_star C_h q then
    laterCollectionCell? rate rewards C_star C_h q ⟨z, h⟩ U a
  else none

private theorem live_noncall_incoming
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (hlive : ReferenceLaterLiveNumericalReadout.laterLiveDomain 0 r)
    (hnf : r.input.state.coordinator ≠ .first)
    (hnd : r.input.state.coordinator ≠ .dagger)
    (hparam : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none) :
    ∃ regs owned base, r.input.state.coordinator = .live regs owned base := by
  obtain ⟨selected, hsel, _hsigma, hactive, _ho⟩ := hlive
  cases hs : r.input.state.coordinator with
  | first => exact (hnf hs).elim
  | dagger => exact (hnd hs).elim
  | live regs owned base => exact ⟨regs, owned, base, rfl⟩
  | collection payload ledger saved =>
      by_cases hc : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let u : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
        let x := ReferenceActivePhysicalStep.collectionInput r.input payload ledger clock u
        have hp : r.output.preparation.coordinator = .collection payload ledger clock u
            (CoordinatorRoundDispatch.dispatchCollection x) := by
          rw [r.output_eq]
          change ReferenceActivePhysicalStep.dispatch r.input = _
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_left hc,
            CoordinatorRoundDispatch.dispatch]
          rfl
        have hf := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
        rw [hp] at hsel hf
        cases hd : CoordinatorRoundDispatch.dispatchCollection x <;> rw [hd] at hsel hf <;>
          try cases hsel
        · have he := Option.some.inj hsel
          exact (hf.1 (by simpa only [← he] using hactive)).elim
        · have hl : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
            unfold ReferenceCollectionPhaseHistory.laterChosen
            have hprep : (ReferenceActivePhysicalStep.prepare r.input).coordinator =
                r.output.preparation.coordinator := by rw [r.output_eq]; rfl
            rw [hprep, hp, hd]
          have hsome := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
            r.input hl
          change (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true at hsome
          rw [hparam] at hsome
          cases hsome
      · have hp : r.output.preparation.coordinator = .invalidCollectionCutoff := by
          rw [r.output_eq]
          change ReferenceActivePhysicalStep.dispatch r.input = _
          simp only [ReferenceActivePhysicalStep.dispatch, hs, dite_eq_right hc]
        rw [hp] at hsel
        cases hsel

private theorem birth_first_or_call
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (P : ReferenceActivePhysicalStep.Payload rate)
    (hbirth : ReferenceAssignmentPayloadPersistence.InstallationBirth r P) :
    r.input.state.coordinator = .first ∨
      (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true := by
  have hp : r.output.preparation.coordinator = ReferenceActivePhysicalStep.dispatch r.input := by
    rw [r.output_eq]
    rfl
  cases hc : r.output.preparation.coordinator with
  | first outcome =>
      left
      have hd := hp.symm.trans hc
      cases hs : r.input.state.coordinator with
      | first => rfl
      | live regs owned base =>
          simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at hd
          cases hd
      | collection payload ledger saved =>
          simp only [ReferenceActivePhysicalStep.dispatch, hs, CoordinatorRoundDispatch.dispatch] at hd
          split at hd <;> cases hd
      | dagger => simp only [ReferenceActivePhysicalStep.dispatch, hs, reduceCtorEq] at hd
  | collection payload ledger clock cutoff outcome =>
      cases outcome <;>
        simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
      right
      apply ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
      unfold ReferenceCollectionPhaseHistory.laterChosen
      rw [(ReferenceActivePhysicalStep.prepare r.input).coordinator_eq, ← hp, hc]
  | live regs owned base outcome =>
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
  | invalidCollectionCutoff =>
      simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth
  | dagger => simp only [ReferenceAssignmentPayloadPersistence.InstallationBirth, hc] at hbirth

private theorem record_noncall_payload
    (r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate)
    (hnf : r.input.state.coordinator ≠ .first)
    (hparam : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none)
    (hpresent : ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator ≠ none) :
    ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator =
      ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator := by
  rcases r with ⟨x, y, hy⟩
  subst y
  rcases ReferenceAssignmentPayloadChronology.actualStep_payload_classification x with hn | ho | hb
  · exact (hpresent hn).elim
  · obtain ⟨P, hin, hout⟩ := ho
    exact hout.trans hin.symm
  · obtain ⟨P, hbirth, _⟩ := hb
    rcases birth_first_or_call rate (ReferenceAssignmentPayloadChronology.actualStepRecord x) P hbirth with hf | hc
    · exact (hnf hf).elim
    · change (ReferenceLaterSamplerParameterMeasurability.parameters? x).isSome = true at hc
      rw [hparam] at hc
      cases hc

/-- Every actual noncall date strictly after launch has a native LIVE cell or
an actual old-payload collection cell. This includes disabled collection dates. -/
theorem noncall_phase_coverage (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hs : start z < q.val)
    (hcall : noCallAt rate rewards C_star C_h q z) :
    z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain rate rewards C_star C_h q ∨
      z ∈ collectionDateDomain rate rewards C_star C_h q := by
  let R := completeSuffixRecords rate z rewards C_star C_h
  have hk : q.val - start z < R.length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hq := q.isLt
    omega
  let k : Fin R.length := ⟨q.val - start z, hk⟩
  let r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate := R[k.val]
  have hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r := by
    rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hs.le]
    exact List.getElem?_eq_getElem hk
  have hall := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1
  have hnfirst : r.input.state.coordinator ≠ .first := by
    let j : Fin R.length := ⟨k.val - 1, by dsimp [k]; omega⟩
    have hj : j.val + 1 < R.length := by dsimp [j, k]; omega
    have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      (rate := rate) rewards C_star C_h z j.val hj
    have hindex : j.val + 1 = k.val := by dsimp [j, k]; omega
    have hcoord := congrArg ReferenceActivePhysicalStep.State.coordinator hadj
    intro hfirst
    apply (hall j).2.2.2.1
    exact hcoord.symm.trans (by simpa only [hindex] using hfirst)
  have hparam : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
    change (match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z with
      | none => True | some record => ReferenceFirstCollectionSamplerCall.collectionCallAt record = none) at hcall
    rw [hr] at hcall
    exact (ReferenceFirstCollectionSamplerCall.collectionCallAt_none_iff r).mp hcall
  rcases (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z k).2 with hlive | ⟨c, hc⟩
  · exact Or.inl ⟨r, hr, live_noncall_incoming rate r hlive hnfirst (hall k).1 hparam,
      (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain 0 r).mpr hlive⟩
  · exact Or.inr (collectionDateDomain_of_readout rate rewards C_star C_h q z r hr c hc)

/-- Every noncall transition retains the actual physical payload, including
cutoff, disabled collection, and post-overflow physical continuation. -/
theorem noncall_payload_step (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hs : start z < q.val)
    (hcall : noCallAt rate rewards C_star C_h q z) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
        (fun r => ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator) =
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q z := by
  obtain ⟨r, hr, hnf⟩ : ∃ r : ReferenceFirstLiveChronologicalPrefixFoundation.Record rate,
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
        r.input.state.coordinator ≠ .first := by
    rcases noncall_phase_coverage rate rewards C_star C_h q z hs hcall with hl | hc
    · obtain ⟨r, hr, ⟨regs, owned, base, hin⟩, _⟩ := hl
      exact ⟨r, hr, by rw [hin]; intro hf; cases hf⟩
    · let d : CollectionDateSource rate rewards C_star C_h q := ⟨z, hc⟩
      refine ⟨collectionRecord rate rewards C_star C_h q d,
        (collectionRecord_spec rate rewards C_star C_h q d).1, ?_⟩
      have hp := collectionCall_oldPayload rate _ _ (collectionArguments_spec rate rewards C_star C_h q d)
      intro hf
      rw [hf, ReferenceAssignmentPayloadPersistence.storedPayload_first] at hp
      cases hp
  have hparam : ReferenceLaterSamplerParameterMeasurability.parameters? r.input = none := by
    unfold noCallAt at hcall
    rw [hr] at hcall
    exact (ReferenceFirstCollectionSamplerCall.collectionCallAt_none_iff r).mp hcall
  obtain ⟨k, hk⟩ := ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecord_suffix_index
    rate rewards C_star C_h q z r hr
  have hall := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 k
  rw [hk] at hall
  have hpresent : ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator ≠ none := by
    cases hc : r.output.next.coordinator with
    | first => exact (hall.2.2.2.1 hc).elim
    | dagger => exact (hall.2.2.2.2 hc).elim
    | live regs owned base => exact Option.some_ne_none _
    | collection payload ledger saved => exact Option.some_ne_none _
  rw [ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?, hr, Option.bind_some]
  exact record_noncall_payload rate r hnf hparam hpresent

/-- The entire old physical payload is inherited from the actual produced
installation's POST up to the PRE-call boundary. Its logical slow set is not
asserted equal to this physical payload during collection. -/
theorem noCallBetween_payload (t : Fin p.T) (n : Fin (p.T + 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hst : start z ≤ t.val)
    (hcall : NoCallBetween rate rewards C_star C_h t n z)
    (q : Fin p.T) (htq : t.val < q.val) (hqn : q.val ≤ n.val) :
    ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h q z =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
        (fun r => ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator) := by
  have h : ∀ m (hm : m < p.T), t.val < m → m ≤ n.val →
      ReferenceFirstCollectionOldRecorderFoundation.incomingPayload? rate rewards C_star C_h ⟨m, hm⟩ z =
        (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
          (fun r => ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator) := by
    intro m
    induction m with
    | zero => intros; omega
    | succ m ih =>
        intro hm htm hmn
        let prev : Fin p.T := ⟨m, by omega⟩
        have hsm : start z ≤ m := by omega
        have hnext : ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
            rate rewards C_star C_h ⟨m + 1, hm⟩ z =
            (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h prev z).bind
              (fun r => ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator) := by
          have hi : m - start z + 1 < (completeSuffixRecords rate z rewards C_star C_h).length := by
            rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
            omega
          have he : m + 1 - start z = m - start z + 1 := by omega
          have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
            (rate := rate) rewards C_star C_h z (m - start z) hi
          unfold ReferenceFirstCollectionOldRecorderFoundation.incomingPayload?
            ReferenceSourcePrefixHistoryFiltration.actualRecord
          rw [ite_eq_left (by omega : start z ≤ m + 1), ite_eq_left hsm, he,
            List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega : m - start z <
              (completeSuffixRecords rate z rewards C_star C_h).length), Option.bind_some, Option.bind_some]
          exact congrArg (fun S : ReferenceActivePhysicalStep.State p rate =>
            ReferenceAssignmentPayloadPersistence.storedPayload S.coordinator) hadj
        rw [hnext]
        by_cases hlt : t.val < m
        · rw [noncall_payload_step rate rewards C_star C_h prev z (by dsimp [prev]; omega)
            (hcall prev hlt (by dsimp [prev]; omega))]
          exact ih (by omega) hlt (by omega)
        · have he : prev = t := Fin.ext (by dsimp [prev]; omega)
          rw [he]
  exact h q.val q.isLt htq hqn

/-- A later collection's whole old payload, including its anchor, comes
from the actual invocation POST on this very source. -/
theorem collectionArguments_inherits_post (t : Fin p.T) (n : Fin (p.T + 1))
    (q : Fin p.T) (z : CollectionDateSource rate rewards C_star C_h q)
    (hst : start z.val ≤ t.val) (htq : t.val < q.val) (hqn : q.val ≤ n.val)
    (hcall : NoCallBetween rate rewards C_star C_h t n z.val) :
    some (collectionArguments rate rewards C_star C_h q z).1 =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z.val).bind
        (fun r => ReferenceAssignmentPayloadPersistence.storedPayload r.output.next.coordinator) :=
  (collectionArguments_incoming rate rewards C_star C_h q z).symm.trans
    (noCallBetween_payload rate rewards C_star C_h t n z.val hst hcall q htq hqn)

/-- On an actual noncall path, absence means disabled, including when an
enabled recorder returns the bottom marker or zero accepted arrivals. -/
theorem noncallDateCell_presence (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (hs : start z < q.val)
    (hcall : noCallAt rate rewards C_star C_h q z)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (U : SlowSet p) :
    (noncallDateCell rate rewards C_star C_h q z a U).isSome =
      ((ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z).bind
        (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).any
          RecordedQueueRun.RoundInput.enabled := by
  have hcover := noncall_phase_coverage rate rewards C_star C_h q z hs hcall
  unfold noncallDateCell
  split
  next h =>
    have hc := continuingSourceCell_spec rate rewards C_star C_h q ⟨z, h⟩
    rw [hc.1, Option.bind_some, ReferenceFirstCollectionCurrentRetainedGate.cell0,
      hc.2.1, Option.some_or]
    have hen := (continuingSourceCell rate rewards C_star C_h q ⟨z, h⟩).enabled
    rw [← hc.2.2, Option.any_some, hen]
    rfl
  next h =>
    have hcollection := hcover.resolve_left h
    rw [dite_eq_left hcollection]
    have hc := collectionRecord_spec rate rewards C_star C_h q ⟨z, hcollection⟩
    have hinput : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (collectionRecord rate rewards C_star C_h q ⟨z, hcollection⟩) =
          some (collectionInput rate rewards C_star C_h q ⟨z, hcollection⟩) := (Option.some_get _).symm
    rw [hc.1, Option.bind_some, hinput, Option.any_some]
    unfold laterCollectionCell?
    cases hen : (collectionInput rate rewards C_star C_h q ⟨z, hcollection⟩).enabled <;>
      simp only [Bool.false_eq_true, ite_true, ite_false, Option.isSome_some, Option.isSome_none]

/-- Every appended cell uses its actual calendar record and complete stopped
numerical prefix. A disabled gap can never be replaced by the last cell's POST. -/
theorem noncallDateCell_actualWord (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hl : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) (U : SlowSet p)
    (e : LogicalCell p rate) (he : noncallDateCell rate rewards C_star C_h q z a U = some e) :
    let W := actualOriginalWord rate rewards C_star C_h z hl
    e.time = q ∧ e.before = RecordedQueueRun.run Q (W.take (q.val - start z)) ∧
      e.after = RecordedQueueRun.run Q (W.take (q.val + 1 - start z)) ∧
      ∃ r c, ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h q z = some r ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c ∧ c.enabled = true ∧
        e.physical = ReferenceActiveHorizonMeasurability.roundRecordCode r ∧
        e.numerical = ReferenceLaterCollectionSourceReadoutMeasurability.numericalCoordinates c ∧
        e.arrivals = RecordedQueueRun.acceptedRecord Q e.before c ∧
        e.service = fun j => RecordedQueueRun.recordService (4 * (Q).n)
          (e.before.registers j) (e.arrivals j) := by
  unfold noncallDateCell at he
  split at he
  next h =>
    have he' := Option.some.inj he
    rw [← he']
    have hc := continuingSourceCell_spec rate rewards C_star C_h q ⟨z, h⟩
    have hw := continuingLogicalCell_word rate rewards C_star C_h q ⟨z, h⟩ a
    refine ⟨hw.1, hw.2.1, hw.2.2.1, _, _, hc.1, ?_,
      (continuingSourceCell rate rewards C_star C_h q ⟨z, h⟩).enabled, rfl, rfl, rfl, rfl⟩
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hc.2.1, Option.some_or, hc.2.2]
  next _ =>
    split at he
    next h =>
      unfold laterCollectionCell? at he
      split at he
      next hen =>
        have he' := Option.some.inj he
        rw [← he']
        have hc := collectionRecord_spec rate rewards C_star C_h q ⟨z, h⟩
        refine ⟨rfl, rfl, laterCollectionCell_after rate rewards C_star C_h q ⟨z, h⟩ U a,
          _, _, hc.1, (Option.some_get _).symm, hen, rfl, rfl, rfl, rfl⟩
      next _ => cases he
    next _ => cases he

/-- Disabled dates retain the logical seed and list. Numerical completion is
read separately from the whole calendar word, never from the last list entry. -/
def appendNoncallDate (q : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (s : SlowSet p × List (LogicalCell p rate)) : SlowSet p × List (LogicalCell p rate) :=
  match noncallDateCell rate rewards C_star C_h q z a s.1 with
  | none => s
  | some c => (c.nextSlowSet, s.2 ++ [c])

/-- Calendar recursion killed BEFORE an actual invocation. An outer `none`
is the killed path, distinct from a disabled date's absent logical cell. -/
def noncallCalendar (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (initial : SlowSet p × List (LogicalCell p rate)) :
    ℕ → Option (SlowSet p × List (LogicalCell p rate))
  | 0 => some initial
  | k + 1 =>
      (noncallCalendar t z a initial k).bind fun s =>
        if h : t.val < k ∧ k < p.T then
          if noCallAt rate rewards C_star C_h ⟨k, h.2⟩ z then
            some (appendNoncallDate rate rewards C_star C_h ⟨k, h.2⟩ z a s)
          else none
        else some s

theorem noncallCalendar_initial (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (initial : SlowSet p × List (LogicalCell p rate)) (k : ℕ) (hk : k ≤ t.val + 1) :
    noncallCalendar rate rewards C_star C_h t z a initial k = some initial := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [noncallCalendar, ih (by omega), Option.bind_some, dite_eq_right (by omega)]

theorem noncallCalendar_isSome (t : Fin p.T) (n : Fin (p.T + 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (initial : SlowSet p × List (LogicalCell p rate)) :
    (noncallCalendar rate rewards C_star C_h t z a initial n.val).isSome = true ↔
      NoCallBetween rate rewards C_star C_h t n z := by
  have h : ∀ k (hk : k ≤ p.T),
      (noncallCalendar rate rewards C_star C_h t z a initial k).isSome = true ↔
        NoCallBetween rate rewards C_star C_h t ⟨k, by omega⟩ z := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp only [noncallCalendar, Option.isSome_some, true_iff]
        intro q _ hq
        exact (Nat.not_lt_zero _ hq).elim
    | succ k ih =>
        intro hk
        let q : Fin p.T := ⟨k, by omega⟩
        have hs := noCallBetween_succ rate rewards C_star C_h t q z
        have hi := ih (by omega)
        change _ ↔ NoCallBetween rate rewards C_star C_h t q.succ z
        rw [hs]
        change _ ↔ NoCallBetween rate rewards C_star C_h t ⟨k, by omega⟩ z ∧
          (t.val < k → noCallAt rate rewards C_star C_h q z)
        rw [← hi, noncallCalendar]
        cases he : noncallCalendar rate rewards C_star C_h t z a initial k with
        | none =>
            simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_and]
        | some s =>
            simp only [Option.bind_some, Option.isSome_some, true_and]
            by_cases htk : t.val < k
            · rw [dite_eq_left ⟨htk, by omega⟩]
              by_cases hc : noCallAt rate rewards C_star C_h q z <;>
                simp only [q, hc, ite_true, ite_false, Option.isSome_some,
                  Option.isSome_none, Bool.false_eq_true, htk, true_implies]
            · rw [dite_eq_right (by omega)]
              simp only [Option.isSome_some, htk, false_implies]
  exact h n.val (Nat.le_of_lt_succ n.isLt)

theorem noncallDateCell_auxiliary_ext (q : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (U : SlowSet p)
    (a b : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (h0 : a (q, 0) = b (q, 0)) (h1 : a (q, 1) = b (q, 1)) :
    noncallDateCell rate rewards C_star C_h q z a U =
      noncallDateCell rate rewards C_star C_h q z b U := by
  unfold noncallDateCell
  split
  · exact congrArg some (continuingLogicalCell_auxiliary_ext rate rewards C_star C_h q _ a b h1)
  · split
    · unfold laterCollectionCell?
      rw [laterCollectionCell_auxiliary_ext rate rewards C_star C_h q _ U a b h0 h1]
    · rfl

/-- The complete recursion retains the whole prior list and uses no auxiliary
coordinate at or after its PRE boundary. -/
theorem noncallCalendar_auxiliary_ext (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (a b : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (initial : SlowSet p × List (LogicalCell p rate)) (k : ℕ)
    (hab : ∀ q : Fin p.T, t.val < q.val → q.val < k → ∀ l : Fin 2, a (q, l) = b (q, l)) :
    noncallCalendar rate rewards C_star C_h t z a initial k =
      noncallCalendar rate rewards C_star C_h t z b initial k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [noncallCalendar, noncallCalendar, ih (fun q ht hq l => hab q ht (by omega) l)]
      congr 1
      funext s
      split
      next h =>
        split
        · unfold appendNoncallDate
          rw [noncallDateCell_auxiliary_ext rate rewards C_star C_h ⟨k, h.2⟩ z s.1 a b
            (hab ⟨k, h.2⟩ h.1 (by change k < k + 1; omega) 0)
            (hab ⟨k, h.2⟩ h.1 (by change k < k + 1; omega) 1)]
        · rfl
      · rfl

/-- The root prefix starts from the native produced append and residual seed.
Its source is exactly the inserted source carried by the transition. -/
def postInvocationPrefix (t : Fin p.T) (n : Fin (p.T + 1))
    (d : TransitionData rate t) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :=
  noncallCalendar rate rewards C_star C_h t (insertedPhysicalSource rate d) a
    (postSeed rate d, postHistory d) n.val

/-- Numerical completion at the PRE boundary includes every physical date. -/
def prefixNumerical (n : Fin (p.T + 1)) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    Option (RecordedQueueRun.RunState p.K) :=
  (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs rate rewards C_star C_h n.val z).map
    (RecordedQueueRun.run Q)

theorem prefixNumerical_actualWord (n : Fin (p.T + 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : ∃ active, ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active) (hsn : start z ≤ n.val) :
    prefixNumerical rate rewards C_star C_h n z = some (RecordedQueueRun.run Q
      ((actualOriginalWord rate rewards C_star C_h z hz).take (n.val - start z))) := by
  rw [prefixNumerical, (originalWord_calendar_prefix rate rewards C_star C_h z hz n hsn).2.2,
    Option.map_some]

end ReentryCalendar

section InitialObservation

/-- Every auxiliary coordinate through the produced installation date.
This retains both current labels, including renewal's already used draw. -/
abbrev UsedAuxiliaryIndex (t : Fin p.T) :=
  {i : Fin p.T × Fin 2 // i.1.val ≤ t.val}

def usedAuxiliary (t : Fin p.T) (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    UsedAuxiliaryIndex t → ContinuousControlSlice.Scalar := fun i => a i.val

theorem measurable_usedAuxiliary (t : Fin p.T) : Measurable (usedAuxiliary (p := p) t) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply i.val)

/-- Joint initial readout on the literal lift, rather than on `TransitionData`:
the consumed scalar remains present here because it is read from that lift's
original array. Full original and inserted physical sources retain private J. -/
abbrev InitialObservation (rate : ReferenceActivePhysicalStep.RateInput p) (t : Fin p.T) :=
  (((BootstrapPrivateRoundStreams.SourceInput p × BootstrapPrivateRoundStreams.SourceInput p) ×
    AssignmentParameterFibreKernel.AssignmentVector p) ×
      ((UsedAuxiliaryIndex t → ContinuousControlSlice.Scalar) × List (LogicalCell p rate)))

def nonrenewedInitialObservation (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (wv : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentParameterFibreKernel.AssignmentVector p) : InitialObservation rate t :=
  (((wv.1.1.val, (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val), wv.2),
    (usedAuxiliary t wv.1.2,
      postHistory (nonrenewedTransition rate rewards C_star C_h control0 u t wv)))

def renewedInitialObservation (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift
      rate rewards C_star C_h u t) : InitialObservation rate t :=
  (((wv.1.1.val,
    (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2).val), wv.2),
    (usedAuxiliary t wv.1.2,
      postHistory (renewedTransition rate rewards C_star C_h control0 u t wv)))

theorem measurable_nonrenewedInitialObservation
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    Measurable (nonrenewedInitialObservation rate rewards C_star C_h control0 u t) := by
  have hsource : Measurable (fun wv :
      (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
        ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentParameterFibreKernel.AssignmentVector p => wv.1.1.val) :=
    measurable_subtype_coe.comp measurable_fst.fst
  have hins : Measurable (fun wv :
      (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
        ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
        AssignmentParameterFibreKernel.AssignmentVector p =>
      (nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2).val) :=
    measurable_subtype_coe.comp
    ((measurable_nonrenewedFirstSource rate rewards C_star C_h t u).comp
      (measurable_fst.fst.prodMk measurable_snd))
  have hpast := (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
    rate rewards C_star C_h control0 t.castSucc).comp (hsource.prodMk measurable_fst.snd)
  have hcell := measurable_nonrenewedFirstCell rate rewards C_star C_h control0 t u
  have hhistory := (ReferenceFirstLiveCalendarMarkedTransition.measurable_appendCurrentTag rate).comp
    (hpast.prodMk (measurable_inr.comp hcell))
  exact ((hsource.prodMk hins).prodMk measurable_snd).prodMk
    (((measurable_usedAuxiliary t).comp measurable_fst.snd).prodMk hhistory)

theorem measurable_renewedInitialObservation
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    Measurable (renewedInitialObservation rate rewards C_star C_h control0 u t) := by
  have hsource : Measurable (fun wv :
      ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t =>
        wv.1.1.val) := measurable_subtype_coe.comp measurable_fst.fst
  have hins : Measurable (fun wv :
      ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t =>
      (ReferenceFirstCollectionRenewalVectorInsertion.put rate rewards C_star C_h u t wv.1.1 wv.2).val) :=
    measurable_subtype_coe.comp
    ((ReferenceFirstCollectionRenewalVectorInsertion.measurable_put rate rewards C_star C_h u t).comp
      (measurable_fst.fst.prodMk measurable_snd))
  have hpast := (ReferenceFirstCollectionLogicalPrefixExtension.measurable_extendedPast
    rate rewards C_star C_h control0 t.castSucc).comp (hsource.prodMk measurable_fst.snd)
  have hcell := measurable_renewedFirstCell rate rewards C_star C_h control0 t u
  have hhistory := (ReferenceFirstLiveCalendarMarkedTransition.measurable_appendCurrentTag rate).comp
    (hpast.prodMk (measurable_inr.comp hcell))
  exact ((hsource.prodMk hins).prodMk measurable_snd).prodMk
    (((measurable_usedAuxiliary t).comp measurable_fst.snd).prodMk hhistory)

/-- Unnormalized starting pushforward of the whole produced readout. -/
def nonrenewedPostCellLaw (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    Measure (InitialObservation rate t) :=
  (ReferenceFirstNextInvocationJointLift.nonrenewedLiftLaw rate rewards C_star C_h u t control0).map
    (nonrenewedInitialObservation rate rewards C_star C_h control0 u t)

def renewedPostCellLaw (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    Measure (InitialObservation rate t) :=
  (ReferenceFirstCollectionRenewalInstallationCoupling.renewalLiftLaw rate rewards C_star C_h u t).map
    (renewedInitialObservation rate rewards C_star C_h control0 u t)

abbrev PrefixAuxiliaryIndex (n : Fin (p.T + 1)) :=
  {i : Fin p.T × Fin 2 // i.1.val < n.val}

/-- Full original/inserted sources and J, installed vector, original produced
append, used auxiliary coordinates, completed numerical state and killed list.
The full physical sources here are readouts, not freshness conditioning data. -/
abbrev PrefixObservation (rate : ReferenceActivePhysicalStep.RateInput p)
    (t : Fin p.T) (n : Fin (p.T + 1)) :=
  InitialObservation rate t × ((PrefixAuxiliaryIndex n → ContinuousControlSlice.Scalar) ×
    (Option (RecordedQueueRun.RunState p.K) × Option (SlowSet p × List (LogicalCell p rate))))

def nonrenewedGeneratedObservation (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (n : Fin (p.T + 1))
    (wv : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentParameterFibreKernel.AssignmentVector p) : PrefixObservation rate t n :=
  let d := nonrenewedTransition rate rewards C_star C_h control0 u t wv
  (nonrenewedInitialObservation rate rewards C_star C_h control0 u t wv,
    (fun i => wv.1.2 i.val, (prefixNumerical rate rewards C_star C_h n
      (insertedPhysicalSource rate d), postInvocationPrefix rate rewards C_star C_h t n d wv.1.2)))

def renewedGeneratedObservation (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (n : Fin (p.T + 1))
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    PrefixObservation rate t n :=
  let d := renewedTransition rate rewards C_star C_h control0 u t wv
  (renewedInitialObservation rate rewards C_star C_h control0 u t wv,
    (fun i => wv.1.2 i.val, (prefixNumerical rate rewards C_star C_h n
      (insertedPhysicalSource rate d), postInvocationPrefix rate rewards C_star C_h t n d wv.1.2)))

theorem nonrenewedGeneratedObservation_numerical
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (wv : (ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t ×
      ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) ×
      AssignmentParameterFibreKernel.AssignmentVector p) :
    let z := nonrenewedFirstSource rate rewards C_star C_h t u wv.1.1 wv.2
    let hl := firstCall_launch rate rewards C_star C_h u t z.val
      (firstCall_insertVector_mem rate rewards C_star C_h u t wv.1.1.val wv.1.1.property.1 wv.2)
    (nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n wv).2.2.1 =
      some (RecordedQueueRun.run Q ((actualOriginalWord rate rewards C_star C_h z.val hl).take
        (n.val - start z.val))) := by
  dsimp only
  apply prefixNumerical_actualWord
  have hd := firstCall_dates rate rewards C_star C_h u t _
    (firstCall_insertVector_mem rate rewards C_star C_h u t wv.1.1.val wv.1.1.property.1 wv.2)
  exact hd.1.trans (hd.2.1.le.trans htn.le)

theorem renewedGeneratedObservation_numerical
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val < n.val)
    (wv : ReferenceFirstCollectionRenewalInstallationCoupling.RenewalLift rate rewards C_star C_h u t) :
    let z := (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2
    let hl := firstCall_launch rate rewards C_star C_h u t z.val z.property.1
    (renewedGeneratedObservation rate rewards C_star C_h control0 u t n wv).2.2.1 =
      some (RecordedQueueRun.run Q ((actualOriginalWord rate rewards C_star C_h z.val hl).take
        (n.val - start z.val))) := by
  dsimp only
  apply prefixNumerical_actualWord
  have hd := firstCall_dates rate rewards C_star C_h u t
    (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.val
    (ReferenceFirstCollectionRenewalInstallationCoupling.pair rate rewards C_star C_h u t wv).2.property.1
  exact hd.1.trans (hd.2.1.le.trans htn.le)

end InitialObservation

section FutureAuxiliaryCoordinates

/-- Erase one future coordinate. `proposal = true` exposes label zero by
the accepted two-label reindexing; `false` exposes label one directly. -/
def futureAuxiliarySplit (q : Fin p.T) (proposal : Bool) :
    ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p ≃ᵐ
      Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q × ContinuousControlSlice.Scalar :=
  if proposal then renewalRefreshScalarSplit q else Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit q

theorem futureAuxiliarySplit_measurePreserving (q : Fin p.T) (proposal : Bool) :
    MeasurePreserving (futureAuxiliarySplit (p := p) q proposal)
      (ReferenceFirstCollectionAuxiliarySeeds.auxiliaryUniformLaw p)
      ((Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.erasedAuxiliaryLaw q).prod ContinuousControlSlice.scalarLaw) := by
  cases proposal
  · exact Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.measurePreserving_actualRefreshScalarSplit q
  · exact measurePreserving_renewalRefreshScalarSplit q

theorem futureAuxiliarySplit_other_date (q : Fin p.T) (proposal : Bool)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q) (x y : ContinuousControlSlice.Scalar)
    (v : Fin p.T) (hv : v ≠ q) (l : Fin 2) :
    (futureAuxiliarySplit q proposal).symm (e, x) (v, l) =
      (futureAuxiliarySplit q proposal).symm (e, y) (v, l) := by
  have h0 : (v, l) ≠ (q, (0 : Fin 2)) := fun h => hv (congrArg Prod.fst h)
  have h1 : (v, l) ≠ (q, (1 : Fin 2)) := fun h => hv (congrArg Prod.fst h)
  cases proposal with
  | false =>
      simp only [futureAuxiliarySplit, Bool.false_eq_true, ite_false,
        Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply, Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.insertActualRefreshCoordinate, h1, dite_false]
  | true =>
      change (Equiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => ContinuousControlSlice.Scalar)
        (Equiv.swap (q, 0) (q, 1))).symm ((Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit q).symm (e, x)) (v, l) =
        (Equiv.piCongrLeft (fun _ : Fin p.T × Fin 2 => ContinuousControlSlice.Scalar)
        (Equiv.swap (q, 0) (q, 1))).symm ((Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit q).symm (e, y)) (v, l)
      rw [Equiv.piCongrLeft_symm_apply, Equiv.piCongrLeft_symm_apply,
        Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply, Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.actualRefreshScalarSplit_symm_apply]
      simp only [Equiv.swap_apply_of_ne_of_ne h0 h1, Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.insertActualRefreshCoordinate, h1, dite_false]

theorem futureAuxiliarySplit_restore (q : Fin p.T) (proposal : Bool)
    (a : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p) :
    (futureAuxiliarySplit q proposal).symm (futureAuxiliarySplit q proposal a) = a :=
  (futureAuxiliarySplit q proposal).symm_apply_apply a

/-- The complete produced post-history is already determined by the erased
observer when the exposed coordinate is strictly after the installation. -/
theorem nonrenewed_postHistory_futureAuxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (proposal : Bool)
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (x y : ContinuousControlSlice.Scalar) :
    postHistory (nonrenewedTransition rate rewards C_star C_h control0 u t
      ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v)) =
      postHistory (nonrenewedTransition rate rewards C_star C_h control0 u t
        ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v)) := by
  have haux (s : Fin p.T) (hs : s.val ≤ t.val) (l : Fin 2) :=
    futureAuxiliarySplit_other_date q proposal e x y s
      (fun he => by subst s; omega) l
  have hp := congrArg Prod.snd
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val _ _
      (fun s hs l => haux s hs.le l))
  change extendedPast rate rewards C_star C_h t.castSucc
    (z.val, (futureAuxiliarySplit q proposal).symm (e, x)) =
      extendedPast rate rewards C_star C_h t.castSucc
        (z.val, (futureAuxiliarySplit q proposal).symm (e, y)) at hp
  change _ ++ [actualFirstCell rate rewards C_star C_h control0 t _
      ((futureAuxiliarySplit q proposal).symm (e, x) (t, 1))] =
    _ ++ [actualFirstCell rate rewards C_star C_h control0 t _
      ((futureAuxiliarySplit q proposal).symm (e, y) (t, 1))]
  dsimp only [nonrenewedTransition]
  rw [hp, haux t le_rfl (1 : Fin 2)]

/-- Renewal's generated append retains both already used current labels;
neither is redrawn when exposing a later proposal or refresh coordinate. -/
theorem renewed_postHistory_futureAuxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (proposal : Bool)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (x y : ContinuousControlSlice.Scalar) :
    postHistory (renewedTransition rate rewards C_star C_h control0 u t
      ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v)) =
      postHistory (renewedTransition rate rewards C_star C_h control0 u t
        ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v)) := by
  have haux (s : Fin p.T) (hs : s.val ≤ t.val) (l : Fin 2) :=
    futureAuxiliarySplit_other_date q proposal e x y s
      (fun he => by subst s; omega) l
  have hp := congrArg Prod.snd
    (ReferenceFirstCollectionLogicalPrefixExtension.extendedPrefixStateAux_auxiliary_ext
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z.val _ _
      (fun s hs l => haux s hs.le l))
  change extendedPast rate rewards C_star C_h t.castSucc
    (z.val, (futureAuxiliarySplit q proposal).symm (e, x)) =
      extendedPast rate rewards C_star C_h t.castSucc
        (z.val, (futureAuxiliarySplit q proposal).symm (e, y)) at hp
  change _ ++ [actualFirstCell rate rewards C_star C_h control0 t _
      ((futureAuxiliarySplit q proposal).symm (e, x) (t, 0))] =
    _ ++ [actualFirstCell rate rewards C_star C_h control0 t _
      ((futureAuxiliarySplit q proposal).symm (e, y) (t, 0))]
  dsimp only [renewedTransition, ReferenceFirstCollectionRenewalInstallationCoupling.pair]
  rw [hp, haux t le_rfl (0 : Fin 2)]

/-- The stronger used-coordinate initial observer is constructed from the
literal lift and is independent of an erased coordinate strictly after `t`. -/
theorem nonrenewedInitialObservation_futureAuxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (proposal : Bool)
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (x y : ContinuousControlSlice.Scalar) :
    nonrenewedInitialObservation rate rewards C_star C_h control0 u t
      ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v) =
      nonrenewedInitialObservation rate rewards C_star C_h control0 u t
        ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v) := by
  have hu : usedAuxiliary t ((futureAuxiliarySplit q proposal).symm (e, x)) =
      usedAuxiliary t ((futureAuxiliarySplit q proposal).symm (e, y)) := by
    funext i
    exact futureAuxiliarySplit_other_date q proposal e x y i.val.1
      (fun he => by have hi := i.property; rw [he] at hi; omega) i.val.2
  exact Prod.ext rfl (Prod.ext hu
    (nonrenewed_postHistory_futureAuxiliary_ext rate rewards C_star C_h control0 u t q htq proposal z e v x y))

theorem renewedInitialObservation_futureAuxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T) (htq : t.val < q.val)
    (proposal : Bool)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (x y : ContinuousControlSlice.Scalar) :
    renewedInitialObservation rate rewards C_star C_h control0 u t
      ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v) =
      renewedInitialObservation rate rewards C_star C_h control0 u t
        ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v) := by
  have hu : usedAuxiliary t ((futureAuxiliarySplit q proposal).symm (e, x)) =
      usedAuxiliary t ((futureAuxiliarySplit q proposal).symm (e, y)) := by
    funext i
    exact futureAuxiliarySplit_other_date q proposal e x y i.val.1
      (fun he => by have hi := i.property; rw [he] at hi; omega) i.val.2
  exact Prod.ext rfl (Prod.ext hu
    (renewed_postHistory_futureAuxiliary_ext rate rewards C_star C_h control0 u t q htq proposal z e v x y))

/-- Equality of the whole produced append identifies its final cell and seed;
future-array agreement then propagates through the complete recursion. -/
theorem postInvocationPrefix_congr (t : Fin p.T) (n : Fin (p.T + 1))
    (d e : TransitionData rate t) (a b : ReferenceFirstCollectionAuxiliarySeeds.AuxiliaryArray p)
    (hz : insertedPhysicalSource rate d = insertedPhysicalSource rate e)
    (hH : postHistory d = postHistory e)
    (hab : ∀ q : Fin p.T, t.val < q.val → q.val < n.val → ∀ l : Fin 2, a (q, l) = b (q, l)) :
    postInvocationPrefix rate rewards C_star C_h t n d a =
      postInvocationPrefix rate rewards C_star C_h t n e b := by
  have hc : d.2.2.2 = e.2.2.2 := Option.some.inj
    ((postHistory_last rate t d).symm.trans
      ((congrArg List.getLast? hH).trans (postHistory_last rate t e)))
  have hseed : postSeed rate d = postSeed rate e := congrArg LogicalCell.nextSlowSet hc
  unfold postInvocationPrefix
  rw [hz, hH, hseed]
  exact noncallCalendar_auxiliary_ext rate rewards C_star C_h t _ a b _ n.val hab

/-- Even at the complete generated prefix, a future tested auxiliary scalar
has been erased from the readout, then reinserted as the SAME scalar. -/
theorem nonrenewedGeneratedObservation_futureAuxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val) (proposal : Bool)
    (z : ReferenceFirstNextInvocationJointLift.EventSource rate rewards C_star C_h u t)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (x y : ContinuousControlSlice.Scalar) :
    nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n
      ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v) =
    nonrenewedGeneratedObservation rate rewards C_star C_h control0 u t n
      ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v) := by
  have hi := nonrenewedInitialObservation_futureAuxiliary_ext rate rewards C_star C_h
    control0 u t q (htn.trans_le hnq) proposal z e v x y
  have hH := congrArg (fun o : InitialObservation rate t => o.2.2) hi
  have hp := postInvocationPrefix_congr rate rewards C_star C_h t n
    (nonrenewedTransition rate rewards C_star C_h control0 u t ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v))
    (nonrenewedTransition rate rewards C_star C_h control0 u t ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v))
    _ _ rfl hH (fun r _ hr l => futureAuxiliarySplit_other_date q proposal e x y r
      (fun he => by subst r; omega) l)
  have ha : (fun i : PrefixAuxiliaryIndex n => (futureAuxiliarySplit q proposal).symm (e, x) i.val) =
      (fun i : PrefixAuxiliaryIndex n => (futureAuxiliarySplit q proposal).symm (e, y) i.val) := by
    funext i
    exact futureAuxiliarySplit_other_date q proposal e x y i.val.1
      (fun he => by have hh := i.property; rw [he] at hh; omega) i.val.2
  exact Prod.ext hi (Prod.ext ha (Prod.ext rfl hp))

theorem renewedGeneratedObservation_futureAuxiliary_ext
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T)
    (n : Fin (p.T + 1)) (htn : t.val < n.val) (hnq : n.val ≤ q.val) (proposal : Bool)
    (z : ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t)
    (e : Bandits.Support.ReferenceFirstLiveActualRefreshTestLaw.ErasedAuxiliaryArray q)
    (v : AssignmentParameterFibreKernel.AssignmentVector p) (x y : ContinuousControlSlice.Scalar) :
    renewedGeneratedObservation rate rewards C_star C_h control0 u t n
      ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v) =
    renewedGeneratedObservation rate rewards C_star C_h control0 u t n
      ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v) := by
  have hi := renewedInitialObservation_futureAuxiliary_ext rate rewards C_star C_h
    control0 u t q (htn.trans_le hnq) proposal z e v x y
  have hH := congrArg (fun o : InitialObservation rate t => o.2.2) hi
  have hp := postInvocationPrefix_congr rate rewards C_star C_h t n
    (renewedTransition rate rewards C_star C_h control0 u t ((z, (futureAuxiliarySplit q proposal).symm (e, x)), v))
    (renewedTransition rate rewards C_star C_h control0 u t ((z, (futureAuxiliarySplit q proposal).symm (e, y)), v))
    _ _ rfl hH (fun r _ hr l => futureAuxiliarySplit_other_date q proposal e x y r
      (fun he => by subst r; omega) l)
  have ha : (fun i : PrefixAuxiliaryIndex n => (futureAuxiliarySplit q proposal).symm (e, x) i.val) =
      (fun i : PrefixAuxiliaryIndex n => (futureAuxiliarySplit q proposal).symm (e, y) i.val) := by
    funext i
    exact futureAuxiliarySplit_other_date q proposal e x y i.val.1
      (fun he => by have hh := i.property; rw [he] at hh; omega) i.val.2
  exact Prod.ext hi (Prod.ext ha (Prod.ext rfl hp))

end FutureAuxiliaryCoordinates

end Bandits.Support.ReferencePostInvocationNoncallGeometry

end
