/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionControlGeometry
public import Bandits.Support.ReferenceCollectionUpReadySupportMeasurability

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection coordinator UP conditional service

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124,193-240`,
`sources/zip4/manuscript/06_interruptions.tex:459-490`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`.

This module joins the actual first-collection coordinator decoder event to
the accepted continuous product draws and proves its internal conditional
service coefficient. Delivery, quota, stopping and regret remain open.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.AffineChannelLaw
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace Bandits.Support.ReferenceFirstCollectionUpConditionalService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput
abbrev UpRecord {p : Parameters} (rate : RateInput p) :=
  OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters} {rate : RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The positive-reward arms in the literal whole reward row. -/
def positiveRewardArms (rewards : RewardTable p) (t : Fin p.T) : Finset (Fin p.K) :=
  Finset.univ.filter fun a => 0 < rewards t a

/-- The cardinality in the one-round service coefficient. -/
def positiveRewardCount (rewards : RewardTable p) (t : Fin p.T) : ℕ :=
  (positiveRewardArms rewards t).card

/-- Embed the manuscript follower index in the accepted sampler carrier. -/
def followerIndex (i : Fin (p.m - 1)) :
    Fin (PublicDiscreteDraws.followerCount p.m) := i

private theorem followerIndex_eq (i : Fin (p.m - 1)) : followerIndex i = i := rfl

/-- The actual-source analytic readout, retaining the `none` tag as zero. -/
def actualFirstCollectionUpReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) : ℝ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => 0
  | some r =>
      if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 t).1 = followerIndex i ∧
          ReferenceActiveAffinePositiveTest.upPositive r.input = true then 1 else 0

/-- The literal joint test on the original whole source and a fresh complete
current `TimeControl`. Only the selected row's current control is replaced. -/
def actualFirstCollectionUpFreshTest
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Set (SourceInput p × TimeControl p) :=
  {z | actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) = 1}

/-- The section of the literal original-source test after replacing the current
whole control of the actual incoming input by a fresh `TimeControl`. -/
def actualFirstCollectionUpFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (source : SourceInput p) : ℝ :=
  ∫ control, actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) control)
    ∂ContinuousLearningRows.timeControlLaw p

private def serviceRecordCodeUpDiagnostic
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) :
    Option (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate) :=
  let tail : ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
    code.2.2.1.2.2.2.2
  tail.2.2.2.2

private theorem measurable_serviceRecordCodeUpDiagnostic :
    Measurable (serviceRecordCodeUpDiagnostic (p := p) (rate := rate)) := by
  fun_prop [serviceRecordCodeUpDiagnostic]

private def upPositiveFromServiceDiagnostic
    (diagnostic : Option
      (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate)) : Bool := by
  classical
  exact match diagnostic with
  | none => false
  | some d => decide (AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput d.input))

private abbrev ServiceRecordObservation :=
  Fin (PublicDiscreteDraws.followerCount p.m) ×
    Option (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate)

private def serviceRecordObservationReadout (i : Fin (p.m - 1))
    (observation : ServiceRecordObservation (p := p) (rate := rate)) : ℝ :=
  if observation.1 = followerIndex i ∧
      upPositiveFromServiceDiagnostic (p := p) observation.2 = true then 1 else 0

private theorem measurable_serviceRecordObservationReadout (i : Fin (p.m - 1)) :
    Measurable (serviceRecordObservationReadout (p := p) (rate := rate) i) :=
  measurable_of_countable _

private def serviceRecordCodeDiagnosticOption
    (code : Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) :
    Option (ReferenceCollectionServiceTailMeasurability.UpDiagnosticCode p rate) :=
  match code with
  | none => none
  | some c => serviceRecordCodeUpDiagnostic (p := p) (rate := rate) c

private theorem measurable_serviceRecordCodeDiagnosticOption :
    Measurable (serviceRecordCodeDiagnosticOption (p := p) (rate := rate)) := by
  let decode := Equiv.optionEquivSumPUnit
    (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
  have hsum : Measurable (Sum.elim
      (serviceRecordCodeUpDiagnostic (p := p) (rate := rate)) (fun _ : PUnit => none)) :=
    (measurable_serviceRecordCodeUpDiagnostic (p := p) (rate := rate)).sumElim measurable_const
  convert hsum.comp (comap_measurable decode) using 1
  funext code
  cases code <;> rfl

private def actualFirstCollectionUpRecordCode
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : SourceInput p) :
    Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) := by
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h source
  let start := p.T - codes.length
  exact if start ≤ t.val then codes[t.val - start]? else none

private theorem actualFirstCollectionUpRecordCode_eq_actualRecord
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : SourceInput p) :
    actualFirstCollectionUpRecordCode (rate := rate) rewards C_star C_h t source =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source).map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := by
  classical
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h source
  have hlength := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode_length
    (rate := rate) rewards C_star C_h source
  have hlength' : codes.length =
      p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
    simpa [codes] using hlength
  have hstartBound := ReferenceCompletePhysicalHistory.physicalStart_le_T
    rate source rewards C_star C_h
  have hstart : p.T - codes.length =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h := by
    omega
  have hcode : actualFirstCollectionUpRecordCode (rate := rate) rewards C_star C_h t source =
      (if p.T - codes.length ≤ t.val then codes[t.val - (p.T - codes.length)]? else none) := rfl
  rw [hcode, hstart]
  have hcodes : codes = (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).map
        (ReferenceActiveHorizonMeasurability.roundRecordCode (p := p) (rate := rate)) := rfl
  rw [hcodes]
  by_cases hp : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h ≤ t.val
  · simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hp, List.getElem?_map]
  · simp [ReferenceSourcePrefixHistoryFiltration.actualRecord, hp]

private theorem actualRecordInputFields
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : SourceInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some record) :
    record.input.rows = source.1.2 ∧
      record.input.selected = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source ∧
      record.input.time = t ∧ record.input.rewards = rewards := by
  by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val source
  · let active := ReferenceLocalReleaseGateChronology.sourceSeed
      rate source rewards C_star C_h hlaunch.1
    have hcorrected := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hlaunch.1
    have hstart : ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h ≤ t.val := by
      simpa [ReferenceSourcePrefixHistoryFiltration.actualLaunchBy] using hlaunch.2
    have hactual := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t source active hcorrected hstart
    have hrecordEq := Option.some.inj (hrecord.symm.trans hactual)
    subst record
    refine ⟨rfl, ?_, ?_, rfl⟩
    · exact ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p source
    · apply Fin.ext
      dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
        ReferenceActivePhysicalHorizon.roundInputAt]
      have ht := t.isLt
      omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t source hlaunch] at hrecord
    cases hrecord

private theorem roundInput_eq_of_fields
    (x y : RoundInput p rate)
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time = y.time)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  simp_all

private theorem actualFirstCollectionUpReadout_sourcePrefix_factor
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source =
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source) := by
  classical
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source
  have hincoming := ReferenceSourcePrefixHistoryFiltration.incoming_factor
    (rate := rate) rewards C_star C_h control0 t pref
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
    t.val (t.val + 1) (by omega) source,
    ← ReferenceSourcePrefixHistoryFiltration.incoming_factor
      (rate := rate) rewards C_star C_h control0 t source] at hincoming
  cases hleft : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source with
  | none =>
      cases hright : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t pref with
      | none => simp [actualFirstCollectionUpReadout, hleft, hright, pref]
      | some r' => simp [ReferenceSourcePrefixHistoryFiltration.incoming, hleft, hright] at hincoming
  | some r =>
      cases hright : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t pref with
      | none => simp [ReferenceSourcePrefixHistoryFiltration.incoming, hleft, hright] at hincoming
      | some r' =>
          have hstate : r'.input.state = r.input.state := by
            apply ReferenceActivePhysicalStepMeasurability.encodeState_injective
            simpa [ReferenceSourcePrefixHistoryFiltration.incoming, hleft, hright] using hincoming
          have hf := actualRecordInputFields (rate := rate) rewards C_star C_h t source r hleft
          have hf' := actualRecordInputFields (rate := rate) rewards C_star C_h t pref r' hright
          have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p pref =
              ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source := rfl
          have hselected : r'.input.selected = r.input.selected := by rw [hf.2.1, hf'.2.1, hindex]
          have htime : r'.input.time = r.input.time := hf'.2.2.1.trans hf.2.2.1.symm
          have hrewards : r'.input.rewards = r.input.rewards := hf'.2.2.2.trans hf.2.2.2.symm
          have hcontrol (v : Fin p.T) (hv : v.val < t.val + 1) :
              ((r'.input.rows r.input.selected).2 v) = ((r.input.rows r.input.selected).2 v) := by
            rw [hf.1, hf'.1, hf.2.1,
              ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
            change ((ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source).1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v = _
            rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left hv]
          have hcurrent : (r.input.rows r.input.selected).2 r.input.time =
              (r'.input.rows r.input.selected).2 r.input.time :=
            (hcontrol r.input.time (by rw [hf.2.2.1]; omega)).symm
          have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
              ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
                ((r'.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop := by
            intro v hv
            rw [hcontrol v (by rw [hf.2.2.1] at hv; omega)]
          have hinput : r'.input =
              ⟨r.input.state, r'.input.rows, r.input.selected, r.input.time,
                r.input.active, r.input.rewards⟩ :=
            roundInput_eq_of_fields _ _ hstate rfl hselected htime hrewards
          have hinputL : r.input =
              ⟨r.input.state, r.input.rows, r.input.selected, r.input.time,
                r.input.active, r.input.rewards⟩ :=
            roundInput_eq_of_fields _ _ rfl rfl rfl rfl rfl
          have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
            r.input.state r.input.rows r'.input.rows r.input.selected r.input.time
            r.input.active r.input.rewards r.input.rewards hcurrent hpast rfl
          have hpositive : ReferenceActiveAffinePositiveTest.upPositive r.input =
              ReferenceActiveAffinePositiveTest.upPositive r'.input := by
            have hcoord := congrArg ReferenceActivePhysicalHorizon.RoundEvidence.coordinator hevidence
            rw [ReferenceActiveAffinePositiveTest.record_upPositive,
              ReferenceActiveAffinePositiveTest.record_upPositive]
            have hcoord' : (ReferenceActivePhysicalStep.step r.input).coordinator =
                (ReferenceActivePhysicalStep.step r'.input).coordinator := by
              change (ReferenceActivePhysicalStep.step
                ⟨r.input.state, r.input.rows, r.input.selected, r.input.time,
                  r.input.active, r.input.rewards⟩).coordinator =
                (ReferenceActivePhysicalStep.step
                  ⟨r.input.state, r'.input.rows, r.input.selected, r.input.time,
                    r.input.active, r.input.rewards⟩).coordinator at hcoord
              rw [← hinputL, ← hinput] at hcoord
              exact hcoord
            rw [r.output_eq, r'.output_eq, hcoord']
          have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (r'.input.row.2 t).1 =
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 t).1 := by
            change PublicDiscreteDraws.selectedFollowerDraw _ _ ((r'.input.rows r'.input.selected).2 t).1 = _
            rw [hselected, hcontrol t (Nat.lt_succ_self t.val)]
            rfl
          simp [actualFirstCollectionUpReadout, hleft, hright, pref, hdraw, hpositive]

private theorem actualUpPositive_code_eq_record
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    upPositiveFromServiceDiagnostic (p := p)
        (serviceRecordCodeUpDiagnostic (p := p)
          (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
      ReferenceActiveAffinePositiveTest.upPositive record.input := by
  rw [ReferenceActiveAffinePositiveTest.record_upPositive]
  have hdecode :=
    (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record).2.1
  have hdiag :
      Option.map ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic
          (serviceRecordCodeUpDiagnostic (p := p) (rate := rate)
            (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
        record.output.coordinator.up := by
    have h := congrArg
      (fun observation : ReferenceActivePhysicalStep.CoordinatorObservation p rate =>
        observation.up) hdecode
    simpa [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics,
      ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation,
      serviceRecordCodeUpDiagnostic] using h
  cases hcode : serviceRecordCodeUpDiagnostic (p := p) (rate := rate)
      (ReferenceActiveHorizonMeasurability.roundRecordCode record) with
  | none =>
      have hnone : record.output.coordinator.up = none := by
        simpa [hcode] using hdiag.symm
      simp [upPositiveFromServiceDiagnostic,
        ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hnone]
  | some diagnostic =>
      have hsome : record.output.coordinator.up =
          some (ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic diagnostic) := by
        simpa [hcode] using hdiag.symm
      simp [upPositiveFromServiceDiagnostic,
        ReferenceActiveAffinePositiveTest.upDiagnosticPositive, hsome,
        ReferenceCollectionServiceTailMeasurability.decodeUpDiagnostic]

private def actualFirstCollectionUpCodeReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : SourceInput p × TimeControl p) : ℝ := by
  classical
  let replaced := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
    p t z.1 z.2
  let recordCode := actualFirstCollectionUpRecordCode (rate := rate)
    rewards C_star C_h t replaced
  let draw := PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1
  exact serviceRecordObservationReadout (p := p) (rate := rate) i
    (draw, serviceRecordCodeDiagnosticOption (p := p) (rate := rate) recordCode)

private theorem actualFirstCollectionUpReadout_eq_codeReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p × TimeControl p) :
    actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) =
      actualFirstCollectionUpCodeReadout (rate := rate) rewards C_star C_h i t z := by
  classical
  let replaced := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t replaced with
  | none =>
      have hrecordCode : actualFirstCollectionUpRecordCode (rate := rate)
          rewards C_star C_h t replaced = none := by
        rw [actualFirstCollectionUpRecordCode_eq_actualRecord, hrecord]
        rfl
      simp [actualFirstCollectionUpReadout, actualFirstCollectionUpCodeReadout,
        serviceRecordObservationReadout, serviceRecordCodeDiagnosticOption,
        upPositiveFromServiceDiagnostic, replaced, hrecord, hrecordCode]
  | some record =>
      have hrecordCode : actualFirstCollectionUpRecordCode (rate := rate)
          rewards C_star C_h t replaced =
            some (ReferenceActiveHorizonMeasurability.roundRecordCode record) := by
        rw [actualFirstCollectionUpRecordCode_eq_actualRecord, hrecord]
        rfl
      have hfields := actualRecordInputFields (rate := rate) rewards C_star C_h t
        replaced record hrecord
      have hrow : record.input.row = replaced.1.2 record.input.selected := by
        rw [ReferenceActivePhysicalStep.RoundInput.row, hfields.1, hfields.2.1]
      have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1 =
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (record.input.row.2 t).1 := by
        rw [hrow, hfields.2.1]
        simp [replaced, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex]
      have hpositive : upPositiveFromServiceDiagnostic (p := p) (rate := rate)
          (serviceRecordCodeUpDiagnostic (p := p) (rate := rate)
            (ReferenceActiveHorizonMeasurability.roundRecordCode record)) =
          ReferenceActiveAffinePositiveTest.upPositive record.input := by
        exact actualUpPositive_code_eq_record record
      simp [actualFirstCollectionUpReadout, actualFirstCollectionUpCodeReadout,
        serviceRecordObservationReadout, serviceRecordCodeDiagnosticOption,
        replaced, hrecord, hrecordCode, hdraw, hpositive]

private theorem measurable_serviceCodeLookup {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (fun records : List α => records[n]?) := by
  have hcoordinates :=
    ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates (α := α)
  have hat := (measurable_pi_apply n).comp (measurable_snd.comp hcoordinates)
  have hsome : Measurable (some : α → Option α) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have hconvert : Measurable (fun v : Unit ⊕ α =>
      Sum.elim (fun _ => (none : Option α)) some v) :=
    Measurable.sumElim measurable_const hsome
  convert hconvert.comp hat using 1
  funext records
  simp only [Function.comp_apply,
    ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt]
  cases records[n]? <;> rfl

private theorem measurable_actualFirstCollectionUpCodeReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualFirstCollectionUpCodeReadout (rate := rate)
      rewards C_star C_h i t) := by
  classical
  let replace := fun z : SourceInput p × TimeControl p =>
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2
  let codes := fun z : SourceInput p × TimeControl p =>
    ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
      (rate := rate) rewards C_star C_h (replace z)
  have hreplace : Measurable replace :=
    ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t
  have hcodes : Measurable codes :=
    (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
      (rate := rate) rewards C_star C_h).comp hreplace
  have hcoordinates :=
    (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate))).comp hcodes
  have hlength : Measurable (fun z => (codes z).length) := measurable_fst.comp hcoordinates
  have hstart : Measurable (fun z => p.T - (codes z).length) :=
    (measurable_of_countable (fun n : ℕ => p.T - n)).comp hlength
  have hindex : Measurable (fun z => t.val - (p.T - (codes z).length)) :=
    (measurable_of_countable (fun n : ℕ => t.val - n)).comp hstart
  have hlookup : Measurable (fun z => (codes z)[t.val - (p.T - (codes z).length)]?) :=
    (measurable_from_prod_countable_right
      (f := fun v : ℕ × List (ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate)) => v.2[v.1]?)
      (fun n => measurable_serviceCodeLookup n)).comp (hindex.prodMk hcodes)
  have hstartSet : MeasurableSet {z : SourceInput p × TimeControl p |
      p.T - (codes z).length ≤ t.val} :=
    hstart (MeasurableSpace.measurableSet_top : MeasurableSet {n : ℕ | n ≤ t.val})
  let recordCode := fun z : SourceInput p × TimeControl p =>
    actualFirstCollectionUpRecordCode (rate := rate) rewards C_star C_h t (replace z)
  have hrecordCodeMeas : Measurable recordCode := by
    change Measurable (fun z : SourceInput p × TimeControl p =>
      if p.T - (codes z).length ≤ t.val then
        (codes z)[t.val - (p.T - (codes z).length)]? else none)
    exact Measurable.ite hstartSet hlookup measurable_const
  have hdraw : Measurable (fun z : SourceInput p × TimeControl p =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      (measurable_fst.comp measurable_snd)
  have hdiagnostic : Measurable (fun z : SourceInput p × TimeControl p =>
      serviceRecordCodeDiagnosticOption (p := p) (rate := rate) (recordCode z)) :=
    (measurable_serviceRecordCodeDiagnosticOption (p := p) (rate := rate)).comp hrecordCodeMeas
  exact (measurable_serviceRecordObservationReadout (p := p) (rate := rate) i).comp
    (hdraw.prodMk hdiagnostic)

/-- The original whole-source readout is a literal zero/one indicator, with
absence retained as zero. -/
theorem actualFirstCollectionUpReadout_zero_or_one
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source = 0 ∨
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source = 1 := by
  classical
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source with
  | none => simp [actualFirstCollectionUpReadout, hrecord]
  | some record =>
      by_cases htest : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = followerIndex i ∧
          ReferenceActiveAffinePositiveTest.upPositive record.input = true
      · simp [actualFirstCollectionUpReadout, hrecord, htest]
      · simp [actualFirstCollectionUpReadout, hrecord, htest]

/-- Bounds for the literal readout, including every absent/exceptional branch. -/
theorem actualFirstCollectionUpReadout_bounds
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source ∧
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source ≤ 1 := by
  rcases actualFirstCollectionUpReadout_zero_or_one
    (rate := rate) rewards C_star C_h i t source with h | h <;> simp [h]

/-- Ambient Borel measurability of the original source readout. -/
theorem measurable_actualFirstCollectionUpReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t) := by
  have hf := (measurable_actualFirstCollectionUpCodeReadout
    (rate := rate) rewards C_star C_h i t).comp
    (measurable_id.prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t t))
  convert hf using 1
  funext source
  change actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source =
    actualFirstCollectionUpCodeReadout (rate := rate) rewards C_star C_h i t
      (source, ReferenceSourceCurrentControlFreshness.u_t p t source)
  rw [← actualFirstCollectionUpReadout_eq_codeReadout]
  exact congrArg (actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t)
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p t source).symm

/-- Integrability under the original product source law. -/
theorem integrable_actualFirstCollectionUpReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_actualFirstCollectionUpReadout rewards C_star C_h i t).aestronglyMeasurable
  filter_upwards [] with source
  rcases actualFirstCollectionUpReadout_zero_or_one
    (rate := rate) rewards C_star C_h i t source with h | h <;> simp [h]

/-- Measurability of the literal current-control test follows from the
complete diagnostic code readout and its equality with `actualRecord`. -/
theorem measurableSet_actualFirstCollectionUpFreshTest
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (actualFirstCollectionUpFreshTest (rate := rate)
      rewards C_star C_h i t) := by
  let f := actualFirstCollectionUpCodeReadout (rate := rate) rewards C_star C_h i t
  have hf : Measurable f := measurable_actualFirstCollectionUpCodeReadout
    (rate := rate) rewards C_star C_h i t
  have hset : actualFirstCollectionUpFreshTest (rate := rate) rewards C_star C_h i t =
      f ⁻¹' {1} := by
    ext z
    change actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) = 1 ↔
      f z = 1
    rw [actualFirstCollectionUpReadout_eq_codeReadout]
  rw [hset]
  exact hf (measurableSet_singleton 1)

/-- The accepted source-prefix reconstruction inserts the retained current
selected control and restores the literal successor prefix. -/
theorem actualFirstCollectionUp_restore_sourcePrefix
    (control0 : TimeControl p) (t : Fin p.T) (source : SourceInput p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
        (ReferenceSourceCurrentControlFreshness.u_t p t source) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source := by
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
  simpa [ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex] using
    (ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t source).symm

/-- The literal round-input restoration updates the selected row's complete
current control and preserves its boundary state, selected private index, time,
and full reward table. -/
theorem actualFirstCollectionUp_roundInput_restore
    (boundary : RoundInput p rate) (source : SourceInput p) (control : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p boundary.time source control) =
      ReferenceLaterOptionalControlResampling.withControl
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary source) control :=
  ReferenceFixedTimeSourceControlCoupling.roundInputAtSource_replaceSourceControl
    p rate boundary source control

private theorem strictPrefix_replaceSourceControl
    (control0 : TimeControl p) (t : Fin p.T) (source : SourceInput p) (c : TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source
    · subst q
      simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      congr 1
      funext v
      by_cases hv : v.val < t.val
      · have hne : v ≠ t := by intro h; subst v; omega
        simp [hv, Function.update_of_ne hne]
      · simp [hv]
    · simp [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ActualInitializationPhysicalStep.selectedRowIndex,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex] at hq ⊢
      simp [Function.update_of_ne hq]
  · rfl

/-- A resampled actual calendar record has exactly the original incoming
state and the literal `withControl` input. This says nothing about its output
or any future record. IDs, private arrays/J and forwards are unchanged by the
source replacement; rows, selected index, time and rewards are identified here. -/
theorem actualFirstCollectionUp_actualRecord_replace
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) (c : TimeControl p) :
    ∃ r', ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) = some r' ∧
      r'.input = ReferenceLaterOptionalControlResampling.withControl r.input c := by
  let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c
  have hin := ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t z
  rw [strictPrefix_replaceSourceControl] at hin
  rw [← ReferenceSourcePrefixHistoryFiltration.incoming_factor
    rate rewards C_star C_h control0 t source] at hin
  cases hz : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [ReferenceSourcePrefixHistoryFiltration.incoming, hz, hr] at hin
  | some r' =>
      have hstate : r'.input.state = r.input.state := by
        apply ReferenceActivePhysicalStepMeasurability.encodeState_injective
        simpa [ReferenceSourcePrefixHistoryFiltration.incoming, hz, hr] using hin
      have hf := actualRecordInputFields (rate := rate) rewards C_star C_h t source r hr
      have hf' := actualRecordInputFields (rate := rate) rewards C_star C_h t z r' hz
      have hboundary : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource
          p rate r.input source = r.input := by
        exact roundInput_eq_of_fields _ _ rfl hf.1.symm hf.2.1.symm rfl rfl
      have hinput : r'.input = ReferenceFixedTimeSourceControlCoupling.roundInputAtSource
          p rate r.input z := by
        exact roundInput_eq_of_fields _ _ hstate hf'.1 hf'.2.1
          (hf'.2.2.1.trans hf.2.2.1.symm) (hf'.2.2.2.trans hf.2.2.2.symm)
      refine ⟨r', rfl, ?_⟩
      rw [hinput]
      dsimp only [z]
      rw [← hf.2.2.1, actualFirstCollectionUp_roundInput_restore, hboundary]

private theorem actualFirstCollectionUpReadout_replacedPrefix
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) (c : TimeControl p) :
    actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) c) =
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) := by
  have hrestore := ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore
    control0 t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c)
  rw [strictPrefix_replaceSourceControl] at hrestore
  have hcurrent :
      ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c))).2 t = c := by
    simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
      ActualInitializationPhysicalStep.selectedRowIndex]
  rw [hcurrent] at hrestore
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix, ← hrestore]
  exact (actualFirstCollectionUpReadout_sourcePrefix_factor
    (rate := rate) rewards C_star C_h control0 i t _).symm

private theorem actualFirstCollectionUpFreshTest_indicator_eq_readout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p × TimeControl p) :
    (actualFirstCollectionUpFreshTest (rate := rate) rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ)) z =
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) := by
  let value := actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2)
  have hvalue : value = 0 ∨ value = 1 :=
    actualFirstCollectionUpReadout_zero_or_one (rate := rate) rewards C_star C_h i t _
  by_cases h : value = 1
  · simp [actualFirstCollectionUpFreshTest, Set.indicator, value, h]
  · rcases hvalue with hzero | hone
    · simp [actualFirstCollectionUpFreshTest, Set.indicator, value, hzero]
    · exact (h hone).elim

private theorem actualFirstCollectionUpFreshSection_eq_indicator_integral
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t source =
      ∫ control, (actualFirstCollectionUpFreshTest (rate := rate) rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
        ∂ContinuousLearningRows.timeControlLaw p := by
  unfold actualFirstCollectionUpFreshSection
  apply integral_congr_ae
  filter_upwards [] with control
  exact (actualFirstCollectionUpFreshTest_indicator_eq_readout
    (rate := rate) rewards C_star C_h i t
    (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)).symm

/-- Each fresh-control section is between zero and one. -/
theorem actualFirstCollectionUpFreshSection_bounds
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t source ∧
      actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t source ≤ 1 := by
  unfold actualFirstCollectionUpFreshSection
  have hnonneg : ∀ᵐ c ∂ContinuousLearningRows.timeControlLaw p,
      0 ≤ actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) c) :=
    Filter.Eventually.of_forall fun c =>
      (actualFirstCollectionUpReadout_bounds rewards C_star C_h i t _).1
  refine ⟨integral_nonneg_of_ae hnonneg, ?_⟩
  calc
    _ ≤ ∫ _ : TimeControl p, (1 : ℝ) ∂ContinuousLearningRows.timeControlLaw p :=
      integral_mono_of_nonneg hnonneg (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall fun c =>
          (actualFirstCollectionUpReadout_bounds rewards C_star C_h i t _).2)
    _ = 1 := by simp

/-- The whole-control section is Borel measurable in the retained source. -/
theorem measurable_m_t_actualFirstCollectionUpFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (actualFirstCollectionUpFreshSection (rate := rate)
      rewards C_star C_h control0 i t) := by
  let B := actualFirstCollectionUpFreshTest (rate := rate) rewards C_star C_h i t
  have hB : MeasurableSet B := measurableSet_actualFirstCollectionUpFreshTest
    (rate := rate) rewards C_star C_h i t
  have hBfun : Measurable (B.indicator (fun _ : SourceInput p × TimeControl p => (1 : ℝ))) :=
    measurable_const.indicator hB
  have hbase := hBfun.stronglyMeasurable.integral_prod_right'
    (ν := ContinuousLearningRows.timeControlLaw p)
  have heq : actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t =
      fun source => ∫ control, B.indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
          ∂ContinuousLearningRows.timeControlLaw p :=
    funext (actualFirstCollectionUpFreshSection_eq_indicator_integral
      (rate := rate) rewards C_star C_h control0 i t)
  rw [heq]
  exact hbase.measurable.comp (comap_measurable _)

/-- Ambient Borel measurability of the adapted fresh-control section. -/
theorem measurable_actualFirstCollectionUpFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualFirstCollectionUpFreshSection (rate := rate)
      rewards C_star C_h control0 i t) :=
  (measurable_m_t_actualFirstCollectionUpFreshSection rewards C_star C_h control0 i t).mono
    (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comap_le le_rfl

/-- Integrability of the bounded fresh-control section under the original
source law. -/
theorem integrable_actualFirstCollectionUpFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (actualFirstCollectionUpFreshSection (rate := rate)
      rewards C_star C_h control0 i t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_actualFirstCollectionUpFreshSection rewards C_star C_h control0 i t).aestronglyMeasurable
  filter_upwards [] with source
  have hb := actualFirstCollectionUpFreshSection_bounds (rate := rate)
    rewards C_star C_h control0 i t source
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- The literal actual-source UP readout has the adapted conditional expectation
given by its fresh whole-control section. Equality is asserted only almost
everywhere, as required for conditional expectation. -/
theorem actual_first_collection_up_condExp
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t := by
  let B := actualFirstCollectionUpFreshTest (rate := rate) rewards C_star C_h i t
  have hB : MeasurableSet B := measurableSet_actualFirstCollectionUpFreshTest
    (rate := rate) rewards C_star C_h i t
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B =
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t := by
    funext source
    calc
      ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B source =
          B.indicator (fun _ => (1 : ℝ))
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source,
              ReferenceSourceCurrentControlFreshness.u_t p t source) := rfl
      _ = actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) :=
        actualFirstCollectionUpFreshTest_indicator_eq_readout
          (rate := rate) rewards C_star C_h i t _
      _ = actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t source := by
        rw [actualFirstCollectionUp_restore_sourcePrefix]
        exact (actualFirstCollectionUpReadout_sourcePrefix_factor
          (rate := rate) rewards C_star C_h control0 i t source).symm
  have hroot := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    (p := p) control0 t B hB
  rw [htest] at hroot
  exact hroot.trans (Filter.Eventually.of_forall fun source =>
    (actualFirstCollectionUpFreshSection_eq_indicator_integral
      (rate := rate) rewards C_star C_h control0 i t source).symm)

private abbrev TupleFiber {m K : ℕ} (i : Fin m) (arm : Fin K) :=
  {tuple : OrderedTupleSampler.Tuple m K // tuple.val i = arm}

private def tupleArmSwapEquiv {m K : ℕ} (a b : Fin K) :
    OrderedTupleSampler.Tuple m K ≃ OrderedTupleSampler.Tuple m K where
  toFun tuple := ⟨Equiv.swap a b ∘ tuple.val,
    (Equiv.injective (Equiv.swap a b)).comp tuple.property⟩
  invFun tuple := ⟨Equiv.swap a b ∘ tuple.val,
    (Equiv.injective (Equiv.swap a b)).comp tuple.property⟩
  left_inv tuple := by
    apply Subtype.ext
    funext i
    simp [Function.comp_def]
  right_inv tuple := by
    apply Subtype.ext
    funext i
    simp [Function.comp_def]

private def tupleFiberSwapEquiv {m K : ℕ} (i : Fin m) (a b : Fin K) :
    TupleFiber i a ≃ TupleFiber i b where
  toFun tuple :=
    ⟨tupleArmSwapEquiv a b tuple.1, by
      change Equiv.swap a b (tuple.1.val i) = b
      rw [tuple.2, Equiv.swap_apply_left]⟩
  invFun tuple :=
    ⟨tupleArmSwapEquiv a b tuple.1, by
      change Equiv.swap a b (tuple.1.val i) = a
      rw [tuple.2, Equiv.swap_apply_right]⟩
  left_inv tuple := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp [tupleArmSwapEquiv, Function.comp_def]
  right_inv tuple := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp [tupleArmSwapEquiv, Function.comp_def]

private theorem tupleFiber_card_eq {m K : ℕ} (i : Fin m) (a b : Fin K) :
    Fintype.card (TupleFiber i a) = Fintype.card (TupleFiber i b) :=
  Fintype.card_congr (tupleFiberSwapEquiv i a b)

private theorem tuple_coordinate_card_total {m K : ℕ} (i : Fin m) :
    Fintype.card (OrderedTupleSampler.Tuple m K) =
      ∑ arm : Fin K, Fintype.card (TupleFiber i arm) := by
  exact (Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun tuple : OrderedTupleSampler.Tuple m K => tuple.val i))).symm.trans Fintype.card_sigma

private theorem tuple_coordinate_filter_card
    {m K : ℕ} (hKpos : 0 < K) (i : Fin m) (S : Finset (Fin K)) :
    (Finset.univ.filter fun tuple : OrderedTupleSampler.Tuple m K =>
      tuple.val i ∈ S).card = S.card * Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by
  classical
  let coordinate : OrderedTupleSampler.Tuple m K → Fin K := fun tuple => tuple.val i
  have hfilter := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (OrderedTupleSampler.Tuple m K)) S coordinate
  rw [← hfilter]
  calc
    (∑ arm ∈ S, (Finset.univ.filter fun tuple : OrderedTupleSampler.Tuple m K =>
        coordinate tuple = arm).card) =
      ∑ arm ∈ S, Fintype.card (TupleFiber i arm) := by
        apply Finset.sum_congr rfl
        intro arm harm
        symm
        simpa [TupleFiber, coordinate] using
          (Fintype.card_subtype (fun tuple : OrderedTupleSampler.Tuple m K =>
            coordinate tuple = arm))
    _ = ∑ arm ∈ S, Fintype.card (TupleFiber i ⟨0, hKpos⟩) :=
      Finset.sum_congr rfl fun arm _ => tupleFiber_card_eq i arm ⟨0, hKpos⟩
    _ = S.card * Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by simp [Finset.sum_const]

private theorem tuple_total_factorization
    {m K : ℕ} (hm : 2 ≤ m) (hmk : m < K) (i : Fin m) :
    Fintype.card (OrderedTupleSampler.Tuple m K) =
      K * Fintype.card (TupleFiber i
        ⟨0, Nat.lt_trans (Nat.lt_of_lt_of_le (by decide : 0 < 2) hm) hmk⟩) := by
  let zeroArm : Fin K := ⟨0, Nat.lt_trans (Nat.lt_of_lt_of_le (by decide : 0 < 2) hm) hmk⟩
  rw [tuple_coordinate_card_total]
  calc
    (∑ arm : Fin K, Fintype.card (TupleFiber i arm)) =
        ∑ _arm : Fin K, Fintype.card (TupleFiber i zeroArm) :=
      Finset.sum_congr rfl fun arm _ => tupleFiber_card_eq i arm zeroArm
    _ = K * Fintype.card (TupleFiber i zeroArm) := by simp [Finset.sum_const]

/-- The selected coordinator coordinate of the accepted ordered tuple is
uniform on the full arm set; the result is derived from the accepted sampler. -/
private theorem orderedTupleCoordinator_uniform
    (i : Fin p.m) (S : Finset (Fin p.K)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      {x | (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val i ∈ S} =
        ENNReal.ofReal ((S.card : ℝ) / p.K) := by
  classical
  let μ := ContinuousControlSlice.sliceLaw p.m p.K
  let event : Set (OrderedTupleSampler.Tuple p.m p.K) := {tuple | tuple.val i ∈ S}
  have hmap := OrderedTupleSampler.map_sample p.two_le_m p.m_lt_K
  have hmeas : MeasurableSet event := MeasurableSet.of_discrete
  change μ ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K) ⁻¹' event) = _
  rw [← Measure.map_apply (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K) hmeas,
    hmap, PMF.toMeasure_apply_fintype]
  simp only [Set.indicator, OrderedTupleSampler.uniformTuplePMF_apply]
  let decPred : DecidablePred (fun x : OrderedTupleSampler.Tuple p.m p.K => x ∈ event) :=
    Classical.decPred _
  have hsumCondition :
      (∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x ∈ event then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0) =
      ∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x.val i ∈ S then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hmem : x.val i ∈ S <;> simp [event, hmem]
  calc
    (∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x ∈ event then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0) =
      ∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x.val i ∈ S then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0 := hsumCondition
    _ = ENNReal.ofReal ((S.card : ℝ) / p.K) := by
      change (∑ tuple ∈ (Finset.univ : Finset (OrderedTupleSampler.Tuple p.m p.K)),
        if tuple.val i ∈ S then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0) = _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hmpos : 0 < p.m := Nat.lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m
      have hKpos : 0 < p.K := Nat.lt_trans hmpos p.m_lt_K
      rw [tuple_coordinate_filter_card (m := p.m) (K := p.K) hKpos i S]
      let c := Fintype.card (TupleFiber i ⟨0, hKpos⟩)
      have hdesc : p.K.descFactorial p.m = p.K * c := by
        simpa [c] using
          (OrderedTupleSampler.card_tuple p.m p.K).symm.trans
            (tuple_total_factorization p.two_le_m p.m_lt_K i)
      have hmk : p.m < p.K := p.m_lt_K
      have hc : 0 < c := by
        let tuple : OrderedTupleSampler.Tuple p.m p.K :=
          ⟨fun j => ⟨j.val, by omega⟩, by
            intro j k hjk
            have hvalue : (⟨j.val, by omega⟩ : Fin p.K) = ⟨k.val, by omega⟩ := hjk
            exact Fin.ext (congrArg (fun z : Fin p.K => z.val) hvalue)⟩
        let swapped : OrderedTupleSampler.Tuple p.m p.K :=
          tupleArmSwapEquiv (tuple.val i) ⟨0, hKpos⟩ tuple
        have hfiber : swapped.1 i = (⟨0, hKpos⟩ : Fin p.K) := by
          change Equiv.swap (tuple.val i) ⟨0, hKpos⟩ (tuple.val i) = _
          exact Equiv.swap_apply_left _ _
        have hnonempty : Nonempty (TupleFiber i ⟨0, hKpos⟩) := ⟨⟨swapped, hfiber⟩⟩
        exact Fintype.card_pos_iff.mpr hnonempty
      have hcancel :
          (S.card : ℝ≥0∞) * (c : ℝ≥0∞) /
              ((p.K : ℝ≥0∞) * (c : ℝ≥0∞)) =
            (S.card : ℝ≥0∞) / (p.K : ℝ≥0∞) := by
        exact ENNReal.mul_div_mul_right _ _ (by exact_mod_cast Nat.ne_of_gt hc)
          (ENNReal.natCast_ne_top _)
      rw [hdesc, Nat.cast_mul, Nat.cast_mul]
      change ((S.card : ℝ≥0∞) * (c : ℝ≥0∞)) *
        ((p.K : ℝ≥0∞) * (c : ℝ≥0∞))⁻¹ = _
      rw [← div_eq_mul_inv, hcancel]
      rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [ENNReal.ofReal_natCast]

private abbrev ServiceSliceOutput (p : Parameters) :=
  (Slot × Fin (PublicDiscreteDraws.followerCount p.m)) ×
    OrderedTupleSampler.Tuple p.m p.K

private def serviceSliceOutput (p : Parameters) (x : ContinuousControlSlice.Slice p.m p.K) :
    ServiceSliceOutput p :=
  ((PublicDiscreteDraws.slotDraw x,
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x),
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K x)

private def coordinatorServiceSliceSet (rewards : RewardTable p) (t : Fin p.T)
    (i : Fin (PublicDiscreteDraws.followerCount p.m)) : Set (ServiceSliceOutput p) :=
  {z | z.1.1 = PublicDiscreteDraws.upSlot ∧ z.1.2 = i ∧
    z.2.val (ActiveRoundActions.coordinator p.two_le_m) ∈ positiveRewardArms rewards t}

private theorem measurable_serviceSliceOutput :
    Measurable (serviceSliceOutput p) := by
  exact ((PublicDiscreteDraws.measurable_slotDraw.prodMk
      (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K)).prodMk
    (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))

private theorem measurableSet_coordinatorServiceSliceSet (rewards : RewardTable p)
    (t : Fin p.T) (i : Fin (PublicDiscreteDraws.followerCount p.m)) :
    MeasurableSet (coordinatorServiceSliceSet (p := p) rewards t i) :=
  MeasurableSet.of_discrete

private theorem coordinatorServiceSlice_probability (rewards : RewardTable p)
    (t : Fin p.T) (i : Fin (PublicDiscreteDraws.followerCount p.m)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      ((serviceSliceOutput p) ⁻¹' coordinatorServiceSliceSet rewards t i) =
        ENNReal.ofReal
          (((positiveRewardCount rewards t : ℝ) /
            (4 * (p.m - 1 : ℝ) * p.K))) := by
  classical
  let μ := ContinuousControlSlice.sliceLaw p.m p.K
  let pairDraw : ContinuousControlSlice.Slice p.m p.K →
      Slot × Fin (PublicDiscreteDraws.followerCount p.m) :=
    fun x => (PublicDiscreteDraws.slotDraw x,
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x)
  let tupleDraw : ContinuousControlSlice.Slice p.m p.K →
      OrderedTupleSampler.Tuple p.m p.K :=
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K
  let tupleSet : Set (OrderedTupleSampler.Tuple p.m p.K) :=
    {f | f.val (ActiveRoundActions.coordinator p.two_le_m) ∈
      positiveRewardArms rewards t}
  let selectedDrawPair (draws : (j : PublicDiscreteDraws.DrawIndex p.m p.K) →
      PublicDiscreteDraws.DrawOutput j) :
      Slot × Fin (PublicDiscreteDraws.followerCount p.m) :=
    (draws .slot, draws .selectedFollower)
  have hselectedPairMeas : Measurable selectedDrawPair := by
    exact (measurable_pi_apply PublicDiscreteDraws.DrawIndex.slot).prodMk
      (measurable_pi_apply PublicDiscreteDraws.DrawIndex.selectedFollower)
  have hind := PublicDiscreteDraws.indepFun_drawFamily_tupleInputs
    p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
  have hpairMap :
      (fun x => selectedDrawPair
        (PublicDiscreteDraws.drawVector p.two_le_m p.m_lt_K
          (ConstructorDimensions.K_pos p) x)) = pairDraw := by
    funext x
    apply Prod.ext <;> rfl
  have htupleMap : OrderedTupleSampler.sampleCube p.m_lt_K ∘
      PublicDiscreteDraws.tupleInputs = tupleDraw := by
    funext x
    rfl
  have hind' : IndepFun pairDraw tupleDraw μ := by
    rw [← hpairMap, ← htupleMap]
    exact hind.comp hselectedPairMeas
      (OrderedTupleSampler.measurable_sampleCube p.m_lt_K)
  have hpairs : μ (pairDraw ⁻¹' {(PublicDiscreteDraws.upSlot, i)}) =
      ENNReal.ofReal (1 / 4) *
        ENNReal.ofReal (1 / (p.m - 1 : ℝ)) := by
    have hij : (PublicDiscreteDraws.DrawIndex.slot :
        PublicDiscreteDraws.DrawIndex p.m p.K) ≠
          PublicDiscreteDraws.DrawIndex.selectedFollower := by
      intro h
      cases h
    have hmass := (PublicDiscreteDraws.iIndepFun_drawFamily
      p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)).indepFun hij
    have hpairmass := hmass.measure_inter_preimage_eq_mul
      ({PublicDiscreteDraws.upSlot} : Set Slot)
      ({i} : Set (Fin (PublicDiscreteDraws.followerCount p.m)))
      (measurableSet_singleton _) (measurableSet_singleton _)
    have hslotEq : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) .slot = PublicDiscreteDraws.slotDraw := rfl
    have hselectedEq : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) .selectedFollower =
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K := rfl
    rw [hslotEq, hselectedEq] at hpairmass
    change μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.upSlot} ∩
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) = _ at hpairmass
    have hevent : pairDraw ⁻¹' {(PublicDiscreteDraws.upSlot, i)} =
        PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.upSlot} ∩
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i} := by
      ext x
      simp [Set.mem_inter_iff, pairDraw]
    calc
      _ = μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.upSlot} ∩
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) := by
        rw [hevent]
      _ = μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.upSlot}) *
          μ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) := hpairmass
      _ = _ := by
        have hslotAtom : μ (PublicDiscreteDraws.slotDraw ⁻¹'
            {PublicDiscreteDraws.upSlot}) = ENNReal.ofReal (1 / 4) := by
          simpa [μ, PublicDiscreteDraws.slotMass_up] using
            (PublicDiscreteDraws.slotDraw_atom (m := p.m) (K := p.K)
              PublicDiscreteDraws.upSlot)
        have hcast : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)]
          norm_num
        have hselectedAtom : μ (PublicDiscreteDraws.selectedFollowerDraw
            p.two_le_m p.m_lt_K ⁻¹' {i}) =
              ENNReal.ofReal (1 / (p.m - 1 : ℝ)) := by
          simpa [μ, PublicDiscreteDraws.equalMass, PublicDiscreteDraws.followerCount, hcast] using
            (PublicDiscreteDraws.selectedFollowerDraw_atom
              p.two_le_m p.m_lt_K i)
        change μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.upSlot}) *
            μ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) = _
        rw [hslotAtom, hselectedAtom]
  have htuple : μ (tupleDraw ⁻¹' tupleSet) =
      ENNReal.ofReal ((positiveRewardCount rewards t : ℝ) / p.K) := by
    have h := orderedTupleCoordinator_uniform (p := p)
      (ActiveRoundActions.coordinator p.two_le_m) (positiveRewardArms rewards t)
    change μ {x | (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
      (ActiveRoundActions.coordinator p.two_le_m) ∈ positiveRewardArms rewards t} = _
    simpa [μ, tupleSet, tupleDraw, positiveRewardCount] using h
  have hmeasure := hind'.measure_inter_preimage_eq_mul
    ({(PublicDiscreteDraws.upSlot, i)} :
      Set (Slot × Fin (PublicDiscreteDraws.followerCount p.m))) tupleSet
    (MeasurableSet.of_discrete) (MeasurableSet.of_discrete)
  have hevent : (serviceSliceOutput p) ⁻¹' coordinatorServiceSliceSet rewards t i =
      pairDraw ⁻¹' {(PublicDiscreteDraws.upSlot, i)} ∩ tupleDraw ⁻¹' tupleSet := by
    ext x
    change (PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (ActiveRoundActions.coordinator p.two_le_m) ∈ positiveRewardArms rewards t) ↔
      ((pairDraw x = (PublicDiscreteDraws.upSlot, i)) ∧ tupleDraw x ∈ tupleSet)
    constructor
    · rintro ⟨hslot, hselected, hreward⟩
      exact ⟨Prod.ext hslot hselected, hreward⟩
    · rintro ⟨hpair, hreward⟩
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair, hreward⟩
  rw [hevent, hmeasure, hpairs, htuple]
  have hmtwo : (1 : ℝ) < p.m := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hmpos : 0 < (p.m : ℝ) - 1 := by linarith
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hcount : 0 ≤ (positiveRewardCount rewards t : ℝ) := Nat.cast_nonneg _
  have htupleNonneg : 0 ≤ (positiveRewardCount rewards t : ℝ) / p.K := by positivity
  have hpairNonneg : 0 ≤ (1 / 4 : ℝ) * (1 / (p.m - 1 : ℝ)) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 4),
    ← ENNReal.ofReal_mul hpairNonneg]
  congr 1
  field_simp

/-- The service event on the actual incoming input, with its whole current
`TimeControl` as the integration variable. -/
def freshCoordinatorUpServiceSet (x : RoundInput p rate)
    (i : Fin (p.m - 1)) : Set (TimeControl p) :=
  {c | PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
    ReferenceActiveAffinePositiveTest.upPositive
      (ReferenceLaterOptionalControlResampling.withControl x c) = true}

private theorem actualFirstCollectionUpReadout_replace_eq_indicator
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) (c : TimeControl p) :
    actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) =
      (freshCoordinatorUpServiceSet r.input i).indicator (fun _ => (1 : ℝ)) c := by
  obtain ⟨r', hr', hinput⟩ := actualFirstCollectionUp_actualRecord_replace
    rewards C_star C_h control0 t source r hr c
  have hf := actualRecordInputFields (rate := rate) rewards C_star C_h t source r hr
  have hcontrol : r'.input.row.2 t = c := by
    rw [hinput, ← hf.2.2.1]
    exact ReferenceLaterOptionalControlResampling.withControl_currentControl r.input c
  simp only [actualFirstCollectionUpReadout, hr', followerIndex_eq,
    freshCoordinatorUpServiceSet, Set.indicator, Set.mem_ofPred_eq]
  rw [hcontrol, hinput]
  by_cases h : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
      ReferenceActiveAffinePositiveTest.upPositive
        (ReferenceLaterOptionalControlResampling.withControl r.input c) = true
  · simp only [h]
  · simp only [h, ite_false]

/-- The whole-source section is exactly the probability of the current-control
event on its actual incoming input. No future run or collection-window
invariance is used. -/
theorem actualFirstCollectionUpFreshSection_eq_measure
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t source =
      (ContinuousLearningRows.timeControlLaw p).real (freshCoordinatorUpServiceSet r.input i) := by
  have hvalue (c : TimeControl p) := actualFirstCollectionUpReadout_replace_eq_indicator
    rewards C_star C_h control0 i t source r hr c
  have hset : freshCoordinatorUpServiceSet r.input i =
      {c | (source, c) ∈ actualFirstCollectionUpFreshTest
        (rate := rate) rewards C_star C_h i t} := by
    ext c
    change c ∈ freshCoordinatorUpServiceSet r.input i ↔
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) = 1
    rw [hvalue]
    by_cases h : c ∈ freshCoordinatorUpServiceSet r.input i <;> simp [Set.indicator, h]
  have hmeas : MeasurableSet (freshCoordinatorUpServiceSet r.input i) := by
    rw [hset]
    exact measurable_prodMk_left
      (measurableSet_actualFirstCollectionUpFreshTest (rate := rate) rewards C_star C_h i t)
  calc
    _ = ∫ c, (freshCoordinatorUpServiceSet r.input i).indicator (fun _ => (1 : ℝ)) c
        ∂ContinuousLearningRows.timeControlLaw p := by
      unfold actualFirstCollectionUpFreshSection
      apply integral_congr_ae
      filter_upwards [] with c
      rw [actualFirstCollectionUpReadout_replacedPrefix, hvalue]
    _ = _ := integral_indicator_one hmeas

/-- The affine, UP-slot, tuple-arm event exposed by the checked actual
first-collection decoder equivalence. -/
def coordinatorUpServiceFormulaSet (rewards : RewardTable p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (U : UpRecord rate) : Set (TimeControl p) :=
  {c | PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
    AffineChannelLaw.affineHash (c.2 (1, i))
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
    0 < rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
      (ActiveRoundActions.coordinator p.two_le_m))}

private def serviceControlOutput (i : Fin (p.m - 1)) (c : TimeControl p) :
    ServiceSliceOutput p × AffineChannelLaw.Sample (B p) :=
  (serviceSliceOutput p c.1, c.2 (1, i))

private theorem measurable_serviceControlOutput (i : Fin (p.m - 1)) :
    Measurable (serviceControlOutput (p := p) i) := by
  exact ((measurable_serviceSliceOutput (p := p)).comp measurable_fst).prodMk
    (ContinuousLearningRows.measurePreserving_affineSample p (1, i)).measurable

/-- Exact probability of the UP-slot, focal selected follower, positive
coordinator-arm, and affine-hash-one event under the complete accepted
`TimeControl` law. The offered word is fixed before the whole control is
integrated. -/
theorem coordinatorUpServiceFormulaSet_probability (rewards : RewardTable p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (U : UpRecord rate) :
    (ContinuousLearningRows.timeControlLaw p)
      (coordinatorUpServiceFormulaSet rewards t i U) =
        ENNReal.ofReal
          (((positiveRewardCount rewards t : ℝ) /
            (8 * (p.m - 1 : ℝ) * p.K))) := by
  classical
  let μ := ContinuousLearningRows.timeControlLaw p
  let ν := (AffineChannelLaw.jointLaw (B p)).toMeasure
  let channel : ContinuousLearningRows.Channel p := (1, i)
  let output := serviceControlOutput (p := p) i
  let sliceSet := coordinatorServiceSliceSet rewards t (followerIndex i)
  let bitSet : Set (AffineChannelLaw.Sample (B p)) :=
    {sample | AffineChannelLaw.affineHash sample
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1}
  have houtput : Measurable output := measurable_serviceControlOutput i
  have hsliceOutput := measurable_serviceSliceOutput (p := p)
  have hcontrolAffine : Measurable (fun c : TimeControl p => c.2 channel) :=
    (ContinuousLearningRows.measurePreserving_affineSample p channel).measurable
  have hindep : IndepFun (fun c : TimeControl p => serviceSliceOutput p c.1)
      (fun c : TimeControl p => c.2 channel) μ := by
    exact (ContinuousLearningRows.indepFun_slice_affineSamples p).comp
      hsliceOutput (measurable_pi_apply channel)
  have houtputLaw : μ.map output =
      ((ContinuousControlSlice.sliceLaw p.m p.K).map (serviceSliceOutput p)).prod ν := by
    have hmap := hindep.map_prod_eq_prod_map_map
      (hsliceOutput.comp measurable_fst).aemeasurable hcontrolAffine.aemeasurable
    change μ.map (fun c : TimeControl p =>
      (serviceSliceOutput p c.1, c.2 channel)) = _
    calc
      _ = (μ.map (fun c : TimeControl p => serviceSliceOutput p c.1)).prod
          (μ.map fun c : TimeControl p => c.2 channel) := hmap
      _ = _ := by
        rw [show μ.map (fun c : TimeControl p => serviceSliceOutput p c.1) =
            ((μ.map Prod.fst).map (serviceSliceOutput p)) by
              exact (Measure.map_map hsliceOutput measurable_fst).symm,
          ContinuousLearningRows.map_slice,
          ContinuousLearningRows.map_affineSample p channel]
  have hslice :
      ((ContinuousControlSlice.sliceLaw p.m p.K).map (serviceSliceOutput p)) sliceSet =
        ENNReal.ofReal
          (((positiveRewardCount rewards t : ℝ) /
            (4 * (p.m - 1 : ℝ) * p.K))) := by
    rw [Measure.map_apply hsliceOutput
      (measurableSet_coordinatorServiceSliceSet rewards t (followerIndex i))]
    have h := coordinatorServiceSlice_probability rewards t (followerIndex i)
    simpa [sliceSet, coordinatorServiceSliceSet, followerIndex_eq,
      positiveRewardCount] using h
  have hbit : ν bitSet = (1 : ℝ≥0∞) / 2 := by
    rw [← AffineChannelLaw.eventProbability_eq_measure]
    exact AffineChannelLaw.affineHash_probability
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) 1
  have hset : coordinatorUpServiceFormulaSet rewards t i U =
      output ⁻¹' (sliceSet ×ˢ bitSet) := by
    ext c
    change (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
        AffineChannelLaw.affineHash (c.2 (1, i))
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1 ∧
        0 < rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
          (ActiveRoundActions.coordinator p.two_le_m))) ↔
      ((PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 =
          followerIndex i ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
          (ActiveRoundActions.coordinator p.two_le_m) ∈ positiveRewardArms rewards t) ∧
        AffineChannelLaw.affineHash (c.2 (1, i))
          (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)
    constructor
    · rintro ⟨hslot, hselected, hbit, hreward⟩
      exact ⟨⟨hslot, by simpa only [followerIndex_eq] using hselected,
        by simpa [positiveRewardArms] using hreward⟩, hbit⟩
    · rintro ⟨⟨hslot, hselected, hreward⟩, hbit⟩
      exact ⟨hslot, by simpa only [followerIndex_eq] using hselected, hbit,
        by simpa [positiveRewardArms] using hreward⟩
  have hproduct : MeasurableSet (sliceSet ×ˢ bitSet) := by
    exact (measurableSet_coordinatorServiceSliceSet rewards t (followerIndex i)).prod
      MeasurableSet.of_discrete
  rw [hset, ← Measure.map_apply houtput hproduct, houtputLaw,
    Measure.prod_prod, hslice, hbit]
  have hmtwo : (1 : ℝ) < p.m := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hmpos : 0 < (p.m : ℝ) - 1 := by linarith
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hq : 0 ≤ (positiveRewardCount rewards t : ℝ) /
      (4 * (p.m - 1 : ℝ) * p.K) := by positivity
  have hhalf : (1 : ℝ≥0∞) / 2 = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hhalf, ← ENNReal.ofReal_mul hq]
  congr 1
  field_simp
  ring

/-- The actual first-collection coordinator UP branch has the exact one-round
service coefficient on the original source. The complete telescope and every
local Ready, formed-reply, follower-state, pending, and accepted-start input
remain visible. The checked offered word is fixed before the whole fresh
`TimeControl` is integrated, and the support conclusion refers to the same
original source and calendar record. -/
theorem actual_first_collection_up_service_coefficient
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (hspan : s + count ≤ p.T) :
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count
      (by simpa only [hsElapsed] using hspan)
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (_hshort : w < count)
      (n : Fin B.length) (_hn : 0 < n.val)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (_hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        B[n.val].input payload l saved)
      (i : Fin (p.m - 1))
      (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (_hfi : B[n.val].input.state.followers i = .ordinary old memory)
      (_hip : i ∈ l.pending)
      (_hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart old),
    ∃ U : UpRecord rate,
      U.val = ActiveFollowerQueueOperation.upOfferFields old ∧
      1 ≤ U.val.sigma ∧
      source ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (rate := rate) rewards C_star C_h i B[n.val].input.time U ∧
      (ContinuousLearningRows.timeControlLaw p)
        (freshCoordinatorUpServiceSet B[n.val].input i) =
        ENNReal.ofReal ((positiveRewardCount rewards B[n.val].input.time : ℝ) /
          (8 * (p.m - 1 : ℝ) * p.K)) ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        B[n.val].input.time source = some B[n.val] ∧
      ∀ control0 : TimeControl p,
        actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i
          B[n.val].input.time source =
          (positiveRewardCount rewards B[n.val].input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  classical
  intro E w B hshort n hn payload l saved hReady i old memory hfi hip hpositive
  let x := B[n.val].input
  let t := x.time
  have hspan' : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        count ≤ p.T := by
    simpa only [hsElapsed] using hspan
  have hgeometry :=
    ReferenceFirstCollectionControlGeometry.actual_first_collection_control_geometry
      rate source rewards C_star C_h count hcross s hsElapsed hspan hshort n hn
      payload l saved hReady i old memory hfi hip hpositive
  dsimp only [x, t] at hgeometry
  rcases hgeometry with ⟨U, hU, hUsigma, hforall⟩
  have hsupport :=
    ReferenceCollectionUpReadySupportMeasurability.actual_first_collection_mem_collectionUpReadySupport
      rate source rewards C_star C_h count hcross hspan' hshort n hn payload l saved
      hReady i old memory hfi hip hpositive U hU.symm
  have hset : freshCoordinatorUpServiceSet x i =
      coordinatorUpServiceFormulaSet rewards t i U := by
    ext c
    exact (hforall c).1
  have hmeasure : (ContinuousLearningRows.timeControlLaw p)
      (freshCoordinatorUpServiceSet x i) = ENNReal.ofReal
        ((positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
    rw [hset]
    exact coordinatorUpServiceFormulaSet_probability rewards t i U
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hcross)
  have hwindow := ReferenceFirstCollectionEpochAlignment.actual_first_collection_window_time
    rate source rewards C_star C_h count hcross hspan' hshort n
  have htime : t.val = s + (w + n.val) := by
    have ht := hwindow.2
    change t.val + 1 = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
      w + 1 + n.val at ht
    rw [← hsElapsed] at ht
    omega
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hindex : w + n.val < count := by
    have hb := (List.getElem?_eq_some_iff.mp hwindow.1).1
    rwa [hcount] at hb
  have hrecordAt : B[n.val] = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n.val) (by omega) (by simpa only [hsElapsed] using active) := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
      (by simpa only [hsElapsed] using active) count hspan ⟨w + n.val, hindex⟩
    apply Option.some.inj
    calc
      some B[n.val] = E.records[w + n.val]? := hwindow.1.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
        simpa only [E, initial, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun,
          ← hsElapsed] using congrArg some hat
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s :=
    hsElapsed.symm
  have hsourceRecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some B[n.val] := by
    have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t source initial hlaunch (by rw [hstart, htime]; omega)
    have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h t source = some
        (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) (by simpa only [hsElapsed] using active)) := by
      simpa only [hstart, htime, Nat.add_sub_cancel_left] using hsource
    exact hsource'.trans (congrArg some hrecordAt.symm)
  refine ⟨U, hU, hUsigma, ?_, hmeasure, hsourceRecord, ?_⟩
  · simpa [x, t] using hsupport
  · intro control0
    have hm : (2 : ℝ) ≤ p.m := by exact_mod_cast p.two_le_m
    have hmpos : 0 < (p.m : ℝ) - 1 := by linarith
    rw [actualFirstCollectionUpFreshSection_eq_measure rewards C_star C_h control0
      i t source B[n.val] hsourceRecord, measureReal_def, hmeasure,
      ENNReal.toReal_ofReal (by positivity)]

/-- For almost every original source, every actual first-collection branch
satisfying the displayed local Ready/formed-pending-reply inputs has the exact
conditional service coefficient. The null set is removed before choosing any
branch or its calendar time. This is an internal result in `m_t`, not a claim
about the manuscript's smaller filtration or about later collection points. -/
theorem actual_first_collection_up_condExp_service
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
    ∀ (count : ℕ)
      (hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (s : ℕ)
      (hsElapsed : s = ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      (hspan : s + count ≤ p.T),
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count (by simpa only [hsElapsed] using hspan)
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (_hshort : w < count) (n : Fin B.length) (_hn : 0 < n.val)
      (payload : ReferenceActivePhysicalStep.Payload rate) (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (_hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        B[n.val].input payload l saved)
      (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (_hfi : B[n.val].input.state.followers i = .ordinary old memory)
      (_hip : i ∈ l.pending) (_hpositive : 1 ≤ ReferencePrelaunchFollower.acceptedStart old),
    ∃ U : UpRecord rate,
      U.val = ActiveFollowerQueueOperation.upOfferFields old ∧ 1 ≤ U.val.sigma ∧
      source ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (rate := rate) rewards C_star C_h i B[n.val].input.time U ∧
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i B[n.val].input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 B[n.val].input.time] source =
        (positiveRewardCount rewards B[n.val].input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hce : ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      actual_first_collection_up_condExp rewards C_star C_h control0 i t
  filter_upwards [hce] with source hce
  intro count hcross s hsElapsed hspan E w B hshort n hn payload l saved hReady i old memory hfi hip hpositive
  obtain ⟨U, hU, hUsigma, hsupport, _hprob, _hrecord, hsection⟩ :=
    actual_first_collection_up_service_coefficient rate source rewards C_star C_h count hcross
      s hsElapsed hspan hshort n hn payload l saved hReady i old memory hfi hip hpositive
  exact ⟨U, hU, hUsigma, hsupport, (hce i B[n.val].input.time).trans (hsection control0)⟩

end Bandits.Support.ReferenceFirstCollectionUpConditionalService

end
