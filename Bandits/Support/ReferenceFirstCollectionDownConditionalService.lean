/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceFirstCollectionDownControlGeometry
public import Bandits.Support.ReferenceFirstCollectionUpConditionalService

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual first-collection old-DOWN conditional service

Sources: `sources/zip4/manuscript/06_interruptions.tex:459-490`,
`sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79,92-157`.

This is an internal current-control service calculation on the actual first
collection calendar. It does not claim a stopped-stage, quota, or regret
result.
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

namespace Bandits.Support.ReferenceFirstCollectionDownConditionalService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput
abbrev DownRecord {p : Parameters} (rate : RateInput p) :=
  OrdinaryMessageCodec.DownRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

variable {p : Parameters} {rate : RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The literal old-DOWN analytic readout on the whole original source.
Absence is zero; on a present actual calendar record it reads the selected
follower draw and the executed DOWN positive-feedback test. -/
def actualFirstCollectionDownReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) : ℝ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => 0
  | some r =>
      if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 t).1 = i ∧
          ReferenceActiveAffinePositiveTest.downPositive r.input = true then 1 else 0

/-- The literal original-source test under a fresh complete current control. -/
def actualFirstCollectionDownFreshTest
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) : Set (SourceInput p × TimeControl p) :=
  {z | actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) = 1}

/-- The full-current-control fresh section of the actual-source readout. -/
def actualFirstCollectionDownFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (source : SourceInput p) : ℝ :=
  ∫ control, actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) control)
    ∂ContinuousLearningRows.timeControlLaw p

private def actualFirstCollectionDownRecordCode
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : SourceInput p) :
    Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) := by
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h source
  let start := p.T - codes.length
  exact if start ≤ t.val then codes[t.val - start]? else none

private theorem actualFirstCollectionDownRecordCode_eq_actualRecord
    (rewards : RewardTable p) (C_star C_h : ℝ) (t : Fin p.T)
    (source : SourceInput p) :
    actualFirstCollectionDownRecordCode (rate := rate) rewards C_star C_h t source =
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
  rw [show actualFirstCollectionDownRecordCode (rate := rate) rewards C_star C_h t source =
      (if p.T - codes.length ≤ t.val then
        codes[t.val - (p.T - codes.length)]? else none) by rfl, hstart]
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

private theorem actualFirstCollectionDownReadout_sourcePrefix_factor
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t source =
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
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
      | none => simp [actualFirstCollectionDownReadout, hleft, hright, pref]
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
              (r'.input.rows r.input.selected).2 v = (r.input.rows r.input.selected).2 v := by
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
          have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (r'.input.row.2 t).1 =
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (r.input.row.2 t).1 := by
            change PublicDiscreteDraws.selectedFollowerDraw _ _
              ((r'.input.rows r'.input.selected).2 t).1 =
                PublicDiscreteDraws.selectedFollowerDraw _ _
                  ((r.input.rows r.input.selected).2 t).1
            rw [hselected, hcontrol t (Nat.lt_succ_self t.val)]
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
          rw [← hinputL, ← hinput] at hevidence
          have hsender : ReferenceActivePhysicalStep.upSenderIndex r'.input =
              ReferenceActivePhysicalStep.upSenderIndex r.input := by
            rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw,
              ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw,
              hf'.2.2.1, hf.2.2.1]
            exact hdraw
          have hdiagnostics := congrArg
            ReferenceActivePhysicalHorizon.RoundEvidence.followers hevidence
          have hgrid := congrArg
            ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback hevidence
          change (ReferenceActivePhysicalStep.step r.input).followers =
            (ReferenceActivePhysicalStep.step r'.input).followers at hdiagnostics
          change (ReferenceActivePhysicalStep.step r.input).preparation.feedback.feedback =
            (ReferenceActivePhysicalStep.step r'.input).preparation.feedback.feedback at hgrid
          have hpositive : ReferenceActiveAffinePositiveTest.downPositive r.input =
              ReferenceActiveAffinePositiveTest.downPositive r'.input := by
            rw [ReferenceActiveAffinePositiveTest.record_downPositive,
              ReferenceActiveAffinePositiveTest.record_downPositive, hsender,
              r.output_eq, r'.output_eq, hdiagnostics,
              ReferenceActiveFeedbackCut.FeedbackCut.observations_eq,
              ReferenceActiveFeedbackCut.FeedbackCut.observations_eq, hgrid]
          simp [actualFirstCollectionDownReadout, hleft, hright, pref, hdraw, hpositive]

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

private theorem actualFirstCollectionDownReadout_replacedPrefix
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) (c : TimeControl p) :
    actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) c) =
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
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
  exact (actualFirstCollectionDownReadout_sourcePrefix_factor
    (rate := rate) rewards C_star C_h control0 i t _).symm

private def serviceDownCallFromFollower
    (observation : ReferenceFollowerTailComposition.FollowerObservable p rate) : Bool :=
  (Sum.elim (fun _ : Unit => false) (fun _ => true) observation.2.2.1) &&
    (match observation.2.2.2 with
    | none => false
    | some cut => cut.rawComparison.isSome)

private theorem serviceDownCallFromFollower_eq_reconstruction
    (observation : ReferenceFollowerTailComposition.FollowerObservable p rate) :
    serviceDownCallFromFollower observation =
      ReferenceActiveAffinePositiveTest.downDiagnosticCall
        (ReferenceFollowerTailComposition.reconstructFollowerObservable observation) := by
  rcases observation with ⟨incoming, failure, downInput, downCut⟩
  cases downInput <;> cases downCut <;> rfl

private theorem measurable_serviceDownCallFromFollower :
    Measurable (serviceDownCallFromFollower (p := p) (rate := rate)) := by
  let cut := ReferenceDownReceptionMeasurability.ReferenceDownCutCode p rate
  have hraw : Measurable (fun code : cut => code.rawComparison.isSome) := measurable_of_countable _
  have hcut : Measurable (fun code : Option cut =>
      match code with
      | none => false
      | some value => value.rawComparison.isSome) := by
    convert (hraw.sumElim (measurable_const (a := false))).comp
      (comap_measurable (Equiv.optionEquivSumPUnit cut)) using 1
    funext code
    cases code <;> rfl
  have htag : Measurable (Sum.elim (fun _ : Unit => false)
      (fun _ : FollowerObservationStageMeasurabilityRepair.CarriedState p rate => true)) :=
    Measurable.sumElim measurable_const measurable_const
  have hand : Measurable (fun pair : Bool × Bool => pair.1 && pair.2) :=
    measurable_of_countable _
  have hinput : Measurable (fun obs : ReferenceFollowerTailComposition.FollowerObservable p rate =>
      obs.2.2.1) := by fun_prop
  have hdown : Measurable (fun obs : ReferenceFollowerTailComposition.FollowerObservable p rate =>
      obs.2.2.2) := by fun_prop
  convert hand.comp ((htag.comp hinput).prodMk (hcut.comp hdown)) using 1
  funext obs
  rcases obs with ⟨incoming, failure, downInput, downCut⟩
  cases downInput <;> cases downCut <;> rfl

private def serviceRecordCodeDownPositive
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))
    (i : Fin (p.m - 1)) : Bool := by
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  exact serviceDownCallFromFollower (code.2.2.2.1 i) &&
    decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p
      (ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback code player)).val.val)

private theorem measurable_serviceRecordCodeDownPositive (i : Fin (p.m - 1)) :
    Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => serviceRecordCodeDownPositive code i) := by
  have hcall : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => serviceDownCallFromFollower (code.2.2.2.1 i)) :=
    measurable_serviceDownCallFromFollower.comp (by fun_prop)
  let player := PublicDiscreteDraws.followerPlayer p.two_le_m i
  have hfeedback : Measurable (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) =>
        ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback code player) := by
    unfold ReferenceActiveHorizonMeasurability.roundRecordCodeFeedback
    fun_prop
  have hpositive := (measurable_of_countable fun grid : Fin (D p + 1) =>
    decide (0 < (ActualInitializationPhysicalStep.observationOfGrid p grid).val.val)).comp hfeedback
  have hand : Measurable (fun pair : Bool × Bool => pair.1 && pair.2) :=
    measurable_of_countable _
  exact hand.comp (hcall.prodMk hpositive)

private theorem serviceRecordCodeDownPositive_eq_record
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1))
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i) :
    serviceRecordCodeDownPositive
        (ReferenceActiveHorizonMeasurability.roundRecordCode record) i =
      ReferenceActiveAffinePositiveTest.downPositive record.input := by
  have hsender : ReferenceActivePhysicalStep.upSenderIndex record.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw]
  have hcode := (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs record).2.2.1 i
  have hfront := ReferenceActiveHorizonMeasurability.roundRecordCode_front record
  have hcall : serviceDownCallFromFollower
      ((ReferenceActiveHorizonMeasurability.roundRecordCode record).2.2.2.1 i) =
      ReferenceActiveAffinePositiveTest.downDiagnosticCall (record.output.followers i) := by
    rw [serviceDownCallFromFollower_eq_reconstruction, hcode]
    rfl
  rw [ReferenceActiveAffinePositiveTest.record_downPositive, hsender]
  unfold serviceRecordCodeDownPositive
  rw [hcall, hfront.2.2.2]
  apply congrArg (fun b : Bool => ReferenceActiveAffinePositiveTest.downDiagnosticCall
    (record.output.followers i) && b)
  apply Bool.decide_congr
  simp only [ReferenceActivePhysicalHorizon.RoundRecord.gridFeedback,
    ReferenceActiveFeedbackCut.FeedbackCut.observations_eq]

private def serviceRecordCodeObservation (i : Fin (p.m - 1))
    (code : Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) : Bool :=
  match code with
  | none => false
  | some value => serviceRecordCodeDownPositive value i

private def serviceRecordCodeReadout (i : Fin (p.m - 1))
    (draw : Fin (PublicDiscreteDraws.followerCount p.m))
    (code : Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate))) : ℝ :=
  if draw = i ∧
      serviceRecordCodeObservation i code then 1 else 0

private theorem measurable_serviceRecordCodeObservation (i : Fin (p.m - 1)) :
    Measurable (serviceRecordCodeObservation (p := p) (rate := rate) i) := by
  let α := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  let decode := Equiv.optionEquivSumPUnit α
  have hsum : Measurable (Sum.elim (fun code =>
      serviceRecordCodeDownPositive (p := p) (rate := rate) code i)
      (fun _ : PUnit => false)) :=
    (measurable_serviceRecordCodeDownPositive (p := p) (rate := rate) i).sumElim measurable_const
  convert hsum.comp (comap_measurable decode) using 1
  funext code
  cases code <;> rfl

private theorem measurable_serviceRecordCodeReadout (i : Fin (p.m - 1)) :
    Measurable (fun pair : Fin (PublicDiscreteDraws.followerCount p.m) ×
      Option (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
        serviceRecordCodeReadout (p := p) (rate := rate) i pair.1 pair.2) := by
  let α := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  have hreadout : Measurable (fun pair : Fin (PublicDiscreteDraws.followerCount p.m) × Bool =>
      if pair.1 = i ∧
          pair.2 then (1 : ℝ) else 0) := measurable_of_countable _
  have hpair : Measurable (fun pair :
      Fin (PublicDiscreteDraws.followerCount p.m) × Option α =>
        (pair.1, serviceRecordCodeObservation (p := p) (rate := rate) i pair.2)) := by
    exact measurable_fst.prodMk
      ((measurable_serviceRecordCodeObservation (p := p) (rate := rate) i).comp measurable_snd)
  unfold serviceRecordCodeReadout
  simpa [Function.comp_def] using hreadout.comp hpair

private def actualFirstCollectionDownCodeReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : SourceInput p × TimeControl p) : ℝ := by
  classical
  let replaced := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2
  exact serviceRecordCodeReadout (p := p) (rate := rate) i
    (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1)
    (actualFirstCollectionDownRecordCode (rate := rate) rewards C_star C_h t replaced)

private theorem actualFirstCollectionDownReadout_eq_codeReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p × TimeControl p) :
    actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) =
      actualFirstCollectionDownCodeReadout (rate := rate) rewards C_star C_h i t z := by
  classical
  let replaced := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t replaced with
  | none =>
      have hcode : actualFirstCollectionDownRecordCode (rate := rate)
          rewards C_star C_h t replaced = none := by
        rw [actualFirstCollectionDownRecordCode_eq_actualRecord, hrecord]
        rfl
      simp [actualFirstCollectionDownReadout, actualFirstCollectionDownCodeReadout,
        serviceRecordCodeReadout, serviceRecordCodeObservation, replaced, hrecord, hcode]
  | some record =>
      have hcode : actualFirstCollectionDownRecordCode (rate := rate)
          rewards C_star C_h t replaced =
            some (ReferenceActiveHorizonMeasurability.roundRecordCode record) := by
        rw [actualFirstCollectionDownRecordCode_eq_actualRecord, hrecord]
        rfl
      have hfields := actualRecordInputFields (rate := rate) rewards C_star C_h t
        replaced record hrecord
      have hrow : record.input.row = replaced.1.2 record.input.selected := by
        rw [ReferenceActivePhysicalStep.RoundInput.row, hfields.1, hfields.2.1]
      have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1 =
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (record.input.row.2 t).1 := by
        rw [hrow, hfields.2.1]
        simp [replaced, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex]
      by_cases hselected : PublicDiscreteDraws.selectedFollowerDraw
          p.two_le_m p.m_lt_K z.2.1 = i
      · have hrecordSelected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (record.input.row.2 record.input.time).1 = i := by
          rw [hfields.2.2.1]
          exact hdraw.symm.trans hselected
        have hpositive := serviceRecordCodeDownPositive_eq_record record i hrecordSelected
        simp [actualFirstCollectionDownReadout, actualFirstCollectionDownCodeReadout,
          serviceRecordCodeReadout, serviceRecordCodeObservation, replaced,
          hrecord, hcode, hdraw, hpositive]
      · have hnotRecord : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (record.input.row.2 t).1 ≠ i := fun heq => hselected (hdraw.trans heq)
        simp [actualFirstCollectionDownReadout, actualFirstCollectionDownCodeReadout,
          serviceRecordCodeReadout, serviceRecordCodeObservation, replaced,
          hrecord, hcode, hdraw, hnotRecord]

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

private theorem measurable_actualFirstCollectionDownCodeReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualFirstCollectionDownCodeReadout (rate := rate)
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
  have hlookup : Measurable (fun z =>
      (codes z)[t.val - (p.T - (codes z).length)]?) :=
    (measurable_from_prod_countable_right
      (f := fun v : ℕ × List (ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate)) => v.2[v.1]?)
      (fun n => measurable_serviceCodeLookup n)).comp (hindex.prodMk hcodes)
  have hstartSet : MeasurableSet {z : SourceInput p × TimeControl p |
      p.T - (codes z).length ≤ t.val} :=
    hstart (MeasurableSpace.measurableSet_top : MeasurableSet {n : ℕ | n ≤ t.val})
  let recordCode := fun z : SourceInput p × TimeControl p =>
    actualFirstCollectionDownRecordCode (rate := rate) rewards C_star C_h t (replace z)
  have hrecordCode : Measurable recordCode := by
    change Measurable (fun z : SourceInput p × TimeControl p =>
      if p.T - (codes z).length ≤ t.val then
        (codes z)[t.val - (p.T - (codes z).length)]? else none)
    exact Measurable.ite hstartSet hlookup measurable_const
  have hdraw : Measurable (fun z : SourceInput p × TimeControl p =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      (measurable_fst.comp measurable_snd)
  change Measurable (fun z : SourceInput p × TimeControl p =>
    if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K z.2.1 =
        i ∧
      serviceRecordCodeObservation i (recordCode z) then 1 else 0)
  exact (measurable_serviceRecordCodeReadout (p := p) (rate := rate) i).comp
    (hdraw.prodMk hrecordCode)

/-- The analytic readout always equals zero or one, including the absent
calendar branch. -/
theorem actualFirstCollectionDownReadout_zero_or_one
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t source = 0 ∨
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t source = 1 := by
  classical
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source with
  | none => simp [actualFirstCollectionDownReadout, hrecord]
  | some record =>
      by_cases htest : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (record.input.row.2 t).1 = i ∧
          ReferenceActiveAffinePositiveTest.downPositive record.input = true
      · exact Or.inr (by simp only [actualFirstCollectionDownReadout, hrecord, ite_eq_left htest])
      · exact Or.inl (by simp only [actualFirstCollectionDownReadout, hrecord, ite_eq_right htest])

/-- Pointwise unit bounds for the whole-source readout. -/
theorem actualFirstCollectionDownReadout_bounds
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t source ∧
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t source ≤ 1 := by
  rcases actualFirstCollectionDownReadout_zero_or_one
    (rate := rate) rewards C_star C_h i t source with h | h <;> simp [h]

/-- Joint Borel measurability of the literal readout after replacing the
complete current control, on the original source product space. -/
theorem measurable_actualFirstCollectionDownReadout_replace
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (fun z : SourceInput p × TimeControl p =>
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2)) := by
  have heq := funext (actualFirstCollectionDownReadout_eq_codeReadout
    (rate := rate) rewards C_star C_h i t)
  rw [heq]
  exact measurable_actualFirstCollectionDownCodeReadout rewards C_star C_h i t

/-- The original whole-source readout is Borel measurable. -/
theorem measurable_actualFirstCollectionDownReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t) := by
  have hf := (measurable_actualFirstCollectionDownReadout_replace
    (rate := rate) rewards C_star C_h i t).comp
    (measurable_id.prodMk (ReferenceSourceCurrentControlFreshness.measurable_u_t t))
  convert hf using 1
  funext source
  exact congrArg (actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t)
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_original p t source).symm

/-- Integrability follows from measurability and the unit bounds. -/
theorem integrable_actualFirstCollectionDownReadout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_actualFirstCollectionDownReadout rewards C_star C_h i t).aestronglyMeasurable
  filter_upwards [] with source
  rcases actualFirstCollectionDownReadout_zero_or_one
    (rate := rate) rewards C_star C_h i t source with h | h <;> simp [h]

/-- The complete joint readout gives a Borel fresh event on the actual
calendar code, retained follower DOWN cut, and physical own-feedback code. -/
theorem measurableSet_actualFirstCollectionDownFreshTest
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (actualFirstCollectionDownFreshTest (rate := rate)
      rewards C_star C_h i t) := by
  exact (measurable_actualFirstCollectionDownReadout_replace
    (rate := rate) rewards C_star C_h i t) (measurableSet_singleton 1)

/-- The section indicator is its fresh event's integral. -/
private theorem actualFirstCollectionDownFreshTest_indicator_eq_readout
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p × TimeControl p) :
    (actualFirstCollectionDownFreshTest (rate := rate) rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ)) z =
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) := by
  rcases actualFirstCollectionDownReadout_zero_or_one (rate := rate)
    rewards C_star C_h i t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z.1 z.2) with hz | ho
  · simp [actualFirstCollectionDownFreshTest, hz]
  · simp [actualFirstCollectionDownFreshTest, ho]

private theorem actualFirstCollectionDownFreshSection_eq_indicator_integral
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t source =
      ∫ control, (actualFirstCollectionDownFreshTest (rate := rate) rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
        ∂ContinuousLearningRows.timeControlLaw p := by
  unfold actualFirstCollectionDownFreshSection
  apply integral_congr_ae
  filter_upwards [] with control
  exact (actualFirstCollectionDownFreshTest_indicator_eq_readout
    (rate := rate) rewards C_star C_h i t
    (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)).symm

/-- The fresh whole-control section is between zero and one. -/
theorem actualFirstCollectionDownFreshSection_bounds
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t source ∧
      actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t source ≤ 1 := by
  unfold actualFirstCollectionDownFreshSection
  have hnonneg : ∀ᵐ c ∂ContinuousLearningRows.timeControlLaw p,
      0 ≤ actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) c) :=
    Filter.Eventually.of_forall fun c =>
      (actualFirstCollectionDownReadout_bounds rewards C_star C_h i t _).1
  refine ⟨integral_nonneg_of_ae hnonneg, ?_⟩
  calc
    _ ≤ ∫ _ : TimeControl p, (1 : ℝ) ∂ContinuousLearningRows.timeControlLaw p :=
      integral_mono_of_nonneg hnonneg (integrable_const (1 : ℝ))
        (Filter.Eventually.of_forall fun c =>
          (actualFirstCollectionDownReadout_bounds rewards C_star C_h i t _).2)
    _ = 1 := by simp

/-- Measurability with respect to the complete current-control field. -/
theorem measurable_m_t_actualFirstCollectionDownFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (actualFirstCollectionDownFreshSection (rate := rate)
        rewards C_star C_h control0 i t) := by
  have hreadout := measurable_actualFirstCollectionDownReadout_replace
    (rate := rate) rewards C_star C_h i t
  have hbase := hreadout.stronglyMeasurable.integral_prod_right'
    (ν := ContinuousLearningRows.timeControlLaw p)
  exact hbase.measurable.comp
    (comap_measurable (ReferenceSourceCurrentControlFreshness.c_t p control0 t))

/-- Ambient Borel measurability of the adapted fresh-control section. -/
theorem measurable_actualFirstCollectionDownFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualFirstCollectionDownFreshSection (rate := rate)
      rewards C_star C_h control0 i t) :=
  (measurable_m_t_actualFirstCollectionDownFreshSection rewards C_star C_h control0 i t).mono
    (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comap_le le_rfl

/-- Integrability of the bounded fresh section under the original source law. -/
theorem integrable_actualFirstCollectionDownFreshSection
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (actualFirstCollectionDownFreshSection (rate := rate)
      rewards C_star C_h control0 i t) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_actualFirstCollectionDownFreshSection rewards C_star C_h control0 i t).aestronglyMeasurable
  filter_upwards [] with source
  have hb := actualFirstCollectionDownFreshSection_bounds
    (rate := rate) rewards C_star C_h control0 i t source
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

/-- Conditional expectation in the exact full-current-control sigma field
`m_t`; the theorem does not identify it with a manuscript or stopped field. -/
theorem actual_first_collection_down_condExp
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
      actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t := by
  let B := actualFirstCollectionDownFreshTest (rate := rate) rewards C_star C_h i t
  have hB := measurableSet_actualFirstCollectionDownFreshTest
    (rate := rate) rewards C_star C_h i t
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B =
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t := by
    funext source
    change B.indicator (fun _ => (1 : ℝ))
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source,
        ReferenceSourceCurrentControlFreshness.u_t p t source) = _
    rw [actualFirstCollectionDownFreshTest_indicator_eq_readout,
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUp_restore_sourcePrefix]
    exact (actualFirstCollectionDownReadout_sourcePrefix_factor
      (rate := rate) rewards C_star C_h control0 i t source).symm
  have hroot := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    (p := p) control0 t B hB
  rw [htest] at hroot
  exact hroot.trans (Filter.Eventually.of_forall fun source =>
    (actualFirstCollectionDownFreshSection_eq_indicator_integral
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
    funext j
    simp [Function.comp_def]
  right_inv tuple := by
    apply Subtype.ext
    funext j
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
    _ = S.card * Fintype.card (TupleFiber i ⟨0, hKpos⟩) := by
      simp [Finset.sum_const]

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

/-- Every physical tuple coordinate, including a follower receiver arm, is
uniform under the accepted ordered-tuple sampler. -/
private theorem orderedTupleReceiver_uniform
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
  have hsum :
      (∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x ∈ event then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0) =
      ∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x.val i ∈ S then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hmem : x.val i ∈ S <;> simp [event, hmem]
  calc
    _ = ∑ x : OrderedTupleSampler.Tuple p.m p.K,
        if x.val i ∈ S then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0 := hsum
    _ = ENNReal.ofReal ((S.card : ℝ) / p.K) := by
      change (∑ tuple ∈ (Finset.univ : Finset (OrderedTupleSampler.Tuple p.m p.K)),
        if tuple.val i ∈ S then (p.K.descFactorial p.m : ℝ≥0∞)⁻¹ else 0) = _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hmpos : 0 < p.m := lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m
      have hKpos : 0 < p.K := lt_trans hmpos p.m_lt_K
      rw [tuple_coordinate_filter_card hKpos i S]
      let c := Fintype.card (TupleFiber i ⟨0, hKpos⟩)
      have hdesc : p.K.descFactorial p.m = p.K * c := by
        simpa [c] using (OrderedTupleSampler.card_tuple p.m p.K).symm.trans
          (tuple_total_factorization p.two_le_m p.m_lt_K i)
      have hc : 0 < c := by
        have hpos := Nat.descFactorial_pos.mpr (Nat.le_of_lt p.m_lt_K)
        rw [hdesc] at hpos
        exact Nat.pos_of_mul_pos_left hpos
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

private abbrev DownServiceSliceOutput (p : Parameters) :=
  (Slot × Fin (PublicDiscreteDraws.followerCount p.m)) ×
    OrderedTupleSampler.Tuple p.m p.K

private def downServiceSliceOutput (p : Parameters)
    (x : ContinuousControlSlice.Slice p.m p.K) : DownServiceSliceOutput p :=
  ((PublicDiscreteDraws.slotDraw x,
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x),
    OrderedTupleSampler.sample p.two_le_m p.m_lt_K x)

private def downServiceSliceSet (rewards : RewardTable p) (t : Fin p.T)
    (i : Fin (PublicDiscreteDraws.followerCount p.m)) : Set (DownServiceSliceOutput p) :=
  {z | z.1.1 = PublicDiscreteDraws.downSlot ∧ z.1.2 = i ∧
    z.2.val (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i) ∈
      ReferenceFirstCollectionUpConditionalService.positiveRewardArms rewards t}

private theorem measurable_downServiceSliceOutput : Measurable (downServiceSliceOutput p) := by
  exact ((PublicDiscreteDraws.measurable_slotDraw.prodMk
      (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K)).prodMk
    (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))

private theorem downServiceSlice_probability (rewards : RewardTable p)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    (ContinuousControlSlice.sliceLaw p.m p.K)
      ((downServiceSliceOutput p) ⁻¹' downServiceSliceSet rewards t i) =
        ENNReal.ofReal
          (((ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
            (4 * (p.m - 1 : ℝ) * p.K))) := by
  classical
  let μ := ContinuousControlSlice.sliceLaw p.m p.K
  let pairDraw : ContinuousControlSlice.Slice p.m p.K →
      Slot × Fin (PublicDiscreteDraws.followerCount p.m) := fun x =>
    (PublicDiscreteDraws.slotDraw x,
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x)
  let tupleDraw : ContinuousControlSlice.Slice p.m p.K →
      OrderedTupleSampler.Tuple p.m p.K := OrderedTupleSampler.sample p.two_le_m p.m_lt_K
  let tupleSet : Set (OrderedTupleSampler.Tuple p.m p.K) :=
    {f | f.val (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i) ∈
      ReferenceFirstCollectionUpConditionalService.positiveRewardArms rewards t}
  let drawPair (draws : (j : PublicDiscreteDraws.DrawIndex p.m p.K) →
      PublicDiscreteDraws.DrawOutput j) : Slot × Fin (PublicDiscreteDraws.followerCount p.m) :=
    (draws .slot, draws .selectedFollower)
  have hpairMeas : Measurable drawPair := by
    exact (measurable_pi_apply PublicDiscreteDraws.DrawIndex.slot).prodMk
      (measurable_pi_apply PublicDiscreteDraws.DrawIndex.selectedFollower)
  have hind := PublicDiscreteDraws.indepFun_drawFamily_tupleInputs
    p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
  have hpairMap :
      (fun x => drawPair (PublicDiscreteDraws.drawVector p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) x)) = pairDraw := by
    funext x
    apply Prod.ext <;> rfl
  have htupleMap : OrderedTupleSampler.sampleCube p.m_lt_K ∘
      PublicDiscreteDraws.tupleInputs = tupleDraw := by funext x; rfl
  have hind' : IndepFun pairDraw tupleDraw μ := by
    rw [← hpairMap, ← htupleMap]
    exact hind.comp hpairMeas (OrderedTupleSampler.measurable_sampleCube p.m_lt_K)
  have hpairs : μ (pairDraw ⁻¹' {(PublicDiscreteDraws.downSlot, i)}) =
      ENNReal.ofReal (1 / 4) * ENNReal.ofReal (1 / (p.m - 1 : ℝ)) := by
    have hij : (PublicDiscreteDraws.DrawIndex.slot : PublicDiscreteDraws.DrawIndex p.m p.K) ≠
        PublicDiscreteDraws.DrawIndex.selectedFollower := by intro h; cases h
    have hmass := (PublicDiscreteDraws.iIndepFun_drawFamily
      p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)).indepFun hij
    have hpairmass := hmass.measure_inter_preimage_eq_mul
      ({PublicDiscreteDraws.downSlot} : Set Slot)
      ({i} : Set (Fin (PublicDiscreteDraws.followerCount p.m)))
      (measurableSet_singleton _) (measurableSet_singleton _)
    have hslot : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) .slot = PublicDiscreteDraws.slotDraw := rfl
    have hselected : PublicDiscreteDraws.drawFamily p.two_le_m p.m_lt_K
        (ConstructorDimensions.K_pos p) .selectedFollower =
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K := rfl
    rw [hslot, hselected] at hpairmass
    change μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot} ∩
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) = _ at hpairmass
    have hevent : pairDraw ⁻¹' {(PublicDiscreteDraws.downSlot, i)} =
        PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot} ∩
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i} := by
      ext x
      change (PublicDiscreteDraws.slotDraw x,
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x) =
            (PublicDiscreteDraws.downSlot, i) ↔
        PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i
      constructor
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
      · rintro ⟨hs, hi⟩
        exact Prod.ext hs hi
    calc
      _ = μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot} ∩
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) := by rw [hevent]
      _ = μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot}) *
          μ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) := hpairmass
      _ = _ := by
        have hs : μ (PublicDiscreteDraws.slotDraw ⁻¹' {PublicDiscreteDraws.downSlot}) =
            ENNReal.ofReal (1 / 4) := by
          simpa [μ, PublicDiscreteDraws.slotMass_down] using
            (PublicDiscreteDraws.slotDraw_atom (m := p.m) (K := p.K)
              PublicDiscreteDraws.downSlot)
        have hcast : ((p.m - 1 : ℕ) : ℝ) = (p.m : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.le_trans (by decide : 1 ≤ 2) p.two_le_m)]
          norm_num
        have hi : μ (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ⁻¹' {i}) =
            ENNReal.ofReal (1 / (p.m - 1 : ℝ)) := by
          simpa [μ, PublicDiscreteDraws.equalMass, PublicDiscreteDraws.followerCount, hcast] using
            (PublicDiscreteDraws.selectedFollowerDraw_atom p.two_le_m p.m_lt_K i)
        rw [hs, hi]
  have htuple : μ (tupleDraw ⁻¹' tupleSet) =
      ENNReal.ofReal ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount
        rewards t : ℝ) / p.K) := by
    have h := orderedTupleReceiver_uniform
      (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i)
      (ReferenceFirstCollectionUpConditionalService.positiveRewardArms rewards t)
    change μ (tupleDraw ⁻¹' {tuple : OrderedTupleSampler.Tuple p.m p.K |
      tuple.val (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i) ∈
        ReferenceFirstCollectionUpConditionalService.positiveRewardArms rewards t}) = _
    simpa [tupleSet, tupleDraw,
      ReferenceFirstCollectionUpConditionalService.positiveRewardCount] using h
  have hmass := hind'.measure_inter_preimage_eq_mul
    ({(PublicDiscreteDraws.downSlot, i)} : Set
      (Slot × Fin (PublicDiscreteDraws.followerCount p.m))) tupleSet
    MeasurableSet.of_discrete MeasurableSet.of_discrete
  have hevent : (downServiceSliceOutput p) ⁻¹' downServiceSliceSet rewards t i =
      pairDraw ⁻¹' {(PublicDiscreteDraws.downSlot, i)} ∩ tupleDraw ⁻¹' tupleSet := by
    ext x
    change (PublicDiscreteDraws.slotDraw x = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K x = i ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x).val
          (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i) ∈
            ReferenceFirstCollectionUpConditionalService.positiveRewardArms rewards t) ↔
      ((pairDraw x = (PublicDiscreteDraws.downSlot, i)) ∧ tupleDraw x ∈ tupleSet)
    constructor
    · rintro ⟨hslot, hselected, hreward⟩
      exact ⟨Prod.ext hslot hselected, hreward⟩
    · rintro ⟨hpair, hreward⟩
      exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair, hreward⟩
  rw [hevent, hmass, hpairs, htuple]
  have hmpos : 0 < (p.m : ℝ) - 1 := by
    have hm : (1 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
    linarith
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hq : 0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
      rewards t : ℝ) / ((4 : ℝ) * (p.m - 1) * p.K) := by positivity
  have htupleNonneg : 0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
      rewards t : ℝ) / p.K := by positivity
  have hprod : 0 ≤ (1 / 4 : ℝ) * (1 / (p.m - 1 : ℝ)) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ)),
    ← ENNReal.ofReal_mul hprod]
  congr 1
  field_simp

/-- The positive old-DOWN event on the actual incoming input and its fresh
complete control. -/
def freshCoordinatorDownServiceSet (x : RoundInput p rate)
    (i : Fin (p.m - 1)) : Set (TimeControl p) :=
  {c | PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
    ReferenceActiveAffinePositiveTest.downPositive
      (ReferenceLaterOptionalControlResampling.withControl x c) = true}

private theorem actualFirstCollectionDownReadout_replace_eq_indicator
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) (c : TimeControl p) :
    actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) =
      (freshCoordinatorDownServiceSet r.input i).indicator (fun _ => (1 : ℝ)) c := by
  obtain ⟨r', hr', hinput⟩ :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUp_actualRecord_replace
      rewards C_star C_h control0 t source r hr c
  have hf := actualRecordInputFields (rate := rate) rewards C_star C_h t source r hr
  have hcontrol : r'.input.row.2 t = c := by
    rw [hinput, ← hf.2.2.1]
    exact ReferenceLaterOptionalControlResampling.withControl_currentControl r.input c
  simp only [actualFirstCollectionDownReadout, hr', freshCoordinatorDownServiceSet,
    Set.indicator, Set.mem_ofPred_eq]
  rw [hcontrol, hinput]
  by_cases h : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive
        (ReferenceLaterOptionalControlResampling.withControl r.input c) = true
  · simp only [h]
  · simp only [h, ite_false]

/-- The fresh section equals the actual incoming control event's probability;
the record restoration uses the public source-replacement identity. -/
theorem actualFirstCollectionDownFreshSection_eq_measure
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t source =
      (ContinuousLearningRows.timeControlLaw p).real
        (freshCoordinatorDownServiceSet r.input i) := by
  have hvalue (c : TimeControl p) := actualFirstCollectionDownReadout_replace_eq_indicator
    rewards C_star C_h control0 i t source r hr c
  have hset : freshCoordinatorDownServiceSet r.input i =
      {c | (source, c) ∈ actualFirstCollectionDownFreshTest
        (rate := rate) rewards C_star C_h i t} := by
    ext c
    change c ∈ freshCoordinatorDownServiceSet r.input i ↔
      actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source c) = 1
    rw [hvalue]
    by_cases h : c ∈ freshCoordinatorDownServiceSet r.input i <;> simp [Set.indicator, h]
  have hmeas : MeasurableSet (freshCoordinatorDownServiceSet r.input i) := by
    rw [hset]
    exact measurable_prodMk_left
      (measurableSet_actualFirstCollectionDownFreshTest (rate := rate) rewards C_star C_h i t)
  calc
    _ = ∫ c, (freshCoordinatorDownServiceSet r.input i).indicator
          (fun _ => (1 : ℝ)) c ∂ContinuousLearningRows.timeControlLaw p := by
      unfold actualFirstCollectionDownFreshSection
      apply integral_congr_ae
      filter_upwards [] with c
      rw [actualFirstCollectionDownReadout_replacedPrefix rewards C_star C_h
          control0 i t source c,
        actualFirstCollectionDownReadout_replace_eq_indicator rewards C_star C_h
          control0 i t source r hr c]
    _ = _ := integral_indicator_one hmeas

/-- The explicit DOWN-slot, receiver-arm and affine-hash event. The word is
fixed before integrating the complete accepted current control. -/
def downServiceFormulaSet (rewards : RewardTable p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    Set (TimeControl p) :=
  {c | PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot ∧
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
    AffineChannelLaw.affineHash (c.2 (0, i)) wD = 1 ∧
    0 < rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
      (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i))}

private def downServiceControlOutput (i : Fin (p.m - 1)) (c : TimeControl p) :
    DownServiceSliceOutput p × AffineChannelLaw.Sample (B p) :=
  (downServiceSliceOutput p c.1, c.2 (0, i))

private theorem measurable_downServiceControlOutput (i : Fin (p.m - 1)) :
    Measurable (downServiceControlOutput (p := p) i) := by
  exact ((measurable_downServiceSliceOutput (p := p)).comp measurable_fst).prodMk
    (ContinuousLearningRows.measurePreserving_affineSample p (0, i)).measurable

/-- Exact complete-control probability of the Down slot, selected receiver,
positive original receiver-arm reward, and affine hash bit one. -/
theorem downServiceFormulaSet_probability (rewards : RewardTable p)
    (t : Fin p.T) (i : Fin (p.m - 1))
    (wD : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    (ContinuousLearningRows.timeControlLaw p) (downServiceFormulaSet rewards t i wD) =
      ENNReal.ofReal ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount
        rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
  classical
  let μ := ContinuousLearningRows.timeControlLaw p
  let ν := (AffineChannelLaw.jointLaw (B p)).toMeasure
  let channel : ContinuousLearningRows.Channel p := (0, i)
  let output := downServiceControlOutput (p := p) i
  let sliceSet := downServiceSliceSet rewards t i
  let bitSet : Set (AffineChannelLaw.Sample (B p)) :=
    {sample | AffineChannelLaw.affineHash sample wD = 1}
  have houtput : Measurable output := measurable_downServiceControlOutput i
  have hsliceOutput := measurable_downServiceSliceOutput (p := p)
  have hcontrolAffine : Measurable (fun c : TimeControl p => c.2 channel) :=
    (ContinuousLearningRows.measurePreserving_affineSample p channel).measurable
  have hindep : IndepFun (fun c : TimeControl p => downServiceSliceOutput p c.1)
      (fun c : TimeControl p => c.2 channel) μ := by
    exact (ContinuousLearningRows.indepFun_slice_affineSamples p).comp
      hsliceOutput (measurable_pi_apply channel)
  have houtputLaw : μ.map output =
      ((ContinuousControlSlice.sliceLaw p.m p.K).map (downServiceSliceOutput p)).prod ν := by
    have hmap := hindep.map_prod_eq_prod_map_map
      (hsliceOutput.comp measurable_fst).aemeasurable hcontrolAffine.aemeasurable
    change μ.map (fun c : TimeControl p =>
      (downServiceSliceOutput p c.1, c.2 channel)) = _
    calc
      _ = (μ.map (fun c : TimeControl p => downServiceSliceOutput p c.1)).prod
          (μ.map fun c : TimeControl p => c.2 channel) := hmap
      _ = _ := by
        rw [show μ.map (fun c : TimeControl p => downServiceSliceOutput p c.1) =
            ((μ.map Prod.fst).map (downServiceSliceOutput p)) by
              exact (Measure.map_map hsliceOutput measurable_fst).symm,
          ContinuousLearningRows.map_slice,
          ContinuousLearningRows.map_affineSample p channel]
  have hslice : ((ContinuousControlSlice.sliceLaw p.m p.K).map
      (downServiceSliceOutput p)) sliceSet = ENNReal.ofReal
        ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
          (4 * (p.m - 1 : ℝ) * p.K)) := by
    rw [Measure.map_apply hsliceOutput MeasurableSet.of_discrete]
    exact downServiceSlice_probability rewards t i
  have hbit : ν bitSet = (1 : ℝ≥0∞) / 2 := by
    rw [← AffineChannelLaw.eventProbability_eq_measure]
    exact AffineChannelLaw.affineHash_probability wD 1
  have hset : downServiceFormulaSet rewards t i wD =
      output ⁻¹' (sliceSet ×ˢ bitSet) := by
    ext c
    simp only [downServiceFormulaSet, output, downServiceControlOutput,
      sliceSet, downServiceSliceSet, downServiceSliceOutput, bitSet,
      ReferenceFirstCollectionUpConditionalService.positiveRewardArms,
      Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_univ, true_and, and_left_comm, and_comm]
  have hproduct : MeasurableSet (sliceSet ×ˢ bitSet) := by
    exact MeasurableSet.of_discrete.prod MeasurableSet.of_discrete
  rw [hset, ← Measure.map_apply houtput hproduct, houtputLaw,
    Measure.prod_prod, hslice, hbit]
  have hmpos : 0 < (p.m : ℝ) - 1 := by
    have hm : (1 : ℝ) < p.m := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
    linarith
  have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
  have hq : 0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
      rewards t : ℝ) / (4 * (p.m - 1 : ℝ) * p.K) := by positivity
  have hhalf : (1 : ℝ≥0∞) / 2 = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hhalf, ← ENNReal.ofReal_mul hq]
  congr 1
  field_simp
  ring

/-- On a genuine old-DOWN first-collection branch, the geometry theorem fixes
the stored word first. Its pointwise all-control event is then the explicit
DOWN-slot, receiver-coordinate and positive-original-reward event. -/
theorem actual_first_collection_down_service_coefficient
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
      (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (_hfi : B[n.val].input.state.followers i = .ordinary old memory)
      (_hip : i ∈ l.pending) (_hnone : old.lastDown = none),
    ∃ wD : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      wD = CoordinatorLocalArmChoice.storedDownFlatWord payload i ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        B[n.val].input.time source = some B[n.val] ∧
      (∀ c : TimeControl p,
        c ∈ freshCoordinatorDownServiceSet B[n.val].input i ↔
          c ∈ downServiceFormulaSet rewards B[n.val].input.time i wD) ∧
      (ContinuousLearningRows.timeControlLaw p)
        (freshCoordinatorDownServiceSet B[n.val].input i) =
        ENNReal.ofReal ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards B[n.val].input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) ∧
      ∀ control0 : TimeControl p,
        actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i
          B[n.val].input.time source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards B[n.val].input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  classical
  intro E w B hshort n hn payload l saved hReady i old memory hfi hip hnone
  let x := B[n.val].input
  let t := x.time
  have hspan' : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        count ≤ p.T := by
    simpa only [hsElapsed] using hspan
  obtain ⟨wD, hwD, hall⟩ :=
    ReferenceFirstCollectionDownControlGeometry.actual_first_collection_down_current_control_geometry
      rate source rewards C_star C_h count hcross hspan' hshort n hn
      payload l saved hReady i old memory hfi hip hnone
  have hset : freshCoordinatorDownServiceSet x i = downServiceFormulaSet rewards t i wD := by
    ext c
    change (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
      ReferenceActiveAffinePositiveTest.downPositive
        (ReferenceLaterOptionalControlResampling.withControl x c) = true) ↔
      (PublicDiscreteDraws.slotDraw c.1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K c.1 = i ∧
        AffineChannelLaw.affineHash (c.2 (0, i)) wD = 1 ∧
        0 < rewards t ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K c.1).val
          (ReferenceFirstCollectionDownControlGeometry.followerPlayerAt i)))
    exact (hall c).1
  have hmeasure : (ContinuousLearningRows.timeControlLaw p)
      (freshCoordinatorDownServiceSet x i) = ENNReal.ofReal
        ((ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
          (8 * (p.m - 1 : ℝ) * p.K)) := by
    rw [hset]
    exact downServiceFormulaSet_probability rewards t i wD
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
  refine ⟨wD, hwD, hsourceRecord, ?_, hmeasure, ?_⟩
  · exact Set.ext_iff.mp hset
  · intro control0
    have hmpos : 0 < (p.m : ℝ) - 1 := by
      have hm : (1 : ℝ) < p.m := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
      linarith
    have hKpos : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hden : 0 < (8 : ℝ) * (p.m - 1 : ℝ) * p.K := by positivity
    have hcoeff : 0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
        rewards t : ℝ) / ((8 : ℝ) * (p.m - 1 : ℝ) * p.K) :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hden)
    rw [actualFirstCollectionDownFreshSection_eq_measure rewards C_star C_h control0
      i t source B[n.val] hsourceRecord, measureReal_def, hmeasure,
      ENNReal.toReal_ofReal hcoeff]

/-- With rewards, constants and `control0` fixed before the null set, the
actual conditional expectation has the branch coefficient for every finite
time and follower and all displayed actual branch witnesses. -/
theorem actual_first_collection_down_condExp_service
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
    ∀ (_hshort : w < count)
      (n : Fin B.length) (_hn : 0 < n.val)
      (payload : ReferenceActivePhysicalStep.Payload rate)
      (l : ReferenceActivePhysicalStep.Ledger rate)
      (saved : Option (Fin p.T × Bool))
      (_hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        B[n.val].input payload l saved)
      (i : Fin (p.m - 1)) (old : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p)
      (_hfi : B[n.val].input.state.followers i = .ordinary old memory)
      (_hip : i ∈ l.pending) (_hnone : old.lastDown = none),
    ∃ wD : AffineChannelLaw.Word (AffineBatchDecoder.width p),
      wD = CoordinatorLocalArmChoice.storedDownFlatWord payload i ∧
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        B[n.val].input.time source = some B[n.val] ∧
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i
          B[n.val].input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 B[n.val].input.time] source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards B[n.val].input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hce : ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      actual_first_collection_down_condExp rewards C_star C_h control0 i t
  filter_upwards [hce] with source hce
  intro count hcross s hsElapsed hspan E w B hshort n hn payload l saved hReady i old memory hfi hip hnone
  obtain ⟨wD, hwD, hrecord, _hset, _hmeasure, hsection⟩ :=
    actual_first_collection_down_service_coefficient rate source rewards C_star C_h count
      hcross s hsElapsed hspan hshort n hn payload l saved hReady i old memory hfi hip hnone
  refine ⟨wD, hwD, hrecord, ?_⟩
  exact (hce i B[n.val].input.time).trans (hsection control0)

end Bandits.Support.ReferenceFirstCollectionDownConditionalService

end
