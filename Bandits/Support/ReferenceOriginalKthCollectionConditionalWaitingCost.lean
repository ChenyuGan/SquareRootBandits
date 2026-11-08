/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionPhaseSupport
public import Bandits.Support.ReferenceOriginalKthCollectionCompositeQuota
public import Bandits.Support.PhaseStartConditionalWaiting

import Mathlib.Tactic

/-!
# Conditional waiting cost on the literal original kth C support

The task mask, interval endpoints, and whole-source OLD/FORMED service
readout are the original kth-C objects. The conditional estimate is at the
existing original stopped physical-transfer start.

Sources: ZIP4 `06_interruptions.tex:431-490` and
`05_binary_transport.tex:180-240`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open Bandits.Support.ReferenceOriginalKthCollectionPhaseSupport
open Bandits.Support.ReferenceOriginalKthCollectionSourceSections
open scoped BigOperators Classical ENNReal

namespace Bandits.Support.ReferenceOriginalKthCollectionConditionalWaitingCost

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceOriginalKthCollectionPhaseSupport.RateInput
abbrev SourceInput (p : Parameters) :=
  ReferenceOriginalKthCollectionPhaseSupport.SourceInput p
abbrev GridRewardTable (p : Parameters) :=
  ReferenceOriginalKthCollectionPhaseSupport.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (k : Fin (p.T + 1))

local notation "Source" => SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "F" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
local notation "P" =>
  ReferenceOriginalKthCollectionPhaseSupport.P rate rewards C_star C_h k
local notation "sigma" =>
  ReferenceOriginalKthCollectionPhaseSupport.sigma rate rewards C_star C_h k
local notation "theta" =>
  ReferenceOriginalKthCollectionPhaseSupport.theta rate rewards C_star C_h k
local notation "quota" => 4 * AffineBatchDecoder.quota p
local notation "a" =>
  1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))

/-- The deterministic whole-row positive-reward weight `g_(n+1)`, extended
by zero beyond the original horizon. -/
public def kthCWeight (_rate : RateInput p)
    (rewards : GridRewardTable p) (_C_star _C_h : ℝ)
    (_control0 : ContinuousLearningRows.TimeControl p)
    (_k : Fin (p.T + 1)) (n : ℕ) (_z : Source) : ℝ :=
  if hn : n < p.T then
    (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
      rewards ⟨n, hn⟩ : ℝ)
  else 0

/-- The actual Bool observation of an OLD DOWN or FORMED UP positive
readout on the corresponding original kth-C stage mask. The horizon branch
is explicitly false. -/
public def kthCObservation (_rate : RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (k : Fin (p.T + 1)) (i : Fin (p.m - 1)) (n : ℕ) (z : Source) : Bool :=
  if hn : n < p.T then
    let t : Fin p.T := ⟨n, hn⟩
    decide
      ((z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
          _rate rewards C_star C_h k t i ∧
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := _rate) rewards C_star C_h i t z = 1) ∨
       (z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
          _rate rewards C_star C_h k t i ∧
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := _rate) rewards C_star C_h i t z = 1))
  else false

private theorem actualRecord_input_fields (t : Fin p.T) (z : Source)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t z hz] at hr
    cases hr

private theorem roundInput_eq_of_fields
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time = y.time)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  simp_all

private theorem record_positive_eq_of_temporal_reads
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : r'.input.state = r.input.state)
    (hselected : r'.input.selected = r.input.selected)
    (htime : r'.input.time = r.input.time)
    (hrewards : r'.input.rewards = r.input.rewards)
    (hcurrent : (r.input.rows r.input.selected).2 r.input.time =
      (r'.input.rows r.input.selected).2 r.input.time)
    (hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
        ((r'.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop) :
    ReferenceActiveAffinePositiveTest.downPositive r.input =
        ReferenceActiveAffinePositiveTest.downPositive r'.input ∧
      ReferenceActiveAffinePositiveTest.upPositive r.input =
        ReferenceActiveAffinePositiveTest.upPositive r'.input := by
  have hinput : r'.input =
      ⟨r.input.state, r'.input.rows, r.input.selected, r.input.time,
        r.input.active, r.input.rewards⟩ :=
    roundInput_eq_of_fields rate _ _ hstate rfl hselected htime hrewards
  have hinputL : r.input =
      ⟨r.input.state, r.input.rows, r.input.selected, r.input.time,
        r.input.active, r.input.rewards⟩ :=
    roundInput_eq_of_fields rate _ _ rfl rfl rfl rfl rfl
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    r.input.state r.input.rows r'.input.rows r.input.selected r.input.time
    r.input.active r.input.rewards r.input.rewards hcurrent hpast rfl
  rw [← hinputL, ← hinput] at hevidence
  have hsender : ReferenceActivePhysicalStep.upSenderIndex r'.input =
      ReferenceActivePhysicalStep.upSenderIndex r.input := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw,
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    change PublicDiscreteDraws.selectedFollowerDraw _ _
        ((r'.input.rows r'.input.selected).2 r'.input.time).1 =
      PublicDiscreteDraws.selectedFollowerDraw _ _
        ((r.input.rows r.input.selected).2 r.input.time).1
    rw [hselected, htime, ← hcurrent]
  have hfollowers := congrArg
    ReferenceActivePhysicalHorizon.RoundEvidence.followers hevidence
  have hgrid := congrArg
    ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback hevidence
  have hcoordinator := congrArg
    ReferenceActivePhysicalHorizon.RoundEvidence.coordinator hevidence
  change (ReferenceActivePhysicalStep.step r.input).followers =
    (ReferenceActivePhysicalStep.step r'.input).followers at hfollowers
  change (ReferenceActivePhysicalStep.step r.input).preparation.feedback.feedback =
    (ReferenceActivePhysicalStep.step r'.input).preparation.feedback.feedback at hgrid
  change (ReferenceActivePhysicalStep.step r.input).coordinator =
    (ReferenceActivePhysicalStep.step r'.input).coordinator at hcoordinator
  constructor
  · rw [ReferenceActiveAffinePositiveTest.record_downPositive,
      ReferenceActiveAffinePositiveTest.record_downPositive, hsender,
      r.output_eq, r'.output_eq, hfollowers,
      ReferenceActiveFeedbackCut.FeedbackCut.observations_eq,
      ReferenceActiveFeedbackCut.FeedbackCut.observations_eq, hgrid]
  · rw [ReferenceActiveAffinePositiveTest.record_upPositive,
      ReferenceActiveAffinePositiveTest.record_upPositive,
      r.output_eq, r'.output_eq, hcoordinator]

private theorem actual_readouts_end_factor (i : Fin (p.m - 1))
    (t : Fin p.T) (z : Source) :
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t z =
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) ∧
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t z =
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming
      rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t pref := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 t z,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 t pref]
    exact congrArg (ReferenceSourcePrefixHistoryFiltration.incoming
      rate rewards C_star C_h t)
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
          t.val (t.val + 1) (by omega) z).symm
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t pref with
      | none =>
          change ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) = none at hr'
          simp only [ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout,
            ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout,
            hr, hr', and_self]
      | some r' =>
          simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr',
            Option.map_none, Option.map_some] at hin
          cases hin
  | some r =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t pref with
      | none =>
          simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hr',
            Option.map_none, Option.map_some] at hin
          cases hin
      | some r' =>
          have hstate : r'.input.state = r.input.state := by
            apply ReferenceActivePhysicalStepMeasurability.encodeState_injective
            simpa only [ReferenceSourcePrefixHistoryFiltration.incoming,
              hr, hr', Option.map_some, Option.some.injEq] using hin.symm
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_input_fields rate rewards C_star C_h t z r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_input_fields rate rewards C_star C_h t pref r' hr'
          have hselectedEq : r'.input.selected = r.input.selected := by
            rw [hselected, hselected',
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
          have hcontrol (v : Fin p.T) (hv : v.val < t.val + 1) :
              (r'.input.rows r.input.selected).2 v =
                (r.input.rows r.input.selected).2 v := by
            rw [hrows, hrows', hselected]
            exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control
              control0 (t.val + 1) z v).trans (ite_eq_left hv)
          have hcurrent : (r.input.rows r.input.selected).2 r.input.time =
              (r'.input.rows r.input.selected).2 r.input.time :=
            (hcontrol r.input.time (by rw [htime]; exact Nat.lt_succ_self t.val)).symm
          have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
              ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
                ((r'.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop := by
            intro v hv
            rw [hcontrol v (by rw [htime] at hv; omega)]
          obtain ⟨hdown, hup⟩ := record_positive_eq_of_temporal_reads rate r r'
            hstate hselectedEq (htime'.trans htime.symm)
            (hrewards'.trans hrewards.symm) hcurrent hpast
          have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (r'.input.row.2 t).1 =
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (r.input.row.2 t).1 := by
            change PublicDiscreteDraws.selectedFollowerDraw _ _
                ((r'.input.rows r'.input.selected).2 t).1 = _
            rw [hselectedEq, hcontrol t (Nat.lt_succ_self t.val)]
            rfl
          change ReferenceSourcePrefixHistoryFiltration.actualRecord
            rate rewards C_star C_h t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) = some r' at hr'
          simp only [ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout,
            ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout,
            hr, hr', hdraw, hdown, hup,
            ReferenceFirstCollectionUpConditionalService.followerIndex, and_self]

private theorem kthCObservation_real_eq_sourceReadout
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source) :
    PhaseServiceWaiting.observation
        (kthCObservation rate rewards C_star C_h k) i t.val z =
      ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
        rate rewards C_star C_h k t i z := by
  let oldSet := ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
    rate rewards C_star C_h k t i
  let formedSet := ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
    rate rewards C_star C_h k t i
  let down := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
    (rate := rate) rewards C_star C_h i t z
  let up := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
    (rate := rate) rewards C_star C_h i t z
  have hdisjoint := Set.disjoint_left.mp
    (ReferenceOriginalKthCollectionAwaitedService.kthCOLDSet_disjoint_kthCFORMEDSet
      rate rewards C_star C_h k t i)
  by_cases hold : z ∈ oldSet
  · have hformed : z ∉ formedSet := hdisjoint hold
    have h01 := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout_zero_or_one
      (rate := rate) rewards C_star C_h i t z
    have hbool : PhaseServiceWaiting.observation
        (kthCObservation rate rewards C_star C_h k) i t.val z =
          if down = 1 then 1 else 0 := by
      simp [PhaseServiceWaiting.observation, kthCObservation, oldSet, formedSet,
        down, t.isLt, hold, hformed]
    have hval : (if down = 1 then 1 else 0) = down := by
      rcases h01 with hz | hz <;> simp [down, hz]
    calc
      PhaseServiceWaiting.observation
          (kthCObservation rate rewards C_star C_h k) i t.val z =
          (if down = 1 then 1 else 0) := hbool
      _ = down := hval
      _ = ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
          rate rewards C_star C_h k t i z := by
        simp [ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout,
          ReferenceOriginalKthCollectionSourceSections.kthCOLDReadout,
          ReferenceOriginalKthCollectionSourceSections.kthCFORMEDReadout,
          oldSet, formedSet, down, hold, hformed]
  · by_cases hformed : z ∈ formedSet
    · have h01 := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout_zero_or_one
        (rate := rate) rewards C_star C_h i t z
      have hbool : PhaseServiceWaiting.observation
          (kthCObservation rate rewards C_star C_h k) i t.val z =
            if up = 1 then 1 else 0 := by
        simp [PhaseServiceWaiting.observation, kthCObservation, oldSet, formedSet,
          up, t.isLt, hold, hformed]
      have hval : (if up = 1 then 1 else 0) = up := by
        rcases h01 with hz | hz <;> simp [up, hz]
      calc
        PhaseServiceWaiting.observation
            (kthCObservation rate rewards C_star C_h k) i t.val z =
            (if up = 1 then 1 else 0) := hbool
        _ = up := hval
        _ = ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
            rate rewards C_star C_h k t i z := by
          simp [ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout,
            ReferenceOriginalKthCollectionSourceSections.kthCOLDReadout,
            ReferenceOriginalKthCollectionSourceSections.kthCFORMEDReadout,
            oldSet, formedSet, up, hold, hformed]
    · have hbool : PhaseServiceWaiting.observation
          (kthCObservation rate rewards C_star C_h k) i t.val z = 0 := by
        simp [PhaseServiceWaiting.observation, kthCObservation, oldSet, formedSet,
          t.isLt, hold, hformed]
      have hreadout :
          ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
            rate rewards C_star C_h k t i z = 0 := by
        simp [ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout,
          ReferenceOriginalKthCollectionSourceSections.kthCOLDReadout,
          ReferenceOriginalKthCollectionSourceSections.kthCFORMEDReadout,
          oldSet, formedSet, hold, hformed]
      rw [hbool, hreadout]

private theorem kthCObservation_real_eq_sourceReadout_nat
    (i : Fin (p.m - 1)) (n : ℕ) (z : Source) :
    PhaseServiceWaiting.observation
        (kthCObservation rate rewards C_star C_h k) i n z =
      if hn : n < p.T then
        ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
          rate rewards C_star C_h k ⟨n, hn⟩ i z
      else 0 := by
  by_cases hn : n < p.T
  · simpa [kthCObservation, hn] using
      kthCObservation_real_eq_sourceReadout rate rewards C_star C_h k i
        ⟨n, hn⟩ z
  · simp [PhaseServiceWaiting.observation, kthCObservation, hn]

private theorem actual_kthC_readout_stronglyMeasurable
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[F (t.val + 2)]
      (ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
        rate rewards C_star C_h k t i) := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  let oldSet := ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
    rate rewards C_star C_h k t i
  let formedSet := ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
    rate rewards C_star C_h k t i
  let down := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
    (rate := rate) rewards C_star C_h i t
  let up := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
    (rate := rate) rewards C_star C_h i t
  have hdownEq :
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t =
        down ∘ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) := by
    funext z
    exact (actual_readouts_end_factor rate rewards C_star C_h control0 i t z).1
  have hupEq :
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t =
        up ∘ ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) := by
    funext z
    exact (actual_readouts_end_factor rate rewards C_star C_h control0 i t z).2
  have hOld : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)] oldSet := by
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono
      (by omega : t.val + 1 ≤ t.val + 2) _
      (ReferenceOriginalKthCollectionSourceSections.kthCOLDSet_preRound_measurable
        rate rewards C_star C_h control0 k t i)
  have hFormed : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)] formedSet := by
    exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).mono
      (by omega : t.val + 1 ≤ t.val + 2) _
      (ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet_preRound_measurable
        rate rewards C_star C_h control0 k t i)
  have hdown' : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)]
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t) := by
    rw [show t.val + 2 = (t.val + 1) + 1 by omega,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ, hdownEq]
    exact (ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t).comp
        (comap_measurable (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
          control0 (t.val + 1)))
  have hup' : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)]
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t) := by
    rw [show t.val + 2 = (t.val + 1) + 1 by omega,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ, hupEq]
    exact (ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t).comp
        (comap_measurable (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
          control0 (t.val + 1)))
  change StronglyMeasurable[
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2)]
      (oldSet.indicator down + formedSet.indicator up)
  exact ((hdown'.indicator hOld).stronglyMeasurable).add
    ((hup'.indicator hFormed).stronglyMeasurable)

private theorem kthCObservation_roundEnd_stronglyMeasurable
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T) :
    StronglyMeasurable[F (n + 2)]
      (PhaseServiceWaiting.observation
        (kthCObservation rate rewards C_star C_h k) i n) := by
  let t : Fin p.T := ⟨n, hn⟩
  have hreadout := actual_kthC_readout_stronglyMeasurable
    rate rewards C_star C_h control0 k i t
  have hEq := funext fun z =>
    kthCObservation_real_eq_sourceReadout rate rewards C_star C_h k i t z
  rw [hEq]
  simpa [t] using hreadout

private theorem kthCSourceMasks_subset_pending
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hmask : z ∈ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
        rate rewards C_star C_h k t i ∨
      z ∈ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
        rate rewards C_star C_h k t i) :
    i ∈ P t.val z := by
  rcases hmask with hOld | hFormed
  · rcases hOld with ⟨hstratum, pending, hip, hstage⟩
    unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage at hstage
    cases hd : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z with
    | none => simp [hd] at hstage
    | some data =>
        simp only [hd, Option.map_some] at hstage
        have htuple := Option.some.inj hstage
        have hpend : data.2.1 = pending := congrArg Prod.fst htuple
        have hP : P t.val z = data.2.1 := by
          simp [ReferenceOriginalKthCollectionPhaseSupport.P, t.isLt, hstratum, hd]
        rw [hP, hpend]
        exact hip
  · rcases hFormed with ⟨hstratum, pending, hip, hstage⟩
    unfold ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceStage at hstage
    cases hd : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z with
    | none => simp [hd] at hstage
    | some data =>
        simp only [hd, Option.map_some] at hstage
        have htuple := Option.some.inj hstage
        have hpend : data.2.1 = pending := congrArg Prod.fst htuple
        have hP : P t.val z = data.2.1 := by
          simp [ReferenceOriginalKthCollectionPhaseSupport.P, t.isLt, hstratum, hd]
        rw [hP, hpend]
        exact hip

private theorem kthCSourceReadout_zero_of_not_pending
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hip : i ∉ P t.val z) :
    ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
      rate rewards C_star C_h k t i z = 0 := by
  unfold ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
    ReferenceOriginalKthCollectionSourceSections.kthCOLDReadout
    ReferenceOriginalKthCollectionSourceSections.kthCFORMEDReadout
  have hOld : z ∉ ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
      rate rewards C_star C_h k t i := by
    intro h
    exact hip (kthCSourceMasks_subset_pending rate rewards C_star C_h k t i z
      (Or.inl h))
  have hFormed : z ∉ ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
      rate rewards C_star C_h k t i := by
    intro h
    exact hip (kthCSourceMasks_subset_pending rate rewards C_star C_h k t i z
      (Or.inr h))
  simp [hOld, hFormed]

private theorem kthCObservation_count_eq_source_prefix
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source) :
    (PhaseServiceWaiting.N P (kthCObservation rate rewards C_star C_h k)
      i t.val z : ℝ) =
      ∑ s : Fin t.val,
        ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
          rate rewards C_star C_h k ⟨s.val, s.isLt.trans t.isLt⟩ i z := by
  rw [PhaseServiceWaiting.N_cast_eq_source_sum]
  apply Finset.sum_bij (s := Finset.range t.val) (t := Finset.univ)
    (fun n hn => ⟨n, Finset.mem_range.mp hn⟩)
  · intro n hn
    exact Finset.mem_univ _
  · intro n hn n' hn' heq
    exact congrArg Fin.val heq
  · intro s hs
    refine ⟨s.val, Finset.mem_range.mpr s.isLt, ?_⟩
    apply Fin.ext
    rfl
  · intro n hn
    have hnT : n < p.T := (Finset.mem_range.mp hn).trans t.isLt
    rw [kthCObservation_real_eq_sourceReadout_nat rate rewards C_star C_h k i n z,
      dite_eq_left hnT]
    by_cases hip : i ∈ P n z
    · simp [PhaseServiceWaiting.J, hip]
    · have hzero := kthCSourceReadout_zero_of_not_pending
        rate rewards C_star C_h k ⟨n, hnT⟩ i z (by simpa using hip)
      simp [PhaseServiceWaiting.J, hip, hzero]

private theorem kthCObservation_count_eq_filtered_source_prefix
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source) :
    (PhaseServiceWaiting.N P (kthCObservation rate rewards C_star C_h k)
      i t.val z : ℝ) =
      ∑ s ∈ Finset.univ.filter (fun s : Fin p.T => s.val < t.val),
        ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
          rate rewards C_star C_h k s i z := by
  rw [kthCObservation_count_eq_source_prefix rate rewards C_star C_h k i t z]
  apply Finset.sum_bij (s := Finset.univ)
    (t := Finset.univ.filter (fun s : Fin p.T => s.val < t.val))
    (fun s _ => ⟨s.val, s.isLt.trans t.isLt⟩)
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact s.isLt
  · intro s hs s' hs' heq
    apply Fin.ext
    exact congrArg (fun x : Fin p.T => x.val) heq
  · intro u hu
    refine ⟨⟨u.val, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro s hs
    rfl

private theorem kthC_prechoice_of_mem_pending
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source)
    (hip : i ∈ P t.val z) :
    ∃ data : ReferenceOriginalKthCollectionSourceSections.KthCPrechoiceData rate,
      ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
        rate rewards C_star C_h t z = some data ∧
      i ∈ data.2.1 ∧
      t ∈ ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
        rate rewards C_star C_h z k := by
  have hstratum : ReferenceOriginalKthCollectionSourceSections.kthCStratum
      rate rewards C_star C_h k t z := by
    by_contra hs
    simp [ReferenceOriginalKthCollectionPhaseSupport.P, t.isLt, hs] at hip
  cases hd : ReferenceOriginalKthCollectionSourceSections.kthCPrechoiceData
      rate rewards C_star C_h t z with
  | none =>
      simp [ReferenceOriginalKthCollectionPhaseSupport.P, t.isLt, hstratum, hd] at hip
  | some data =>
      have hip' : i ∈ data.2.1 := by
        simpa [ReferenceOriginalKthCollectionPhaseSupport.P, t.isLt, hstratum, hd] using hip
      have hnonempty : (P t.val z).Nonempty := ⟨i, hip⟩
      have hdate :=
        (ReferenceOriginalKthCollectionPhaseSupport.P_nonempty_iff_mem_kthCDates
          rate rewards C_star C_h k t.val z t.isLt).mp hnonempty
      exact ⟨data, rfl, hip', hdate⟩

private theorem kthCObservation_quota
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : Source)
    (hip : i ∈ P t.val z) :
    PhaseServiceWaiting.N P (kthCObservation rate rewards C_star C_h k)
      i t.val z < quota := by
  obtain ⟨data, hdata, hipData, hdate⟩ :=
    kthC_prechoice_of_mem_pending rate rewards C_star C_h k t i z hip
  have hprefix :=
    ReferenceOriginalKthCollectionCompositeQuota.kthCSourceReadout_prechoice_prefix_lt
      rate rewards C_star C_h z k t i hdate data hdata hipData
  have hN := kthCObservation_count_eq_filtered_source_prefix
    rate rewards C_star C_h k i t z
  have hreal :
      (PhaseServiceWaiting.N P (kthCObservation rate rewards C_star C_h k)
        i t.val z : ℝ) < 4 * (AffineBatchDecoder.quota p : ℝ) := by
    rw [hN]
    exact hprefix
  exact_mod_cast hreal

/-- The literal uncapped original support charge over the accepted actual
kth-C calendar. -/
public def kthCWaitingCharge (_control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (z : Source) : ℝ :=
  ∑ t ∈ ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
      rate rewards C_star C_h z k,
    (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)

/-- The same support charge with the manuscript's capped envelope
`ḡ_t = min(m, g_t)`. -/
public def kthCappedWaitingCharge (_control0 : ContinuousLearningRows.TimeControl p)
    (k : Fin (p.T + 1)) (z : Source) : ℝ :=
  ∑ t ∈ ReferenceOriginalKthCollectionCutoffAlignment.kthCDates
      rate rewards C_star C_h z k,
    min (p.m : ℝ)
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ)

/-- The source constant `B_col` for the actual kth-C support charge. -/
public def B_col : ℝ :=
  (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) / (1 - Real.exp (-1))) *
    (4 * (AffineBatchDecoder.quota p : ℝ) +
      Real.log ((p.m - 1 : ℕ) : ℝ))

/-- The literal support sum is the accepted generic total charge on the same
original pending process and the same physical start and first-empty endpoint.
This also handles an absent `C` phase: its actual start has empty support and
the charge is zero there. -/
public theorem kthCWaitingCharge_eq_totalCharge (z : Source) :
    kthCWaitingCharge rate rewards C_star C_h control0 k z =
      PhaseServiceWaiting.totalCharge P sigma theta
        (kthCWeight rate rewards C_star C_h control0 k) p.T z := by
  have hgeneric :
      PhaseServiceWaiting.totalCharge P sigma theta
          (kthCWeight rate rewards C_star C_h control0 k) p.T z =
        ∑ n ∈ Finset.range p.T,
          if hn : n < p.T then
            if (P n z).Nonempty then
              (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards
                ⟨n, hn⟩ : ℝ)
            else 0
          else 0 := by
    unfold PhaseServiceWaiting.totalCharge PhaseServiceWaiting.A
    apply Finset.sum_congr rfl
    intro n hn
    have hnT := Finset.mem_range.mp hn
    have hphase :=
      ReferenceOriginalKthCollectionPhaseSupport.P_nonempty_iff_phase
        rate rewards C_star C_h k z n
    by_cases hne : (P n z).Nonempty
    · have hs := hphase.mp hne
      simp [kthCWeight, hnT, hne, hs.1, hs.2]
    · simp [hnT, hne]
  calc
    kthCWaitingCharge rate rewards C_star C_h control0 k z =
        ∑ n ∈ Finset.range p.T,
          if hn : n < p.T then
            if (P n z).Nonempty then
              (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards
                ⟨n, hn⟩ : ℝ)
            else 0
          else 0 := by
      unfold kthCWaitingCharge
      rw [ReferenceOriginalKthCollectionPhaseSupport.collection_support_charge_eq
        rate rewards C_star C_h k z]
    _ = PhaseServiceWaiting.totalCharge P sigma theta
          (kthCWeight rate rewards C_star C_h control0 k) p.T z := hgeneric.symm

/-- Pointwise nonnegativity of the capped source charge gives the source
comparison `ḡ` charge ≤ uncapped `g` charge. -/
public theorem kthCappedWaitingCharge_le_kthCWaitingCharge (z : Source) :
    kthCappedWaitingCharge rate rewards C_star C_h control0 k z ≤
      kthCWaitingCharge rate rewards C_star C_h control0 k z := by
  unfold kthCappedWaitingCharge kthCWaitingCharge
  apply Finset.sum_le_sum
  intro t ht
  exact min_le_right _ _

/-- Integrability, localization to every event in the original stopped-start
field, and the conditional-expectation version of the actual kth-C waiting
bound. -/
public theorem kthCWaiting_bounds
    (B : Set Source)
    (hB : MeasurableSet[
      PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma
        (ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
          rate rewards C_star C_h control0 k)] B) :
    Integrable (kthCWaitingCharge rate rewards C_star C_h control0 k) μ ∧
      (∫ z in B, kthCWaitingCharge rate rewards C_star C_h control0 k z ∂μ ≤
        B_col (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B) ∧
      μ[kthCWaitingCharge rate rewards C_star C_h control0 k |
        PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma
          (ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
            rate rewards C_star C_h control0 k)] ≤ᵐ[μ]
        fun _ => B_col (p := p) := by
  let X := kthCObservation rate rewards C_star C_h k
  let w := kthCWeight rate rewards C_star C_h control0 k
  have hdNat : 0 < p.m - 1 := by
    have hm := p.two_le_m
    omega
  have hT : 0 < p.T := ConstructorDimensions.T_pos p
  have hK : 0 < p.K := ConstructorDimensions.K_pos p
  have hq : 0 < quota :=
    Nat.mul_pos (by decide) (AffineBatchDecoder.quota_pos p)
  have hdR : 0 < ((p.m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hdNat
  have hKR : 0 < (p.K : ℝ) := Nat.cast_pos.mpr hK
  have ha : 0 < a := by positivity
  have hsigma :=
    ReferenceOriginalKthCollectionPhaseSupport.sigma_is_pre_round_stopping_time
      rate rewards C_star C_h control0 k
  have htheta :=
    ReferenceOriginalKthCollectionPhaseSupport.theta_is_pre_round_stopping_time
      rate rewards C_star C_h control0 k
  have hP : ∀ i n, n < p.T →
      MeasurableSet[F (n + 1)] {z : Source | i ∈ P n z} := by
    intro i n hn
    exact ReferenceOriginalKthCollectionPhaseSupport.P_mem_preRound_measurable_any
      rate rewards C_star C_h control0 k n i
  have hphase : ∀ n, n < p.T → ∀ z, (P n z).Nonempty →
      sigma z ≤ n + 1 ∧ n + 1 < theta z := by
    intro n hn z hne
    exact (ReferenceOriginalKthCollectionPhaseSupport.P_nonempty_iff_phase
      rate rewards C_star C_h k z n).mp hne
  have hnested : ∀ s t, s ≤ t → t < p.T → ∀ z,
      sigma z ≤ s + 1 → t + 1 < theta z → P t z ⊆ P s z := by
    intro s t hst ht z hs _hbelow
    exact ReferenceOriginalKthCollectionPhaseSupport.P_subset_of_le
      rate rewards C_star C_h k z s t hst hs
  have hwMeas : ∀ n, n < p.T → StronglyMeasurable[F (n + 1)] (w n) := by
    intro n hn
    dsimp only [w, kthCWeight, dite_eq_left hn]
    exact stronglyMeasurable_const
  have hwBound : ∀ n, n < p.T → ∀ z, w n z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
    intro n hn z
    let t : Fin p.T := ⟨n, hn⟩
    have hwEq : w n z =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards t : ℝ) := by
      simp [w, kthCWeight, t, hn]
    rw [hwEq]
    have hcard : ReferenceFirstCollectionUpConditionalService.positiveRewardCount
        rewards t ≤ p.K := by
      unfold ReferenceFirstCollectionUpConditionalService.positiveRewardCount
        ReferenceFirstCollectionUpConditionalService.positiveRewardArms
      calc
        _ ≤ (Finset.univ : Finset (Fin p.K)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = p.K := by simp
    constructor
    · exact Nat.cast_nonneg _
    · exact_mod_cast hcard
  have hXMeas : ∀ i n, n < p.T →
      StronglyMeasurable[F (n + 2)] (PhaseServiceWaiting.observation X i n) := by
    intro i n hn
    exact kthCObservation_roundEnd_stronglyMeasurable
      rate rewards C_star C_h control0 k i n hn
  have hquota : ∀ i n, n < p.T → ∀ z, i ∈ P n z →
      PhaseServiceWaiting.N P X i n z < quota := by
    intro i n hn z hi
    exact kthCObservation_quota rate rewards C_star C_h k i
      ⟨n, hn⟩ z hi
  have hservice : ∀ i n, n < p.T → ∀ᵐ z ∂μ, i ∈ P n z →
      a * w n z ≤ μ[PhaseServiceWaiting.observation X i n | F (n + 1)] z := by
    intro i n hn
    let t : Fin p.T := ⟨n, hn⟩
    have hserviceRoot :=
      ReferenceOriginalKthCollectionAwaitedService.kthCSourceReadout_condExp_service
        rate rewards C_star C_h control0 k t i
    have hsourceCE := hserviceRoot.2.2
    have hobsEq :
        (fun z : Source => PhaseServiceWaiting.observation X i n z) =
          ReferenceOriginalKthCollectionSourceSections.kthCSourceReadout
            rate rewards C_star C_h k t i := by
      funext z
      exact kthCObservation_real_eq_sourceReadout rate rewards C_star C_h k i t z
    have hobsCE :
        μ[PhaseServiceWaiting.observation X i n | F (n + 1)] =ᵐ[μ]
          (ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
              rate rewards C_star C_h k t i ∪
            ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
              rate rewards C_star C_h k t i).indicator
              (fun _ =>
                (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
                  rewards t : ℝ) /
                  (8 * (p.m - 1 : ℝ) * (p.K : ℝ))) := by
      change μ[(fun z : Source => PhaseServiceWaiting.observation X i n z) |
        F (t.val + 1)] =ᵐ[μ] _
      rw [hobsEq]
      simpa [t] using hsourceCE
    have hcoef : (fun z : Source => a * w n z) =ᵐ[μ] fun _ =>
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) /
          (8 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
      filter_upwards [] with z
      change (1 / (8 * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ))) *
          (kthCWeight rate rewards C_star C_h control0 k n z) = _
      dsimp [w, kthCWeight]
      rw [dite_eq_left hn]
      have hm : 1 ≤ p.m := by omega
      rw [Nat.cast_sub hm]
      field_simp [ne_of_gt hdR, ne_of_gt hKR]
      ring
    filter_upwards [hobsCE, hcoef] with z hce hweight
    intro hi
    obtain ⟨data, hdata, hipData, _hdate⟩ :=
      kthC_prechoice_of_mem_pending rate rewards C_star C_h k t i z hi
    have hstratum : ReferenceOriginalKthCollectionSourceSections.kthCStratum
        rate rewards C_star C_h k t z := by
      by_contra hs
      change i ∈ P t.val z at hi
      simp [ReferenceOriginalKthCollectionPhaseSupport.P, t.isLt, hs] at hi
    have hmask :=
      ReferenceOriginalKthCollectionAwaitedService.kthC_pending_mem_OLD_or_FORMED
        rate rewards C_star C_h k t i z hstratum data hdata hipData
    have hzmask : z ∈
        ReferenceOriginalKthCollectionSourceSections.kthCOLDSet
            rate rewards C_star C_h k t i ∪
          ReferenceOriginalKthCollectionSourceSections.kthCFORMEDSet
            rate rewards C_star C_h k t i := hmask
    rw [hce, Set.indicator_of_mem hzmask, ← hweight]
  have htotalInt := PhaseServiceWaiting.totalCharge_exp_integrable μ F P sigma theta w a ha
    hsigma htheta hP hwMeas hphase hwBound
  have hchargeEq :
      (fun z : Source => kthCWaitingCharge rate rewards C_star C_h control0 k z) =
        PhaseServiceWaiting.totalCharge P sigma theta w p.T := by
    funext z
    exact kthCWaitingCharge_eq_totalCharge rate rewards C_star C_h control0 k z
  have hchargeInt : Integrable
      (kthCWaitingCharge rate rewards C_star C_h control0 k) μ := by
    change Integrable (fun z : Source => kthCWaitingCharge
      rate rewards C_star C_h control0 k z) μ
    rw [hchargeEq]
    exact htotalInt.1
  have hset := PhaseStartConditionalWaiting.phase_start_totalCharge_setIntegral_bound
    μ (d := p.m - 1) (T := p.T) (K := p.K) (q := quota)
    hdNat hT hK hq F P X w sigma theta a ha hsigma htheta
    (fun z => (ReferenceOriginalKthCollectionPhaseSupport.endpoint_bounds
      rate rewards C_star C_h k z).1)
    (fun z => (ReferenceOriginalKthCollectionPhaseSupport.endpoint_bounds
      rate rewards C_star C_h k z).2.1)
    (fun z => (ReferenceOriginalKthCollectionPhaseSupport.endpoint_bounds
      rate rewards C_star C_h k z).2.2)
    hP hphase hnested hwMeas hwBound hXMeas hquota hservice B hB
  have hcond := PhaseStartConditionalWaiting.phase_start_totalCharge_condExp_bound
    μ (d := p.m - 1) (T := p.T) (K := p.K) (q := quota)
    hdNat hT hK hq F P X w sigma theta a ha hsigma htheta
    (fun z => (ReferenceOriginalKthCollectionPhaseSupport.endpoint_bounds
      rate rewards C_star C_h k z).1)
    (fun z => (ReferenceOriginalKthCollectionPhaseSupport.endpoint_bounds
      rate rewards C_star C_h k z).2.1)
    (fun z => (ReferenceOriginalKthCollectionPhaseSupport.endpoint_bounds
      rate rewards C_star C_h k z).2.2)
    hP hphase hnested hwMeas hwBound hXMeas hquota hservice
  have hconst :
      ((quota : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
          (PhaseServiceWaiting.kappa * a) = B_col (p := p) := by
    have hkappa : PhaseServiceWaiting.kappa = 1 - Real.exp (-1) := by
      rfl
    have hkappaPos : 0 < 1 - Real.exp (-1) := by
      rw [← hkappa]
      exact PhaseServiceWaiting.kappa_pos
    have hden : (8 : ℝ) * ((p.m - 1 : ℕ) : ℝ) * (p.K : ℝ) ≠ 0 := by
      positivity
    have hm : 1 ≤ p.m := by omega
    have hquotaReal : (quota : ℝ) =
        4 * (AffineBatchDecoder.quota p : ℝ) := by
      norm_cast
    dsimp [B_col]
    rw [hquotaReal, hkappa, Nat.cast_sub hm]
    push_cast
    field_simp [ne_of_gt hkappaPos, hden]
  refine ⟨hchargeInt, ?_, ?_⟩
  · calc
      ∫ z in B, kthCWaitingCharge rate rewards C_star C_h control0 k z ∂μ =
          ∫ z in B, PhaseServiceWaiting.totalCharge P sigma theta w p.T z ∂μ := by
        congr 1
      _ ≤ (((quota : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
            (PhaseServiceWaiting.kappa * a)) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hset
      _ = B_col (p := p) * (BootstrapPrivateRoundStreams.sourceInputLaw p).real B := by rw [hconst]
  · have hcondCharge :
        μ[kthCWaitingCharge rate rewards C_star C_h control0 k |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma] ≤ᵐ[μ]
          fun _ => ((quota : ℝ) + Real.log ((p.m - 1 : ℕ) : ℝ)) /
            (PhaseServiceWaiting.kappa * a) := by
      change μ[(fun z : Source => kthCWaitingCharge
        rate rewards C_star C_h control0 k z) |
          PhaseStartConditionalWaiting.phaseStartSigmaAlgebra F sigma hsigma] ≤ᵐ[μ] _
      rw [hchargeEq]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcond
    simpa only [hconst] using hcondCharge
