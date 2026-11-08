/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalInstallationReleaseSentinelSection

import Mathlib.Tactic

/-!
# Fixed-label signed physical release charge

This module retains the unmasked signed physical deficit on the original
continuous source and conditions only on the current source control.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReleaseRoundKernel
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveReleaseGeometry
open Bandits.Support.ReferenceSourcePrefixHistoryFiltration
open scoped Classical BigOperators

namespace Bandits.Support.ReferenceOriginalInstallationReleaseSignedCharge

variable {p : ConstructorDimensions.Parameters}

/- The entry label is fixed by the caller.  In particular this is not masked
by the pending set, so a supported empty-pending date keeps its signed value. -/
public def actualFixedReleaseSignedDeficit
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if (entry rate rewards C_star C_h s t z).map Prod.fst = some true then
    match actualRecord rate rewards C_star C_h t z with
    | none => 0
    | some r =>
      match ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator with
      | none => 0
      | some M =>
        slowReward (wholeGridRewardRow rewards t) M.slowSet +
          (wholeGridRewardRow rewards t).val
            (r.actions (ActiveRoundActions.coordinator p.two_le_m)) -
          ∑ player : Fin p.m, ((r.ownEntries player).2).val.val
  else 0

private def fixedLabelSignedCodeValue
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (s : ℕ) (t : Fin p.T)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) : ℝ :=
  if (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t code.2.1).1 then
    match ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1 with
    | none => 0
    | some M =>
      slowReward (wholeGridRewardRow rewards t) M.slowSet +
        (wholeGridRewardRow rewards t).val
          (ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
            (ActiveRoundActions.coordinator p.two_le_m)) -
        ∑ player : Fin p.m,
          ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val
  else 0

private theorem actualFixedReleaseSignedDeficit_eq_code
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFixedReleaseSignedDeficit rate rewards C_star C_h s t z =
      ReferenceCollectionOutcomeMeasurability.optionalElim 0
        (fixedLabelSignedCodeValue rate rewards s t)
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t z) := by
  classical
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none =>
      simp [actualFixedReleaseSignedDeficit, ReferenceCalendarActualControlCallbackSections.codeAt,
        ReferenceSourcePrefixHistoryFiltration.entry,
        ReferenceSourcePrefixHistoryFiltration.incoming, hr,
        ReferenceCollectionOutcomeMeasurability.optionalElim]
  | some r =>
      have hfront := ReferenceActiveHorizonMeasurability.roundRecordCode_front r
      have hstate : (ReferenceActiveHorizonMeasurability.roundRecordCode r).2.1 =
          ReferenceActivePhysicalStepMeasurability.encodeState r.input.state := rfl
      have hstoredEncoded :
          ReferenceRetainedReleasePhaseObservation.localStoredPayload
            (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) =
            ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator := by
        rw [ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
          ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
      have hown :=
        (ReferenceActiveHorizonMeasurability.roundRecordCode_reconstructs r).2.2.2.2
      simp only [actualFixedReleaseSignedDeficit,
        ReferenceSourcePrefixHistoryFiltration.entry,
        ReferenceSourcePrefixHistoryFiltration.incoming,
        ReferenceCalendarActualControlCallbackSections.codeAt, hr, Option.map_some,
        ReferenceCollectionOutcomeMeasurability.optionalElim,
        fixedLabelSignedCodeValue, hstate, hstoredEncoded, hfront.2.2.1]
      change (if (some (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state))).map
            Prod.fst = some true then _ else 0) = _
      simp only [Option.map_some, Option.some.injEq]
      split_ifs
      · cases hp : ReferenceAssignmentPayloadPersistence.storedPayload
            r.input.state.coordinator with
        | none => simp
        | some M =>
            simp only
            have hsum : (∑ player : Fin p.m,
                ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
                  (ReferenceActiveHorizonMeasurability.roundRecordCode r) player).2).val.val) =
                ∑ player : Fin p.m, ((r.ownEntries player).2).val.val :=
              Finset.sum_congr rfl (fun player _ =>
                congrArg (fun e => (e.2).val.val) (hown player))
            rw [hsum]
      · rfl

private theorem fixedLabelSignedCodeValue_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (s : ℕ) (t : Fin p.T) :
    Measurable (fixedLabelSignedCodeValue rate rewards s t) := by
  classical
  let Code := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  let Payload := ReferenceActivePhysicalStep.Payload rate
  have hstate : Measurable (fun code : Code => code.2.1) := measurable_fst.comp measurable_snd
  have hstored : Measurable (fun code : Code =>
      ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1) :=
    (ReferenceReleaseStrictPastFactor.measurable_localStoredPayload rate).comp hstate
  have hslowSet : Measurable (fun M : Payload => M.slowSet.val) := by
    change Measurable (fun M : Payload =>
      (LaterAssignmentStartMeasurability.payloadObservation M).2.2.1)
    exact measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp (comap_measurable _)))
  have hslow : Measurable (fun M : Payload => slowReward (wholeGridRewardRow rewards t) M.slowSet) :=
    (measurable_of_countable (fun U : Finset (Fin p.K) =>
      ∑ a ∈ U, (wholeGridRewardRow rewards t).val a)).comp hslowSet
  have haction : Measurable (fun code : Code =>
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
        (ActiveRoundActions.coordinator p.two_le_m)) :=
    (ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry
      (ActiveRoundActions.coordinator p.two_le_m)).fst
  have hreward : Measurable (fun code : Code =>
      (wholeGridRewardRow rewards t).val
        (ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
          (ActiveRoundActions.coordinator p.two_le_m))) :=
    (measurable_of_countable _).comp haction
  have hown (player : Fin p.m) : Measurable (fun code : Code =>
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val) :=
    (ReferenceActiveHorizonMeasurability.measurable_roundRecordCodeOwnEntry player).snd.subtype_val.subtype_val
  have hsum : Measurable (fun code : Code => ∑ player : Fin p.m,
      ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry code player).2).val.val) :=
    Finset.measurable_fun_sum _ (fun player _ => hown player)
  have hvalue : Measurable (fun v : Payload × Code =>
      slowReward (wholeGridRewardRow rewards t) v.1.slowSet +
        (wholeGridRewardRow rewards t).val
          (ReferenceActiveHorizonMeasurability.roundRecordCodeActions v.2
            (ActiveRoundActions.coordinator p.two_le_m)) -
        ∑ player : Fin p.m,
          ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry v.2 player).2).val.val) :=
    ((hslow.comp measurable_fst).add (hreward.comp measurable_snd)).sub
      (hsum.comp measurable_snd)
  have hmap := (ReferenceCollectionOutcomeMeasurability.measurable_mapOptional _ hvalue).comp
    (hstored.prodMk measurable_id)
  have helim := ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
    (0 : ℝ) id measurable_id
  have hgate := (ReferenceReleaseStrictPastFactor.measurable_localReleaseEntry rate s t).comp hstate
  have hgateTrue : MeasurableSet {code : Code |
      (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t code.2.1).1 = true} :=
    measurableSet_eq_fun (measurable_fst.comp hgate) (measurable_const (a := true))
  have hmeas : Measurable (fun code : Code =>
      if (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate s t code.2.1).1 = true then
        ReferenceCollectionOutcomeMeasurability.optionalElim 0 id
          (ReferenceCollectionOutcomeMeasurability.mapOptional
            (fun v : Payload × Code =>
              slowReward (wholeGridRewardRow rewards t) v.1.slowSet +
                (wholeGridRewardRow rewards t).val
                  (ReferenceActiveHorizonMeasurability.roundRecordCodeActions v.2
                    (ActiveRoundActions.coordinator p.two_le_m)) -
                ∑ player : Fin p.m,
                  ((ReferenceActiveHorizonMeasurability.roundRecordCodeOwnEntry
                    v.2 player).2).val.val)
            (ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1, code))
      else (0 : ℝ)) := (helim.comp hmap).ite hgateTrue measurable_const
  convert hmeas using 1
  funext code
  dsimp only [fixedLabelSignedCodeValue, Function.comp_def,
    ReferenceCollectionOutcomeMeasurability.mapOptional]
  split_ifs with hg
  · cases hM : ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1 <;>
      simp [ReferenceCollectionOutcomeMeasurability.optionalElim]
  · rfl

theorem actualFixedReleaseSignedDeficit_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s : ℕ) (t : Fin p.T) :
    Measurable (actualFixedReleaseSignedDeficit rate rewards C_star C_h s t) := by
  have hm := (ReferenceCollectionOutcomeMeasurability.measurable_optionalElim (0 : ℝ) _
    (fixedLabelSignedCodeValue_measurable rate rewards s t)).comp
      (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
        rate rewards C_star C_h t)
  convert hm using 1
  funext z
  exact actualFixedReleaseSignedDeficit_eq_code rate rewards C_star C_h s t z

theorem actualFixedReleaseSignedDeficit_abs_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    |actualFixedReleaseSignedDeficit rate rewards C_star C_h s t z| ≤ 2 * (p.m : ℝ) := by
  classical
  unfold actualFixedReleaseSignedDeficit
  split_ifs
  · cases hrec : actualRecord rate rewards C_star C_h t z with
    | none => simp
    | some r =>
      cases hM : ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator with
      | none => simp [hM]
      | some M =>
        simp only [hM]
        have hslow0 : 0 ≤ slowReward (wholeGridRewardRow rewards t) M.slowSet :=
          Finset.sum_nonneg (fun a _ => ((wholeGridRewardRow rewards t).property a).1)
        have hcard : (M.slowSet.val.card : ℝ) + 1 = (p.m : ℝ) := by
          exact_mod_cast CanonicalOrientedSetLaw.slowSet_card p.two_le_m M.slowSet
        have hslow1 : slowReward (wholeGridRewardRow rewards t) M.slowSet ≤ (p.m : ℝ) := by
          calc
            _ ≤ ∑ _a ∈ M.slowSet.val, (1 : ℝ) :=
              Finset.sum_le_sum (fun a _ => ((wholeGridRewardRow rewards t).property a).2)
            _ = (M.slowSet.val.card : ℝ) := by simp
            _ ≤ (p.m : ℝ) := by linarith
        have hreward := (wholeGridRewardRow rewards t).property
          (r.actions (ActiveRoundActions.coordinator p.two_le_m))
        have hown0 : 0 ≤ ∑ player : Fin p.m, ((r.ownEntries player).2).val.val :=
          Finset.sum_nonneg (fun player _ => (r.ownEntries player).2.val.property.1)
        have hown1 : (∑ player : Fin p.m, ((r.ownEntries player).2).val.val) ≤ (p.m : ℝ) := by
          calc
            _ ≤ ∑ _player : Fin p.m, (1 : ℝ) :=
              Finset.sum_le_sum (fun player _ => (r.ownEntries player).2.val.property.2)
            _ = (p.m : ℝ) := by simp
        have hmNat : 1 ≤ p.m := Nat.le_trans (by decide) p.two_le_m
        have hm : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hmNat
        rcases hreward with ⟨hreward0, hreward1⟩
        exact abs_le.mpr
          ⟨by linarith only [hslow0, hreward0, hown1, hm],
            by linarith only [hslow1, hreward1, hown0, hm]⟩
  · simp

theorem actualFixedReleaseSignedDeficit_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s : ℕ) (t : Fin p.T) :
    Integrable (actualFixedReleaseSignedDeficit rate rewards C_star C_h s t)
      (sourceInputLaw p) := by
  apply (integrable_const (2 * (p.m : ℝ))).mono'
    (actualFixedReleaseSignedDeficit_measurable rate rewards C_star C_h s t).aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_eq_abs] using
    actualFixedReleaseSignedDeficit_abs_le rate rewards C_star C_h s t z

public theorem actualFixedReleaseSignedDeficit_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFixedReleaseSignedDeficit rate rewards C_star C_h s t z =
      actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
        (sourcePrefix control0 (t.val + 1) z) := by
  rw [actualFixedReleaseSignedDeficit_eq_code rate rewards C_star C_h s t z,
    actualFixedReleaseSignedDeficit_eq_code rate rewards C_star C_h s t
      (sourcePrefix control0 (t.val + 1) z),
    ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
      rate rewards C_star C_h control0 t z]

private theorem sourcePrefix_successor_replace_current
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (u : ContinuousLearningRows.TimeControl p) :
    sourcePrefix control0 (t.val + 1)
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (sourcePrefix control0 t.val z) u := by
  rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore,
    ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current control0 t z u]
  congr 1
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]

public theorem actualFixedReleaseSignedDeficit_replace_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (u : ContinuousLearningRows.TimeControl p) :
    actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
      actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) u) := by
  rw [actualFixedReleaseSignedDeficit_prefix rate rewards C_star C_h control0 s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u),
    sourcePrefix_successor_replace_current,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]

public theorem actualFixedReleaseSignedDeficit_restore
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFixedReleaseSignedDeficit rate rewards C_star C_h s t z =
      actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z)
          (ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    ReferenceSourceCurrentControlFreshness.u_t, ←
      ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore]
  exact actualFixedReleaseSignedDeficit_prefix rate rewards C_star C_h control0 s t z

public def actualFixedReleaseSignedDeficitControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (s : ℕ) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  ∫ u, actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
    ∂timeControlLaw p

public theorem actualFixedReleaseSignedDeficit_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (s : ℕ) (t : Fin p.T) :
    (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t := by
  let B : ℝ := 2 * (p.m : ℝ)
  let c := ReferenceSourceCurrentControlFreshness.c_t p control0 t
  let u := ReferenceSourceCurrentControlFreshness.u_t p t
  let f : BootstrapPrivateRoundStreams.SourceInput p ×
      ContinuousLearningRows.TimeControl p → ℝ := fun v =>
    actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2) / B
  have hmNat : 0 < p.m := Nat.lt_of_lt_of_le (by decide : 0 < 2) p.two_le_m
  have hm : 0 < (p.m : ℝ) := by exact_mod_cast hmNat
  have hB : 0 < B := by dsimp [B]; positivity
  have hf : Measurable f := by
    exact ((actualFixedReleaseSignedDeficit_measurable rate rewards C_star C_h s t).comp
      (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)).div_const B
  have hbound : ∀ v, ‖f v‖ ≤ 1 := by
    intro v
    have habs := actualFixedReleaseSignedDeficit_abs_le rate rewards C_star C_h s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2)
    change ‖actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2) / B‖ ≤ 1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hB]
    exact (div_le_iff₀ hB).2 (by simpa [B] using habs)
  have hce := ReferenceFirstLiveInspectedFastCollision.source_control_weighted_condExp
    control0 t f hf hbound
  have hscaled : (actualFixedReleaseSignedDeficit rate rewards C_star C_h s t) =
      fun z => B * f (c z, u z) := by
    funext z
    rw [actualFixedReleaseSignedDeficit_restore rate rewards C_star C_h control0 s t z]
    simp only [f, c, u, B, div_eq_mul_inv]
    field_simp [ne_of_gt hB]
  have hsection : (fun z => B * ∫ v,
      f (c z, v) ∂timeControlLaw p) =
      actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t := by
    funext z
    rw [actualFixedReleaseSignedDeficitControlSection]
    have hfun : (fun v : ContinuousLearningRows.TimeControl p =>
        actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v)) =
        fun v => B * f (c z, v) := by
      funext v
      rw [actualFixedReleaseSignedDeficit_replace_prefix rate rewards C_star C_h
        control0 s t z v]
      dsimp only [f, c, B]
      field_simp [ne_of_gt hB]
    calc
      B * ∫ v, f (c z, v) ∂timeControlLaw p =
          ∫ v, B * f (c z, v) ∂timeControlLaw p := by rw [integral_const_mul]
      _ = ∫ v, actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v)
          ∂timeControlLaw p := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact (congrFun hfun v).symm
  have hscaledCE : (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
      sourcePrefixFiltration control0 (t.val + 1)] =
      (sourceInputLaw p)[(fun z => B * f (c z, u z)) |
        sourcePrefixFiltration control0 (t.val + 1)] :=
    congrArg (fun g => (sourceInputLaw p)[g | sourcePrefixFiltration control0 (t.val + 1)]) hscaled
  have hce' : (sourceInputLaw p)[(fun z => f (c z, u z)) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      (fun z => ∫ v, f (c z, v) ∂timeControlLaw p) := by
    simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t] using hce
  filter_upwards [MeasureTheory.condExp_smul (μ := sourceInputLaw p)
      (m := sourcePrefixFiltration control0 (t.val + 1)) B
      (fun z => f (c z, u z)), hce'] with z hsmul hce
  have hsmul' : (sourceInputLaw p)[(fun x => B * f (c x, u x)) |
      sourcePrefixFiltration control0 (t.val + 1)] z =
      B * (sourceInputLaw p)[(fun x => f (c x, u x)) |
        sourcePrefixFiltration control0 (t.val + 1)] z := by
    change (sourceInputLaw p)[(fun x => B * f (c x, u x)) |
      sourcePrefixFiltration control0 (t.val + 1)] z =
      B * (sourceInputLaw p)[(fun x => f (c x, u x)) |
        sourcePrefixFiltration control0 (t.val + 1)] z at hsmul
    exact hsmul
  calc
    (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
        sourcePrefixFiltration control0 (t.val + 1)] z =
        (sourceInputLaw p)[(fun x => B * f (c x, u x)) |
          sourcePrefixFiltration control0 (t.val + 1)] z := congrFun hscaledCE z
    _ = B * (sourceInputLaw p)[(fun x => f (c x, u x)) |
        sourcePrefixFiltration control0 (t.val + 1)] z := hsmul'
    _ = B * ∫ v, f (c z, v) ∂timeControlLaw p := by rw [hce]
    _ = actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z :=
      congrFun hsection z

public theorem actualFixedReleaseSignedDeficit_condExp_all
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ, ∀ t : Fin p.T,
      (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
        sourcePrefixFiltration control0 (t.val + 1)] z =
        actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z := by
  simp only [ae_all_iff]
  intro s t
  exact actualFixedReleaseSignedDeficit_condExp rate rewards C_star C_h control0 s t

private theorem actual_later_local_release_signed_section_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (s : ℕ)
    (b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) (t : Fin p.T)
    (hs : s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val)
    (hb : ReferenceCollectionPhaseHistory.laterChosen
      (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[b.val].input = true)
    (hg : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t z).map
      Prod.fst = some true) :
    ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (selected : ReferenceActivePhysicalStep.Selection r.input),
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r ∧
      r.output.preparation.coordinator.selection = some selected ∧
      ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h s t z =
        ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r ∧
      actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z ≤
        (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
          ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelControlSection
            rate rewards C_star C_h s t z ∧
      (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r = ∅ →
        actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z ≤ 0) := by
  classical
  let birth := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val
  have hgate : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birth t z).map
      Prod.fst = some true := by
    simpa only [hs] using hg
  obtain ⟨r0, hr0, _ht0, registers, owned, base, selected0, states0, memories0,
    hstate, hpayload, _hpending0, hselection0, _hpendingView0, _hcutoff0, _hlive0,
    _hvalid0, _hordinary0, _hfields0, _hcarry0, _hcarryNext0, _hweights0,
    _hfast0, _hactions0, _hfeedback0, _hcost0, _hcontinue0⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame
      rate rewards C_star C_h control0 z b t hb hgate
  obtain ⟨r, selected, _states, _memories, hr, hselection, hall⟩ :=
    ReferenceOriginalInstallationReleasePhysicalFrame.actual_later_local_release_physical_frame_all_controls
      rate rewards C_star C_h control0 z b t hb hgate
  have hrEq : r0 = r := Option.some.inj (hr0.symm.trans hr)
  subst r0
  have hselectedEq : selected0 = selected := Option.some.inj (hselection0.symm.trans hselection)
  subst selected0
  have hstored : ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator =
      some selected.view.payload := by
    rw [hstate]
    simp only [ReferenceAssignmentPayloadPersistence.storedPayload_live, hpayload]
  have hobs : ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h
      birth t z = ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r := by
    have hgateBool : (ReferenceRetainedReleasePhaseObservation.localReleaseGate rate birth t
        (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state)) = true := by
      simpa only [ReferenceSourcePrefixHistoryFiltration.entry,
        ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
        ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
        Option.map_some, Option.some.injEq] using hgate
    simp only [ReferenceSourcePrefixHistoryFiltration.pending,
      ReferenceSourcePrefixHistoryFiltration.entry,
      ReferenceSourcePrefixHistoryFiltration.incoming, hr, Option.map_some,
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry,
      ite_eq_left hgateBool]
    rw [ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
      ReferenceActivePhysicalStepMeasurability.decodeState_encodeState, hstored]
    simp [ReferenceRetainedReleasePhaseObservation.localReleasePending,
      hgateBool, ReferencePhysicalReleaseQuota.pendingSet]
    rw [_ht0]
  have hobsS : ReferenceSourcePrefixHistoryFiltration.pending rate rewards C_star C_h s t z =
      ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r := by
    simpa only [hs] using hobs
  have hsectionBound : actualFixedReleaseSignedDeficitControlSection
      rate rewards C_star C_h s t z ≤
      (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
        ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
          (selected.view.payload.assignment.assigned i)) +
        ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelControlSection
          rate rewards C_star C_h s t z ∧
      (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r = ∅ →
        actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z ≤ 0) := by
    let P := ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r
    have hDmeas : Measurable (fun u : ContinuousLearningRows.TimeControl p =>
        actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) :=
      (actualFixedReleaseSignedDeficit_measurable rate rewards C_star C_h s t).comp
        ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
          (measurable_const.prodMk measurable_id))
    have hDint : Integrable (fun u : ContinuousLearningRows.TimeControl p =>
        actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u))
        (ContinuousLearningRows.timeControlLaw p) := by
      apply (integrable_const (2 * (p.m : ℝ))).mono' hDmeas.aestronglyMeasurable
      filter_upwards with u
      exact actualFixedReleaseSignedDeficit_abs_le rate rewards C_star C_h s t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
    have hSmeas : Measurable (fun u : ContinuousLearningRows.TimeControl p =>
        ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
          rate rewards C_star C_h s t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) :=
      (ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge_measurable
        rate rewards C_star C_h s t).comp
        ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
          (measurable_const.prodMk measurable_id))
    have hSint : Integrable (fun u : ContinuousLearningRows.TimeControl p =>
        ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
          rate rewards C_star C_h s t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u))
        (ContinuousLearningRows.timeControlLaw p) := by
      apply (integrable_const (1 : ℝ)).mono' hSmeas.aestronglyMeasurable
      filter_upwards with u
      obtain ⟨hzero, hone⟩ :=
        ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge_bounds
          rate rewards C_star C_h s t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hzero] using hone
    have hpoint (u : ContinuousLearningRows.TimeControl p) :
        actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) ≤
          (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
            ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
              rate rewards C_star C_h s t
                (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) := by
      have hcode := ReferencePostReplacementCollectionReleaseResamplingData.incomingStateCode_replace_current
        rate rewards C_star C_h control0 t z u
      have hentryU : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birth t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
        ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birth t z := by
        change Option.map (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate birth t)
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) = _
        exact congrArg (Option.map (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate birth t))
          hcode
      have hgateU : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)).map Prod.fst =
          some true := by
        rw [hs, hentryU]
        exact hgate
      obtain ⟨ru, vu, hru, hinput, hstateU, _htimeU, hselectionU, hviewU,
        _hweightsU, _hpendingChoiceU, _hcutoffU, _hliveU, _hordinaryU, _hfieldsU,
        hpendingU, _hfastU, _hactionsU, _hfeedbackU, _hownU, hcostU, _hnonposU⟩ := hall u
      have hstoredU : ReferenceAssignmentPayloadPersistence.storedPayload ru.input.state.coordinator =
          some vu.view.payload := by
        rw [hstateU, hstate]
        simp only [ReferenceAssignmentPayloadPersistence.storedPayload_live, hpayload, hviewU]
      have hcoordArm : ru.actions (ActiveRoundActions.coordinator p.two_le_m) = vu.arm := by
        change ru.output.preparation.arms.actions _ = _
        rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
        change ReferenceActivePhysicalStep.DispatchCut.arm ru.output.preparation.coordinator = _
        simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hselectionU]
      have hD : actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
          slowReward (wholeGridRewardRow rewards t) vu.view.payload.slowSet +
            (wholeGridRewardRow rewards t).val vu.arm -
              ∑ player : Fin p.m, ((ru.ownEntries player).2).val.val := by
        unfold actualFixedReleaseSignedDeficit
        simp only [hgateU, ite_true, hru, hstoredU]
        rw [hcoordArm]
      have hsent : ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
          rate rewards C_star C_h s t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
          if vu.arm = vu.view.payload.assignment.auxiliary ∧
              (ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru).Nonempty then
            (wholeGridRewardRow rewards t).val vu.view.payload.assignment.auxiliary else 0 := by
        unfold ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
        simp only [hgateU, ite_true, hru, hselectionU,
          ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm,
          ReleaseRoundKernel.auxiliaryFastArm]
        rfl
      have hpendingFixed : ReferencePhysicalReleaseQuota.pendingSet selected.view.payload ru =
          ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r := by
        simpa only [hviewU] using hpendingU
      have hsumFixed :
          (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload ru,
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i)) =
          (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) := by
        change (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload ru,
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i)) =
          (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i))
        exact congrArg (fun S : Finset (ActiveRoundActions.Follower p.m) =>
          ∑ i ∈ S, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) hpendingFixed
      have hcostFixed :
          slowReward (wholeGridRewardRow rewards t) vu.view.payload.slowSet +
            (wholeGridRewardRow rewards t).val vu.arm -
              ∑ player : Fin p.m, ((ru.ownEntries player).2).val.val ≤
          (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
            (if vu.arm = vu.view.payload.assignment.auxiliary ∧
                (ReferencePhysicalReleaseQuota.pendingSet vu.view.payload ru).Nonempty then
              (wholeGridRewardRow rewards t).val vu.view.payload.assignment.auxiliary else 0) := by
        rw [← hsumFixed]
        simpa only [hviewU] using hcostU
      rw [hD, hsent]
      exact hcostFixed
    have hzeroP (u : ContinuousLearningRows.TimeControl p)
        (hP : P = ∅) :
        actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) ≤ 0 := by
      have hcode := ReferencePostReplacementCollectionReleaseResamplingData.incomingStateCode_replace_current
        rate rewards C_star C_h control0 t z u
      have hentryU : ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birth t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
        ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h birth t z := by
        change Option.map (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate birth t)
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)) = _
        exact congrArg (Option.map (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate birth t))
          hcode
      have hgateU : (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)).map Prod.fst =
          some true := by
        rw [hs, hentryU]
        exact hgate
      obtain ⟨ru, vu, hru, hinput, hstateU, _htimeU, hselectionU, hviewU,
        _hweightsU, _hpendingChoiceU, _hcutoffU, _hliveU, _hordinaryU, _hfieldsU,
        hpendingU, _hfastU, _hactionsU, _hfeedbackU, _hownU, _hcostU, hnonposU⟩ := hall u
      have hstoredU : ReferenceAssignmentPayloadPersistence.storedPayload ru.input.state.coordinator =
          some vu.view.payload := by
        rw [hstateU, hstate]
        simp only [ReferenceAssignmentPayloadPersistence.storedPayload_live, hpayload, hviewU]
      have hcoordArm : ru.actions (ActiveRoundActions.coordinator p.two_le_m) = vu.arm := by
        change ru.output.preparation.arms.actions _ = _
        rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
        change ReferenceActivePhysicalStep.DispatchCut.arm ru.output.preparation.coordinator = _
        simp only [ReferenceActivePhysicalStep.DispatchCut.arm, hselectionU]
      have hD : actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u) =
          slowReward (wholeGridRewardRow rewards t) vu.view.payload.slowSet +
            (wholeGridRewardRow rewards t).val vu.arm -
              ∑ player : Fin p.m, ((ru.ownEntries player).2).val.val := by
        unfold actualFixedReleaseSignedDeficit
        simp only [hgateU, ite_true, hru, hstoredU]
        rw [hcoordArm]
      rw [hD]
      apply hnonposU
      rw [hpendingU]
      simpa only [P] using hP
    have hmono := integral_mono hDint
      ((integrable_const (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
        (selected.view.payload.assignment.assigned i))).add hSint)
      hpoint
    have hsectionIdentity :
        (∫ u, actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
          ∂ContinuousLearningRows.timeControlLaw p) =
        actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z := rfl
    have hsumIntegral :
        (∫ u, (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
          ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
            rate rewards C_star C_h s t
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
          ∂ContinuousLearningRows.timeControlLaw p) =
        (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
          (selected.view.payload.assignment.assigned i)) +
          ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelControlSection
            rate rewards C_star C_h s t z := by
      rw [integral_add (integrable_const _) hSint, integral_const]
      simp [ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelControlSection]
    constructor
    · calc
        actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z =
            (∫ u, actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
              ∂ContinuousLearningRows.timeControlLaw p) := hsectionIdentity.symm
        _ ≤ ∫ u, (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i)) +
            ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
              rate rewards C_star C_h s t
                (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
            ∂ContinuousLearningRows.timeControlLaw p := by
          simpa only [Pi.add_apply] using hmono
        _ = (∑ i ∈ P, ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i)) +
            ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelControlSection
              rate rewards C_star C_h s t z := hsumIntegral
    · intro hP
      let f : ContinuousLearningRows.TimeControl p → ℝ := fun u =>
        actualFixedReleaseSignedDeficit rate rewards C_star C_h s t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z u)
      have hnonpos : ∀ u, f u ≤ 0 := fun u => hzeroP u hP
      rw [actualFixedReleaseSignedDeficitControlSection]
      exact integral_nonpos_of_ae (Filter.Eventually.of_forall hnonpos)
  exact ⟨r, selected, hr, hselection, hobsS, hsectionBound.1, hsectionBound.2⟩

/-- At every supported actual later-installation date, the conditional signed
physical deficit is controlled by the actual pending chi sum and the fixed
sentinel conditional charge. Empty pending sets retain the unmasked signed
deficit and yield conditional nonpositivity. -/
public theorem actual_later_local_release_signed_condExp_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) :
    ∀ᵐ z ∂sourceInputLaw p, ∀ s : ℕ,
      ∀ b : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length, ∀ t : Fin p.T,
      s = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + b.val →
      ReferenceCollectionPhaseHistory.laterChosen
        (ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[b.val].input = true →
      (entry rate rewards C_star C_h s t z).map Prod.fst = some true →
      ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (selected : ReferenceActivePhysicalStep.Selection r.input),
        actualRecord rate rewards C_star C_h t z = some r ∧
        r.output.preparation.coordinator.selection = some selected ∧
        pending rate rewards C_star C_h s t z =
          ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r ∧
        (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
          sourcePrefixFiltration control0 (t.val + 1)] z ≤
          (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i)) +
          (sourceInputLaw p)[ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
            rate rewards C_star C_h s t |
            sourcePrefixFiltration control0 (t.val + 1)] z ∧
        (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
          sourcePrefixFiltration control0 (t.val + 1)] z ≤
          (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (selected.view.payload.assignment.assigned i)) +
          (if (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
            (1 : ℝ) else 0) *
            ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
              rate selected
              (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
                rate selected) *
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
                rate selected).val ∧
        (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r = ∅ →
          (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
            sourcePrefixFiltration control0 (t.val + 1)] z ≤ 0) := by
  filter_upwards
    [actualFixedReleaseSignedDeficit_condExp_all rate rewards C_star C_h control0,
      ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge_condExp_all
        rate rewards C_star C_h control0,
      ReferenceOriginalInstallationReleaseSentinelSection.actual_later_local_release_physical_sentinel_condExp_bound
        rate rewards C_star C_h control0] with z hzD hzSent hzPhysical
  intro s b t hs hb hg
  obtain ⟨r, selected, hr, hselection, hpendingObs, hsection, hzero⟩ :=
    actual_later_local_release_signed_section_bound
      rate rewards C_star C_h control0 z s b t hs hb hg
  obtain ⟨rSent, selectedSent, hrSent, hselectionSent, _hphysical, hsentBound⟩ :=
    hzPhysical s b t hs hb hg
  have hrEq : rSent = r := Option.some.inj (hrSent.symm.trans hr)
  subst rSent
  have hselectionEq : selectedSent = selected :=
    Option.some.inj (hselectionSent.symm.trans hselection)
  subst selectedSent
  have hD := hzD s t
  have hSent := hzSent s t
  have hfirst :
      (sourceInputLaw p)[actualFixedReleaseSignedDeficit rate rewards C_star C_h s t |
        sourcePrefixFiltration control0 (t.val + 1)] z ≤
        (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
        (sourceInputLaw p)[ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
          rate rewards C_star C_h s t |
          sourcePrefixFiltration control0 (t.val + 1)] z := by
    calc
      _ = actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z := hD
      _ ≤ (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
          ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelControlSection
            rate rewards C_star C_h s t z := hsection
      _ = _ := by rw [← hSent]
  refine ⟨r, selected, hr, hselection, hpendingObs, hfirst, ?_, ?_⟩
  · calc
      _ ≤ (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
          (sourceInputLaw p)[ReferenceOriginalInstallationReleaseSentinelSection.actualFixedReleaseSentinelCharge
            rate rewards C_star C_h s t |
            sourcePrefixFiltration control0 (t.val + 1)] z := hfirst
      _ ≤ (∑ i ∈ ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r,
          ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
            (selected.view.payload.assignment.assigned i)) +
          (if (ReferencePhysicalReleaseQuota.pendingSet selected.view.payload r).Nonempty then
            (1 : ℝ) else 0) *
          ReferencePostReplacementCollectionSentinelSectionLaw.selectedFastArmMass
              rate selected
              (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
                rate selected) *
            ReleaseRoundKernel.chi (wholeGridRewardRow rewards t)
              (ReferencePostReplacementCollectionSentinelSectionLaw.selectedAuxiliaryFastArm
                rate selected).val := by
        linarith [hsentBound]
  · intro hEmpty
    calc
      _ = actualFixedReleaseSignedDeficitControlSection rate rewards C_star C_h s t z := hD
      _ ≤ 0 := hzero hEmpty

end Bandits.Support.ReferenceOriginalInstallationReleaseSignedCharge

end
