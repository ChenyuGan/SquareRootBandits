/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveFastCollisionSection

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Reward-weighted fast collision on the existing inspected history

Sources: `sources/zip4/manuscript/05_binary_transport.tex:293-348` and
`sources/zip4/manuscript/06_interruptions.tex:452-492`.

All observations below concern the original physical execution and original
source law. The guard is the existing indexed first-live guarded event. No
coverage of all release rounds, stopped endpoint, or regret closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInspectedFastCollision

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}

private theorem measurable_optionElim {α β X : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace X]
    (f : α × X → β) (hf : Measurable f) (g : X → β) (hg : Measurable g)
    (v : X → Option α) (hv : Measurable v) :
    Measurable (fun x => match v x with | none => g x | some a => f (a, x)) := by
  have h := (hf.sumElim (hg.comp measurable_snd)).comp
    (MeasurableEquiv.sumProdDistrib α PUnit X).measurable_toFun
  have hpair := h.comp
    (((comap_measurable (Equiv.optionEquivSumPUnit α)).comp hv).prodMk measurable_id)
  convert hpair using 1
  funext x
  change (match v x with | none => g x | some a => f (a, x)) =
    Sum.elim f (g ∘ Prod.snd) ((Equiv.sumProdDistrib α PUnit X)
      ((Equiv.optionEquivSumPUnit α) (v x), x))
  cases v x <;> rfl

private theorem integrable_unit {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] (f : α → ℝ)
    (hf : Measurable f) (hb : ∀ x, ‖f x‖ ≤ 1) : Integrable f ν :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

local notation "Z" => ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
  rate rewards C_star C_h

/-- Lossless Borel code of the same optional actual record. -/
def actualRecordCode (t : Fin p.T) (z : SourceInput p) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
    ReferenceActiveHorizonMeasurability.roundRecordCode

theorem measurable_actualRecordCode (t : Fin p.T) :
    Measurable (actualRecordCode rate rewards C_star C_h t) := by
  have houtput := (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h rate.eta rewards).comp
      ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
  have hstart : Measurable (fun z : SourceInput p =>
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
    have h := (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
      ReferenceInitializationRun.elapsed p b.completed)).comp houtput
    convert h using 1
    funext z
    exact congrArg (fun x => ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed)
      (ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput
        z rewards C_star C_h rate).symm
  have hlookup (n : ℕ) : Measurable (fun records : List
      (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)) =>
      records[n]?) := by
    have hat := (measurable_pi_apply n).comp
      (measurable_snd.comp
        (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
          (α := ReferenceActiveHorizonMeasurability.RoundRecordCode
            (p := p) (rate := rate))))
    have hsome : Measurable (some :
        ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) →
          Option (ReferenceActiveHorizonMeasurability.RoundRecordCode
            (p := p) (rate := rate))) := by
      apply measurable_comap_iff.mpr
      exact measurable_inl
    have hconvert : Measurable (Sum.elim
        (fun _ : Unit => (none : Option
          (ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate))))
        some) := Measurable.sumElim measurable_const hsome
    have h := hconvert.comp hat
    convert h using 1
    funext records
    dsimp only [Function.comp_apply,
      ReferenceActiveHorizonMeasurability.listObservationCoordinates,
      ReferenceActiveHorizonMeasurability.listObservationAt]
    cases records[n]? <;> rfl
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h
  have hindex : Measurable (fun z : SourceInput p =>
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
    (measurable_of_countable (fun n : ℕ => t.val - n)).comp hstart
  have hlookupJoint := (measurable_from_prod_countable_right
    (f := fun v : ℕ × List (ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) => v.2[v.1]?) hlookup).comp
        (hindex.prodMk
          (ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
            (rate := rate) rewards C_star C_h))
  have hset : MeasurableSet {z : SourceInput p |
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val} :=
    hstart (MeasurableSpace.measurableSet_top : MeasurableSet {n : ℕ | n ≤ t.val})
  have h : Measurable (fun z : SourceInput p =>
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val
      then (codes z)[t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h]? else none) :=
    Measurable.ite hset hlookupJoint measurable_const
  convert h using 1
  funext z
  unfold actualRecordCode ReferenceSourcePrefixHistoryFiltration.actualRecord
  split_ifs <;> simp only [codes,
    ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
    List.getElem?_map, Option.map_none]

private theorem actualRecord_fields (t : Fin p.T) (z : SourceInput p)
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

/-- The literal charge read from a lossless record code and the whole reward row.
The absent payload and empty pending-set cases retain zero charge. -/
def codeFastCollisionCharge (t : Fin p.T)
    (code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate)) : ℝ :=
  match ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1 with
  | none => 0
  | some M =>
      if ReferenceActiveHorizonMeasurability.roundRecordCodeActions code
          (ActiveRoundActions.coordinator p.two_le_m) = M.assignment.auxiliary ∧
          (ReferencePhysicalReleaseQuota.pendingAtStart M t
            (ReferenceActivePhysicalStepMeasurability.decodeState code.2.1)).Nonempty then
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
          M.assignment.auxiliary
      else 0

theorem measurable_codeFastCollisionCharge (t : Fin p.T) :
    Measurable (codeFastCollisionCharge rate rewards t) := by
  let Code := ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)
  have haux : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × Code =>
      z.1.assignment.auxiliary) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp measurable_fst
  have haction : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × Code =>
      ReferenceActiveHorizonMeasurability.roundRecordCodeActions z.2
        (ActiveRoundActions.coordinator p.two_le_m)) := by
    dsimp only [Code, ReferenceActiveHorizonMeasurability.roundRecordCodeActions]
    fun_prop
  have hstate : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × Code =>
      ReferenceActivePhysicalStepMeasurability.decodeState z.2.2.1) :=
    (ReferenceReleaseStrictPastFactor.measurable_decodeState rate).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hpending : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × Code =>
      ReferencePhysicalReleaseQuota.pendingAtStart z.1 t
        (ReferenceActivePhysicalStepMeasurability.decodeState z.2.2.1)) :=
    ReferencePhysicalReleaseObservability.measurable_pendingAtStart.comp
      (measurable_fst.prodMk (measurable_const.prodMk hstate))
  have hnonempty : MeasurableSet {z : ReferenceActivePhysicalStep.Payload rate × Code |
      (ReferencePhysicalReleaseQuota.pendingAtStart z.1 t
        (ReferenceActivePhysicalStepMeasurability.decodeState z.2.2.1)).Nonempty} :=
    hpending (Set.to_countable {P : Finset (Fin (p.m - 1)) | P.Nonempty}).measurableSet
  have hrow : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate × Code =>
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
        z.1.assignment.auxiliary) := (measurable_of_countable _).comp haux
  unfold codeFastCollisionCharge
  have h := measurable_optionElim
    (fun z : ReferenceActivePhysicalStep.Payload rate × Code =>
      if ReferenceActiveHorizonMeasurability.roundRecordCodeActions z.2
          (ActiveRoundActions.coordinator p.two_le_m) = z.1.assignment.auxiliary ∧
          (ReferencePhysicalReleaseQuota.pendingAtStart z.1 t
            (ReferenceActivePhysicalStepMeasurability.decodeState z.2.2.1)).Nonempty then
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
          z.1.assignment.auxiliary else 0)
    (hrow.ite ((measurableSet_eq_fun haction haux).inter hnonempty) measurable_const)
    (fun _ => (0 : ℝ)) measurable_const _
    ((ReferenceReleaseStrictPastFactor.measurable_localStoredPayload rate).comp
      (measurable_fst.comp measurable_snd))
  convert h using 1
  funext code
  dsimp only [Function.comp_apply]
  cases ReferenceRetainedReleasePhaseObservation.localStoredPayload code.2.1
  · rfl
  · rfl

theorem sourceFastCollisionCharge_eq_code (t : Fin p.T) (z : SourceInput p) :
    Z t z = ((actualRecordCode rate rewards C_star C_h t z).map
      (codeFastCollisionCharge rate rewards t)).getD 0 := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge,
      actualRecordCode, hr]
  | some r =>
      obtain ⟨_, _, ht, hw⟩ := actualRecord_fields rate rewards C_star C_h t z r hr
      simp only [ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge,
        actualRecordCode, hr, Option.map_some, Option.getD_some,
        codeFastCollisionCharge, ReferenceActiveHorizonMeasurability.roundRecordCode,
        ReferenceRetainedReleasePhaseObservation.localStoredPayload_eq_decoded,
        ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
      rw [← ReferenceActiveHorizonMeasurability.roundRecordCode]
      rw [(ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.1]
      cases ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator <;>
        simp only [ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge,
          ReferencePhysicalReleaseQuota.pendingSet, ht, hw]

theorem sourceFastCollisionCharge_measurable (t : Fin p.T) : Measurable (Z t) := by
  have h := measurable_optionElim
    (fun v : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
      SourceInput p => codeFastCollisionCharge rate rewards t v.1)
    ((measurable_codeFastCollisionCharge rate rewards t).comp measurable_fst)
    (fun _ => (0 : ℝ)) measurable_const _
    (measurable_actualRecordCode rate rewards C_star C_h t)
  convert h using 1
  funext z
  rw [sourceFastCollisionCharge_eq_code]
  cases actualRecordCode rate rewards C_star C_h t z <;> rfl

theorem sourceFastCollisionCharge_bounds (t : Fin p.T) (z : SourceInput p) :
    0 ≤ Z t z ∧ Z t z ≤ 1 := by
  unfold ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
  split
  · exact ⟨le_rfl, zero_le_one⟩
  · split
    · exact ⟨le_rfl, zero_le_one⟩
    · unfold ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge
      split
      · exact (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow _ _).property _
      · exact ⟨le_rfl, zero_le_one⟩

theorem sourceFastCollisionCharge_integrable (t : Fin p.T) :
    Integrable (Z t) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  exact integrable_unit _ (sourceFastCollisionCharge_measurable rate rewards C_star C_h t)
    (fun z => by rw [Real.norm_eq_abs,
      abs_of_nonneg (sourceFastCollisionCharge_bounds rate rewards C_star C_h t z).1]
                 exact (sourceFastCollisionCharge_bounds rate rewards C_star C_h t z).2)

private theorem record_action_congr
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : r.input.state = r'.input.state)
    (hselected : r.input.selected = r'.input.selected)
    (htime : r.input.time = r'.input.time)
    (hrewards : r.input.rewards = r'.input.rewards)
    (hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time)
    (hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
          (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop) :
    r.actions (ActiveRoundActions.coordinator p.two_le_m) =
      r'.actions (ActiveRoundActions.coordinator p.two_le_m) := by
  rcases r with ⟨x, output, hout⟩
  rcases r' with ⟨y, output', hout'⟩
  subst output
  subst output'
  rcases x with ⟨state, rows, selected, time, active, rewards⟩
  rcases y with ⟨state', rows', selected', time', active', rewards'⟩
  dsimp only at hstate hselected htime hrewards hcurrent hpast
  subst state'
  subst selected'
  subst time'
  subst rewards'
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    state rows rows' selected time active rewards rewards hcurrent hpast rfl
  have harm := congrArg (fun e : ReferenceActivePhysicalHorizon.RoundEvidence
    (p := p) (rate := rate) =>
      (e.ownEntries (ActiveRoundActions.coordinator p.two_le_m)).1) hevidence
  change (ReferenceActivePhysicalStep.prepare
    ⟨state, rows, selected, time, active, rewards⟩).arms.actions
      (ActiveRoundActions.coordinator p.two_le_m) =
    (ReferenceActivePhysicalStep.prepare
      ⟨state, rows', selected, time, active', rewards⟩).arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) at harm
  simpa only [ReferenceActivePhysicalHorizon.RoundRecord.actions,
    ReferenceActivePhysicalStep.step] using harm

private theorem record_charge_congr
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : r.input.state = r'.input.state)
    (hselected : r.input.selected = r'.input.selected)
    (htime : r.input.time = r'.input.time)
    (hrewards : r.input.rewards = r'.input.rewards)
    (hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time)
    (hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
        (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop)
    (M : ReferenceActivePhysicalStep.Payload rate) :
    ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge M r =
      ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge M r' := by
  have harm := record_action_congr rate r r' hstate hselected htime hrewards hcurrent hpast
  have hpending := ReferencePhysicalReleaseQuota.pendingSet_eq_of_state_time_eq
    M r r' hstate htime
  unfold ReferenceFirstLiveFastCollisionSection.recordFastCollisionCharge
  by_cases h : r.actions (ActiveRoundActions.coordinator p.two_le_m) =
      M.assignment.auxiliary ∧ (ReferencePhysicalReleaseQuota.pendingSet M r).Nonempty
  · have h' : r'.actions (ActiveRoundActions.coordinator p.two_le_m) =
        M.assignment.auxiliary ∧ (ReferencePhysicalReleaseQuota.pendingSet M r').Nonempty :=
      ⟨harm ▸ h.1, hpending ▸ h.2⟩
    rw [ite_eq_left h, ite_eq_left h', htime, hrewards]
  · have h' : ¬ (r'.actions (ActiveRoundActions.coordinator p.two_le_m) =
        M.assignment.auxiliary ∧ (ReferencePhysicalReleaseQuota.pendingSet M r').Nonempty) :=
      fun h' => h ⟨harm.symm ▸ h'.1, hpending.symm ▸ h'.2⟩
    rw [ite_eq_right h, ite_eq_right h']

/-- The actual charge only reads the original source through this round.
This follows from incoming-state locality and the physical STEP comparison. -/
theorem sourceFastCollisionCharge_prefix (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    Z t z = Z t (ReferenceSourcePrefixHistoryFiltration.sourcePrefix
      control0 (t.val + 1) z) := by
  have hin : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
    rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t z,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z),
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val (t.val + 1) (by omega)]
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hin
  unfold ReferenceFirstLiveFastCollisionSection.sourceFastCollisionCharge
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z <;>
    cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) <;>
    simp only [hr, hr', Option.map_none, Option.map_some] at hin
  · rfl
  · cases hin
  · cases hin
  · rename_i r r'
    have hstate : r.input.state = r'.input.state := by
      have h := congrArg ReferenceActivePhysicalStepMeasurability.decodeState
        (Option.some.inj hin)
      simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using h
    obtain ⟨hrows, hselected, htime, hrewards⟩ :=
      actualRecord_fields rate rewards C_star C_h t z r hr
    obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
      actualRecord_fields rate rewards C_star C_h t _ r' hr'
    have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
        hselected, hselected', htime, htime',
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
        Nat.lt_succ_self, ite_true]
    have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
        (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
          (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
      intro v hv
      rw [htime] at hv
      simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
        hselected, hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
        ite_eq_left (hv.trans (Nat.lt_succ_self t.val))]
    simp only [hstate]
    cases ReferenceAssignmentPayloadPersistence.storedPayload r'.input.state.coordinator with
    | none => rfl
    | some M =>
        exact record_charge_congr rate r r' hstate
          (by rw [hselected, hselected',
            ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected])
          (htime.trans htime'.symm) (hrewards.trans hrewards'.symm) hcurrent hpast M

/-- Joint Borel measurability of the actual reward-weighted replacement. -/
theorem sourceFastCollisionCharge_joint_measurable (t : Fin p.T) :
    Measurable (fun v : SourceInput p × TimeControl p => Z t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2)) :=
  (sourceFastCollisionCharge_measurable rate rewards C_star C_h t).comp
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)

/-- Restoration uses the actual selected current control and the accepted
source prefix; every other private coordinate remains original. -/
theorem sourceFastCollisionCharge_restore (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    Z t z = Z t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z)
      (ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
  unfold ReferenceSourceCurrentControlFreshness.u_t
  rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    ← ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore]
  exact sourceFastCollisionCharge_prefix rate rewards C_star C_h control0 t z

section WeightedFreshness

open ReferenceSourceCurrentControlFreshness

/-- Weighted extension of current-control freshness, proved from the joint
product law and bounded Fubini. Its input is an arbitrary bounded Borel real
function, not an assumed conditional law. -/
theorem source_control_weighted_condExp {p : ConstructorDimensions.Parameters}
    (control0 : TimeControl p) (t : Fin p.T)
    (f : SourceInput p × TimeControl p → ℝ) (hf : Measurable f)
    (hb : ∀ v, ‖f v‖ ≤ 1) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => f (c_t p control0 t z, u_t p t z)) | m_t p control0 t] =ᵐ[
        BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun z => ∫ u, f (c_t p control0 t z, u)
        ∂ContinuousLearningRows.timeControlLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let ν := ContinuousLearningRows.timeControlLaw p
  let c := c_t p control0 t
  let u := u_t p t
  let pairMap := fun z => (c z, u z)
  let g := fun x : SourceInput p => ∫ v, f (x, v) ∂ν
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  have hc : Measurable c := measurable_c_t control0 t
  have hu : Measurable u := measurable_u_t t
  have hle : m_t p control0 t ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    hc.comap_le
  have hg : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    calc
      ‖g x‖ ≤ ∫ v, ‖f (x, v)‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : TimeControl p, (1 : ℝ) ∂ν :=
        integral_mono (integrable_unit _ (hf.comp measurable_prodMk_left) (fun v => hb (x, v))).norm
          (integrable_const _) (fun v => hb (x, v))
      _ = 1 := by simp [ν]
  have hfi : Integrable (fun z => f (pairMap z)) μ :=
    integrable_unit _ (hf.comp (hc.prodMk hu)) (fun z => hb (pairMap z))
  have hgi : Integrable (fun z => g (c z)) μ :=
    integrable_unit _ (hg.comp hc) (fun z => hgb (c z))
  have hgm : Measurable[m_t p control0 t] (fun z => g (c z)) :=
    hg.comp (comap_measurable c)
  have hset : ∀ A : Set (SourceInput p), MeasurableSet[m_t p control0 t] A →
      μ A < ⊤ → ∫ z in A, g (c z) ∂μ = ∫ z in A, f (pairMap z) ∂μ := by
    intro A hA _
    rcases (MeasurableSpace.measurableSet_comap
      (m := (inferInstance : MeasurableSpace (SourceInput p))) (f := c)).mp hA with
      ⟨V, hV, hVA⟩
    rw [← hVA]
    let H := fun z : SourceInput p × TimeControl p => V.indicator (fun _ => (1 : ℝ)) z.1 * f z
    let G := fun x : SourceInput p => V.indicator (fun _ => (1 : ℝ)) x * g x
    have hH : Measurable H := ((measurable_const.indicator hV).comp measurable_fst).mul hf
    have hHb : ∀ z, ‖H z‖ ≤ 1 := by
      intro z
      by_cases hz : z.1 ∈ V <;> simp only [H, Set.indicator, hz, reduceIte, one_mul, zero_mul]
      · exact hb z
      · norm_num
    have hHi : Integrable H ((μ.map c).prod ν) := integrable_unit _ hH hHb
    have hjoint := source_joint_prefix_control control0 t
    have hG : Measurable G := (measurable_const.indicator hV).mul hg
    have hGb : ∀ x, ‖G x‖ ≤ 1 := by
      intro x
      by_cases hx : x ∈ V <;> simp only [G, Set.indicator, hx, reduceIte, one_mul, zero_mul]
      · exact hgb x
      · norm_num
    have hGi : Integrable G (μ.map c) := integrable_unit _ hG hGb
    have hHmap : AEStronglyMeasurable H (μ.map pairMap) := by
      rw [hjoint]
      exact hHi.aestronglyMeasurable
    have htest : (c ⁻¹' V).indicator (fun z => f (pairMap z)) =
        fun z => H (pairMap z) := by
      funext z
      by_cases hz : c z ∈ V <;> simp [H, pairMap, Set.indicator, hz]
    have hcand : (c ⁻¹' V).indicator (fun z => g (c z)) =
        fun z => G (c z) := by
      funext z
      by_cases hz : c z ∈ V <;> simp [G, Set.indicator, hz]
    symm
    calc
      _ = ∫ z, H (pairMap z) ∂μ := by rw [← htest, integral_indicator (hc hV)]
      _ = ∫ z, H z ∂μ.map pairMap :=
        (integral_map (hc.prodMk hu).aemeasurable hHmap).symm
      _ = ∫ z, H z ∂((μ.map c).prod ν) := by rw [hjoint]
      _ = ∫ x, ∫ v, H (x, v) ∂ν ∂μ.map c := integral_prod H hHi
      _ = ∫ x, G x ∂μ.map c := by
        congr 1
        funext x
        dsimp only [H, G, g]
        exact integral_const_mul _ _
      _ = ∫ z, G (c z) ∂μ := integral_map hc.aemeasurable hGi.aestronglyMeasurable
      _ = _ := by rw [← hcand, integral_indicator (hc hV)]
  exact (ae_eq_condExp_of_forall_setIntegral_eq hle hfi
    (fun _ _ _ => hgi.integrableOn) hset hgm.stronglyMeasurable.aestronglyMeasurable).symm

end WeightedFreshness

variable (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
  (q : Fin (M p)) (s : ℕ) (hs : s ≤ t.val) (b : ℕ)

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "Kfield" => ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
  rate rewards C_star C_h t.val (le_of_lt t.isLt)
local notation "mPrefix" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
local notation "G" => ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
  rate rewards C_star C_h control0 i t q s hs b
local notation "Iguard" =>
  ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator
    rate rewards C_star C_h control0 i t q s hs b
local notation "omega" =>
  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
    rate rewards C_star C_h control0 i t q s hs b
local notation "c" => ReferenceSourceCurrentControlFreshness.c_t p control0 t
local notation "u" => ReferenceSourceCurrentControlFreshness.u_t p t

private theorem guard_measurable_prefix : Measurable[mPrefix] Iguard :=
  measurable_const.indicator
    (ReferenceFirstLiveGuardedConditionalService.measurableSet_firstLiveGuardedEvent
      rate rewards C_star C_h control0 i t q s hs b)

private theorem guard_measurable_ambient : Measurable Iguard :=
  (guard_measurable_prefix rate rewards C_star C_h control0 i t q s hs b).mono
    ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (t.val + 1))
    le_rfl

private theorem guard_prefix_factor (z : SourceInput p) : Iguard (c z) = Iguard z := by
  have hm := guard_measurable_prefix rate rewards C_star C_h control0 i t q s hs b
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hm
  exact hm.factorsThrough (by
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val t.val le_rfl])

/-- Replacing the current control preserves exactly the existing indexed
guard, since its entire definition is adapted to the strict source prefix. -/
theorem firstLiveGuardedEvent_replaceSourceControl (z : SourceInput p) (v : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v ∈ G ↔ z ∈ G := by
  have hG := ReferenceFirstLiveGuardedConditionalService.measurableSet_firstLiveGuardedEvent
    rate rewards C_star C_h control0 i t q s hs b
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hG
  rcases (MeasurableSpace.measurableSet_comap.mp hG) with ⟨V, _, hV⟩
  rw [← hV]
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v) ∈ V ↔
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z ∈ V
  rw [ReferenceFirstLiveActualFlagSections.sourcePrefix_replace_current]

theorem guardedFastCollisionCharge_measurable : Measurable (fun z => Iguard z * Z t z) :=
  (guard_measurable_ambient rate rewards C_star C_h control0 i t q s hs b).mul
    (sourceFastCollisionCharge_measurable rate rewards C_star C_h t)

theorem guardedFastCollisionCharge_bounds (z : SourceInput p) :
    0 ≤ Iguard z * Z t z ∧ Iguard z * Z t z ≤ 1 := by
  by_cases hz : z ∈ G
  · simpa only [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
      Set.indicator_of_mem hz, one_mul] using
        sourceFastCollisionCharge_bounds rate rewards C_star C_h t z
  · simp only [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
      Set.indicator_of_notMem hz, zero_mul, le_rfl, zero_le_one, and_self]

theorem guardedFastCollisionCharge_integrable : Integrable (fun z => Iguard z * Z t z) μ := by
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  apply integrable_unit _
    (guardedFastCollisionCharge_measurable rate rewards C_star C_h control0 i t q s hs b)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (guardedFastCollisionCharge_bounds rate rewards C_star C_h control0 i t q s hs b z).1]
  exact (guardedFastCollisionCharge_bounds rate rewards C_star C_h control0 i t q s hs b z).2

/-- Joint measurability also holds with both actual factors evaluated on the
same replaced original source. -/
theorem guardedFastCollisionCharge_joint_measurable :
    Measurable (fun v : SourceInput p × TimeControl p =>
      let z := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2
      Iguard z * Z t z) :=
  (guardedFastCollisionCharge_measurable rate rewards C_star C_h control0 i t q s hs b).comp
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)

/-- The guarded charge restores at the original selected current control. -/
theorem guardedFastCollisionCharge_restore (z : SourceInput p) :
    Iguard z * Z t z =
      let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t (c z) (u z)
      Iguard z' * Z t z' := by
  have hI : Iguard
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t (c z) (u z)) =
        Iguard (c z) := by
    have hmem := firstLiveGuardedEvent_replaceSourceControl
      rate rewards C_star C_h control0 i t q s hs b (c z) (u z)
    by_cases hz : c z ∈ G
    · simp only [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        Set.indicator_of_mem hz, Set.indicator_of_mem (hmem.mpr hz)]
    · simp only [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz (hmem.mp h))]
  dsimp only
  rw [hI, guard_prefix_factor rate rewards C_star C_h control0 i t q s hs b,
    ← sourceFastCollisionCharge_restore rate rewards C_star C_h control0 t]

private theorem omega_prefix_factor (z : SourceInput p) : omega (c z) = omega z := by
  have hm :=
    (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_measurable_in_inspectedField
      rate rewards C_star C_h control0 i t q s hs b).mono
        (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
          rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)) le_rfl
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at hm
  exact hm.factorsThrough (by
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val t.val le_rfl])

/-- The actual whole-control charge integral on the guarded branch is bounded
by the same inspected coefficient. Nonemptiness is supplied by the actual
baseline's membership of `i`, not by a new pending-set assumption. -/
theorem guardedFastCollisionCharge_section_bound (z : SourceInput p) :
    (∫ v, Iguard z * Z t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z v)
        ∂ContinuousLearningRows.timeControlLaw p) ≤ omega z := by
  by_cases hz : z ∈ G
  · have hsection := ReferenceFirstLiveFastCollisionSection.actual_source_fast_collision_section
      rate rewards C_star C_h control0 i t q s hs z hz.1
    let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
      rate rewards C_star C_h control0 i t q s hs z hz.1
    let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
      rate rewards C_star C_h control0 i t q s hs z hz.1
    have hspec := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_spec
      rate rewards C_star C_h q t s hs control0 i x hx
    have hp := Finset.nonempty_iff_ne_empty.mpr
      (Finset.ne_empty_of_mem hspec.2.2)
    dsimp only [x, hx] at hp
    have homega : omega z =
        ReferenceFirstLiveFastCollisionSection.qAuxiliary
          (ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
            rate rewards C_star C_h q t s hs control0 i x hx)
          (ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
            rate rewards C_star C_h q t s hs control0 i x hx) *
        ReleaseRoundKernel.chi (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
          (ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
            rate rewards C_star C_h q t s hs control0 i x hx).view.payload.assignment.auxiliary := by
      have hz' : z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
          rate rewards C_star C_h control0 i t q s hs b := hz
      simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi,
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
        dite_eq_left hz']
      rfl
    rw [homega]
    simpa only [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
      Set.indicator_of_mem hz, one_mul, ite_eq_left hp, mul_one] using hsection.2.2
  · have hzero : omega z = 0 := by
      have hz' : z ∉ ReferenceFirstLiveInspectedCoefficients.guardedEvent
          rate rewards C_star C_h control0 i t q s hs b := hz
      simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi,
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
        dite_eq_right hz',
        ReferenceFirstLiveInspectedCoefficients.zeroValues]
    simp only [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
      Set.indicator_of_notMem hz, zero_mul, integral_zero, hzero, le_rfl]

/-- The weighted conditional law at the strict source-prefix field. -/
theorem guardedFastCollisionCharge_prefix_condExp_le :
    μ[fun z => Iguard z * Z t z | mPrefix] ≤ᵐ[μ] omega := by
  let f := fun v : SourceInput p × TimeControl p => Iguard v.1 * Z t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t v.1 v.2)
  have hf : Measurable f :=
    ((guard_measurable_ambient rate rewards C_star C_h control0 i t q s hs b).comp
      measurable_fst).mul (sourceFastCollisionCharge_joint_measurable rate rewards C_star C_h t)
  have hb : ∀ v, ‖f v‖ ≤ 1 := by
    intro v
    by_cases hz : v.1 ∈ G
    · simpa only [f, ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        Set.indicator_of_mem hz, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (sourceFastCollisionCharge_bounds rate rewards C_star C_h t _).1] using
          (sourceFastCollisionCharge_bounds rate rewards C_star C_h t _).2
    · simp only [f, ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        Set.indicator_of_notMem hz, zero_mul, norm_zero, zero_le_one]
  have hmean := source_control_weighted_condExp control0 t f hf hb
  have hrestore : (fun z => f (c z, u z)) = (fun z => Iguard z * Z t z) := by
    funext z
    dsimp only [f]
    rw [guard_prefix_factor rate rewards C_star C_h control0 i t q s hs b,
      ← sourceFastCollisionCharge_restore rate rewards C_star C_h control0 t]
  rw [hrestore, ← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t
    control0 t] at hmean
  filter_upwards [hmean] with z hz
  rw [hz]
  exact (guardedFastCollisionCharge_section_bound rate rewards C_star C_h control0 i t q s hs b
    (c z)).trans_eq (omega_prefix_factor rate rewards C_star C_h control0 i t q s hs b z)

/-- Primary export: the reward-weighted actual charge is bounded conditionally
on the existing inspected history, with its genuinely adapted coefficient. -/
theorem firstLiveInspected_fastCollision_condExp_le :
    μ[fun z => Iguard z * Z t z | Kfield] ≤ᵐ[μ] omega := by
  have hY := guardedFastCollisionCharge_integrable
    rate rewards C_star C_h control0 i t q s hs b
  have hmle := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  have htower := ReferenceSourceOwnHistoryContainment.inspectedHistory_condExp_tower
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt) _ hY
  have hmono := condExp_mono (m := Kfield) (integrable_condExp :
      Integrable (μ[fun z => Iguard z * Z t z | mPrefix]) μ)
    (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_integrable
      rate rewards C_star C_h control0 i t q s hs b)
    (guardedFastCollisionCharge_prefix_condExp_le
      rate rewards C_star C_h control0 i t q s hs b)
  have homega := condExp_of_stronglyMeasurable hmle
    (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_stronglyMeasurable_in_inspectedField
      rate rewards C_star C_h control0 i t q s hs b)
    (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_integrable
      rate rewards C_star C_h control0 i t q s hs b)
  filter_upwards [htower, hmono] with z ht hm
  rw [homega] at hm
  exact ht ▸ hm

/-- Equivalent testing inequality for every event measurable in the same
inspected history. No event probability is divided out. -/
theorem firstLiveInspected_fastCollision_setIntegral_le
    (A : Set (SourceInput p)) (hA : MeasurableSet[Kfield] A) :
    (∫ z in A, Iguard z * Z t z ∂μ) ≤ ∫ z in A, omega z ∂μ := by
  have hmle := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  rw [← setIntegral_condExp hmle
    (guardedFastCollisionCharge_integrable rate rewards C_star C_h control0 i t q s hs b) hA]
  exact integral_mono_ae integrable_condExp.integrableOn
    (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_integrable
      rate rewards C_star C_h control0 i t q s hs b).integrableOn
    (ae_restrict_of_ae (firstLiveInspected_fastCollision_condExp_le
      rate rewards C_star C_h control0 i t q s hs b))

/-- The testing formulation is equivalent to the conditional inequality on
this exact smaller field. The reverse implication tests the trimmed measure. -/
theorem firstLiveInspected_fastCollision_condExp_le_iff_setIntegral :
    (μ[fun z => Iguard z * Z t z | Kfield] ≤ᵐ[μ] omega) ↔
      ∀ A : Set (SourceInput p), MeasurableSet[Kfield] A →
        (∫ z in A, Iguard z * Z t z ∂μ) ≤ ∫ z in A, omega z ∂μ := by
  have hmle := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  have hY := guardedFastCollisionCharge_integrable
    rate rewards C_star C_h control0 i t q s hs b
  have homega :=
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_integrable
      rate rewards C_star C_h control0 i t q s hs b
  have hce : StronglyMeasurable[Kfield] (μ[fun z => Iguard z * Z t z | Kfield]) :=
    stronglyMeasurable_condExp
  have hom : StronglyMeasurable[Kfield] omega :=
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi_stronglyMeasurable_in_inspectedField
      rate rewards C_star C_h control0 i t q s hs b
  constructor
  · intro h A hA
    rw [← setIntegral_condExp hmle hY hA]
    exact integral_mono_ae integrable_condExp.integrableOn homega.integrableOn
      (ae_restrict_of_ae h)
  · intro h
    apply ae_le_of_ae_le_trim (hm := hmle)
    apply ae_le_of_forall_setIntegral_le
      (Integrable.trim hmle integrable_condExp hce) (Integrable.trim hmle homega hom)
    intro A hA _
    rw [← setIntegral_trim hmle hce hA, ← setIntegral_trim hmle hom hA,
      setIntegral_condExp hmle hY hA]
    exact h A hA

/-- On almost every point of the SAME guard, the unguarded actual charge has
the inspected conditional bound, by measurable-guard pullout. -/
theorem firstLiveInspected_fastCollision_condExp_on_guard :
    ∀ᵐ z ∂μ, z ∈ G → μ[Z t | Kfield] z ≤ omega z := by
  have hmle := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure μ := BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  have hguard := ReferenceFirstLiveInspectedGuardReadout.measurableSet_inspected_guard
    rate rewards C_star C_h control0 i t q s hs b
  have heq : (fun z => Iguard z * Z t z) = Set.indicator G (Z t) := by
    funext z
    by_cases hz : z ∈ G <;>
      simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator, hz]
  have hpull : μ[fun z => Iguard z * Z t z | Kfield] =ᵐ[μ]
      Set.indicator G (μ[Z t | Kfield]) := by
    rw [heq]
    exact condExp_indicator (sourceFastCollisionCharge_integrable rate rewards C_star C_h t) hguard
  filter_upwards [firstLiveInspected_fastCollision_condExp_le
    rate rewards C_star C_h control0 i t q s hs b, hpull] with z hbound hlink
  intro hz
  rw [hlink, Set.indicator_of_mem hz] at hbound
  exact hbound

end Bandits.Support.ReferenceFirstLiveInspectedFastCollision

end
