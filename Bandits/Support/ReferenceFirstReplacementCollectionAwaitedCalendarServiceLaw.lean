/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionAwaitedTaskSupport
public import Bandits.Support.ReferenceFirstReplacementCollectionUnmaskedFreshPositiveService

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Original-source service law for the first replacement awaited collection

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-55,180-240,354-431`,
`06_interruptions.tex:110-177,246-296,425-437,459-487`, and
`appendix_a_local_protocol.tex:8-85,92-108,141-157`.

The support and binary service are the accepted new awaited observers. The
stage below uses that support and the actual unmasked physical choice.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFirstReplacementCollectionPendingFoundation
open ReferenceFirstReplacementCollectionAwaitedTaskSupport
open ReferenceFirstReplacementCollectionOldDownCallDates (actualOldAt)
open ReferenceFirstReplacementCollectionStoppedPureUpQuota (replyFormedAt)
open ReferenceFirstReplacementCollectionPredictableStages
  (Down TaskStage choiceStage choiceStage_old_iff choiceStage_formed_iff
    wordOnset wordOnset_measurable preRoundStart preRoundStart_measurable
    preRoundStart_choiceStage startStage)
open ReferenceFirstCollectionDownConditionalService
  (actualFirstCollectionDownReadout actualFirstCollectionDownFreshSection)
open ReferenceFirstCollectionUpConditionalService
  (actualFirstCollectionUpReadout actualFirstCollectionUpFreshSection positiveRewardCount)
open scoped Classical

namespace Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarServiceLaw

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

variable (rate) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)

/-- The accepted binary sum is exactly the real waiting observation at every date. -/
theorem observation_eq_service (i : Fin (p.m - 1)) (n : ℕ) (z : Source (p := p)) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n z =
      (service rate rewards C_star C_h control0 i n z : ℝ) := by
  rw [service_eq_indicator]
  unfold PhaseServiceWaiting.observation
  split <;> simp_all

private instance startCodeDiscreteMeasurableSpace :
    DiscreteMeasurableSpace (FollowerLifecycleMeasurability.StartRoundResultCode p rate) :=
  ⟨fun _ => trivial⟩

private instance startSumMeasurableSingletonClass :
    MeasurableSingletonClass (Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate) where
  measurableSet_singleton q := by
    rw [measurableSet_sum_iff]
    cases q <;> constructor <;> simp

/-- The actual optional stage, supported by the actual masked pending set.
Neither a missing payload nor a missing physical record is reconstructed. -/
def taskStage (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Option TaskStage :=
  if i ∈ Pnew rate rewards C_star C_h control0 n z then
    if hn : n < p.T then
      (ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h n z).bind fun pair =>
        (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h ⟨n, hn⟩ z).map
          (fun r => choiceStage r pair.1 i)
    else none
  else none

def OLD (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Prop :=
  taskStage rate rewards C_star C_h control0 n i z = some .old

def FORMED (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) : Prop :=
  taskStage rate rewards C_star C_h control0 n i z = some .formed

/-- Disjointness requires no trajectory, stage-domain or service premise. -/
theorem OLD_FORMED_disjoint (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    ¬ (OLD rate rewards C_star C_h control0 n i z ∧
      FORMED rate rewards C_star C_h control0 n i z) := by
  rintro ⟨hOld, hFormed⟩
  have h : (some TaskStage.old : Option TaskStage) = some .formed := hOld.symm.trans hFormed
  cases h

/-- Exact pointwise readout on a present actual record and its retained
payload. These are local lookup equations, not supplied phase or stage laws. -/
theorem taskStage_at_record (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (r : Record (rate := rate)) (payload : Payload (rate := rate)) (u : ℕ)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hp : ReferenceFirstReplacementCollectionPendingFoundation.payloadOnset rate rewards C_star C_h t.val z = some (payload, u)) :
    taskStage rate rewards C_star C_h control0 t.val i z =
      if i ∈ Pnew rate rewards C_star C_h control0 t.val z
      then some (choiceStage r payload i) else none := by
  simp only [taskStage, dite_eq_left t.isLt, hp, hr, Option.bind_some, Option.map_some]


/-- Unsupported labels have no stage, including nonordinary choices. -/
theorem taskStage_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ Pnew rate rewards C_star C_h control0 n z) :
    taskStage rate rewards C_star C_h control0 n i z = none := by
  simp only [taskStage, ite_eq_right hi]

/-- The observer is absent from the horizon onward. -/
theorem taskStage_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) : taskStage rate rewards C_star C_h control0 n i z = none := by
  simp only [taskStage, dite_eq_right (Nat.not_lt.mpr hn), ite_self]

/-- Exact row-free expression of the literal stage observer. The incoming
option preserves missing records rather than inventing a local configuration. -/
theorem taskStage_eq_preRound (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    taskStage rate rewards C_star C_h control0 t.val i z =
      if i ∈ Pnew rate rewards C_star C_h control0 t.val z then
        (wordOnset rate rewards C_star C_h t.val i z).bind fun q =>
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
            (fun _ => startStage rate q.1 (preRoundStart rate rewards C_star C_h t i z))
      else none := by
  unfold taskStage wordOnset
  rw [dite_eq_left t.isLt]
  split_ifs
  · cases hp : payloadOnset rate rewards C_star C_h t.val z with
    | none => rfl
    | some pair =>
      rcases pair with ⟨payload, u⟩
      cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
      | none => simp only [ReferenceSourcePrefixHistoryFiltration.incoming, hr,
          Option.map_none, Option.map_some, Option.bind_some]
      | some r =>
        simp only [Option.map_some, Option.bind_some, ReferenceSourcePrefixHistoryFiltration.incoming,
          hr, Option.map_some]
        exact congrArg some (preRoundStart_choiceStage rate rewards C_star C_h t i z r payload hr).symm
  · rfl

/-- Strict-past measurability of the entire actual optional stage, on every
original source with whole rewards and unrestricted constants. -/
theorem taskStage_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      (taskStage rate rewards C_star C_h control0 n i) := by
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let : MeasurableSpace (Source (p := p)) := F (n + 1)
  by_cases hn : n < p.T
  · let t : Fin p.T := ⟨n, hn⟩
    have hw := wordOnset_measurable rate rewards C_star C_h control0 n i
    have hs := preRoundStart_measurable rate rewards C_star C_h control0 t i
    have hin := ReferenceSourcePrefixHistoryFiltration.incoming_measurable
      rate rewards C_star C_h control0 t
    have hread : Measurable (fun q :
        Option (Down (rate := rate) × ℕ) ×
          ((Unit ⊕ FollowerLifecycleMeasurability.StartRoundResultCode p rate) ×
            Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) =>
        q.1.bind fun w => q.2.2.map (fun _ => startStage rate w.1 q.2.1)) := by
      apply measurable_from_prod_countable_right
      intro word
      apply measurable_from_prod_countable_right
      intro start
      cases word with
      | none => exact measurable_const
      | some w =>
          convert ReferenceCollectionOutcomeMeasurability.measurable_optionalElim
            (none : Option TaskStage)
            (fun _ : ReferenceActivePhysicalStepMeasurability.StateCode p rate =>
              some (startStage rate w.1 start)) measurable_const using 1
          funext code
          cases code <;> rfl
    have h : Measurable (fun z : Source (p := p) =>
        if i ∈ Pnew rate rewards C_star C_h control0 n z then
          (wordOnset rate rewards C_star C_h n i z).bind fun w =>
            (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z).map
              (fun _ => startStage rate w.1 (preRoundStart rate rewards C_star C_h t i z))
        else none) :=
      Measurable.ite (Pnew_mem_measurable rate rewards C_star C_h control0 n i)
        (hread.comp (hw.prodMk (hs.prodMk hin))) measurable_const
    convert h using 1
    funext z
    exact taskStage_eq_preRound rate rewards C_star C_h control0 t i z
  · convert (measurable_const : Measurable (fun _ : Source (p := p) =>
      (none : Option TaskStage))) using 1
    funext z
    exact taskStage_of_horizon_le rate rewards C_star C_h control0 n i z (Nat.le_of_not_lt hn)

/-- OLD is an event in the pre-round original-source field. -/
theorem OLD_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      {z : Source (p := p) | OLD rate rewards C_star C_h control0 n i z} :=
  (taskStage_measurable rate rewards C_star C_h control0 n i) (measurableSet_singleton _)

/-- FORMED uses exactly the same predictable observer as OLD. -/
theorem FORMED_measurable (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)]
      {z : Source (p := p) | FORMED rate rewards C_star C_h control0 n i z} :=
  (taskStage_measurable rate rewards C_star C_h control0 n i) (measurableSet_singleton _)

theorem OLD_borel (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet {z : Source (p := p) | OLD rate rewards C_star C_h control0 n i z} :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (n + 1)
    _ (OLD_measurable rate rewards C_star C_h control0 n i)

theorem FORMED_borel (n : ℕ) (i : Fin (p.m - 1)) :
    MeasurableSet {z : Source (p := p) | FORMED rate rewards C_star C_h control0 n i z} :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (n + 1)
    _ (FORMED_measurable rate rewards C_star C_h control0 n i)

/-- Pointwise prefix factorization, not just an almost-everywhere version. -/
theorem taskStage_factor (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    taskStage rate rewards C_star C_h control0 n i z =
      taskStage rate rewards C_star C_h control0 n i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have h := (taskStage_measurable rate rewards C_star C_h control0 n i)
    (measurableSet_singleton (taskStage rate rewards C_star C_h control0 n i z))
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at h
  obtain ⟨B, _hB, he⟩ := h
  have hmem : z ∈ {x | taskStage rate rewards C_star C_h control0 n i x =
      taskStage rate rewards C_star C_h control0 n i z} := rfl
  change z ∈ taskStage rate rewards C_star C_h control0 n i ⁻¹'
    {taskStage rate rewards C_star C_h control0 n i z} at hmem
  rw [← he] at hmem
  have hmem' : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      {x | taskStage rate rewards C_star C_h control0 n i x =
        taskStage rate rewards C_star C_h control0 n i z} := by
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      taskStage rate rewards C_star C_h control0 n i ⁻¹'
        {taskStage rate rewards C_star C_h control0 n i z}
    rw [← he]
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ∈ B
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n n le_rfl]
    exact hmem
  exact hmem'.symm

/-- The finite DOWN/onset projection itself factors through the strict past. -/
theorem wordOnset_factor (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p)) :
    wordOnset rate rewards C_star C_h n i z =
      wordOnset rate rewards C_star C_h n i
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) := by
  have h := (wordOnset_measurable rate rewards C_star C_h control0 n i)
    (measurableSet_singleton (wordOnset rate rewards C_star C_h n i z))
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ] at h
  obtain ⟨B, _hB, he⟩ := h
  have hmem : z ∈ wordOnset rate rewards C_star C_h n i ⁻¹'
      {wordOnset rate rewards C_star C_h n i z} := rfl
  rw [← he] at hmem
  have hmem' : ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z ∈
      wordOnset rate rewards C_star C_h n i ⁻¹'
        {wordOnset rate rewards C_star C_h n i z} := by
    rw [← he]
    change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n z) ∈ B
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 n n le_rfl]
    exact hmem
  exact hmem'.symm

theorem not_OLD_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ Pnew rate rewards C_star C_h control0 n z) :
    ¬ OLD rate rewards C_star C_h control0 n i z := by
  unfold OLD
  rw [taskStage_of_not_pending rate rewards C_star C_h control0 n i z hi]
  intro h
  cases h

theorem not_FORMED_of_not_pending (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∉ Pnew rate rewards C_star C_h control0 n z) :
    ¬ FORMED rate rewards C_star C_h control0 n i z := by
  unfold FORMED
  rw [taskStage_of_not_pending rate rewards C_star C_h control0 n i z hi]
  intro h
  cases h

theorem not_OLD_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) : ¬ OLD rate rewards C_star C_h control0 n i z := by
  unfold OLD
  rw [taskStage_of_horizon_le rate rewards C_star C_h control0 n i z hn]
  intro h
  cases h

theorem not_FORMED_of_horizon_le (n : ℕ) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hn : p.T ≤ n) : ¬ FORMED rate rewards C_star C_h control0 n i z := by
  unfold FORMED
  rw [taskStage_of_horizon_le rate rewards C_star C_h control0 n i z hn]
  intro h
  cases h

theorem disjoint_OLD_FORMED (n : ℕ) (i : Fin (p.m - 1)) :
    Disjoint {z : Source (p := p) | OLD rate rewards C_star C_h control0 n i z}
      {z : Source (p := p) | FORMED rate rewards C_star C_h control0 n i z} := by
  exact Set.disjoint_left.mpr fun z ho hf =>
    OLD_FORMED_disjoint rate rewards C_star C_h control0 n i z ⟨ho, hf⟩


variable {rate rewards C_star C_h control0}

private theorem integral_of_indicator_formula
    (g : ContinuousLearningRows.TimeControl p → ℝ)
    (E : Set (ContinuousLearningRows.TimeControl p))
    (hg : Measurable g) (he : ∀ h, g h = E.indicator (fun _ => (1 : ℝ)) h) :
    ∫ h, g h ∂ContinuousLearningRows.timeControlLaw p =
      (ContinuousLearningRows.timeControlLaw p).real E := by
  have hE : MeasurableSet E := by
    have hset : E = g ⁻¹' {1} := by
      ext h
      rw [Set.mem_preimage, Set.mem_singleton_iff, he h]
      by_cases hm : h ∈ E <;> simp [Set.indicator, hm]
    rw [hset]
    exact hg (measurableSet_singleton 1)
  calc
    _ = ∫ h, E.indicator (fun _ => (1 : ℝ)) h
        ∂ContinuousLearningRows.timeControlLaw p := integral_congr_ae
          (Filter.Eventually.of_forall he)
    _ = _ := integral_indicator_one hE

private theorem coefficient_nonneg
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (t : Fin p.T) :
    0 ≤ (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hm : (1 : ℝ) < p.m := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) p.two_le_m)
  have hK : (0 : ℝ) < p.K := by exact_mod_cast (K_pos p)
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

private theorem down_integral_of_formula
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (he : ∀ h, ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h) =
        (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet rewards t i w).indicator (fun _ => (1 : ℝ)) h) :
    ∫ h, ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hg : Measurable (fun h => ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)) :=
    (ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t).comp
      ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
        ((measurable_const : Measurable (fun _ : ContinuousLearningRows.TimeControl p => z)).prodMk measurable_id))
  calc
    _ = (ContinuousLearningRows.timeControlLaw p).real
        (ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet rewards t i w) :=
      integral_of_indicator_formula _ _ hg he
    _ = _ := by rw [measureReal_def,
    ReferenceFirstCollectionDownConditionalService.downServiceFormulaSet_probability, ENNReal.toReal_ofReal (coefficient_nonneg rewards t)]

private theorem up_integral_of_formula
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (reply : ReferenceFirstCollectionUpConditionalService.UpRecord rate)
    (he : ∀ h, ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h) =
        (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet (rate := rate) rewards t i reply).indicator
          (fun _ => (1 : ℝ)) h) :
    ∫ h, ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  have hg := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)
  have hm : Measurable (fun h => ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)) :=
    (ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout (rate := rate)
    rewards C_star C_h i t).comp (hg.comp ((measurable_const : Measurable (fun _ : ContinuousLearningRows.TimeControl p => z)).prodMk measurable_id))
  calc
    _ = (ContinuousLearningRows.timeControlLaw p).real
        (ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet (rate := rate) rewards t i reply) :=
      integral_of_indicator_formula _ _ hm he
    _ = _ := by rw [measureReal_def,
    ReferenceFirstCollectionUpConditionalService.coordinatorUpServiceFormulaSet_probability,
    ENNReal.toReal_ofReal (coefficient_nonneg rewards t)]


/-- On a supported date, the actual replacement coordinate supplies both
literal readout identities and the original whole-control service integrals. -/
theorem pending_service_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (i : Fin (p.m - 1)) (z : Source (p := p))
    (hi : i ∈ Pnew rate rewards C_star C_h control0 t.val z) :
    (OLD rate rewards C_star C_h control0 t.val i z ∨
      FORMED rate rewards C_star C_h control0 t.val i z) ∧
    (((serviceParts rate rewards C_star C_h control0 i t.val z).1 : ℝ) =
      if OLD rate rewards C_star C_h control0 t.val i z then
        actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t z else 0) ∧
    (((serviceParts rate rewards C_star C_h control0 i t.val z).2 : ℝ) =
      if FORMED rate rewards C_star C_h control0 t.val i z then
        actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t z else 0) ∧
    (OLD rate rewards C_star C_h control0 t.val i z →
      ∫ h, actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
        (positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) ∧
    (FORMED rate rewards C_star C_h control0 t.val i z →
      ∫ h, actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z h)
        ∂ContinuousLearningRows.timeControlLaw p =
        (positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
  have hLoc := complete_first_replacement_awaited_pending_localization
    rate rewards C_star C_h control0 z t.val ⟨i, hi⟩
  have hPending := complete_first_replacement_pending_coordinates
    rate rewards C_star C_h control0 z
  have hStages := ReferenceFirstReplacementCollectionOrdinaryStages.complete_first_replacement_collection_ordinary_stages
    rate z rewards C_star C_h control0
  have hServices := ReferenceFirstReplacementCollectionUnmaskedFreshPositiveService.complete_first_replacement_collection_unmasked_fresh_positive_tests
    rate z rewards C_star C_h control0
  have hGeometry := ReferenceFirstReplacementCollectionFreshFollowerGeometry.complete_first_replacement_collection_follower_control_geometry
    rate z rewards C_star C_h
  have hBoundary := ReferenceFirstReplacementCutoffPreparedBoundary.complete_first_replacement_cutoff_follower_boundary
    rate z rewards C_star C_h
  have hReceiver := ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
    rate z rewards C_star C_h
  have hPure := ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
    rate z rewards C_star C_h
  dsimp only at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => simp only [hb] at hLoc
  | some birth =>
    simp only [hb] at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
    cases hbirth : birth.output.preparation.coordinator <;>
      simp only [hbirth] at hLoc
    rename_i old ledger clock cutoff outcome
    simp only [hbirth] at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
    cases outcome <;> try contradiction
    rename_i core consistent started hstart instruction hinstruction output hconsistent
      clockData installed selectedBirth
    dsimp only [ReferenceActivePhysicalStep.collectionInput]
      at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
    cases hc : R[c]? with
    | none => simp only [hc] at hLoc
    | some cut =>
      simp only [tail, c, hc] at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
      rcases hBoundary with ⟨_, hBoundary⟩
      rcases hReceiver with ⟨_, _, hReceiver⟩
      rcases hPure with ⟨_, _, hPure⟩
      cases hcut : cut.output.preparation.coordinator <;>
        simp only [hcut] at hLoc
      rename_i registers owned base outcome
      simp only [hcut] at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
      cases outcome <;> try contradiction
      rename_i dispatched hs ledger hiLedger hledger hdata hclock hpending hnone selectedCut
      dsimp only at hLoc hPending hStages hServices hGeometry hBoundary hReceiver hPure
      rcases hBoundary with
        ⟨_, _, _, _, _, _, _, _, _, _, _, selectedB, hselectedB, _, hpendingB, _, _⟩
      rcases hPure with ⟨_, ⟨_, hZLinks, hZRecords⟩, _⟩
      rcases hReceiver with ⟨hEndpoints, _, _⟩
      let P : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      let W := (R.drop (c + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
      let K := cut :: W
      let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.output.next (W.take j)
      let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
        cut.input.state (K.take j)
      obtain ⟨a, hdate, htime, hOnset⟩ := hLoc
      let r := K.get a
      have hfin : r.input.time = t := Fin.ext htime
      obtain ⟨_, hActualRecord, hRaw, _⟩ := hPending a
      have hrecord : actualRecord rate rewards C_star C_h t z = some r := by
        rw [← hfin]
        exact hActualRecord
      obtain ⟨v0, hv0, _hvpay, _hvcut, hbranches⟩ := hServices a
      have hViewPending : i ∈ v0.view.pendingAtChoice := by
        cases a using Fin.cases with
        | zero =>
          have hvCut : cut.output.preparation.coordinator.selection = some v0 := by
            simpa only [K, List.get_cons_zero] using hv0
          have hselectedCut : cut.output.preparation.coordinator.selection = some selectedB := by
            simpa only [hcut] using hselectedB
          have hvEq : v0 = selectedB := Option.some.inj (hvCut.symm.trans hselectedCut)
          have hview : v0.view.pendingAtChoice = Finset.univ := by
            simpa only [hvEq] using hpendingB
          rw [hview]
          exact Finset.mem_univ i
        | succ j =>
          have hjW : j.val < W.length := j.isLt
          let q : Fin K.length := ⟨j.val + 1, by dsimp only [K, List.length_cons]; omega⟩
          have hrecordState : (K.get q).input.state = E j := by
            exact (hZRecords q).1.trans (hZLinks j.val (Nat.le_of_lt hjW))
          have hselection : r.output.preparation.coordinator.selection = some v0 := hv0
          have hnotDagger : r.input.state.coordinator ≠ .dagger := by
            intro hd
            have hprep : (ReferenceActivePhysicalStep.prepare r.input).coordinator = .dagger :=
              ReferenceActivePhysicalStep.dispatch_dagger r.input hd
            have hnone : r.output.preparation.coordinator.selection = none := by
              rw [r.output_eq]
              change (ReferenceActivePhysicalStep.prepare r.input).coordinator.selection = none
              rw [hprep]
              rfl
            cases hnone.symm.trans hselection
          rcases hEndpoints j.val (Nat.le_of_lt hjW) with hdagger | ⟨taskLedger, saved, hcoord, _, _, _⟩
          · exact (hnotDagger ((congrArg
              (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
              hrecordState).trans hdagger)).elim
          · have hcoordInput : r.input.state.coordinator = .collection P taskLedger saved :=
              (congrArg (fun st : ReferenceActivePhysicalStep.State p rate => st.coordinator)
                hrecordState).trans hcoord
            have hn : ReferenceCollectionPhaseHistory.laterChosen r.input = false := by
              have hmemW : r ∈ W := by
                have hr : r = W.get ⟨j, hjW⟩ := by
                  simp only [r, K, List.get_cons_succ']
                  rfl
                exact hr ▸ List.get_mem W ⟨j, hjW⟩
              have hall := List.all_eq_true.mp (List.all_takeWhile
                (l := R.drop (c + 1))
                (p := fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)) r hmemW
              cases htag : ReferenceCollectionPhaseHistory.laterChosen r.input <;>
                simp_all only [Bool.not_true, Bool.false_eq_true]
            have hQ : i ∈ ReferenceFirstCollectionPendingObservation.Q
                rate rewards C_star C_h P.sigma.val r.input.time z := by
              rw [← hRaw, ← hdate]
              exact Pnew_subset_Praw rate rewards C_star C_h control0 t.val z hi
            have hQledger : i ∈ taskLedger.pending := by
              have hactual : actualRecord rate rewards C_star C_h r.input.time z = some r := by
                rw [hfin]
                exact hrecord
              simpa only [ReferenceFirstCollectionPendingObservation.Q, hactual,
                hcoordInput, ite_true, eq_self] using hQ
            have hfields := ReferenceFirstReplacementCollectionOldDownSenderReadiness.collection_selection_pending
              r P taskLedger saved hcoordInput hn v0 hselection
            rw [hfields.2]
            exact hQledger
      have hstage : taskStage rate rewards C_star C_h control0 t.val i z =
          some (choiceStage r P i) := by
        rw [taskStage_at_record rate rewards C_star C_h control0 t i z r P
          (cut.input.time.val + 1) hrecord hOnset, ite_eq_left hi]
      have ho : OLD rate rewards C_star C_h control0 t.val i z ↔
          actualOldAt r i (P.downRecord i) := by
        unfold OLD
        rw [hstage, Option.some.injEq, choiceStage_old_iff]
      have hf : FORMED rate rewards C_star C_h control0 t.val i z ↔
          replyFormedAt r i (P.downRecord i) := by
        unfold FORMED
        rw [hstage, Option.some.injEq, choiceStage_formed_iff]
        rfl
      obtain ⟨choice, memory, U, hchoice, hstatus, hdomain, _⟩ := hGeometry a i
      have hd : (ReferenceFirstReplacementCollectionActualCalendarTasks.downPositive r i : ℝ) =
          actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t z := by
        rw [ReferenceFirstReplacementCollectionCalendarServiceLaw.downPositive_eq_test
          r i choice memory hchoice hstatus hdomain, actualFirstCollectionDownReadout, hrecord]
        rw [hfin]
      have hu : (ReferenceFirstReplacementCollectionActualCalendarTasks.upPositive r i : ℝ) =
          actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t z := by
        rw [ReferenceFirstReplacementCollectionCalendarServiceLaw.upPositive_eq_test,
          actualFirstCollectionUpReadout, hrecord]
        rw [hfin]
        apply ite_congr
        · rfl
        · intro _; rfl
        · intro _; rfl
      have hparts := serviceParts_at_record rate rewards C_star C_h control0 i t z P
        (cut.input.time.val + 1) r hi hOnset hrecord
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rcases (hStages a i).1 with h | h
        · exact Or.inl (ho.mpr ((choiceStage_old_iff r P i).mp h))
        · exact Or.inr (hf.mpr ((choiceStage_formed_iff r P i).mp h))
      · simp only [hparts, recordServiceParts, ← ho, Nat.cast_ite, Nat.cast_zero, hd]
      · simp only [hparts, recordServiceParts, ← hf, Nat.cast_ite, Nat.cast_zero, hu]
      · intro hOld
        apply down_integral_of_formula rewards C_star C_h i t z
          (CoordinatorLocalArmChoice.storedDownFlatWord P i)
        intro h
        obtain ⟨rh, vh, _, _, _, _, _, _, _, he⟩ := (hbranches i hViewPending).1 (ho.mp hOld) h
        rw [hfin] at he
        exact he
      · intro hFormed
        obtain ⟨_, _, reply, _, _, _, _, _, _, hall⟩ := (hbranches i hViewPending).2 (hf.mp hFormed)
        apply up_integral_of_formula rewards C_star C_h i t z reply
        intro h
        obtain ⟨rh, vh, _, _, _, _, _, _, _, he⟩ := hall h
        rw [hfin] at he
        exact he

/-- Whole-source decomposition of the NEW literal service into its predictable
stage masks and the actual executed DOWN and UP readouts. -/
theorem service_eq_masked_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (fun z => (service rate rewards C_star C_h control0 i t.val z : ℝ)) =
      {z | OLD rate rewards C_star C_h control0 t.val i z}.indicator
        (actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t) +
      {z | FORMED rate rewards C_star C_h control0 t.val i z}.indicator
        (actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t) := by
  funext z
  by_cases hi : i ∈ Pnew rate rewards C_star C_h control0 t.val z
  · have h := pending_service_data rate rewards C_star C_h control0 t i z hi
    simp only [service, Nat.cast_add, Pi.add_apply, Set.indicator_apply]
    exact congrArg₂ (· + ·) h.2.1 h.2.2.1
  · have hnA := not_OLD_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    have hnB := not_FORMED_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    simp only [service, serviceParts_of_not_mem rate rewards C_star C_h control0 i t.val z hi,
      Nat.cast_zero, Pi.add_apply, Set.indicator_apply,
      Set.mem_ofPred_eq, ite_eq_right hnA, ite_eq_right hnB, add_zero]

/-- Ambient Borel measurability of the NEW actual sum. -/
theorem measurable_service
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable (fun z => (service rate rewards C_star C_h control0 i t.val z : ℝ)) := by
  rw [service_eq_masked_readouts]
  exact ((ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t).indicator
      (OLD_borel rate rewards C_star C_h control0 t.val i)).add
    ((ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t).indicator
      (FORMED_borel rate rewards C_star C_h control0 t.val i))

/-- Integrability under the original source law, with the new masks. -/
theorem integrable_service
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (fun z => (service rate rewards C_star C_h control0 i t.val z : ℝ))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  rw [service_eq_masked_readouts]
  exact ((ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t).indicator
      (OLD_borel rate rewards C_star C_h control0 t.val i)).add
    ((ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t).indicator
      (FORMED_borel rate rewards C_star C_h control0 t.val i))

/-- Every date outside the new task support keeps its literal zero readout. -/
theorem observation_eq_zero_of_not_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ)
    (z : Source (p := p)) (hi : i ∉ Pnew rate rewards C_star C_h control0 n z) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n z = 0 := by
  rw [observation_eq_service]
  simp only [service, serviceParts_of_not_mem rate rewards C_star C_h control0 i n z hi,
    Nat.add_zero, Nat.cast_zero]

/-- The analytical calendar extension has zero service after the horizon. -/
theorem observation_eq_zero_of_horizon_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ)
    (hn : p.T ≤ n) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n = 0 := by
  funext z
  apply observation_eq_zero_of_not_mem
  rw [Pnew_of_horizon_le rate rewards C_star C_h control0 n hn z]
  exact Finset.notMem_empty i

/-- The waiting observation is Borel measurable on every natural date. -/
theorem measurable_observation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ) :
    Measurable (PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n) := by
  by_cases hn : n < p.T
  · have he : PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n =
        fun z => (service rate rewards C_star C_h control0 i n z : ℝ) := by
      funext z
      exact observation_eq_service rate rewards C_star C_h control0 i n z
    rw [he]
    exact measurable_service rate rewards C_star C_h control0 ⟨n, hn⟩ i
  · rw [observation_eq_zero_of_horizon_le rate rewards C_star C_h control0 i n
      (Nat.le_of_not_lt hn)]
    exact measurable_const

/-- Integrability of the all-date observation uses only the original source law. -/
theorem integrable_observation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ) :
    Integrable (PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  by_cases hn : n < p.T
  · have he : PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n =
        fun z => (service rate rewards C_star C_h control0 i n z : ℝ) := by
      funext z
      exact observation_eq_service rate rewards C_star C_h control0 i n z
    rw [he]
    exact integrable_service rate rewards C_star C_h control0 ⟨n, hn⟩ i
  · rw [observation_eq_zero_of_horizon_le rate rewards C_star C_h control0 i n
      (Nat.le_of_not_lt hn)]
    exact integrable_zero _ _ _

/-- The new predictable stage is preserved by the prefix including this round. -/
theorem taskStage_end_factor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ)
    (z : Source (p := p)) :
    taskStage rate rewards C_star C_h control0 n i z =
      taskStage rate rewards C_star C_h control0 n i (sourcePrefix control0 (n + 1) z) := by
  rw [taskStage_factor rate rewards C_star C_h control0 n i z,
    taskStage_factor rate rewards C_star C_h control0 n i (sourcePrefix control0 (n + 1) z),
    sourcePrefix_sourcePrefix control0 n (n + 1) (by omega) z]

/-- The actual executed readouts and the new stage masks yield an actual
end-prefix factorization, with no adaptedness premise. -/
theorem observation_end_factor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ)
    (z : Source (p := p)) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n z =
      PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n
        (sourcePrefix control0 (n + 1) z) := by
  by_cases hn : n < p.T
  · let t : Fin p.T := ⟨n, hn⟩
    rw [observation_eq_service, observation_eq_service]
    have he := service_eq_masked_readouts rate rewards C_star C_h control0 t i
    have hz := congrFun he z
    have hp := congrFun he (sourcePrefix control0 (n + 1) z)
    rw [hz, hp]
    obtain ⟨hd, hu⟩ := ReferenceFirstCollectionRoundEndObservation.actual_readouts_end_factor
      (rate := rate) rewards C_star C_h control0 i t z
    have hs := taskStage_end_factor rate rewards C_star C_h control0 i n z
    dsimp only [t] at hd hu ⊢
    simp only [Pi.add_apply, Set.indicator_apply, Set.mem_ofPred_eq, OLD, FORMED,
      ← hs, hd, hu]
  · rw [observation_eq_zero_of_horizon_le rate rewards C_star C_h control0 i n
      (Nat.le_of_not_lt hn)]
    rfl

/-- The precise round-end strong-measurability input for the waiting assembly. -/
theorem observation_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ) :
    StronglyMeasurable[sourcePrefixFiltration control0 (n + 2)]
      (PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n) := by
  rw [show n + 2 = (n + 1) + 1 by omega, sourcePrefixFiltration_succ]
  have h := (measurable_observation rate rewards C_star C_h control0 i n).comp
    (comap_measurable (sourcePrefix control0 (n + 1)))
  have he : PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n =
      (PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n) ∘
        sourcePrefix control0 (n + 1) := by
    funext z
    exact observation_end_factor rate rewards C_star C_h control0 i n z
  rw [he]
  exact h.stronglyMeasurable

/-- OLD's strict-past factor permits applying the same actual-run constructor
to `c_t`. The full current control is then integrated using its fixed word. -/
theorem downFreshSection_of_OLD
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (ho : OLD rate rewards C_star C_h control0 t.val i z) :
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  let zp := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
  have ho' : OLD rate rewards C_star C_h control0 t.val i zp := by
    unfold OLD at ho ⊢
    rw [show zp = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z from
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
      ← taskStage_factor rate rewards C_star C_h control0 t.val i z]
    exact ho
  have hi' : i ∈ Pnew rate rewards C_star C_h control0 t.val zp := by
    by_contra hn
    exact not_OLD_of_not_pending rate rewards C_star C_h control0 t.val i zp hn ho'
  exact (pending_service_data rate rewards C_star C_h control0 t i zp hi').2.2.2.1 ho'

/-- FORMED is treated by the same original prefix. Its actual UP record is
produced inside the ordinary-stage theorem, and its coefficient is uniform. -/
theorem upFreshSection_of_FORMED
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1))
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hf : FORMED rate rewards C_star C_h control0 t.val i z) :
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t z =
      (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  let zp := ReferenceSourceCurrentControlFreshness.c_t p control0 t z
  have hf' : FORMED rate rewards C_star C_h control0 t.val i zp := by
    unfold FORMED at hf ⊢
    rw [show zp = ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z from
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
      ← taskStage_factor rate rewards C_star C_h control0 t.val i z]
    exact hf
  have hi' : i ∈ Pnew rate rewards C_star C_h control0 t.val zp := by
    by_contra hn
    exact not_FORMED_of_not_pending rate rewards C_star C_h control0 t.val i zp hn hf'
  exact (pending_service_data rate rewards C_star C_h control0 t i zp hi').2.2.2.2 hf'

/-- Whole-source conditional expectation of the NEW literal actual service.
The field is the original strict-past source-prefix filtration; neither a
replacement law nor a stage, survival, or history premise is assumed. -/
theorem actual_first_replacement_collection_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => (service rate rewards C_star C_h control0 i t.val z : ℝ)) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
      BootstrapPrivateRoundStreams.sourceInputLaw p]
    {z | i ∈ Pnew rate rewards C_star C_h control0 t.val z}.indicator
      (fun _ => (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
  let mu := BootstrapPrivateRoundStreams.sourceInputLaw p
  let F := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
  let A := {z | OLD rate rewards C_star C_h control0 t.val i z}
  let B := {z | FORMED rate rewards C_star C_h control0 t.val i z}
  let d := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
  let u := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
  have hd : Integrable d mu := ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout rewards C_star C_h i t
  have hu : Integrable u mu := ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout rewards C_star C_h i t
  have hA : MeasurableSet[F] A := OLD_measurable rate rewards C_star C_h control0 t.val i
  have hB : MeasurableSet[F] B := FORMED_measurable rate rewards C_star C_h control0 t.val i
  have hDA : Integrable (A.indicator d) mu :=
    hd.indicator (OLD_borel rate rewards C_star C_h control0 t.val i)
  have hUB : Integrable (B.indicator u) mu :=
    hu.indicator (FORMED_borel rate rewards C_star C_h control0 t.val i)
  have hsum := condExp_add hDA hUB F
  have hmaskD := condExp_indicator hd hA
  have hmaskU := condExp_indicator hu hB
  have hfield : F = ReferenceSourceCurrentControlFreshness.m_t p control0 t :=
    ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t
  have hcondD : mu[d | F] =ᵐ[mu]
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection (rate := rate) rewards C_star C_h control0 i t := by
    rw [hfield]
    exact ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp rewards C_star C_h control0 i t
  have hcondU : mu[u | F] =ᵐ[mu]
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection (rate := rate) rewards C_star C_h control0 i t := by
    rw [hfield]
    exact ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp rewards C_star C_h control0 i t
  rw [service_eq_masked_readouts]
  filter_upwards [hsum, hmaskD, hmaskU, hcondD, hcondU] with z hsum hmaskD hmaskU hcondD hcondU
  change mu[A.indicator d + B.indicator u | F] z = _
  rw [hsum]
  change mu[A.indicator d | F] z + mu[B.indicator u | F] z = _
  rw [hmaskD, hmaskU]
  by_cases hi : i ∈ Pnew rate rewards C_star C_h control0 t.val z
  · have hiSet : z ∈ {z | i ∈ Pnew
        rate rewards C_star C_h control0 t.val z} := hi
    rw [Set.indicator_of_mem hiSet]
    rcases (pending_service_data rate rewards C_star C_h control0 t i z hi).1 with ho | hf
    · have hn : z ∉ B := fun hf => OLD_FORMED_disjoint
        rate rewards C_star C_h control0 t.val i z ⟨ho, hf⟩
      have hoSet : z ∈ A := ho
      rw [Set.indicator_of_mem hoSet, Set.indicator_of_notMem hn, add_zero, hcondD]
      exact downFreshSection_of_OLD rate rewards C_star C_h control0 t i z ho
    · have hn : z ∉ A := fun ho => OLD_FORMED_disjoint
        rate rewards C_star C_h control0 t.val i z ⟨ho, hf⟩
      have hfSet : z ∈ B := hf
      rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hfSet, zero_add, hcondU]
      exact upFreshSection_of_FORMED rate rewards C_star C_h control0 t i z hf
  · have hnA : z ∉ A := not_OLD_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    have hnB : z ∉ B := not_FORMED_of_not_pending rate rewards C_star C_h control0 t.val i z hi
    rw [Set.indicator_of_notMem hnA, Set.indicator_of_notMem hnB]
    have hiSet : z ∉ {z | i ∈ Pnew
        rate rewards C_star C_h control0 t.val z} := hi
    rw [Set.indicator_of_notMem hiSet, add_zero]

/-- Pending-point form used by the separate actual collection waiting assembly.
All exceptional paths stay in the unchanged pending mask. -/
theorem actual_first_replacement_collection_condExp_of_pending
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n < p.T)
    (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      i ∈ Pnew rate rewards C_star C_h control0 n z →
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        (fun z => (service rate rewards C_star C_h control0 i n z : ℝ)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (n + 1)] z =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount rewards ⟨n, hn⟩ : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  filter_upwards [actual_first_replacement_collection_condExp rate rewards C_star C_h control0 ⟨n, hn⟩ i]
    with z hz
  intro hi
  have hiSet : z ∈ {z | i ∈ Pnew
      rate rewards C_star C_h control0 n z} := hi
  exact hz.trans (Set.indicator_of_mem hiSet _)

/-- Whole-source original-law conditional service for the accepted NEW binary
observation, including the current detecting update. -/
theorem observation_condExp
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (i : Fin (p.m - 1)) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i t.val |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[
        BootstrapPrivateRoundStreams.sourceInputLaw p]
      {z | i ∈ Pnew rate rewards C_star C_h control0 t.val z}.indicator
        (fun _ => (positiveRewardCount rewards t : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) := by
  have he : PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i t.val =
      fun z => (service rate rewards C_star C_h control0 i t.val z : ℝ) := by
    funext z
    exact observation_eq_service rate rewards C_star C_h control0 i t.val z
  rw [he]
  exact actual_first_replacement_collection_condExp rate rewards C_star C_h control0 t i

/-- The waiting weight is exactly the whole row's positive-arm count in range. -/
theorem g_eq_positiveRewardCount
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (n : ℕ) (hn : n < p.T)
    (z : Source (p := p)) :
    ReferenceFirstCollectionRoundEndObservation.g rewards n z =
      (positiveRewardCount rewards ⟨n, hn⟩ : ℝ) := by
  exact dite_eq_left hn

/-- Supported-point service in the exact weight notation used by the new
calendar waiting consumer. The field and law remain the original source's. -/
theorem observation_condExp_of_mem
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n < p.T)
    (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      i ∈ Pnew rate rewards C_star C_h control0 n z →
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n |
        sourcePrefixFiltration control0 (n + 1)] z =
        ReferenceFirstCollectionRoundEndObservation.g rewards n z /
          (8 * (p.m - 1 : ℝ) * p.K) := by
  filter_upwards [observation_condExp rate rewards C_star C_h control0 ⟨n, hn⟩ i] with z hz
  intro hi
  rw [g_eq_positiveRewardCount rewards n hn z]
  have hiSet : z ∈ {z | i ∈ Pnew rate rewards C_star C_h control0 n z} := hi
  exact hz.trans (Set.indicator_of_mem hiSet _)

/-- Directly usable service inequality with the coefficient `1/(8dK)`. -/
theorem observation_service_lower_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n < p.T)
    (i : Fin (p.m - 1)) :
    ∀ᵐ z ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      i ∈ Pnew rate rewards C_star C_h control0 n z →
      1 / (8 * (p.m - 1 : ℝ) * p.K) *
          ReferenceFirstCollectionRoundEndObservation.g rewards n z ≤
        (BootstrapPrivateRoundStreams.sourceInputLaw p)[
          PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n |
          sourcePrefixFiltration control0 (n + 1)] z := by
  filter_upwards [observation_condExp_of_mem rate rewards C_star C_h control0 n hn i] with z hz
  intro hi
  rw [hz hi, one_div_mul_eq_div]

/-- Missing replacement onset has zero observation on the entire calendar. -/
theorem observation_eq_zero_of_onset_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (n : ℕ)
    (z : Source (p := p))
    (hp : payloadOnset rate rewards C_star C_h n z = none) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i n z = 0 := by
  apply observation_eq_zero_of_not_mem
  rw [Pnew_of_onset_none rate rewards C_star C_h control0 n z hp]
  exact Finset.notMem_empty i

/-- A missing actual record is still a literal zero branch of the NEW service. -/
theorem observation_eq_zero_of_record_none
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : Source (p := p)) (hr : actualRecord rate rewards C_star C_h t z = none) :
    PhaseServiceWaiting.observation (x rate rewards C_star C_h control0) i t.val z = 0 := by
  rw [observation_eq_service]
  by_cases hi : i ∈ Pnew rate rewards C_star C_h control0 t.val z
  · simp only [service, serviceParts, ite_eq_left hi, dite_eq_left t.isLt, hr]
    cases payloadOnset rate rewards C_star C_h t.val z with
    | none => norm_num
    | some pair => rcases pair with ⟨payload, u⟩; norm_num
  · simp only [service, serviceParts_of_not_mem rate rewards C_star C_h control0 i t.val z hi,
      Nat.add_zero, Nat.cast_zero]

end Bandits.Support.ReferenceFirstReplacementCollectionAwaitedCalendarServiceLaw
