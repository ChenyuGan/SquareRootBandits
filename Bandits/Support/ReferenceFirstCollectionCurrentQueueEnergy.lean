/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentQueueReadout

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original first collection-call score marginals and queue energy

This module reads both score-weight vectors from the original optional queue
readouts, localizes their scalar inclusion marginals to the actual first-call
event, and proves the deterministic reflected-energy drift envelope on the
original source space.

Sources: `04_slow_fast_learner.tex:140-188,245-315`,
`05_binary_transport.tex:352-431`, and `06_interruptions.tex:355-426` under
`sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionCurrentQueueEnergy

open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefixFiltration)
open ReferenceFirstCollectionCurrentRetainedGate (G)
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability (stateReadout)
open ReferenceFirstCollectionCurrentQueueReadout
  (QueueReadout before? after? bMinus bPlus Bcap x)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "E" => firstCell rate rewards C_star C_h
local notation "G" => G rate rewards C_star C_h
local notation "μ" => sourceInputLaw p

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance readoutOptionMeasurableSpace :
    MeasurableSpace (Option (QueueReadout p.K)) :=
  ReferenceInitializationMeasurability.optionCountableMeasurableSpace _

/-- The source score-weight vector read directly from one existing register
tuple. -/
public def weightVectorOfReadout (r : QueueReadout p.K) :
    Fin p.K → ℝ :=
  fun a => (1 + 1 / (D p : ℝ)) ^ ((r.1 a).1 : ℕ)

/-- The optional incoming whole score-weight vector. Absence stays absent. -/
public def weightMinus? (t : Fin p.T) (z : SourceInput p) :
    Option (Fin p.K → ℝ) :=
  (before? rate rewards C_star C_h t z).map weightVectorOfReadout

/-- The optional outgoing whole score-weight vector. Absence stays absent. -/
public def weightPlus? (t : Fin p.T) (z : SourceInput p) :
    Option (Fin p.K → ℝ) :=
  (after? rate rewards C_star C_h t z).map weightVectorOfReadout

/-- Apply the product-set marginal only inside a present whole vector. The
scalar for an absent observation is explicitly zero. -/
public def thetaOfOptionalWeights
    (w? : Option (Fin p.K → ℝ)) (a : Fin p.K) : ℝ :=
  w?.elim 0 (fun w => ProductSetLaw.theta p.m w a)

/-- The incoming score marginal, localized to the original first-call event. -/
public def thetaMinus (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (E u t).indicator (fun z =>
    thetaOfOptionalWeights
      (weightMinus? rate rewards C_star C_h t z) a) z

/-- The outgoing score marginal, localized to the same original call. -/
public def thetaPlus (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (E u t).indicator (fun z =>
    thetaOfOptionalWeights
      (weightPlus? rate rewards C_star C_h t z) a) z

/-- Incoming score-weighted quadratic backlog energy. -/
public def VMinus (u t : Fin p.T) (z : SourceInput p) : ℝ :=
  ∑ a : Fin p.K,
    thetaMinus rate rewards C_star C_h u t a z *
      (bMinus rate rewards C_star C_h u t a z) ^ 2

/-- Outgoing score-weighted quadratic backlog energy. -/
public def VPlus (u t : Fin p.T) (z : SourceInput p) : ℝ :=
  ∑ a : Fin p.K,
    thetaPlus rate rewards C_star C_h u t a z *
      (bPlus rate rewards C_star C_h u t a z) ^ 2

/-- The incoming score-weighted backlog used by the next conditional drift
consumer. -/
public def weightedBacklog (u t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  ∑ a : Fin p.K,
    thetaMinus rate rewards C_star C_h u t a z *
      bMinus rate rewards C_star C_h u t a z

/-- One arm's localized deterministic reduced drift term. -/
public def reducedDriftTerm (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  (G u t).indicator (fun z =>
    thetaMinus rate rewards C_star C_h u t a z *
      ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
        (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z +
        (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t a z) ^ 2 + 16)) z

/-- The deterministic reduced drift envelope on the whole source space. -/
public def reducedDriftEnvelope (u t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  (G u t).indicator (fun z =>
    ∑ a : Fin p.K,
      thetaMinus rate rewards C_star C_h u t a z *
        ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
          (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
            ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
              rate rewards C_star C_h u t a z +
          (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z) ^ 2 + 16)) z

private theorem weightVectorOfReadout_stateReadout
    (state : RecordedQueueRun.RunState p.K) :
    weightVectorOfReadout (stateReadout state) =
      RecordedQueueRun.scoreWeight q state := by
  funext a
  rfl

/-- The original first-call witness identifies both optional score vectors
with the same actual run and its one retained step. -/
theorem firstCell_actual_score_marginals (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ E u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      weightMinus? rate rewards C_star C_h t z =
        some (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) ∧
      weightPlus? rate rewards C_star C_h t z =
        some (RecordedQueueRun.scoreWeight q
          (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) ∧
      (fun a => thetaMinus rate rewards C_star C_h u t a z) =
        (fun a => ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a) ∧
      (fun a => thetaPlus rate rewards C_star C_h u t a z) =
        (fun a => ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a) := by
  obtain ⟨L, c, hL, hc, henabled, hbefore, hafter, _, _, _, _⟩ :=
    ReferenceFirstCollectionCurrentQueueReadout.firstCell_actual_queue_readouts
      rate rewards C_star C_h u t
        (⟨0, lt_of_lt_of_le (by decide : 0 < 2)
          (le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K))⟩) z hz
  have hwm : weightMinus? rate rewards C_star C_h t z =
      some (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) := by
    unfold weightMinus?
    rw [hbefore]
    simp only [Option.map_some]
    exact congrArg some
      (weightVectorOfReadout_stateReadout rate (RecordedQueueRun.run q L))
  have hwp : weightPlus? rate rewards C_star C_h t z =
      some (RecordedQueueRun.scoreWeight q
        (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) := by
    unfold weightPlus?
    rw [hafter]
    simp only [Option.map_some]
    exact congrArg some (weightVectorOfReadout_stateReadout rate
      (RecordedQueueRun.step q (RecordedQueueRun.run q L) c))
  refine ⟨L, c, hL, hc, henabled, hwm, hwp, ?_, ?_⟩
  · funext a
    simp [thetaMinus, Set.indicator_of_mem hz, hwm,
      thetaOfOptionalWeights]
  · funext a
    simp [thetaPlus, Set.indicator_of_mem hz, hwp,
      thetaOfOptionalWeights]

private theorem thetaReadoutOption_bounds
    (r? : Option (QueueReadout p.K)) (a : Fin p.K) :
    0 ≤ thetaOfOptionalWeights (r?.map weightVectorOfReadout) a ∧
      thetaOfOptionalWeights (r?.map weightVectorOfReadout) a ≤ 1 := by
  cases r? with
  | none => simp [thetaOfOptionalWeights]
  | some r =>
      have hw (j : Fin p.K) :
          0 < weightVectorOfReadout r j := by
        unfold weightVectorOfReadout
        positivity
      change 0 ≤ ProductSetLaw.theta p.m
          (weightVectorOfReadout r) a ∧
        ProductSetLaw.theta p.m
          (weightVectorOfReadout r) a ≤ 1
      exact ⟨(ProductSetLaw.theta_pos _ _
          (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
          p.m_lt_K hw).le,
        (ProductSetLaw.theta_lt_one _ _
          (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
          p.m_lt_K hw).le⟩

/-- Both localized inclusion marginals are globally in the unit interval. -/
theorem thetaMinus_bounds (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    0 ≤ thetaMinus rate rewards C_star C_h u t a z ∧
      thetaMinus rate rewards C_star C_h u t a z ≤ 1 := by
  by_cases hE : z ∈ E u t
  · rw [thetaMinus, Set.indicator_of_mem hE]
    exact thetaReadoutOption_bounds
      (before? rate rewards C_star C_h t z) a
  · rw [thetaMinus, Set.indicator_of_notMem hE]
    exact ⟨le_rfl, zero_le_one⟩

theorem thetaPlus_bounds (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) :
    0 ≤ thetaPlus rate rewards C_star C_h u t a z ∧
      thetaPlus rate rewards C_star C_h u t a z ≤ 1 := by
  by_cases hE : z ∈ E u t
  · rw [thetaPlus, Set.indicator_of_mem hE]
    exact thetaReadoutOption_bounds
      (after? rate rewards C_star C_h t z) a
  · rw [thetaPlus, Set.indicator_of_notMem hE]
    exact ⟨le_rfl, zero_le_one⟩

/-- The incoming score marginals have total mass `m` exactly on the original
first-call event, and total mass zero elsewhere. -/
theorem sum_thetaMinus (u t : Fin p.T) (z : SourceInput p) :
    (∑ a : Fin p.K, thetaMinus rate rewards C_star C_h u t a z) =
      (p.m : ℝ) * (E u t).indicator (fun _ : SourceInput p => (1 : ℝ)) z := by
  by_cases hE : z ∈ E u t
  · obtain ⟨L, _, _, _, _, _, _, hθ, _⟩ :=
      firstCell_actual_score_marginals rate rewards C_star C_h u t z hE
    have hsum := ProductSetLaw.sum_theta_eq_card
      (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L))
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (fun a => RecordedPotentialStep.scoreWeight_pos q (RecordedQueueRun.run q L) a)
    have hrewrite : (∑ a : Fin p.K,
        thetaMinus rate rewards C_star C_h u t a z) =
        ∑ a : Fin p.K, ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrFun hθ a
    rw [hrewrite, hsum]
    simp [Set.indicator_of_mem hE]
  · rw [Set.indicator_of_notMem hE]
    have hzθ (a : Fin p.K) : thetaMinus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaMinus, Set.indicator_of_notMem hE]
    simp [hzθ]

theorem sum_thetaPlus (u t : Fin p.T) (z : SourceInput p) :
    (∑ a : Fin p.K, thetaPlus rate rewards C_star C_h u t a z) =
      (p.m : ℝ) * (E u t).indicator (fun _ : SourceInput p => (1 : ℝ)) z := by
  by_cases hE : z ∈ E u t
  · obtain ⟨L, c, _, _, _, _, _, _, hθ⟩ :=
      firstCell_actual_score_marginals rate rewards C_star C_h u t z hE
    have hsum := ProductSetLaw.sum_theta_eq_card
      (RecordedQueueRun.scoreWeight q
        (RecordedQueueRun.step q (RecordedQueueRun.run q L) c))
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (fun a => RecordedPotentialStep.scoreWeight_pos q
        (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) a)
    have hrewrite : (∑ a : Fin p.K,
        thetaPlus rate rewards C_star C_h u t a z) =
        ∑ a : Fin p.K, ProductSetLaw.theta p.m
          (RecordedQueueRun.scoreWeight q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact congrFun hθ a
    rw [hrewrite, hsum]
    simp [Set.indicator_of_mem hE]
  · rw [Set.indicator_of_notMem hE]
    have hzθ (a : Fin p.K) : thetaPlus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaPlus, Set.indicator_of_notMem hE]
    simp [hzθ]

private theorem sourceSmallRate : 4 * rate.eta.val ≤ 1 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) p.two_le_m)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 2)
      (le_trans p.two_le_m (Nat.le_of_lt p.m_lt_K)))
  have hL : (1 : ℝ) ≤
      (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hden : (4 : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      (4 : ℝ) = 4 * 1 * 1 * 1 := by ring
      _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by
        gcongr
        norm_num
  have hdenpos : 0 <
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    linarith
  calc
    4 * rate.eta.val ≤ 4 *
        (1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ))) :=
      mul_le_mul_of_nonneg_left rate.sourceCap (by norm_num)
    _ = 4 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) := by ring
    _ ≤ 1 := (div_le_iff₀ hdenpos).2 (by simpa using hden)

private theorem exp_four_eta_le_one_add_eight_eta :
    Real.exp (4 * rate.eta.val) ≤ 1 + 8 * rate.eta.val := by
  have hx : 0 ≤ 4 * rate.eta.val :=
    mul_nonneg (by norm_num) rate.eta.property.le
  have hsmall := sourceSmallRate rate
  have hexp := RecordedPotentialStep.exp_le_one_add_add_sq hx hsmall
  have hxsq : (4 * rate.eta.val) ^ 2 ≤ 4 * rate.eta.val := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * rate.eta.val)
      (by linarith : 0 ≤ 1 - 4 * rate.eta.val)]
  nlinarith

private theorem actual_weight_ratio_bounds
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    1 ≤ RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state c) a /
        RecordedQueueRun.scoreWeight q state a ∧
      RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state c) a /
        RecordedQueueRun.scoreWeight q state a ≤ Real.exp (4 * rate.eta.val) := by
  let w := RecordedQueueRun.scoreWeight q state a
  let w' := RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state c) a
  have hw : 0 < w := RecordedPotentialStep.scoreWeight_pos q state a
  have hLam0 : 0 ≤ RecordedPotentialStep.potentialLambda q :=
    (RecordedPotentialStep.potentialLambda_pos q).le
  have hLam : RecordedPotentialStep.potentialLambda q ≤ rate.eta.val :=
    RecordedPotentialStep.potentialLambda_le_eta q
  have hs0 : 0 ≤ RecordedPotentialStep.servedEstimate q state c a :=
    RecordedPotentialStep.servedEstimate_nonneg q state c a
  have hs4 : RecordedPotentialStep.servedEstimate q state c a ≤ 4 :=
    RecordedPotentialStep.servedEstimate_le_four q state c a
  have hx0 : 0 ≤ RecordedPotentialStep.potentialLambda q *
      RecordedPotentialStep.servedEstimate q state c a :=
    mul_nonneg hLam0 hs0
  have hxle : RecordedPotentialStep.potentialLambda q *
      RecordedPotentialStep.servedEstimate q state c a ≤ 4 * rate.eta.val := by
    calc
      _ ≤ rate.eta.val *
          RecordedPotentialStep.servedEstimate q state c a :=
        mul_le_mul_of_nonneg_right hLam hs0
      _ ≤ rate.eta.val * 4 :=
        mul_le_mul_of_nonneg_left hs4 rate.eta.property.le
      _ = 4 * rate.eta.val := by ring
  have hratio := RecordedPotentialStep.step_scoreWeight_ratio_exp q state c a
  have hratioBounds : 1 ≤ w' / w ∧
      w' / w ≤ Real.exp (4 * rate.eta.val) := by
    rw [hratio]
    constructor
    · simpa using (Real.exp_le_exp.mpr hx0)
    · exact Real.exp_le_exp.mpr hxle
  constructor
  · simpa [w, w'] using hratioBounds.1
  · simpa [w, w'] using hratioBounds.2

private theorem actual_theta_growth
    (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state c)) a ≤
      Real.exp (4 * rate.eta.val) *
        ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight q state) a := by
  let v := RecordedQueueRun.scoreWeight q state
  let w := RecordedQueueRun.scoreWeight q (RecordedQueueRun.step q state c)
  have hvpos (j : Fin p.K) : 0 < v j :=
    RecordedPotentialStep.scoreWeight_pos q state j
  have hwpos (j : Fin p.K) : 0 < w j :=
    RecordedPotentialStep.scoreWeight_pos q (RecordedQueueRun.step q state c) j
  have hratio (j : Fin p.K) :
      1 ≤ w j / v j ∧ w j / v j ≤ Real.exp (4 * rate.eta.val) :=
    actual_weight_ratio_bounds rate state c j
  have hle (j : Fin p.K) : v j ≤ w j := by
    have h := hratio j |>.1
    have h' : 1 * v j ≤ w j := by
      exact (le_div_iff₀ (hvpos j)).mp h
    simpa using h'
  let cfac := w a / v a
  have hcfac : 1 ≤ cfac := (hratio a).1
  have hfacupper : cfac ≤ Real.exp (4 * rate.eta.val) := (hratio a).2
  have hcoord : cfac * v a = w a := by
    dsimp [cfac]
    field_simp [ne_of_gt (hvpos a)]
  have hposUpdate (j : Fin p.K) :
      0 < Function.update v a (w a) j := by
    by_cases hja : j = a
    · subst j
      simpa using hwpos a
    · simpa [Function.update_of_ne hja] using hvpos j
  have hother (j : Fin p.K) (hja : j ≠ a) :
      Function.update v a (w a) j ≤ w j := by
    simpa [Function.update_of_ne hja] using hle j
  have hanti := ProductMarginalStability.theta_antitone_of_other_coord_le
    (Function.update v a (w a)) w a p.two_le_m p.m_lt_K
    hposUpdate (fun j => hwpos j) (by simp) hother
  have hupdate := ProductMarginalStability.theta_update_le v a cfac
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hvpos hcfac
  have hupdateEq : Function.update v a (cfac * v a) =
      Function.update v a (w a) := by
    funext j
    by_cases hja : j = a
    · subst j
      simp [hcoord]
    · simp [Function.update_of_ne hja]
  calc
    ProductSetLaw.theta p.m w a ≤
        ProductSetLaw.theta p.m (Function.update v a (w a)) a := hanti
    _ = ProductSetLaw.theta p.m (Function.update v a (cfac * v a)) a := by
      rw [← hupdateEq]
    _ ≤ cfac * ProductSetLaw.theta p.m v a := hupdate
    _ ≤ Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v a :=
      mul_le_mul_of_nonneg_right hfacupper
        (ProductSetLaw.theta_pos v a
          (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
          p.m_lt_K hvpos).le

/-- On the original call, all arm weights are the actual same-run score
weights, and each includes the first detecting overflow update. -/
theorem firstCell_weight_ratio_bounds (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ E u t) :
    ∃ (L : List (RecordedQueueRun.RoundInput p.K))
      (c : RecordedQueueRun.RoundInput p.K),
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
          rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
          rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      weightMinus? rate rewards C_star C_h t z =
        some (RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L)) ∧
      weightPlus? rate rewards C_star C_h t z =
        some (RecordedQueueRun.scoreWeight q
          (RecordedQueueRun.step q (RecordedQueueRun.run q L) c)) ∧
      (∀ a, 1 ≤ RecordedQueueRun.scoreWeight q
          (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) a /
            RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) a ∧
          RecordedQueueRun.scoreWeight q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) a /
            RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) a ≤
              Real.exp (4 * rate.eta.val)) := by
  obtain ⟨L, c, hL, hc, henabled, hwm, hwp, _, _⟩ :=
    firstCell_actual_score_marginals rate rewards C_star C_h u t z hz
  exact ⟨L, c, hL, hc, henabled, hwm, hwp,
    fun a => actual_weight_ratio_bounds rate
      (RecordedQueueRun.run q L) c a⟩

/-- The outgoing numerical inclusion marginal grows by at most the source
factor, with both vectors identified by one actual first-call witness. -/
theorem thetaPlus_le_exp_mul_thetaMinus (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ E u t) (a : Fin p.K) :
    thetaPlus rate rewards C_star C_h u t a z ≤
      Real.exp (4 * rate.eta.val) *
        thetaMinus rate rewards C_star C_h u t a z := by
  obtain ⟨L, c, _, _, _, _, _, hθminus, hθplus⟩ :=
    firstCell_actual_score_marginals rate rewards C_star C_h u t z hz
  rw [congrFun hθplus a, congrFun hθminus a]
  exact actual_theta_growth rate (RecordedQueueRun.run q L) c a

/-- The ordinary small-rate form of the same actual marginal comparison. -/
theorem thetaPlus_le_one_add_eight_eta_mul_thetaMinus
    (u t : Fin p.T) (z : SourceInput p) (hz : z ∈ E u t)
    (a : Fin p.K) :
    thetaPlus rate rewards C_star C_h u t a z ≤
      (1 + 8 * rate.eta.val) *
        thetaMinus rate rewards C_star C_h u t a z := by
  exact (thetaPlus_le_exp_mul_thetaMinus rate rewards C_star C_h u t
    z hz a).trans (mul_le_mul_of_nonneg_right
      (exp_four_eta_le_one_add_eight_eta rate)
      (thetaMinus_bounds rate rewards C_star C_h u t a z).1)

private theorem thetaReadoutOption_measurable (a : Fin p.K) :
    Measurable (fun r? : Option (QueueReadout p.K) =>
      thetaOfOptionalWeights (r?.map weightVectorOfReadout) a) := by
  classical
  exact measurable_of_countable _

/-- The incoming numerical marginal is measurable in the exact source
pre-choice filtration. -/
theorem measurable_thetaMinus (control0 : TimeControl p) (u t : Fin p.T)
    (a : Fin p.K) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (thetaMinus rate rewards C_star C_h u t a) := by
  let F := sourcePrefixFiltration control0 (t.val + 1)
  have hbefore : Measurable[F]
      (before? rate rewards C_star C_h t) :=
    ReferenceFirstCollectionCurrentQueueReadout.before?_measurable
      rate rewards C_star C_h control0 t
  have hbase : Measurable[F] (fun z =>
      thetaOfOptionalWeights
        ((before? rate rewards C_star C_h t z).map weightVectorOfReadout) a) :=
    (thetaReadoutOption_measurable a).comp hbefore
  have hE : MeasurableSet[F] (E u t) :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  change Measurable[F] ((E u t).indicator (fun z =>
    thetaOfOptionalWeights
      ((before? rate rewards C_star C_h t z).map weightVectorOfReadout) a))
  exact hbase.indicator hE

/-- The outgoing marginal is ambient Borel measurable on the original source
space; no post-update pre-choice measurability is asserted. -/
theorem measurable_thetaPlus (control0 : TimeControl p) (u t : Fin p.T)
    (a : Fin p.K) :
    Measurable (thetaPlus rate rewards C_star C_h u t a) := by
  have hafter : Measurable (after? rate rewards C_star C_h t) :=
    ReferenceFirstCollectionCurrentQueueReadout.after?_measurable
      rate rewards C_star C_h control0 t
  have hbase : Measurable (fun z =>
      thetaOfOptionalWeights
        ((after? rate rewards C_star C_h t z).map weightVectorOfReadout) a) :=
    (thetaReadoutOption_measurable a).comp hafter
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  have hE_F : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      (E u t) :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hE : MeasurableSet (E u t) := hle _ hE_F
  change Measurable ((E u t).indicator (fun z =>
    thetaOfOptionalWeights
      ((after? rate rewards C_star C_h t z).map weightVectorOfReadout) a))
  exact hbase.indicator hE

theorem measurable_thetaMinus_ambient (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Measurable (thetaMinus rate rewards C_star C_h u t a) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono
    (measurable_thetaMinus rate rewards C_star C_h control0 u t a) hle le_rfl

theorem measurable_VMinus (control0 : TimeControl p) (u t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (VMinus rate rewards C_star C_h u t) := by
  apply Finset.measurable_fun_sum
  intro a ha
  exact (measurable_thetaMinus rate rewards C_star C_h control0 u t a).mul
    ((ReferenceFirstCollectionCurrentQueueReadout.bMinus_measurable
      rate rewards C_star C_h control0 u t a).pow_const 2)

theorem measurable_VPlus (control0 : TimeControl p) (u t : Fin p.T) :
    Measurable (VPlus rate rewards C_star C_h u t) := by
  apply Finset.measurable_fun_sum
  intro a ha
  exact (measurable_thetaPlus rate rewards C_star C_h control0 u t a).mul
    ((ReferenceFirstCollectionCurrentQueueReadout.bPlus_measurable
      rate rewards C_star C_h control0 u t a).pow_const 2)

theorem measurable_weightedBacklog (control0 : TimeControl p)
    (u t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (weightedBacklog rate rewards C_star C_h u t) := by
  apply Finset.measurable_fun_sum
  intro a ha
  exact (measurable_thetaMinus rate rewards C_star C_h control0 u t a).mul
    (ReferenceFirstCollectionCurrentQueueReadout.bMinus_measurable
      rate rewards C_star C_h control0 u t a)

private theorem Bcap_nonneg : 0 ≤ Bcap rate := by
  unfold Bcap
  exact le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property))

private theorem Vcap_nonneg : 0 ≤ 4 * (p.m : ℝ) * Bcap rate ^ 2 := by
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ Bcap rate := Bcap_nonneg rate
  positivity

private theorem backlogCap_nonneg : 0 ≤ 2 * (p.m : ℝ) * Bcap rate := by
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ Bcap rate := Bcap_nonneg rate
  positivity

private theorem sum_thetaMinus_on_firstCell (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ E u t) :
    (∑ a : Fin p.K, thetaMinus rate rewards C_star C_h u t a z) =
      (p.m : ℝ) := by
  simpa [Set.indicator_of_mem hz] using
    (sum_thetaMinus rate rewards C_star C_h u t z)

private theorem sum_thetaPlus_on_firstCell (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ E u t) :
    (∑ a : Fin p.K, thetaPlus rate rewards C_star C_h u t a z) =
      (p.m : ℝ) := by
  simpa [Set.indicator_of_mem hz] using
    (sum_thetaPlus rate rewards C_star C_h u t z)

/-- Both original-call energies obey the stopped queue's actual two-cap
envelope, and vanish off the call. -/
theorem VMinus_bounds (u t : Fin p.T) (z : SourceInput p) :
    0 ≤ VMinus rate rewards C_star C_h u t z ∧
      VMinus rate rewards C_star C_h u t z ≤
        4 * (p.m : ℝ) * Bcap rate ^ 2 := by
  by_cases hE : z ∈ E u t
  · have hsum := sum_thetaMinus_on_firstCell rate rewards C_star C_h u t z hE
    have hcap : 0 ≤ 2 * Bcap rate := mul_nonneg (by norm_num) (Bcap_nonneg rate)
    have hterms (a : Fin p.K) :
        thetaMinus rate rewards C_star C_h u t a z *
            (bMinus rate rewards C_star C_h u t a z) ^ 2 ≤
          thetaMinus rate rewards C_star C_h u t a z * (2 * Bcap rate) ^ 2 := by
      have hθ := thetaMinus_bounds rate rewards C_star C_h u t a z
      have hb := ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
        rate rewards C_star C_h u t a z
      have hsq : (bMinus rate rewards C_star C_h u t a z) ^ 2 ≤
          (2 * Bcap rate) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hb.2)
          (add_nonneg hcap hb.1)]
      exact mul_le_mul_of_nonneg_left hsq hθ.1
    constructor
    · unfold VMinus
      apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (thetaMinus_bounds rate rewards C_star C_h u t a z).1
        (sq_nonneg _)
    · calc
        VMinus rate rewards C_star C_h u t z ≤
            ∑ a : Fin p.K,
              thetaMinus rate rewards C_star C_h u t a z *
                (2 * Bcap rate) ^ 2 := by
          unfold VMinus
          exact Finset.sum_le_sum (fun a ha => hterms a)
        _ = (∑ a : Fin p.K,
              thetaMinus rate rewards C_star C_h u t a z) *
              (2 * Bcap rate) ^ 2 := by rw [Finset.sum_mul]
        _ = 4 * (p.m : ℝ) * Bcap rate ^ 2 := by rw [hsum]; ring
  · have hθ (a : Fin p.K) :
        thetaMinus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaMinus, Set.indicator_of_notMem hE]
    constructor
    · simp [VMinus, hθ]
    · have hzero : VMinus rate rewards C_star C_h u t z = 0 := by
        simp [VMinus, hθ]
      rw [hzero]
      exact Vcap_nonneg rate

theorem VPlus_bounds (u t : Fin p.T) (z : SourceInput p) :
    0 ≤ VPlus rate rewards C_star C_h u t z ∧
      VPlus rate rewards C_star C_h u t z ≤
        4 * (p.m : ℝ) * Bcap rate ^ 2 := by
  by_cases hE : z ∈ E u t
  · have hsum := sum_thetaPlus_on_firstCell rate rewards C_star C_h u t z hE
    have hcap : 0 ≤ 2 * Bcap rate := mul_nonneg (by norm_num) (Bcap_nonneg rate)
    have hterms (a : Fin p.K) :
        thetaPlus rate rewards C_star C_h u t a z *
            (bPlus rate rewards C_star C_h u t a z) ^ 2 ≤
          thetaPlus rate rewards C_star C_h u t a z * (2 * Bcap rate) ^ 2 := by
      have hθ := thetaPlus_bounds rate rewards C_star C_h u t a z
      have hb := ReferenceFirstCollectionCurrentQueueReadout.bPlus_global_bounds
        rate rewards C_star C_h u t a z
      have hsq : (bPlus rate rewards C_star C_h u t a z) ^ 2 ≤
          (2 * Bcap rate) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hb.2)
          (add_nonneg hcap hb.1)]
      exact mul_le_mul_of_nonneg_left hsq hθ.1
    constructor
    · unfold VPlus
      apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (thetaPlus_bounds rate rewards C_star C_h u t a z).1
        (sq_nonneg _)
    · calc
        VPlus rate rewards C_star C_h u t z ≤
            ∑ a : Fin p.K,
              thetaPlus rate rewards C_star C_h u t a z *
                (2 * Bcap rate) ^ 2 := by
          unfold VPlus
          exact Finset.sum_le_sum (fun a ha => hterms a)
        _ = (∑ a : Fin p.K,
              thetaPlus rate rewards C_star C_h u t a z) *
              (2 * Bcap rate) ^ 2 := by rw [Finset.sum_mul]
        _ = 4 * (p.m : ℝ) * Bcap rate ^ 2 := by rw [hsum]; ring
  · have hθ (a : Fin p.K) :
        thetaPlus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaPlus, Set.indicator_of_notMem hE]
    constructor
    · simp [VPlus, hθ]
    · have hzero : VPlus rate rewards C_star C_h u t z = 0 := by
        simp [VPlus, hθ]
      rw [hzero]
      exact Vcap_nonneg rate

theorem weightedBacklog_bounds (u t : Fin p.T) (z : SourceInput p) :
    0 ≤ weightedBacklog rate rewards C_star C_h u t z ∧
      weightedBacklog rate rewards C_star C_h u t z ≤
        2 * (p.m : ℝ) * Bcap rate := by
  by_cases hE : z ∈ E u t
  · have hsum := sum_thetaMinus_on_firstCell rate rewards C_star C_h u t z hE
    have hterms (a : Fin p.K) :
        thetaMinus rate rewards C_star C_h u t a z *
            bMinus rate rewards C_star C_h u t a z ≤
          thetaMinus rate rewards C_star C_h u t a z * (2 * Bcap rate) := by
      exact mul_le_mul_of_nonneg_left
        (ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
          rate rewards C_star C_h u t a z).2
        (thetaMinus_bounds rate rewards C_star C_h u t a z).1
    constructor
    · unfold weightedBacklog
      apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (thetaMinus_bounds rate rewards C_star C_h u t a z).1
        (ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
          rate rewards C_star C_h u t a z).1
    · calc
        weightedBacklog rate rewards C_star C_h u t z ≤
            ∑ a : Fin p.K,
              thetaMinus rate rewards C_star C_h u t a z * (2 * Bcap rate) := by
          unfold weightedBacklog
          exact Finset.sum_le_sum (fun a ha => hterms a)
        _ = (∑ a : Fin p.K,
              thetaMinus rate rewards C_star C_h u t a z) * (2 * Bcap rate) :=
          by rw [← Finset.sum_mul]
        _ = 2 * (p.m : ℝ) * Bcap rate := by rw [hsum]; ring
  · have hθ (a : Fin p.K) :
        thetaMinus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaMinus, Set.indicator_of_notMem hE]
    constructor
    · simp [weightedBacklog, hθ]
    · have hzero : weightedBacklog rate rewards C_star C_h u t z = 0 := by
        simp [weightedBacklog, hθ]
      rw [hzero]
      exact backlogCap_nonneg rate

private theorem reflected_square_increment (b A : ℝ) (hA : 0 ≤ A) :
    (max (b + A - 4) 0) ^ 2 - b ^ 2 ≤
      2 * b * (A - 4) + A ^ 2 + 16 := by
  by_cases h : b + A - 4 ≤ 0
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (b + A - 4), hA]
  · have hx : 0 ≤ b + A - 4 := le_of_not_ge h
    rw [max_eq_left hx]
    nlinarith [sq_nonneg (b + A - 4)]

/-- On the retained gate, the reflected queue transition gives the first
source square inequality, including the exact four-unit service. -/
theorem source_square_increment_on_G (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) (hG : z ∈ G u t) :
    (bPlus rate rewards C_star C_h u t a z) ^ 2 -
        (bMinus rate rewards C_star C_h u t a z) ^ 2 ≤
      2 * bMinus rate rewards C_star C_h u t a z *
          (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z - 4) +
        (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t a z) ^ 2 + 16 := by
  let A := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
    rate rewards C_star C_h u t a z
  have hA := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
    rate rewards C_star C_h u t a z
  have hx : x rate rewards C_star C_h u t a z = A - 4 := by
    rw [ReferenceFirstCollectionCurrentQueueReadout.x_eq_retainedRaw_sub_service]
    simp [A, Set.indicator_of_mem hG]
  rw [ReferenceFirstCollectionCurrentQueueReadout.bPlus_reflected_transition,
    hx]
  have hshift : bMinus rate rewards C_star C_h u t a z + (A - 4) =
      bMinus rate rewards C_star C_h u t a z + A - 4 := by ring
  rw [hshift]
  exact reflected_square_increment
    (bMinus rate rewards C_star C_h u t a z) A hA.1

/-- The reflected post-queue square is controlled by the incoming backlog
and the retained arrival on the retained gate. -/
theorem source_square_post_bound_on_G (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) (hG : z ∈ G u t) :
    (bPlus rate rewards C_star C_h u t a z) ^ 2 ≤
      2 * Bcap rate *
        (bMinus rate rewards C_star C_h u t a z +
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z) := by
  let A := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
    rate rewards C_star C_h u t a z
  have hA := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
    rate rewards C_star C_h u t a z
  have hx : x rate rewards C_star C_h u t a z = A - 4 := by
    rw [ReferenceFirstCollectionCurrentQueueReadout.x_eq_retainedRaw_sub_service]
    simp [A, Set.indicator_of_mem hG]
  have hbp := ReferenceFirstCollectionCurrentQueueReadout.bPlus_reflected_transition
    rate rewards C_star C_h u t a z
  have hbm := ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
    rate rewards C_star C_h u t a z
  have hbpGlobal := ReferenceFirstCollectionCurrentQueueReadout.bPlus_global_bounds
    rate rewards C_star C_h u t a z
  have hsum : 0 ≤ bMinus rate rewards C_star C_h u t a z + A :=
    add_nonneg hbm.1 hA.1
  have hupper : bPlus rate rewards C_star C_h u t a z ≤
      bMinus rate rewards C_star C_h u t a z + A := by
    rw [hbp, hx]
    apply max_le
    · linarith
    · exact hsum
  have hcap : 0 ≤ 2 * Bcap rate :=
    mul_nonneg (by norm_num) (Bcap_nonneg rate)
  calc
    (bPlus rate rewards C_star C_h u t a z) ^ 2 =
        bPlus rate rewards C_star C_h u t a z *
          bPlus rate rewards C_star C_h u t a z := by ring
    _ ≤ (2 * Bcap rate) *
          (bMinus rate rewards C_star C_h u t a z + A) :=
      mul_le_mul hbpGlobal.2 hupper hbpGlobal.1 hcap

private theorem source_square_drift_on_G (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) (hG : z ∈ G u t) :
    thetaPlus rate rewards C_star C_h u t a z *
        (bPlus rate rewards C_star C_h u t a z) ^ 2 -
      thetaMinus rate rewards C_star C_h u t a z *
        (bMinus rate rewards C_star C_h u t a z) ^ 2 ≤
      thetaMinus rate rewards C_star C_h u t a z *
        ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
          (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
            ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
              rate rewards C_star C_h u t a z +
          (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z) ^ 2 + 16) := by
  let A := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
    rate rewards C_star C_h u t a z
  let bm := bMinus rate rewards C_star C_h u t a z
  let bp := bPlus rate rewards C_star C_h u t a z
  let θm := thetaMinus rate rewards C_star C_h u t a z
  let θp := thetaPlus rate rewards C_star C_h u t a z
  have hE : z ∈ E u t := hG.1
  have hθ : θp ≤ (1 + 8 * rate.eta.val) * θm := by
    exact thetaPlus_le_one_add_eight_eta_mul_thetaMinus
      rate rewards C_star C_h u t z hE a
  have hθnonneg : 0 ≤ θm := (thetaMinus_bounds rate rewards C_star C_h u t a z).1
  have hinc := source_square_increment_on_G rate rewards C_star C_h u t a z hG
  have hpost := source_square_post_bound_on_G rate rewards C_star C_h u t a z hG
  have hη : 0 ≤ 8 * rate.eta.val := by positivity [rate.eta.property]
  have hcredit : 16 * rate.eta.val * Bcap rate = 1 / 2 := by
    rw [Bcap]
    field_simp [ne_of_gt rate.eta.property]
    norm_num
  have hcredit' : 8 * rate.eta.val * (2 * Bcap rate) = 1 / 2 := by
    nlinarith [hcredit]
  change θp * bp ^ 2 - θm * bm ^ 2 ≤
    θm * ((-15 / 2 : ℝ) * bm + (2 * bm + 1 / 2) * A + A ^ 2 + 16)
  calc
    θp * bp ^ 2 - θm * bm ^ 2 ≤
        ((1 + 8 * rate.eta.val) * θm) * bp ^ 2 - θm * bm ^ 2 := by
          exact sub_le_sub_right
            (mul_le_mul_of_nonneg_right hθ (sq_nonneg bp)) _
    _ = θm * ((bp ^ 2 - bm ^ 2) + 8 * rate.eta.val * bp ^ 2) := by ring
    _ ≤ θm * ((2 * bm * (A - 4) + A ^ 2 + 16) +
          8 * rate.eta.val * (2 * Bcap rate * (bm + A))) := by
            apply mul_le_mul_of_nonneg_left _ hθnonneg
            exact add_le_add hinc (mul_le_mul_of_nonneg_left hpost hη)
    _ = θm * ((-15 / 2 : ℝ) * bm + (2 * bm + 1 / 2) * A + A ^ 2 + 16) := by
          calc
            _ = θm * (2 * bm * (A - 4) + A ^ 2 + 16 +
                  (8 * rate.eta.val * (2 * Bcap rate)) * (bm + A)) := by ring
            _ = _ := by rw [hcredit']; ring

/-- Whole-space deterministic drift: the actual energy difference is
dominated by the retained-gate reduced envelope. -/
theorem V_drift_le_reducedDriftEnvelope (_control0 : TimeControl p)
    (u t : Fin p.T) (z : SourceInput p) :
    VPlus rate rewards C_star C_h u t z -
        VMinus rate rewards C_star C_h u t z ≤
      reducedDriftEnvelope rate rewards C_star C_h u t z := by
  by_cases hE : z ∈ E u t
  · by_cases hG : z ∈ G u t
    · have hsum :
        (∑ a : Fin p.K,
            thetaPlus rate rewards C_star C_h u t a z *
              (bPlus rate rewards C_star C_h u t a z) ^ 2) -
          (∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z *
              (bMinus rate rewards C_star C_h u t a z) ^ 2) ≤
          ∑ a : Fin p.K,
            thetaMinus rate rewards C_star C_h u t a z *
              ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
                (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
                  ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
                    rate rewards C_star C_h u t a z +
                (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
                  rate rewards C_star C_h u t a z) ^ 2 + 16) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_le_sum fun a ha =>
            source_square_drift_on_G rate rewards C_star C_h u t a z hG
      simpa [VPlus, VMinus, reducedDriftEnvelope, thetaPlus, thetaMinus,
        Set.indicator_of_mem hE, Set.indicator_of_mem hG] using hsum
    · have hnotH : z ∉ ReferenceFirstCollectionCurrentRetainedGate.H
          rate rewards C_star C_h t := by
        intro hzH
        exact hG ⟨hE, hzH⟩
      have htheta (a : Fin p.K) :
          thetaPlus rate rewards C_star C_h u t a z =
            thetaMinus rate rewards C_star C_h u t a z := by
        obtain ⟨L, c, hL, _, _, _, _, hθm, hθp⟩ :=
          firstCell_actual_score_marginals rate rewards C_star C_h u t z hE
        have hprefix : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
            rate rewards C_star C_h t z =
            some (stateReadout (RecordedQueueRun.run q L)) := by
          simp [ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL]
        have hoverflow : (RecordedQueueRun.run q L).overflow = true := by
          cases hs : (RecordedQueueRun.run q L).overflow with
          | false =>
              exact False.elim (hnotH ⟨_, hprefix, hs⟩)
          | true => rfl
        have hpres (i : Fin p.K) := RecordedQueueRun.step_after_overflow_preserves
          q (RecordedQueueRun.run q L) c hoverflow i
        have hweight : RecordedQueueRun.scoreWeight q
            (RecordedQueueRun.step q (RecordedQueueRun.run q L) c) =
          RecordedQueueRun.scoreWeight q (RecordedQueueRun.run q L) := by
          funext i
          unfold RecordedQueueRun.scoreWeight
          rw [(hpres i).1]
        have hθpa := congrFun hθp a
        have hθma := congrFun hθm a
        rw [hθpa, hθma, hweight]
      have hbp : (fun a => bPlus rate rewards C_star C_h u t a z) =
          (fun a => bMinus rate rewards C_star C_h u t a z) := by
        funext a
        have hAzero : ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z = 0 := by
          simp [ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw,
            Set.indicator_of_notMem hG]
        have hx : x rate rewards C_star C_h u t a z = 0 := by
          rw [ReferenceFirstCollectionCurrentQueueReadout.x_eq_retainedRaw_sub_service]
          rw [hAzero]
          simp [Set.indicator_of_notMem hG]
        rw [ReferenceFirstCollectionCurrentQueueReadout.bPlus_reflected_transition, hx]
        simpa only [add_zero] using max_eq_left
          (ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
            rate rewards C_star C_h u t a z).1
      have henergy : VPlus rate rewards C_star C_h u t z =
          VMinus rate rewards C_star C_h u t z := by
        unfold VPlus VMinus
        apply Finset.sum_congr rfl
        intro a ha
        rw [htheta a, congrFun hbp a]
      have hzero : reducedDriftEnvelope rate rewards C_star C_h u t z = 0 := by
        simp [reducedDriftEnvelope, Set.indicator_of_notMem hG]
      rw [henergy, hzero]
      norm_num
  · have hnotG : z ∉ G u t := by
      intro hz
      exact hE hz.1
    have hθm (a : Fin p.K) : thetaMinus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaMinus, Set.indicator_of_notMem hE]
    have hθp (a : Fin p.K) : thetaPlus rate rewards C_star C_h u t a z = 0 := by
      simp [thetaPlus, Set.indicator_of_notMem hE]
    have hvm : VMinus rate rewards C_star C_h u t z = 0 := by
      simp [VMinus, hθm]
    have hvp : VPlus rate rewards C_star C_h u t z = 0 := by
      simp [VPlus, hθp]
    have henv : reducedDriftEnvelope rate rewards C_star C_h u t z = 0 := by
      simp [reducedDriftEnvelope, Set.indicator_of_notMem hnotG]
    rw [hvm, hvp, henv]
    norm_num

private theorem integrable_of_bounded_measurable
    {f : SourceInput p → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f (sourceInputLaw p) := by
  have hconst : Integrable (fun _ : SourceInput p => C) (sourceInputLaw p) :=
    integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  have hAbs : |C| = C := abs_of_nonneg hC
  filter_upwards [] with z
  simpa [Real.norm_eq_abs, hAbs] using hbound z

private theorem integrable_product_nonneg_bounded
    {f g : SourceInput p → ℝ} (hf : Measurable f) (hg : Measurable g)
    (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf0 : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ Cf)
    (hg0 : ∀ z, 0 ≤ g z) (hgb : ∀ z, g z ≤ Cg) :
    Integrable (fun z => f z * g z) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable (hf.mul hg) (Cf * Cg)
    (mul_nonneg hCf hCg)
  intro z
  change ‖f z * g z‖ ≤ Cf * Cg
  rw [Real.norm_of_nonneg (mul_nonneg (hf0 z) (hg0 z))]
  exact mul_le_mul (hfb z) (hgb z) (hg0 z) hCf

private theorem measurable_VMinus_ambient (control0 : TimeControl p)
    (u t : Fin p.T) : Measurable (VMinus rate rewards C_star C_h u t) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono
    (measurable_VMinus rate rewards C_star C_h control0 u t) hle le_rfl

private theorem measurable_weightedBacklog_ambient (control0 : TimeControl p)
    (u t : Fin p.T) : Measurable (weightedBacklog rate rewards C_star C_h u t) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact Measurable.mono
    (measurable_weightedBacklog rate rewards C_star C_h control0 u t) hle le_rfl

/-- Incoming score marginals are integrable by their actual probability bounds. -/
theorem thetaMinus_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (thetaMinus rate rewards C_star C_h u t a) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (measurable_thetaMinus_ambient rate rewards C_star C_h control0 u t a) 1
    (by norm_num)
  intro z
  have h := thetaMinus_bounds rate rewards C_star C_h u t a z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- Outgoing score marginals are ambiently integrable under the original law. -/
theorem thetaPlus_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (thetaPlus rate rewards C_star C_h u t a) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (measurable_thetaPlus rate rewards C_star C_h control0 u t a) 1
    (by norm_num)
  intro z
  have h := thetaPlus_bounds rate rewards C_star C_h u t a z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- The incoming quadratic energy is integrable by the stopped queue envelope. -/
theorem VMinus_integrable (control0 : TimeControl p) (u t : Fin p.T) :
    Integrable (VMinus rate rewards C_star C_h u t) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (measurable_VMinus_ambient rate rewards C_star C_h control0 u t)
    (4 * (p.m : ℝ) * Bcap rate ^ 2) (Vcap_nonneg rate)
  intro z
  have h := VMinus_bounds rate rewards C_star C_h u t z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- The outgoing quadratic energy is integrable by the reflected queue envelope. -/
theorem VPlus_integrable (control0 : TimeControl p) (u t : Fin p.T) :
    Integrable (VPlus rate rewards C_star C_h u t) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (measurable_VPlus rate rewards C_star C_h control0 u t)
    (4 * (p.m : ℝ) * Bcap rate ^ 2) (Vcap_nonneg rate)
  intro z
  have h := VPlus_bounds rate rewards C_star C_h u t z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

/-- The energy difference needed by conditional expectation is integrable. -/
theorem energyDifference_integrable (control0 : TimeControl p)
    (u t : Fin p.T) :
    Integrable (fun z => VPlus rate rewards C_star C_h u t z -
      VMinus rate rewards C_star C_h u t z) (sourceInputLaw p) := by
  have hm := (measurable_VPlus rate rewards C_star C_h control0 u t).sub
    (measurable_VMinus_ambient rate rewards C_star C_h control0 u t)
  apply integrable_of_bounded_measurable hm
    (4 * (p.m : ℝ) * Bcap rate ^ 2) (Vcap_nonneg rate)
  intro z
  have hp := VPlus_bounds rate rewards C_star C_h u t z
  have hm := VMinus_bounds rate rewards C_star C_h u t z
  have hC := Vcap_nonneg rate
  change ‖VPlus rate rewards C_star C_h u t z -
      VMinus rate rewards C_star C_h u t z‖ ≤
    4 * (p.m : ℝ) * Bcap rate ^ 2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2, hC]

/-- The incoming weighted backlog is integrable under the original source law. -/
theorem weightedBacklog_integrable (control0 : TimeControl p)
    (u t : Fin p.T) :
    Integrable (weightedBacklog rate rewards C_star C_h u t) (sourceInputLaw p) := by
  apply integrable_of_bounded_measurable
    (measurable_weightedBacklog_ambient rate rewards C_star C_h control0 u t)
    (2 * (p.m : ℝ) * Bcap rate) (backlogCap_nonneg rate)
  intro z
  have h := weightedBacklog_bounds rate rewards C_star C_h u t z
  rw [Real.norm_of_nonneg h.1]
  exact h.2

private theorem rawCap_nonneg :
    0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
  positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]

/-- The square retained raw input needed by the next source-law CE step is
integrable by the source retained-moment bound. -/
theorem retainedRaw_sq_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z =>
      (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z) ^ 2) (sourceInputLaw p) := by
  have hA := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
    rate rewards C_star C_h u t a
  have hm := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_sq_measurable
    rate rewards C_star C_h control0 u t a
  have hcap : 0 ≤ (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 :=
    sq_nonneg _
  apply integrable_of_bounded_measurable hm
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2) hcap
  intro z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [hA z]

/-- The incoming marginal times a retained arrival is integrable. -/
theorem thetaMinus_mul_retainedRaw_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => thetaMinus rate rewards C_star C_h u t a z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z) (sourceInputLaw p) := by
  have hθ z := thetaMinus_bounds rate rewards C_star C_h u t a z
  have hA z := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
    rate rewards C_star C_h u t a z
  exact integrable_product_nonneg_bounded
    (measurable_thetaMinus_ambient rate rewards C_star C_h control0 u t a)
    (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
      rate rewards C_star C_h control0 u t a)
    1 (1 / CanonicalRecordingRates.beta p rate.eta.val) (by norm_num)
    (rawCap_nonneg rate) (fun z => (hθ z).1) (fun z => (hθ z).2)
    (fun z => (hA z).1) (fun z => (hA z).2)

/-- The marginal times the retained raw square is integrable. -/
theorem thetaMinus_mul_retainedRaw_sq_integrable
    (control0 : TimeControl p) (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => thetaMinus rate rewards C_star C_h u t a z *
      (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z) ^ 2) (sourceInputLaw p) := by
  have hθ z := thetaMinus_bounds rate rewards C_star C_h u t a z
  have hA z := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
    rate rewards C_star C_h u t a z
  have hsq : Measurable (fun z : SourceInput p =>
      (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z) ^ 2) :=
    (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
      rate rewards C_star C_h control0 u t a).pow_const 2
  exact integrable_product_nonneg_bounded
    (measurable_thetaMinus_ambient rate rewards C_star C_h control0 u t a)
    hsq 1 ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2)
    (by norm_num) (sq_nonneg _) (fun z => (hθ z).1) (fun z => (hθ z).2)
    (fun z => sq_nonneg _) (fun z => by nlinarith [hA z])

/-- The marginal times incoming backlog is integrable. -/
theorem thetaMinus_mul_bMinus_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z => thetaMinus rate rewards C_star C_h u t a z *
      bMinus rate rewards C_star C_h u t a z) (sourceInputLaw p) := by
  have hθ z := thetaMinus_bounds rate rewards C_star C_h u t a z
  have hb z := ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
    rate rewards C_star C_h u t a z
  exact integrable_product_nonneg_bounded
    (measurable_thetaMinus_ambient rate rewards C_star C_h control0 u t a)
    (ReferenceFirstCollectionCurrentQueueReadout.bMinus_measurable_ambient
      rate rewards C_star C_h control0 u t a)
    1 (2 * Bcap rate) (by norm_num) (mul_nonneg (by norm_num) (Bcap_nonneg rate))
    (fun z => (hθ z).1) (fun z => (hθ z).2)
    (fun z => (hb z).1) (fun z => (hb z).2)

private theorem thetaMinus_mul_bMinus_nonneg_bound
    (u t : Fin p.T) (a : Fin p.K) :
    (∀ z, 0 ≤ thetaMinus rate rewards C_star C_h u t a z *
      bMinus rate rewards C_star C_h u t a z) ∧
    (∀ z, thetaMinus rate rewards C_star C_h u t a z *
      bMinus rate rewards C_star C_h u t a z ≤ 2 * Bcap rate) := by
  constructor
  · intro z
    exact mul_nonneg (thetaMinus_bounds rate rewards C_star C_h u t a z).1
      (ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
        rate rewards C_star C_h u t a z).1
  · intro z
    calc
      thetaMinus rate rewards C_star C_h u t a z *
          bMinus rate rewards C_star C_h u t a z ≤
        1 * (2 * Bcap rate) := mul_le_mul
          (thetaMinus_bounds rate rewards C_star C_h u t a z).2
          (ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
            rate rewards C_star C_h u t a z).2
          (ReferenceFirstCollectionCurrentQueueReadout.bMinus_global_bounds
            rate rewards C_star C_h u t a z).1 (by norm_num)
      _ = 2 * Bcap rate := by ring

/-- The marginal, backlog and retained input product in the reduced drift is
integrable under the original source law. -/
theorem thetaMinus_mul_bMinus_mul_retainedRaw_integrable
    (control0 : TimeControl p) (u t : Fin p.T) (a : Fin p.K) :
    Integrable (fun z =>
      (thetaMinus rate rewards C_star C_h u t a z *
        bMinus rate rewards C_star C_h u t a z) *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z) (sourceInputLaw p) := by
  have hθb := thetaMinus_mul_bMinus_nonneg_bound rate rewards C_star C_h u t a
  exact integrable_product_nonneg_bounded
    ((measurable_thetaMinus_ambient rate rewards C_star C_h control0 u t a).mul
      (ReferenceFirstCollectionCurrentQueueReadout.bMinus_measurable_ambient
        rate rewards C_star C_h control0 u t a))
    (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_measurable
      rate rewards C_star C_h control0 u t a)
    (2 * Bcap rate) (1 / CanonicalRecordingRates.beta p rate.eta.val)
    (mul_nonneg (by norm_num) (Bcap_nonneg rate)) (rawCap_nonneg rate)
    hθb.1 hθb.2
    (fun z => (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
      rate rewards C_star C_h u t a z).1)
    (fun z => (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_bounds
      rate rewards C_star C_h u t a z).2)

private theorem measurableSet_G_ambient (control0 : TimeControl p)
    (u t : Fin p.T) : MeasurableSet (G u t) := by
  have hle : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le' (t.val + 1)
  exact hle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
    rate rewards C_star C_h control0 u t)

private def reducedUnmaskedTerm (u t : Fin p.T) (a : Fin p.K)
    (z : SourceInput p) : ℝ :=
  thetaMinus rate rewards C_star C_h u t a z *
    ((-15 / 2 : ℝ) * bMinus rate rewards C_star C_h u t a z +
      (2 * bMinus rate rewards C_star C_h u t a z + 1 / 2) *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
          rate rewards C_star C_h u t a z +
      (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t a z) ^ 2 + 16)

/-- Each localized per-arm reduced drift term is integrable, using only the
actual queue and retained raw envelopes. -/
theorem reducedDriftTerm_integrable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Fin p.K) :
    Integrable (reducedDriftTerm rate rewards C_star C_h u t a)
      (sourceInputLaw p) := by
  have hθb := thetaMinus_mul_bMinus_integrable rate rewards C_star C_h control0 u t a
  have hθA := thetaMinus_mul_retainedRaw_integrable rate rewards C_star C_h control0 u t a
  have hθA2 := thetaMinus_mul_retainedRaw_sq_integrable
    rate rewards C_star C_h control0 u t a
  have hθbA := thetaMinus_mul_bMinus_mul_retainedRaw_integrable
    rate rewards C_star C_h control0 u t a
  have hθ := thetaMinus_integrable rate rewards C_star C_h control0 u t a
  have hsum1 := (hθb.const_mul (-(15 / 2 : ℝ))).add (hθbA.const_mul (2 : ℝ))
  have hsum2 := hsum1.add (hθA.const_mul (1 / 2 : ℝ))
  have hsum3 := hsum2.add hθA2
  have hsum := hsum3.add (hθ.const_mul (16 : ℝ))
  have heq : reducedUnmaskedTerm rate rewards C_star C_h u t a =
      fun z => (-(15 / 2 : ℝ)) *
          (thetaMinus rate rewards C_star C_h u t a z *
            bMinus rate rewards C_star C_h u t a z) +
        2 * ((thetaMinus rate rewards C_star C_h u t a z *
            bMinus rate rewards C_star C_h u t a z) *
          ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z) +
        (1 / 2 : ℝ) *
          (thetaMinus rate rewards C_star C_h u t a z *
            ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
              rate rewards C_star C_h u t a z) +
        thetaMinus rate rewards C_star C_h u t a z *
          (ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
            rate rewards C_star C_h u t a z) ^ 2 +
        16 * thetaMinus rate rewards C_star C_h u t a z := by
    funext z
    unfold reducedUnmaskedTerm
    ring
  have hbase : Integrable (reducedUnmaskedTerm rate rewards C_star C_h u t a)
      (sourceInputLaw p) := by
    rw [heq]
    exact hsum
  have hG := measurableSet_G_ambient rate rewards C_star C_h control0 u t
  change Integrable ((G u t).indicator
    (reducedUnmaskedTerm rate rewards C_star C_h u t a))
    (sourceInputLaw p)
  exact hbase.indicator hG

/-- The deterministic envelope is the finite sum of its integrable arm terms. -/
theorem reducedDriftEnvelope_eq_sum_reducedDriftTerm (u t : Fin p.T)
    (z : SourceInput p) :
    reducedDriftEnvelope rate rewards C_star C_h u t z =
      ∑ a : Fin p.K, reducedDriftTerm rate rewards C_star C_h u t a z := by
  by_cases hz : z ∈ G u t
  · simp [reducedDriftEnvelope, reducedDriftTerm, Set.indicator_of_mem hz]
  · simp [reducedDriftEnvelope, reducedDriftTerm, Set.indicator_of_notMem hz]

/-- The whole-space reduced drift envelope is integrable. -/
theorem reducedDriftEnvelope_integrable (control0 : TimeControl p)
    (u t : Fin p.T) :
    Integrable (reducedDriftEnvelope rate rewards C_star C_h u t)
      (sourceInputLaw p) := by
  have heq : reducedDriftEnvelope rate rewards C_star C_h u t =
      fun z => ∑ a : Fin p.K, reducedDriftTerm rate rewards C_star C_h u t a z := by
    funext z
    exact reducedDriftEnvelope_eq_sum_reducedDriftTerm rate rewards C_star C_h u t z
  rw [heq]
  exact integrable_finsetSum Finset.univ (fun a ha =>
    reducedDriftTerm_integrable rate rewards C_star C_h control0 u t a)

end Bandits.Support.ReferenceFirstCollectionCurrentQueueEnergy

end
