/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceExponentialStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Tactic

/-!
# Whole-marker weighted queue-energy drift on the first-renewal source

The scalar energy observations below read the registers of the existing
incoming state and the existing whole-cell stopped-queue update. The current
cell is appended to the original past list, with all registers and overflow
information retained.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Source {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalWholeSourceExponentialStep.Source
    rate rewards C_star C_h u t
abbrev Readout (p : Parameters) :=
  ReferenceFirstCollectionRenewalSourceConditionalExponential.Readout p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : TimeControl p)

local notation "Z" => Source rate rewards C_star C_h u t
local notation "B" =>
  ReferenceFirstCollectionRenewalWholeSourceExponentialStep.Pair
    rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t
local notation "G" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap
  (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0)
  (inferInstance : MeasurableSpace
    (ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates p))
local notation "nu" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "ER" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
    rate rewards C_star C_h u t
local notation "F_ER" =>
  ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER
    rate rewards C_star C_h u t
local notation "wholePost" =>
  ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
    rate rewards C_star C_h u t
local notation "incoming" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t
local notation "qp" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "theta" =>
  ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
    rate rewards C_star C_h u t control0
local notation "backlog" =>
  ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
    rate rewards C_star C_h u t control0
local notation "fullA" =>
  ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.fullAcceptedA
    rate rewards C_star C_h u t

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalBaseMeasurableSpace :
    MeasurableSpace
      (ReferenceFirstCollectionRenewalControlFactor.RenewalBase
        rate rewards C_star C_h u t) := by
  change MeasurableSpace
    (ReferenceFirstCollectionRenewalControlFactor.Source
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalControlFactor.AuxiliaryArray p)
  infer_instance

local instance sourceLawIsFinite : IsFiniteMeasure nu :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite
    rate rewards C_star C_h u t

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

local instance retainedFieldSigmaFinite : SigmaFinite ((mu).trim
    (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
      rate rewards C_star C_h u t control0)) :=
  ReferenceFirstCollectionRenewalComplementMoments.retainedField_trim_sigmaFinite
    rate rewards C_star C_h u t control0

/-- The incoming integer queue registers read from the original renewal
source's existing incoming readout. -/
def Aminus (z : Z) : Fin p.K → ℕ × ℕ := (ER z).1

/-- The integer queue registers after the actual whole-marker cell has been
appended to the original past queue run. -/
def Aplus (z : Z) : Fin p.K → ℕ × ℕ := (wholePost z).1

/-- Incoming product-set inclusion masses, computed from the original
incoming score registers. -/
def thetaMinus (j : Fin p.K) (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
    rate j (Aminus rate rewards C_star C_h u t z)

/-- Incoming normalized backlogs, computed from the original incoming
backlog registers. -/
def bMinus (j : Fin p.K) (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
    rate j (Aminus rate rewards C_star C_h u t z)

/-- The incoming weighted quadratic energy on the original source. -/
def Vminus (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
    rate (Aminus rate rewards C_star C_h u t z)

/-- The weighted quadratic energy after the same-run whole-marker update. -/
def VwholePlus (z : Z) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
    rate (Aplus rate rewards C_star C_h u t z)

/-- Incoming weighted backlog, retaining the same incoming weights used by
the quadratic energy. -/
def Bminus (z : Z) : ℝ :=
  ∑ j : Fin p.K, thetaMinus rate rewards C_star C_h u t j z *
    bMinus rate rewards C_star C_h u t j z

/-- The exact event that the original incoming readout has not overflowed. -/
def E : Set Z := {z | (ER z).2.1 = false}

/-- The incoming scalar observations are precisely the existing original
incoming run's queue registers. -/
theorem Aminus_eq_incomingRegisters (z : Z) :
    Aminus rate rewards C_star C_h u t z = (incoming z).registers := rfl

/-- Membership in `E` is exactly the incoming run's pre-update clear flag. -/
theorem mem_E_iff_noIncomingOverflow (z : Z) :
    z ∈ E rate rewards C_star C_h u t ↔ (incoming z).overflow = false := Iff.rfl

/-- The whole post registers are precisely those of the run with the actual
whole current cell appended to the original past cells. -/
theorem Aplus_eq_appendedWholeRunRegisters (z : Z) :
    Aplus rate rewards C_star C_h u t z =
      (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
          rate rewards C_star C_h u t z ++
          [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
            rate rewards C_star C_h u t z])).registers := by
  change (wholePost z).1 = _
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_fullPrefix]
  rfl

/-- The incoming energy uses exactly the existing incoming registers. -/
theorem Vminus_eq_energyFromIncoming (z : Z) :
    Vminus rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate ((ER z).1) := rfl

/-- The post energy uses exactly the existing same-run whole-post registers. -/
theorem VwholePlus_eq_energyFromWholePost (z : Z) :
    VwholePlus rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate ((wholePost z).1) := rfl

private theorem integral_source_eq_pair (f : Z → ℝ) (hf : Measurable f) :
    (∫ z : Z, f z ∂nu) =
      ∫ b : ReferenceFirstCollectionRenewalWholeSourceExponentialStep.Pair
        rate rewards C_star C_h u t, f b.2 ∂
          ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
            rate rewards C_star C_h u t := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]

private theorem integrable_of_norm_le_const {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ᵐ z ∂μ, ‖f z‖ ≤ C) : Integrable f μ := by
  have hconst : Integrable (fun _ : α => C) μ := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [hbound] with z hz
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hz

/-- The incoming registers and their literal scalar queue observations are
Borel on the existing renewal source. -/
theorem measurable_Aminus : Measurable (Aminus rate rewards C_star C_h u t) :=
  measurable_fst.comp
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)

/-- The whole post-register observation is Borel on the existing renewal
source. -/
theorem measurable_Aplus : Measurable (Aplus rate rewards C_star C_h u t) :=
  measurable_fst.comp
    (ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholePostReadout
      rate rewards C_star C_h u t)

/-- Incoming weighted backlog is Borel. -/
theorem measurable_Bminus : Measurable (Bminus rate rewards C_star C_h u t) := by
  change Measurable (fun z : Z =>
    ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j (Aminus rate rewards C_star C_h u t z) *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
        rate j (Aminus rate rewards C_star C_h u t z))
  exact Finset.measurable_fun_sum Finset.univ fun j _ =>
    ((measurable_of_countable
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j)).comp
      (measurable_Aminus rate rewards C_star C_h u t)).mul
    ((measurable_of_countable
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j)).comp
      (measurable_Aminus rate rewards C_star C_h u t))

/-- Incoming energy is Borel. -/
theorem measurable_Vminus : Measurable (Vminus rate rewards C_star C_h u t) :=
  (measurable_of_countable
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate)).comp
    (measurable_Aminus rate rewards C_star C_h u t)

/-- Whole post energy is Borel. -/
theorem measurable_VwholePlus : Measurable (VwholePlus rate rewards C_star C_h u t) :=
  (measurable_of_countable
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate)).comp
    (measurable_Aplus rate rewards C_star C_h u t)

private theorem thetaFromRegisters_bounds (registers : Fin p.K → ℕ × ℕ)
    (j : Fin p.K) :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j registers ∧
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j registers ≤ 1 := by
  let w := fun i : Fin p.K =>
    ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
      rate i registers
  have hwpos : ∀ i, 0 < w i := by
    intro i
    dsimp [w, ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters]
    exact ScoreWeights.scoreWeight_pos
      (ScoreWeights.sourceBase_pos
        (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _
  constructor
  · exact (ProductSetLaw.theta_pos w j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hwpos).le
  · exact (ProductSetLaw.theta_lt_one w j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hwpos).le

private theorem sum_thetaFromRegisters (registers : Fin p.K → ℕ × ℕ) :
    (∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j registers) = (p.m : ℝ) := by
  apply ProductSetLaw.sum_theta_eq_card
  · exact Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)
  · exact p.m_lt_K
  · intro j
    change 0 < ScoreWeights.scoreWeight
      (1 + 1 / (ConstructorDimensions.D p : ℝ)) (registers j).1
    exact ScoreWeights.scoreWeight_pos
      (ScoreWeights.sourceBase_pos
        (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _

private theorem pairVwholePlus_bounds :
    ∀ᵐ b : B ∂mu,
      0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
          rate (wholePost b.2).1 ∧
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
          rate (wholePost b.2).1 ≤
            (p.m : ℝ) *
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0) ^ 2 := by
  have hback (j : Fin p.K) :=
    ReferenceFirstCollectionRenewalWholeExponentialQueueStep.ae_fullPostBacklog_bounds
      rate rewards C_star C_h u t control0 j
  have hbackAll : ∀ᵐ b : B ∂mu, ∀ j : Fin p.K,
      0 ≤ ((((wholePost b.2).1 j).2 : ℝ) / (rate.n : ℝ)) ∧
        ((((wholePost b.2).1 j).2 : ℝ) / (rate.n : ℝ)) ≤
          2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 := by
    rw [ae_all_iff]
    exact hback
  filter_upwards [hbackAll] with b hb
  have hcap : 0 ≤ 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0 := by
    unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
    have hden : 0 < (32 : ℝ) * rate.eta.val :=
      mul_pos (by norm_num) rate.eta.property
    have hrecip : 0 < 1 / ((32 : ℝ) * rate.eta.val) := one_div_pos.mpr hden
    nlinarith
  constructor
  · unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
    exact Finset.sum_nonneg fun j hj => mul_nonneg
      (thetaFromRegisters_bounds rate (wholePost b.2).1 j).1
      (sq_nonneg _)
  · unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
    calc
      _ ≤ ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
            rate j (wholePost b.2).1 *
            (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have ht := thetaFromRegisters_bounds rate (wholePost b.2).1 j
        have hq := (hb j).2
        have hsq :
            ((((wholePost b.2).1 j).2 : ℝ) / (rate.n : ℝ)) ^ 2 ≤
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hq)
            (add_nonneg hcap ((hb j).1))]
        exact mul_le_mul_of_nonneg_left hsq ht.1
      _ = (p.m : ℝ) *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0) ^ 2 := by
        rw [← Finset.sum_mul, sum_thetaFromRegisters]

theorem integrable_VwholePlus (control0 : TimeControl p) :
    Integrable (VwholePlus rate rewards C_star C_h u t) nu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  have hcomp : Integrable
      ((VwholePlus rate rewards C_star C_h u t) ∘ Prod.snd) mu := by
    change Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate (wholePost b.2).1) mu
    exact integrable_of_norm_le_const
      ((measurable_of_countable
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate)).comp
        (measurable_fst.comp
          ((ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholePostReadout
            rate rewards C_star C_h u t).comp measurable_snd)))
      ((p.m : ℝ) *
        (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0) ^ 2)
      (by positivity)
      (pairVwholePlus_bounds rate rewards C_star C_h u t control0 |>.mono fun b hb => by
        rw [Real.norm_of_nonneg hb.1]
        exact hb.2)
  exact (integrable_map_measure
    (measurable_VwholePlus rate rewards C_star C_h u t).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hcomp

theorem integrable_Vminus (control0 : TimeControl p) :
    Integrable (Vminus rate rewards C_star C_h u t) nu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  have hcomp : Integrable ((Vminus rate rewards C_star C_h u t) ∘ Prod.snd) mu := by
    change Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
        rate rewards C_star C_h u t control0 b) mu
    exact ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_VMinus
      rate rewards C_star C_h u t control0
  exact (integrable_map_measure
    (measurable_Vminus rate rewards C_star C_h u t).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hcomp

theorem integrable_Bminus (control0 : TimeControl p) :
    Integrable (Bminus rate rewards C_star C_h u t) nu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t]
  have hcomp : Integrable ((Bminus rate rewards C_star C_h u t) ∘ Prod.snd) mu := by
    change Integrable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b) mu
    simpa only [← Finset.sum_apply] using
      (integrable_finsetSum (Finset.univ : Finset (Fin p.K))
        (fun j hj =>
          ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus
            rate rewards C_star C_h u t control0 j))
  exact (integrable_map_measure
    (measurable_Bminus rate rewards C_star C_h u t).aestronglyMeasurable
    measurable_snd.aemeasurable).mpr hcomp

theorem measurableSet_E : MeasurableSet (E rate rewards C_star C_h u t) := by
  have hflag : Measurable (fun z : Z => (ER z).2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
        rate rewards C_star C_h u t))
  exact hflag (MeasurableSet.singleton false)

theorem integrable_weightedCost (control0 : TimeControl p) :
    Integrable
      ((E rate rewards C_star C_h u t).indicator (fun z =>
        -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ))) nu := by
  have hraw : Integrable (fun z : Z =>
      -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) nu := by
    have h := (integrable_Bminus rate rewards C_star C_h u t control0).const_mul
      (-(11 / 2 : ℝ))
    have hc : Integrable (fun _ : Z =>
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) nu := integrable_const
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ))
    refine h.add hc |>.congr ?_
    filter_upwards [] with z
    simp only [Pi.add_apply]
    ring
  exact hraw.indicator (measurableSet_E rate rewards C_star C_h u t)

private def pairPostWeight (b : B) (j : Fin p.K) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
    rate j (wholePost b.2).1

private def pairPostTheta (b : B) (j : Fin p.K) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
    rate j (wholePost b.2).1

private def pairPostBacklog (b : B) (j : Fin p.K) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
    rate j (wholePost b.2).1

private theorem pairPostWeight_bounds (b : B) (j : Fin p.K) :
    ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b ≤
        pairPostWeight rate rewards C_star C_h u t b j ∧
      pairPostWeight rate rewards C_star C_h u t b j ≤ Real.exp (4 * rate.eta.val) *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
          rate rewards C_star C_h u t control0 j b := by
  let state := incoming b.2
  let cell := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
    rate rewards C_star C_h u t b.2
  have hpostRegs : (wholePost b.2).1 = (RecordedQueueRun.step qp state cell).registers := by
    rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_projections]
  have hafter : pairPostWeight rate rewards C_star C_h u t b j =
      RecordedQueueRun.scoreWeight qp
      (RecordedQueueRun.step qp state cell) j := by
    dsimp [pairPostWeight, ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters,
      RecordedQueueRun.scoreWeight, ScoreWeights.scoreWeight, state, cell]
    rw [congrArg (fun r : Fin p.K → ℕ × ℕ => (r j).1) hpostRegs]
  have hbefore :
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
          rate rewards C_star C_h u t control0 j b = RecordedQueueRun.scoreWeight qp state j := by
    rfl
  have hratio : pairPostWeight rate rewards C_star C_h u t b j /
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b =
      Real.exp (RecordedPotentialStep.potentialLambda qp *
        RecordedPotentialStep.servedEstimate qp state cell j) := by
    rw [hafter, hbefore]
    exact RecordedPotentialStep.step_scoreWeight_ratio_exp qp state cell j
  have hbeforePos : 0 <
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b := by
    rw [hbefore]
    exact RecordedPotentialStep.scoreWeight_pos qp state j
  have hservice := RecordedPotentialStep.servedEstimate_nonneg qp state cell j
  have hserviceLe := RecordedPotentialStep.servedEstimate_le_four qp state cell j
  have hlambdaPos := RecordedPotentialStep.potentialLambda_pos qp
  have hlambdaLe : RecordedPotentialStep.potentialLambda qp ≤ rate.eta.val := by
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using
      RecordedPotentialStep.potentialLambda_le_eta qp
  have hratioLow : 1 ≤ pairPostWeight rate rewards C_star C_h u t b j /
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b := by
    rw [hratio]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hlambdaPos.le hservice)
  have hratioHigh : pairPostWeight rate rewards C_star C_h u t b j /
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b ≤ Real.exp (4 * rate.eta.val) := by
    rw [hratio]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ RecordedPotentialStep.potentialLambda qp * 4 :=
        mul_le_mul_of_nonneg_left hserviceLe hlambdaPos.le
      _ ≤ rate.eta.val * 4 := mul_le_mul_of_nonneg_right hlambdaLe (by norm_num)
      _ = 4 * rate.eta.val := by ring
  constructor
  · simpa only [one_mul] using (le_div_iff₀ hbeforePos).mp hratioLow
  · exact (div_le_iff₀ hbeforePos).mp hratioHigh

private theorem pairPostRegisters_eq_incoming_of_overflow (b : B)
    (hoverflow : (incoming b.2).overflow = true) :
    (wholePost b.2).1 = (incoming b.2).registers := by
  let state := incoming b.2
  let cell := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
    rate rewards C_star C_h u t b.2
  change (wholePost b.2).1 = state.registers
  rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_projections]
  change (RecordedQueueRun.step qp state cell).registers = state.registers
  simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
    ReferenceFirstLaunchNumericalCell.queueParameters, QueueReplay.transition,
    state, hoverflow]

private theorem pairPostTheta_le_exp (b : B) (j : Fin p.K) :
    pairPostTheta rate rewards C_star C_h u t b j ≤
      Real.exp (4 * rate.eta.val) * theta j b := by
  let v := fun i : Fin p.K =>
    ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
      rate i (incoming b.2).registers
  let w := fun i : Fin p.K => pairPostWeight rate rewards C_star C_h u t b i
  let c := w j / v j
  let mid := Function.update w j (v j)
  have hvpos : ∀ i, 0 < v i := by
    intro i
    dsimp [v, ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters]
    exact ScoreWeights.scoreWeight_pos
      (ScoreWeights.sourceBase_pos
        (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _
  have hwpos : ∀ i, 0 < w i := by
    intro i
    dsimp [w, pairPostWeight,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters]
    exact ScoreWeights.scoreWeight_pos
      (ScoreWeights.sourceBase_pos
        (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _
  have hweights : ∀ i, v i ≤ w i ∧
      w i ≤ Real.exp (4 * rate.eta.val) * v i := by
    intro i
    have hbefore :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
            rate rewards C_star C_h u t control0 i b = v i := by
      rfl
    have hi := pairPostWeight_bounds rate rewards C_star C_h u t control0 b i
    rw [hbefore] at hi
    simpa [w, pairPostWeight] using hi
  have hc1 : 1 ≤ c := by
    rw [le_div_iff₀ (hvpos j)]
    simpa only [one_mul] using (hweights j).1
  have hc2 : c ≤ Real.exp (4 * rate.eta.val) := by
    rw [div_le_iff₀ (hvpos j)]
    exact (hweights j).2
  have hmidpos : ∀ i, 0 < mid i := by
    intro i
    by_cases hi : i = j
    · subst i
      simp [mid, hvpos]
    · simp [mid, hi, hwpos]
  have hmidown : v j = mid j := by simp [mid]
  have hmidother : ∀ i, i ≠ j → v i ≤ mid i := by
    intro i hij
    simpa [mid, hij] using (hweights i).1
  have hother := ProductMarginalStability.theta_antitone_of_other_coord_le
    v mid j p.two_le_m p.m_lt_K hvpos hmidpos hmidown hmidother
  have hownScale : c * v j = w j := by
    dsimp [c]
    field_simp [ne_of_gt (hvpos j)]
  have hupdate : Function.update mid j (c * v j) = w := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [hownScale, mid]
    · simp [Function.update, hi, mid]
  have hscaledRaw := ProductMarginalStability.theta_update_le
    mid j c (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      hmidpos hc1
  have hscaled : ProductSetLaw.theta p.m (Function.update mid j (c * v j)) j ≤
      c * ProductSetLaw.theta p.m mid j := by
    simpa only [hmidown] using hscaledRaw
  have htheta0 := thetaFromRegisters_bounds rate (incoming b.2).registers j
  calc
    pairPostTheta rate rewards C_star C_h u t b j = ProductSetLaw.theta p.m w j := by
      rfl
    _ = ProductSetLaw.theta p.m (Function.update mid j (c * v j)) j := by
      rw [← hupdate]
    _ ≤ c * ProductSetLaw.theta p.m mid j := hscaled
    _ ≤ c * ProductSetLaw.theta p.m v j :=
      mul_le_mul_of_nonneg_left hother (by positivity [hc1])
    _ ≤ Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v j :=
      mul_le_mul_of_nonneg_right hc2 htheta0.1
    _ = Real.exp (4 * rate.eta.val) * theta j b := by rfl

private theorem exp_four_eta_le_one_add :
    Real.exp (4 * rate.eta.val) ≤ 1 + 8 * rate.eta.val := by
  have heta0 : 0 ≤ rate.eta.val := le_of_lt rate.eta.property
  have hx0 : 0 ≤ 4 * rate.eta.val := mul_nonneg (by norm_num) heta0
  have hsmall := CanonicalQueueProcess.four_mul_eta_le_one p
    rate.eta.property rate.sourceCap
  have hexp := RecordedPotentialStep.exp_le_one_add_add_sq hx0 hsmall
  have hsquare : (4 * rate.eta.val) ^ 2 ≤ 4 * rate.eta.val := by
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 4 * rate.eta.val)]
  nlinarith

private theorem pairPostTheta_le_one_add (b : B) (j : Fin p.K) :
    pairPostTheta rate rewards C_star C_h u t b j ≤
      (1 + 8 * rate.eta.val) * theta j b := by
  calc
    pairPostTheta rate rewards C_star C_h u t b j ≤
        Real.exp (4 * rate.eta.val) * theta j b :=
      pairPostTheta_le_exp rate rewards C_star C_h u t control0 b j
    _ ≤ (1 + 8 * rate.eta.val) * theta j b :=
      mul_le_mul_of_nonneg_right
        (exp_four_eta_le_one_add rate)
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
          rate rewards C_star C_h u t control0 j b).1

/-- Every arm's actual whole-post product-set mass is bounded by the
incoming mass times the whole-step multiplicative stability factor. -/
theorem wholePostTheta_le_one_add (b : B) (j : Fin p.K) :
    ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j (wholePost b.2).1 ≤
      (1 + 8 * rate.eta.val) * theta j b := by
  exact pairPostTheta_le_one_add rate rewards C_star C_h u t control0 b j

/-- Each actual whole-cell score weight increases by at most the exponential
of four learning-rate units on the existing queue run. -/
theorem wholePostWeight_bounds (b : B) (j : Fin p.K) :
    ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b ≤
        ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
          rate j (wholePost b.2).1 ∧
      ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
          rate j (wholePost b.2).1 ≤
        Real.exp (4 * rate.eta.val) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
            rate rewards C_star C_h u t control0 j b := by
  exact pairPostWeight_bounds rate rewards C_star C_h u t control0 b j

/-- The actual whole-cell quadratic step is bounded by the full accepted
arrival polynomial on the same original renewal pair law. -/
theorem ae_pairWholeEnergyStep_le_fullArrivalBound :
    ∀ᵐ b : B ∂mu,
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
          rate (wholePost b.2).1 -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
          rate (incoming b.2).registers) ≤
      Set.indicator G (fun b =>
        ∑ j : Fin p.K,
          theta j b *
            ((-(15 / 2 : ℝ)) * backlog j b +
              (2 * backlog j b + 1 / 2) * fullA j b +
              fullA j b ^ 2 + 16)) b := by
  have hclear := ReferenceFirstCollectionRenewalExponentialQueueStep.ae_G_iff_incoming_noOverflow
    rate rewards C_star C_h u t control0
  have hreflect := ReferenceFirstCollectionRenewalWholeExponentialQueueStep.ae_fullPostBacklog_eq_reflected_increment
    rate rewards C_star C_h u t control0
  have hreflectAll : ∀ᵐ b ∂mu, ∀ j : Fin p.K,
      pairPostBacklog rate rewards C_star C_h u t b j =
        max (backlog j b +
          ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullRetainedIncrement
            rate rewards C_star C_h u t control0 j b) 0 := by
    filter_upwards [hreflect] with b hb
    intro j
    simpa [pairPostBacklog,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters] using hb j
  filter_upwards [hclear, hreflectAll] with b hclear hreflect
  by_cases hg : b ∈ G
  · have hno := hclear.mp hg
    have hBcapNonneg : 0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
        rate rewards C_star C_h u t control0 := by
      rw [ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap]
      exact one_div_nonneg.mpr (le_of_lt (mul_pos (by norm_num) rate.eta.property))
    have hBetaFloor : 32 * rate.eta.val ≤ CanonicalRecordingRates.beta p rate.eta.val := by
      unfold CanonicalRecordingRates.beta
      have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
        exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) (le_of_lt rate.eta.property)]
    have hInvBetaCap : 1 / CanonicalRecordingRates.beta p rate.eta.val ≤
        ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 := by
      rw [ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap]
      exact one_div_le_one_div_of_le
        (mul_pos (by norm_num) rate.eta.property) hBetaFloor
    have hEtaBcap : (16 * rate.eta.val) *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 = 1 / 2 := by
      rw [ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap]
      field_simp [ne_of_gt rate.eta.property]
      ring
    have hterms (j : Fin p.K) :
        pairPostTheta rate rewards C_star C_h u t b j *
            pairPostBacklog rate rewards C_star C_h u t b j ^ 2 -
          theta j b * backlog j b ^ 2 ≤
        theta j b *
          ((-(15 / 2 : ℝ)) * backlog j b +
            (2 * backlog j b + 1 / 2) * fullA j b +
            fullA j b ^ 2 + 16) := by
      let x := backlog j b
      let a := fullA j b
      let y := pairPostBacklog rate rewards C_star C_h u t b j
      have htheta :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
          rate rewards C_star C_h u t control0 j b
      have hback := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
        rate rewards C_star C_h u t control0 j b
      have hbackCap :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_Bcap_of_noOverflow
          rate rewards C_star C_h u t control0 j b hno
      have hArr := ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullAcceptedA_bounds
        rate rewards C_star C_h u t j b
      have hArrCap : a ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 := by
        calc
          a ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := by
            simpa [a] using hArr.2
          _ ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0 := hInvBetaCap
      have hreflection : y = max (x + a - 4) 0 := by
        have hinc :
            ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullRetainedIncrement
                rate rewards C_star C_h u t control0 j b = a - 4 := by
          simp [ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullRetainedIncrement,
            a, hg]
        dsimp [y]
        rw [hreflect j, hinc]
        congr 1; dsimp [x, a]; ring
      have hy0 : 0 ≤ y := by rw [hreflection]; exact le_max_right _ _
      have hyle : y ≤ x + a := by
        rw [hreflection]
        apply max_le
        · linarith
        · linarith [hback, hArr.1]
      have hmaxsq : (max (x + a - 4) 0) ^ 2 ≤ (x + a - 4) ^ 2 := by
        by_cases hsign : 0 ≤ x + a - 4
        · simp [max_eq_left hsign]
        · rw [max_eq_right (le_of_not_ge hsign)]
          simpa using sq_nonneg (x + a - 4)
      have henergy : y ^ 2 - x ^ 2 ≤ 2 * x * (a - 4) + a ^ 2 + 16 := by
        rw [hreflection]
        nlinarith [hmaxsq]
      have hyCap : y ≤ 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 := by
        calc
          y ≤ x + a := hyle
          _ ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0 +
              ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0 := add_le_add hbackCap hArrCap
          _ = 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0 := by ring
      have hysq : y ^ 2 ≤ 2 *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 * (x + a) := by
        have hprod := mul_nonneg (sub_nonneg.mpr hyCap) (sub_nonneg.mpr hyle)
        nlinarith
      have hthetaPost := pairPostTheta_le_one_add
        rate rewards C_star C_h u t control0 b j
      have hthetaDiff : pairPostTheta rate rewards C_star C_h u t b j - theta j b ≤
          8 * rate.eta.val * theta j b := by
        nlinarith [hthetaPost]
      have hratio : pairPostTheta rate rewards C_star C_h u t b j * y ^ 2 -
            theta j b * x ^ 2 ≤
          theta j b * (y ^ 2 - x ^ 2) +
            (8 * rate.eta.val * theta j b) * y ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hthetaDiff (sq_nonneg y)
        nlinarith
      have hcoef : 0 ≤ 8 * rate.eta.val * theta j b := by
        positivity [htheta.1, rate.eta.property]
      have hsecond : (8 * rate.eta.val * theta j b) * y ^ 2 ≤
          theta j b * (1 / 2 : ℝ) * (x + a) := by
        calc
          _ ≤ (8 * rate.eta.val * theta j b) *
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0 * (x + a)) :=
            mul_le_mul_of_nonneg_left hysq hcoef
          _ = theta j b * (1 / 2 : ℝ) * (x + a) := by
            have hEtaBcap' :
                (8 * rate.eta.val) *
                    (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                      rate rewards C_star C_h u t control0) = 1 / 2 := by
              nlinarith [hEtaBcap]
            calc
              _ = theta j b * ((8 * rate.eta.val) *
                    (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                      rate rewards C_star C_h u t control0)) * (x + a) := by ring
              _ = theta j b * (1 / 2 : ℝ) * (x + a) := by rw [hEtaBcap']
      calc
        _ = pairPostTheta rate rewards C_star C_h u t b j * y ^ 2 -
              theta j b * x ^ 2 := by rfl
        _ ≤ theta j b * (y ^ 2 - x ^ 2) +
              (8 * rate.eta.val * theta j b) * y ^ 2 := hratio
        _ ≤ theta j b * (2 * x * (a - 4) + a ^ 2 + 16) +
              theta j b * (1 / 2 : ℝ) * (x + a) :=
            add_le_add
              (mul_le_mul_of_nonneg_left henergy htheta.1) hsecond
        _ = theta j b *
              ((-(15 / 2 : ℝ)) * x + (2 * x + 1 / 2) * a + a ^ 2 + 16) := by
            ring
    have hpostEnergy :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
            rate (wholePost b.2).1 =
          ∑ j : Fin p.K,
            pairPostTheta rate rewards C_star C_h u t b j *
              pairPostBacklog rate rewards C_star C_h u t b j ^ 2 := by
      unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    have hpreEnergy :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
            rate (incoming b.2).registers =
          ∑ j : Fin p.K, theta j b * backlog j b ^ 2 := by
      unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hterms j)
    rw [hpostEnergy, hpreEnergy, ← Finset.sum_sub_distrib]
    simpa [Set.indicator_of_mem hg] using hsum
  · have hoverflow : (incoming b.2).overflow = true := by
      cases h : (incoming b.2).overflow with
      | false => exact False.elim (hg (hclear.mpr h))
      | true => rfl
    have hregs := pairPostRegisters_eq_incoming_of_overflow
      rate rewards C_star C_h u t b hoverflow
    have hzero :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
            rate (wholePost b.2).1 =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
            rate (incoming b.2).registers := by rw [hregs]
    simp [Set.indicator_of_notMem hg, hzero]


local notation "xi" => ReferenceFirstCollectionRenewalComplementMoments.xi
  rate rewards C_star C_h u t
local notation "reward" => ReferenceFirstCollectionRenewalComplementMoments.r rewards t

private def arm (j : Fin p.K) (b : B) : ℝ :=
  theta j b * ((-(15 / 2 : ℝ)) * backlog j b +
    (2 * backlog j b + 1 / 2) * fullA j b + fullA j b ^ 2 + 16)

private def armCE (j : Fin p.K) (b : B) : ℝ :=
  theta j b * (2 * backlog j b + 1 / 2) * mu[fullA j | F_R] b +
    theta j b * mu[(fun x : B => fullA j x ^ 2) | F_R] b +
    (-(15 / 2 : ℝ)) * (theta j b * backlog j b) + 16 * theta j b

private theorem arm_parts_integrable (j : Fin p.K) :
    Integrable (fun b : B => theta j b * (2 * backlog j b + 1 / 2) * fullA j b) mu ∧
    Integrable (fun b : B => theta j b * fullA j b ^ 2) mu ∧
    Integrable (fun b : B => (-(15 / 2 : ℝ)) * (theta j b * backlog j b) +
      16 * theta j b) mu := by
  have ht := ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_thetaMinus
    rate rewards C_star C_h u t control0 j
  have htb := ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus
    rate rewards C_star C_h u t control0 j
  have hc : Integrable (fun b : B => theta j b * (2 * backlog j b + 1 / 2)) mu := by
    convert (htb.const_mul (2 : ℝ)).add (ht.const_mul (1 / 2 : ℝ)) using 1
    ext b
    dsimp
    ring
  have ha := ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.measurable_fullAcceptedA
    rate rewards C_star C_h u t j
  have hbound : ∀ᵐ b : B ∂mu, ‖fullA j b‖ ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
    filter_upwards [] with b
    have h := ReferenceFirstCollectionRenewalWholeExponentialQueueStep.fullAcceptedA_bounds
      rate rewards C_star C_h u t j b
    simpa only [Real.norm_of_nonneg h.1] using h.2
  have hbound2 : ∀ᵐ b : B ∂mu, ‖fullA j b ^ 2‖ ≤
      (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    filter_upwards [hbound] with b hb
    simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
  exact ⟨hc.mul_bdd ha.aestronglyMeasurable hbound,
    ht.mul_bdd (ha.pow_const 2).aestronglyMeasurable hbound2,
    (htb.const_mul (-(15 / 2 : ℝ))).add (ht.const_mul (16 : ℝ))⟩

private theorem integrable_arm (j : Fin p.K) : Integrable
    (arm rate rewards C_star C_h u t control0 j) mu := by
  obtain ⟨h1, h2, h3⟩ := arm_parts_integrable rate rewards C_star C_h u t control0 j
  convert (h1.add h2).add h3 using 1
  ext b
  dsimp [arm]
  ring

private theorem condExp_arm (j : Fin p.K) :
    mu[arm rate rewards C_star C_h u t control0 j | F_R] =ᵐ[mu]
      armCE rate rewards C_star C_h u t control0 j := by
  let c : B → ℝ := fun b => theta j b * (2 * backlog j b + 1 / 2)
  let base : B → ℝ := fun b =>
    (-(15 / 2 : ℝ)) * (theta j b * backlog j b) + 16 * theta j b
  have ht : AEStronglyMeasurable[F_R] (theta j) mu :=
    (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinusRetained
      rate rewards C_star C_h u t control0 j).aestronglyMeasurable.congr
      ((ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_thetaMinus_eq_retained
        rate rewards C_star C_h u t control0 j).mono (fun _ h => h.symm))
  have hb : AEStronglyMeasurable[F_R] (backlog j) mu :=
    (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinusRetained
      rate rewards C_star C_h u t control0 j).aestronglyMeasurable.congr
      ((ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_bMinus_eq_retained
        rate rewards C_star C_h u t control0 j).mono (fun _ h => h.symm))
  have hc : AEStronglyMeasurable[F_R] c mu :=
    ht.mul ((hb.const_mul (2 : ℝ)).add aestronglyMeasurable_const)
  have hbase : AEStronglyMeasurable[F_R] base mu :=
    ((ht.mul hb).const_mul (-(15 / 2 : ℝ))).add (ht.const_mul (16 : ℝ))
  obtain ⟨h1, h2, h3⟩ := arm_parts_integrable rate rewards C_star C_h u t control0 j
  change Integrable (c * fullA j) mu at h1
  change Integrable (theta j * fun b : B => fullA j b ^ 2) mu at h2
  change Integrable base mu at h3
  have hp1 := condExp_mul_of_aestronglyMeasurable_left hc h1
    (ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.integrable_fullAcceptedA
      rate rewards C_star C_h u t j)
  have hp2 := condExp_mul_of_aestronglyMeasurable_left ht h2
    (ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.integrable_fullAcceptedA_sq
      rate rewards C_star C_h u t j)
  have hfixed := condExp_of_aestronglyMeasurable'
    (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
      rate rewards C_star C_h u t control0) hbase h3
  have heq : arm rate rewards C_star C_h u t control0 j =
      (c * fullA j + (theta j * fun b : B => fullA j b ^ 2)) + base := by
    ext b
    dsimp [arm, c, base]
    ring
  rw [heq]
  filter_upwards [condExp_add (h1.add h2) h3 F_R, condExp_add h1 h2 F_R,
    hp1, hp2, hfixed] with b ha hb hc hd he
  rw [ha]
  change mu[c * fullA j + (theta j * fun b : B => fullA j b ^ 2) | F_R] b +
    mu[base | F_R] b = _
  rw [hb]
  simp only [Pi.add_apply]
  rw [hc, hd, he]
  dsimp [c, base, armCE]
  ring

private theorem condExp_armSum :
    mu[(fun b : B => ∑ j, arm rate rewards C_star C_h u t control0 j b) | F_R] =ᵐ[mu]
      fun b : B => ∑ j, armCE rate rewards C_star C_h u t control0 j b := by
  have hs := condExp_finsetSum (μ := mu) (s := Finset.univ)
    (fun j _ => integrable_arm rate rewards C_star C_h u t control0 j) F_R
  have he : (fun b : B => ∑ j, arm rate rewards C_star C_h u t control0 j b) =
      ∑ j, arm rate rewards C_star C_h u t control0 j := by
    ext b
    simp only [Finset.sum_apply]
  rw [he]
  filter_upwards [hs, Filter.eventually_all.mpr
    (fun j => condExp_arm rate rewards C_star C_h u t control0 j)] with b hb hj
  simpa only [Finset.sum_apply, hj] using hb

/-- Whole-marker conditional energy drift on the existing renewal pair law.
This uses every owner contribution in the full first and square moments. -/
theorem ae_pairConditionalWeightedEnergyDrift :
    mu[(fun b : B => VwholePlus rate rewards C_star C_h u t b.2 -
      Vminus rate rewards C_star C_h u t b.2) | F_R] ≤ᵐ[mu]
    (G).indicator (fun b => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t b.2 +
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
  have hsint : Integrable (fun b : B => ∑ j,
      arm rate rewards C_star C_h u t control0 j b) mu := by
    simpa only [← Finset.sum_apply] using integrable_finsetSum Finset.univ
      (fun j _ => integrable_arm rate rewards C_star C_h u t control0 j)
  have hG := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0
  have hm := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hdint : Integrable (fun b : B => VwholePlus rate rewards C_star C_h u t b.2 -
      Vminus rate rewards C_star C_h u t b.2) mu := by
    have hi := (integrable_VwholePlus rate rewards C_star C_h u t control0).sub
      (integrable_Vminus rate rewards C_star C_h u t control0)
    rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
      rate rewards C_star C_h u t] at hi
    exact (integrable_map_measure
      ((measurable_VwholePlus rate rewards C_star C_h u t).sub
        (measurable_Vminus rate rewards C_star C_h u t)).aestronglyMeasurable
      measurable_snd.aemeasurable).mp hi
  have hmono := condExp_mono (m := F_R) hdint (hsint.indicator (hm G hG))
    (ae_pairWholeEnergyStep_le_fullArrivalBound rate rewards C_star C_h u t control0)
  have hmask := condExp_indicator hsint hG
  have hs := condExp_armSum rate rewards C_star C_h u t control0
  have hfirst := Filter.eventually_all.mpr (fun j =>
    ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.condExp_fullAcceptedA
      rate rewards C_star C_h u t control0 j)
  have hsquare := Filter.eventually_all.mpr (fun j =>
    ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.condExp_fullAcceptedA_sq
      rate rewards C_star C_h u t control0 j)
  filter_upwards [hmono, hmask, hs, hfirst, hsquare,
    ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_sum_thetaMinus_div_actualRenewalRate_le_R
      rate rewards C_star C_h u t control0] with b hmono hmask hs hfirst hsquare hrate
  have hbound : ((G).indicator (fun b => ∑ j,
      armCE rate rewards C_star C_h u t control0 j b)) b ≤
      ((G).indicator (fun b => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t b.2 +
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ))) b := by
    by_cases hg : b ∈ G
    · simp only [Set.indicator_of_mem hg]
      have hterm (j : Fin p.K) : armCE rate rewards C_star C_h u t control0 j b ≤
          -(11 / 2 : ℝ) * (theta j b * backlog j b) +
            theta j b / xi b j + (33 / 2 : ℝ) * theta j b := by
        have ht := ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
          rate rewards C_star C_h u t control0 j b
        have hb := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
          rate rewards C_star C_h u t control0 j b
        have hr : reward j ∈ Set.Icc (0 : ℝ) 1 :=
          RealRewardGridCount.realRewardGridValue_mem_Icc (D p) (D_pos p) (rewards t j)
        have hxi : 0 < xi b j := CanonicalRecordingRates.xi_pos p rate.eta.property _ j
        have hq1 := QuantizedRecordingMoments.quantizedValue_firstMoment_le
          (D p) rate.eta.val (xi b j) (reward j) (D_pos p) rate.eta.property hxi hr
        have hq2 := QuantizedRecordingMoments.quantizedValue_secondMoment_le
          (D p) rate.eta.val (xi b j) (reward j) (D_pos p) rate.eta.property hxi hr
        have hce1 : mu[fullA j | F_R] b ≤ 1 := by
          rw [hfirst j, Set.indicator_of_mem hg, one_mul]
          exact hq1.trans hr.2
        have hce2 : mu[(fun x : B => fullA j x ^ 2) | F_R] b ≤ 1 / xi b j := by
          rw [hsquare j, Set.indicator_of_mem hg, one_mul]
          exact hq2.trans (div_le_div_of_nonneg_right (by nlinarith [hr.1, hr.2]) hxi.le)
        have h1 := mul_le_mul_of_nonneg_left hce1
          (mul_nonneg ht.1 (by linarith : 0 ≤ 2 * backlog j b + 1 / 2))
        have h2 := mul_le_mul_of_nonneg_left hce2 ht.1
        dsimp [armCE]
        have hdiv : theta j b * (1 / xi b j) = theta j b / xi b j := by ring
        rw [hdiv] at h2
        nlinarith only [h1, h2]
      have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
      have halg : (∑ j : Fin p.K, (-(11 / 2 : ℝ) * (theta j b * backlog j b) +
          theta j b / xi b j + (33 / 2 : ℝ) * theta j b)) =
          -(11 / 2 : ℝ) * (∑ j, theta j b * backlog j b) +
          (∑ j, theta j b / xi b j) + (33 / 2 : ℝ) * (∑ j, theta j b) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      rw [halg, ReferenceFirstCollectionRenewalIncomingQueueBounds.sum_thetaMinus] at hsum
      exact hsum.trans (by change _ ≤ -(11 / 2 : ℝ) * (∑ j, theta j b * backlog j b) +
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ); linarith [hrate hg])
    · simp only [Set.indicator_of_notMem hg, le_refl]
  apply hmono.trans
  apply le_trans _ hbound
  rw [hmask]
  by_cases hg : b ∈ G <;> simp only [Set.indicator, hg, hs, le_refl, ↓reduceIte]


/-- The exact incoming energy is measurable in the incoming-readout field. -/
theorem measurable_Vminus_F_ER : Measurable[F_ER]
    (Vminus rate rewards C_star C_h u t) :=
  (measurable_of_countable
    (ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate)).comp
      (measurable_fst.comp (comap_measurable ER))

/-- The exact incoming weighted backlog uses only the incoming readout. -/
theorem measurable_Bminus_F_ER : Measurable[F_ER]
    (Bminus rate rewards C_star C_h u t) := by
  let h : (Fin p.K → ℕ × ℕ) → ℝ := fun A => ∑ j,
    ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j A *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j A
  exact (measurable_of_countable h).comp
    (measurable_fst.comp (comap_measurable ER))

/-- The incoming clear event is measurable before the whole-cell update. -/
theorem measurableSet_E_F_ER : MeasurableSet[F_ER] (E rate rewards C_star C_h u t) :=
  ((measurable_fst.comp measurable_snd).comp (comap_measurable ER))
    (MeasurableSet.singleton false)

local notation "cost" => Set.indicator (E rate rewards C_star C_h u t) (fun z =>
  -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
    CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ))

private theorem measurable_cost_F_ER : Measurable[F_ER] cost :=
  (((measurable_Bminus_F_ER rate rewards C_star C_h u t).const_mul (-(11 / 2 : ℝ))).add_const
    (CanonicalRecordingRates.R p) |>.add_const ((33 / 2 : ℝ) * (p.m : ℝ))).indicator
      (measurableSet_E_F_ER rate rewards C_star C_h u t)

private theorem measurable_cost : Measurable cost :=
  (measurable_cost_F_ER rate rewards C_star C_h u t).mono
    (ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
      rate rewards C_star C_h u t) le_rfl

private theorem integrable_pair_comp {f : Z → ℝ} (hf : Measurable f)
    (hi : Integrable f nu) : Integrable (fun b : B => f b.2) mu := by
  rw [← ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_map_snd
    rate rewards C_star C_h u t] at hi
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mp hi

include control0

/-- Every bounded nonnegative Borel test of the original incoming readout
preserves the whole-marker quadratic drift comparison on the source law. -/
theorem integral_readoutMul_wholeEnergyDrift_le
    (psi : Readout p → ℝ) (hpsi : Measurable psi)
    (C : ℝ) (hpsiBound : ∀ x, 0 ≤ psi x ∧ psi x ≤ C) :
    (∫ z : Z, psi (ER z) * (VwholePlus rate rewards C_star C_h u t z -
      Vminus rate rewards C_star C_h u t z) ∂nu) ≤
      ∫ z : Z, psi (ER z) * cost z ∂nu := by
  let f : B → ℝ := fun b => VwholePlus rate rewards C_star C_h u t b.2 -
    Vminus rate rewards C_star C_h u t b.2
  let g : B → ℝ := fun b => cost b.2
  let H : B → ℝ := fun b => psi (ER b.2)
  have hf := integrable_pair_comp rate rewards C_star C_h u t
    ((measurable_VwholePlus rate rewards C_star C_h u t).sub
      (measurable_Vminus rate rewards C_star C_h u t))
    ((integrable_VwholePlus rate rewards C_star C_h u t control0).sub
      (integrable_Vminus rate rewards C_star C_h u t control0))
  have hg := integrable_pair_comp rate rewards C_star C_h u t
    (measurable_cost rate rewards C_star C_h u t)
    (integrable_weightedCost rate rewards C_star C_h u t control0)
  have hH : AEStronglyMeasurable[F_R] H mu := by
    have hret := hpsi.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncomingReadout
        rate rewards C_star C_h u t control0)
    apply hret.aestronglyMeasurable.congr
    filter_upwards [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.ae_incomingReadout_eq_retained
      rate rewards C_star C_h u t control0] with b hb
    exact congrArg psi hb.symm
  have hHambient : Measurable H := (hpsi.comp
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)).comp measurable_snd
  have hHnorm : ∀ᵐ b : B ∂mu, ‖H b‖ ≤ C := by
    filter_upwards [] with b
    exact (Real.norm_of_nonneg (hpsiBound _).1).trans_le (hpsiBound _).2
  have hHf : Integrable (H * f) mu := hf.bdd_mul hHambient.aestronglyMeasurable hHnorm
  have hHg : Integrable (H * g) mu := hg.bdd_mul hHambient.aestronglyMeasurable hHnorm
  have hpull := condExp_mul_of_aestronglyMeasurable_left hH hHf hf
  have hHce : Integrable (H * mu[f | F_R]) mu := integrable_condExp.congr hpull
  have hce : mu[f | F_R] ≤ᵐ[mu] g := by
    filter_upwards [ae_pairConditionalWeightedEnergyDrift rate rewards C_star C_h u t control0,
      ReferenceFirstCollectionRenewalExponentialQueueStep.ae_G_iff_incoming_noOverflow
        rate rewards C_star C_h u t control0] with b hb hclear
    have he : b ∈ G ↔ b.2 ∈ E rate rewards C_star C_h u t := hclear
    simpa only [g, Set.indicator, he] using hb
  have hpoint : H * mu[f | F_R] ≤ᵐ[mu] H * g := by
    filter_upwards [hce] with b hb
    exact mul_le_mul_of_nonneg_left hb (hpsiBound _).1
  have hpair : (∫ b : B, H b * f b ∂mu) ≤ ∫ b : B, H b * g b ∂mu := by
    calc
      _ = ∫ b : B, mu[H * f | F_R] b ∂mu :=
        (integral_condExp (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
          rate rewards C_star C_h u t control0)).symm
      _ = ∫ b : B, H b * mu[f | F_R] b ∂mu := integral_congr_ae hpull
      _ ≤ _ := integral_mono_ae hHce hHg hpoint
  have htest : Measurable (fun z : Z => psi (ER z)) := hpsi.comp
    (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)
  calc
    _ = ∫ b : B, H b * f b ∂mu :=
      integral_source_eq_pair rate rewards C_star C_h u t
        (fun z => psi (ER z) * (VwholePlus rate rewards C_star C_h u t z -
          Vminus rate rewards C_star C_h u t z))
        (htest.mul ((measurable_VwholePlus rate rewards C_star C_h u t).sub
          (measurable_Vminus rate rewards C_star C_h u t)))
    _ ≤ ∫ b : B, H b * g b ∂mu := hpair
    _ = _ := (integral_source_eq_pair rate rewards C_star C_h u t
      (fun z => psi (ER z) * cost z)
      (htest.mul (measurable_cost rate rewards C_star C_h u t))).symm

/-- Set tests on precisely the incoming-readout field, with the same
incoming and outgoing whole-marker energies under the original source law. -/
theorem setIntegral_wholeEnergyDrift_le (H : Set Z) (hH : MeasurableSet[F_ER] H) :
    (∫ z in H, VwholePlus rate rewards C_star C_h u t z -
      Vminus rate rewards C_star C_h u t z ∂nu) ≤ ∫ z in H, cost z ∂nu := by
  obtain ⟨Dtest, hDtest, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hH
  let psi : Readout p → ℝ := Dtest.indicator (fun _ => (1 : ℝ))
  have hpsi : Measurable psi := measurable_const.indicator hDtest
  have hbound : ∀ r, 0 ≤ psi r ∧ psi r ≤ 1 := by
    intro r
    by_cases hr : r ∈ Dtest <;> simp [psi, hr]
  have hi := integral_readoutMul_wholeEnergyDrift_le rate rewards C_star C_h u t control0
    psi hpsi 1 hbound
  have htest (f : Z → ℝ) : (fun z => psi (ER z) * f z) = H.indicator f := by
    ext z
    have hz : ER z ∈ Dtest ↔ z ∈ H := by
      change z ∈ ER ⁻¹' Dtest ↔ z ∈ H
      rw [hpre]
    by_cases h : z ∈ H <;> simp [psi, Set.indicator, hz, h]
  rw [htest, htest, integral_indicator
    ((ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
      rate rewards C_star C_h u t) H hH), integral_indicator
    ((ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
      rate rewards C_star C_h u t) H hH)] at hi
  exact hi

/-- Principal whole-marker one-cell weighted quadratic drift, conditioned
only on the original incoming readout and retaining both energies. -/
theorem ae_conditionalWholeWeightedEnergyDrift :
    nu[(fun z : Z => VwholePlus rate rewards C_star C_h u t z -
      Vminus rate rewards C_star C_h u t z) | F_ER] ≤ᵐ[nu] cost := by
  let m₀ : MeasurableSpace Z := inferInstance
  let μ₀ : @Measure Z m₀ := nu
  let m : MeasurableSpace Z := F_ER
  have hm : m ≤ m₀ :=
    ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
      rate rewards C_star C_h u t
  let μm : @Measure Z m := μ₀.trim hm
  let ce : Z → ℝ := μ₀[(fun z : Z => VwholePlus rate rewards C_star C_h u t z -
    Vminus rate rewards C_star C_h u t z) | m]
  have hce : StronglyMeasurable[m] ce := stronglyMeasurable_condExp
  have hc : StronglyMeasurable[m] cost :=
    (measurable_cost_F_ER rate rewards C_star C_h u t).stronglyMeasurable
  have hci : Integrable cost μ₀ := integrable_weightedCost rate rewards C_star C_h u t control0
  have hi : Integrable (fun z : Z => VwholePlus rate rewards C_star C_h u t z -
      Vminus rate rewards C_star C_h u t z) μ₀ :=
    (integrable_VwholePlus rate rewards C_star C_h u t control0).sub
      (integrable_Vminus rate rewards C_star C_h u t control0)
  have hcei : Integrable ce μ₀ := integrable_condExp
  have ht : ce ≤ᵐ[μm] cost := by
    apply ae_le_of_forall_setIntegral_le (hcei.trim hm hce) (hci.trim hm hc)
    intro H hH _
    have hs := setIntegral_wholeEnergyDrift_le rate rewards C_star C_h u t control0 H hH
    have hces : (∫ z in H, ce z ∂μ₀) = ∫ z in H,
        VwholePlus rate rewards C_star C_h u t z - Vminus rate rewards C_star C_h u t z ∂μ₀ :=
      setIntegral_condExp hm hi hH
    rw [← setIntegral_trim hm hce hH, ← setIntegral_trim hm hc hH, hces]
    exact hs
  exact MeasureTheory.ae_le_of_ae_le_trim (hm := hm) ht

/-- Integrated whole-marker cost inequality on the finite, unnormalized,
possibly-zero original renewal source law. No chronological telescope is asserted. -/
theorem weightedCost_integral_le :
    (11 / 2 : ℝ) * (∫ z : Z, (E rate rewards C_star C_h u t).indicator
      (Bminus rate rewards C_star C_h u t) z ∂nu) ≤
    (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
      (nu).real (E rate rewards C_star C_h u t) +
        (∫ z : Z, Vminus rate rewards C_star C_h u t z ∂nu) -
        ∫ z : Z, VwholePlus rate rewards C_star C_h u t z ∂nu := by
  have hm := ReferenceFirstCollectionRenewalSourceConditionalExponential.F_ER_le_ambient
    rate rewards C_star C_h u t
  have hle := integral_mono_ae integrable_condExp
    (integrable_weightedCost rate rewards C_star C_h u t control0)
    (ae_conditionalWholeWeightedEnergyDrift rate rewards C_star C_h u t control0)
  rw [integral_condExp hm, integral_sub
    (integrable_VwholePlus rate rewards C_star C_h u t control0)
    (integrable_Vminus rate rewards C_star C_h u t control0)] at hle
  have hcost : (∫ z : Z, cost z ∂nu) =
      -(11 / 2 : ℝ) * (∫ z : Z, (E rate rewards C_star C_h u t).indicator
        (Bminus rate rewards C_star C_h u t) z ∂nu) +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (nu).real (E rate rewards C_star C_h u t) := by
    rw [integral_indicator (measurableSet_E rate rewards C_star C_h u t)]
    have heq : (fun z : Z => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) =
        fun z => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
      ext z
      ring
    rw [heq, integral_add
      (((integrable_Bminus rate rewards C_star C_h u t control0).restrict).const_mul _)
      (integrable_const _), integral_const_mul, integral_const,
      integral_indicator (measurableSet_E rate rewards C_star C_h u t)]
    simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm]
  rw [hcost] at hle
  linarith only [hle]

end Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift

end
