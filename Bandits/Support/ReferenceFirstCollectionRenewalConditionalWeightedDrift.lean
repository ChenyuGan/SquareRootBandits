/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalQueueEnergy

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# First-renewal conditional weighted queue drift

The conditional drift and its set-integral consequences use the original
finite, unnormalized renewal pair law and the exact retained-control comap
field. The complete queue cost is masked by the same no-incoming-overflow
event.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalConditionalWeightedDrift

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" =>
  ReferenceFirstCollectionRenewalAcceptedComplementMoments.Pair
    rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t
local notation "H" =>
  ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p
local notation "Rcoord" =>
  ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
local notation "F_R" =>
  MeasurableSpace.comap Rcoord (inferInstance : MeasurableSpace H)
local notation "G" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0
local notation "theta" =>
  ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
    rate rewards C_star C_h u t control0
local notation "backlog" =>
  ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
    rate rewards C_star C_h u t control0
local notation "acceptedA" =>
  ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
    rate rewards C_star C_h u t
local notation "chi" =>
  ReferenceFirstCollectionRenewalComplementMoments.chi
    rate rewards C_star C_h u t
local notation "xi" =>
  ReferenceFirstCollectionRenewalComplementMoments.xi
    rate rewards C_star C_h u t
local notation "reward" =>
  ReferenceFirstCollectionRenewalComplementMoments.r rewards t

/-- The literal incoming score weight on the actual renewal pair. -/
def thetaReadout (j : Fin p.K) (b : B) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
    rate rewards C_star C_h u t control0 j b

/-- The literal incoming queue on the actual renewal pair. -/
def backlogReadout (j : Fin p.K) (b : B) : ℝ :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
    rate rewards C_star C_h u t control0 j b

/-- The accepted-arrival readout on the same finite pair law. -/
def acceptedAReadout (j : Fin p.K) (b : B) : ℝ :=
  ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
    rate rewards C_star C_h u t j b

/-- The enabled and accepted complement indicator. -/
def chiReadout (b : B) (j : Fin p.K) : ℝ :=
  ReferenceFirstCollectionRenewalComplementMoments.chi
    rate rewards C_star C_h u t b j

/-- The exact actual renewal-rate denominator. -/
def xiReadout (b : B) (j : Fin p.K) : ℝ :=
  ReferenceFirstCollectionRenewalComplementMoments.xi
    rate rewards C_star C_h u t b j

/-- The whole reward-table value for the selected calendar date and arm. -/
def rewardReadout (j : Fin p.K) : ℝ :=
  ReferenceFirstCollectionRenewalComplementMoments.r rewards t j

/-- The incoming-minus-after first-renewal energy difference on the pair. -/
def firstRenewalEnergyDifference (b : B) : ℝ :=
  ReferenceFirstCollectionRenewalQueueEnergy.VPlus
      rate rewards C_star C_h u t b -
    ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
      rate rewards C_star C_h u t control0 b

/-- The actual first-renewal incoming-energy summand. -/
def reducedEnergyArm (j : Fin p.K) (b : B) : ℝ :=
  theta j b *
    ((-15 / 2 : ℝ) * backlog j b +
      (2 * backlog j b + 1 / 2) * acceptedA j b +
      acceptedA j b ^ 2 + 16)

/-- Its exact conditional-expectation decomposition on the retained field. -/
def reducedEnergyArmConditional (j : Fin p.K) (b : B) : ℝ :=
  theta j b * (2 * backlog j b + 1 / 2) *
      mu[(fun x : B => acceptedA j x) | F_R] b +
    theta j b * mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b +
    (-(15 / 2 : ℝ)) * (theta j b * backlog j b) +
    16 * theta j b

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

local instance retainedFieldSigmaFinite :
    SigmaFinite ((mu).trim
      (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
        rate rewards C_star C_h u t control0)) :=
  ReferenceFirstCollectionRenewalComplementMoments.retainedField_trim_sigmaFinite
    rate rewards C_star C_h u t control0

private theorem integrable_armReduced (j : Fin p.K) :
    Integrable (reducedEnergyArm rate rewards C_star C_h u t control0 j) mu := by
  have htb :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus
      rate rewards C_star C_h u t control0 j
  have htba :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus_mul_acceptedA
      rate rewards C_star C_h u t control0 j
  have hta :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_acceptedA
      rate rewards C_star C_h u t control0 j
  have hta2 :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_acceptedA_sq
      rate rewards C_star C_h u t control0 j
  have htheta :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_thetaMinus
      rate rewards C_star C_h u t control0 j
  have hsum1 := (htba.const_mul (2 : ℝ)).add (hta.const_mul (1 / 2 : ℝ))
  have hsum2 := hsum1.add (htb.const_mul (-(15 / 2 : ℝ)))
  have hsum3 := hsum2.add hta2
  have hsum := hsum3.add (htheta.const_mul (16 : ℝ))
  refine hsum.congr ?_
  filter_upwards [] with b
  dsimp [reducedEnergyArm]
  ring_nf

private theorem condExp_armReduced (j : Fin p.K) :
    mu[reducedEnergyArm rate rewards C_star C_h u t control0 j | F_R] =ᵐ[mu]
      reducedEnergyArmConditional rate rewards C_star C_h u t control0 j := by
  let thetaR : B → ℝ :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinusRetained
      rate rewards C_star C_h u t control0 j
  let backlogR : B → ℝ :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinusRetained
      rate rewards C_star C_h u t control0 j
  let coeff : B → ℝ := fun b => thetaR b * (2 * backlogR b + 1 / 2)
  let base : B → ℝ := fun b =>
    (-(15 / 2 : ℝ)) * (thetaR b * backlogR b) + 16 * thetaR b
  have hthetaEq : (fun b : B => theta j b) =ᵐ[mu] thetaR :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_thetaMinus_eq_retained
      rate rewards C_star C_h u t control0 j
  have hbacklogEq : (fun b : B => backlog j b) =ᵐ[mu] backlogR :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_bMinus_eq_retained
      rate rewards C_star C_h u t control0 j
  have hactualEq :
      (fun b : B =>
        theta j b *
          ((-15 / 2 : ℝ) * backlog j b +
            (2 * backlog j b + 1 / 2) * acceptedA j b +
            acceptedA j b ^ 2 + 16)) =ᵐ[mu]
      (fun b : B =>
        thetaR b *
          ((-15 / 2 : ℝ) * backlogR b +
            (2 * backlogR b + 1 / 2) * acceptedA j b +
            acceptedA j b ^ 2 + 16)) := by
    filter_upwards [hthetaEq, hbacklogEq] with b hθ hb
    rw [hθ, hb]
  have hCoeffActual : Integrable (fun b : B =>
      theta j b * (2 * backlog j b + 1 / 2) * acceptedA j b) mu := by
    have hsum :=
      (ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus_mul_acceptedA
        rate rewards C_star C_h u t control0 j).const_mul (2 : ℝ) |>.add
      ((ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_acceptedA
        rate rewards C_star C_h u t control0 j).const_mul (1 / 2 : ℝ))
    refine hsum.congr ?_
    filter_upwards [] with b
    dsimp
    ring
  have hCoeffEq :
      (fun b : B => coeff b * acceptedA j b) =ᵐ[mu]
        (fun b : B => theta j b * (2 * backlog j b + 1 / 2) * acceptedA j b) := by
    filter_upwards [hthetaEq, hbacklogEq] with b hθ hb
    simp [coeff, thetaR, backlogR, hθ, hb]
  have hCoeffInt := hCoeffActual.congr hCoeffEq.symm
  have hThetaSqActual : Integrable (fun b : B => theta j b * acceptedA j b ^ 2) mu :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_acceptedA_sq
      rate rewards C_star C_h u t control0 j
  have hThetaSqEq :
      (fun b : B => thetaR b * acceptedA j b ^ 2) =ᵐ[mu]
        (fun b : B => theta j b * acceptedA j b ^ 2) := by
    filter_upwards [hthetaEq] with b hθ
    simp [hθ]
  have hThetaSqInt := hThetaSqActual.congr hThetaSqEq.symm
  have hThetaBackActual : Integrable (fun b : B => theta j b * backlog j b) mu :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus
      rate rewards C_star C_h u t control0 j
  have hThetaBackEq :
      (fun b : B => thetaR b * backlogR b) =ᵐ[mu]
        (fun b : B => theta j b * backlog j b) := by
    filter_upwards [hthetaEq, hbacklogEq] with b hθ hb
    simp [hθ, hb]
  have hThetaBackInt := hThetaBackActual.congr hThetaBackEq.symm
  have hThetaActual : Integrable (fun b : B => theta j b) mu :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_thetaMinus
      rate rewards C_star C_h u t control0 j
  have hThetaEq : (fun b : B => thetaR b) =ᵐ[mu] fun b : B => theta j b :=
    hthetaEq.symm
  have hThetaInt := hThetaActual.congr hThetaEq.symm
  have hCoeffMeas : Measurable[F_R] coeff := by
    dsimp [coeff]
    exact (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinusRetained
      rate rewards C_star C_h u t control0 j).mul
      ((measurable_const.mul
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinusRetained
          rate rewards C_star C_h u t control0 j)).add_const (1 / 2 : ℝ))
  have hThetaMeas : Measurable[F_R] thetaR := by
    dsimp [thetaR]
    exact ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinusRetained
      rate rewards C_star C_h u t control0 j
  have hBaseMeas : Measurable[F_R] base := by
    dsimp [base]
    exact (measurable_const.mul
      ((ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinusRetained
        rate rewards C_star C_h u t control0 j).mul
       (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinusRetained
        rate rewards C_star C_h u t control0 j))).add
      (measurable_const.mul
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinusRetained
          rate rewards C_star C_h u t control0 j))
  have hBaseInt : Integrable base mu := by
    dsimp [base]
    exact (hThetaBackInt.const_mul (-(15 / 2 : ℝ))).add
      (hThetaInt.const_mul (16 : ℝ))
  have hAcceptedInt :=
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.integrable_acceptedA
      rate rewards C_star C_h u t j
  have hAcceptedSqInt :=
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.integrable_acceptedA_sq
      rate rewards C_star C_h u t j
  have hCoeffFunctionEq :
      (fun b : B => coeff b * acceptedA j b) = coeff * acceptedA j := by
    funext b
    rfl
  have hThetaFunctionEq :
      (fun b : B => thetaR b * acceptedA j b ^ 2) =
        thetaR * (fun b : B => acceptedA j b ^ 2) := by
    funext b
    rfl
  have hCoeffBridge := condExp_congr_ae (m := F_R)
    (ae_of_all mu fun b => congrFun hCoeffFunctionEq b)
  have hThetaBridge := condExp_congr_ae (m := F_R)
    (ae_of_all mu fun b => congrFun hThetaFunctionEq b)
  have hCoeffPull := condExp_mul_of_aestronglyMeasurable_left
    hCoeffMeas.aestronglyMeasurable hCoeffInt hAcceptedInt
  have hThetaPull := condExp_mul_of_aestronglyMeasurable_left
    hThetaMeas.aestronglyMeasurable hThetaSqInt hAcceptedSqInt
  have hBaseFixed := condExp_of_aestronglyMeasurable'
    (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
      rate rewards C_star C_h u t control0)
    hBaseMeas.aestronglyMeasurable hBaseInt
  have hCoeffShape :
      (fun b : B => coeff b * acceptedA j b) =
        (fun b => coeff b * acceptedA j b) := rfl
  have hThetaShape :
      (fun b : B => thetaR b * acceptedA j b ^ 2) =
        (fun b => thetaR b * acceptedA j b ^ 2) := rfl
  have hShape :
      (fun b : B =>
        thetaR b *
          ((-15 / 2 : ℝ) * backlogR b +
            (2 * backlogR b + 1 / 2) * acceptedA j b +
            acceptedA j b ^ 2 + 16)) =
      ((fun b : B => coeff b * acceptedA j b) +
        (fun b : B => thetaR b * acceptedA j b ^ 2)) + base := by
    funext b
    dsimp [coeff, base]
    ring
  have hFirstCE := condExp_add hCoeffInt hThetaSqInt F_R
  have hTotalCE := condExp_add (hCoeffInt.add hThetaSqInt) hBaseInt F_R
  filter_upwards [
    condExp_congr_ae (m := F_R) hactualEq,
    condExp_congr_ae (m := F_R) (ae_of_all mu fun b => congrFun hShape b),
    hFirstCE, hTotalCE, hCoeffPull, hThetaPull, hBaseFixed,
    hCoeffBridge, hThetaBridge, hthetaEq, hbacklogEq] with b
      hactual hshape hfirst htotal hcoeff htheta hbase hcoeffBridge hthetaBridge hθ hb
  calc
    mu[(fun x : B =>
      theta j x *
        ((-15 / 2 : ℝ) * backlog j x +
          (2 * backlog j x + 1 / 2) * acceptedA j x +
          acceptedA j x ^ 2 + 16)) | F_R] b =
        mu[(fun x : B =>
          thetaR x *
            ((-15 / 2 : ℝ) * backlogR x +
              (2 * backlogR x + 1 / 2) * acceptedA j x +
              acceptedA j x ^ 2 + 16)) | F_R] b := hactual
    _ = mu[((fun x : B => coeff x * acceptedA j x) +
          (fun x : B => thetaR x * acceptedA j x ^ 2)) + base | F_R] b := by
          rw [hshape]
    _ = (mu[(fun x : B => coeff x * acceptedA j x) +
            (fun x : B => thetaR x * acceptedA j x ^ 2) | F_R] b) +
          mu[base | F_R] b := htotal
    _ = (mu[(fun x : B => coeff x * acceptedA j x) | F_R] b +
          mu[(fun x : B => thetaR x * acceptedA j x ^ 2) | F_R] b) +
          mu[base | F_R] b := by
        change (mu[(fun x : B => coeff x * acceptedA j x) +
            (fun x : B => thetaR x * acceptedA j x ^ 2) | F_R] b +
            mu[base | F_R] b) =
          (mu[(fun x : B => coeff x * acceptedA j x) | F_R] b +
            mu[(fun x : B => thetaR x * acceptedA j x ^ 2) | F_R] b) +
            mu[base | F_R] b
        rw [hfirst]
        simp only [Pi.add_apply]
    _ = coeff b * mu[(fun x : B => acceptedA j x) | F_R] b +
          thetaR b * mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b + base b := by
          rw [hcoeffBridge, hcoeff, hthetaBridge, htheta, hbase]
          simp only [Pi.mul_apply]
    _ = reducedEnergyArmConditional rate rewards C_star C_h u t control0 j b := by
          dsimp [reducedEnergyArmConditional, coeff, base]
          rw [← hθ, ← hb]
          ring_nf

private theorem condExp_reducedSum :
    mu[(fun b : B =>
      ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j b) | F_R] =ᵐ[mu]
      (fun b : B =>
        ∑ j : Fin p.K,
          reducedEnergyArmConditional rate rewards C_star C_h u t control0 j b) := by
  have hPointwise :
      (fun b : B =>
        ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j b) =
      ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j := by
    funext b
    simp only [Finset.sum_apply]
  have hchange := condExp_congr_ae (m := F_R)
    (ae_of_all mu fun b => congrFun hPointwise b)
  have hsum := condExp_finsetSum
    (s := Finset.univ)
    (f := fun j : Fin p.K => reducedEnergyArm rate rewards C_star C_h u t control0 j)
    (by intro j hj; exact integrable_armReduced rate rewards C_star C_h u t control0 j)
    F_R
  have harm (j : Fin p.K) :=
    condExp_armReduced rate rewards C_star C_h u t control0 j
  have harmAll : ∀ᵐ b ∂mu, ∀ j : Fin p.K,
      mu[reducedEnergyArm rate rewards C_star C_h u t control0 j | F_R] b =
        reducedEnergyArmConditional rate rewards C_star C_h u t control0 j b := by
    apply ae_all_iff.mpr
    exact harm
  filter_upwards [hchange, hsum, harmAll] with b hchange hsum harmAll
  calc
    mu[(fun x : B =>
      ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j x) | F_R] b =
        mu[(∑ j : Fin p.K,
          reducedEnergyArm rate rewards C_star C_h u t control0 j) | F_R] b := hchange
    _ = ∑ j : Fin p.K,
          mu[reducedEnergyArm rate rewards C_star C_h u t control0 j | F_R] b := by
            simpa only [Finset.sum_apply] using hsum
    _ = ∑ j : Fin p.K,
          reducedEnergyArmConditional rate rewards C_star C_h u t control0 j b := by
          apply Finset.sum_congr rfl
          intro j hj
          exact harmAll j

private theorem measurableSet_G : MeasurableSet[F_R] G :=
  ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0

/-- The actual masked right hand side is integrable on the unnormalized
renewal pair law. -/
theorem integrable_maskedDriftBound :
    Integrable (fun b : B => Set.indicator G
      (fun b =>
        -(11 / 2 : ℝ) *
            (∑ j : Fin p.K, theta j b * backlog j b) +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) b) mu := by
  have hsum : Integrable (fun b : B =>
      ∑ j : Fin p.K, theta j b * backlog j b) mu := by
    simpa only [← Finset.sum_apply] using
      (integrable_finsetSum (Finset.univ : Finset (Fin p.K))
        (fun j hj =>
          ReferenceFirstCollectionRenewalQueueEnergy.integrable_thetaMinus_mul_bMinus
            rate rewards C_star C_h u t control0 j))
  have hraw : Integrable (fun b : B =>
      -(11 / 2 : ℝ) *
          (∑ j : Fin p.K, theta j b * backlog j b) +
        CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) mu := by
    have hsumScaled := hsum.const_mul (-(11 / 2 : ℝ))
    have hconst := integrable_const (μ := mu)
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ))
    have h := hsumScaled.add hconst
    refine h.congr ?_
    filter_upwards [] with b
    dsimp
    ring
  exact hraw.indicator (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0 G
    (measurableSet_G rate rewards C_star C_h u t control0))

/-- The conditional first-renewal energy step is bounded by the retained
complement readouts, with the whole right hand side stopped on `G_R`. -/
theorem ae_conditional_energy_step_complement_bound :
    mu[(fun b : B =>
      ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t b -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
          rate rewards C_star C_h u t control0 b) | F_R] ≤ᵐ[mu]
      Set.indicator G (fun b =>
        ∑ j : Fin p.K,
          (theta j b *
            ((-(15 / 2 : ℝ) +
                2 * chi b j * reward j) * backlog j b +
              chi b j * reward j ^ 2 / xi b j + 16 +
              chi b j * reward j / 2))) := by
  have hDiffInt :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_energyDifference
      rate rewards C_star C_h u t control0
  have hSums :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_weighted_energy_step_sums
      rate rewards C_star C_h u t control0
  have hReducedInt := hSums.2
  have hMaskInt := hReducedInt.indicator
    (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
      rate rewards C_star C_h u t control0 G
      (measurableSet_G rate rewards C_star C_h u t control0))
  have hmono := condExp_mono (m := F_R) hDiffInt hMaskInt
    (ReferenceFirstCollectionRenewalQueueEnergy.ae_weighted_energy_step
      rate rewards C_star C_h u t control0)
  have hmask := condExp_indicator hReducedInt
    (measurableSet_G rate rewards C_star C_h u t control0)
  have hsum := condExp_reducedSum rate rewards C_star C_h u t control0
  have hmasked :
      mu[(fun b : B => Set.indicator G
        (fun b =>
          ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j b) b) | F_R] =ᵐ[mu]
      Set.indicator G (fun b : B =>
        ∑ j : Fin p.K,
          reducedEnergyArmConditional rate rewards C_star C_h u t control0 j b) := by
    filter_upwards [hmask, hsum] with b hmask hsum
    by_cases hg : b ∈ G
    · rw [Set.indicator_of_mem hg]
      calc
        _ = Set.indicator G (fun x : B =>
            mu[(fun y : B =>
              ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j y)
              | F_R] x) b := hmask
        _ = mu[(fun x : B =>
            ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j x)
              | F_R] b := by simp [Set.indicator_of_mem hg]
        _ = ∑ j : Fin p.K,
              reducedEnergyArmConditional rate rewards C_star C_h u t control0 j b := hsum
    · have hzero :
          mu[(fun b : B => Set.indicator G
            (fun b =>
              ∑ j : Fin p.K, reducedEnergyArm rate rewards C_star C_h u t control0 j b) b)
            | F_R] b = 0 := by
        calc
          _ = Set.indicator G (fun x : B =>
                mu[(fun y : B =>
                  ∑ j : Fin p.K,
                    reducedEnergyArm rate rewards C_star C_h u t control0 j y) | F_R] x) b := hmask
          _ = 0 := by simp [Set.indicator_of_notMem hg]
      simpa [Set.indicator_of_notMem hg] using hzero
  have hfirst (j : Fin p.K) :=
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.condExp_acceptedA_bounds
      rate rewards C_star C_h u t control0 j
  have hsquare (j : Fin p.K) :=
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.condExp_acceptedA_sq_bounds
      rate rewards C_star C_h u t control0 j
  have hfirstAll : ∀ᵐ b ∂mu, ∀ j : Fin p.K,
      0 ≤ mu[(fun x : B => acceptedA j x) | F_R] b ∧
        (Set.indicator G (fun b => chi b j * (reward j - xi b j /
          (rate.eta.val * (D p : ℝ)))) b ≤
          mu[(fun x : B => acceptedA j x) | F_R] b ∧
        mu[(fun x : B => acceptedA j x) | F_R] b ≤
          Set.indicator G (fun b => chi b j * reward j) b) := by
    apply ae_all_iff.mpr
    exact hfirst
  have hsquareAll : ∀ᵐ b ∂mu, ∀ j : Fin p.K,
      0 ≤ mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b ∧
        mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b ≤
          Set.indicator G (fun b => chi b j * reward j ^ 2 / xi b j) b := by
    apply ae_all_iff.mpr
    exact hsquare
  have hχbounds (b : B) (j : Fin p.K) : 0 ≤ chi b j ∧ chi b j ≤ 1 := by
    dsimp [ReferenceFirstCollectionRenewalComplementMoments.chi]
    split_ifs <;> norm_num
  have hrbounds (j : Fin p.K) : 0 ≤ reward j ∧ reward j ≤ 1 := by
    change RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t j) ∈ Set.Icc (0 : ℝ) 1
    exact RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) (rewards t j)
  have hxiPos (b : B) (j : Fin p.K) : 0 < xi b j := by
    dsimp [ReferenceFirstCollectionRenewalComplementMoments.xi,
      ReferenceFirstCollectionRenewalComplementMoments.v]
    exact CanonicalRecordingRates.xi_pos p rate.eta.property _ j
  have hinfo := hmono.trans
    (hmasked.mono fun b h => le_of_eq h)
  filter_upwards [hinfo, hfirstAll, hsquareAll] with b hinfo hfirst hsquare
  by_cases hg : b ∈ G
  · rw [Set.indicator_of_mem hg]
    have hInfoG :
        mu[(fun x : B =>
          ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t x -
            ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
              rate rewards C_star C_h u t control0 x) | F_R] b ≤
        ∑ j : Fin p.K,
          (theta j b * (2 * backlog j b + 1 / 2) *
              mu[(fun x : B => acceptedA j x) | F_R] b +
            theta j b * mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b +
            (-(15 / 2 : ℝ)) * (theta j b * backlog j b) +
            16 * theta j b) := by
      simpa [Set.indicator_of_mem hg, reducedEnergyArmConditional] using hinfo
    have hterm (j : Fin p.K) :
        theta j b * (2 * backlog j b + 1 / 2) *
            mu[(fun x : B => acceptedA j x) | F_R] b +
          theta j b * mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b +
          (-(15 / 2 : ℝ)) * (theta j b * backlog j b) +
          16 * theta j b ≤
        theta j b *
          ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
            chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) := by
      have htheta :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
          rate rewards C_star C_h u t control0 j b
      have hbacklog :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
          rate rewards C_star C_h u t control0 j b
      have hχ := hχbounds b j
      have hr := hrbounds j
      have hxi := hxiPos b j
      have hceA : mu[(fun x : B => acceptedA j x) | F_R] b ≤ chi b j * reward j := by
        simpa [Set.indicator_of_mem hg] using (hfirst j).2.2
      have hceSq : mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b ≤
          chi b j * reward j ^ 2 / xi b j := by
        simpa [Set.indicator_of_mem hg] using (hsquare j).2
      have hcoef : 0 ≤ theta j b * (2 * backlog j b + 1 / 2) :=
        mul_nonneg htheta.1 (by positivity [hbacklog])
      have hmulA := mul_le_mul_of_nonneg_left hceA hcoef
      have hmulSq := mul_le_mul_of_nonneg_left hceSq htheta.1
      calc
        _ ≤ theta j b * (2 * backlog j b + 1 / 2) * (chi b j * reward j) +
            theta j b * (chi b j * reward j ^ 2 / xi b j) +
            (-(15 / 2 : ℝ)) * (theta j b * backlog j b) + 16 * theta j b := by
          linarith [hmulA, hmulSq]
        _ = theta j b *
            ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
              chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) := by
          ring
    have hsumTerms :
        (∑ j : Fin p.K,
          (theta j b * (2 * backlog j b + 1 / 2) *
              mu[(fun x : B => acceptedA j x) | F_R] b +
            theta j b * mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b +
            (-(15 / 2 : ℝ)) * (theta j b * backlog j b) + 16 * theta j b)) ≤
        ∑ j : Fin p.K,
          theta j b *
            ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
              chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) :=
      Finset.sum_le_sum (fun j hj => hterm j)
    calc
      _ ≤ ∑ j : Fin p.K,
            (theta j b * (2 * backlog j b + 1 / 2) *
                mu[(fun x : B => acceptedA j x) | F_R] b +
              theta j b * mu[(fun x : B => (acceptedA j x) ^ 2) | F_R] b +
              (-(15 / 2 : ℝ)) * (theta j b * backlog j b) + 16 * theta j b) := hInfoG
      _ ≤ ∑ j : Fin p.K,
            theta j b *
              ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
                chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) := hsumTerms
  · simpa [Set.indicator, hg] using hinfo

/-- The principal conditional weighted queue drift on the same renewal pair
law and exact retained-coordinate field. -/
theorem ae_conditionalWeightedEnergyDrift :
    mu[(fun b : B =>
      ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t b -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
          rate rewards C_star C_h u t control0 b) | F_R] ≤ᵐ[mu]
      Set.indicator G (fun b =>
        -(11 / 2 : ℝ) *
            (∑ j : Fin p.K, theta j b * backlog j b) +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
  have hInfo := ae_conditional_energy_step_complement_bound
    rate rewards C_star C_h u t control0
  have hRate :=
    ReferenceFirstCollectionRenewalQueueEnergy.ae_sum_thetaMinus_div_actualRenewalRate_le_R
      rate rewards C_star C_h u t control0
  have hSumTheta :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.sum_thetaMinus
      rate rewards C_star C_h u t control0
  have hChiBounds (b : B) (j : Fin p.K) : 0 ≤ chi b j ∧ chi b j ≤ 1 := by
    dsimp [ReferenceFirstCollectionRenewalComplementMoments.chi]
    split_ifs <;> norm_num
  have hRewardBounds (j : Fin p.K) : 0 ≤ reward j ∧ reward j ≤ 1 := by
    change RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
      (rewards t j) ∈ Set.Icc (0 : ℝ) 1
    exact RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) (rewards t j)
  filter_upwards [hInfo, hRate] with b hInfo hRate
  by_cases hg : b ∈ G
  · rw [Set.indicator_of_mem hg]
    have hInfoG :
        mu[(fun x : B =>
          ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t x -
            ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
              rate rewards C_star C_h u t control0 x) | F_R] b ≤
        ∑ j : Fin p.K,
          theta j b *
            ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
              chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) := by
      simpa [Set.indicator_of_mem hg] using hInfo
    have hterm (j : Fin p.K) :
        theta j b *
          ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
            chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) ≤
        -(11 / 2 : ℝ) * (theta j b * backlog j b) +
          theta j b / xi b j + (33 / 2 : ℝ) * theta j b := by
      have hTheta :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
          rate rewards C_star C_h u t control0 j b
      have hBacklog :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
          rate rewards C_star C_h u t control0 j b
      have hChi := hChiBounds b j
      have hReward := hRewardBounds j
      have hXi : 0 < xi b j := by
        dsimp [ReferenceFirstCollectionRenewalComplementMoments.xi,
          ReferenceFirstCollectionRenewalComplementMoments.v]
        exact CanonicalRecordingRates.xi_pos p rate.eta.property _ j
      have hChiReward : chi b j * reward j ≤ 1 := by
        calc
          chi b j * reward j ≤ 1 * reward j :=
            mul_le_mul_of_nonneg_right hChi.2 hReward.1
          _ ≤ 1 := by linarith
      have hRewardSq : reward j ^ 2 ≤ 1 := by nlinarith
      have hChiRewardSq : chi b j * reward j ^ 2 / xi b j ≤ 1 / xi b j := by
        have hdivNonneg : 0 ≤ reward j ^ 2 / xi b j :=
          div_nonneg (sq_nonneg _) hXi.le
        calc
          chi b j * reward j ^ 2 / xi b j =
              chi b j * (reward j ^ 2 / xi b j) := by ring
          _ ≤ 1 * (reward j ^ 2 / xi b j) :=
            mul_le_mul_of_nonneg_right hChi.2 hdivNonneg
          _ ≤ 1 / xi b j := by
            simpa using (div_le_div_of_nonneg_right hRewardSq hXi.le)
      have hCoeff :
          (-(15 / 2 : ℝ) + 2 * chi b j * reward j) ≤ -(11 / 2 : ℝ) := by
        linarith
      have hLinear := mul_le_mul_of_nonneg_right hCoeff hBacklog
      have hConstant : 16 + chi b j * reward j / 2 ≤ 33 / 2 := by
        linarith
      have hInside :
          (-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
            chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2 ≤
          -(11 / 2 : ℝ) * backlog j b + 1 / xi b j + 33 / 2 := by
        linarith [hLinear, hChiRewardSq, hConstant]
      calc
        _ ≤ theta j b *
            (-(11 / 2 : ℝ) * backlog j b + 1 / xi b j + 33 / 2) :=
          mul_le_mul_of_nonneg_left hInside hTheta.1
        _ = -(11 / 2 : ℝ) * (theta j b * backlog j b) +
            theta j b / xi b j + (33 / 2 : ℝ) * theta j b := by ring
    have hsumTerms := Finset.sum_le_sum (s := Finset.univ)
      (fun j hj => hterm j)
    have hsumRewrite :
        (∑ j : Fin p.K,
          (-(11 / 2 : ℝ) * (theta j b * backlog j b) +
            theta j b / xi b j + (33 / 2 : ℝ) * theta j b)) =
        -(11 / 2 : ℝ) * (∑ j : Fin p.K, theta j b * backlog j b) +
          (∑ j : Fin p.K, theta j b / xi b j) +
          (33 / 2 : ℝ) * (p.m : ℝ) := by
      calc
        _ = (∑ j : Fin p.K, -(11 / 2 : ℝ) * (theta j b * backlog j b)) +
            (∑ j : Fin p.K, theta j b / xi b j) +
            (∑ j : Fin p.K, (33 / 2 : ℝ) * theta j b) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = -(11 / 2 : ℝ) * (∑ j : Fin p.K, theta j b * backlog j b) +
            (∑ j : Fin p.K, theta j b / xi b j) +
            (33 / 2 : ℝ) * (p.m : ℝ) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hSumTheta]
    have hRateAt := hRate hg
    calc
      _ ≤ ∑ j : Fin p.K,
            theta j b *
              ((-(15 / 2 : ℝ) + 2 * chi b j * reward j) * backlog j b +
                chi b j * reward j ^ 2 / xi b j + 16 + chi b j * reward j / 2) := hInfoG
      _ ≤ ∑ j : Fin p.K,
            (-(11 / 2 : ℝ) * (theta j b * backlog j b) +
              theta j b / xi b j + (33 / 2 : ℝ) * theta j b) := hsumTerms
      _ = -(11 / 2 : ℝ) * (∑ j : Fin p.K, theta j b * backlog j b) +
            (∑ j : Fin p.K, theta j b / xi b j) +
            (33 / 2 : ℝ) * (p.m : ℝ) := hsumRewrite
      _ ≤ -(11 / 2 : ℝ) * (∑ j : Fin p.K, theta j b * backlog j b) +
            CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
          linarith
  · simpa [Set.indicator, hg] using hInfo

/-- The corresponding set-integral estimate for every measurable subset of
the exact retained-control field. -/
theorem setIntegral_conditionalWeightedEnergyDrift
    (Hset : Set B) (hH : MeasurableSet[F_R] Hset) :
    ∫ b in Hset,
      (ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t b -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
          rate rewards C_star C_h u t control0 b) ∂mu ≤
    ∫ b in Hset,
      Set.indicator G (fun b =>
        -(11 / 2 : ℝ) *
            (∑ j : Fin p.K, theta j b * backlog j b) +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) b ∂mu := by
  have hDiffInt :=
    ReferenceFirstCollectionRenewalQueueEnergy.integrable_energyDifference
      rate rewards C_star C_h u t control0
  have hRhsInt := integrable_maskedDriftBound rate rewards C_star C_h u t control0
  have hCeInt : Integrable
      (mu[(fun b : B =>
        ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t b -
          ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
            rate rewards C_star C_h u t control0 b) | F_R]) mu :=
    integrable_condExp
  calc
    _ = ∫ b in Hset,
        mu[(fun b : B =>
          ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t b -
            ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
              rate rewards C_star C_h u t control0 b) | F_R] b ∂mu := by
      symm
      exact setIntegral_condExp
        (ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
          rate rewards C_star C_h u t control0) hDiffInt hH
    _ ≤ ∫ b in Hset,
        Set.indicator G (fun b =>
          -(11 / 2 : ℝ) *
              (∑ j : Fin p.K, theta j b * backlog j b) +
            CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) b ∂mu :=
      setIntegral_mono_ae hCeInt.integrableOn hRhsInt.integrableOn
        (ae_conditionalWeightedEnergyDrift rate rewards C_star C_h u t control0)

/-- The total integral estimate on the same original pair law. -/
theorem integral_conditionalWeightedEnergyDrift :
    ∫ b,
      (ReferenceFirstCollectionRenewalQueueEnergy.VPlus rate rewards C_star C_h u t b -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
          rate rewards C_star C_h u t control0 b) ∂mu ≤
    ∫ b,
      Set.indicator G (fun b =>
        -(11 / 2 : ℝ) *
            (∑ j : Fin p.K, theta j b * backlog j b) +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) b ∂mu := by
  simpa only [setIntegral_univ] using
    (setIntegral_conditionalWeightedEnergyDrift rate rewards C_star C_h u t control0
      Set.univ MeasurableSet.univ)

end Bandits.Support.ReferenceFirstCollectionRenewalConditionalWeightedDrift

end
