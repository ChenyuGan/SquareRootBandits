/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFutureWeightedEnergyStep
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope

import Mathlib.Tactic

/-!
# Supported strict-future weighted backlog budget

This module sums the actual supported future-date energy estimates on the
original first-renewal source law. Consecutive calendar dates are retained,
and loss of the optional queue support is charged as a nonnegative energy
loss between adjacent dates.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MeasureTheory
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget

open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureExponentialIncrement
open ReferenceFirstCollectionRenewalFutureWeightedEnergyStep

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t

/-- The literal consecutive calendar dates strictly after the first
post-renewal date and before the horizon. -/
def futureCalendarDates : Finset ℕ := Finset.Ico (t.val + 2) p.T

/-- The actual future gate at natural calendar index `n`; indices outside the
physical horizon or the strict-future region have empty gate. -/
def futureGateAt (n : ℕ) : Set Z :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t ⟨n, hn⟩ hf
    else ∅
  else ∅

/-- The accepted supported backlog at a natural calendar index. -/
def futureBacklogAt (n : ℕ) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog
        rate rewards C_star C_h u t ⟨n, hn⟩ hf
    else 0
  else 0

/-- The backlog charged only on the actual exponential future gate. -/
def supportedFutureBacklogAt (n : ℕ) : Z → ℝ :=
  (futureGateAt rate rewards C_star C_h u t n).indicator
    (futureBacklogAt rate rewards C_star C_h u t n)

/-- The original first-renewal source mass of the actual gate at one
calendar date. -/
def futureGateMassAt (n : ℕ) : ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t ⟨n, hn⟩ hf)
    else 0
  else 0

/-- Incoming energy at a natural future date, using the exact accepted
first-renewal readout. -/
def futureEnergyMinusAt (n : ℕ) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
        rate rewards C_star C_h u t ⟨n, hn⟩ hf
    else 0
  else 0

/-- Outgoing energy at a natural future date, using its adjacent optional
readout on the current support. -/
def futureEnergyPlusAt (n : ℕ) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
        rate rewards C_star C_h u t ⟨n, hn⟩ hf
    else 0
  else 0

/-- Energy lost between two consecutive future dates. The next-date energy is
the actual localized energy, so support loss is retained as a charge. -/
def futureAdjacentLossAt (n : ℕ) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      if hn' : n + 1 < p.T then
        let hf' : t.val + 1 < n + 1 := by omega
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
            rate rewards C_star C_h u t ⟨n, hn⟩ hf -
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
            rate rewards C_star C_h u t ⟨n + 1, hn'⟩ hf'
      else 0
    else 0
  else 0

/-- Future dates which have a genuine next physical date still below `T`. -/
def futureAdjacentLossDates : Finset ℕ := Finset.Ico (t.val + 2) (p.T - 1)

/-- The incoming boundary energy at date `t+2`, or zero when the strict-future
calendar interval is empty. -/
def futureInitialEnergy : Z → ℝ :=
  if h : t.val + 2 < p.T then
    let hf : t.val + 1 < (⟨t.val + 2, h⟩ : Fin p.T).val := by
      change t.val + 1 < t.val + 2
      omega
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
      rate rewards C_star C_h u t ⟨t.val + 2, h⟩ hf
  else 0

/-- The terminal outgoing energy at calendar date `T-1`, or zero when there is
no strict-future date. Its optional readout is at natural index `T`. -/
def futureTerminalEnergy : Z → ℝ :=
  if h : t.val + 2 < p.T then
    let q : Fin p.T := ⟨p.T - 1, by
      have hT := p.one_le_T
      omega⟩
    have hq : t.val + 1 < q.val := by
      change t.val + 1 < p.T - 1
      omega
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
      rate rewards C_star C_h u t q hq
  else 0

/-- Total supported backlog over the original consecutive future dates. -/
def supportedFutureBacklog : Z → ℝ :=
  fun z => ∑ n ∈ futureCalendarDates t,
    supportedFutureBacklogAt rate rewards C_star C_h u t n z

/-- Total actual gate mass over the same future dates and original source law. -/
def futureGateMass : ℝ :=
  ∑ n ∈ futureCalendarDates t,
    futureGateMassAt rate rewards C_star C_h u t n

/-- Sum of the actual adjacent support-loss energies, on dates whose next
calendar date is still strictly before `T`. -/
def futureAdjacentLoss : Z → ℝ :=
  fun z => ∑ n ∈ futureAdjacentLossDates t,
    futureAdjacentLossAt rate rewards C_star C_h u t n z

private theorem ae_futureRecordingCost_le_R
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ∀ᵐ z : Z ∂ν,
      z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture →
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
        rate rewards C_star C_h u t q hfuture z ≤ CanonicalRecordingRates.R p := by
  filter_upwards [ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope.ae_Gfuture_actual_numerical_weight_envelope
    rate rewards C_star C_h u t control0 q hfuture] with z hwitness
  intro hz
  obtain ⟨r, data, xi, cell, hread, _, _, _, hparameters, _, _, _, _, _, _, hsum⟩ :=
    hwitness hz
  have hsupport :=
    ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
      rate rewards C_star C_h u t q hfuture hz
  have htheta (j : Fin p.K) :
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z =
      ProductSetLaw.theta p.m
        (fun i => (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (r.1 i).1) j := by
    simp only [ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus,
      Set.indicator_of_mem hsupport, hread]
    simp only [Option.elim_some]
    simp [ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters,
      ScoreWeights.scoreWeight,
      ReferenceFirstLaunchNumericalCell.queueParameters]
  have hcost :
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
        rate rewards C_star C_h u t q hfuture z =
      ∑ j : Fin p.K,
        ProductSetLaw.theta p.m
          (fun i => (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (r.1 i).1) j /
          xi j := by
    rw [ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost,
      hparameters]
    simp_rw [htheta]
  rw [hcost]
  exact hsum

/-- The strict-future one-date integral estimate with the actual canonical
rate envelope, derived on the unchanged renewal source law. -/
theorem futureWeightedEnergy_integral_R
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    (11 / 2 : ℝ) * (∫ z,
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog
            rate rewards C_star C_h u t q hfuture) z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t q hfuture) +
        (∫ z, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
          rate rewards C_star C_h u t q hfuture z ∂ν) -
        ∫ z, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
          rate rewards C_star C_h u t q hfuture z ∂ν := by
  let G := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let C := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
    rate rewards C_star C_h u t q hfuture
  let c : ℝ := (33 / 2 : ℝ) * p.m
  have hG := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hG' := hle _ hG
  have hC :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureRecordingCost
      rate rewards C_star C_h u t q hfuture control0
  have hleft : Integrable (G.indicator (fun z => C z + c)) ν := by
    exact (hC.add (integrable_const c)).indicator hG'
  have hright : Integrable (G.indicator (fun _ : Z => CanonicalRecordingRates.R p + c)) ν := by
    exact (integrable_const (CanonicalRecordingRates.R p + c)).indicator hG'
  have hcost : ∀ᵐ z ∂ν,
      G.indicator (fun z => C z + c) z ≤
        G.indicator (fun _ : Z => CanonicalRecordingRates.R p + c) z := by
    filter_upwards [ae_futureRecordingCost_le_R rate rewards C_star C_h u t
      control0 q hfuture] with z hz
    by_cases hzg : z ∈ G
    · simp only [Set.indicator_of_mem hzg]
      have hbound := hz hzg
      dsimp [C, c]
      linarith only [hbound]
    · simp only [Set.indicator_of_notMem hzg]
      exact le_rfl
  have hcostInt := integral_mono_ae hleft hright hcost
  rw [integral_indicator_const _ hG', smul_eq_mul] at hcostInt
  change (∫ z, G.indicator (fun z => C z + c) z ∂ν) ≤
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real G * (CanonicalRecordingRates.R p + c) at hcostInt
  have hstep :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergy_integral
      rate rewards C_star C_h u t q hfuture control0
  have hreplace : (∫ z,
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun z => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
          rate rewards C_star C_h u t q hfuture z + (33 / 2 : ℝ) * p.m) z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture) := by
    simpa [G, C, c, mul_comm] using hcostInt
  linarith only [hstep, hreplace]

private theorem sum_Ico_energy_sub_telescope
    (f g : ℕ → ℝ) (a b : ℕ) (hab : a < b) :
    (∑ n ∈ Finset.Ico a b, (f n - g n)) =
      f a - g (b - 1) -
        ∑ n ∈ Finset.Ico a (b - 1), (g n - f (n + 1)) := by
  induction b generalizing a with
  | zero => omega
  | succ b ih =>
      by_cases hae : a = b
      · subst a
        rw [Finset.sum_Ico_succ_top le_rfl]
        simp [Finset.Ico_eq_empty_of_le]
      · have hab' : a < b := by omega
        have hab0 : a ≤ b - 1 := Nat.le_sub_one_of_lt hab'
        have hbsub : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
        rw [Finset.sum_Ico_succ_top (Nat.le_of_lt hab')]
        have hloss :
            (∑ n ∈ Finset.Ico a b, (g n - f (n + 1))) =
              (∑ n ∈ Finset.Ico a (b - 1), (g n - f (n + 1))) +
                (g (b - 1) - f b) := by
          calc
            (∑ n ∈ Finset.Ico a b, (g n - f (n + 1))) =
                ∑ n ∈ Finset.Ico a (b - 1 + 1), (g n - f (n + 1)) := by rw [hbsub]
            _ = (∑ n ∈ Finset.Ico a (b - 1), (g n - f (n + 1))) +
                (g (b - 1) - f ((b - 1) + 1)) :=
                  Finset.sum_Ico_succ_top hab0 (fun n => g n - f (n + 1))
            _ = _ := by rw [hbsub]
        have hlast : b + 1 - 1 = b := by omega
        rw [hlast, hloss, ih a hab']
        ring

/-- Pathwise boundary/loss identity for the actual future energy readouts.
The initial `t+2` potential is kept as the incoming boundary. -/
theorem futureEnergy_boundary_loss_identity (z : Z) :
    (∑ n ∈ futureCalendarDates t,
      (futureEnergyMinusAt rate rewards C_star C_h u t n z -
        futureEnergyPlusAt rate rewards C_star C_h u t n z)) =
      futureInitialEnergy rate rewards C_star C_h u t z -
        futureTerminalEnergy rate rewards C_star C_h u t z -
          futureAdjacentLoss rate rewards C_star C_h u t z := by
  let a := t.val + 2
  by_cases ha : a < p.T
  · have htelescope := sum_Ico_energy_sub_telescope
      (fun n => futureEnergyMinusAt rate rewards C_star C_h u t n z)
      (fun n => futureEnergyPlusAt rate rewards C_star C_h u t n z)
      a p.T ha
    have hleft :
        (∑ n ∈ futureCalendarDates t,
          (futureEnergyMinusAt rate rewards C_star C_h u t n z -
            futureEnergyPlusAt rate rewards C_star C_h u t n z)) =
        ∑ n ∈ Finset.Ico a p.T,
          (futureEnergyMinusAt rate rewards C_star C_h u t n z -
            futureEnergyPlusAt rate rewards C_star C_h u t n z) := by
      rfl
    have hinitial :
        futureInitialEnergy rate rewards C_star C_h u t z =
          futureEnergyMinusAt rate rewards C_star C_h u t a z := by
      simp [futureInitialEnergy, futureEnergyMinusAt, a, ha]
    have hterminal :
        futureTerminalEnergy rate rewards C_star C_h u t z =
          futureEnergyPlusAt rate rewards C_star C_h u t (p.T - 1) z := by
      have hT := p.one_le_T
      have hlast : p.T - 1 < p.T := by omega
      have hfuture : t.val + 1 < p.T - 1 := by omega
      simp [futureTerminalEnergy, futureEnergyPlusAt, a, ha, hlast, hfuture]
    have hloss :
        futureAdjacentLoss rate rewards C_star C_h u t z =
          ∑ n ∈ Finset.Ico a (p.T - 1),
            (futureEnergyPlusAt rate rewards C_star C_h u t n z -
              futureEnergyMinusAt rate rewards C_star C_h u t (n + 1) z) := by
      unfold futureAdjacentLoss
      change (∑ n ∈ Finset.Ico (t.val + 2) (p.T - 1),
          futureAdjacentLossAt rate rewards C_star C_h u t n z) = _
      apply Finset.sum_congr rfl
      intro n hn
      have hnlt : n < p.T := by
        have := Finset.mem_Ico.mp hn
        omega
      have hn' : n + 1 < p.T := by
        have := Finset.mem_Ico.mp hn
        omega
      have hf : t.val + 1 < n := by
        have := Finset.mem_Ico.mp hn
        omega
      have hfn : t.val + 1 < n + 1 := by omega
      simp [futureAdjacentLossAt, futureEnergyPlusAt,
        futureEnergyMinusAt, hnlt, hn', hf, hfn]
    rw [hleft, htelescope, hinitial, hterminal, hloss]
  · have hle : p.T ≤ a := Nat.not_lt.mp ha
    have hle' : p.T - 1 ≤ a := by omega
    have hnot : ¬ t.val + 2 < p.T := by simpa [a] using ha
    simp [futureCalendarDates, futureAdjacentLossDates, futureAdjacentLoss,
      futureInitialEnergy, futureTerminalEnergy, a, hle, hle', hnot]

/-- Each actual adjacent support loss is nonnegative. -/
theorem futureAdjacentLossAt_nonneg (n : ℕ) (hn : n ∈ futureAdjacentLossDates t) (z : Z) :
    0 ≤ futureAdjacentLossAt rate rewards C_star C_h u t n z := by
  have hn' := Finset.mem_Ico.mp hn
  have hn_lt : n < p.T := by omega
  have hnnext : n + 1 < p.T := by omega
  have hf : t.val + 1 < n := by omega
  have hfnext : t.val + 1 < n + 1 := by omega
  have hle :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergy_adjacent_le
      rate rewards C_star C_h u t ⟨n, hn_lt⟩ hf ⟨n + 1, hnnext⟩ rfl hfnext z
  simpa [futureAdjacentLossAt, hn_lt, hf, hnnext,
    futureEnergyPlusAt, futureEnergyMinusAt] using sub_nonneg.mpr hle

/-- On next-date support, the loss vanishes because the accepted optional
readout is shared by the adjacent energies. -/
theorem futureAdjacentLossAt_zero_of_next_support (n : ℕ)
    (hn : n ∈ futureAdjacentLossDates t)
    (hnnext : n + 1 < p.T)
    (hfutureNext : t.val + 1 < n + 1)
    (z : Z)
    (hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t ⟨n + 1, hnnext⟩ hfutureNext) :
    futureAdjacentLossAt rate rewards C_star C_h u t n z = 0 := by
  have hn' := Finset.mem_Ico.mp hn
  have hn_lt : n < p.T := by omega
  have hf : t.val + 1 < n := by omega
  have hfnext : t.val + 1 < n + 1 := hfutureNext
  have hadj : (⟨n + 1, hnnext⟩ : Fin p.T).val = (⟨n, hn_lt⟩ : Fin p.T).val + 1 := rfl
  have heq :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergy_adjacent
      rate rewards C_star C_h u t ⟨n, hn_lt⟩ hf ⟨n + 1, hnnext⟩ hadj hfnext z hz
  simp [futureAdjacentLossAt, hn_lt, hf, hnnext, heq]

/-- The total supported backlog has finite-source integrability, proved from
the accepted one-date measurability and integrability facts. -/
theorem integrable_supportedFutureBacklog
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (supportedFutureBacklog rate rewards C_star C_h u t) ν := by
  unfold supportedFutureBacklog
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (futureCalendarDates t)
      (f := fun n z => supportedFutureBacklogAt rate rewards C_star C_h u t n z)
      (fun n hn => by
      have hn' := Finset.mem_Ico.mp hn
      have hq : n < p.T := hn'.2
      have hf : t.val + 1 < n := by omega
      have hG0 := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
        rate rewards C_star C_h u t ⟨n, hq⟩ hf control0
      have htq : t.val < (⟨n, hq⟩ : Fin p.T).val := by
        change t.val < n
        omega
      have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
        rate rewards C_star C_h u t control0 ⟨n, hq⟩ htq
      have hG := hle _ hG0
      simpa [supportedFutureBacklogAt, futureGateAt, futureBacklogAt, hq, hf] using
        (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedBacklog
          rate rewards C_star C_h u t ⟨n, hq⟩ hf control0).indicator hG))

private theorem integrable_futureEnergyMinusAt
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable (futureEnergyMinusAt rate rewards C_star C_h u t n) ν := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · simpa [futureEnergyMinusAt, hq, hf] using
        (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
          rate rewards C_star C_h u t ⟨n, hq⟩ hf control0)
    · simp [futureEnergyMinusAt, hq, hf]
  · simp [futureEnergyMinusAt, hq]

private theorem integrable_futureEnergyPlusAt
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable (futureEnergyPlusAt rate rewards C_star C_h u t n) ν := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · simpa [futureEnergyPlusAt, hq, hf] using
        (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
          rate rewards C_star C_h u t ⟨n, hq⟩ hf control0)
    · simp [futureEnergyPlusAt, hq, hf]
  · simp [futureEnergyPlusAt, hq]

private theorem integrable_futureAdjacentLossAt
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable (futureAdjacentLossAt rate rewards C_star C_h u t n) ν := by
  by_cases hq : n < p.T
  · by_cases hf : t.val + 1 < n
    · by_cases hnext : n + 1 < p.T
      · have hplus :=
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
            rate rewards C_star C_h u t ⟨n, hq⟩ hf control0
        let qnext : Fin p.T := ⟨n + 1, hnext⟩
        have hfnext : t.val + 1 < qnext.val := by
          simp only [qnext]
          omega
        have hminus :=
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
            rate rewards C_star C_h u t qnext hfnext control0
        simpa [futureAdjacentLossAt, hq, hf, hnext] using hplus.sub hminus
      · simp [futureAdjacentLossAt, hq, hf, hnext]
    · simp [futureAdjacentLossAt, hq, hf]
  · simp [futureAdjacentLossAt, hq]

private theorem integrable_futureInitialEnergy
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (futureInitialEnergy rate rewards C_star C_h u t) ν := by
  by_cases h : t.val + 2 < p.T
  · have hf : t.val + 1 < (⟨t.val + 2, h⟩ : Fin p.T).val := by
      change t.val + 1 < t.val + 2
      omega
    simpa [futureInitialEnergy, h] using
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
        rate rewards C_star C_h u t ⟨t.val + 2, h⟩ hf control0)
  · simp [futureInitialEnergy, h]

private theorem integrable_futureTerminalEnergy
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (futureTerminalEnergy rate rewards C_star C_h u t) ν := by
  by_cases h : t.val + 2 < p.T
  · have hT := p.one_le_T
    let q : Fin p.T := ⟨p.T - 1, by omega⟩
    have hf : t.val + 1 < q.val := by
      change t.val + 1 < p.T - 1
      omega
    simpa [futureTerminalEnergy, h, q] using
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
        rate rewards C_star C_h u t q hf control0)
  · simp [futureTerminalEnergy, h]

private theorem integrable_supportedFutureEnergyMinus
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun z =>
      ∑ n ∈ futureCalendarDates t,
        futureEnergyMinusAt rate rewards C_star C_h u t n z) ν := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (futureCalendarDates t)
      (fun n hn => integrable_futureEnergyMinusAt rate rewards C_star C_h u t control0 n))

private theorem integrable_supportedFutureEnergyPlus
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun z =>
      ∑ n ∈ futureCalendarDates t,
        futureEnergyPlusAt rate rewards C_star C_h u t n z) ν := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (futureCalendarDates t)
      (fun n hn => integrable_futureEnergyPlusAt rate rewards C_star C_h u t control0 n))

private theorem integrable_futureAdjacentLoss
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (futureAdjacentLoss rate rewards C_star C_h u t) ν := by
  unfold futureAdjacentLoss
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (futureAdjacentLossDates t)
      (f := fun n z => futureAdjacentLossAt rate rewards C_star C_h u t n z)
      (fun n hn => integrable_futureAdjacentLossAt rate rewards C_star C_h u t control0 n))

/-- Total integrability of the supported strict-future backlog. -/
theorem integrable_total_supported_future_backlog
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (supportedFutureBacklog rate rewards C_star C_h u t) ν :=
  integrable_supportedFutureBacklog rate rewards C_star C_h u t control0

/-- The source-law boundary/loss identity integrates with every term
integrable on the original, possibly zero, renewal measure. -/
private theorem integral_futureEnergy_boundary_loss_identity
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z, (∑ n ∈ futureCalendarDates t,
      (futureEnergyMinusAt rate rewards C_star C_h u t n z -
        futureEnergyPlusAt rate rewards C_star C_h u t n z)) ∂ν) =
      (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
        (∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) -
          ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
  have hpath := futureEnergy_boundary_loss_identity rate rewards C_star C_h u t
  have hminus := integrable_supportedFutureEnergyMinus rate rewards C_star C_h u t control0
  have hplus := integrable_supportedFutureEnergyPlus rate rewards C_star C_h u t control0
  have hinitial := integrable_futureInitialEnergy rate rewards C_star C_h u t control0
  have hterminal := integrable_futureTerminalEnergy rate rewards C_star C_h u t control0
  have hloss := integrable_futureAdjacentLoss rate rewards C_star C_h u t control0
  calc
    (∫ z, (∑ n ∈ futureCalendarDates t,
        (futureEnergyMinusAt rate rewards C_star C_h u t n z -
          futureEnergyPlusAt rate rewards C_star C_h u t n z)) ∂ν) =
        ∫ z, ((∑ n ∈ futureCalendarDates t,
          futureEnergyMinusAt rate rewards C_star C_h u t n z) -
          ∑ n ∈ futureCalendarDates t,
            futureEnergyPlusAt rate rewards C_star C_h u t n z) ∂ν := by
      congr 1
      funext z
      rw [Finset.sum_sub_distrib]
    _ = ∫ z, (futureInitialEnergy rate rewards C_star C_h u t z -
          futureTerminalEnergy rate rewards C_star C_h u t z -
            futureAdjacentLoss rate rewards C_star C_h u t z) ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← Finset.sum_sub_distrib]
      exact hpath z
    _ = (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
          (∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) -
            ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
      calc
        _ = (∫ z, futureInitialEnergy rate rewards C_star C_h u t z -
                futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) -
              ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν :=
              integral_sub (hinitial.sub hterminal) hloss
        _ = _ := by rw [integral_sub hinitial hterminal]

/-- The strict-future supported budget, retaining the incoming boundary
potential, terminal outgoing potential, and every adjacent support loss. -/
theorem supported_future_weighted_budget
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) * (∫ z, supportedFutureBacklog rate rewards C_star C_h u t z ∂ν) +
        (∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) +
        (∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          futureGateMass rate rewards C_star C_h u t +
        (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) := by
  have hsum :
      (∑ n ∈ futureCalendarDates t,
        (11 / 2 : ℝ) *
          (∫ z, supportedFutureBacklogAt rate rewards C_star C_h u t n z ∂ν)) ≤
      ∑ n ∈ futureCalendarDates t,
        ((CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
            futureGateMassAt rate rewards C_star C_h u t n +
          ((∫ z, futureEnergyMinusAt rate rewards C_star C_h u t n z ∂ν) -
            ∫ z, futureEnergyPlusAt rate rewards C_star C_h u t n z ∂ν)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hq : n < p.T := hn'.2
    have hf : t.val + 1 < n := by omega
    have h := futureWeightedEnergy_integral_R rate rewards C_star C_h u t control0
      ⟨n, hq⟩ hf
    have h' : (11 / 2 : ℝ) *
          (∫ z, supportedFutureBacklogAt rate rewards C_star C_h u t n z ∂ν) ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
            futureGateMassAt rate rewards C_star C_h u t n +
          (∫ z, futureEnergyMinusAt rate rewards C_star C_h u t n z ∂ν) -
            ∫ z, futureEnergyPlusAt rate rewards C_star C_h u t n z ∂ν := by
      simpa [supportedFutureBacklogAt, futureGateAt, futureBacklogAt,
        futureGateMassAt, futureEnergyMinusAt, futureEnergyPlusAt, hq, hf] using h
    linarith only [h']
  have hbackSum := integral_finsetSum (futureCalendarDates t)
    (f := fun n z => supportedFutureBacklogAt rate rewards C_star C_h u t n z)
    (fun n hn => by
      have hn' := Finset.mem_Ico.mp hn
      have hq : n < p.T := hn'.2
      have hf : t.val + 1 < n := by omega
      have htq : t.val < (⟨n, hq⟩ : Fin p.T).val := by
        change t.val < n
        omega
      have hG0 := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
        rate rewards C_star C_h u t ⟨n, hq⟩ hf control0
      have hG := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
        rate rewards C_star C_h u t control0 ⟨n, hq⟩ htq _ hG0
      simpa [supportedFutureBacklogAt, futureGateAt, futureBacklogAt, hq, hf] using
        ((ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedBacklog
          rate rewards C_star C_h u t ⟨n, hq⟩ hf control0).indicator hG))
  have hminusSum := integral_finsetSum
    (futureCalendarDates t)
    (fun n hn => integrable_futureEnergyMinusAt rate rewards C_star C_h u t control0 n)
  have hplusSum := integral_finsetSum
    (futureCalendarDates t)
    (fun n hn => integrable_futureEnergyPlusAt rate rewards C_star C_h u t control0 n)
  have henergy := integral_futureEnergy_boundary_loss_identity
    rate rewards C_star C_h u t control0
  have hminus := integrable_supportedFutureEnergyMinus rate rewards C_star C_h u t control0
  have hplus := integrable_supportedFutureEnergyPlus rate rewards C_star C_h u t control0
  have hsumEnergy :
      (∑ n ∈ futureCalendarDates t,
        ((∫ z, futureEnergyMinusAt rate rewards C_star C_h u t n z ∂ν) -
          ∫ z, futureEnergyPlusAt rate rewards C_star C_h u t n z ∂ν)) =
      (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
        (∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) -
          ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
    calc
      _ = (∑ n ∈ futureCalendarDates t,
            ∫ z, futureEnergyMinusAt rate rewards C_star C_h u t n z ∂ν) -
          ∑ n ∈ futureCalendarDates t,
            ∫ z, futureEnergyPlusAt rate rewards C_star C_h u t n z ∂ν := by
          rw [Finset.sum_sub_distrib]
      _ = (∫ z, ∑ n ∈ futureCalendarDates t,
            futureEnergyMinusAt rate rewards C_star C_h u t n z ∂ν) -
          ∫ z, ∑ n ∈ futureCalendarDates t,
            futureEnergyPlusAt rate rewards C_star C_h u t n z ∂ν := by
          rw [← hminusSum, ← hplusSum]
      _ = ∫ z, ((∑ n ∈ futureCalendarDates t,
            futureEnergyMinusAt rate rewards C_star C_h u t n z) -
          ∑ n ∈ futureCalendarDates t,
            futureEnergyPlusAt rate rewards C_star C_h u t n z) ∂ν := by
          rw [← integral_sub hminus hplus]
      _ = ∫ z, ∑ n ∈ futureCalendarDates t,
            (futureEnergyMinusAt rate rewards C_star C_h u t n z -
              futureEnergyPlusAt rate rewards C_star C_h u t n z) ∂ν := by
          congr 1
          funext z
          rw [Finset.sum_sub_distrib]
      _ = _ := henergy
  have hsumGate :
      (∑ n ∈ futureCalendarDates t,
        futureGateMassAt rate rewards C_star C_h u t n) =
        futureGateMass rate rewards C_star C_h u t := rfl
  have hsum' : (11 / 2 : ℝ) *
        (∫ z, supportedFutureBacklog rate rewards C_star C_h u t z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          futureGateMass rate rewards C_star C_h u t +
        (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
          (∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) -
            ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
    calc
      _ = ∑ n ∈ futureCalendarDates t,
            ((11 / 2 : ℝ) *
              ∫ z, supportedFutureBacklogAt rate rewards C_star C_h u t n z ∂ν) := by
          change (11 / 2 : ℝ) * (∫ z,
            (∑ n ∈ futureCalendarDates t,
              supportedFutureBacklogAt rate rewards C_star C_h u t n z) ∂ν) = _
          rw [hbackSum, Finset.mul_sum]
      _ ≤ ∑ n ∈ futureCalendarDates t,
            ((CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
                futureGateMassAt rate rewards C_star C_h u t n +
              ((∫ z, futureEnergyMinusAt rate rewards C_star C_h u t n z ∂ν) -
                ∫ z, futureEnergyPlusAt rate rewards C_star C_h u t n z ∂ν)) := hsum
      _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
            futureGateMass rate rewards C_star C_h u t +
          (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
            (∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν) -
              ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumGate, hsumEnergy]
          ring
  have hterm_nonneg : 0 ≤ ∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν := by
    apply integral_nonneg
    intro z
    by_cases h : t.val + 2 < p.T
    · have hT := p.one_le_T
      have hf : t.val + 1 < (⟨p.T - 1, by omega⟩ : Fin p.T).val := by
        change t.val + 1 < p.T - 1
        omega
      simp only [futureTerminalEnergy, dite_eq_left h]
      exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus_bounds
        rate rewards C_star C_h u t ⟨p.T - 1, by omega⟩ hf z).1
    · simp [futureTerminalEnergy, h]
  have hloss_nonneg : 0 ≤ ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
    apply integral_nonneg
    intro z
    unfold futureAdjacentLoss
    apply Finset.sum_nonneg
    intro n hn
    exact futureAdjacentLossAt_nonneg rate rewards C_star C_h u t n hn z
  linarith only [hsum', hterm_nonneg, hloss_nonneg]

/-- The usual weakened form obtained by dropping the nonnegative outgoing and
support-loss terms. -/
theorem supported_future_weighted_budget_drop_outgoing
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) * (∫ z, supportedFutureBacklog rate rewards C_star C_h u t z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          futureGateMass rate rewards C_star C_h u t +
        (∫ z, futureInitialEnergy rate rewards C_star C_h u t z ∂ν) := by
  have h := supported_future_weighted_budget rate rewards C_star C_h u t control0
  have hterm : 0 ≤ ∫ z, futureTerminalEnergy rate rewards C_star C_h u t z ∂ν := by
    apply integral_nonneg
    intro z
    by_cases h' : t.val + 2 < p.T
    · have hT := p.one_le_T
      have hf : t.val + 1 < (⟨p.T - 1, by omega⟩ : Fin p.T).val := by
        change t.val + 1 < p.T - 1
        omega
      simp only [futureTerminalEnergy, dite_eq_left h']
      exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus_bounds
        rate rewards C_star C_h u t ⟨p.T - 1, by omega⟩ hf z).1
    · simp [futureTerminalEnergy, h']
  have hloss : 0 ≤ ∫ z, futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
    apply integral_nonneg
    intro z
    unfold futureAdjacentLoss
    apply Finset.sum_nonneg
    intro n hn
    exact futureAdjacentLossAt_nonneg rate rewards C_star C_h u t n hn z
  linarith only [h, hterm, hloss]

/-- The total actual future gate mass is bounded by the number of literal
future calendar dates times the mass of the original source law. -/
theorem futureGateMass_le_horizon :
    futureGateMass rate rewards C_star C_h u t ≤
      ((p.T - (t.val + 2) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
  calc
    futureGateMass rate rewards C_star C_h u t ≤
        ∑ n ∈ futureCalendarDates t, (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
      unfold futureGateMass
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hq : n < p.T := hn'.2
      have hf : t.val + 1 < n := by omega
      simp only [futureGateMassAt, dite_eq_left hq, dite_eq_left hf]
      exact MeasureTheory.measureReal_mono (Set.subset_univ _) (by finiteness)
    _ = ((p.T - (t.val + 2) : ℕ) : ℝ) * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real Set.univ := by
      simp [futureCalendarDates, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

end Bandits.Support.ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget

end
