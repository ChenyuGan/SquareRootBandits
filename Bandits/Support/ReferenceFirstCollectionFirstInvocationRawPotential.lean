/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionCurrentOriginalRoundedComparison
public import Bandits.Support.ReferenceFirstCollectionOldConditionalWeightedEnergyDrift
public import Bandits.Support.ReferenceFirstLiveRawPotentialBound

import Mathlib.Tactic

/-!
# Raw potential through the first original collection invocation

The optional list below is the zero-origin numerical prefix at the actual
first invocation, including its current update.  In the no-invocation branch
it is the original pre-call horizon.  An absent launch/readout remains absent.
The scalar readouts are deterministic projections of this existing source
prefix; this module makes no law, expectation, or coupling claim.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318,393-466`,
`05_binary_transport.tex:352-431`, `06_interruptions.tex:355-426`, and
`appendix_a_local_protocol.tex:8-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFirstInvocationRawPotential

open BootstrapPrivateRoundStreams (SourceInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ReferenceFirstCollectionSamplerCall (firstCollectionCall)
open ReferenceFirstCollectionPrecallCalendarSupport (firstCallBoundary precallCells?)
open ReferenceFirstCollectionCurrentQueueEnergy (thetaMinus weightedBacklog)
open ReferenceFirstCollectionOldCalendarExponentialStep (G)
open ReferenceFirstCollectionOldRecorderFoundation (oldRaw)
open ReferenceFirstCollectionOldConditionalWeightedEnergyDrift (incomingTheta costOld)
open ReferenceFirstCollectionCurrentOriginalRoundedComparison (rawGap)
open ReferenceFirstLiveRawPotentialBound
  (firstWindowCells firstWindowQueue firstWindowAcceptedArrival firstWindowMarginal
    firstWindowNormalizedBacklog firstWindowRawGap firstWindowMarginalBacklogCorrection)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
open ReferenceFirstCollectionPrecallCalendarSupport
open ReferenceSourcePrefixHistoryFiltration (actualRecord actualLaunchBy)

/-- The actual zero-origin queue input prefix through the current update at
the first original invocation.  With no invocation, retain the whole actual
pre-call horizon. -/
def firstInvocationCells? (z : SourceInput p) :
    Option (List (RecordedQueueRun.RoundInput p.K)) :=
  let call := firstCollectionCall rate rewards C_star C_h z
  (precallCells? rate rewards C_star C_h p.T z).bind fun L =>
      match call with
      | none => some L
      | some (_, (t, _)) =>
          (ReferenceFirstCollectionCurrentNumericalCell.currentCell
            rate rewards C_star C_h t z).map (fun c => L ++ [c])

/-- The raw comparator gap read from the single actual recorded run.  The
absent optional prefix has the explicitly localized scalar value zero. -/
def firstInvocationRawGap (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  (firstInvocationCells? rate rewards C_star C_h z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length,
      ((∑ i ∈ S.1,
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord Q
              (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
            (rate.n : ℝ))) -
        ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
            ((RecordedQueueRun.acceptedArrival
              (RecordedQueueRun.acceptedRecord Q
                (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
              (rate.n : ℝ)))

/-- The served-estimate comparator gap on the same optional actual run. -/
def firstInvocationServedGap (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  (firstInvocationCells? rate rewards C_star C_h z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length,
      ((∑ i ∈ S.1,
          RecordedPotentialStep.servedEstimate Q
            (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) -
        ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
            RecordedPotentialStep.servedEstimate Q
              (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i)

/-- Weighted accepted arrivals on the same actual queue prefix. -/
def firstInvocationWeightedArrival (z : SourceInput p) : ℝ :=
  (firstInvocationCells? rate rewards C_star C_h z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length, ∑ i : Fin p.K,
      RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord Q
            (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
          (rate.n : ℝ))

/-- The all-successor signed marginal/backlog correction on the same run. -/
def firstInvocationCorrection (z : SourceInput p) : ℝ :=
  (firstInvocationCells? rate rewards C_star C_h z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length, ∑ i : Fin p.K,
      (RecordedQueueSummation.runMarginal Q p.m rounds (k.val + 1) i -
        RecordedQueueSummation.runMarginal Q p.m rounds k.val i) *
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take (k.val + 1))) i

/-- The terminal comparator-minus-weighted-backlog term at boundary `N`.
It uses the same actual run and the same all-`N` successor convention as the
correction immediately above. -/
def firstInvocationTerminalCorrection (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  (firstInvocationCells? rate rewards C_star C_h z).elim 0 fun rounds =>
    (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take rounds.length)) i) -
      ∑ i : Fin p.K,
        RecordedQueueSummation.runMarginal Q p.m rounds rounds.length i *
          StoppedQueueBound.normalizedBacklog Q
            (RecordedQueueRun.run Q (rounds.take rounds.length)) i

/-- Active-prefix weighted backlog cost, with the source mask defined by the
actual enabled bit and the incoming stopped-run overflow flag. -/
def firstInvocationActiveBacklog (z : SourceInput p) : ℝ :=
  (firstInvocationCells? rate rewards C_star C_h z).elim 0 fun rounds =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin rounds.length =>
        rounds[k.val].enabled = true ∧
          (RecordedQueueRun.run Q (rounds.take k.val)).overflow = false),
      ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
            StoppedQueueBound.normalizedBacklog Q
              (RecordedQueueRun.run Q (rounds.take k.val)) i

/-- The calendar cost paid by the first LIVE, original OLD, and current
retained gates. -/
def firstInvocationCost (z : SourceInput p) : ℝ :=
  (∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
        rate rewards C_star C_h t z) +
    (∑ t : Fin p.T, costOld rate rewards C_star C_h t z) +
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t).indicator
        (weightedBacklog rate rewards C_star C_h u t) z

/-- One original OLD raw comparator term, localized to its existing selector
and actual incoming prefix readout. -/
def firstInvocationOldRawStepGap (t : Fin p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  (∑ i ∈ S.1,
        (ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t).indicator
            (oldRaw rate rewards C_star C_h t i) z) -
      ∑ i : Fin p.K,
        incomingTheta rate rewards C_star C_h t i z *
          (ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t).indicator
              (oldRaw rate rewards C_star C_h t i) z

/-- The original OLD raw comparator sum over the full actual calendar. -/
def firstInvocationOldRawGap (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) : ℝ :=
  ∑ t : Fin p.T, firstInvocationOldRawStepGap rate rewards C_star C_h t S z

/-- The weighted accepted arrivals on the original first LIVE list. -/
def firstInvocationLiveWeightedArrival (z : SourceInput p) : ℝ :=
  ∑ k : Fin (firstWindowCells rate rewards C_star C_h z).length,
    ∑ i : Fin p.K,
      firstWindowMarginal rate rewards C_star C_h z k.val i *
        firstWindowAcceptedArrival rate rewards C_star C_h z k i

/-- The sum of the original OLD weighted raw arrivals. -/
def firstInvocationOldWeightedArrival (z : SourceInput p) : ℝ :=
  ∑ t : Fin p.T, ∑ i : Fin p.K,
    incomingTheta rate rewards C_star C_h t i z *
      (ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t).indicator
          (oldRaw rate rewards C_star C_h t i) z

/-- The sum of the original current-call weighted retained raw arrivals. -/
def firstInvocationCurrentWeightedArrival (z : SourceInput p) : ℝ :=
  ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ i : Fin p.K,
      thetaMinus
      rate rewards C_star C_h u t i z *
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw
        rate rewards C_star C_h u t i z

/-- The scalar projections are zero only when the source carrier itself is
absent; no queue or history is selected on that branch. -/
theorem firstInvocationAbsent_scalars_zero (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p)
    (h : firstInvocationCells? rate rewards C_star C_h z = none) :
    firstInvocationRawGap rate rewards C_star C_h S z = 0 ∧
      firstInvocationServedGap rate rewards C_star C_h S z = 0 ∧
      firstInvocationWeightedArrival rate rewards C_star C_h z = 0 ∧
      firstInvocationCorrection rate rewards C_star C_h z = 0 ∧
      firstInvocationTerminalCorrection rate rewards C_star C_h S z = 0 ∧
      firstInvocationActiveBacklog rate rewards C_star C_h z = 0 := by
  simp [firstInvocationRawGap, firstInvocationServedGap,
    firstInvocationWeightedArrival, firstInvocationCorrection,
    firstInvocationTerminalCorrection, firstInvocationActiveBacklog, h]

private theorem eta_mul_den_le_one :
    rate.eta.val * (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 := by
  have hcap : rate.eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) := by
    calc
      _ ≤ _ := rate.sourceCap
      _ = _ := by simp only [one_div, mul_inv_rev]
  have hm := ConstructorDimensions.m_pos p
  have hK := ConstructorDimensions.K_pos p
  have hL := CanonicalRecordingRates.L_stab_ge_one p
  exact (le_div_iff₀ (by positivity)).mp hcap

private theorem eta_den_ge (c : ℝ) (hc : c ≤ 1024) (hc0 : 0 ≤ c) :
    c * (p.m : ℝ) ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast (CanonicalRecordingRates.L_stab_ge_one p)
  have hprod := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hK hL)
    (mul_nonneg hc0 (Nat.cast_nonneg p.m))
  have hscale := mul_le_mul_of_nonneg_right hc (by positivity :
    0 ≤ (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ))
  nlinarith only [hprod, hscale]

private theorem firstInvocation_four_m_eta_le_one : 4 * (p.m : ℝ) * (Q).eta ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (eta_den_ge (p := p) 4 (by norm_num) (by norm_num)) rate.eta.property.le
  have hcap := eta_mul_den_le_one rate
  change 4 * (p.m : ℝ) * rate.eta.val ≤ 1
  nlinarith only [h, hcap]

private theorem firstInvocation_eta_le_one_div_sixtyfour : (Q).eta ≤ 1 / 64 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hden := eta_den_ge (p := p) 64 (by norm_num) (by norm_num)
  have h := mul_le_mul_of_nonneg_left (show (64 : ℝ) ≤
    1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) by nlinarith only [hm, hden])
    rate.eta.property.le
  have hcap := eta_mul_den_le_one rate
  change rate.eta.val ≤ 1 / 64
  linarith only [h, hcap]

private theorem firstInvocation_prefix_backlog_le_arrivals
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (k : Fin rounds.length) (i : Fin p.K) :
    StoppedQueueBound.normalizedBacklog
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (rounds.take (k.val + 1))) i ≤
      StoppedQueueBound.normalizedBacklog
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (rounds.take k.val)) i +
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (rounds.take k.val)) rounds[k.val] i) : ℝ) /
          (rate.n : ℝ)) := by
  let q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let state := RecordedQueueRun.run q (rounds.take k.val)
  let round := rounds[k.val]
  have hNatStep :
      ((RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round).registers i).2 ≤
        (state.registers i).2 +
          RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round i) := by
    change (QueueReplay.transition
        (4 * (ReferenceFirstLaunchNumericalCell.queueParameters rate).n) (state.registers i)
        (RecordedQueueRun.acceptedRecord
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) state round i)).2 ≤ _
    cases hrecord : RecordedQueueRun.acceptedRecord q state round i with
    | mk enabled amount =>
        cases enabled <;>
          simp [QueueReplay.transition, RecordedQueueRun.acceptedArrival]
  have hstep := RecordedPotentialStep.run_take_succ_eq_step
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) rounds k.val k.isLt
  have hNat :
      ((RecordedQueueRun.run q (rounds.take (k.val + 1))).registers i).2 ≤
        (state.registers i).2 +
          RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord q state round i) := by
    rw [hstep]
    exact hNatStep
  have hReal :
      (((RecordedQueueRun.run q (rounds.take (k.val + 1))).registers i).2 : ℝ) ≤
        ((state.registers i).2 : ℝ) +
          (RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord q state round i) : ℝ) := by
    exact_mod_cast hNat
  have hDiv := div_le_div_of_nonneg_right hReal
    (Nat.cast_nonneg (ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
  change (((RecordedQueueRun.run q (rounds.take (k.val + 1))).registers i).2 : ℝ) /
      ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) ≤
    (((state.registers i).2 : ℝ) /
        ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) +
      ((RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord q state round i) : ℝ) / (q.n : ℝ))
  rw [← add_div]
  simpa [state, round, ReferenceFirstLaunchNumericalCell.queueParameters] using hDiv

/-- The served-estimate part of the one-normalizer potential bound applies to
the same actual source prefix, including its current first-call update. -/
theorem firstInvocationServedGap_le_length
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : firstInvocationCells? rate rewards C_star C_h z = some rounds) :
    firstInvocationServedGap rate rewards C_star C_h S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) *
          (rounds.length : ℝ) := by
  have hpotential := RecordedPotentialTelescope.servedEstimate_cumulative_comparison
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) rounds p.two_le_m p.m_lt_K
    (firstInvocation_four_m_eta_le_one rate) S
  simpa [firstInvocationServedGap, hrounds,
    RecordedQueueSummation.runMarginal,
    ReferenceFirstLaunchNumericalCell.queueParameters] using hpotential

/-- The one-step signed marginal correction on the same present prefix is
controlled by its active incoming backlog and weighted accepted arrivals.
This is the finite-run inequality before transporting active backlog to the
three actual source calendars. -/
theorem firstInvocationCorrection_le_activeBacklog
    (z : SourceInput p) (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : firstInvocationCells? rate rewards C_star C_h z = some rounds) :
    firstInvocationCorrection rate rewards C_star C_h z ≤
      8 * rate.eta.val *
        (firstInvocationActiveBacklog rate rewards C_star C_h z +
          firstInvocationWeightedArrival rate rewards C_star C_h z) := by
  classical
  let θ := RecordedQueueSummation.runMarginal Q p.m rounds
  let b (k : ℕ) := StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (rounds.take k))
  let A (k : Fin rounds.length) (i : Fin p.K) : ℝ :=
    (RecordedQueueRun.acceptedArrival
      (RecordedQueueRun.acceptedRecord Q (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
        (rate.n : ℝ)
  let active := Finset.univ.filter fun k : Fin rounds.length =>
    rounds[k.val].enabled = true ∧ (RecordedQueueRun.run Q (rounds.take k.val)).overflow = false
  have hθ (k : ℕ) (i : Fin p.K) : 0 ≤ θ k i :=
    (RecordedQueueSummation.runMarginal_pos Q p.m rounds k i p.two_le_m p.m_lt_K).le
  have hb (k : ℕ) (i : Fin p.K) : 0 ≤ b k i :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA (k : Fin rounds.length) (i : Fin p.K) : 0 ≤ A k i :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ 8 * rate.eta.val := mul_nonneg (by norm_num) rate.eta.property.le
  have hstep (k : Fin rounds.length) :
      (∑ i, (θ (k.val + 1) i - θ k.val i) * b (k.val + 1) i) ≤
        if k ∈ active then 8 * rate.eta.val *
          ((∑ i, θ k.val i * b k.val i) + ∑ i, θ k.val i * A k i) else 0 := by
    by_cases hk : k ∈ active
    · rw [ite_eq_left hk]
      have hg (i : Fin p.K) : θ (k.val + 1) i - θ k.val i ≤ 8 * rate.eta.val * θ k.val i := by
        obtain ⟨h1, h2⟩ := RecordedMarginalGrowth.run_prefix_theta_growth Q rounds k.val k.isLt i
          p.two_le_m p.m_lt_K (firstInvocation_eta_le_one_div_sixtyfour rate)
        change θ (k.val + 1) i ≤ Real.exp (4 * (Q).eta) * θ k.val i at h1
        change Real.exp (4 * (Q).eta) * θ k.val i ≤ (1 + 8 * (Q).eta) * θ k.val i at h2
        have he : (Q).eta = rate.eta.val := rfl
        rw [he] at h1 h2
        linarith only [h1, h2]
      calc
        _ ≤ ∑ i, (8 * rate.eta.val * θ k.val i) * (b k.val i + A k i) := by
          apply Finset.sum_le_sum
          intro i _
          exact (mul_le_mul_of_nonneg_right (hg i) (hb _ i)).trans
            (mul_le_mul_of_nonneg_left
              (firstInvocation_prefix_backlog_le_arrivals rate rounds k i)
              (mul_nonneg hcoef (hθ _ i)))
        _ = _ := by simp only [mul_add, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    · rw [ite_eq_right hk]
      have hstop : rounds[k.val].enabled = false ∨
          (RecordedQueueRun.run Q (rounds.take k.val)).overflow = true := by
        cases he : rounds[k.val].enabled <;>
          cases ho : (RecordedQueueRun.run Q (rounds.take k.val)).overflow <;> simp_all [active]
      have heq (i : Fin p.K) : θ (k.val + 1) i = θ k.val i :=
        RecordedMarginalGrowth.run_prefix_theta_eq_of_disabled_or_overflowed
          (m := p.m) Q rounds k.val k.isLt i hstop
      simp only [heq, sub_self, zero_mul, Finset.sum_const_zero, le_refl]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hstep k)
  have harrival : (∑ k ∈ active, ∑ i, θ k.val i * A k i) ≤
      ∑ k : Fin rounds.length, ∑ i, θ k.val i * A k i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
      (fun k _ _ => Finset.sum_nonneg (fun i _ => mul_nonneg (hθ _ i) (hA k i)))
  have hcombined := mul_le_mul_of_nonneg_left
    (add_le_add_right harrival (∑ k ∈ active, ∑ i, θ k.val i * b k.val i)) hcoef
  simp only [Finset.sum_ite_mem, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.univ_inter] at hsum
  have hresult := hsum.trans hcombined
  simpa only [firstInvocationCorrection, firstInvocationActiveBacklog,
    firstInvocationWeightedArrival, hrounds, Option.elim_some, θ, b, A, active] using hresult

/-- Finite summation by parts for the actual optional run.  In particular,
the terminal marginal is at `N`, and the signed correction includes every
one of the `N` successor terms. -/
theorem firstInvocationRawGap_eq_served_terminal_add_correction
    (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    firstInvocationRawGap rate rewards C_star C_h S z =
      firstInvocationServedGap rate rewards C_star C_h S z +
        firstInvocationTerminalCorrection rate rewards C_star C_h S z +
        firstInvocationCorrection rate rewards C_star C_h z := by
  classical
  cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
  | none =>
      simp [firstInvocationRawGap, firstInvocationServedGap,
        firstInvocationTerminalCorrection, firstInvocationCorrection, hrounds]
  | some rounds =>
      have hsummation := RecordedQueueSummation.run_raw_served_summation_by_parts_all
        Q rounds p.two_le_m p.m_lt_K S
      have hsum :
          firstInvocationRawGap rate rewards C_star C_h S z =
            firstInvocationServedGap rate rewards C_star C_h S z +
              (∑ i ∈ S.1,
                StoppedQueueBound.normalizedBacklog Q
                  (RecordedQueueRun.run Q rounds) i) -
              ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal Q p.m rounds rounds.length i *
                  StoppedQueueBound.normalizedBacklog Q
                    (RecordedQueueRun.run Q rounds) i +
              firstInvocationCorrection rate rewards C_star C_h z := by
        simpa [firstInvocationRawGap, firstInvocationServedGap,
          firstInvocationCorrection, hrounds,
          ReferenceFirstLaunchNumericalCell.queueParameters] using hsummation
      rw [hsum]
      simp [firstInvocationTerminalCorrection, hrounds,
        ReferenceFirstLaunchNumericalCell.queueParameters]
      ring

/-- On an actual first-call cell, the optional carrier appends the actual
current numerical update exactly once to the strict-past queue prefix. -/
theorem firstInvocationCells?_firstCell_append (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ∃ L c,
      ReferenceFirstCollectionCurrentRetainedGate.pastCells?
        rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell
        rate rewards C_star C_h t z = some c ∧
      c.enabled = true ∧
      firstInvocationCells? rate rewards C_star C_h z = some (L ++ [c]) ∧
      RecordedQueueRun.run Q (L ++ [c]) =
        RecordedQueueRun.step Q (RecordedQueueRun.run Q L) c := by
  classical
  have hcallExists : ∃ theta,
      firstCollectionCall rate rewards C_star C_h z = some (u, (t, theta)) := by
    change (firstCollectionCall rate rewards C_star C_h z).map
      (fun c => (c.1, c.2.1)) = some (u, t) at hz
    cases h : firstCollectionCall rate rewards C_star C_h z with
    | none => simp [h] at hz
    | some call =>
        rcases call with ⟨u', rest⟩
        rcases rest with ⟨t', theta⟩
        simp only [h] at hz
        have hpair : (u', t') = (u, t) := Option.some.inj hz
        cases hpair
        exact ⟨theta, rfl⟩
  obtain ⟨theta, hcall⟩ := hcallExists
  let a : Fin p.K := ⟨0, Nat.lt_trans (ConstructorDimensions.m_pos p) p.m_lt_K⟩
  obtain ⟨L, c, hL, hc, henabled, _, _⟩ :=
    ReferenceFirstCollectionCurrentRetainedGate.firstCell_acceptedRecord
      rate rewards C_star C_h u t a z hz
  have hpre : precallCells? rate rewards C_star C_h p.T z = some L := by
    rw [ReferenceFirstCollectionPrecallCalendarSupport.precallCells_at_or_after_firstCell
      rate rewards C_star C_h u t p.T (Nat.le_of_lt t.isLt) z hz]
    exact hL
  refine ⟨L, c, hL, hc, henabled, ?_, ?_⟩
  · simp [firstInvocationCells?, hcall, hpre, hc]
  · simp only [RecordedQueueRun.run, CanonicalQueueProcess.execute_append,
      RecordedQueueRun.execute]

private theorem firstInvocationOldIncomingTheta_on_E (t : Fin p.T)
    (z : SourceInput p)
    (hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
      rate rewards C_star C_h t)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : precallCells? rate rewards C_star C_h t.val z = some L)
    (i : Fin p.K) :
    incomingTheta rate rewards C_star C_h t i z =
      ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight Q (RecordedQueueRun.run Q L)) i := by
  have hread := ReferenceFirstCollectionOldCalendarExponentialStep.precallReadout_eq_prefixReadout_on_E
    rate rewards C_star C_h t z hzE
  have hbefore :
      ReferenceFirstCollectionCurrentQueueReadout.before?
        rate rewards C_star C_h t z =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run Q L)) := by
    exact hread.symm.trans (by
      simp only [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL,
        Option.map_some])
  rw [incomingTheta, Set.indicator_of_mem hzE, hbefore]
  rfl

/-- If no original invocation occurs, the carrier is the actual pre-call
collection through the terminal horizon. -/
theorem firstInvocationCells?_noCall (z : SourceInput p)
    (hnone : firstCollectionCall rate rewards C_star C_h z = none) :
    firstInvocationCells? rate rewards C_star C_h z =
      precallCells? rate rewards C_star C_h p.T z := by
  simp [firstInvocationCells?, hnone]

/-- A no-call source with no genuine launch keeps the optional carrier absent. -/
theorem firstInvocationCells?_noCall_noLaunch (z : SourceInput p)
    (hnone : firstCollectionCall rate rewards C_star C_h z = none)
    (hn : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h p.T z) :
    firstInvocationCells? rate rewards C_star C_h z = none := by
  rw [firstInvocationCells?_noCall rate rewards C_star C_h z hnone]
  have hcut :
      ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
        rate rewards C_star C_h p.T z = p.T := by
    simp [ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary,
      ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary, hnone]
  exact ReferenceFirstCollectionPrecallCalendarSupport.precallCells_no_launch
    rate rewards C_star C_h p.T z (by simpa [hcut] using hn)

private theorem liveReadout_zero_of_some
    (start : ℕ) (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceLaterLiveNumericalReadout.laterLiveReadout start r = some c) :
    ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = some c := by
  obtain ⟨selected, ho, hs, hstart, hlive, heq⟩ :=
    ReferenceLaterLiveNumericalReadout.laterLiveReadout_some start r c hc
  have hzero : 0 < selected.view.payload.sigma.val := lt_of_le_of_lt (Nat.zero_le _) hstart
  simp only [ReferenceLaterLiveNumericalReadout.laterLiveReadout, hs,
    hzero, hlive, and_self, ↓reduceIte, ho]
  exact congrArg some heq.symm

/-- Every present inclusive prefix consists of the original consecutive dated
observations, starting at the genuine launch and ending by the horizon. -/
theorem firstInvocationCells?_support (z : SourceInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : firstInvocationCells? rate rewards C_star C_h z = some rounds) :
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    rounds.length ≤ p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
    ∀ k : Fin rounds.length,
      ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]? = some r ∧
        r.input.time.val = ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some rounds[k.val] := by
  cases hcall : firstCollectionCall rate rewards C_star C_h z with
  | none =>
      rw [firstInvocationCells?_noCall rate rewards C_star C_h z hcall] at hrounds
      rcases ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_support
        rate rewards C_star C_h p.T le_rfl z with ⟨_, hn⟩ | ⟨hlaunch, L, hL, hlen, _, hcells⟩
      · rw [hn] at hrounds
        contradiction
      · have heq : L = rounds := Option.some.inj (hL.symm.trans hrounds)
        subst L
        refine ⟨hlaunch.1, ?_, hcells⟩
        rw [hlen]
        exact Nat.sub_le_sub_right
          (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary_le rate rewards C_star C_h p.T z) _
  | some call =>
      rcases call with ⟨u, t, theta⟩
      have hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
        change (firstCollectionCall rate rewards C_star C_h z).map _ = some (u, t)
        simp only [hcall, Option.map_some]
      obtain ⟨hc, _, _, _, _, _, _, L, hparts⟩ :=
        ReferenceFirstCollectionCurrentRetainedGate.firstCell_prefix_coverage rate rewards C_star C_h u t z hz
      rcases hparts with ⟨hsu, hut, _, _, _, _, _, _, _, _, _, hL, hlen, hcells⟩
      obtain ⟨L', c, hL', hcCell, _, hcarrier, _⟩ :=
        firstInvocationCells?_firstCell_append rate rewards C_star C_h u t z hz
      have heq : L' = L := Option.some.inj (hL'.symm.trans hL)
      subst L'
      have hroundEq : rounds = L ++ [c] := Option.some.inj (hrounds.symm.trans hcarrier)
      subst rounds
      refine ⟨hc, ?_, ?_⟩
      · have hst := hsu.trans (Nat.le_of_lt hut)
        simp only [List.length_append, List.length_singleton, hlen]
        have ht := t.isLt
        omega
      · intro k
        by_cases hk : k.val < L.length
        · obtain ⟨r, hr, ht, hcell⟩ := hcells ⟨k.val, hk⟩
          exact ⟨r, hr, ht, by simpa only [List.getElem_append_left hk] using hcell⟩
        · have hlast : k.val = L.length := by
            have hb := k.isLt
            simp only [List.length_append, List.length_singleton] at hb
            omega
          obtain ⟨n, r, theta', selected, c', hr, ht, _, _, _, _, _, _, _, hc', hread, _⟩ :=
            ReferenceFirstCollectionCurrentRecordedCell.firstCell_selected rate rewards C_star C_h u t z hz
          have hcc : c' = c := Option.some.inj (hc'.symm.trans hcCell)
          subst c'
          have htime := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
            rate z rewards C_star C_h n r hr
          rw [ht] at htime
          have hn : n = L.length := by omega
          refine ⟨r, ?_, ?_, ?_⟩
          · simpa only [hlast, hn] using hr
          · rw [ht, hlast, hlen]
            omega
          · have hzero := liveReadout_zero_of_some rate _ r c hread
            simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hzero, hlast]

/-- All earlier pre-call queries take the very same inclusive list.  Queries
before the genuine launch retain their absent optional value. -/
theorem firstInvocationCells?_precall_take (z : SourceInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : firstInvocationCells? rate rewards C_star C_h z = some rounds)
    (n : ℕ) (hn : n ≤ p.T) :
    precallCells? rate rewards C_star C_h n z =
      if ReferenceSourcePrefixHistoryFiltration.actualLaunchBy rate rewards C_star C_h
          (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n z) z then
        some (rounds.take (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n z -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)) else none := by
  cases hcall : firstCollectionCall rate rewards C_star C_h z with
  | none =>
      rw [firstInvocationCells?_noCall rate rewards C_star C_h z hcall] at hrounds
      exact ReferenceFirstCollectionPrecallCalendarSupport.precallCells_take
        rate rewards C_star C_h n p.T hn z rounds hrounds
  | some call =>
      rcases call with ⟨u, t, theta⟩
      have hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
        change (firstCollectionCall rate rewards C_star C_h z).map _ = some (u, t)
        simp only [hcall, Option.map_some]
      obtain ⟨L, c, hL, _, _, hcarrier, _⟩ :=
        firstInvocationCells?_firstCell_append rate rewards C_star C_h u t z hz
      have heq : rounds = L ++ [c] := Option.some.inj (hrounds.symm.trans hcarrier)
      have hpre : precallCells? rate rewards C_star C_h p.T z = some L := by
        rw [ReferenceFirstCollectionPrecallCalendarSupport.precallCells_at_or_after_firstCell
          rate rewards C_star C_h u t p.T (Nat.le_of_lt t.isLt) z hz]
        exact hL
      rw [ReferenceFirstCollectionPrecallCalendarSupport.precallCells_take
        rate rewards C_star C_h n p.T hn z L hpre]
      obtain ⟨L', hL', hlength, _⟩ :=
        ReferenceFirstCollectionCurrentRetainedGate.firstCell_allPrefixes rate rewards C_star C_h u t z hz
      have heqL : L' = L := Option.some.inj (hL'.symm.trans hL)
      have htake : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary rate rewards C_star C_h n z -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ L.length := by
        rw [← heqL, hlength]
        apply Nat.sub_le_sub_right
        rw [ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary,
          ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell rate rewards C_star C_h u t z hz]
        exact Nat.min_le_right _ _
      rw [heq, List.take_append_of_le_length htake]

local notation "R" z:max => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "s" z:max => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
local notation "V" z:max => firstWindowCells rate rewards C_star C_h z
local notation "W" z:max => ReferenceFirstLiveConfirmationHistory.firstLiveWindow (R z)

private theorem liveCells_length (z : SourceInput p) : (V z).length = (W z).length := by
  exact ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length rate rewards C_star C_h z

private theorem record_time (z : SourceInput p) (k : ℕ)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (R z)[k]? = some r) : r.input.time.val = s z + k :=
  ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time rate z rewards C_star C_h k r hr

private theorem index_lt_takeWhile {A : Type*} (test : A → Bool)
    (xs : List A) (k : ℕ) (hk : k < xs.length)
    (hall : ∀ j ≤ k, ∀ x, xs[j]? = some x → test x = true) :
    k < (xs.takeWhile test).length := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at hk
  | cons x xs ih =>
      have hx : test x = true := hall 0 (Nat.zero_le _) x rfl
      cases k with
      | zero => simp only [List.takeWhile_cons, hx, ↓reduceIte,
          List.length_cons, Nat.zero_lt_succ]
      | succ k =>
          have hk' : k < xs.length := Nat.lt_of_succ_lt_succ hk
          have hh : ∀ j ≤ k, ∀ y, xs[j]? = some y → test y = true := by
            intro j hj y hy
            exact hall (j + 1) (by omega) y
              (by simpa only [List.getElem?_cons_succ] using hy)
          simpa only [List.takeWhile_cons, hx, ↓reduceIte, List.length_cons,
            Nat.succ_lt_succ_iff] using ih k hk' hh

private theorem index_lt_collectionWindow (z : SourceInput p) (k w : ℕ)
    (hw : w < (R z).length) (hwk : w ≤ k) (hk : k < (R z).length)
    (hbefore : s z + k < firstCallBoundary rate rewards C_star C_h z) :
    k - w < (ReferenceCollectionPhaseHistory.collectionWindow (R z) w).length := by
  have hhead : ((R z).drop w |>.take 1).length = 1 := by
    simp only [List.length_take, List.length_drop]
    omega
  unfold ReferenceCollectionPhaseHistory.collectionWindow
  rw [List.length_append, hhead]
  by_cases heq : k = w
  · omega
  · have htail : k - w - 1 < ((R z).drop (w + 1)).length := by
      simp only [List.length_drop]
      omega
    have htake := index_lt_takeWhile
      (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        !ReferenceCollectionPhaseHistory.laterChosen r.input)
      ((R z).drop (w + 1)) (k - w - 1) htail (by
        intro j hj r hr
        have hr' : (R z)[w + 1 + j]? = some r := by
          simpa only [List.getElem?_drop] using hr
        have hd := record_time rate rewards C_star C_h z _ r hr'
        have hnone := parameters_none_before_cut rate rewards C_star C_h z _ r hr'
          (by omega)
        cases hb : ReferenceCollectionPhaseHistory.laterChosen r.input with
        | false => rfl
        | true =>
            have hp := ReferenceFirstCollectionRenewalRecordingFeedback.laterChosen_parameters_present
              r.input hb
            change (ReferenceLaterSamplerParameterMeasurability.parameters? r.input).isSome = true at hp
            simp only [hnone, Option.isSome_none, Bool.false_eq_true] at hp)
    have hi : k - w = k - w - 1 + 1 := by omega
    rw [hi]
    simpa only [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_lt_succ htake

/-- Once the first LIVE list has ended, every actual pre-call date is still
in the original initialized collection stream. Its last physical update is
retained even if no next invocation exists. -/
private theorem oldReadout_afterLive (t : Fin p.T) (z : SourceInput p)
    (hz : actualLaunchBy rate rewards C_star C_h t.val z)
    (hbefore : t.val < firstCallBoundary rate rewards C_star C_h z)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r)
    (hend : s z + (V z).length ≤ t.val) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c ∧
      ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r = none := by
  let count := p.T - s z
  let hs := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseReadySpan
    rate rewards C_star C_h z
  let w := (W z).length
  let k := t.val - s z
  have hwk : w ≤ k := by
    rw [liveCells_length rate rewards C_star C_h z] at hend
    dsimp only [w, k]
    omega
  have hk : k < (R z).length := by
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
    have hs0 := hz.2
    have ht0 := t.isLt
    dsimp only [k]
    omega
  have hbefore' : s z + k < firstCallBoundary rate rewards C_star C_h z := by
    have hs0 := hz.2
    dsimp only [k]
    omega
  have hR : (R z)[k]? = some r := by
    simpa only [actualRecord, ite_eq_left hz.2] using hr
  have hepoch := ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstEpoch
    rate rewards C_star C_h z hz.1
  have hcount : (R z).length = count :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hz.1 count hs).records).length < count := by
    rw [← hepoch]
    change w < count
    omega
  obtain ⟨_, _, d, head, initializer, valid, D, hhead, hpay, hinit, hchecked,
      hDlen, hzero, hcells⟩ :=
    ReferenceCompleteFirstPhaseObservationRecovery.actualFirstCollectionRawObservationIdentity
      rate rewards C_star C_h z hz.1 hshort
  have hwin : k - w < d.stream.window.length := by
    rw [d.stream.windowIsActual]
    change k - w < (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate) z rewards C_star C_h
        hz.1 count hs).records _).length
    rw [← hepoch]
    exact index_lt_collectionWindow rate rewards C_star C_h z k w
      (by omega) hwk hk hbefore'
  have hell : k - w < d.stream.ell := by
    by_contra hn
    have hshorter : d.stream.ell < d.stream.window.length := by omega
    have halign := (d.stream.alignment
      ⟨d.last.val, lt_of_lt_of_le d.last.isLt d.stream.withinWindow⟩).2
    have hrecord : d.stream.window[d.last.val]'(by
        exact lt_of_lt_of_le d.last.isLt d.stream.withinWindow) = d.record :=
      (List.getElem?_eq_some_iff.mp d.recordAt).2
    rw [hrecord, ← hepoch] at halign
    have hlast : d.record.input.time.val + 1 = s z + w + d.stream.ell := by
      have he := d.lastIsLast
      change d.record.input.time.val + 1 = s z + w + 1 + d.last.val at halign
      omega
    cases d.outcome with
    | exhausted _ hend _ _ _ => omega
    | empty e =>
        cases e.nextBoundary with
        | terminal ht _ =>
            have hsT := d.record.input.time.isLt
            have hsbound := firstCallBoundary_le_T rate rewards C_star C_h z
            omega
        | next hb _ x _ _ htime _ _ _ _ hrun dispatch =>
            have hnext : w + d.stream.ell < (R z).length := by
              rw [hcount]
              dsimp only [count]
              omega
            let rNext := (R z)[w + d.stream.ell]'hnext
            have hlook : (R z)[w + d.stream.ell]? = some rNext :=
              List.getElem?_eq_getElem hnext
            have hx : x = rNext.input := hrun rNext (by
              rw [← hepoch]
              exact hlook)
            have hp : (ReferenceLaterSamplerParameterMeasurability.parameters?
                rNext.input).isSome = true := by
              rw [← hx]
              exact actualNextDispatch_parameters_present rate x _ _ _ dispatch
                (fun a c hc => (e.cutoffLastService a c hc).1)
            have hfirst := firstCallBoundary_le_of_parameters rate rewards C_star C_h
              z _ rNext hlook hp
            have hdate := record_time rate rewards C_star C_h z _ rNext hlook
            omega
  let j : Fin d.stream.ell := ⟨k - w, hell⟩
  obtain ⟨call, validCall, _, _, _, _, _, _, _, _, _, _, _, _, hread, hnone, _⟩ :=
    hcells j
  let r0 := d.stream.window[j.val]'(lt_of_lt_of_le j.isLt d.stream.withinWindow)
  have hlookup := (d.stream.alignment
    ⟨j.val, lt_of_lt_of_le j.isLt d.stream.withinWindow⟩).1
  rw [← hepoch] at hlookup
  have hindex : w + j.val = k := by dsimp only [j]; omega
  change (R z)[w + j.val]? = some r0 at hlookup
  rw [hindex] at hlookup
  have heq : r0 = r := Option.some.inj (hlookup.symm.trans hR)
  exact ⟨_, by simpa only [← heq] using hread, by simpa only [← heq] using hnone⟩

private def acceptedRaw (state : RecordedQueueRun.RunState p.K)
    (c : RecordedQueueRun.RoundInput p.K) (i : Fin p.K) : ℝ :=
  (RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q state c i) : ℝ) / (rate.n : ℝ)

private def weightedStep (state : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K) : ℝ :=
  ∑ i, ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q state) i * acceptedRaw rate state c i

private def rawStep (S : ProductSetLaw.ProductSet p.K p.m)
    (state : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K) : ℝ :=
  (∑ i ∈ S.1, acceptedRaw rate state c i) - weightedStep rate state c

private def activeBacklogStep (state : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K) : ℝ :=
  if c.enabled = true ∧ state.overflow = false then RecordedWeightedDrift.weightedBacklog p.m Q state else 0

private theorem oldStep_statistics (S : ProductSetLaw.ProductSet p.K p.m) (t : Fin p.T) (z : SourceInput p)
    (hzE : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h t) :
    ∃ L c, precallCells? rate rewards C_star C_h t.val z = some L ∧
      ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h t z = some c ∧
      rawStep rate S (RecordedQueueRun.run Q L) c = firstInvocationOldRawStepGap rate rewards C_star C_h t S z ∧
      weightedStep rate (RecordedQueueRun.run Q L) c = ∑ i : Fin p.K,
        incomingTheta rate rewards C_star C_h t i z *
          (G rate rewards C_star C_h t).indicator (oldRaw rate rewards C_star C_h t i) z ∧
      activeBacklogStep rate (RecordedQueueRun.run Q L) c = costOld rate rewards C_star C_h t z := by
  obtain ⟨L, c, hL, hc, _, _⟩ := ReferenceFirstCollectionOldCalendarExponentialStep.actual_old_calendar_append rate rewards C_star C_h t z hzE
  have hprefix : ReferenceFirstCollectionCurrentRetainedGate.prefixReadout? rate rewards C_star C_h t z =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (RecordedQueueRun.run Q L)) :=
    (ReferenceFirstCollectionOldCalendarExponentialStep.precallReadout_eq_prefixReadout_on_E rate rewards C_star C_h t z hzE).symm.trans
      (by simp only [ReferenceFirstCollectionPrecallCalendarSupport.precallReadout?, hL, Option.map_some])
  have hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔
      (RecordedQueueRun.run Q L).overflow = false := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.H, hprefix, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  have hinc := ReferenceFirstCollectionOldRecorderFoundation.oldCell_enabled_eq_incoming rate rewards C_star C_h t z c hc
  have hG : z ∈ G rate rewards C_star C_h t ↔ c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false := by
    simp only [G, Set.mem_inter_iff, Set.mem_ofPred_eq, hzE, true_and, hH, hinc, Option.some.injEq]
    exact and_comm
  have hraw (i : Fin p.K) : acceptedRaw rate (RecordedQueueRun.run Q L) c i =
      (G rate rewards C_star C_h t).indicator (oldRaw rate rewards C_star C_h t i) z := by
    by_cases ha : c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false
    · rw [Set.indicator_of_mem (hG.mpr ha)]
      simp only [acceptedRaw, RecordedQueueRun.acceptedRecord, ha.2, Bool.false_eq_true,
        ↓reduceIte, ha.1, RecordedQueueRun.acceptedArrival, oldRaw, hc,
        RecordedRoundMoments.normalizedQuantizedArrival]
      rfl
    · rw [Set.indicator_of_notMem (fun h => ha (hG.mp h))]
      cases he : c.enabled <;> cases ho : (RecordedQueueRun.run Q L).overflow <;>
        simp_all [acceptedRaw, RecordedQueueRun.acceptedRecord, RecordedQueueRun.acceptedArrival]
  have htheta := firstInvocationOldIncomingTheta_on_E rate rewards C_star C_h t z hzE L hL
  refine ⟨L, c, hL, hc, ?_, ?_, ?_⟩
  · simp_rw [rawStep, weightedStep, hraw, ← htheta]
    rfl
  · simp_rw [weightedStep, hraw, ← htheta]
  · by_cases ha : c.enabled = true ∧ (RecordedQueueRun.run Q L).overflow = false
    · simp only [activeBacklogStep, ite_eq_left ha, costOld, Set.indicator_of_mem (hG.mpr ha),
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldBacklog, hL]
    · simp only [activeBacklogStep, ite_eq_right ha, costOld, Set.indicator_of_notMem (fun h => ha (hG.mp h))]

private theorem currentStep_statistics (S : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :
    ∃ L c, ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z = some L ∧
      ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z = some c ∧
      rawStep rate S (RecordedQueueRun.run Q L) c = rawGap rate rewards C_star C_h u t S z ∧
      weightedStep rate (RecordedQueueRun.run Q L) c = ∑ i : Fin p.K,
        thetaMinus rate rewards C_star C_h u t i z * ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw rate rewards C_star C_h u t i z ∧
      activeBacklogStep rate (RecordedQueueRun.run Q L) c =
        (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
          (weightedBacklog rate rewards C_star C_h u t) z := by
  obtain ⟨L, c, hL, hc, he, _, _, hθ, _⟩ := ReferenceFirstCollectionCurrentQueueEnergy.firstCell_actual_score_marginals rate rewards C_star C_h u t z hz
  have htheta (i : Fin p.K) := congrFun hθ i
  have hraw (i : Fin p.K) : acceptedRaw rate (RecordedQueueRun.run Q L) c i =
      ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw rate rewards C_star C_h u t i z := by
    obtain ⟨L', c', hL', hc', _, _, _, _, _, hr, _⟩ := ReferenceFirstCollectionCurrentQueueReadout.firstCell_actual_queue_readouts rate rewards C_star C_h u t i z hz
    have hLL : L' = L := Option.some.inj (hL'.symm.trans hL)
    have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
    simpa only [acceptedRaw, hLL, hcc, ReferenceFirstLaunchNumericalCell.queueParameters] using hr.symm
  have hbefore : ReferenceFirstCollectionCurrentQueueReadout.before? rate rewards C_star C_h t z =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout (RecordedQueueRun.run Q L)) := by
    simp only [ReferenceFirstCollectionCurrentQueueReadout.before?, ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?, hL, Option.map_some]
  have hH : z ∈ ReferenceFirstCollectionCurrentRetainedGate.H rate rewards C_star C_h t ↔ (RecordedQueueRun.run Q L).overflow = false := by
    change (∃ v, ReferenceFirstCollectionCurrentQueueReadout.before? rate rewards C_star C_h t z = some v ∧ v.2.1 = false) ↔ _
    simp [hbefore, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  have hb (i : Fin p.K) : ReferenceFirstCollectionCurrentQueueReadout.bMinus rate rewards C_star C_h u t i z =
      StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q L) i := by
    simp only [ReferenceFirstCollectionCurrentQueueReadout.bMinus, Set.indicator_of_mem hz, hbefore,
      ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog, ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
    rfl
  refine ⟨L, c, hL, hc, ?_, ?_, ?_⟩
  · simp_rw [rawStep, weightedStep, hraw, ← htheta]
    rfl
  · simp_rw [weightedStep, hraw, ← htheta]
  · by_cases ho : (RecordedQueueRun.run Q L).overflow = false
    · have hG : z ∈ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t := ⟨hz, hH.mpr ho⟩
      rw [activeBacklogStep, ite_eq_left ⟨he, ho⟩, Set.indicator_of_mem hG]
      simp_rw [weightedBacklog, htheta, hb]
      rfl
    · have hG : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t := fun h => ho (hH.mp h.2)
      rw [activeBacklogStep, ite_eq_right (fun h => ho h.2), Set.indicator_of_notMem hG]

private def listStatistic
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (L : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ k : Fin L.length, f (RecordedQueueRun.run Q (L.take k.val)) L[k.val]

private def oldStatistic
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (t : Fin p.T) (z : SourceInput p) : ℝ :=
  (ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h t).indicator
    (fun z => ((precallCells? rate rewards C_star C_h t.val z).bind fun L =>
      (ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h t z).map
        (fun c => f (RecordedQueueRun.run Q L) c)).elim 0 id) z

private theorem oldSelector_iff_calendar (t : Fin p.T) (z : SourceInput p) :
    z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h t ↔
      actualLaunchBy rate rewards C_star C_h t.val z ∧
        s z + (V z).length ≤ t.val ∧ t.val < firstCallBoundary rate rewards C_star C_h z := by
  constructor
  · intro hz
    obtain ⟨hb, hsome⟩ := (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mp hz
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨r, hr, hold⟩ := Option.bind_eq_some_iff.mp hc
    have hlaunch : actualLaunchBy rate rewards C_star C_h t.val z := by
      by_contra hn
      rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
        rate rewards C_star C_h t z hn] at hr
      contradiction
    have hend := old_readout_after_firstLiveWindow rate rewards C_star C_h t z hlaunch r hr
      (by rw [hold]; rfl)
    rw [← liveCells_length rate rewards C_star C_h z] at hend
    exact ⟨hlaunch, hend, hb⟩
  · rintro ⟨hlaunch, hend, hb⟩
    obtain ⟨_, r, _, _, hr, _, _, _, _, _⟩ := precallPrefix_append rate rewards C_star C_h t z hlaunch hb
    obtain ⟨c, hold, _⟩ := oldReadout_afterLive rate rewards C_star C_h t z hlaunch hb r hr hend
    apply (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
      rate rewards C_star C_h t z).mpr
    refine ⟨hb, ?_⟩
    simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hr, Option.bind_some, hold, Option.isSome_some]

private theorem precallStatistic_decomposition
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (z : SourceInput p) :
    (precallCells? rate rewards C_star C_h p.T z).elim 0 (listStatistic rate f) =
      listStatistic rate f (V z) + ∑ t : Fin p.T, oldStatistic rate rewards C_star C_h f t z := by
  rcases precallPrefix_support rate rewards C_star C_h p.T le_rfl z with ⟨hn, hnone⟩ | ⟨hlaunch, L, hL, hlen, _, hcells⟩
  · have hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing = none := by
      have hnot : ¬ (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
        intro hc
        apply hn
        refine ⟨hc, ?_⟩
        rw [cutBoundary_horizon]
        exact physicalStart_le_firstCallBoundary rate rewards C_star C_h z
      cases he : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing <;> simp_all
    have hV : V z = [] := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch rate rewards C_star C_h z hc).2.1
    have hOld (t : Fin p.T) : oldStatistic rate rewards C_star C_h f t z = 0 := by
      apply Set.indicator_of_notMem
      intro hz
      have hlaunch := (oldSelector_iff_calendar rate rewards C_star C_h t z).mp hz |>.1
      have hh : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := hlaunch.1
      simp only [hc, Option.isSome_none, Bool.false_eq_true] at hh
    simp [hnone, hV, listStatistic, hOld]
  · rw [cutBoundary_horizon] at hlen
    have hcross := hlaunch.1
    have hend := ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary rate rewards C_star C_h z
    change s z + (V z).length ≤ firstCallBoundary rate rewards C_star C_h z at hend
    have hVlen : (V z).length ≤ L.length := by have hs := physicalStart_le_firstCallBoundary rate rewards C_star C_h z; omega
    have hpreV := ReferenceFirstCollectionPrecallCalendarIncrementIdentity.precallCells_eq_firstLive_take
      rate rewards C_star C_h (s z + (V z).length) z ⟨hcross, Nat.le_add_right _ _⟩ le_rfl
    have htake := precallCells_take rate rewards C_star C_h (s z + (V z).length) p.T
      (hend.trans (firstCallBoundary_le_T rate rewards C_star C_h z)) z L hL
    have hcut : cutBoundary rate rewards C_star C_h (s z + (V z).length) z = s z + (V z).length := Nat.min_eq_left hend
    rw [hcut, ite_eq_left ⟨hcross, Nat.le_add_right _ _⟩] at htake
    change precallCells? rate rewards C_star C_h (s z + (V z).length) z = some ((V z).take (s z + (V z).length - s z)) at hpreV
    have hVtake : L.take (V z).length = V z := by
      have h := Option.some.inj (htake.symm.trans hpreV)
      simpa only [Nat.add_sub_cancel_left, List.take_length] using h
    have hLive : (∑ k ∈ Finset.univ.filter (fun k : Fin L.length => k.val < (V z).length),
        f (RecordedQueueRun.run Q (L.take k.val)) L[k.val]) = listStatistic rate f (V z) := by
      apply Finset.sum_bij (fun k hk => (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin (V z).length))
      · intro k _; exact Finset.mem_univ _
      · intro a _ b _ hab; exact Fin.ext (congrArg (fun x : Fin (V z).length => x.val) hab)
      · intro k _; exact ⟨⟨k.val, k.isLt.trans_le hVlen⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact k.isLt, rfl⟩
      · intro k hk
        have hkv := (Finset.mem_filter.mp hk).2
        have hp := congrArg (List.take k.val) hVtake
        have hv := congrArg (fun xs : List (RecordedQueueRun.RoundInput p.K) => xs[k.val]?) hVtake
        have hp' : L.take k.val = (V z).take k.val := by simpa only [List.take_take, Nat.min_eq_left hkv.le] using hp
        have hv' : L[k.val] = (V z)[k.val] := by
          simpa only [List.getElem?_take, hkv, ↓reduceIte, List.getElem?_eq_getElem k.isLt,
            List.getElem?_eq_getElem hkv, Option.some.injEq] using hv
        rw [hp', hv']
    have hOld : (∑ k ∈ Finset.univ.filter (fun k : Fin L.length => ¬ k.val < (V z).length),
        f (RecordedQueueRun.run Q (L.take k.val)) L[k.val]) = ∑ t : Fin p.T, oldStatistic rate rewards C_star C_h f t z := by
      rw [← Finset.sum_filter_of_ne (p := fun t => z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h t)
        (fun t _ ht => by unfold oldStatistic at ht; by_contra hn; rw [Set.indicator_of_notMem hn] at ht; exact ht rfl)]
      apply Finset.sum_bij (fun k _ => (⟨s z + k.val, by have hk := k.isLt; have hB := firstCallBoundary_le_T rate rewards C_star C_h z; omega⟩ : Fin p.T))
      · intro k hk
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, (oldSelector_iff_calendar rate rewards C_star C_h _ z).mpr ?_⟩
        refine ⟨⟨hcross, Nat.le_add_right _ _⟩, ?_, ?_⟩
        · change s z + (V z).length ≤ s z + k.val
          have hk := (Finset.mem_filter.mp hk).2; omega
        · change s z + k.val < firstCallBoundary rate rewards C_star C_h z
          have hk := k.isLt; omega
      · intro a _ b _ hab
        apply Fin.ext
        have h := congrArg Fin.val hab
        dsimp only at h
        omega
      · intro t ht
        obtain ⟨hlaunchT, hafter, hbefore⟩ := (oldSelector_iff_calendar rate rewards C_star C_h t z).mp (Finset.mem_filter.mp ht).2
        let k : Fin L.length := ⟨t.val - s z, by have hs := hlaunchT.2; omega⟩
        refine ⟨k, ?_, Fin.ext (by have hs := hlaunchT.2; dsimp only [k]; omega)⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp only [k]; omega
      · intro k hk
        let t : Fin p.T := ⟨s z + k.val, by have hh := k.isLt; have hB := firstCallBoundary_le_T rate rewards C_star C_h z; omega⟩
        have hlaunchT : actualLaunchBy rate rewards C_star C_h t.val z := ⟨hcross, Nat.le_add_right _ _⟩
        have hbefore : t.val < firstCallBoundary rate rewards C_star C_h z := by have hh := k.isLt; dsimp only [t]; omega
        have hE := (oldSelector_iff_calendar rate rewards C_star C_h t z).mpr
          ⟨hlaunchT, by have hh := (Finset.mem_filter.mp hk).2; dsimp only [t]; omega, hbefore⟩
        have hp := precallCells_take rate rewards C_star C_h t.val p.T (Nat.le_of_lt t.isLt) z L hL
        have hcutT : cutBoundary rate rewards C_star C_h t.val z = t.val := Nat.min_eq_left hbefore.le
        rw [hcutT, ite_eq_left hlaunchT] at hp
        obtain ⟨r, hr, _, hcell⟩ := hcells k
        have har : actualRecord rate rewards C_star C_h t z = some r := by
          simp only [actualRecord, show s z ≤ t.val from Nat.le_add_right _ _, ↓reduceIte]
          simpa only [t, Nat.add_sub_cancel_left] using hr
        obtain ⟨c, hold, hlive⟩ := oldReadout_afterLive rate rewards C_star C_h t z hlaunchT hbefore r har
          (by have hh := (Finset.mem_filter.mp hk).2; dsimp only [t]; omega)
        have hc : c = L[k.val] := Option.some.inj (by simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hold] using hcell)
        have ho : ReferenceFirstCollectionOldRecorderFoundation.oldCell? rate rewards C_star C_h t z = some L[k.val] := by
          simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, har, Option.bind_some, hold, hc]
        change _ = oldStatistic rate rewards C_star C_h f t z
        rw [oldStatistic, Set.indicator_of_mem hE, hp, Option.bind_some, ho, Option.map_some, Option.elim_some]
        simp only [id_eq, t, Nat.add_sub_cancel_left]
    rw [hL, Option.elim_some, ← hLive, ← hOld]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : Fin L.length => k.val < (V z).length)
      (fun k => f (RecordedQueueRun.run Q (L.take k.val)) L[k.val])).symm

private def currentStatistic
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (u t : Fin p.T) (z : SourceInput p) : ℝ :=
  (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t).indicator
    (fun z => ((ReferenceFirstCollectionCurrentRetainedGate.pastCells? rate rewards C_star C_h t z).bind fun L =>
      (ReferenceFirstCollectionCurrentNumericalCell.currentCell rate rewards C_star C_h t z).map
        (fun c => f (RecordedQueueRun.run Q L) c)).elim 0 id) z

private theorem listStatistic_append_singleton
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (L : List (RecordedQueueRun.RoundInput p.K)) (c : RecordedQueueRun.RoundInput p.K) :
    listStatistic rate f (L ++ [c]) = listStatistic rate f L + f (RecordedQueueRun.run Q L) c := by
  let g (k : Fin (L.length + 1)) := f (RecordedQueueRun.run Q ((L ++ [c]).take k.val))
    ((L ++ [c])[k.val]'(by simpa only [List.length_append, List.length_singleton] using k.isLt))
  have hsum : listStatistic rate f (L ++ [c]) = ∑ k, g k :=
    Fintype.sum_equiv (finCongr (by simp only [List.length_append, List.length_singleton])) _ _ (fun _ => rfl)
  rw [hsum, Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    simp only [g, Fin.val_castSucc, List.getElem_append_left k.isLt,
      List.take_append_of_le_length k.isLt.le]
  · simp only [g, Fin.val_last, List.take_left, List.getElem_append_right (Nat.le_refl L.length), Nat.sub_self, List.getElem_cons_zero]


private theorem firstInvocationStatistic_decomposition
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (z : SourceInput p) :
    (firstInvocationCells? rate rewards C_star C_h z).elim 0 (listStatistic rate f) =
      listStatistic rate f (V z) + (∑ t : Fin p.T, oldStatistic rate rewards C_star C_h f t z) +
        ∑ u : Fin p.T, ∑ t : Fin p.T, currentStatistic rate rewards C_star C_h f u t z := by
  have hpre := precallStatistic_decomposition rate rewards C_star C_h f z
  cases hcall : firstCollectionCall rate rewards C_star C_h z with
  | none =>
      have hcurrent (u t : Fin p.T) : currentStatistic rate rewards C_star C_h f u t z = 0 := by
        simp [currentStatistic, ReferenceCalendarCollectionCallControlLaw.firstCell, hcall, Set.indicator]
      rw [firstInvocationCells?_noCall rate rewards C_star C_h z hcall, hpre]
      simp only [hcurrent, Finset.sum_const_zero, add_zero]
  | some call =>
      rcases call with ⟨u, t, theta⟩
      have hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
        change (firstCollectionCall rate rewards C_star C_h z).map _ = some (u, t)
        simp only [hcall, Option.map_some]
      obtain ⟨L, c, hL, hc, _, hcarrier, _⟩ := firstInvocationCells?_firstCell_append rate rewards C_star C_h u t z hz
      have hterminal : precallCells? rate rewards C_star C_h p.T z = some L := by
        rw [precallCells_at_or_after_firstCell rate rewards C_star C_h u t p.T (Nat.le_of_lt t.isLt) z hz]
        exact hL
      have hcurrent : (∑ v : Fin p.T, ∑ w : Fin p.T, currentStatistic rate rewards C_star C_h f v w z) =
          f (RecordedQueueRun.run Q L) c := by
        have hcell (v w : Fin p.T) :
            z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h v w ↔ v = u ∧ w = t := by
          change (firstCollectionCall rate rewards C_star C_h z).map _ = some (v, w) ↔ _
          rw [hcall]
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          exact and_congr eq_comm eq_comm
        simp only [currentStatistic, Set.indicator_apply, hcell, ite_and]
        simp [hL, hc]
      rw [hterminal, Option.elim_some] at hpre
      rw [hcarrier, Option.elim_some, listStatistic_append_singleton, hpre, hcurrent]

private theorem oldStatistic_matches (S : ProductSetLaw.ProductSet p.K p.m) (t : Fin p.T) (z : SourceInput p) :
    oldStatistic rate rewards C_star C_h (rawStep rate S) t z = firstInvocationOldRawStepGap rate rewards C_star C_h t S z ∧
    oldStatistic rate rewards C_star C_h (weightedStep rate) t z =
      (∑ i : Fin p.K, incomingTheta rate rewards C_star C_h t i z *
        (G rate rewards C_star C_h t).indicator (oldRaw rate rewards C_star C_h t i) z) ∧
    oldStatistic rate rewards C_star C_h (activeBacklogStep rate) t z = costOld rate rewards C_star C_h t z := by
  by_cases he : z ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h t
  · obtain ⟨L, c, hL, hc, hr, hw, hb⟩ := oldStep_statistics rate rewards C_star C_h S t z he
    simp only [oldStatistic, Set.indicator_of_mem he, hL, Option.bind_some, hc, Option.map_some, Option.elim_some, id_eq]
    exact ⟨hr, hw, hb⟩
  · have hg : z ∉ G rate rewards C_star C_h t := fun h => he h.1.1
    simp [oldStatistic, he, firstInvocationOldRawStepGap, hg, costOld]

private theorem currentStatistic_matches (S : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) (z : SourceInput p) :
    currentStatistic rate rewards C_star C_h (rawStep rate S) u t z = rawGap rate rewards C_star C_h u t S z ∧
    currentStatistic rate rewards C_star C_h (weightedStep rate) u t z =
      (∑ i : Fin p.K, thetaMinus rate rewards C_star C_h u t i z *
        ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw rate rewards C_star C_h u t i z) ∧
    currentStatistic rate rewards C_star C_h (activeBacklogStep rate) u t z =
      (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
        (weightedBacklog rate rewards C_star C_h u t) z := by
  by_cases he : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t
  · obtain ⟨L, c, hL, hc, hr, hw, hb⟩ := currentStep_statistics rate rewards C_star C_h S u t z he
    simp only [currentStatistic, Set.indicator_of_mem he, hL, Option.bind_some, hc, Option.map_some, Option.elim_some, id_eq]
    exact ⟨hr, hw, hb⟩
  · have hg : z ∉ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t := fun h => he h.1
    have hr (i : Fin p.K) := ReferenceFirstCollectionCurrentRetainedMoments.retainedRaw_eq_zero_of_not_mem_firstCell rate rewards C_star C_h u t i z he
    simp [currentStatistic, he, rawGap, hr, hg]

/-- The actual zero-origin prefix splits into the original first LIVE raw gap,
the original OLD calendar, and the single original current invocation. -/
theorem firstInvocationRawGap_decomposition (S : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    firstInvocationRawGap rate rewards C_star C_h S z =
      firstWindowRawGap rate rewards C_star C_h z S + firstInvocationOldRawGap rate rewards C_star C_h S z +
        ∑ u : Fin p.T, ∑ t : Fin p.T, rawGap rate rewards C_star C_h u t S z := by
  have h := firstInvocationStatistic_decomposition rate rewards C_star C_h (rawStep rate S) z
  have hleft : (firstInvocationCells? rate rewards C_star C_h z).elim 0 (listStatistic rate (rawStep rate S)) =
      firstInvocationRawGap rate rewards C_star C_h S z := by
    cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
    | none => simp only [firstInvocationRawGap, hrounds, Option.elim_none]
    | some rounds => simp only [firstInvocationRawGap, hrounds, Option.elim_some, listStatistic,
        rawStep, weightedStep, acceptedRaw, RecordedQueueSummation.runMarginal]
  rw [hleft] at h
  simp_rw [(oldStatistic_matches rate rewards C_star C_h S _ z).1,
    (currentStatistic_matches rate rewards C_star C_h S _ _ z).1] at h
  simpa only [firstInvocationRawGap, firstInvocationOldRawGap, listStatistic, rawStep, weightedStep, acceptedRaw,
    RecordedQueueSummation.runMarginal, ReferenceFirstLiveRawPotentialBound.firstWindowRawGap,
    firstWindowAcceptedArrival, firstWindowMarginal, ReferenceFirstLiveRawPotentialBound.firstWindowRun,
    firstWindowCells, firstWindowQueue,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
    ReferenceFirstLaunchNumericalCell.queueParameters] using h

/-- Weighted accepted arrivals use the same incoming marginals throughout
LIVE, OLD, and the current first invocation. -/
theorem firstInvocationWeightedArrival_decomposition (z : SourceInput p) :
    firstInvocationWeightedArrival rate rewards C_star C_h z =
      firstInvocationLiveWeightedArrival rate rewards C_star C_h z +
        firstInvocationOldWeightedArrival rate rewards C_star C_h z +
        firstInvocationCurrentWeightedArrival rate rewards C_star C_h z := by
  obtain ⟨S, hS⟩ := ProductSetLaw.support_nonempty (ConstructorDimensions.m_pos p) p.m_lt_K
  let comparator : ProductSetLaw.ProductSet p.K p.m := ⟨S, hS⟩
  have h := firstInvocationStatistic_decomposition rate rewards C_star C_h (weightedStep rate) z
  have hleft : (firstInvocationCells? rate rewards C_star C_h z).elim 0 (listStatistic rate (weightedStep rate)) =
      firstInvocationWeightedArrival rate rewards C_star C_h z := by
    cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
    | none => simp only [firstInvocationWeightedArrival, hrounds, Option.elim_none]
    | some rounds => simp only [firstInvocationWeightedArrival, hrounds, Option.elim_some, listStatistic,
        weightedStep, acceptedRaw, RecordedQueueSummation.runMarginal]
  rw [hleft] at h
  simp_rw [(oldStatistic_matches rate rewards C_star C_h comparator _ z).2.1,
    (currentStatistic_matches rate rewards C_star C_h comparator _ _ z).2.1] at h
  simpa only [firstInvocationWeightedArrival, firstInvocationLiveWeightedArrival,
    firstInvocationOldWeightedArrival, firstInvocationCurrentWeightedArrival, listStatistic, weightedStep, acceptedRaw,
    RecordedQueueSummation.runMarginal, firstWindowAcceptedArrival, firstWindowMarginal,
    ReferenceFirstLiveRawPotentialBound.firstWindowRun, firstWindowCells, firstWindowQueue,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
    ReferenceFirstLaunchNumericalCell.queueParameters] using h

private theorem firstLiveStatistic_cost (z : SourceInput p) :
    listStatistic rate (activeBacklogStep rate) (V z) =
      ∑ t : Fin p.T, ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost rate rewards C_star C_h t z := by
  let cost := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost rate rewards C_star C_h
  have hend := ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary rate rewards C_star C_h z
  change s z + (V z).length ≤ firstCallBoundary rate rewards C_star C_h z at hend
  have hT := hend.trans (firstCallBoundary_le_T rate rewards C_star C_h z)
  let date (k : Fin (V z).length) : Fin p.T := ⟨s z + k.val, by have hk := k.isLt; omega⟩
  have hmatch (k : Fin (V z).length) : cost (date k) z =
      activeBacklogStep rate (RecordedQueueRun.run Q ((V z).take k.val)) (V z)[k.val] := by
    have hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true := by
      by_contra hn
      have hV : V z = [] := by
        change ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h z = []
        simp only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells, dite_eq_right hn]
      exact (Nat.not_lt_zero k.val) (k.isLt.trans_eq (congrArg List.length hV))
    have hevent : z ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent rate rewards C_star C_h (date k) ↔
        (V z)[k.val].enabled = true ∧ (RecordedQueueRun.run Q ((V z).take k.val)).overflow = false := by
      change ((ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true ∧
        s z ≤ (date k).val ∧ ∃ hn : (date k).val - s z < (V z).length,
          (V z)[(date k).val - s z].enabled = true ∧ (RecordedQueueRun.run Q ((V z).take ((date k).val - s z))).overflow = false) ↔ _
      simp only [date, Nat.add_sub_cancel_left, hc, Nat.le_add_right, true_and, k.isLt]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩
    have hb : ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt rate rewards C_star C_h (date k).val z =
        RecordedWeightedDrift.weightedBacklog p.m Q (RecordedQueueRun.run Q ((V z).take k.val)) := by
      simp only [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt, date, Nat.add_sub_cancel_left]
      rfl
    simp only [cost, ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost,
      Set.indicator_apply, hevent, hb, activeBacklogStep]
  unfold listStatistic
  apply Finset.sum_bij_ne_zero (fun k _ _ => date k)
  · intro k _ _; exact Finset.mem_univ _
  · intro a _ _ b _ _ hab
    apply Fin.ext
    have h := congrArg (fun t : Fin p.T => t.val) hab
    dsimp only [date] at h
    omega
  · intro t ht hn
    have he : z ∈ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent rate rewards C_star C_h t := by
      by_contra hnot
      exact hn (Set.indicator_of_notMem hnot _)
    obtain ⟨_, hs, hk, _, _⟩ := he
    let k : Fin (V z).length := ⟨t.val - s z, hk⟩
    have heq : date k = t := Fin.ext (by dsimp only [date, k]; change s z ≤ t.val at hs; omega)
    refine ⟨k, Finset.mem_univ _, ?_, heq⟩
    rw [← hmatch k, heq]
    exact hn
  · intro k _ _; exact (hmatch k).symm

/-- The active incoming backlog sum is exactly the three retained source
calendar costs. Disabled, zero-arrival, and detecting updates keep their masks. -/
theorem firstInvocationCost_decomposition (z : SourceInput p) :
    firstInvocationActiveBacklog rate rewards C_star C_h z = firstInvocationCost rate rewards C_star C_h z := by
  obtain ⟨S, hS⟩ := ProductSetLaw.support_nonempty (ConstructorDimensions.m_pos p) p.m_lt_K
  let comparator : ProductSetLaw.ProductSet p.K p.m := ⟨S, hS⟩
  have h := firstInvocationStatistic_decomposition rate rewards C_star C_h (activeBacklogStep rate) z
  simp_rw [(oldStatistic_matches rate rewards C_star C_h comparator _ z).2.2,
    (currentStatistic_matches rate rewards C_star C_h comparator _ _ z).2.2] at h
  rw [firstLiveStatistic_cost rate rewards C_star C_h z] at h
  have hactive : (firstInvocationCells? rate rewards C_star C_h z).elim 0 (listStatistic rate (activeBacklogStep rate)) =
      firstInvocationActiveBacklog rate rewards C_star C_h z := by
    cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
    | none => simp only [firstInvocationActiveBacklog, hrounds, Option.elim_none]
    | some rounds =>
        simp only [firstInvocationActiveBacklog, hrounds, Option.elim_some, listStatistic,
          activeBacklogStep, Finset.sum_filter, RecordedWeightedDrift.weightedBacklog, RecordedQueueSummation.runMarginal]
  rw [hactive] at h
  exact h

/-- The signed correction is charged to the literal actual calendar cost and
weighted accepted arrivals of this one continuous zero-origin queue run. -/
theorem firstInvocationCorrection_le (z : SourceInput p) :
    firstInvocationCorrection rate rewards C_star C_h z ≤
      8 * rate.eta.val * (firstInvocationCost rate rewards C_star C_h z + firstInvocationWeightedArrival rate rewards C_star C_h z) := by
  rw [← firstInvocationCost_decomposition rate rewards C_star C_h z]
  cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
  | none => simp only [firstInvocationCorrection, firstInvocationActiveBacklog,
      firstInvocationWeightedArrival, hrounds, Option.elim_none, add_zero, mul_zero, le_refl]
  | some rounds => exact firstInvocationCorrection_le_activeBacklog rate rewards C_star C_h z rounds hrounds

private theorem cell0_rate (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r = some c) :
    ∀ i, 32 * (Q).eta ≤ c.rate i := by
  unfold ReferenceFirstCollectionCurrentRetainedGate.cell0 at hc
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some d =>
      have hdc : d = c := Option.some.inj (by simpa only [hl, Option.some_or] using hc)
      subst d
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hl
      intro i
      rw [hrate, selected.view.payload.rate_eq_canonical]
      exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property _ i
  | none =>
      have hold : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
        simpa only [hl, Option.none_or] using hc
      obtain ⟨payload, _, _, _, _, _, _, _, _, _, hrate, _⟩ :=
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hold
      intro i
      rw [hrate, payload.rate_eq_canonical]
      exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property _ i

/-- The terminal term at boundary `N` is bounded on every original source,
including an absent launch and a no-call horizon. -/
theorem firstInvocationTerminalCorrection_le (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) :
    firstInvocationTerminalCorrection rate rewards C_star C_h S z ≤
      (p.m : ℝ) / (16 * rate.eta.val) := by
  cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
  | none =>
      simp only [firstInvocationTerminalCorrection, hrounds, Option.elim_none]
      exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) rate.eta.property.le)
  | some rounds =>
      obtain ⟨_, _, hcells⟩ := firstInvocationCells?_support rate rewards C_star C_h z rounds hrounds
      have hrate : ∀ c ∈ rounds, ∀ i, 32 * (Q).eta ≤ c.rate i := by
        intro c hc
        obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hc
        obtain ⟨r, _, _, hr⟩ := hcells ⟨k, hk⟩
        exact cell0_rate rate r c (by simpa only [heq] using hr)
      have hb (i : Fin p.K) :
          StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (rounds.take rounds.length)) i ≤
            1 / (16 * rate.eta.val) := by
        have h := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold Q rounds hrate rounds.length i
        have heq : 2 * (1 / (32 * (Q).eta)) = 1 / (16 * rate.eta.val) := by
          change 2 * (1 / (32 * rate.eta.val)) = _
          ring
        exact h.trans_eq heq
      have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
      have hsum : (∑ i ∈ S.1,
          StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (rounds.take rounds.length)) i) ≤
            (p.m : ℝ) / (16 * rate.eta.val) := by
        calc
          _ ≤ ∑ i ∈ S.1, 1 / (16 * rate.eta.val) := Finset.sum_le_sum fun i _ => hb i
          _ = _ := by simp [hcard, div_eq_mul_inv]
      have hw : 0 ≤ ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal Q p.m rounds rounds.length i *
            StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (rounds.take rounds.length)) i :=
        Finset.sum_nonneg fun i _ => mul_nonneg
          (RecordedQueueSummation.runMarginal_pos Q p.m rounds rounds.length i p.two_le_m p.m_lt_K).le
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      simp only [firstInvocationTerminalCorrection, hrounds, Option.elim_some]
      linarith only [hsum, hw]

/-- One potential normalizer bounds the raw comparator on the complete actual
inclusive prefix. The signed correction uses all successors and terminal `theta_N`. -/
theorem firstInvocationRawGap_le (S : ProductSetLaw.ProductSet p.K p.m)
    (z : SourceInput p) :
    firstInvocationRawGap rate rewards C_star C_h S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) + firstInvocationCorrection rate rewards C_star C_h z := by
  have hterminal := firstInvocationTerminalCorrection_le rate rewards C_star C_h S z
  have hserved : firstInvocationServedGap rate rewards C_star C_h S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) := by
    cases hrounds : firstInvocationCells? rate rewards C_star C_h z with
    | none =>
        simp only [firstInvocationServedGap, hrounds, Option.elim_none]
        have hc : (1 : ℝ) ≤ (Nat.choose p.K p.m : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (Nat.choose_pos p.m_lt_K.le))
        exact add_nonneg (div_nonneg (Real.log_nonneg hc)
          (RecordedPotentialStep.potentialLambda_pos Q).le)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
            (RecordedPotentialStep.potentialLambda_pos Q).le) (Nat.cast_nonneg _))
    | some rounds =>
        have h := firstInvocationServedGap_le_length rate rewards C_star C_h S z rounds hrounds
        have hlen : (rounds.length : ℝ) ≤ (p.T : ℝ) := by
          exact_mod_cast ((firstInvocationCells?_support rate rewards C_star C_h z rounds hrounds).2.1.trans
            (Nat.sub_le _ _))
        have hcoeff : 0 ≤ 16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
            (RecordedPotentialStep.potentialLambda_pos Q).le
        have hmul := mul_le_mul_of_nonneg_left hlen hcoeff
        linarith only [h, hmul]
  rw [firstInvocationRawGap_eq_served_terminal_add_correction]
  linarith only [hserved, hterminal]


end Bandits.Support.ReferenceFirstCollectionFirstInvocationRawPotential

end
