/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalRawPrefixJoin
public import Bandits.Support.ReferenceFirstCollectionRenewalNextLearningMoments
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureLearningMoments

import Mathlib.Tactic

/-!
# Raw potential on the actual first-renewal endpoint prefix

This module records finite scalar observations on the literal optional prefix
through the first-renewal endpoint. The carrier, list, queue run, and endpoint
are the existing source objects. No source law or probability statement is
introduced here.
-/

@[expose] public section

noncomputable section

open Bandits.Support ConstructorDimensions
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalRawPotential

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Z" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
    rate rewards C_star C_h u t
local notation "κ" =>
  ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
    rate rewards C_star C_h u t

/-- The literal optional numerical prefix through the actual inclusive
first-replacement endpoint. -/
def endpointCells? (z : Z) : Option (List (RecordedQueueRun.RoundInput p.K)) :=
  ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
      rate rewards C_star C_h u t
      (ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
        rate rewards C_star C_h u t z) z)

/-- The actual accepted arrival divided by the source denominator at a slot
of a present endpoint word. -/
def endpointArrival (rounds : List (RecordedQueueRun.RoundInput p.K))
    (k : Fin rounds.length) (i : Fin p.K) : ℝ :=
  ((RecordedQueueRun.acceptedArrival
      (RecordedQueueRun.acceptedRecord Q
        (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
    (rate.n : ℝ))

/-- Raw comparator gap on the complete actual endpoint word. -/
def endpointRawGap (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  (endpointCells? rate rewards C_star C_h u t z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length,
      ((∑ i ∈ S.1, endpointArrival rate rounds k i) -
        ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
            endpointArrival rate rounds k i)

/-- Served comparator gap on the same endpoint word. -/
def endpointServedGap (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  (endpointCells? rate rewards C_star C_h u t z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length,
      ((∑ i ∈ S.1,
          RecordedPotentialStep.servedEstimate Q
            (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) -
        ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
            RecordedPotentialStep.servedEstimate Q
              (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i)

/-- Weighted accepted arrivals on the same complete endpoint word. -/
def endpointWeightedArrival (z : Z) : ℝ :=
  (endpointCells? rate rewards C_star C_h u t z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length, ∑ i : Fin p.K,
      RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
        endpointArrival rate rounds k i

/-- All-successor signed marginal/backlog correction, with terminal marginal
at `rounds.length`. -/
def endpointCorrection (z : Z) : ℝ :=
  (endpointCells? rate rewards C_star C_h u t z).elim 0 fun rounds =>
    ∑ k : Fin rounds.length, ∑ i : Fin p.K,
      (RecordedQueueSummation.runMarginal Q p.m rounds (k.val + 1) i -
        RecordedQueueSummation.runMarginal Q p.m rounds k.val i) *
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take (k.val + 1))) i

/-- Active incoming weighted backlog on the complete endpoint word. The mask
keeps enabled zero-arrival and first-overflow updates and excludes disabled
and already-overflowed rows. -/
def endpointActiveBacklog (z : Z) : ℝ :=
  (endpointCells? rate rewards C_star C_h u t z).elim 0 fun rounds =>
    ∑ k ∈ Finset.univ.filter (fun k : Fin rounds.length =>
        rounds[k.val].enabled = true ∧
          (RecordedQueueRun.run Q (rounds.take k.val)).overflow = false),
      ∑ i : Fin p.K,
        RecordedQueueSummation.runMarginal Q p.m rounds k.val i *
          StoppedQueueBound.normalizedBacklog Q
            (RecordedQueueRun.run Q (rounds.take k.val)) i

/-- Terminal comparator-minus-weighted-backlog term at the actual endpoint.
It uses the terminal marginal at the same length as the all-successor sum. -/
def endpointTerminalCorrection (S : ProductSetLaw.ProductSet p.K p.m)
    (z : Z) : ℝ :=
  (endpointCells? rate rewards C_star C_h u t z).elim 0 fun rounds =>
    (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take rounds.length)) i) -
      ∑ i : Fin p.K,
        RecordedQueueSummation.runMarginal Q p.m rounds rounds.length i *
          StoppedQueueBound.normalizedBacklog Q
            (RecordedQueueRun.run Q (rounds.take rounds.length)) i

/-- The accepted endpoint root supplies the unique actual whole endpoint
word and all its literal prefix restrictions. -/
theorem endpointCells_present (z : Z) :
    ∃ rounds, endpointCells? rate rewards C_star C_h u t z = some rounds ∧
      rounds.length = κ z -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z := by
  obtain ⟨rounds, hrounds, hlen, _, _, _⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_and_takes
      rate rewards C_star C_h u t z
  exact ⟨rounds, hrounds, hlen⟩

/-- The accepted endpoint root also identifies the original first-invocation
word as the literal take ending just after date `t`, and supplies every
intermediate optional prefix from the same endpoint list. -/
theorem endpointCells_current_take_and_prefixes (z : Z) :
    ∃ rounds,
      endpointCells? rate rewards C_star C_h u t z = some rounds ∧
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCells?
        rate rewards C_star C_h z.val =
          some (rounds.take (t.val + 1 -
            ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
              rate rewards C_star C_h u t z)) ∧
      rounds.length = κ z -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z ∧
      (∀ n,
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
            rate rewards C_star C_h u t z ≤ n →
        n ≤ κ z →
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
          (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
            rate rewards C_star C_h u t n z) =
            some (rounds.take (n -
              ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
                rate rewards C_star C_h u t z))) := by
  obtain ⟨rounds, hrounds, hlen, _, hfirst, hprefix⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_and_takes
      rate rewards C_star C_h u t z
  exact ⟨rounds, by simpa [endpointCells?] using hrounds, hfirst, hlen,
    fun n hn1 hn2 => (hprefix n hn1 hn2).1⟩

/-- At the last physical call, the inclusive endpoint is exactly the horizon,
and the endpoint observer is the original first-invocation observer on the
same literal numerical word. -/
theorem endpointStatistics_eq_firstInvocation_at_lastCall
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (hlast : t.val + 1 = p.T) :
    κ z = p.T ∧
    endpointRawGap rate rewards C_star C_h u t S z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z.val ∧
    endpointWeightedArrival rate rewards C_star C_h u t z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h z.val ∧
    endpointActiveBacklog rate rewards C_star C_h u t z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationActiveBacklog
        rate rewards C_star C_h z.val ∧
    endpointCorrection rate rewards C_star C_h u t z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection
        rate rewards C_star C_h z.val := by
  have hend := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hκ : κ z = p.T := by
    have hlow : t.val + 1 ≤ κ z := hend.1.trans hend.2.1
    omega
  have hwords := endpointCells_current_take_and_prefixes
    rate rewards C_star C_h u t z
  obtain ⟨rounds, hrounds, hfirst, hlength, _⟩ := hwords
  have htake : rounds.take
      (t.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z) = rounds := by
    apply List.take_of_length_le
    rw [hlength, hκ]
    omega
  have hfirst' :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCells?
        rate rewards C_star C_h z.val = some rounds := by
    rw [hfirst, htake]
  constructor
  · exact hκ
  constructor
  · simp [endpointRawGap, endpointArrival,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap,
      hrounds, hfirst']
  constructor
  · simp [endpointWeightedArrival, endpointArrival,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival,
      hrounds, hfirst']
  constructor
  · simp [endpointActiveBacklog,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationActiveBacklog,
      hrounds, hfirst']
  · simp [endpointCorrection,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection,
      hrounds, hfirst']

/-- The signed one-step correction at the immediate next date, using exactly
the retained selector and its pre/post marginal and post backlog readouts. -/
def nextDateSignedIncrement (z : Z) : ℝ :=
  if hq : t.val + 1 < p.T then
    (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
      rate rewards C_star C_h u t hq).indicator
        (fun z => ∑ i : Fin p.K,
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.postTheta
              rate rewards C_star C_h u t hq z i -
            ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta
              rate rewards C_star C_h u t z i) *
          ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.postBacklog
            rate rewards C_star C_h u t hq z i) z
  else 0

/-- The signed correction at one actual strict-future calendar date, using the
existing supported incoming/outgoing marginal and post-backlog selectors. -/
def strictFutureSignedIncrementAt (n : ℕ) (z : Z) : ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t ⟨n, hn⟩ hf).indicator
        (fun z => ∑ i : Fin p.K,
          (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaPlus
              rate rewards C_star C_h u t ⟨n, hn⟩ hf i z -
            ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
              rate rewards C_star C_h u t ⟨n, hn⟩ hf i z) *
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureBacklogPlus
            rate rewards C_star C_h u t ⟨n, hn⟩ hf i z) z
    else 0
  else 0

/-- Sum the literal signed corrections over the admitted strict-future dates.
Every signed increment is retained, including negative values. -/
def strictFutureSignedIncrementTotal (z : Z) : ℝ :=
  ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
    strictFutureSignedIncrementAt rate rewards C_star C_h u t n z

private theorem eta_mul_source_den_le_one (rate : ReferenceActivePhysicalStep.RateInput p) :
    rate.eta.val * (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 := by
  have hcap : rate.eta.val ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) := by
    calc
      _ ≤ _ := rate.sourceCap
      _ = _ := by simp only [one_div, mul_inv_rev]
  have hm := ConstructorDimensions.m_pos p
  have hK := ConstructorDimensions.K_pos p
  have hL := CanonicalRecordingRates.L_stab_ge_one p
  exact (le_div_iff₀ (by positivity)).mp hcap

private theorem eta_denominator_ge {p : ConstructorDimensions.Parameters}
    (c : ℝ) (hc : c ≤ 1024) (hc0 : 0 ≤ c) :
    c * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast (CanonicalRecordingRates.L_stab_ge_one p)
  have hprod := mul_le_mul_of_nonneg_left
    (one_le_mul_of_one_le_of_one_le hK hL)
    (mul_nonneg hc0 (Nat.cast_nonneg p.m))
  have hscale := mul_le_mul_of_nonneg_right hc
    (by positivity : 0 ≤ (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))
  nlinarith only [hprod, hscale]

private theorem four_m_eta_le_one : 4 * (p.m : ℝ) * (Q).eta ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left
    (eta_denominator_ge (p := p) 4 (by norm_num) (by norm_num))
    rate.eta.property.le
  have hcap := eta_mul_source_den_le_one rate
  change 4 * (p.m : ℝ) * rate.eta.val ≤ 1
  nlinarith only [h, hcap]

private theorem eta_le_one_div_sixtyfour : (Q).eta ≤ 1 / 64 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hden := eta_denominator_ge (p := p) 64 (by norm_num) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left
    (show (64 : ℝ) ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) by nlinarith only [hm, hden])
    rate.eta.property.le
  have hcap := eta_mul_source_den_le_one rate
  change rate.eta.val ≤ 1 / 64
  nlinarith only [hmul, hcap]

private theorem prefix_backlog_le_arrival
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (k : Fin rounds.length) (i : Fin p.K) :
    StoppedQueueBound.normalizedBacklog Q
        (RecordedQueueRun.run Q (rounds.take (k.val + 1))) i ≤
      StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take k.val)) i +
        endpointArrival rate rounds ⟨k.val, k.isLt⟩ i := by
  let state := RecordedQueueRun.run Q (rounds.take k.val)
  let round := rounds[k.val]
  have hNatStep :
      ((RecordedQueueRun.step Q state round).registers i).2 ≤
        (state.registers i).2 +
          RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord Q state round i) := by
    change (QueueReplay.transition (4 * (Q).n) (state.registers i)
        (RecordedQueueRun.acceptedRecord Q state round i)).2 ≤ _
    cases hrecord : RecordedQueueRun.acceptedRecord Q state round i with
    | mk enabled amount => cases enabled <;>
        simp [QueueReplay.transition, RecordedQueueRun.acceptedArrival]
  have hstep := RecordedPotentialStep.run_take_succ_eq_step Q rounds k.val k.isLt
  have hNat :
      ((RecordedQueueRun.run Q (rounds.take (k.val + 1))).registers i).2 ≤
        (state.registers i).2 +
          RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord Q state round i) := by
    rw [hstep]
    exact hNatStep
  have hReal :
      (((RecordedQueueRun.run Q (rounds.take (k.val + 1))).registers i).2 : ℝ) ≤
        ((state.registers i).2 : ℝ) +
          (RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord Q state round i) : ℝ) := by
    exact_mod_cast hNat
  have hDiv := div_le_div_of_nonneg_right hReal (Nat.cast_nonneg (Q).n)
  change (((RecordedQueueRun.run Q (rounds.take (k.val + 1))).registers i).2 : ℝ) /
      (rate.n : ℝ) ≤ ((state.registers i).2 : ℝ) / (rate.n : ℝ) +
        ((RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord Q state round i) : ℝ) / (rate.n : ℝ))
  rw [← add_div]
  simpa [state, round, endpointArrival, ReferenceFirstLaunchNumericalCell.queueParameters]
    using hDiv

/-- The signed all-successor correction is bounded by the active incoming
backlog and weighted arrivals on this same actual word. -/
theorem endpointCorrection_le_activeBacklog (z : Z)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    endpointCorrection rate rewards C_star C_h u t z ≤
      8 * rate.eta.val *
        (endpointActiveBacklog rate rewards C_star C_h u t z +
          endpointWeightedArrival rate rewards C_star C_h u t z) := by
  classical
  let θ := RecordedQueueSummation.runMarginal Q p.m rounds
  let b (k : ℕ) := StoppedQueueBound.normalizedBacklog Q
    (RecordedQueueRun.run Q (rounds.take k))
  let A (k : Fin rounds.length) (i : Fin p.K) : ℝ :=
      endpointArrival rate rounds k i
  let active := Finset.univ.filter fun k : Fin rounds.length =>
    rounds[k.val].enabled = true ∧
      (RecordedQueueRun.run Q (rounds.take k.val)).overflow = false
  have hθ (k : ℕ) (i : Fin p.K) : 0 ≤ θ k i :=
    (RecordedQueueSummation.runMarginal_pos Q p.m rounds k i
      p.two_le_m p.m_lt_K).le
  have hb (k : ℕ) (i : Fin p.K) : 0 ≤ b k i :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA (k : Fin rounds.length) (i : Fin p.K) : 0 ≤ A k i := by
    change 0 ≤ ((RecordedQueueRun.acceptedArrival
      (RecordedQueueRun.acceptedRecord Q
        (RecordedQueueRun.run Q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
      (rate.n : ℝ))
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ 8 * rate.eta.val :=
    mul_nonneg (by norm_num) rate.eta.property.le
  have hstep (k : Fin rounds.length) :
      (∑ i, (θ (k.val + 1) i - θ k.val i) * b (k.val + 1) i) ≤
        if k ∈ active then 8 * rate.eta.val *
          ((∑ i, θ k.val i * b k.val i) + ∑ i, θ k.val i * A k i) else 0 := by
    by_cases hk : k ∈ active
    · rw [ite_eq_left hk]
      have hg (i : Fin p.K) :
          θ (k.val + 1) i - θ k.val i ≤ 8 * rate.eta.val * θ k.val i := by
        obtain ⟨h1, h2⟩ := RecordedMarginalGrowth.run_prefix_theta_growth
          Q rounds k.val k.isLt i p.two_le_m p.m_lt_K
          (eta_le_one_div_sixtyfour rate)
        change θ (k.val + 1) i ≤ Real.exp (4 * (Q).eta) * θ k.val i at h1
        change Real.exp (4 * (Q).eta) * θ k.val i ≤
          (1 + 8 * (Q).eta) * θ k.val i at h2
        have he : (Q).eta = rate.eta.val := rfl
        rw [he] at h1 h2
        linarith only [h1, h2]
      calc
        _ ≤ ∑ i, (8 * rate.eta.val * θ k.val i) *
            (b k.val i + A k i) := by
          apply Finset.sum_le_sum
          intro i _
          exact (mul_le_mul_of_nonneg_right (hg i) (hb _ _)).trans
            (mul_le_mul_of_nonneg_left
              (prefix_backlog_le_arrival rate rounds k i)
              (mul_nonneg hcoef (hθ _ _)))
        _ = _ := by
          simp only [mul_add, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
    · rw [ite_eq_right hk]
      have hstop : rounds[k.val].enabled = false ∨
          (RecordedQueueRun.run Q (rounds.take k.val)).overflow = true := by
        cases he : rounds[k.val].enabled <;>
          cases ho : (RecordedQueueRun.run Q (rounds.take k.val)).overflow <;>
          simp_all [active]
      have heq (i : Fin p.K) : θ (k.val + 1) i = θ k.val i :=
        RecordedMarginalGrowth.run_prefix_theta_eq_of_disabled_or_overflowed
          (m := p.m) Q rounds k.val k.isLt i hstop
      simp only [heq, sub_self, zero_mul, Finset.sum_const_zero, le_refl]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hstep k)
  have harrival :
      (∑ k ∈ active, ∑ i, θ k.val i * A k i) ≤
        ∑ k : Fin rounds.length, ∑ i, θ k.val i * A k i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ active)
      (fun k _ _ => Finset.sum_nonneg fun i _ => mul_nonneg (hθ _ _) (hA k i))
  have hcombined := mul_le_mul_of_nonneg_left
    (add_le_add_right harrival
      (∑ k ∈ active, ∑ i, θ k.val i * b k.val i)) hcoef
  simp only [Finset.sum_ite_mem, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.univ_inter] at hsum
  have hresult := hsum.trans hcombined
  simpa only [endpointCorrection, endpointActiveBacklog, endpointWeightedArrival,
    hrounds, Option.elim_some, θ, b, A, active, endpointArrival,
    RecordedQueueSummation.runMarginal,
    ReferenceFirstLaunchNumericalCell.queueParameters] using hresult

/-- One normalizer bounds the served gap along the complete endpoint word. -/
theorem endpointServedGap_le_length (S : ProductSetLaw.ProductSet p.K p.m)
    (z : Z) (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    endpointServedGap rate rewards C_star C_h u t S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q *
          (rounds.length : ℝ) := by
  have hpotential := RecordedPotentialTelescope.servedEstimate_cumulative_comparison
    Q rounds p.two_le_m p.m_lt_K (four_m_eta_le_one rate) S
  simpa [endpointServedGap, hrounds, RecordedQueueSummation.runMarginal,
    ReferenceFirstLaunchNumericalCell.queueParameters] using hpotential

/-- Exact finite-run summation by parts, with terminal marginal at the full
word length and every successor represented in `endpointCorrection`. -/
theorem endpointRawGap_eq_served_terminal_add_correction
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    endpointRawGap rate rewards C_star C_h u t S z =
      endpointServedGap rate rewards C_star C_h u t S z +
        endpointTerminalCorrection rate rewards C_star C_h u t S z +
        endpointCorrection rate rewards C_star C_h u t z := by
  classical
  obtain ⟨rounds, hrounds, _⟩ := endpointCells_present rate rewards C_star C_h u t z
  have hsummation := RecordedQueueSummation.run_raw_served_summation_by_parts_all
    Q rounds p.two_le_m p.m_lt_K S
  have hsum :
      endpointRawGap rate rewards C_star C_h u t S z =
        endpointServedGap rate rewards C_star C_h u t S z +
          (∑ i ∈ S.1,
            StoppedQueueBound.normalizedBacklog Q
              (RecordedQueueRun.run Q (rounds.take rounds.length)) i) -
          (∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal Q p.m rounds rounds.length i *
              StoppedQueueBound.normalizedBacklog Q
                (RecordedQueueRun.run Q (rounds.take rounds.length)) i) +
          endpointCorrection rate rewards C_star C_h u t z := by
    simpa [endpointRawGap, endpointServedGap, endpointCorrection,
      endpointArrival, hrounds, RecordedQueueSummation.runMarginal,
      ReferenceFirstLaunchNumericalCell.queueParameters] using hsummation
  rw [hsum]
  simp only [endpointTerminalCorrection, hrounds, Option.elim_some]
  ring

private theorem endpoint_cell_rate
    (r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell
      rate r = some c) : ∀ i, 32 * (Q).eta ≤ c.rate i := by
  unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell at hc
  cases hl : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 r with
  | some d =>
      have hdc : d = c := Option.some.inj (by simpa only [hl, Option.some_or] using hc)
      subst d
      obtain ⟨_, selected, _, _, hrate, _⟩ :=
        ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 r c hl
      intro i
      rw [hrate, selected.view.payload.rate_eq_canonical]
      exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi
        p rate.eta.property _ i
  | none =>
      have hold : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 r = some c := by
        simpa only [hl, Option.none_or] using hc
      obtain ⟨payload, _, _, _, _, _, _, _, _, _, hrate, _⟩ :=
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 r c hold
      intro i
      rw [hrate, payload.rate_eq_canonical]
      exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi
        p rate.eta.property _ i

private theorem endpoint_cells_rates
    (z : Z) (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    ∀ c ∈ rounds, ∀ i, 32 * (Q).eta ≤ c.rate i := by
  intro c hc i
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hc
  obtain ⟨L, r, c', hL, _, _, hcell, _, hslot, _, _⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_successor
      rate rewards C_star C_h u t z
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z + k)
      (by omega)
      (by
        obtain ⟨base, hbase, hbaseLen⟩ := endpointCells_present rate rewards C_star C_h u t z
        have heq : rounds = base := Option.some.inj (hrounds.symm.trans hbase)
        have hlen : rounds.length =
            ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex
                rate rewards C_star C_h u t z -
              ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
                rate rewards C_star C_h u t z := by
          rw [heq]
          exact hbaseLen
        omega)
  have hLeq : L = rounds := Option.some.inj (hL.symm.trans hrounds)
  have hc' : c' = c := by
    have hslot' := hslot
    rw [hLeq] at hslot'
    have hslot'' : some rounds[k] = some c' := by
      simpa [List.getElem?_eq_getElem hk, Nat.add_sub_cancel_left] using hslot'
    exact (Option.some.inj hslot'').symm.trans hget
  subst c'
  exact endpoint_cell_rate rate r c hcell i

/-- The terminal comparator term retains the actual last update and is
bounded by the canonical source-rate queue cap on every endpoint slot. -/
theorem endpointTerminalCorrection_le
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    endpointTerminalCorrection rate rewards C_star C_h u t S z ≤
      (p.m : ℝ) / (16 * rate.eta.val) := by
  have hrate := endpoint_cells_rates rate rewards C_star C_h u t z rounds hrounds
  have hb (i : Fin p.K) :
      StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take rounds.length)) i ≤
        1 / (16 * rate.eta.val) := by
    have h := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      Q rounds hrate rounds.length i
    have heq : 2 * (1 / (32 * (Q).eta)) = 1 / (16 * rate.eta.val) := by
      change 2 * (1 / (32 * rate.eta.val)) = _
      ring
    exact h.trans_eq heq
  have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
  have hsum :
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take rounds.length)) i) ≤
        (p.m : ℝ) / (16 * rate.eta.val) := by
    calc
      _ ≤ ∑ i ∈ S.1, 1 / (16 * rate.eta.val) :=
        Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp [hcard, div_eq_mul_inv]
  have hw : 0 ≤ ∑ i : Fin p.K,
      RecordedQueueSummation.runMarginal Q p.m rounds rounds.length i *
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (rounds.take rounds.length)) i :=
    Finset.sum_nonneg fun i _ => mul_nonneg
      (RecordedQueueSummation.runMarginal_pos Q p.m rounds rounds.length i
        p.two_le_m p.m_lt_K).le
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  simp only [endpointTerminalCorrection, hrounds, Option.elim_some]
  exact sub_le_iff_le_add.mpr (by
    nlinarith only [hsum, hw])

/-- The single normalizer, queue terminal, and signed all-successor correction
bound the raw comparator on this exact endpoint word. -/
theorem endpointRawGap_le_length
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    endpointRawGap rate rewards C_star C_h u t S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q *
          (rounds.length : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        8 * rate.eta.val *
          (endpointActiveBacklog rate rewards C_star C_h u t z +
            endpointWeightedArrival rate rewards C_star C_h u t z) := by
  have hdecomp := endpointRawGap_eq_served_terminal_add_correction
    rate rewards C_star C_h u t S z
  have hserved := endpointServedGap_le_length rate rewards C_star C_h u t S z rounds hrounds
  have hterminal := endpointTerminalCorrection_le rate rewards C_star C_h u t S z rounds hrounds
  have hcorrection := endpointCorrection_le_activeBacklog rate rewards C_star C_h u t z rounds hrounds
  rw [hdecomp]
  linarith

/-- The endpoint word is no longer than the physical horizon. -/
theorem endpointCells_length_le_horizon (z : Z)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    (rounds.length : ℝ) ≤ (p.T : ℝ) := by
  obtain ⟨_, hpresent, hlength⟩ := endpointCells_present rate rewards C_star C_h u t z
  have hEq : rounds = _ := Option.some.inj (hrounds.symm.trans hpresent)
  rw [hEq, hlength]
  have hbound := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  exact_mod_cast ((Nat.sub_le _ _).trans hbound.2.2)

/-- Horizon form of the deterministic endpoint-prefix potential inequality. -/
theorem endpointRawGap_le_horizon
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrounds : endpointCells? rate rewards C_star C_h u t z = some rounds) :
    endpointRawGap rate rewards C_star C_h u t S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q *
          (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        8 * rate.eta.val *
          (endpointActiveBacklog rate rewards C_star C_h u t z +
            endpointWeightedArrival rate rewards C_star C_h u t z) := by
  have hraw := endpointRawGap_le_length rate rewards C_star C_h u t S z rounds hrounds
  have hlen := endpointCells_length_le_horizon rate rewards C_star C_h u t z rounds hrounds
  have hcoeff : 0 ≤
      16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (RecordedPotentialStep.potentialLambda_pos Q).le
  calc
    _ ≤ _ := hraw
    _ ≤ _ := by gcongr

private theorem next_record_lookup (z : Z) (hq : t.val + 1 < p.T) :
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceRecords
      rate rewards C_star C_h u t z)[t.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z]? =
      some (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq) := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  have heq := ReferenceFirstCollectionRenewalIncomingQueuePrefix.start_eq_physicalStart
    rate rewards C_star C_h u t z
  have hi : t.val + 1 -
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
        rate rewards C_star C_h u t z =
      t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
        rate rewards C_star C_h u t z + 1 := by
    change t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
      rate z.val rewards C_star C_h = _
    rw [← heq]
    change ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z ≤ t.val at hs
    omega
  rw [hi]
  exact ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_lookup
    rate rewards C_star C_h u t z hq

/-- The immediate optional cell is present exactly when the literal endpoint
word extends past the already included call. -/
theorem nextCell_present_iff_endpoint (z : Z) (hq : t.val + 1 < p.T) :
    (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq).isSome = true ↔ t.val + 1 < κ z := by
  have hbaseline := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_baseline_readouts
    rate rewards C_star C_h u t z hq
  have hcal : ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell rate
      (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
        rate rewards C_star C_h u t z hq) =
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq := by
    unfold ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
    rw [hbaseline.1, hbaseline.2]
  constructor
  · intro hp
    have hl := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord_lookup
      rate rewards C_star C_h u t z hq
    obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp hl
    have htail : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
        rate rewards C_star C_h u t z =
        ((ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
          rate rewards C_star C_h u t z hq ::
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
            rate rewards C_star C_h u t z).drop
              (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
                rate rewards C_star C_h u t z + 1 + 1)).takeWhile
          ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen).length := by
      change (((ReferenceFirstCollectionRenewalIncomingQueuePrefix.sourceRecords
        rate rewards C_star C_h u t z).drop
          (t.val - ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
            rate rewards C_star C_h u t z + 1)).takeWhile _).length = _
      rw [List.drop_eq_getElem_cons hi, hv]
    have hfirst (hz : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
        rate rewards C_star C_h u t z = 0) :
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.firstNoncontinuingRecord
          rate rewards C_star C_h u t z =
          some (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
            rate rewards C_star C_h u t z hq) := by
      unfold ReferenceFirstCollectionRenewalFutureSliceEndpoint.firstNoncontinuingRecord
      rw [hz, Nat.add_zero]
      exact hl
    have hread := ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_readouts
      rate rewards C_star C_h u t z hq
    dsimp only at hread
    cases hc : (ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord
      rate rewards C_star C_h u t z hq).output.preparation.coordinator
      <;> simp only [hc] at hread htail
    all_goals try
      simp only [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
        hread.1, hread.2.2.1, Option.none_or, Option.isSome_none, Bool.false_eq_true] at hp
    rename_i outcome
    cases outcome <;> simp only at hread htail
    all_goals try
      simp only [ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
        hread.1, hread.2.2.1, Option.none_or, Option.isSome_none, Bool.false_eq_true] at hp
    · have hz : ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
          rate rewards C_star C_h u t z = 0 := by
        simpa [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] using htail
      have hd : ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta
          rate rewards C_star C_h u t z = 1 := by
        simp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.cutoffEndpointDelta, hfirst hz, hc]
      simp [ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpointIndex,
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingEnd,
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.beginning, hz, hd]
    · have hpos : 0 < ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
          rate rewards C_star C_h u t z := by
        simp [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hc] at htail
        omega
      change t.val + 1 < t.val + 1 +
        ReferenceFirstCollectionRenewalFutureSliceEndpoint.continuingLength
          rate rewards C_star C_h u t z + _
      omega
  · intro hk
    obtain ⟨L, r, c, _, hr, _, hcell, _⟩ :=
      ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_successor
        rate rewards C_star C_h u t z (t.val + 1)
        (by have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
              rate rewards C_star C_h u t z; omega) hk
    have hrEq := Option.some.inj
      (hr.symm.trans (next_record_lookup rate rewards C_star C_h u t z hq))
    rw [hrEq, hcal] at hcell
    rw [hcell]
    rfl

/-- The immediate slot has the original current run as its incoming state
and the same literal endpoint successor as its outgoing state. -/
theorem endpointNextSlot (z : Z) (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : endpointCells? rate rewards C_star C_h u t z = some L)
    (hq : t.val + 1 < p.T) (hk : t.val + 1 < κ z) :
    ∃ k : Fin L.length,
      k.val = t.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z ∧
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = some L[k.val] ∧
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
        rate rewards C_star C_h u t z = RecordedQueueRun.run Q (L.take k.val) ∧
      (z ∈ ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hq ↔
        L[k.val].enabled = true ∧
          (RecordedQueueRun.run Q (L.take k.val)).overflow = false) := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  obtain ⟨base, hbase, hlen, hcurrent, _, _⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_and_takes
      rate rewards C_star C_h u t z
  have hbaseEq : base = L := Option.some.inj (hbase.symm.trans hL)
  subst base
  let k : Fin L.length := ⟨t.val + 1 -
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z, by rw [hlen]; omega⟩
  obtain ⟨base, r, c, hbase, hr, _, hc, _, hslot, _, _⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_successor
      rate rewards C_star C_h u t z (t.val + 1) (by omega) hk
  have hbaseEq : base = L := Option.some.inj (hbase.symm.trans hL)
  subst base
  have hrecord := Option.some.inj
    (hr.symm.trans (next_record_lookup rate rewards C_star C_h u t z hq))
  have hbaseline := ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_baseline_readouts
    rate rewards C_star C_h u t z hq
  have hnext : ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c := by
    rw [hrecord] at hc
    simpa only [ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCell,
      ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell,
      hbaseline.1, hbaseline.2] using hc
  have hcell : L[k.val] = c := by
    change L[k.val]? = some c at hslot
    rw [List.getElem?_eq_getElem k.isLt] at hslot
    exact Option.some.inj hslot
  have hstate : ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
      rate rewards C_star C_h u t z = RecordedQueueRun.run Q (L.take k.val) := by
    unfold ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
    rw [hcurrent]
  have hparams := ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
    rate rewards C_star C_h u t hq z c hnext
  have hover : ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
      rate rewards C_star C_h u t z =
      (RecordedQueueRun.run Q (L.take k.val)).overflow := by
    have hread := ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
      rate rewards C_star C_h u t z
    rw [hstate] at hread
    unfold ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
    rw [← hread]
    rfl
  refine ⟨k, rfl, by rw [hcell]; exact hnext, hstate, ?_⟩
  change z ∈ ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
    rate rewards C_star C_h u t hq ↔ _
  rw [ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff]
  simp only [hparams, Option.some.injEq, Prod.mk.injEq, hover, hcell]
  exact ⟨fun ⟨⟨_, he, _⟩, ho⟩ => ⟨he, ho⟩,
    fun ⟨he, ho⟩ => ⟨⟨c.rate, he, rfl⟩, ho⟩⟩

/-- The strict-future selectors read the same incoming and final-successor
registers as the literal endpoint word, and their retained gate is exactly
the enabled, incoming-prior-clear mask at that word's actual slot. -/
theorem endpointFutureSlot
    (z : Z) (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : endpointCells? rate rewards C_star C_h u t z = some L)
    (q : Fin p.T) (hf : t.val + 1 < q.val) (hq : q.val < κ z) :
    ∃ k : Fin L.length,
      k.val = q.val -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z ∧
      (z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hf ↔
        L[k.val].enabled = true ∧
          (RecordedQueueRun.run Q (L.take k.val)).overflow = false) ∧
      (∀ i, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hf i z = endpointArrival rate L k i) ∧
      (∀ i, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hf i z =
        RecordedQueueSummation.runMarginal Q p.m L k.val i) ∧
      (∀ i, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureBacklogMinus
          rate rewards C_star C_h u t q hf i z =
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (L.take k.val)) i) ∧
      (∀ i, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaPlus
          rate rewards C_star C_h u t q hf i z =
        RecordedQueueSummation.runMarginal Q p.m L (k.val + 1) i) ∧
      (∀ i, ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureBacklogPlus
          rate rewards C_star C_h u t q hf i z =
        StoppedQueueBound.normalizedBacklog Q
          (RecordedQueueRun.run Q (L.take (k.val + 1))) i) := by
  have hs := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
    rate rewards C_star C_h u t z
  obtain ⟨base, hbase, hlen, _, _, hprefix⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_and_takes
      rate rewards C_star C_h u t z
  have hbaseEq : base = L := Option.some.inj (hbase.symm.trans hL)
  subst base
  let k : Fin L.length := ⟨q.val -
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
      rate rewards C_star C_h u t z, by rw [hlen]; omega⟩
  have hsupport : z ∈
      ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
        rate rewards C_star C_h u t q hf :=
    (ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
      rate rewards C_star C_h u t z q hf).2 hq
  obtain ⟨inputs, c, hinputs, hc, hprior, hpost, _, _, hθ, hb, hθ', hb'⟩ :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureReadouts_same_run_step
      rate rewards C_star C_h u t q hf z hsupport
  have hinputsEq : inputs = L.take k.val :=
    Option.some.inj (hinputs.symm.trans (hprefix q.val (by omega) hq.le).1)
  subst inputs
  obtain ⟨L', r, c', hL', hr, _, hcal, _, hslot, hstep, _⟩ :=
    ReferenceFirstCollectionRenewalRawPrefixJoin.renewalCells_endpoint_successor
      rate rewards C_star C_h u t z q.val (by omega) hq
  have hL'eq : L' = L := Option.some.inj (hL'.symm.trans hL)
  subst L'
  have hrecord :=
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord_lookup_fields
      rate rewards C_star C_h u t q z hf).1
  have hrEq : r = ReferenceFirstCollectionRenewalFutureNumericalPrefix.futureRecord
      rate rewards C_star C_h u t q z := Option.some.inj (hr.symm.trans hrecord)
  have hunmasked := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureSliceCell_eq_unmasked
    rate rewards C_star C_h u t q hf z c hc
  have hcc : c' = c := by
    rw [hrEq] at hcal
    exact Option.some.inj (hcal.symm.trans hunmasked)
  subst c'
  have hcell : L[k.val] = c := by
    have hv : some L[k.val] = some c := by
      change L[k.val]? = some c at hslot
      rw [List.getElem?_eq_getElem k.isLt] at hslot
      exact hslot
    exact Option.some.inj hv
  have hstep' : RecordedQueueRun.run Q (L.take (k.val + 1)) =
      RecordedQueueRun.step Q (RecordedQueueRun.run Q (L.take k.val)) c := by
    have hi : q.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z = k.val + 1 := by dsimp [k]; omega
    rw [hi] at hstep
    exact hstep
  have hparams : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hf = some (c.enabled, c.rate) := by
    have hv := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
      rate rewards C_star C_h u t z q hf
    cases hd : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
        rate rewards C_star C_h u t z q hf with
    | none =>
        rw [hd] at hv
        simp only at hv
        have hbad := hc.symm.trans hv.2
        cases hbad
    | some data =>
        rcases data with ⟨parameters, view, code⟩
        rw [hd] at hv
        obtain ⟨cell, snapshot, valid, hcell', hp, _, _, _, _⟩ := hv
        have heq : cell = c := Option.some.inj (hcell'.symm.trans hc)
        subst cell
        simp only [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters,
          hd, Option.bind_some, hp]
  have hclear : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z =
        !(RecordedQueueRun.run Q (L.take k.val)).overflow := by
    rw [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear, hprior]
    cases ho : (RecordedQueueRun.run Q (L.take k.val)).overflow <;>
      simp [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, ho]
  refine ⟨k, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcell]
    cases he : c.enabled <;>
      cases ho : (RecordedQueueRun.run Q (L.take k.val)).overflow <;>
      simp [ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture,
        hparams, hclear, he, ho]
  · intro i
    have ha := (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_acceptance
      rate rewards C_star C_h u t q hf i z (L.take k.val) c hinputs hc).1
    simpa only [endpointArrival, hcell,
      ReferenceFirstLaunchNumericalCell.queueParameters] using ha
  · intro i
    rw [hθ i]
    rfl
  · intro i
    rw [hb i]
    rfl
  · intro i
    rw [hθ' i, ← hstep']
    rfl
  · intro i
    rw [hb' i, ← hstep']
    rfl

private def wordStatistic
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (L : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ k : Fin L.length, f (RecordedQueueRun.run Q (L.take k.val)) L[k.val]

private def slotStatistic
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (L : List (RecordedQueueRun.RoundInput p.K)) (k : ℕ) : ℝ :=
  (L[k]?).elim 0 (fun c => f (RecordedQueueRun.run Q (L.take k)) c)

private theorem wordStatistic_take_dates
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (L : List (RecordedQueueRun.RoundInput p.K)) (s n : ℕ)
    (hs : s ≤ n) (hn : n - s ≤ L.length) :
    wordStatistic rate f (L.take (n - s)) =
      ∑ q ∈ Finset.Ico s n, slotStatistic rate f L (q - s) := by
  have hlen : (L.take (n - s)).length = n - s := by
    simp only [List.length_take, Nat.min_eq_left hn]
  unfold wordStatistic
  apply Finset.sum_bij (fun k _ => s + k.val)
  · intro k _
    have hk : k.val < n - s := by simpa only [hlen] using k.isLt
    exact Finset.mem_Ico.mpr (by omega)
  · intro k _ l _ heq
    apply Fin.ext
    omega
  · intro q hq
    have hq' := Finset.mem_Ico.mp hq
    exact ⟨⟨q - s, by rw [hlen]; omega⟩, Finset.mem_univ _, by dsimp only; omega⟩
  · intro k _
    have hk : k.val < n - s := by simpa only [hlen] using k.isLt
    simp only [slotStatistic, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem (hk.trans_le hn), Option.elim_some,
      List.getElem_take]
    rw [List.take_take, Nat.min_eq_left hk.le]

private theorem statistic_partition
    (f : RecordedQueueRun.RunState p.K → RecordedQueueRun.RoundInput p.K → ℝ)
    (z : Z) (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : endpointCells? rate rewards C_star C_h u t z = some L)
    (next : ℝ) (future : ℕ → ℝ)
    (hnext : next = if t.val + 1 < κ z then
      slotStatistic rate f L (t.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z) else 0)
    (hfuture : ∀ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
      future n = if n < κ z then slotStatistic rate f L (n -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z) else 0) :
    wordStatistic rate f L =
      wordStatistic rate f (L.take (t.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z)) + next +
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        future n := by
  let s := ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
    rate rewards C_star C_h u t z
  let g (n : ℕ) := slotStatistic rate f L (n - s)
  obtain ⟨base, hbase, hlen⟩ := endpointCells_present rate rewards C_star C_h u t z
  have hbaseEq : base = L := Option.some.inj (hbase.symm.trans hL)
  subst base
  have hs : s ≤ t.val :=
    ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart_le_call
      rate rewards C_star C_h u t z
  have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
    rate rewards C_star C_h u t z
  have hb : t.val + 1 ≤ κ z := hbounds.1.trans hbounds.2.1
  have hwhole : wordStatistic rate f L = ∑ n ∈ Finset.Ico s (κ z), g n := by
    have h := wordStatistic_take_dates rate f L s (κ z) (by omega) (by rw [hlen])
    have hlen' : L.length = κ z - s := hlen
    rw [← hlen', List.take_length] at h
    exact h
  have hpre := wordStatistic_take_dates rate f L s (t.val + 1)
    (by omega) (by rw [hlen]; omega)
  rw [hwhole, hpre, hnext]
  rw [Finset.sum_congr rfl hfuture]
  change (∑ n ∈ Finset.Ico s (κ z), g n) =
    (∑ n ∈ Finset.Ico s (t.val + 1), g n) +
      (if t.val + 1 < κ z then g (t.val + 1) else 0) +
      ∑ n ∈ Finset.Ico (t.val + 2) p.T, if n < κ z then g n else 0
  rw [← Finset.sum_Ico_consecutive g (by omega : s ≤ t.val + 1) hb, add_assoc]
  congr 1
  have htail : (∑ n ∈ Finset.Ico (t.val + 2) p.T, if n < κ z then g n else 0) =
      ∑ n ∈ Finset.Ico (t.val + 2) (κ z), g n := by
    rw [← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [htail]
  by_cases hk : t.val + 1 < κ z
  · rw [ite_eq_left hk, Finset.sum_eq_sum_Ico_succ_bot hk g]
  · have heq : κ z = t.val + 1 := by omega
    simp [heq]

private abbrev ScalarObservation (K : ℕ) :=
  (Fin K → ℝ) → (Fin K → ℝ) → (Fin K → ℝ) →
    (Fin K → ℝ) → (Fin K → ℝ) → ℝ

private def activeStepObservation (H : ScalarObservation p.K)
    (state : RecordedQueueRun.RunState p.K) (c : RecordedQueueRun.RoundInput p.K) : ℝ :=
  if c.enabled = true ∧ state.overflow = false then
    H (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate i state.registers)
      (StoppedQueueBound.normalizedBacklog Q state)
      (RecordedRoundMoments.rawEstimate Q state c)
      (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate i (RecordedQueueRun.step Q state c).registers)
      (StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.step Q state c))
  else 0

private def nextObservation (H : ScalarObservation p.K) (z : Z) : ℝ :=
  if hq : t.val + 1 < p.T then
    (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
      rate rewards C_star C_h u t hq).indicator (fun z => H
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta rate rewards C_star C_h u t z)
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preBacklog rate rewards C_star C_h u t z)
        (fun i => ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar rate rewards C_star C_h u t hq i z)
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.postTheta rate rewards C_star C_h u t hq z)
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.postBacklog rate rewards C_star C_h u t hq z)) z
  else 0

private def futureObservation (H : ScalarObservation p.K) (n : ℕ) (z : Z) : ℝ :=
  if hn : n < p.T then if hf : t.val + 1 < n then
    (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
      rate rewards C_star C_h u t ⟨n, hn⟩ hf).indicator (fun z => H
        (fun i => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus rate rewards C_star C_h u t ⟨n, hn⟩ hf i z)
        (fun i => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureBacklogMinus rate rewards C_star C_h u t ⟨n, hn⟩ hf i z)
        (fun i => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar rate rewards C_star C_h u t ⟨n, hn⟩ hf i z)
        (fun i => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaPlus rate rewards C_star C_h u t ⟨n, hn⟩ hf i z)
        (fun i => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureBacklogPlus rate rewards C_star C_h u t ⟨n, hn⟩ hf i z)) z
    else 0 else 0

private theorem next_theta_registers (A : Fin p.K → ℕ × ℕ) :
    ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.thetaFromRegisters A =
      fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate i A := by
  rfl

private theorem next_backlog_registers (state : RecordedQueueRun.RunState p.K) :
    ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.backlogFromRegisters rate state.registers =
      StoppedQueueBound.normalizedBacklog Q state := by
  rfl

private theorem marginal_registers (L : List (RecordedQueueRun.RoundInput p.K)) (n : ℕ) :
    RecordedQueueSummation.runMarginal Q p.m L n =
      fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate i
        (RecordedQueueRun.run Q (L.take n)).registers := by
  rfl

private theorem activeObservation_decomposition (H : ScalarObservation p.K) (z : Z)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hL : endpointCells? rate rewards C_star C_h u t z = some L) :
    wordStatistic rate (activeStepObservation rate H) L =
      wordStatistic rate (activeStepObservation rate H) (L.take (t.val + 1 -
        ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
          rate rewards C_star C_h u t z)) + nextObservation rate rewards C_star C_h u t H z +
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        futureObservation rate rewards C_star C_h u t H n z := by
  apply statistic_partition rate rewards C_star C_h u t _ z L hL
  · have hbounds := ReferenceFirstCollectionRenewalFutureSliceEndpoint.endpoint_bounds
      rate rewards C_star C_h u t z
    by_cases hq : t.val + 1 < p.T
    · by_cases hk : t.val + 1 < κ z
      · obtain ⟨k, hkv, hc, hstate, hgate⟩ := endpointNextSlot rate rewards C_star C_h u t z L hL hq hk
        have ha (i : Fin p.K) :=
          (ReferenceFirstCollectionRenewalNextLearningMoments.actual_nextScalar_present_run
            rate rewards C_star C_h u t hq i z L[k.val] hc).1
        simp only [nextObservation, dite_eq_left hq, Set.indicator_apply, hgate,
          ite_eq_left hk, ← hkv, slotStatistic, List.getElem?_eq_getElem k.isLt, Option.elim_some,
          activeStepObservation]
        simp_rw [ha]
        have hpre : ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta
            rate rewards C_star C_h u t z =
            fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
              rate i (RecordedQueueRun.run Q (L.take k.val)).registers := by
          change ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.thetaFromRegisters
            (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).registers = _
          rw [next_theta_registers rate, hstate]
        have hback : ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preBacklog
            rate rewards C_star C_h u t z =
            StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (L.take k.val)) := by
          change ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.backlogFromRegisters rate
            (ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).registers = _
          rw [next_backlog_registers rate, hstate]
        have hpost : ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.postTheta
            rate rewards C_star C_h u t hq z =
            fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate i
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q (L.take k.val)) L[k.val]).registers := by
          change ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.thetaFromRegisters
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.nextRegisters rate rewards C_star C_h u t hq z) = _
          rw [next_theta_registers rate]
          simp only [ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.nextRegisters, hc, hstate]
        have hpostback : ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.postBacklog
            rate rewards C_star C_h u t hq z =
            StoppedQueueBound.normalizedBacklog Q
              (RecordedQueueRun.step Q (RecordedQueueRun.run Q (L.take k.val)) L[k.val]) := by
          change ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.backlogFromRegisters rate
            (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.nextRegisters rate rewards C_star C_h u t hq z) = _
          simp only [ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.nextRegisters, hc, hstate,
            next_backlog_registers rate]
        rw [hpre, hback, hpost, hpostback, hstate]
      · have hnot : z ∉ ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
            rate rewards C_star C_h u t hq := by
          intro hz
          obtain ⟨c, _, hc, _, _, _, _⟩ :=
            ReferenceFirstCollectionRenewalNextLearningMoments.retained_nextCell_data
              rate rewards C_star C_h u t hq z hz
          have hp := (nextCell_present_iff_endpoint rate rewards C_star C_h u t z hq).1
            (by rw [hc]; rfl)
          exact hk hp
        simp only [nextObservation, dite_eq_left hq, Set.indicator_of_notMem hnot, ite_eq_right hk]
    · have hk : ¬ t.val + 1 < κ z := by omega
      simp only [nextObservation, dite_eq_right hq, ite_eq_right hk]
  · intro n hn
    have hdate := Finset.mem_Ico.mp hn
    have hnt : n < p.T := hdate.2
    have hnf : t.val + 1 < n := by omega
    let q : Fin p.T := ⟨n, hnt⟩
    by_cases hk : n < κ z
    · obtain ⟨k, hkv, hgate, ha, hθ, hb, hθ', hb'⟩ :=
        endpointFutureSlot rate rewards C_star C_h u t z L hL q hnf hk
      have hstep := RecordedPotentialStep.run_take_succ_eq_step Q L k.val k.isLt
      dsimp only [q] at hkv hgate ha hθ hb hθ' hb'
      simp only [futureObservation, dite_eq_left hnt, dite_eq_left hnf, Set.indicator_apply,
        hgate, ite_eq_left hk, ← hkv, slotStatistic, List.getElem?_eq_getElem k.isLt,
        Option.elim_some, activeStepObservation]
      simp_rw [ha, hθ, hb, hθ', hb', hstep]
      simp only [marginal_registers rate, hstep]
      rfl
    · have hnot : z ∉ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hnf := by
        intro hz
        have hs := ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
          rate rewards C_star C_h u t q hnf hz
        exact hk ((ReferenceFirstCollectionRenewalFutureSliceEndpoint.supportTest_iff_before_endpoint
          rate rewards C_star C_h u t z q hnf).1 hs)
      dsimp only [q] at hnot
      simp only [futureObservation, dite_eq_left hnt, dite_eq_left hnf,
        Set.indicator_of_notMem hnot, ite_eq_right hk]

private def wordObservation (H : ScalarObservation p.K)
    (L : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ k : Fin L.length, H (RecordedQueueSummation.runMarginal Q p.m L k.val)
    (StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (L.take k.val)))
    (endpointArrival rate L k)
    (RecordedQueueSummation.runMarginal Q p.m L (k.val + 1))
    (StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (L.take (k.val + 1))))

private theorem backlog_registers (state : RecordedQueueRun.RunState p.K) :
    StoppedQueueBound.normalizedBacklog Q state =
      fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate i state.registers := by
  rfl

private theorem wordStatistic_eq_wordObservation (H : ScalarObservation p.K)
    (hzero : ∀ θ b, H θ b 0 θ b = 0)
    (L : List (RecordedQueueRun.RoundInput p.K)) :
    wordStatistic rate (activeStepObservation rate H) L = wordObservation rate H L := by
  apply Finset.sum_congr rfl
  intro k _
  have hstep := RecordedPotentialStep.run_take_succ_eq_step Q L k.val k.isLt
  change activeStepObservation rate H _ _ = _
  dsimp only [activeStepObservation]
  by_cases ha : L[k.val].enabled = true ∧
      (RecordedQueueRun.run Q (L.take k.val)).overflow = false
  · rw [ite_eq_left ha]
    simp only [marginal_registers rate, hstep]
    rfl
  · rw [ite_eq_right ha]
    let state := RecordedQueueRun.run Q (L.take k.val)
    have hrecord (i : Fin p.K) : RecordedQueueRun.acceptedRecord Q state L[k.val] i = (false, 0) := by
      cases he : L[k.val].enabled <;> cases ho : state.overflow <;>
        simp_all [RecordedQueueRun.acceptedRecord, state]
    have hregs : (RecordedQueueRun.step Q state L[k.val]).registers = state.registers := by
      funext i
      simp only [RecordedQueueRun.step, hrecord, QueueReplay.transition, Bool.false_eq_true, ite_false]
    have hraw : endpointArrival rate L k = 0 := by
      funext i
      change (RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord Q state L[k.val] i) : ℝ) / (rate.n : ℝ) = 0
      rw [hrecord]
      simp only [RecordedQueueRun.acceptedArrival, Bool.false_eq_true, ite_false, Nat.cast_zero, zero_div]
    rw [hraw, hstep]
    change 0 = H _ _ 0 _ _
    dsimp only [state] at hregs
    simp only [marginal_registers rate, backlog_registers rate, hstep, hregs]
    exact (hzero _ _).symm

/-- The raw endpoint comparator is exactly the original invocation plus its
one next-date observation and its supported strict-future observations. -/
theorem endpointRawGap_decomposition (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    endpointRawGap rate rewards C_star C_h u t S z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S z.val +
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
        rate rewards C_star C_h u t S z +
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
        rate rewards C_star C_h u t S z := by
  obtain ⟨L, hL, hfirst, _, _⟩ := endpointCells_current_take_and_prefixes rate rewards C_star C_h u t z
  let H : ScalarObservation p.K := fun θ _ a _ _ => (∑ i ∈ S.1, a i) - ∑ i, θ i * a i
  have hzero : ∀ θ b, H θ b 0 θ b = 0 := by intro θ b; simp [H]
  have h := activeObservation_decomposition rate rewards C_star C_h u t H z L hL
  simp_rw [wordStatistic_eq_wordObservation rate H hzero] at h
  simpa only [H, wordObservation, endpointRawGap, hL, Option.elim_some,
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap, hfirst,
    nextObservation, futureObservation, endpointArrival,
    ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation,
    ReferenceFirstCollectionRenewalNextLearningMoments.comparatorObservation,
    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal,
    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt,
    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGap,
    dite_apply, Pi.zero_apply, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate] using h

/-- Weighted arrivals have the same exact three-way original-source split. -/
theorem endpointWeightedArrival_decomposition (z : Z) :
    endpointWeightedArrival rate rewards C_star C_h u t z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h z.val +
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
        rate rewards C_star C_h u t z +
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
        rate rewards C_star C_h u t z := by
  obtain ⟨L, hL, hfirst, _, _⟩ := endpointCells_current_take_and_prefixes rate rewards C_star C_h u t z
  let H : ScalarObservation p.K := fun θ _ a _ _ => ∑ i, θ i * a i
  have hzero : ∀ θ b, H θ b 0 θ b = 0 := by intro θ b; simp [H]
  have h := activeObservation_decomposition rate rewards C_star C_h u t H z L hL
  simp_rw [wordStatistic_eq_wordObservation rate H hzero] at h
  simpa only [H, wordObservation, endpointWeightedArrival, hL, Option.elim_some,
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival, hfirst,
    nextObservation, futureObservation, endpointArrival,
    ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation,
    ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation,
    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal,
    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservation,
    dite_apply, Pi.zero_apply, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate] using h

/-- Exact signed correction split. The successor marginal and backlog in
every term include the last actual endpoint update. -/
theorem endpointCorrection_decomposition (z : Z) :
    endpointCorrection rate rewards C_star C_h u t z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection
        rate rewards C_star C_h z.val +
      nextDateSignedIncrement rate rewards C_star C_h u t z +
      strictFutureSignedIncrementTotal rate rewards C_star C_h u t z := by
  obtain ⟨L, hL, hfirst, _, _⟩ := endpointCells_current_take_and_prefixes rate rewards C_star C_h u t z
  let H : ScalarObservation p.K := fun θ _ _ θ' b' => ∑ i, (θ' i - θ i) * b' i
  have hzero : ∀ θ b, H θ b 0 θ b = 0 := by intro θ b; simp [H]
  have h := activeObservation_decomposition rate rewards C_star C_h u t H z L hL
  simp_rw [wordStatistic_eq_wordObservation rate H hzero] at h
  simpa only [H, wordObservation, endpointCorrection, hL, Option.elim_some,
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection, hfirst,
    nextObservation, futureObservation, nextDateSignedIncrement,
    strictFutureSignedIncrementTotal, strictFutureSignedIncrementAt] using h

/-- The active backlog is exactly the already-paid original cost and the
accepted after-call calendar cost, with enabled zero arrivals still charged. -/
theorem endpointActiveBacklog_decomposition (z : Z) :
    endpointActiveBacklog rate rewards C_star C_h u t z =
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
        rate rewards C_star C_h z.val +
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t z := by
  obtain ⟨L, hL, hfirst, _, _⟩ := endpointCells_current_take_and_prefixes rate rewards C_star C_h u t z
  let H : ScalarObservation p.K := fun θ b _ _ _ => ∑ i, θ i * b i
  have h := activeObservation_decomposition rate rewards C_star C_h u t H z L hL
  have hf (n : ℕ) : futureObservation rate rewards C_star C_h u t H n z =
      ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt
        rate rewards C_star C_h u t n z := by
    by_cases hn : n < p.T
    · by_cases ht : t.val + 1 < n
      · simp only [futureObservation,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
          dite_eq_left hn, dite_eq_left ht,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog,
          H]
        apply congrArg (fun f : Z → ℝ =>
          (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t ⟨n, hn⟩ ht).indicator f z)
        funext w
        simp only [Finset.sum_apply, Pi.mul_apply]
      · simp only [futureObservation,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
          dite_eq_left hn, dite_eq_right ht, Set.indicator_empty]
    · simp only [futureObservation,
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt,
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
        dite_eq_right hn, Set.indicator_empty]
  have hn : nextObservation rate rewards C_star C_h u t H z =
      (if hq : t.val + 1 < p.T then
        (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hq).indicator
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z
      else 0) := by
    unfold nextObservation
    split <;> rfl
  have hw (M : List (RecordedQueueRun.RoundInput p.K)) :
      wordStatistic rate (activeStepObservation rate H) M =
      ∑ k ∈ Finset.univ.filter (fun k : Fin M.length => M[k.val].enabled = true ∧
        (RecordedQueueRun.run Q (M.take k.val)).overflow = false),
        ∑ i : Fin p.K, RecordedQueueSummation.runMarginal Q p.m M k.val i *
          StoppedQueueBound.normalizedBacklog Q (RecordedQueueRun.run Q (M.take k.val)) i := by
    simp only [wordStatistic, activeStepObservation, H, Finset.sum_filter, marginal_registers rate]
  simp_rw [hf, hw] at h
  rw [hn] at h
  rw [← ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost_decomposition]
  simpa only [endpointActiveBacklog, hL, Option.elim_some,
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationActiveBacklog, hfirst,
    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog,
    ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog,
    add_assoc] using h

/-- The signed all-successor estimate with the exact original-source cost. -/
theorem endpointCorrection_le_cost_and_arrival (z : Z) :
    endpointCorrection rate rewards C_star C_h u t z ≤
      8 * rate.eta.val *
        (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z.val +
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
            rate rewards C_star C_h u t z +
          endpointWeightedArrival rate rewards C_star C_h u t z) := by
  obtain ⟨L, hL, _⟩ := endpointCells_present rate rewards C_star C_h u t z
  rw [← endpointActiveBacklog_decomposition]
  exact endpointCorrection_le_activeBacklog rate rewards C_star C_h u t z L hL

/-- One complete-word normalizer and one actual terminal backlog bound,
with the exact original and after-call cost decomposition. -/
theorem endpointRawGap_le_cost_and_arrival
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    endpointRawGap rate rewards C_star C_h u t S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q *
          ((κ z - ReferenceFirstCollectionRenewalFutureNumericalPrefix.sourceStart
            rate rewards C_star C_h u t z : ℕ) : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) + 8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z.val +
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
              rate rewards C_star C_h u t z +
            endpointWeightedArrival rate rewards C_star C_h u t z) := by
  obtain ⟨L, hL, hlen⟩ := endpointCells_present rate rewards C_star C_h u t z
  have h := endpointRawGap_le_length rate rewards C_star C_h u t S z L hL
  rwa [hlen, endpointActiveBacklog_decomposition] at h

/-- Horizon specialization of the same single-normalizer source-cost bound. -/
theorem endpointRawGap_le_horizon_cost_and_arrival
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    endpointRawGap rate rewards C_star C_h u t S z ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) + 8 * rate.eta.val *
          (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
              rate rewards C_star C_h z.val +
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
              rate rewards C_star C_h u t z +
            endpointWeightedArrival rate rewards C_star C_h u t z) := by
  obtain ⟨L, hL, _⟩ := endpointCells_present rate rewards C_star C_h u t z
  have h := endpointRawGap_le_horizon rate rewards C_star C_h u t S z L hL
  rwa [endpointActiveBacklog_decomposition] at h

end Bandits.Support.ReferenceFirstCollectionRenewalRawPotential

end
