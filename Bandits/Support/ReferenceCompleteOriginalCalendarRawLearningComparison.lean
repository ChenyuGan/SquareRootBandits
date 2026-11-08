/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalCalendarWeightMarginalRestoration
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalPrefixLearning

import Mathlib.Tactic

/-!
# Raw learning comparison on the complete original calendar

The source comparison is made on the unique numerical word recovered from the
actual original suffix. Every term uses the same stopped `RecordedQueueRun`:
raw arrivals are its accepted quantized arrivals, current marginals are its
full product-set marginals before each update, and the terminal signed term
uses the marginal after the preceding update. The physical installation,
cutoff, previous-weight, and corrected-mass identities are consumed from the
complete-calendar restoration theorem on this same word.

This is a deterministic numerical comparison. It makes no assignment-law,
conditional-expectation, or selected-play claim.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionCorrectedSliceNumericalPrefix

namespace Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

variable {p : Parameters}

public abbrev calendarQueue
    (rate : ReferenceActivePhysicalStep.RateInput p) : RecordedQueueRun.Parameters :=
  ReferenceFirstLaunchNumericalCell.queueParameters (p := p) rate

private noncomputable def rawAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (t : Fin rounds.length) (i : Fin p.K) : ℝ :=
  (RecordedQueueRun.acceptedArrival
    (RecordedQueueRun.acceptedRecord (calendarQueue rate)
      (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i) : ℝ) /
    ((calendarQueue rate).n : ℝ)

private noncomputable def servedAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (t : Fin rounds.length) (i : Fin p.K) : ℝ :=
  RecordedPotentialStep.servedEstimate (calendarQueue rate)
    (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i

private noncomputable def marginalAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (n : ℕ) (i : Fin p.K) : ℝ :=
  RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds n i

private noncomputable def backlogAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (n : ℕ) (i : Fin p.K) : ℝ :=
  StoppedQueueBound.normalizedBacklog (calendarQueue rate) (RecordedQueueRun.run (calendarQueue rate) (rounds.take n)) i

private noncomputable def rawGapOnWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (S : ProductSetLaw.ProductSet p.K p.m)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ t : Fin rounds.length,
    ((∑ i ∈ S.1, rawAt rate rounds t i) -
      ∑ i : Fin p.K, marginalAt rate rounds t.val i * rawAt rate rounds t i)

private noncomputable def servedGapOnWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (S : ProductSetLaw.ProductSet p.K p.m)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ t : Fin rounds.length,
    ((∑ i ∈ S.1, servedAt rate rounds t i) -
      ∑ i : Fin p.K, marginalAt rate rounds t.val i * servedAt rate rounds t i)

/-- The exact signed terminal comparator-minus-current-marginal backlog term.
The current marginal is the one after the last retained update, as in the
finite queue identity. -/
private noncomputable def terminalCorrectionOnWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (S : ProductSetLaw.ProductSet p.K p.m)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  (∑ i ∈ S.1, backlogAt rate rounds rounds.length i) -
    ∑ i : Fin p.K,
      marginalAt rate rounds (rounds.length - 1) i *
        backlogAt rate rounds rounds.length i

/-- Chronological marginal change times the following backlog, with the
source terminal convention that stops at the marginal before the final
update. -/
private noncomputable def marginalCorrectionOnWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ t : Fin (rounds.length - 1), ∑ i : Fin p.K,
    (marginalAt rate rounds (t.val + 1) i - marginalAt rate rounds t.val i) *
      backlogAt rate rounds (t.val + 1) i

private def activeAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) (t : Fin rounds.length) : Prop :=
  rounds[t].enabled = true ∧
    (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow = false

private noncomputable def backlogCostOnWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ t : Fin rounds.length,
    if rounds[t].enabled = true ∧
        (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow = false then
      ∑ i : Fin p.K, marginalAt rate rounds t.val i * backlogAt rate rounds t.val i
    else 0

private noncomputable def weightedRawArrivalOnWord
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) : ℝ :=
  ∑ t : Fin rounds.length, ∑ i : Fin p.K,
    marginalAt rate rounds t.val i * rawAt rate rounds t i

/-- The literal served comparator on the same optional original word. -/
noncomputable def originalCalendarServedGap
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h p.T z with
  | none => 0
  | some rounds =>
      ∑ t : Fin rounds.length,
        ((∑ i ∈ S.1,
            RecordedPotentialStep.servedEstimate (calendarQueue rate)
              (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i) -
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds t.val i *
              RecordedPotentialStep.servedEstimate (calendarQueue rate)
                (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i)

/-- The signed terminal comparator/current-marginal backlog term on the same
optional original word. -/
noncomputable def originalCalendarTerminalCorrection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h p.T z with
  | none => 0
  | some rounds =>
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog (calendarQueue rate)
          (RecordedQueueRun.run (calendarQueue rate) rounds) i) -
        ∑ i : Fin p.K,
          RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds
            (rounds.length - 1) i *
            StoppedQueueBound.normalizedBacklog (calendarQueue rate)
              (RecordedQueueRun.run (calendarQueue rate) rounds) i

/-- The chronological successor-marginal/backlog correction on the same
optional original word. -/
noncomputable def originalCalendarMarginalCorrection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h p.T z with
  | none => 0
  | some rounds =>
      ∑ t : Fin (rounds.length - 1), ∑ i : Fin p.K,
        (RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds
            (t.val + 1) i -
          RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds t.val i) *
          StoppedQueueBound.normalizedBacklog (calendarQueue rate)
            (RecordedQueueRun.run (calendarQueue rate) (rounds.take (t.val + 1))) i

/-- The literal optional raw comparator on the original calendar word. No
launch means the source observation stays absent and its finite sum is zero. -/
noncomputable def originalCalendarRawGap
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h p.T z with
  | none => 0
  | some rounds =>
      ∑ t : Fin rounds.length,
        ((∑ i ∈ S.1,
            (RecordedQueueRun.acceptedArrival
              (RecordedQueueRun.acceptedRecord (calendarQueue rate)
                (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i) : ℝ) /
              ((calendarQueue rate).n : ℝ)) -
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds t.val i *
              ((RecordedQueueRun.acceptedArrival
                (RecordedQueueRun.acceptedRecord (calendarQueue rate)
                  (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i) : ℝ) /
                ((calendarQueue rate).n : ℝ)))

/-- The literal active, retained full-marginal backlog COST on the same
original word. -/
noncomputable def originalCalendarBacklogCost
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h p.T z with
  | none => 0
  | some rounds =>
      ∑ t : Fin rounds.length,
        if rounds[t].enabled = true ∧
            (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow = false then
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds t.val i *
              StoppedQueueBound.normalizedBacklog (calendarQueue rate)
                (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) i
        else 0

/-- The literal full-marginal weighted accepted raw-arrival W on the same
original word. The accepted record itself handles disabled and stopped dates. -/
noncomputable def originalCalendarWeightedRawArrival
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match prefixInputs rate rewards C_star C_h p.T z with
  | none => 0
  | some rounds =>
      ∑ t : Fin rounds.length, ∑ i : Fin p.K,
        RecordedQueueSummation.runMarginal (calendarQueue rate) p.m rounds t.val i *
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord (calendarQueue rate)
              (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[t] i) : ℝ) /
            ((calendarQueue rate).n : ℝ))

private theorem source_eta_le_sixty_four
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    rate.eta.val ≤ 1 / 64 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.le_trans (by decide) p.two_le_m)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    have htwo : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
    exact_mod_cast (Nat.le_trans (by decide) htwo)
  have hLnat : 1 ≤ CanonicalRecordingRates.L_stab p :=
    CanonicalRecordingRates.L_stab_ge_one p
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast hLnat
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hden64 : 64 ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      (64 : ℝ) ≤ 1024 := by norm_num
      _ = 1024 * 1 * 1 * 1 := by ring
      _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by gcongr
  have hscaled : rate.eta.val *
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
    (le_div_iff₀ hden).mp rate.sourceCap
  have hmul : rate.eta.val * 64 ≤ 1 := by
    calc
      rate.eta.val * 64 ≤ rate.eta.val *
          (1024 * (p.m : ℝ) * (p.K : ℝ) *
            (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hden64 rate.eta.property.le
      _ ≤ 1 := hscaled
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).2 (by nlinarith)

private theorem four_m_eta_le_one
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    4 * (p.m : ℝ) * rate.eta.val ≤ 1 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.le_trans (by decide) p.two_le_m)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    have htwo : 2 ≤ p.K := p.two_le_m.trans (Nat.le_of_lt p.m_lt_K)
    exact_mod_cast (Nat.le_trans (by decide) htwo)
  have hLnat : 1 ≤ CanonicalRecordingRates.L_stab p :=
    CanonicalRecordingRates.L_stab_ge_one p
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast hLnat
  have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hdenLower : 4 * (p.m : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      4 * (p.m : ℝ) ≤ 1024 * (p.m : ℝ) := by
        gcongr
        norm_num
      _ = 1024 * (p.m : ℝ) * 1 * 1 := by ring
      _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by gcongr
  have hscaled : rate.eta.val *
      (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
    (le_div_iff₀ hden).mp rate.sourceCap
  calc
    4 * (p.m : ℝ) * rate.eta.val = rate.eta.val * (4 * (p.m : ℝ)) := by ring
    _ ≤ rate.eta.val *
        (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) :=
      mul_le_mul_of_nonneg_left hdenLower rate.eta.property.le
    _ ≤ 1 := hscaled

private theorem original_word_rate_floor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K))
    (hword : prefixInputs rate rewards C_star C_h p.T z = some L) :
    ∀ round ∈ L, ∀ i,
      32 * rate.eta.val ≤ round.rate i := by
  classical
  let R : List (ReferenceCompletePhysicalHistory.RoundRecord p rate) :=
    ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hnone := ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
      rw [hnone.2.2 p.T] at hword
      cases hword
  | some active =>
    have hdata := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
      rate rewards C_star C_h z
    simp only [hlaunch] at hdata
    rcases hdata with ⟨L0, hlen0, hmap, hprefix, _hphase⟩
    have hT : s + R.length = p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
      have hRlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
      dsimp [s, R]
      omega
    have hterminal : prefixInputs rate rewards C_star C_h p.T z = some L0 := by
      have hp := hprefix R.length le_rfl
      rw [hT, ← hlen0, List.take_length] at hp
      exact hp
    have hsame : L0 = L := Option.some.inj (hterminal.symm.trans hword)
    subst L
    intro round hround i
    have hsome : some round ∈ L0.map some :=
      List.mem_map.mpr ⟨round, hround, rfl⟩
    rw [← hmap] at hsome
    obtain ⟨record, _hrecord, hcell⟩ := List.mem_map.mp hsome
    change (ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record).or
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record) = some round at hcell
    have hbetaFloor : 32 * rate.eta.val ≤ CanonicalRecordingRates.beta p rate.eta.val := by
      have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
        exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
      rw [CanonicalRecordingRates.beta]
      calc
        32 * rate.eta.val = 32 * rate.eta.val * 1 := by ring
        _ ≤ 32 * rate.eta.val * (CanonicalRecordingRates.L_stab p : ℝ) :=
          mul_le_mul_of_nonneg_left hL
            (mul_nonneg (by norm_num) rate.eta.property.le)
        _ = 32 * rate.eta.val * (CanonicalRecordingRates.L_stab p : ℝ) := rfl
    cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
    | none =>
        simp only [hlive, Option.none_or] at hcell
        obtain ⟨payload, ledger, started, weights, out, hcall, _hdiag, _hrun,
          _henabled, _hclock, hrate, _hreward, _hdiagrecord, _hgate, _harrival⟩ :=
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
            0 record round hcell
        have hβ := payload.beta_le_rate i
        rw [congrFun hrate i]
        exact hbetaFloor.trans hβ
    | some c =>
        have hEq : c = round := by
          exact Option.some.inj (by simpa only [hlive, Option.some_or] using hcell)
        subst round
        obtain ⟨_henabled, selected, _hselection, _hreward, hrate, _hraw⟩ :=
          ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical 0 record c hlive
        have hβ := selected.view.payload.beta_le_rate i
        rw [congrFun hrate i]
        exact hbetaFloor.trans hβ

private theorem fin_prefix_sum_le {n : ℕ} (f : Fin n → ℝ)
    (hf : ∀ t, 0 ≤ f t) :
    (∑ t : Fin (n - 1), f ⟨t.val, by omega⟩) ≤ ∑ t : Fin n, f t := by
  cases n with
  | zero => simp
  | succ k =>
      simp only [Nat.succ_sub_one]
      rw [Fin.sum_univ_castSucc]
      exact le_add_of_nonneg_right (hf ⟨k, Nat.lt_succ_self k⟩)

private theorem marginalCorrection_le_cost_and_arrival
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) :
    marginalCorrectionOnWord rate rounds ≤
      8 * rate.eta.val *
        (backlogCostOnWord rate rounds + weightedRawArrivalOnWord rate rounds) := by
  classical
  let n := rounds.length
  let θ := marginalAt rate rounds
  let b := backlogAt rate rounds
  let A := rawAt rate rounds
  let idx (t : Fin (n - 1)) : Fin n := ⟨t.val, by dsimp [n] at t; omega⟩
  let activePrefix : Finset (Fin (n - 1)) :=
    Finset.univ.filter (fun t => activeAt rate rounds (idx t))
  have hactive_mem (t : Fin (n - 1)) :
      t ∈ activePrefix ↔ activeAt rate rounds (idx t) := by
    simp [activePrefix]
  have hθ (k : ℕ) (i : Fin p.K) : 0 ≤ θ k i := by
    simpa [θ, marginalAt] using
      (RecordedQueueSummation.runMarginal_pos (calendarQueue rate) p.m rounds k i
        p.two_le_m p.m_lt_K).le
  have hb (k : ℕ) (i : Fin p.K) : 0 ≤ b k i := by
    dsimp [b, backlogAt]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hA (t : Fin rounds.length) (i : Fin p.K) : 0 ≤ A t i := by
    dsimp [A, rawAt]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcoef : 0 ≤ 8 * rate.eta.val :=
    mul_nonneg (by norm_num) rate.eta.property.le
  have hstep (t : Fin (n - 1)) :
      (∑ i : Fin p.K,
        (θ (t.val + 1) i - θ t.val i) * b (t.val + 1) i) ≤
        if t ∈ activePrefix then
          8 * rate.eta.val *
            ((∑ i : Fin p.K, θ t.val i * b t.val i) +
              ∑ i : Fin p.K, θ t.val i * A (idx t) i)
        else 0 := by
    by_cases ht : t ∈ activePrefix
    · rw [ite_eq_left ht]
      have hgrowth (i : Fin p.K) :
          θ (t.val + 1) i - θ t.val i ≤ 8 * rate.eta.val * θ t.val i := by
        obtain ⟨h1, h2⟩ := RecordedMarginalGrowth.run_prefix_theta_growth
          (m := p.m) (calendarQueue rate) rounds t.val (by dsimp [n] at t; omega) i
          p.two_le_m p.m_lt_K (source_eta_le_sixty_four rate)
        have heta : (calendarQueue rate).eta = rate.eta.val := rfl
        rw [heta] at h1 h2
        change θ (t.val + 1) i ≤ Real.exp (4 * rate.eta.val) * θ t.val i at h1
        change Real.exp (4 * rate.eta.val) * θ t.val i ≤
          (1 + 8 * rate.eta.val) * θ t.val i at h2
        linarith only [h1, h2]
      have hbacklog (i : Fin p.K) :
          b (t.val + 1) i ≤ b t.val i + A (idx t) i := by
        have hrec := RecordedQueueSummation.rawArrival_sub_servedEstimate_eq_backlog_difference
          (calendarQueue rate) rounds (idx t) i
        have hserved := RecordedPotentialStep.servedEstimate_nonneg (calendarQueue rate)
          (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[idx t] i
        change A (idx t) i - servedAt rate rounds (idx t) i =
          b (t.val + 1) i - b t.val i at hrec
        have hserved' : 0 ≤ servedAt rate rounds (idx t) i := by
          change 0 ≤ RecordedPotentialStep.servedEstimate (calendarQueue rate)
            (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)) rounds[idx t] i
          exact hserved
        nlinarith only [hrec, hserved']
      calc
        _ ≤ ∑ i : Fin p.K,
            (8 * rate.eta.val * θ t.val i) * b (t.val + 1) i := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right (hgrowth i) (hb _ i)
        _ ≤ ∑ i : Fin p.K,
            (8 * rate.eta.val * θ t.val i) * (b t.val i + A (idx t) i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hbacklog i)
            (mul_nonneg hcoef (hθ _ i))
        _ = 8 * rate.eta.val *
            ((∑ i : Fin p.K, θ t.val i * b t.val i) +
              ∑ i : Fin p.K, θ t.val i * A (idx t) i) := by
          simp only [mul_add, mul_assoc, Finset.sum_add_distrib,
            Finset.mul_sum]
    · rw [ite_eq_right ht]
      have hstop : rounds[idx t].enabled = false ∨
          (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow = true := by
        by_contra h
        have he : rounds[idx t].enabled = true := by
          cases hh : rounds[idx t].enabled <;> simp_all
        have ho : (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow = false := by
          cases hh : (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow <;> simp_all
        have hactive : activeAt rate rounds (idx t) := ⟨he, ho⟩
        have hmem : t ∈ activePrefix := hactive_mem t |>.mpr hactive
        exact ht hmem
      have heq (i : Fin p.K) : θ (t.val + 1) i = θ t.val i :=
        RecordedMarginalGrowth.run_prefix_theta_eq_of_disabled_or_overflowed
          (m := p.m) (calendarQueue rate) rounds t.val (by dsimp [n] at t; omega) i hstop
      simp only [heq, sub_self, zero_mul, Finset.sum_const_zero, le_refl]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hstep t)
  have hsum' :
      marginalCorrectionOnWord rate rounds ≤
        8 * rate.eta.val *
          ((∑ t : Fin (n - 1), if t ∈ activePrefix then
              ∑ i : Fin p.K, θ t.val i * b t.val i else 0) +
            ∑ t : Fin (n - 1), if t ∈ activePrefix then
              ∑ i : Fin p.K, θ t.val i * A (idx t) i else 0) := by
    simpa only [marginalCorrectionOnWord, n, activePrefix, θ, b, A,
      Finset.sum_ite_mem, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.univ_inter] using hsum
  have hprefixCost_le :
      (∑ t : Fin (n - 1), if t ∈ activePrefix then
          ∑ i : Fin p.K, θ t.val i * b t.val i else 0) ≤
        backlogCostOnWord rate rounds := by
    let f : Fin n → ℝ := fun t =>
      if rounds[t].enabled = true ∧
          (RecordedQueueRun.run (calendarQueue rate) (rounds.take t.val)).overflow = false then
        ∑ i : Fin p.K, θ t.val i * b t.val i else 0
    have hf : ∀ t, 0 ≤ f t := by
      intro t
      dsimp [f]
      split_ifs
      · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hθ _ _) (hb _ _))
      · exact le_rfl
    have hprefix :
        (∑ t : Fin (n - 1), if t ∈ activePrefix then
            ∑ i : Fin p.K, θ t.val i * b t.val i else 0) =
          ∑ t : Fin (n - 1), f (idx t) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [f, hactive_mem t, activeAt, idx]
    rw [hprefix]
    calc
      (∑ t : Fin (n - 1), f (idx t)) ≤ ∑ t : Fin n, f t := by
        simpa [idx] using fin_prefix_sum_le (n := n) f hf
      _ = backlogCostOnWord rate rounds := by
        simp [f, backlogCostOnWord, n, θ, b]
  have hprefixArrival_le :
      (∑ t : Fin (n - 1), if t ∈ activePrefix then
          ∑ i : Fin p.K, θ t.val i * A (idx t) i else 0) ≤
        weightedRawArrivalOnWord rate rounds := by
    let f : Fin n → ℝ := fun t => ∑ i : Fin p.K, θ t.val i * A t i
    have hf : ∀ t, 0 ≤ f t := by
      intro t
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hθ _ _) (hA t _))
    have hprefix :
        (∑ t : Fin (n - 1), if t ∈ activePrefix then
            ∑ i : Fin p.K, θ t.val i * A (idx t) i else 0) ≤
          ∑ t : Fin (n - 1), f (idx t) := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hactive : t ∈ activePrefix
      · simp [hactive, f, idx]
      · simp only [hactive, ite_false]
        have hnot : ¬ activeAt rate rounds (idx t) := by
          intro h
          exact hactive ((hactive_mem t).mpr h)
        simpa [f, idx, hnot] using
          (Finset.sum_nonneg (fun i _ => mul_nonneg (hθ _ _) (hA _ _)))
    calc
      (∑ t : Fin (n - 1), if t ∈ activePrefix then
          ∑ i : Fin p.K, θ t.val i * A (idx t) i else 0) ≤
          ∑ t : Fin (n - 1), f (idx t) := hprefix
      _ ≤ ∑ t : Fin n, f t := by
        simpa [idx] using fin_prefix_sum_le (n := n) f hf
      _ = weightedRawArrivalOnWord rate rounds := by
        simp [f, weightedRawArrivalOnWord, n, θ, A]
  have hsumBounds := add_le_add hprefixCost_le hprefixArrival_le
  exact hsum'.trans (mul_le_mul_of_nonneg_left hsumBounds hcoef)

private theorem raw_gap_eq_source_decomposition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (S : ProductSetLaw.ProductSet p.K p.m)
    (rounds : List (RecordedQueueRun.RoundInput p.K)) :
    rawGapOnWord rate S rounds =
      servedGapOnWord rate S rounds + terminalCorrectionOnWord rate S rounds +
        marginalCorrectionOnWord rate rounds := by
  classical
  by_cases hT : 0 < rounds.length
  · have h := RecordedQueueSummation.run_raw_served_summation_by_parts
      (calendarQueue rate) rounds p.two_le_m p.m_lt_K S hT
    convert h using 1
    all_goals
      simp [rawGapOnWord, servedGapOnWord, terminalCorrectionOnWord,
        marginalCorrectionOnWord, rawAt, servedAt, marginalAt, backlogAt,
        RecordedQueueSummation.runMarginal, Finset.sum_sub_distrib]
    all_goals ring
  · have hzero : rounds.length = 0 := Nat.eq_zero_of_not_pos hT
    have hback (i : Fin p.K) : backlogAt rate rounds rounds.length i = 0 := by
      rw [hzero]
      exact RecordedQueueSummation.run_initial_backlog_eq_zero (calendarQueue rate) rounds i
    have hterminal : terminalCorrectionOnWord rate S rounds = 0 := by
      simp [terminalCorrectionOnWord, hback]
    simp [rawGapOnWord, servedGapOnWord, marginalCorrectionOnWord,
      hzero, hterminal]

private theorem raw_gap_on_word_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (S : ProductSetLaw.ProductSet p.K p.m)
    (rounds : List (RecordedQueueRun.RoundInput p.K))
    (hrate : ∀ round ∈ rounds, ∀ i, 32 * rate.eta.val ≤ round.rate i) :
    rawGapOnWord rate S rounds ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda (calendarQueue rate) +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda (calendarQueue rate) *
          (rounds.length : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        8 * rate.eta.val *
          (backlogCostOnWord rate rounds + weightedRawArrivalOnWord rate rounds) := by
  have hpotential := RecordedPotentialTelescope.servedEstimate_cumulative_comparison
    (calendarQueue rate) rounds p.two_le_m p.m_lt_K (four_m_eta_le_one rate) S
  have hdecomp := raw_gap_eq_source_decomposition rate S rounds
  have hterminal : terminalCorrectionOnWord rate S rounds ≤
      (p.m : ℝ) / (16 * rate.eta.val) := by
    by_cases hT : 0 < rounds.length
    · exact RecordedQueueSummation.run_terminal_backlog_correction_le
        (calendarQueue rate) rounds p.two_le_m p.m_lt_K S hrate hT
    · have hzero : rounds.length = 0 := Nat.eq_zero_of_not_pos hT
      have hback (i : Fin p.K) : backlogAt rate rounds rounds.length i = 0 := by
        rw [hzero]
        exact RecordedQueueSummation.run_initial_backlog_eq_zero (calendarQueue rate) rounds i
      simp [terminalCorrectionOnWord, hback]
      have heta : 0 < rate.eta.val := rate.eta.property
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (by positivity))
  have hcorrection := marginalCorrection_le_cost_and_arrival rate rounds
  have hserved : servedGapOnWord rate S rounds ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda (calendarQueue rate) +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda (calendarQueue rate) *
          (rounds.length : ℝ) := by
    simpa [servedGapOnWord, servedAt, marginalAt,
      RecordedQueueSummation.runMarginal] using hpotential
  linarith

/-- The exact chronological raw/served identity, before any inequality is
applied. In particular the terminal correction is signed, and its marginal
is the current full marginal after the preceding update. -/
theorem originalCalendarRawGap_signed_decomposition
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    match prefixInputs rate rewards C_star C_h p.T z with
    | none => originalCalendarRawGap rate rewards C_star C_h S z = 0
    | some _rounds =>
        originalCalendarRawGap rate rewards C_star C_h S z =
          originalCalendarServedGap rate rewards C_star C_h S z +
            originalCalendarTerminalCorrection rate rewards C_star C_h S z +
            originalCalendarMarginalCorrection rate rewards C_star C_h z := by
  cases hword : prefixInputs rate rewards C_star C_h p.T z with
  | none => simp [originalCalendarRawGap, hword]
  | some rounds =>
      simpa [originalCalendarRawGap, originalCalendarServedGap,
        originalCalendarTerminalCorrection, originalCalendarMarginalCorrection,
        rawGapOnWord, servedGapOnWord, terminalCorrectionOnWord,
        marginalCorrectionOnWord, rawAt, servedAt, marginalAt, backlogAt,
        RecordedQueueSummation.runMarginal, List.take_length, hword] using
        raw_gap_eq_source_decomposition rate S rounds

/-- The score-side output attached to the same original word as the RAW
comparison. Queue marginals follow the stopped analytical prefixes. At every
physical later installation, the un-stopped source current, cutoff, and
previous vectors and the corrected raw-mass identity retain that same word. -/
noncomputable def originalCalendarSourceWordAndLaterRestoration
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (L : List (RecordedQueueRun.RoundInput p.K)) : Prop :=
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let base := AssignmentScoreReconstruction.sourceWeightBase p
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  (∀ h, h ≤ L.length →
      (fun i : Fin p.K => RecordedQueueSummation.runMarginal Q p.m L h i) =
        ProductSetLaw.theta p.m (fun i => base ^
          (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i
            (min h (UnstoppedRecordedQueueComparison.firstOverflowPrefix Q L))).1)) ∧
    (∀ b : Fin R.length, match (R[b.val]'b.isLt).output.preparation.coordinator with
      | .collection payload ledger clock cutoff
          (.laterChosen core _consistent _started _hstart instruction _hassignment output _hlocal
            clockData installed _selected) =>
          let operation := CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceActivePhysicalStep.collectionInput R[b.val].input payload ledger clock cutoff)
            core.payload_n_eq
          let W := fun h (i : Fin p.K) => base ^
            (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i h).1
          ∃ (a : Fin R.length) (e : ℕ)
            (seg : ReferenceCollectionSegmentExtraction.Segment rate),
              a.val < e ∧ e < b.val ∧ ReferenceAssignmentPayloadPersistence.InstallationBirth R[a.val] payload ∧
              ReferenceCollectionSegmentExtraction.segmentAt R e = some seg ∧
              b.val = e + seg.records.length ∧ seg.final = ledger ∧ ledger.pending = ∅ ∧
              instruction.time = R[b.val].input.time ∧ ledger.cutoff = s + e + 1 ∧
              (∀ i : Fin p.K, output.reconstruction.registers.cutoff i =
                CoordinatorCollectionLedger.CutoffRegister.mk
                  (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i e).1
                  (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i e).2
                  ((ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i e).1 -
                    (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i (e - 1)).1) ∧
                ledger.increment i = (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i b.val).1 -
                  (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i e).1 ∧
                AssignmentScoreReconstruction.sourceScore output.reconstruction i =
                  (ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L i b.val).1) ∧
              AssignmentScoreReconstruction.currentWeight output.reconstruction = W b.val ∧
              AssignmentScoreReconstruction.cutoffWeight output.reconstruction = W e ∧
              ProductSetLaw.theta p.m (AssignmentScoreReconstruction.currentWeight output.reconstruction) =
                ProductSetLaw.theta p.m (W b.val) ∧
              ProductSetLaw.theta p.m (AssignmentScoreReconstruction.cutoffWeight output.reconstruction) =
                ProductSetLaw.theta p.m (W e) ∧
              LaterAssignmentStartOperation.correctionScale
                (ReferenceActivePhysicalStep.collectionInput R[b.val].input payload ledger clock cutoff).payload
                operation instruction output.cutoffReached =
                  (1 - 4 * (p.m : ℝ) * rate.eta.val) ^ (b.val - e + 1) /
                    (4 * (p.m : ℝ) * rate.eta.val) ∧
              ((instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.corrected ∧
                instruction.time.val + 1 < operation.freezeAt ∧
                AssignmentScoreReconstruction.previousWeight output.reconstruction = some (W (e - 1)) ∧
                output.payload.anchor = payload.anchor ∧ installed.registers.payload.anchor = payload.anchor ∧
                (∀ S, output.law.mass S = LaterAssignmentStartOperation.correctedRawMass
                  (ReferenceActivePhysicalStep.collectionInput R[b.val].input payload ledger clock cutoff).payload
                  operation instruction output.reconstruction (W (e - 1)) output.cutoffReached S) ∧
                ∀ S, LaterAssignmentStartOperation.correctedRawMass
                  (ReferenceActivePhysicalStep.collectionInput R[b.val].input payload ledger clock cutoff).payload
                  operation instruction output.reconstruction (W (e - 1)) output.cutoffReached S =
                  LaterAssignmentStartOperation.productQOnPrefixCarrier (W b.val) S +
                    LaterAssignmentStartOperation.correctionScale
                      (ReferenceActivePhysicalStep.collectionInput R[b.val].input payload ledger clock cutoff).payload
                      operation instruction output.cutoffReached *
                    (LaterAssignmentStartOperation.productQOnPrefixCarrier (W e) S -
                      LaterAssignmentStartOperation.productQOnPrefixCarrier (W (e - 1)) S)) ∨
              (instruction.kind = CoordinatorPhaseClock.AssignmentStartKind.renewal ∧
                operation.freezeAt ≤ instruction.time.val + 1 ∧
                AssignmentScoreReconstruction.previousWeight output.reconstruction = none ∧
                output.payload.anchor = W b.val ∧ installed.registers.payload.anchor = W b.val ∧
                ∀ S, output.law.mass S = LaterAssignmentStartOperation.productQOnPrefixCarrier (W b.val) S))
      | _ => True)

/-- The complete original-calendar RAW comparison. The weight/marginal
restoration conjunct is the admitted full-word result: it identifies every
later actual current, cutoff, and previous vector, and each corrected raw mass
with this same unique word. The numerical inequality is deterministic and uses
the literal retained COST and accepted-arrival W defined above. -/
theorem complete_original_calendar_raw_learning_comparison
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (match ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
     | none =>
         originalCalendarRawGap rate rewards C_star C_h S z = 0 ∧
         originalCalendarBacklogCost rate rewards C_star C_h z = 0 ∧
         originalCalendarWeightedRawArrival rate rewards C_star C_h z = 0
     | some _ =>
         ∃ L : List (RecordedQueueRun.RoundInput p.K),
         prefixInputs rate rewards C_star C_h p.T z = some L ∧
         (∀ L', prefixInputs rate rewards C_star C_h p.T z = some L' → L' = L) ∧
         originalCalendarSourceWordAndLaterRestoration rate rewards C_star C_h z L ∧
         originalCalendarRawGap rate rewards C_star C_h S z ≤
           Real.log (Nat.choose p.K p.m : ℝ) /
               RecordedPotentialStep.potentialLambda (calendarQueue rate) +
             16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda (calendarQueue rate) *
               ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate z rewards C_star C_h).length : ℝ) +
             (p.m : ℝ) / (16 * rate.eta.val) +
             8 * rate.eta.val *
               (originalCalendarBacklogCost rate rewards C_star C_h z +
                originalCalendarWeightedRawArrival rate rewards C_star C_h z)) := by
  classical
  have hrestoration :=
    ReferenceCompleteOriginalCalendarWeightMarginalRestoration.complete_original_installation_weight_marginal_restoration
      rate rewards C_star C_h z
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hnone := ReferenceCompleteOriginalCalendarCellPresence.no_launch_complete_original_calendar_cell_presence
        rate rewards C_star C_h z hlaunch
      rcases hnone with ⟨_hrecords, _hstart, hprefix⟩
      simp [originalCalendarRawGap, originalCalendarBacklogCost,
        originalCalendarWeightedRawArrival, hprefix]
  | some active =>
      simp only [hlaunch] at hrestoration
      rcases hrestoration with ⟨L, hlen, _hprefixes, hterminal, hunique,
        _hinstallations, hlaterInstallations, hprefixRun⟩
      have hsource : originalCalendarSourceWordAndLaterRestoration
          rate rewards C_star C_h z L := by
        dsimp [originalCalendarSourceWordAndLaterRestoration]
        refine ⟨?_, hlaterInstallations⟩
        intro h hh
        exact (hprefixRun h hh).2.2.1
      have hrate := original_word_rate_floor rate rewards C_star C_h z L hterminal
      have hbound := raw_gap_on_word_le rate S L hrate
      have hcost : originalCalendarBacklogCost rate rewards C_star C_h z =
          backlogCostOnWord rate L := by
        unfold originalCalendarBacklogCost
        simp only [hterminal]
        unfold backlogCostOnWord marginalAt backlogAt
        rfl
      have harrival : originalCalendarWeightedRawArrival rate rewards C_star C_h z =
          weightedRawArrivalOnWord rate L := by
        unfold originalCalendarWeightedRawArrival
        simp only [hterminal]
        unfold weightedRawArrivalOnWord rawAt marginalAt
        rfl
      have hgap : originalCalendarRawGap rate rewards C_star C_h S z =
          rawGapOnWord rate S L := by
        simp [originalCalendarRawGap, hterminal, rawGapOnWord,
          rawAt, marginalAt]
      have hlenEq :
          (ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h).length = L.length := hlen.symm
      refine ⟨L, hterminal, hunique, hsource, ?_⟩
      rw [hgap, hcost, harrival, hlenEq]
      exact hbound

end Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

end
