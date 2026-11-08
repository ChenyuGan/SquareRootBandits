/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstLiveOriginalCalendarWeightedBacklogBound
public import Bandits.Support.CanonicalRawPotentialBound

import Mathlib.Tactic

/-!
# Pathwise raw potential and signed backlog correction on the actual first-live list

The list, queue, arrivals, marginals, and backlog coordinates below are the
literal actual-source readouts. The results are deterministic bounds on each
source input; they make no expectation or policy-law claim.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveRawPotentialBound

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ)

/-- The queue parameters selected by the actual first launch. -/
abbrev firstWindowQueue :=
  ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate

/-- The complete actual numerical cell list, including its physical suffix
after the analytical queue has frozen. -/
def firstWindowCells (omega : SourceInput p) :=
  ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
    rate rewards C_star C_h omega

/-- The actual calendar origin of the first-live list. -/
def firstWindowStart (omega : SourceInput p) : ℕ :=
  ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
    rate rewards C_star C_h omega

/-- The actual finite queue prefix at length `k`. -/
def firstWindowRun (omega : SourceInput p) (k : ℕ) :=
  RecordedQueueRun.run (firstWindowQueue rate)
    ((firstWindowCells rate rewards C_star C_h omega).take k)

/-- The literal `A_k(i)` accepted arrival divided by the selected integer
recording denominator. -/
def firstWindowAcceptedArrival (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length)
    (i : Fin p.K) : ℝ :=
  (RecordedQueueRun.acceptedArrival (RecordedQueueRun.acceptedRecord
      (firstWindowQueue rate) (firstWindowRun rate rewards C_star C_h omega k.val)
      (firstWindowCells rate rewards C_star C_h omega)[k.val] i) : ℝ) /
    (rate.n : ℝ)

/-- The actual inclusion marginal at a finite first-live prefix. -/
def firstWindowMarginal (omega : SourceInput p) (k : ℕ) (i : Fin p.K) : ℝ :=
  RecordedQueueSummation.runMarginal (firstWindowQueue rate) p.m
    (firstWindowCells rate rewards C_star C_h omega) k i

/-- The normalized backlog at a finite first-live prefix. -/
def firstWindowNormalizedBacklog (omega : SourceInput p) (k : ℕ)
    (i : Fin p.K) : ℝ :=
  StoppedQueueBound.normalizedBacklog (firstWindowQueue rate)
    (firstWindowRun rate rewards C_star C_h omega k) i

/-- The sum of current inclusion marginals times the actual normalized
backlogs at prefix `k`. -/
def firstWindowWeightedBacklog (omega : SourceInput p) (k : ℕ) : ℝ :=
  ∑ i : Fin p.K,
    firstWindowMarginal rate rewards C_star C_h omega k i *
      firstWindowNormalizedBacklog rate rewards C_star C_h omega k i

/-- The literal served estimate `H_k(i)` of the same recorded queue step. -/
def firstWindowServedEstimate (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length)
    (i : Fin p.K) : ℝ :=
  RecordedPotentialStep.servedEstimate (firstWindowQueue rate)
    (firstWindowRun rate rewards C_star C_h omega k.val)
    (firstWindowCells rate rewards C_star C_h omega)[k.val] i

/-- The actual raw comparator-minus-current-marginal sum on the first-live list. -/
def firstWindowRawGap (omega : SourceInput p)
    (S : ProductSetLaw.ProductSet p.K p.m) : ℝ :=
  ∑ k : Fin (firstWindowCells rate rewards C_star C_h omega).length,
    ((∑ i ∈ S.1, firstWindowAcceptedArrival rate rewards C_star C_h omega k i) -
      ∑ i : Fin p.K, firstWindowMarginal rate rewards C_star C_h omega k.val i *
        firstWindowAcceptedArrival rate rewards C_star C_h omega k i)

/-- The corresponding served-estimate comparator-minus-marginal sum. -/
def firstWindowServedGap (omega : SourceInput p)
    (S : ProductSetLaw.ProductSet p.K p.m) : ℝ :=
  ∑ k : Fin (firstWindowCells rate rewards C_star C_h omega).length,
    ((∑ i ∈ S.1, firstWindowServedEstimate rate rewards C_star C_h omega k i) -
      ∑ i : Fin p.K, firstWindowMarginal rate rewards C_star C_h omega k.val i *
        firstWindowServedEstimate rate rewards C_star C_h omega k i)

/-- The signed successor-marginal backlog correction with all `N` successors. -/
def firstWindowMarginalBacklogCorrection (omega : SourceInput p) : ℝ :=
  ∑ k : Fin (firstWindowCells rate rewards C_star C_h omega).length,
    ∑ i : Fin p.K,
      (firstWindowMarginal rate rewards C_star C_h omega (k.val + 1) i -
        firstWindowMarginal rate rewards C_star C_h omega k.val i) *
        firstWindowNormalizedBacklog rate rewards C_star C_h omega (k.val + 1) i

private theorem firstWindow_length_le_remaining (omega : SourceInput p) :
    (firstWindowCells rate rewards C_star C_h omega).length ≤
      p.T - firstWindowStart rate rewards C_star C_h omega := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate omega rewards C_star C_h
  cases hcross : boundary.crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h omega (by simpa [boundary] using hcross)
      have hcells : firstWindowCells rate rewards C_star C_h omega = [] := by
        simpa [firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using hno.2.1
      rw [hcells]
      simp
  | some crossing =>
      have hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true := by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using
          (show boundary.crossing.isSome = true by simp [hcross])
      let start := ReferenceInitializationRun.elapsed p boundary.completed
      have hstart : firstWindowStart rate rewards C_star C_h omega = start := by
        rfl
      have hstartLe : start ≤ p.T := by
        rw [← hstart]
        exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
      let s : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le hstartLe⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
        ⟨omega, ⟨hc, rfl⟩⟩
      have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
        rate rewards C_star C_h s x
      have hlen :
          (firstWindowCells rate rewards C_star C_h omega).length =
            (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
              start (p.T - start)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) x).length := by
        simpa [firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using
          congrArg List.length hwhole.2
      calc
        (firstWindowCells rate rewards C_star C_h omega).length =
            (ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
              start (p.T - start)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) x).length := hlen
        _ = ReferenceFirstLiveOverflowReadout.firstLiveLength rate rewards C_star C_h
              start (p.T - start)
              (ReferenceFirstLiveOverflowReadout.maximal_span s) x :=
          ReferenceFirstLiveOverflowReadout.firstLiveCells_length rate rewards C_star C_h
            start (p.T - start)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) x
        _ ≤ p.T - start :=
          ReferenceFirstLiveOverflowReadout.firstLiveLength_le_count rate rewards C_star C_h
            start (p.T - start)
            (ReferenceFirstLiveOverflowReadout.maximal_span s) x
        _ = p.T - firstWindowStart rate rewards C_star C_h omega := by rw [hstart]

private theorem firstWindow_cell_enabled_rate (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length) :
    (firstWindowCells rate rewards C_star C_h omega)[k.val].enabled = true ∧
      ∀ i : Fin p.K,
        32 * rate.eta.val ≤ (firstWindowCells rate rewards C_star C_h omega)[k.val].rate i := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate omega rewards C_star C_h
  cases hcross : boundary.crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h omega (by simpa [boundary] using hcross)
      have hcells : firstWindowCells rate rewards C_star C_h omega = [] := by
        simpa [firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using hno.2.1
      rw [hcells] at k
      exact Fin.elim0 k
  | some crossing =>
      have hc : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput omega rewards C_star C_h rate)).crossing.isSome = true := by
        simpa [boundary, ReferenceCompletePhysicalHistory.generatedBoundary,
          ReferenceCompletePhysicalHistory.generatedInput] using
          (show boundary.crossing.isSome = true by simp [hcross])
      let start := ReferenceInitializationRun.elapsed p boundary.completed
      have hstart : firstWindowStart rate rewards C_star C_h omega = start := by
        rfl
      have hstartLe : start ≤ p.T := by
        rw [← hstart]
        exact ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
      let s : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le hstartLe⟩
      let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
        ⟨omega, ⟨hc, rfl⟩⟩
      let count := p.T - start
      let hspanFiber := ReferenceFirstLiveOverflowReadout.maximal_span s
      have hwhole := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
        rate rewards C_star C_h s x
      have hspan := ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h
        start count hspanFiber x
      have hcells :
          firstWindowCells rate rewards C_star C_h omega =
            ReferenceFirstLiveOverflowReadout.firstLiveCells rate rewards C_star C_h
              start count hspanFiber x := by
        simpa [firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
          count, hspanFiber] using hwhole.2
      have hcellsActual : firstWindowCells rate rewards C_star C_h omega =
          ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate omega rewards C_star C_h hc count hspan := by
        simpa [firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
          ReferenceFirstLiveOverflowReadout.firstLiveCells, count, hspanFiber] using hwhole.2
      have hkActual : k.val <
          (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow rate omega rewards C_star C_h
            hc count hspan).length := by
        rw [← ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
          rate omega rewards C_star C_h hc count hspan, ← hcellsActual]
        exact k.isLt
      let kActual : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate omega rewards C_star C_h hc count hspan).length := ⟨k.val, hkActual⟩
      let cell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
        rate omega rewards C_star C_h hc count hspan kActual
      have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
        rate omega rewards C_star C_h hc count hspan kActual
      dsimp only at hfacts
      rcases hfacts with ⟨_, _, _, _, henabled, _, hrate, _, _⟩
      have hsourceGet := ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
        rate omega rewards C_star C_h hc count hspan kActual
      have hgetActual :
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate omega rewards
            C_star C_h hc count hspan)[k.val]'(by
              rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
                rate omega rewards C_star C_h hc count hspan]
              exact kActual.isLt) = cell.input := by
        simpa [cell, kActual] using hsourceGet
      have hgetOption := congrArg
        (fun cells : List (RecordedQueueRun.RoundInput p.K) => cells[k.val]?) hcellsActual
      have hactualIndex : k.val <
          (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate omega rewards
            C_star C_h hc count hspan).length := by
        rw [← hcellsActual]
        exact k.isLt
      rw [List.getElem?_eq_getElem k.isLt,
        List.getElem?_eq_getElem hactualIndex] at hgetOption
      have hget :
          (firstWindowCells rate rewards C_star C_h omega)[k.val] =
            (ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate omega rewards
              C_star C_h hc count hspan)[k.val] := Option.some.inj hgetOption
      refine ⟨?_, ?_⟩
      · rw [hget, hgetActual]
        exact henabled
      · intro i
        rw [hget, hgetActual, hrate]
        rw [cell.selected.view.payload.rate_eq_canonical]
        exact CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property
          cell.selected.view.payload.anchor i

private theorem firstWindow_rates (omega : SourceInput p) :
    ∀ round ∈ firstWindowCells rate rewards C_star C_h omega,
      ∀ i : Fin p.K, 32 * (firstWindowQueue rate).eta ≤ round.rate i := by
  intro round hround i
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hround
  let kFin : Fin (firstWindowCells rate rewards C_star C_h omega).length := ⟨k, hk⟩
  have hfacts := firstWindow_cell_enabled_rate rate rewards C_star C_h omega kFin
  rw [← hget]
  change 32 * rate.eta.val ≤
    (firstWindowCells rate rewards C_star C_h omega)[kFin.val].rate i
  exact hfacts.2 i

private theorem four_m_eta_le_one :
    4 * (p.m : ℝ) * (firstWindowQueue rate).eta ≤ 1 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast (CanonicalRecordingRates.L_stab_ge_one p)
  have hKL : (1 : ℝ) ≤ (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) :=
    one_le_mul_of_one_le_of_one_le hK hL
  have hdenLower : (4 : ℝ) ≤
      1024 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      (4 : ℝ) = 4 * 1 := by ring
      _ ≤ 4 * ((p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hKL (by norm_num)
      _ ≤ 1024 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by nlinarith
  have hfactor :
      4 * (p.m : ℝ) ≤
        1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      4 * (p.m : ℝ) = (p.m : ℝ) * 4 := by ring
      _ ≤ (p.m : ℝ) *
          (1024 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hdenLower (by positivity)
      _ = 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by ring
  have hden : (0 : ℝ) <
      1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    positivity
  have hcap : (firstWindowQueue rate).eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) := by
    have hsource : rate.eta.val ≤
        (CanonicalRecordingRates.L_stab p : ℝ)⁻¹ *
          ((p.K : ℝ)⁻¹ * ((p.m : ℝ)⁻¹ * (1024 : ℝ)⁻¹)) := by
      simpa [firstWindowQueue,
        ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
        ReferenceFirstLaunchNumericalCell.queueParameters] using rate.sourceCap
    calc
      (firstWindowQueue rate).eta ≤
          (CanonicalRecordingRates.L_stab p : ℝ)⁻¹ *
            ((p.K : ℝ)⁻¹ * ((p.m : ℝ)⁻¹ * (1024 : ℝ)⁻¹)) := hsource
      _ = 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by
        field_simp
  have hcapProd := (le_div_iff₀ hden).mp hcap
  have heta : 0 ≤ (firstWindowQueue rate).eta := by
    exact le_of_lt (firstWindowQueue rate).eta_pos
  calc
    4 * (p.m : ℝ) * (firstWindowQueue rate).eta =
        (firstWindowQueue rate).eta * (4 * (p.m : ℝ)) := by ring
    _ ≤ (firstWindowQueue rate).eta *
        (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor heta
    _ = (firstWindowQueue rate).eta *
        (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by ring
    _ ≤ 1 := by nlinarith only [hcapProd]

private theorem firstWindow_eta_le_one_div_sixtyfour :
    (firstWindowQueue rate).eta ≤ 1 / 64 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.m_pos p))
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (ConstructorDimensions.K_pos p))
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast (CanonicalRecordingRates.L_stab_ge_one p)
  have hproduct : (1 : ℝ) ≤
      (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hm hK) hL
  have hden : (64 : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by
    calc
      (64 : ℝ) = 64 * 1 := by ring
      _ ≤ 64 * ((p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) :=
        mul_le_mul_of_nonneg_left hproduct (by norm_num)
      _ ≤ 1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ) := by nlinarith
  have hdenPos : (0 : ℝ) <
      1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
  have hcap : (firstWindowQueue rate).eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)) := by
    have hsource : rate.eta.val ≤
        (CanonicalRecordingRates.L_stab p : ℝ)⁻¹ *
          ((p.K : ℝ)⁻¹ * ((p.m : ℝ)⁻¹ * (1024 : ℝ)⁻¹)) := by
      simpa [firstWindowQueue,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
      ReferenceFirstLaunchNumericalCell.queueParameters] using rate.sourceCap
    calc
      (firstWindowQueue rate).eta ≤
          (CanonicalRecordingRates.L_stab p : ℝ)⁻¹ *
            ((p.K : ℝ)⁻¹ * ((p.m : ℝ)⁻¹ * (1024 : ℝ)⁻¹)) := hsource
      _ = 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by
        field_simp
  have hcapProd := (le_div_iff₀ hdenPos).mp hcap
  have hetaPos := (firstWindowQueue rate).eta_pos
  have hscale := mul_le_mul_of_nonneg_left hden hetaPos.le
  have hsixtyFour : (firstWindowQueue rate).eta * 64 ≤ 1 := hscale.trans hcapProd
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).2 hsixtyFour

private theorem firstWindow_prefix_backlog_le_arrivals (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length)
    (i : Fin p.K) :
    firstWindowNormalizedBacklog rate rewards C_star C_h omega (k.val + 1) i ≤
      firstWindowNormalizedBacklog rate rewards C_star C_h omega k.val i +
        firstWindowAcceptedArrival rate rewards C_star C_h omega k i := by
  let q := firstWindowQueue rate
  let rounds := firstWindowCells rate rewards C_star C_h omega
  let state := RecordedQueueRun.run q (rounds.take k.val)
  let round := rounds[k.val]
  have hNatStep :
      ((RecordedQueueRun.step q state round).registers i).2 ≤
        (state.registers i).2 +
          RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord q state round i) := by
    change (QueueReplay.transition (4 * q.n) (state.registers i)
        (RecordedQueueRun.acceptedRecord q state round i)).2 ≤ _
    cases hrecord : RecordedQueueRun.acceptedRecord q state round i with
    | mk enabled amount =>
        cases enabled <;>
        simp [QueueReplay.transition, RecordedQueueRun.acceptedArrival]
  have hstep := RecordedPotentialStep.run_take_succ_eq_step q rounds k.val k.isLt
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
  have hDiv := div_le_div_of_nonneg_right hReal (Nat.cast_nonneg q.n)
  change (((RecordedQueueRun.run q (rounds.take (k.val + 1))).registers i).2 : ℝ) /
      (q.n : ℝ) ≤
    (((state.registers i).2 : ℝ) / (q.n : ℝ)) +
      ((RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord q state round i) : ℝ) / (q.n : ℝ))
  rw [← add_div]
  exact hDiv

private theorem firstWindow_source_crossing (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length) :
    (ReferenceCompletePhysicalHistory.generatedBoundary
      rate omega rewards C_star C_h).crossing.isSome = true := by
  classical
  let boundary := ReferenceCompletePhysicalHistory.generatedBoundary
    rate omega rewards C_star C_h
  cases hcross : boundary.crossing with
  | none =>
      have hno := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h omega (by simpa [boundary] using hcross)
      have hcells : firstWindowCells rate rewards C_star C_h omega = [] := by
        simpa [firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using hno.2.1
      rw [hcells] at k
      exact Fin.elim0 k
  | some crossing => simp

/-- Pathwise raw comparator bound on the actual first-live numerical list. -/
theorem firstWindowRawGap_le (omega : SourceInput p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    firstWindowRawGap rate rewards C_star C_h omega S ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda (firstWindowQueue rate) +
        16 * (p.m : ℝ) ^ 2 *
          RecordedPotentialStep.potentialLambda (firstWindowQueue rate) * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        firstWindowMarginalBacklogCorrection rate rewards C_star C_h omega := by
  classical
  let q := firstWindowQueue rate
  let rounds := firstWindowCells rate rewards C_star C_h omega
  have hlength : rounds.length ≤ p.T := by
    have hrem := firstWindow_length_le_remaining rate rewards C_star C_h omega
    have hstart : firstWindowStart rate rewards C_star C_h omega ≤ p.T :=
      ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h
    exact hrem.trans (Nat.sub_le _ _)
  have hrate : ∀ round ∈ rounds, ∀ i : Fin p.K, 32 * q.eta ≤ round.rate i := by
    simpa [q, rounds] using firstWindow_rates rate rewards C_star C_h omega
  have hsmall : 4 * (p.m : ℝ) * q.eta ≤ 1 := by
    simpa [q] using four_m_eta_le_one rate
  have hpotential := RecordedPotentialTelescope.servedEstimate_cumulative_comparison
    q rounds p.two_le_m p.m_lt_K hsmall S
  have hpotentialAtLength :
      (∑ k : Fin rounds.length,
        ((∑ i ∈ S.1,
            RecordedPotentialStep.servedEstimate q
              (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) -
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal q p.m rounds k.val i *
              RecordedPotentialStep.servedEstimate q
                (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i)) ≤
        Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q *
          (rounds.length : ℝ) := hpotential
  have hlengthReal : (rounds.length : ℝ) ≤ (p.T : ℝ) := by
    exact_mod_cast hlength
  have hpotential' :
      firstWindowServedGap rate rewards C_star C_h omega S ≤
        Real.log (Nat.choose p.K p.m : ℝ) /
            RecordedPotentialStep.potentialLambda q +
          16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q * (p.T : ℝ) := by
    have hcoeff : 0 ≤ 16 * (p.m : ℝ) ^ 2 *
        RecordedPotentialStep.potentialLambda q := by
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (RecordedPotentialStep.potentialLambda_pos q).le
    have hpotentialGap :
        firstWindowServedGap rate rewards C_star C_h omega S ≤
          Real.log (Nat.choose p.K p.m : ℝ) /
              RecordedPotentialStep.potentialLambda q +
            16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q *
              (rounds.length : ℝ) := by
      change (∑ k : Fin rounds.length,
        ((∑ i ∈ S.1,
            RecordedPotentialStep.servedEstimate q
              (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) -
          ∑ i : Fin p.K,
            RecordedQueueSummation.runMarginal q p.m rounds k.val i *
              RecordedPotentialStep.servedEstimate q
                (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i)) ≤ _
      exact hpotentialAtLength
    calc
      firstWindowServedGap rate rewards C_star C_h omega S ≤
          Real.log (Nat.choose p.K p.m : ℝ) /
              RecordedPotentialStep.potentialLambda q +
            16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q *
              (rounds.length : ℝ) := hpotentialGap
      _ ≤ Real.log (Nat.choose p.K p.m : ℝ) /
            RecordedPotentialStep.potentialLambda q +
          16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda q * (p.T : ℝ) :=
        by
          have hmul := mul_le_mul_of_nonneg_left hlengthReal hcoeff
          linarith only [hmul]
  have hsummation := RecordedQueueSummation.run_raw_served_summation_by_parts_all
    q rounds p.two_le_m p.m_lt_K S
  have hidentity :
      firstWindowRawGap rate rewards C_star C_h omega S =
        firstWindowServedGap rate rewards C_star C_h omega S +
          (∑ i ∈ S.1,
            firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i) -
          ∑ i : Fin p.K,
            firstWindowMarginal rate rewards C_star C_h omega rounds.length i *
              firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i +
          firstWindowMarginalBacklogCorrection rate rewards C_star C_h omega := by
    simpa [firstWindowRawGap, firstWindowServedGap, firstWindowAcceptedArrival,
      firstWindowServedEstimate, firstWindowMarginal, firstWindowNormalizedBacklog,
      firstWindowMarginalBacklogCorrection,
      firstWindowRun, firstWindowQueue, firstWindowCells, q, rounds,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
      ReferenceFirstLaunchNumericalCell.queueParameters] using hsummation
  have hterminalBacklog (i : Fin p.K) :
      firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i ≤
        1 / (16 * q.eta) := by
    have htwice := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
      q rounds hrate rounds.length i
    have hscale : 2 * (1 / (32 * q.eta)) = 1 / (16 * q.eta) := by
      field_simp [ne_of_gt q.eta_pos]
      ring
    change StoppedQueueBound.normalizedBacklog q
      (RecordedQueueRun.run q (rounds.take rounds.length)) i ≤ 1 / (16 * q.eta)
    calc
      _ ≤ 2 * (1 / (32 * q.eta)) := by
        simpa [q, rounds] using htwice
      _ = 1 / (16 * q.eta) := hscale
  have hcomparatorBacklog :
      (∑ i ∈ S.1,
        firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i) ≤
        (p.m : ℝ) / (16 * q.eta) := by
    have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
    calc
      _ ≤ ∑ i ∈ S.1, 1 / (16 * q.eta) :=
        Finset.sum_le_sum fun i _ => hterminalBacklog i
      _ = (p.m : ℝ) / (16 * q.eta) := by
        simp [hcard, Finset.sum_const, nsmul_eq_mul]
        field_simp [ne_of_gt q.eta_pos]
  have hterminalWeightedNonneg :
      0 ≤ ∑ i : Fin p.K,
        firstWindowMarginal rate rewards C_star C_h omega rounds.length i *
          firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (RecordedQueueSummation.runMarginal_pos q p.m rounds rounds.length i
        p.two_le_m p.m_lt_K).le
      (div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg (firstWindowQueue rate).n))
  have hterminal :
      (∑ i ∈ S.1,
        firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i) -
        ∑ i : Fin p.K,
          firstWindowMarginal rate rewards C_star C_h omega rounds.length i *
            firstWindowNormalizedBacklog rate rewards C_star C_h omega rounds.length i ≤
        (p.m : ℝ) / (16 * rate.eta.val) := by
    have hqeta : q.eta = rate.eta.val := by rfl
    rw [hqeta] at hcomparatorBacklog
    linarith only [hcomparatorBacklog, hterminalWeightedNonneg]
  rw [hidentity]
  linarith only [hpotential', hterminal]

private theorem firstWindow_backlog_nonneg (omega : SourceInput p) (k : ℕ)
    (i : Fin p.K) :
    0 ≤ firstWindowNormalizedBacklog rate rewards C_star C_h omega k i := by
  change 0 ≤
    (((firstWindowRun rate rewards C_star C_h omega k).registers i).2 : ℝ) /
      ((firstWindowQueue rate).n : ℝ)
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

private theorem firstWindow_marginal_nonneg (omega : SourceInput p) (k : ℕ)
    (i : Fin p.K) : 0 ≤ firstWindowMarginal rate rewards C_star C_h omega k i :=
  (RecordedQueueSummation.runMarginal_pos (firstWindowQueue rate) p.m
    (firstWindowCells rate rewards C_star C_h omega) k i
    p.two_le_m p.m_lt_K).le

private theorem firstWindow_arrival_nonneg (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length)
    (i : Fin p.K) :
    0 ≤ firstWindowAcceptedArrival rate rewards C_star C_h omega k i := by
  exact div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg (rate.n))

private theorem firstWindow_weighted_arrival_nonneg (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length) :
    0 ≤ ∑ i : Fin p.K,
      firstWindowMarginal rate rewards C_star C_h omega k.val i *
        firstWindowAcceptedArrival rate rewards C_star C_h omega k i := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (firstWindow_marginal_nonneg rate rewards C_star C_h omega k.val i)
    (firstWindow_arrival_nonneg rate rewards C_star C_h omega k i)

private theorem firstWindow_weighted_backlogAt_nonneg (omega : SourceInput p)
    (t : Fin p.T) :
    0 ≤ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt
      rate rewards C_star C_h t.val omega := by
  unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt
  rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt]
  unfold RecordedWeightedDrift.weightedBacklog
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    ((RecordedQueueSummation.runMarginal_pos (firstWindowQueue rate) p.m
      (firstWindowCells rate rewards C_star C_h omega)
      (t.val - firstWindowStart rate rewards C_star C_h omega) i
      p.two_le_m p.m_lt_K).le)
    (div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_nonneg (firstWindowQueue rate).n))

private theorem firstWindow_cost_nonneg (omega : SourceInput p) (t : Fin p.T) :
    0 ≤ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
      rate rewards C_star C_h t omega := by
  by_cases hevent : omega ∈
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
        rate rewards C_star C_h t
  · simp [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost,
      hevent, firstWindow_weighted_backlogAt_nonneg rate rewards C_star C_h omega t]
  · simp [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost,
      hevent]

private theorem firstWindow_calendar_cost_eq_backlog (omega : SourceInput p)
    (k : Fin (firstWindowCells rate rewards C_star C_h omega).length)
    (hN : (firstWindowCells rate rewards C_star C_h omega).length ≤
      p.T - firstWindowStart rate rewards C_star C_h omega)
    (hactive :
      (firstWindowCells rate rewards C_star C_h omega)[k.val].enabled = true ∧
        (firstWindowRun rate rewards C_star C_h omega k.val).overflow = false) :
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
        rate rewards C_star C_h
        ⟨firstWindowStart rate rewards C_star C_h omega + k.val, by
          have hk : k.val < p.T - firstWindowStart rate rewards C_star C_h omega :=
            lt_of_lt_of_le k.isLt hN
          omega⟩ omega =
      firstWindowWeightedBacklog rate rewards C_star C_h omega k.val := by
  classical
  let start := firstWindowStart rate rewards C_star C_h omega
  let t : Fin p.T := ⟨start + k.val, by
    have hk : k.val < p.T - start := by
      exact lt_of_lt_of_le k.isLt hN
    omega⟩
  have hstartEq :
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
        rate rewards C_star C_h omega = start := by rfl
  have hrelative :
      t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
        rate rewards C_star C_h omega = k.val := by
    rw [hstartEq]
    dsimp [t, start]
    omega
  have hc := firstWindow_source_crossing rate rewards C_star C_h omega k
  have hcell := firstWindow_cell_enabled_rate rate rewards C_star C_h omega k
  have hrun :
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
        rate rewards C_star C_h t.val omega =
      firstWindowRun rate rewards C_star C_h omega k.val := by
    change RecordedQueueRun.run
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
        ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
          rate rewards C_star C_h omega).take
            (t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
              rate rewards C_star C_h omega)) =
      RecordedQueueRun.run
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue rate)
        ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
          rate rewards C_star C_h omega).take k.val)
    rw [hrelative]
  have hevent : omega ∈
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
        rate rewards C_star C_h t := by
    change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate omega rewards C_star C_h).crossing.isSome = true ∧
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
          rate rewards C_star C_h omega ≤ t.val ∧
      ∃ hn : t.val - ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
          rate rewards C_star C_h omega <
            (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
              rate rewards C_star C_h omega).length,
        ((ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
          rate rewards C_star C_h omega)[t.val -
            ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
              rate rewards C_star C_h omega]'hn).enabled = true ∧
          (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
            rate rewards C_star C_h t.val omega).overflow = false
    refine ⟨hc, ?_, ?_⟩
    · rw [hstartEq]
      dsimp [t]
      exact Nat.le_add_right _ _
    · refine ⟨?_, ?_, ?_⟩
      · rw [hrelative]
        exact k.isLt
      · simpa [hrelative, firstWindowCells,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells] using hcell.1
      · rw [hrun]
        exact hactive.2
  have hwindowBacklog :
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt
        rate rewards C_star C_h t.val omega =
      firstWindowWeightedBacklog rate rewards C_star C_h omega k.val := by
    unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt
    rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt]
    have hcalendarRelative : t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate omega rewards C_star C_h = k.val := by
      simpa [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart] using
        hrelative
    rw [hcalendarRelative]
    simp [firstWindowWeightedBacklog, firstWindowMarginal,
      firstWindowNormalizedBacklog, firstWindowRun, firstWindowQueue,
      firstWindowCells,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveQueue,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
      ReferenceFirstLiveCalendarPrefixReadout.queueParameters,
      ReferenceFirstLaunchNumericalCell.queueParameters,
      RecordedWeightedDrift.weightedBacklog,
      RecordedQueueSummation.runMarginal]
  change Set.indicator
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
        rate rewards C_star C_h t)
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt
        rate rewards C_star C_h t.val) omega = _
  rw [Set.indicator_of_mem hevent, hwindowBacklog]

/-- The signed first-live successor-marginal correction is controlled by the
actual retained calendar backlog and the same weighted accepted arrivals. -/
theorem firstWindowCorrection_le (omega : SourceInput p) :
    firstWindowMarginalBacklogCorrection rate rewards C_star C_h omega ≤
      8 * rate.eta.val *
        ((∑ t : Fin p.T,
            ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
              rate rewards C_star C_h t omega) +
          ∑ k : Fin (firstWindowCells rate rewards C_star C_h omega).length,
            ∑ i : Fin p.K,
              firstWindowMarginal rate rewards C_star C_h omega k.val i *
                firstWindowAcceptedArrival rate rewards C_star C_h omega k i) := by
  classical
  let q := firstWindowQueue rate
  let rounds := firstWindowCells rate rewards C_star C_h omega
  let start := firstWindowStart rate rewards C_star C_h omega
  let active : Finset (Fin rounds.length) := Finset.univ.filter fun k =>
    rounds[k.val].enabled = true ∧
      (RecordedQueueRun.run q (rounds.take k.val)).overflow = false
  let calendar (k : Fin rounds.length) : Fin p.T :=
    ⟨start + k.val, by
      have hN := firstWindow_length_le_remaining rate rewards C_star C_h omega
      have hk : k.val < p.T - start := by
        exact lt_of_lt_of_le k.isLt (by simpa [rounds, start] using hN)
      omega⟩
  have hN : rounds.length ≤ p.T - start := by
    simpa [rounds, start] using
      firstWindow_length_le_remaining rate rewards C_star C_h omega
  have hEta64 : q.eta ≤ 1 / 64 := by
    simpa [q] using firstWindow_eta_le_one_div_sixtyfour rate
  have hterm (k : Fin rounds.length) :
      (∑ i : Fin p.K,
        (RecordedQueueSummation.runMarginal q p.m rounds (k.val + 1) i -
          RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
          StoppedQueueBound.normalizedBacklog q
            (RecordedQueueRun.run q (rounds.take (k.val + 1))) i) ≤
        if k ∈ active then
          8 * rate.eta.val *
            (∑ i : Fin p.K,
              RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                StoppedQueueBound.normalizedBacklog q
                  (RecordedQueueRun.run q (rounds.take k.val)) i +
              ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  ((RecordedQueueRun.acceptedArrival
                    (RecordedQueueRun.acceptedRecord q
                      (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                    (rate.n : ℝ)))
        else 0 := by
    classical
    by_cases hk : k ∈ active
    · have hactive : rounds[k.val].enabled = true ∧
          (RecordedQueueRun.run q (rounds.take k.val)).overflow = false := by
        simpa [active] using hk
      have htheta (i : Fin p.K) :
          RecordedQueueSummation.runMarginal q p.m rounds (k.val + 1) i -
            RecordedQueueSummation.runMarginal q p.m rounds k.val i ≤
            8 * rate.eta.val * RecordedQueueSummation.runMarginal q p.m rounds k.val i := by
        have heta : q.eta = rate.eta.val := by rfl
        rw [← heta]
        have hgrowth := RecordedMarginalGrowth.run_prefix_theta_growth
          q rounds k.val k.isLt i p.two_le_m p.m_lt_K hEta64
        have h1 := hgrowth.1
        have h2 := hgrowth.2
        change RecordedQueueSummation.runMarginal q p.m rounds (k.val + 1) i ≤
          Real.exp (4 * q.eta) *
            RecordedQueueSummation.runMarginal q p.m rounds k.val i at h1
        change Real.exp (4 * q.eta) *
            RecordedQueueSummation.runMarginal q p.m rounds k.val i ≤
          (1 + 8 * q.eta) *
            RecordedQueueSummation.runMarginal q p.m rounds k.val i at h2
        linarith only [h1, h2]
      have hbnext (i : Fin p.K) :
          0 ≤ StoppedQueueBound.normalizedBacklog q
            (RecordedQueueRun.run q (rounds.take (k.val + 1))) i := by
        exact div_nonneg (Nat.cast_nonneg _)
          (Nat.cast_nonneg q.n)
      have htheta0 (i : Fin p.K) :
          0 ≤ RecordedQueueSummation.runMarginal q p.m rounds k.val i :=
        (RecordedQueueSummation.runMarginal_pos q p.m rounds k.val i
          p.two_le_m p.m_lt_K).le
      have hbacklogStep (i : Fin p.K) :
          StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take (k.val + 1))) i ≤
            StoppedQueueBound.normalizedBacklog q
                (RecordedQueueRun.run q (rounds.take k.val)) i +
              ((RecordedQueueRun.acceptedArrival
                (RecordedQueueRun.acceptedRecord q
                  (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                (rate.n : ℝ)) := by
        have hprefix := firstWindow_prefix_backlog_le_arrivals
          rate rewards C_star C_h omega k i
        simpa [firstWindowNormalizedBacklog, firstWindowAcceptedArrival,
          firstWindowRun, firstWindowCells, firstWindowQueue, q, rounds] using hprefix
      have hcoef (i : Fin p.K) :
          0 ≤ 8 * rate.eta.val * RecordedQueueSummation.runMarginal q p.m rounds k.val i :=
        mul_nonneg (mul_nonneg (by norm_num) (le_of_lt rate.eta.property)) (htheta0 i)
      rw [ite_eq_left hk]
      calc
        (∑ i : Fin p.K,
          (RecordedQueueSummation.runMarginal q p.m rounds (k.val + 1) i -
            RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
            StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take (k.val + 1))) i) ≤
          ∑ i : Fin p.K,
            (8 * rate.eta.val * RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
              (StoppedQueueBound.normalizedBacklog q
                  (RecordedQueueRun.run q (rounds.take k.val)) i +
                ((RecordedQueueRun.acceptedArrival
                  (RecordedQueueRun.acceptedRecord q
                    (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                  (rate.n : ℝ))) := by
            apply Finset.sum_le_sum
            intro i hi
            calc
              _ ≤ (8 * rate.eta.val * RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
                  StoppedQueueBound.normalizedBacklog q
                    (RecordedQueueRun.run q (rounds.take (k.val + 1))) i :=
                mul_le_mul_of_nonneg_right (htheta i) (hbnext i)
              _ ≤ (8 * rate.eta.val * RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
                  (StoppedQueueBound.normalizedBacklog q
                      (RecordedQueueRun.run q (rounds.take k.val)) i +
                    ((RecordedQueueRun.acceptedArrival
                      (RecordedQueueRun.acceptedRecord q
                        (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                      (rate.n : ℝ))) :=
                mul_le_mul_of_nonneg_left (hbacklogStep i) (hcoef i)
        _ = 8 * rate.eta.val *
            (∑ i : Fin p.K,
              RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                StoppedQueueBound.normalizedBacklog q
                  (RecordedQueueRun.run q (rounds.take k.val)) i +
             ∑ i : Fin p.K,
              RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                ((RecordedQueueRun.acceptedArrival
                  (RecordedQueueRun.acceptedRecord q
                    (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                  (rate.n : ℝ))) := by
          calc
            _ = ∑ i : Fin p.K,
                (8 * rate.eta.val *
                  (RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                    StoppedQueueBound.normalizedBacklog q
                      (RecordedQueueRun.run q (rounds.take k.val)) i) +
                 8 * rate.eta.val *
                  (RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                    ((RecordedQueueRun.acceptedArrival
                      (RecordedQueueRun.acceptedRecord q
                        (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                      (rate.n : ℝ)))) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = 8 * rate.eta.val *
                (∑ i : Fin p.K,
                  RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                    StoppedQueueBound.normalizedBacklog q
                      (RecordedQueueRun.run q (rounds.take k.val)) i +
                 ∑ i : Fin p.K,
                  RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                    ((RecordedQueueRun.acceptedArrival
                      (RecordedQueueRun.acceptedRecord q
                        (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                      (rate.n : ℝ))) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              ring
    · have hstop : rounds[k.val].enabled = false ∨
          (RecordedQueueRun.run q (rounds.take k.val)).overflow = true := by
        by_cases hEnabled : rounds[k.val].enabled = true
        · by_cases hOverflow :
              (RecordedQueueRun.run q (rounds.take k.val)).overflow = false
          · exact False.elim (hk (by simp [active, hEnabled, hOverflow]))
          · right
            cases hoverflow : (RecordedQueueRun.run q (rounds.take k.val)).overflow <;>
              simp_all
        · left
          cases henabled : rounds[k.val].enabled <;> simp_all
      rw [ite_eq_right hk]
      have hzero (i : Fin p.K) :=
        RecordedMarginalGrowth.run_prefix_theta_eq_of_disabled_or_overflowed
          (m := p.m) q rounds k.val k.isLt i hstop
      have hsum : ∑ i : Fin p.K,
          (RecordedQueueSummation.runMarginal q p.m rounds (k.val + 1) i -
            RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
            StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take (k.val + 1))) i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [RecordedQueueSummation.runMarginal, hzero i]
      rw [hsum]
  have hsumActive :
      (∑ k : Fin rounds.length,
        ∑ i : Fin p.K,
          (RecordedQueueSummation.runMarginal q p.m rounds (k.val + 1) i -
            RecordedQueueSummation.runMarginal q p.m rounds k.val i) *
            StoppedQueueBound.normalizedBacklog q
              (RecordedQueueRun.run q (rounds.take (k.val + 1))) i) ≤
        8 * rate.eta.val *
          ((∑ k ∈ active,
              ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  StoppedQueueBound.normalizedBacklog q
                    (RecordedQueueRun.run q (rounds.take k.val)) i) +
            ∑ k ∈ active,
              ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  ((RecordedQueueRun.acceptedArrival
                    (RecordedQueueRun.acceptedRecord q
                      (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                    (rate.n : ℝ))) := by
    calc
      _ ≤ ∑ k : Fin rounds.length,
          if k ∈ active then
            8 * rate.eta.val *
              (∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  StoppedQueueBound.normalizedBacklog q
                    (RecordedQueueRun.run q (rounds.take k.val)) i +
               ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  ((RecordedQueueRun.acceptedArrival
                    (RecordedQueueRun.acceptedRecord q
                      (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                    (rate.n : ℝ))) else 0 :=
        Finset.sum_le_sum fun k _ => hterm k
      _ = 8 * rate.eta.val *
          ((∑ k ∈ active,
              ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  StoppedQueueBound.normalizedBacklog q
                    (RecordedQueueRun.run q (rounds.take k.val)) i) +
            ∑ k ∈ active,
              ∑ i : Fin p.K,
                RecordedQueueSummation.runMarginal q p.m rounds k.val i *
                  ((RecordedQueueRun.acceptedArrival
                    (RecordedQueueRun.acceptedRecord q
                      (RecordedQueueRun.run q (rounds.take k.val)) rounds[k.val] i) : ℝ) /
                    (rate.n : ℝ))) := by
        simp [Finset.sum_ite_mem, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hbacklogActive :
      (∑ k ∈ active, firstWindowWeightedBacklog rate rewards C_star C_h omega k.val) ≤
        ∑ t : Fin p.T,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h t omega := by
    have hcalendar_inj : Function.Injective calendar := by
      intro k₁ k₂ hEq
      apply Fin.ext
      exact Nat.add_left_cancel (congrArg Fin.val hEq)
    have hpoint (k : Fin rounds.length) (hk : k ∈ active) :
        firstWindowWeightedBacklog rate rewards C_star C_h omega k.val =
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h (calendar k) omega := by
      have hactive : rounds[k.val].enabled = true ∧
          (RecordedQueueRun.run q (rounds.take k.val)).overflow = false := by
        simpa [active] using hk
      have hcost := firstWindow_calendar_cost_eq_backlog rate rewards C_star C_h omega k
        (by simpa [rounds, start] using hN) hactive
      simpa [calendar, q, rounds, start, firstWindowQueue, firstWindowCells,
        firstWindowStart] using hcost.symm
    calc
      _ = ∑ k ∈ active,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h (calendar k) omega := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hpoint k hk
      _ = ∑ t ∈ active.image calendar,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h t omega := by
        rw [Finset.sum_image (fun k hk k' hk' heq => hcalendar_inj heq)]
      _ ≤ ∑ t : Fin p.T,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h t omega :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun t _ _ => firstWindow_cost_nonneg rate rewards C_star C_h omega t)
  have harrivalActive :
      (∑ k ∈ active,
        ∑ i : Fin p.K,
          firstWindowMarginal rate rewards C_star C_h omega k.val i *
            firstWindowAcceptedArrival rate rewards C_star C_h omega k i) ≤
        ∑ k : Fin rounds.length,
          ∑ i : Fin p.K,
            firstWindowMarginal rate rewards C_star C_h omega k.val i *
              firstWindowAcceptedArrival rate rewards C_star C_h omega k i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => firstWindow_weighted_arrival_nonneg rate rewards C_star C_h omega k)
  have hmain :
      firstWindowMarginalBacklogCorrection rate rewards C_star C_h omega ≤
        8 * rate.eta.val *
          ((∑ t : Fin p.T,
              ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
                rate rewards C_star C_h t omega) +
            ∑ k : Fin rounds.length,
              ∑ i : Fin p.K,
                firstWindowMarginal rate rewards C_star C_h omega k.val i *
                  firstWindowAcceptedArrival rate rewards C_star C_h omega k i) := by
    have hsum := hsumActive
    have hbacklogTransport := hbacklogActive
    have harrivalTransport := harrivalActive
    have hetaNonneg : 0 ≤ 8 * rate.eta.val := by
      have heta : 0 < rate.eta.val := rate.eta.property
      positivity
    dsimp [firstWindowMarginalBacklogCorrection]
    calc
      _ ≤ 8 * rate.eta.val *
          ((∑ k ∈ active,
              firstWindowWeightedBacklog rate rewards C_star C_h omega k.val) +
            ∑ k ∈ active,
              ∑ i : Fin p.K,
                firstWindowMarginal rate rewards C_star C_h omega k.val i *
                  firstWindowAcceptedArrival rate rewards C_star C_h omega k i) := by
        simpa [firstWindowMarginal, firstWindowNormalizedBacklog,
          firstWindowAcceptedArrival, firstWindowRun, firstWindowCells, firstWindowQueue,
          q, rounds, firstWindowWeightedBacklog] using hsum
      _ ≤ 8 * rate.eta.val *
          ((∑ t : Fin p.T,
              ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
                rate rewards C_star C_h t omega) +
            ∑ k : Fin rounds.length,
              ∑ i : Fin p.K,
                firstWindowMarginal rate rewards C_star C_h omega k.val i *
                  firstWindowAcceptedArrival rate rewards C_star C_h omega k i) := by
        apply mul_le_mul_of_nonneg_left _ hetaNonneg
        exact add_le_add hbacklogTransport harrivalTransport
  exact hmain

end Bandits.Support.ReferenceFirstLiveRawPotentialBound

end
