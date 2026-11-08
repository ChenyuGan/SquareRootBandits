/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOldConditionalWeightedEnergyDrift
public import Bandits.Support.ReferenceFirstCollectionPrecallLiveOldMass
public import Bandits.Support.ReferenceFirstLiveOriginalCalendarWeightedBacklogBound

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Original-source pre-call weighted backlog budget

The scalar potential is the accepted optional OLD potential on the original
calendar prefix. Its first-LIVE portion and actual OLD continuation are charged
against one common source-cell mass budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionPrecallWeightedBacklogBound

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open ReferenceFirstCollectionPrecallCalendarSupport
open ReferenceFirstCollectionOldCalendarExponentialStep (E G)
open ReferenceFirstLiveSourcePhasePartition (originalEmptyEvent)
open ReferenceFirstLiveBranchIntegralTransport (originalBranchEvent)

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "s" z:max => ReferenceCompletePhysicalHistory.physicalStart
  rate z rewards C_star C_h
local notation "V" => ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
  rate rewards C_star C_h
local notation "W" => ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt
  rate rewards C_star C_h
local notation "Phi" =>
  ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential
    rate rewards C_star C_h

private theorem firstWindowPotentialAt_preserve (m n : ℕ) (z : S)
    (hm : s z + (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z).length ≤ m)
    (hn : s z + (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z).length ≤ n) :
    V m z = V n z := by
  have hm' : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z).length ≤ m - s z := by omega
  have hn' : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z).length ≤ n - s z := by omega
  simp only [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt,
    List.take_of_length_le hm', List.take_of_length_le hn']

private theorem firstWindowPotentialAt_zero_before_start (n : ℕ) (z : S)
    (hn : n ≤ s z) : V n z = 0 := by
  simp [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt,
    Nat.sub_eq_zero_of_le hn, RecordedWeightedDrift.weightedSquarePotential,
    RecordedQueueRun.run, RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

private theorem firstWindowPotentialAt_zero_no_launch (n : ℕ) (z : S)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome ≠ true) :
    V n z = 0 := by
  have hV : ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z = [] := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
    split
    · rename_i h
      exact (hc h).elim
    · rfl
  simp [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt, hV,
    RecordedWeightedDrift.weightedSquarePotential, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

private theorem precallPotential_eq_firstWindowPotentialAt (n : ℕ) (z : S)
    (hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n z)
    (hlive : n ≤ s z +
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z).length) :
    Phi n z = V n z := by
  unfold ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential
  rw [ReferenceFirstCollectionPrecallCalendarIncrementIdentity.precallCells_eq_firstLive_take
    rate rewards C_star C_h n z hz hlive]
  rfl

private theorem dOld_eq_potential_increment_of_mem_E (t : Fin p.T) (z : S)
    (hz : z ∈ E rate rewards C_star C_h t) :
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t z = Phi (t.val + 1) z - Phi t.val z := by
  have h := congrFun
    (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_increment_eq_E_increment
      rate rewards C_star C_h t) z
  rw [Set.indicator_of_mem hz] at h
  simpa only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld] using h

private theorem dOld_eq_zero_of_not_mem_E (t : Fin p.T) (z : S)
    (hz : z ∉ E rate rewards C_star C_h t) :
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t z = 0 := by
  have h := congrFun
    (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_increment_eq_E_increment
      rate rewards C_star C_h t) z
  rw [Set.indicator_of_notMem hz] at h
  simpa only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld] using h

private theorem not_mem_E_of_oldCell_none (t : Fin p.T) (z : S)
    (hnone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
      rate rewards C_star C_h t z = none) :
    z ∉ E rate rewards C_star C_h t := by
  intro hz
  have h := (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
    rate rewards C_star C_h t z).mp hz |>.2
  simp only [hnone, Option.isSome_none, Bool.false_eq_true] at h

theorem precallPotential_zero (z : S) : Phi 0 z = 0 := by
  by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h (ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
        rate rewards C_star C_h 0 z) z
  · have hlaunch0 : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h 0 z := by
      simpa [ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary] using hlaunch
    simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential,
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?, hlaunch0,
      ReferenceFirstCollectionPrecallCalendarSupport.precallSlots,
      ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary,
      RecordedWeightedDrift.weightedSquarePotential, RecordedQueueRun.run,
      RecordedQueueRun.execute, RecordedQueueRun.initialState,
      StoppedQueueBound.normalizedBacklog]
  · have hlaunch0 : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h 0 z := by
      intro h0
      apply hlaunch
      simpa [ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary] using h0
    simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential,
      ReferenceFirstCollectionPrecallCalendarSupport.precallCells?, hlaunch0,
      ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary]

private theorem precallPotential_zero_on_empty (n : ℕ) (z : S)
    (hL : ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
      rate rewards C_star C_h n z = some []) : Phi n z = 0 := by
  simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential, hL,
    RecordedWeightedDrift.weightedSquarePotential, RecordedQueueRun.run,
    RecordedQueueRun.execute, RecordedQueueRun.initialState,
    StoppedQueueBound.normalizedBacklog]

/-! The weighted increment is proved on the original optional calendar word. -/

/-- The actual pre-call weighted potential has the first-LIVE calendar step
plus the accepted OLD increment at every source and date. -/
theorem precallPotential_calendar_increment (t : Fin p.T) (z : S) :
    Phi (t.val + 1) z - Phi t.val z =
      (V (t.val + 1) z - V t.val z) +
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
          rate rewards C_star C_h t z := by
  by_cases hafter : ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
      rate rewards C_star C_h z ≤ t.val
  · have hprefix := ReferenceFirstCollectionPrecallCalendarSupport.precallCells_preserve
      rate rewards C_star C_h (t.val + 1) t.val z (by omega) hafter
    have hPhi : Phi (t.val + 1) z = Phi t.val z := by
      simp only [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential, hprefix]
    have hend := ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
      rate rewards C_star C_h z
    have hV := firstWindowPotentialAt_preserve rate rewards C_star C_h
      (t.val + 1) t.val z (by omega) (by omega)
    have hnot : z ∉ E rate rewards C_star C_h t := by
      intro hz
      have hb := (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
        rate rewards C_star C_h t z).mp hz |>.1
      omega
    rw [hPhi, hV, dOld_eq_zero_of_not_mem_E rate rewards C_star C_h t z hnot]
    ring
  · have hbefore : t.val <
      ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary rate rewards C_star C_h z := by
        omega
    by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h t.val z
    · obtain ⟨L, r, c, hL, hr, htime, hcell, hread, hnext, _⟩ :=
        ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_append
          rate rewards C_star C_h t z hz hbefore
      rcases hread with ⟨_hlive, holdNone⟩ | ⟨hold, _⟩
      · have hlt : t.val < s z +
          (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
            rate rewards C_star C_h z).length := by
          by_contra h
          obtain ⟨c0, hcollection, _⟩ :=
            ReferenceFirstCollectionOldPrefixOriginRateCredit.actual_old_cell_after_firstLive_before_boundary
              rate rewards C_star C_h t z hz hbefore r hr (by omega)
          rw [holdNone] at hcollection
          cases hcollection
        have hzNext : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
            rate rewards C_star C_h (t.val + 1) z :=
          ⟨hz.1, hz.2.trans (Nat.le_succ _)⟩
        have hcurrent := precallPotential_eq_firstWindowPotentialAt
          rate rewards C_star C_h t.val z hz (Nat.le_of_lt hlt)
        have hnextPot := precallPotential_eq_firstWindowPotentialAt
          rate rewards C_star C_h (t.val + 1) z hzNext (by omega)
        have hnone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
            rate rewards C_star C_h t z = none := by
          simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hr,
            Option.bind_some, holdNone]
        have hnot := not_mem_E_of_oldCell_none rate rewards C_star C_h t z hnone
        calc
          Phi (t.val + 1) z - Phi t.val z =
              V (t.val + 1) z - V t.val z :=
                congrArg₂ (fun x y : ℝ => x - y) hnextPot hcurrent
          _ = (V (t.val + 1) z - V t.val z) + 0 := by ring
          _ = (V (t.val + 1) z - V t.val z) +
              ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
                rate rewards C_star C_h t z := by
            rw [dOld_eq_zero_of_not_mem_E rate rewards C_star C_h t z hnot]
      · have hE : z ∈ E rate rewards C_star C_h t := by
          apply (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
            rate rewards C_star C_h t z).mpr
          refine ⟨hbefore, ?_⟩
          simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hr,
            Option.bind_some, hold, Option.isSome_some]
        have hend :=
          ReferenceFirstCollectionPrecallCalendarSupport.old_readout_after_firstLiveWindow
            rate rewards C_star C_h t z hz r hr (by rw [hold]; rfl)
        have hendCells : s z +
            (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
              rate rewards C_star C_h z).length ≤ t.val := by
          rw [ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
            rate rewards C_star C_h z]
          exact hend
        have hV := firstWindowPotentialAt_preserve rate rewards C_star C_h
          (t.val + 1) t.val z (by omega) hendCells
        rw [hV, sub_self, zero_add]
        exact (dOld_eq_potential_increment_of_mem_E
          rate rewards C_star C_h t z hE).symm
    · have hcut : ReferenceFirstCollectionPrecallCalendarSupport.cutBoundary
          rate rewards C_star C_h t.val z = t.val :=
        Nat.min_eq_left (Nat.le_of_lt hbefore)
      have hnone : ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
          rate rewards C_star C_h t.val z = none :=
        ReferenceFirstCollectionPrecallCalendarSupport.precallCells_no_launch
          rate rewards C_star C_h t.val z (by rw [hcut]; exact hz)
      have hnext : ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
          rate rewards C_star C_h (t.val + 1) z = none ∨
          ReferenceFirstCollectionPrecallCalendarSupport.precallCells?
            rate rewards C_star C_h (t.val + 1) z = some [] := by
        rcases ReferenceFirstCollectionPrecallCalendarSupport.precallPrefix_step_or_preserve
            rate rewards C_star C_h t z with hpreserve | habsent | happend
        · exact (Nat.not_le_of_gt hbefore hpreserve.1).elim
        · exact habsent.2.2.2
        · obtain ⟨_, L, c, hL, _, _⟩ := happend
          rw [hnone] at hL
          cases hL
      have hPhi : Phi t.val z = 0 := by
        simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential, hnone]
      have hPhiNext : Phi (t.val + 1) z = 0 := by
        rcases hnext with hn | hn
        · simp [ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential, hn]
        · exact precallPotential_zero_on_empty rate rewards C_star C_h (t.val + 1) z hn
      have hcross : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∨
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome ≠ true :=
        Classical.em _
      have hV0 : V t.val z = 0 ∧ V (t.val + 1) z = 0 := by
        rcases hcross with hc | hc
        · have hs : t.val + 1 ≤ s z := by
            by_contra h
            exact hz ⟨hc, by omega⟩
          exact ⟨firstWindowPotentialAt_zero_before_start rate rewards C_star C_h t.val z (by omega),
            firstWindowPotentialAt_zero_before_start rate rewards C_star C_h (t.val + 1) z hs⟩
        · exact ⟨firstWindowPotentialAt_zero_no_launch rate rewards C_star C_h t.val z hc,
            firstWindowPotentialAt_zero_no_launch rate rewards C_star C_h (t.val + 1) z hc⟩
      have hrecord := ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
        rate rewards C_star C_h t z hz
      have hOldNone : ReferenceFirstCollectionOldRecorderFoundation.oldCell?
          rate rewards C_star C_h t z = none := by
        simp only [ReferenceFirstCollectionOldRecorderFoundation.oldCell?, hrecord,
          Option.bind_none]
      have hnot := not_mem_E_of_oldCell_none rate rewards C_star C_h t z hOldNone
      rw [hPhiNext, hPhi]
      calc
        0 - 0 = (0 - 0) + 0 := by ring
        _ = (V (t.val + 1) z - V t.val z) +
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
              rate rewards C_star C_h t z := by
          rw [hV0.1, hV0.2,
            dOld_eq_zero_of_not_mem_E rate rewards C_star C_h t z hnot]

/-- Whole-carrier regularity of the inherited optional OLD potential. -/
theorem precallPotential_regular (n : ℕ) (hn : n ≤ p.T) :
    Measurable (Phi n) ∧ Integrable (Phi n) μ := by
  have h := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_scalar_readouts_regular
    rate rewards C_star C_h n hn
  exact ⟨h.1, h.2.1⟩

/-- The terminal readout retains the nonnegative optional-prefix energy even
when no call occurs. -/
theorem precallPotential_terminal_nonneg (z : S) : 0 ≤ Phi p.T z :=
  (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readout_bounds
    rate rewards C_star C_h p.T (Nat.le_refl _) z).1

private theorem sum_fin_sub_succ (b : ℕ → ℝ) (n : ℕ) :
    (∑ t : Fin n, (b (t.val + 1) - b t.val)) = b n - b 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

/-- Exact finite integral telescope of the original optional OLD potential. -/
theorem integral_preCallPotential_telescope :
    (∫ z, Phi p.T z ∂μ) =
      ∑ t : Fin p.T, ∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ := by
  have hpoint : (fun z : S =>
      ∑ t : Fin p.T, (Phi (t.val + 1) z - Phi t.val z)) = Phi p.T := by
    funext z
    rw [sum_fin_sub_succ (fun n => Phi n z) p.T]
    rw [precallPotential_zero rate rewards C_star C_h z]
    ring
  calc
    (∫ z, Phi p.T z ∂μ) =
        ∫ z, ∑ t : Fin p.T, (Phi (t.val + 1) z - Phi t.val z) ∂μ := by
          rw [hpoint]
    _ = ∑ t : Fin p.T, ∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ := by
      rw [integral_finsetSum Finset.univ fun t _ =>
        (precallPotential_regular rate rewards C_star C_h (t.val + 1)
          (Nat.succ_le_of_lt t.isLt)).2.sub
          (precallPotential_regular rate rewards C_star C_h t.val
            (Nat.le_of_lt t.isLt)).2]

theorem firstLive_cell_mass_bound
    (t : Fin p.T) (control0 : TimeControl p) :
    (∫ z, V (t.val + 1) z - V t.val z ∂μ) ≤
      -(11 / 2 : ℝ) *
        (∫ z, ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
          rate rewards C_star C_h t z ∂μ) +
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ((∑ q : Fin (ConstructorDimensions.M p),
          (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
         ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
          ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
           (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
              v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) := by
  let H := {z : S | (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
    rate rewards C_star C_h t.val z).overflow = false}
  let f := fun z : S => V (t.val + 1) z - V t.val z
  let nonemptyCell := fun (q : Fin (ConstructorDimensions.M p))
      (v : Fin (t.val + 1)) =>
    originalBranchEvent rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0
  let emptyCell := fun (q : Fin (ConstructorDimensions.M p))
      (v : Fin (t.val + 1)) =>
    originalEmptyEvent rate rewards C_star C_h q t v.val
      (Nat.lt_succ_iff.mp v.isLt) control0
  let cost := fun q v =>
    (∫ z in nonemptyCell q v ∩ H,
      W (t.val) z ∂μ) +
    (∫ z in emptyCell q v ∩ H,
      W (t.val) z ∂μ)
  let mass := fun q v => (μ).real (nonemptyCell q v) + (μ).real (emptyCell q v)
  let delta := fun q v => (∫ z in nonemptyCell q v, f z ∂μ) +
    (∫ z in emptyCell q v, f z ∂μ)
  let birthMass := fun q : Fin (ConstructorDimensions.M p) =>
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ
  let birth := fun q : Fin (ConstructorDimensions.M p) =>
    ∫ z, ReferenceFirstLaunchEnergyInitialization.birthPotential
      rate rewards C_star C_h q t control0 z ∂
      ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hC : 0 ≤ C := by
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
    have hsub : 0 ≤ 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
    dsimp [C, CanonicalRecordingRates.R]
    positivity
  have hcost :
      (∫ z, ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
        rate rewards C_star C_h t z ∂μ) = ∑ q, ∑ v, cost q v := by
    simpa only [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt,
      H, cost, nonemptyCell, emptyCell] using
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integral_retainedWeightedBacklogCost_eq_sum
        rate rewards C_star C_h t control0
  have hbirth (q : Fin (ConstructorDimensions.M p)) :
      birth q ≤ C * birthMass q := by
    exact ReferenceFirstLaunchEnergyInitialization.integral_birthPotential
      rate rewards C_star C_h q t control0
  have hcell (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) :
      delta q v ≤ -(11 / 2 : ℝ) * cost q v + C * mass q v := by
    have hN := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.nonemptyOriginalPotentialStep_bound
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
    have hE := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.emptyOriginalPotentialStep_bound
      rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control0
    have hn : (μ).real (nonemptyCell q v ∩ H) ≤ (μ).real (nonemptyCell q v) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have he : (μ).real (emptyCell q v ∩ H) ≤ (μ).real (emptyCell q v) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have hm := mul_le_mul_of_nonneg_left (add_le_add hn he) hC
    change (∫ z in nonemptyCell q v, f z ∂μ) ≤
      -(11 / 2 : ℝ) * (∫ z in nonemptyCell q v ∩ H, W t.val z ∂μ) +
        C * (μ).real (nonemptyCell q v ∩ H) at hN
    change (∫ z in emptyCell q v, f z ∂μ) ≤
      -(11 / 2 : ℝ) * (∫ z in emptyCell q v ∩ H, W t.val z ∂μ) +
        C * (μ).real (emptyCell q v ∩ H) at hE
    dsimp only [delta, cost, mass]
    linarith only [hN, hE, hm]
  have hstep :
      (∫ z, f z ∂μ) = (∑ q, birth q) + (∑ q, ∑ v, delta q v) := by
    dsimp only [birth, delta, nonemptyCell, emptyCell, f]
    simp_rw [← ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch
        rate rewards C_star C_h,
      ← ReferenceFirstLiveSourcePhasePartition.integral_originalEmpty
        rate rewards C_star C_h]
    exact ReferenceFirstLiveCalendarIntegralAssembly.integral_potential_calendar_step
      rate rewards C_star C_h t control0
  calc
    (∫ z, f z ∂μ) = (∑ q, birth q) + (∑ q, ∑ v, delta q v) := hstep
    _ ≤ (∑ q, C * birthMass q) +
        ∑ q, ∑ v, (-(11 / 2 : ℝ) * cost q v + C * mass q v) :=
      add_le_add (Finset.sum_le_sum fun q _ => hbirth q)
        (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun v _ => hcell q v)
    _ = -(11 / 2 : ℝ) * (∑ q, ∑ v, cost q v) +
        C * ((∑ q, birthMass q) + (∑ q, ∑ v, mass q v)) := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ = -(11 / 2 : ℝ) *
        (∫ z, ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
          rate rewards C_star C_h t z ∂μ) +
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          ((∑ q : Fin (ConstructorDimensions.M p),
            (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
              (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
           ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
            ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
                v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
             (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
                v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)) := by
      rw [← hcost]
      simp only [birthMass, mass, nonemptyCell, emptyCell, Measure.real_def,
        ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_mass_original,
        ReferenceFirstLiveSourcePhasePartition.muEmpty_mass_original]
      dsimp only [C]

/-- One actual calendar step pays both weighted costs using the exact shared
birth/continuing/empty/OLD source masses. -/
theorem integral_preCallPotential_calendar_step_le
    (t : Fin p.T) (control0 : TimeControl p) :
    (∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
      (11 / 2 : ℝ) *
        (∫ z,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
              rate rewards C_star C_h t z +
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
              rate rewards C_star C_h t z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
  let liveCost := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
    rate rewards C_star C_h t
  let oldCost := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
    rate rewards C_star C_h t
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  let liveMass :=
    (∑ q : Fin (ConstructorDimensions.M p),
      (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real Set.univ) +
    ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
      ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ +
       (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
          v.val (Nat.lt_succ_iff.mp v.isLt) control0).real Set.univ)
  have hPhi := precallPotential_regular rate rewards C_star C_h (t.val + 1)
    (Nat.succ_le_of_lt t.isLt)
  have hPhi0 := precallPotential_regular rate rewards C_star C_h t.val
    (Nat.le_of_lt t.isLt)
  have hDelta : Integrable (fun z : S => Phi (t.val + 1) z - Phi t.val z) μ :=
    hPhi.2.sub hPhi0.2
  have hOld := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
    rate rewards C_star C_h control0 t
  have hD : Integrable
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t) μ := hOld.2.1
  have hOldCost : Integrable oldCost μ := hOld.2.2.2
  have hLive : Integrable liveCost μ :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
      rate rewards C_star C_h t control0
  have hV : Integrable (fun z : S => V (t.val + 1) z - V t.val z) μ := by
    have heq : (fun z : S => V (t.val + 1) z - V t.val z) =
        fun z => (Phi (t.val + 1) z - Phi t.val z) -
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z := by
      funext z
      rw [precallPotential_calendar_increment rate rewards C_star C_h t z]
      ring
    rw [heq]
    exact hDelta.sub hD
  have hIntegralIdentity :
      (∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) =
        (∫ z, V (t.val + 1) z - V t.val z ∂μ) +
          ∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z ∂μ := by
    calc
      _ = ∫ z, (V (t.val + 1) z - V t.val z) +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
            rate rewards C_star C_h t z ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact precallPotential_calendar_increment rate rewards C_star C_h t z
      _ = _ := integral_add hV hD
  have hLiveStep := firstLive_cell_mass_bound rate rewards C_star C_h t control0
  have hLiveCombined :
      (∫ z, V (t.val + 1) z - V t.val z ∂μ) +
        (11 / 2 : ℝ) * (∫ z, liveCost z ∂μ) ≤ C * liveMass := by
    have hh := hLiveStep
    dsimp only [C, liveMass, liveCost] at hh ⊢
    linarith only [hh]
  have hOldStep := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.sourceIntegral_weighted_cost
    rate rewards C_star C_h control0 t
  have hOldCombined :
      (∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t z ∂μ) +
        (11 / 2 : ℝ) * (∫ z, oldCost z ∂μ) ≤
      C * (μ).real (G rate rewards C_star C_h t) := by
    simpa [C, oldCost] using hOldStep
  have hMass := ReferenceFirstCollectionPrecallLiveOldMass.source_cell_masses_add_G_le_one
    rate rewards C_star C_h t control0
  have hShared : liveMass + (μ).real (G rate rewards C_star C_h t) ≤ 1 := by
    simpa only [liveMass] using hMass
  have hC : 0 ≤ C := by
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
    have hsub : 0 ≤ 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
    dsimp [C, CanonicalRecordingRates.R]
    positivity
  have hCostIntegral :
      (∫ z, liveCost z + oldCost z ∂μ) =
        (∫ z, liveCost z ∂μ) + (∫ z, oldCost z ∂μ) := integral_add hLive hOldCost
  change (∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
      (11 / 2 : ℝ) * (∫ z, liveCost z + oldCost z ∂μ) ≤ C
  rw [hIntegralIdentity, hCostIntegral]
  calc
    _ = ((∫ z, V (t.val + 1) z - V t.val z ∂μ) +
          (11 / 2 : ℝ) * (∫ z, liveCost z ∂μ)) +
        ((∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
          rate rewards C_star C_h t z ∂μ) +
          (11 / 2 : ℝ) * (∫ z, oldCost z ∂μ)) := by ring
    _ ≤ C * liveMass +
        C * (μ).real (G rate rewards C_star C_h t) := add_le_add hLiveCombined hOldCombined
    _ = C * (liveMass + (μ).real (G rate rewards C_star C_h t)) := by ring
    _ ≤ C := (mul_le_mul_of_nonneg_left hShared hC).trans_eq (mul_one _)

/-- The original-source pre-call calendar identity budget. Both retained
weighted costs use one calendar sum and one source-cell probability budget. -/
theorem integral_preCallPotential_and_weighted_cost_bound
    (control0 : TimeControl p) :
    (∫ z, Phi p.T z ∂μ) +
      (11 / 2 : ℝ) *
        (∫ z, ∑ t : Fin p.T,
          (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
              rate rewards C_star C_h t z +
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
              rate rewards C_star C_h t z) ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
  have hsum0 := Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
    integral_preCallPotential_calendar_step_le rate rewards C_star C_h t control0
  have hsum :
      (∑ t : Fin p.T,
        ∫ z, Phi (t.val + 1) z - Phi t.val z ∂μ) +
        (11 / 2 : ℝ) * (∑ t : Fin p.T,
          ∫ z,
            ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
                rate rewards C_star C_h t z +
              ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
                rate rewards C_star C_h t z ∂μ) ≤
      ∑ _t : Fin p.T,
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hsum0
  have hcostInt :
      (∫ z, ∑ t : Fin p.T,
        (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
            rate rewards C_star C_h t z +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
            rate rewards C_star C_h t z) ∂μ) =
        ∑ t : Fin p.T, ∫ z,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
              rate rewards C_star C_h t z +
            ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
              rate rewards C_star C_h t z ∂μ := by
    exact integral_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  rw [← integral_preCallPotential_telescope rate rewards C_star C_h,
    ← hcostInt] at hsum
  calc
    _ ≤ (p.T : ℝ) *
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
    _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by ring

/-- Dropping the nonnegative terminal energy and OLD backlog cost leaves the
same sharp weighted-backlog budget for the full pre-call calendar. -/
theorem integral_retainedWeightedBacklogCost_preCall_le
    (control0 : TimeControl p) :
    (∫ z, ∑ t : Fin p.T,
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
        rate rewards C_star C_h t z ∂μ) ≤
      (2 / 11 : ℝ) *
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
  let liveCost := fun t : Fin p.T =>
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
      rate rewards C_star C_h t
  let oldCost := fun t : Fin p.T =>
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
      rate rewards C_star C_h t
  let allCost := fun z : S => ∑ t : Fin p.T, (liveCost t z + oldCost t z)
  let liveTotal := fun z : S => ∑ t : Fin p.T, liveCost t z
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hLiveInt : Integrable liveTotal μ :=
    integrable_finsetSum Finset.univ fun t _ =>
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0
  have hAllInt : Integrable allCost μ :=
    integrable_finsetSum Finset.univ fun t _ =>
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
        rate rewards C_star C_h t control0).add
      (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
        rate rewards C_star C_h control0 t).2.2.2
  have hpoint : ∀ z, liveTotal z ≤ allCost z := by
    intro z
    dsimp only [liveTotal, allCost]
    apply Finset.sum_le_sum
    intro t _
    have hOld : 0 ≤ oldCost t z := by
      by_cases hg : z ∈ G rate rewards C_star C_h t
      · simp [oldCost, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld, hg]
        exact (ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readout_bounds
          rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) z).2.2.1
      · simp [oldCost, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld, hg]
    linarith
  have hle := integral_mono_ae hLiveInt hAllInt (Filter.Eventually.of_forall hpoint)
  have hterm : 0 ≤ ∫ z, Phi p.T z ∂μ :=
    integral_nonneg fun z => precallPotential_terminal_nonneg rate rewards C_star C_h z
  have hstrong := integral_preCallPotential_and_weighted_cost_bound
    rate rewards C_star C_h control0
  have hstrong' :
      (∫ z, Phi p.T z ∂μ) + (11 / 2 : ℝ) * (∫ z, allCost z ∂μ) ≤ C * (p.T : ℝ) := by
    simpa [C, allCost, liveCost, oldCost] using hstrong
  have hle' := mul_le_mul_of_nonneg_left hle (by norm_num : 0 ≤ (11 / 2 : ℝ))
  have hfinal : (11 / 2 : ℝ) * (∫ z, liveTotal z ∂μ) ≤ C * (p.T : ℝ) := by
    linarith only [hstrong', hle', hterm]
  dsimp only [liveTotal, liveCost] at hfinal ⊢
  dsimp only [C] at hfinal
  nlinarith only [hfinal]

end Bandits.Support.ReferenceFirstCollectionPrecallWeightedBacklogBound

end
