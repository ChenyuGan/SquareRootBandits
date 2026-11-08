/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpSourceCalendar

import Lean.Elab.Tactic.Omega

/-!
# Original-source UP calendar recurrence and tail

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:111-153`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The recurrence is on the exact finite physical calendar and the original
source-input law. Its zero event is the original selected-row stratum. The
all-J event is the literal finite union of those same calendar events. These
are unconditional fixed-candidate source-law bounds; they do not provide
completed-batch coverage or a conditional-at-birth theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open scoped Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AdaptiveAffineBatchTail
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpSourceCalendar

namespace Bandits.Support.ReferenceGeneratedUpSourceTail

abbrev Parameters := ReferenceGeneratedUpSourceCalendar.Parameters
abbrev RateInput := ReferenceGeneratedUpSourceCalendar.RateInput
abbrev TimeControl := ReferenceGeneratedUpSourceCalendar.TimeControl
abbrev SourceInput := ReferenceGeneratedUpSourceCalendar.SourceInput
abbrev Candidate (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)

variable {p : Parameters} {rate : RateInput p}

/-- The actual all-J union of the same original-source calendar survival
events. In particular, its zero fiber is the partition by the original `J`. -/
def upSourceAllJSurvivalEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ) : Set (SourceInput p) :=
  ⋃ q : Fin (M p),
    ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q control0 alpha candidate i ell

/-- Every calendar survival stratum retains its original selected-row index.
For positive ordinals this follows from the actual generated launch witness
in each literal calendar constituent. -/
theorem upSourceSurvivalEvent_subset_selectedRowIndex
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ) :
    ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q control0 alpha candidate i ell ⊆
        {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q} := by
  cases ell with
  | zero => exact Set.Subset.rfl
  | succ n =>
      intro z hz
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
      change z ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
          rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
            control0 alpha (n + 1) candidate i ∧
        AffineChannelLaw.affineHash (((z.1.2 q).2 c.1).2 (1, i)) candidate = 1 at hc
      obtain ⟨hbranch, _, _⟩ := hc.1
      exact ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
        (rate := rate) rewards C_star C_h q c.1 (1, i) c.2.val ⟨z, hbranch⟩

/-- Different original selected-row strata are disjoint for every ordinal. -/
theorem upSourceSurvivalEvent_pairwiseDisjoint
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun q : Fin (M p) =>
        ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell)) := by
  intro q q' hne
  change Disjoint
    (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q control0 alpha candidate i ell)
    (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q' control0 alpha candidate i ell)
  rw [Set.disjoint_left]
  intro z hz hz'
  have hrow := upSourceSurvivalEvent_subset_selectedRowIndex
    (rate := rate) rewards C_star C_h q control0 alpha candidate i ell hz
  have hrow' := upSourceSurvivalEvent_subset_selectedRowIndex
    (rate := rate) rewards C_star C_h q' control0 alpha candidate i ell hz'
  exact hne (hrow.symm.trans hrow')

/-- Measurability of the literal all-J union under the original source space. -/
theorem measurableSet_upSourceAllJSurvivalEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ) :
    MeasurableSet (upSourceAllJSurvivalEvent (rate := rate)
      rewards C_star C_h control0 alpha candidate i ell) := by
  apply MeasurableSet.iUnion
  intro q
  exact ReferenceGeneratedUpSourceCalendar.measurableSet_upSourceSurvivalEvent
    (rate := rate) rewards C_star C_h q control0 alpha candidate i ell

/-- The all-J union at ordinal zero is exactly the space partitioned by the
original selected-row index. -/
theorem upSourceAllJSurvivalEvent_zero_eq_univ
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) :
    upSourceAllJSurvivalEvent (rate := rate)
      rewards C_star C_h control0 alpha candidate i 0 = Set.univ := by
  ext z
  simp only [upSourceAllJSurvivalEvent, Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨ActualInitializationPhysicalStep.selectedRowIndex p z, rfl⟩

/-- Exact finite disjoint-union measure equality for the literal all-J event. -/
theorem upSourceAllJSurvivalEvent_measure_eq_sum
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (upSourceAllJSurvivalEvent (rate := rate)
          rewards C_star C_h control0 alpha candidate i ell) =
      ∑ q : Fin (M p), BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) := by
  classical
  change BootstrapPrivateRoundStreams.sourceInputLaw p
      (⋃ q : Fin (M p),
        ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) = _
  rw [measure_iUnion
    (upSourceSurvivalEvent_pairwiseDisjoint (rate := rate)
      rewards C_star C_h control0 alpha candidate i ell)
    (fun q => ReferenceGeneratedUpSourceCalendar.measurableSet_upSourceSurvivalEvent
      (rate := rate) rewards C_star C_h q control0 alpha candidate i ell), tsum_fintype]

/-- The original `J`-stratum masses sum to one under the source-input law. -/
theorem upSourceOriginalRowStrata_measure_sum_eq_one
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) :
    ∑ q : Fin (M p), BootstrapPrivateRoundStreams.sourceInputLaw p
      (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha candidate i 0) = 1 := by
  calc
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p
        (upSourceAllJSurvivalEvent (rate := rate)
          rewards C_star C_h control0 alpha candidate i 0) :=
      (upSourceAllJSurvivalEvent_measure_eq_sum (rate := rate)
        rewards C_star C_h control0 alpha candidate i 0).symm
    _ = BootstrapPrivateRoundStreams.sourceInputLaw p Set.univ := by
      rw [upSourceAllJSurvivalEvent_zero_eq_univ]
    _ = 1 := measure_univ

/-- Exact half-measure equality on the actual UP calendar: the disjoint union
of the current-hash-one constituents has half the measure of the disjoint
union of the corresponding unchecked attempt constituents. -/
theorem upSourceSurvivalEvent_measure_eq_half_attempt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hell : 1 ≤ ell) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) =
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
          rewards C_star C_h q control0 alpha ell candidate i) := by
  classical
  cases ell with
  | zero => omega
  | succ n =>
      let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
      have hhashDisjoint := ReferenceGeneratedUpSourceCalendar.upSourceHashOne_pairwiseDisjoint
        (rate := rate) rewards C_star C_h q control0 alpha (n + 1) candidate i
      have hpositiveDisjoint := ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent_pairwiseDisjoint
        (rate := rate) rewards C_star C_h q control0 alpha (n + 1) candidate i
      have hhashMeas : ∀ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
          MeasurableSet (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i) := by
        intro c
        exact measurableSet_actualUpPrefixPositiveHashOneSourceEvent
          rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
            control0 alpha (n + 1) candidate i
      have hpositiveMeas : ∀ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
          MeasurableSet (actualUpPrefixPositiveSourceEvent (rate := rate)
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i) := by
        intro c
        exact measurableSet_actualUpPrefixPositiveSourceEvent
          rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
            control0 alpha (n + 1) candidate i
      have hpositiveMeasure :
          μ (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
              rewards C_star C_h q control0 alpha (n + 1) candidate i) =
            ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
              μ (actualUpPrefixPositiveSourceEvent (rate := rate)
                rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                  control0 alpha (n + 1) candidate i) := by
        change μ (⋃ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
          actualUpPrefixPositiveSourceEvent (rate := rate)
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i) = _
        rw [measure_iUnion hpositiveDisjoint hpositiveMeas, tsum_fintype]
      calc
        μ (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha candidate i (n + 1)) =
            ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
              μ (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
                rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                  control0 alpha (n + 1) candidate i) := by
          change μ (⋃ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
            actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
              rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                control0 alpha (n + 1) candidate i) = _
          rw [measure_iUnion hhashDisjoint hhashMeas, tsum_fintype]
        _ = ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
              ((1 : ℝ≥0∞) / 2) *
                μ (actualUpPrefixPositiveSourceEvent (rate := rate)
                  rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                    control0 alpha (n + 1) candidate i) := by
          apply Finset.sum_congr rfl
          intro c _
          exact actualUpPrefixPositive_hash_half
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i
        _ = ((1 : ℝ≥0∞) / 2) *
              ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
                μ (actualUpPrefixPositiveSourceEvent (rate := rate)
                  rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                    control0 alpha (n + 1) candidate i) := by
          rw [← Finset.mul_sum]
        _ = ((1 : ℝ≥0∞) / 2) *
              μ (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
                rewards C_star C_h q control0 alpha (n + 1) candidate i) := by
          rw [hpositiveMeasure]

/-- The source-law calendar survival event satisfies the half recurrence. -/
theorem upSourceSurvivalEvent_measure_recurrence
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hell : 1 ≤ ell) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i (ell - 1)) := by
  have hhalf := upSourceSurvivalEvent_measure_eq_half_attempt
    (rate := rate) rewards C_star C_h q control0 alpha candidate i ell hell hellQ
  have hsubset :
      ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
        rewards C_star C_h q control0 alpha ell candidate i ⊆
      ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha candidate i (ell - 1) := by
    by_cases hfirst : ell = 1
    · subst ell
      exact ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent_one_subset_zero
        rewards C_star C_h q control0 alpha candidate i
    · exact ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent_subset_predecessor
        rewards C_star C_h q control0 alpha ell candidate i (by omega)
  calc
    _ = ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
            rewards C_star C_h q control0 alpha ell candidate i) := hhalf
    _ ≤ ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha candidate i (ell - 1)) :=
      mul_le_mul_of_nonneg_left (measure_mono hsubset) (by positivity)

/-- Iteration through the inclusive quota gives the geometric bound with the
actual original `J=q` stratum as the base event. -/
theorem upSourceSurvivalEvent_measure_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) ^ ell * BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i 0) := by
  induction ell with
  | zero => simp
  | succ n ih =>
      have hnQ : n ≤ AffineBatchDecoder.quota p := by omega
      have hrec := upSourceSurvivalEvent_measure_recurrence
        (rate := rate) rewards C_star C_h q control0 alpha candidate i (n + 1)
          (by omega) hellQ
      have hbound := ih hnQ
      calc
        _ ≤ ((1 : ℝ≥0∞) / 2) *
            BootstrapPrivateRoundStreams.sourceInputLaw p
              (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
                rewards C_star C_h q control0 alpha candidate i n) := hrec
        _ ≤ ((1 : ℝ≥0∞) / 2) *
            (((1 : ℝ≥0∞) / 2) ^ n * BootstrapPrivateRoundStreams.sourceInputLaw p
              (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
                rewards C_star C_h q control0 alpha candidate i 0)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = ((1 : ℝ≥0∞) / 2) ^ (n + 1) *
              BootstrapPrivateRoundStreams.sourceInputLaw p
                (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
                  rewards C_star C_h q control0 alpha candidate i 0) := by
          rw [pow_succ]
          ac_rfl

/-- Exact all-J calendar recurrence, assembled by finite disjoint-union
measure equalities at the current and preceding ordinals. -/
theorem upSourceAllJSurvivalEvent_measure_recurrence
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hell : 1 ≤ ell) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (upSourceAllJSurvivalEvent (rate := rate)
          rewards C_star C_h control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
        (upSourceAllJSurvivalEvent (rate := rate)
          rewards C_star C_h control0 alpha candidate i (ell - 1)) := by
  classical
  have hcurrent := upSourceAllJSurvivalEvent_measure_eq_sum
    (rate := rate) rewards C_star C_h control0 alpha candidate i ell
  have hprevious := upSourceAllJSurvivalEvent_measure_eq_sum
    (rate := rate) rewards C_star C_h control0 alpha candidate i (ell - 1)
  have hprevQ : ell - 1 ≤ AffineBatchDecoder.quota p := by omega
  calc
    _ = ∑ q : Fin (M p), BootstrapPrivateRoundStreams.sourceInputLaw p
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) := hcurrent
    _ ≤ ∑ q : Fin (M p), ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha candidate i (ell - 1)) := by
      apply Finset.sum_le_sum
      intro q _
      exact upSourceSurvivalEvent_measure_recurrence
        (rate := rate) rewards C_star C_h q control0 alpha candidate i ell hell hellQ
    _ = ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (upSourceAllJSurvivalEvent (rate := rate)
            rewards C_star C_h control0 alpha candidate i (ell - 1)) := by
      rw [← Finset.mul_sum, ← hprevious]

/-- The literal all-J union has the unconditional geometric tail. The base
mass is one because its zero strata partition the original selected-row law. -/
theorem upSourceAllJSurvivalEvent_measure_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (upSourceAllJSurvivalEvent (rate := rate)
          rewards C_star C_h control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) ^ ell := by
  induction ell with
  | zero =>
      rw [upSourceAllJSurvivalEvent_zero_eq_univ, measure_univ, pow_zero]
  | succ n ih =>
      have hnQ : n ≤ AffineBatchDecoder.quota p := by omega
      have hrec := upSourceAllJSurvivalEvent_measure_recurrence
        (rate := rate) rewards C_star C_h control0 alpha candidate i (n + 1)
          (by omega) hellQ
      have hbound := ih hnQ
      calc
        _ ≤ ((1 : ℝ≥0∞) / 2) * BootstrapPrivateRoundStreams.sourceInputLaw p
            (upSourceAllJSurvivalEvent (rate := rate)
              rewards C_star C_h control0 alpha candidate i n) := hrec
        _ ≤ ((1 : ℝ≥0∞) / 2) * ((1 : ℝ≥0∞) / 2) ^ n :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = ((1 : ℝ≥0∞) / 2) ^ (n + 1) := by
          rw [pow_succ]
          ac_rfl

end Bandits.Support.ReferenceGeneratedUpSourceTail

end
