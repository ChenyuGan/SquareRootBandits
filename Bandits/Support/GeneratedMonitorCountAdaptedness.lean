/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
public import Bandits.Support.GeneratedDownBlockBoundaryMean

/-!
# Adaptedness of the actual reference initialization DOWN count

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:640-683` and
`sources/zip4/manuscript/07_public_setup.tex:63-113`.

The block observable is the accepted `downBlockTest` on the original
complete-row/private-coordinate carrier. Its Nat-valued version is defined by
the increment of the accepted reference run's own cumulative counter. The
source clock observes block `s` at index `s.val + 1`. At time zero and after
the finite opportunity horizon the analytical process is zero; the final
opportunity remains present at time `n_boot p`.

Every factorization uses the literal `sourcePrefix`, which retains the
calendar, follower block profiles, coordinator target scalars, and original
player-round scalars through the requested boundary. The separate coordinator
`J` scalar stays excluded as in that accepted prefix. No transition, random
input, or physical run is added here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.GeneratedMonitorCountAdaptedness

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedDownBlockBoundaryMean

abbrev Parameters := ConstructorDimensions.Parameters

/-- The original complete-row/private-coordinate carrier of the accepted law. -/
abbrev Coordinates (p : Parameters) :=
  GeneratedBootstrapBlockFiltrationRepair.Coordinates p

variable {p : Parameters}

/-- The actual increment of the accepted reference run's cumulative arm
counter at opportunity `s`. -/
def referenceDownBlockCounterIncrementAt (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : ℕ) (a : Fin p.K)
    (e : Coordinates p) : ℕ :=
  (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      (s + 1)).counters a -
    (ReferenceInitializationRun.run
      (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
      s).counters a

/-- The Nat-valued DOWN count for one genuine reference opportunity, read
from the actual stopped run counter increment. -/
def referenceDownBlockCount (p : Parameters) (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p) : ℕ :=
  referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta s.val a e

/-- Source-clock version of the actual count: opportunity `s` is observed at
time `s.val + 1`. It is zero at time zero and after the finite horizon; the
last opportunity is retained because the horizon branch is `time ≤ n_boot p`. -/
def sourceShiftedDownBlockCount (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K)
    (e : Coordinates p) : ℕ :=
  if _hzero : time = 0 then 0
  else if _htime : time ≤ n_boot p then
    referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta (time - 1) a e
  else 0

/-- Measurable section of the original coordinate space over a literal source
prefix. Omitted coordinates are filled from the fixed original point only for
this factorization proof. -/
def sourceShiftedDownBlockCountFactor (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K)
    (e₀ : Coordinates p) :
    GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p time → ℕ := fun z =>
  if _hzero : time = 0 then 0
  else if _htime : time ≤ n_boot p then
    referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta (time - 1) a
      (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z)
  else 0

/-- A coordinate's actual counter is nondecreasing through one opportunity.
This follows from the accepted stop branch or the accepted cumulative update. -/
theorem referenceRun_counter_mono_succ (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (e : Coordinates p)
    (n : ℕ) (a : Fin p.K) :
    (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) n).counters a ≤
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) (n + 1)).counters a := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  by_cases hc : (ReferenceInitializationRun.run x n).crossing.isSome = true
  · rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_crossing x _ hc]
  · have hnone : (ReferenceInitializationRun.run x n).crossing = none := by
      cases he : (ReferenceInitializationRun.run x n).crossing <;>
        simp_all only [Option.isSome_some, Option.isSome_none, not_true_eq_false]
    by_cases h : (ReferenceInitializationRun.run x n).completed < n_boot p
    · rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_no_crossing x _ hnone h]
      change (ReferenceInitializationRun.run x n).counters a ≤
        ReferenceInitializationRun.updatedCounters x (ReferenceInitializationRun.run x n) h a
      unfold ReferenceInitializationRun.updatedCounters
      exact Nat.le_add_right _ _
    · rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_exhausted x _ (Nat.le_of_not_gt h)]

/-- Casting the actual Nat increment gives the real difference of the same
two cumulative reference counters. -/
theorem cast_referenceDownBlockCounterIncrementAt (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : ℕ) (a : Fin p.K)
    (e : Coordinates p) :
    ((referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta s a e : ℕ) : ℝ) =
      (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) (s + 1)).counters a -
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s).counters a := by
  unfold referenceDownBlockCounterIncrementAt
  rw [Nat.cast_sub (referenceRun_counter_mono_succ p ids rewards C_star C_h eta e s a)]

/-- The accepted real block test is exactly the real counter increment. This
uses the accepted history-count and counter-update identities on an active
boundary, and the accepted zero test and frozen run on an already-stopped
boundary. The first crossing block remains in the active-boundary case. -/
theorem downBlockTest_eq_referenceCounterIncrement (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p) :
    GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta s a e =
      ((referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta s.val a e : ℕ) : ℝ) := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  by_cases hstopped : (ReferenceInitializationRun.run x s.val).crossing ≠ none
  · have hc : (ReferenceInitializationRun.run x s.val).crossing.isSome = true := by
      cases h : (ReferenceInitializationRun.run x s.val).crossing <;> simp_all
    rw [GeneratedDownBlockBoundaryMean.downBlockTest_eq_zero_when_stopped
      ids rewards C_star C_h eta s a e hstopped]
    simp [referenceDownBlockCounterIncrementAt, x,
      ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_crossing x _ hc]
  · have hnone : (ReferenceInitializationRun.run x s.val).crossing = none := by
      cases h : (ReferenceInitializationRun.run x s.val).crossing <;> simp_all
    have hprogress := ReferenceInitializationRun.run_progress x s.val
      (Nat.le_of_lt s.isLt)
    have hnotSome :
        ¬ (ReferenceInitializationRun.run x s.val).crossing.isSome = true := by
      intro hsome
      apply hstopped
      cases hc : (ReferenceInitializationRun.run x s.val).crossing <;>
        simp_all
    have hcompleted : (ReferenceInitializationRun.run x s.val).completed = s.val :=
      hprogress.resolve_left hnotSome
    let b := ReferenceInitializationRun.run x s.val
    have hb : GeneratedBlockStartLaw.boundaryAtOriginal p s ids rewards C_star C_h eta e = b := rfl
    have hcount := GeneratedDownBlockBoundaryMean.downBlockTest_eq_historyBlockCount_on_boundary
      ids rewards C_star C_h eta s a b hcompleted hnone e hb
    have hblock : b.completed < n_boot p := by rw [hcompleted]; exact s.isLt
    have hnext : ReferenceInitializationRun.run x (s.val + 1) =
        ReferenceInitializationRun.finishBlock x b hblock := by
      rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_no_crossing x b hnone hblock]
    have hupdated := GeneratedDownBlockBoundaryMean.updatedCounters_eq_old_add_historyBlockCount
      ids rewards C_star C_h eta s a b hcompleted hnone e hb
    have hnextCounter :
        (ReferenceInitializationRun.run x (s.val + 1)).counters a =
          b.counters a + GeneratedBootstrapMonitor.historyBlockCount x
            (ReferenceInitializationRun.elapsed p (b.completed + 1))
            (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
            (ReferenceInitializationRun.extendedHistory x b hblock
              (ActiveRoundActions.coordinator p.two_le_m))
            (ReferenceInitializationRun.nextBlock b hblock)
            (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd b hblock]) a := by
      rw [hnext]
      change ReferenceInitializationRun.updatedCounters x b hblock a = _
      exact hupdated
    rw [hcount]
    change ((GeneratedBootstrapMonitor.historyBlockCount x
        (ReferenceInitializationRun.elapsed p (b.completed + 1))
        (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
        (ReferenceInitializationRun.extendedHistory x b hblock
          (ActiveRoundActions.coordinator p.two_le_m))
        (ReferenceInitializationRun.nextBlock b hblock)
        (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd b hblock]) a : ℕ) : ℝ) = _
    have hincNat : referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta
        s.val a e = GeneratedBootstrapMonitor.historyBlockCount x
          (ReferenceInitializationRun.elapsed p (b.completed + 1))
          (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))
          (ReferenceInitializationRun.extendedHistory x b hblock
            (ActiveRoundActions.coordinator p.two_le_m))
          (ReferenceInitializationRun.nextBlock b hblock)
          (by rw [← ReferenceInitializationRun.elapsed_succ_eq_blockEnd b hblock]) a := by
      change (ReferenceInitializationRun.run x (s.val + 1)).counters a -
          (ReferenceInitializationRun.run x s.val).counters a = _
      rw [hnextCounter]
      change (b.counters a + _) - b.counters a = _
      exact Nat.add_sub_cancel_left _ _
    rw [hincNat]

/-- Pointwise equality of the accepted DOWN block test with the actual real
difference of the same reference run's cumulative counters. -/
theorem downBlockTest_eq_realCounterDifference (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p) :
    GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta s a e =
      (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) (s.val + 1)).counters a -
        (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) s.val).counters a := by
  calc
    _ = ((referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta
        s.val a e : ℕ) : ℝ) :=
      downBlockTest_eq_referenceCounterIncrement p ids rewards C_star C_h eta s a e
    _ = _ := cast_referenceDownBlockCounterIncrementAt
      p ids rewards C_star C_h eta s.val a e

/-- A block count is bounded by its genuine clipped calendar block length. -/
theorem referenceDownBlockCount_le_B_boot (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p) :
    referenceDownBlockCount p ids rewards C_star C_h eta s a e ≤ B_boot p := by
  have htest := downBlockTest_eq_referenceCounterIncrement p ids rewards C_star C_h eta s a e
  have hbound := GeneratedDownBlockBoundaryMean.downBlockTest_nonneg_le_boot
    ids rewards C_star C_h eta s a e
  have hcast :
      (referenceDownBlockCount p ids rewards C_star C_h eta s a e : ℝ) ≤ B_boot p := by
    rw [referenceDownBlockCount, ← htest]
    exact hbound.2
  exact_mod_cast hcast

/-- The finite source-shifted process takes the actual run-counter increment
at times `1` through `n_boot`, including the shortened final block. -/
theorem sourceShiftedDownBlockCount_succ_eq_increment (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (n : ℕ)
    (hn : n < n_boot p) (a : Fin p.K) (e : Coordinates p) :
    sourceShiftedDownBlockCount p ids rewards C_star C_h eta (n + 1) a e =
      referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta n a e := by
  have hzero : n + 1 ≠ 0 := by omega
  have htime : n + 1 ≤ n_boot p := Nat.succ_le_iff.mpr hn
  simp [sourceShiftedDownBlockCount, htime]

/-- Measurable factor on a fixed source-prefix carrier. Its two boundary
values are measurable by the accepted reference-run measurability theorem
after applying the accepted measurable completion section. -/
theorem measurable_sourceShiftedDownBlockCountFactor (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K)
    (e₀ : Coordinates p) :
    Measurable (sourceShiftedDownBlockCountFactor p ids rewards C_star C_h eta time a e₀) := by
  by_cases hzero : time = 0
  · subst time
    change Measurable (fun _ : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p 0 => 0)
    exact measurable_const
  · by_cases htime : time ≤ n_boot p
    · unfold sourceShiftedDownBlockCountFactor
      simp only [hzero, htime, dite_false, dite_true]
      have hnow : Measurable (fun z : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p time =>
          ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
              (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z)) time) := by
        change Measurable (fun z => ReferenceInitializationRun.run
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
            (ids, GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z)) time)
        exact (ReferenceInitializationMeasurability.measurable_run
          p C_star C_h eta rewards time).comp
          (measurable_const.prodMk
            (GeneratedBootstrapBlockFiltrationRepair.measurable_completeSourcePrefix p time e₀))
      have hbefore : Measurable
          (fun z : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p time =>
            ReferenceInitializationRun.run
              (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta
                (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z))
              (time - 1)) := by
        change Measurable (fun z => ReferenceInitializationRun.run
          (ReferenceInitializationMeasurability.inputOfCoordinates p C_star C_h eta rewards
            (ids, GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z))
          (time - 1))
        exact (ReferenceInitializationMeasurability.measurable_run
          p C_star C_h eta rewards (time - 1)).comp
          (measurable_const.prodMk
            (GeneratedBootstrapBlockFiltrationRepair.measurable_completeSourcePrefix p time e₀))
      have hadd : time - 1 + 1 = time := Nat.sub_add_cancel (by omega)
      let difference : ReferenceInitializationRun.Boundary p ×
          ReferenceInitializationRun.Boundary p → ℕ :=
        fun z => z.1.counters a - z.2.counters a
      let runPair : GeneratedBootstrapBlockFiltrationRepair.SourcePrefix p time →
          ReferenceInitializationRun.Boundary p × ReferenceInitializationRun.Boundary p :=
        fun z =>
          (ReferenceInitializationRun.run
              (GeneratedBootstrapBlockFiltrationRepair.referenceInput
                p ids rewards C_star C_h eta
                (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z)) time,
            ReferenceInitializationRun.run
              (GeneratedBootstrapBlockFiltrationRepair.referenceInput
                p ids rewards C_star C_h eta
                (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀ z))
              (time - 1))
      have hcomp : Measurable (difference ∘ runPair) := by
        exact (measurable_of_countable difference).comp (hnow.prodMk hbefore)
      convert hcomp using 1
      funext z
      simp [difference, runPair, referenceDownBlockCounterIncrementAt, hadd]
    · unfold sourceShiftedDownBlockCountFactor
      simp only [hzero, htime, dite_false]
      exact measurable_const

/-- The full source-shifted count process factors through the literal prefix
at its own time. The zero branches use only the permitted stopped analytical
extension; on a live opportunity, the previous boundary is obtained by
restricting the exact current source prefix. -/
theorem sourceShiftedDownBlockCount_eq_sourcePrefixFactor (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K)
    (e₀ e : Coordinates p) :
    sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a e =
      sourceShiftedDownBlockCountFactor p ids rewards C_star C_h eta time a e₀
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time e) := by
  by_cases hzero : time = 0
  · simp [sourceShiftedDownBlockCount, sourceShiftedDownBlockCountFactor, hzero]
  · by_cases htime : time ≤ n_boot p
    · have hfull := GeneratedBootstrapBlockFiltrationRepair.sourcePrefix_completeSourcePrefix
        p time e₀ (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time e)
      have hprevRaw := congrArg
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict p (time - 1) time
          (Nat.sub_le time 1)) hfull
      have hprev :
          GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (time - 1)
              (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀
                (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time e)) =
            GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (time - 1) e := by
        simpa only [GeneratedBootstrapBlockFiltrationRepair.sourcePrefixRestrict_sourcePrefix]
          using hprevRaw
      have hnow := GeneratedBootstrapBlockFiltrationRepair.run_eq_of_sourcePrefix_eq
        p time ids rewards C_star C_h eta e
        (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀
          (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time e)) hfull.symm
      have hbefore := GeneratedBootstrapBlockFiltrationRepair.run_eq_of_sourcePrefix_eq
        p (time - 1) ids rewards C_star C_h eta
        (GeneratedBootstrapBlockFiltrationRepair.completeSourcePrefix p time e₀
          (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time e)) e hprev
      have hadd : time - 1 + 1 = time := Nat.sub_add_cancel (by omega)
      simp only [sourceShiftedDownBlockCount, sourceShiftedDownBlockCountFactor,
        dite_eq_right hzero, dite_eq_left htime]
      dsimp [referenceDownBlockCounterIncrementAt]
      rw [hadd, hnow, hbefore]
    · simp [sourceShiftedDownBlockCount, sourceShiftedDownBlockCountFactor, hzero, htime]

/-- The individual genuine block count factors through exactly the prefix
available at its source-shifted observation time `s.val + 1`. -/
theorem referenceDownBlockCount_eq_sourcePrefixFactor (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e₀ e : Coordinates p) :
    referenceDownBlockCount p ids rewards C_star C_h eta s a e =
      sourceShiftedDownBlockCountFactor p ids rewards C_star C_h eta (s.val + 1) a e₀
        (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p (s.val + 1) e) := by
  have h := sourceShiftedDownBlockCount_eq_sourcePrefixFactor p ids rewards C_star C_h eta
    (s.val + 1) a e₀ e
  simpa [sourceShiftedDownBlockCount, referenceDownBlockCount,
    Nat.succ_ne_zero, Nat.succ_sub_one, Nat.succ_le_of_lt s.isLt] using h

/-- At each source time the Nat-valued process is measurable in the exact
accepted boundary filtration. The proof is an explicit source-prefix factor,
not an analysis-past or side-past factor. -/
theorem measurable_sourceShiftedDownBlockCount_at_boundary (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K) :
    @Measurable (Coordinates p) ℕ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p time) inferInstance
      (sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a) := by
  let e₀ : Coordinates p := Classical.choice
    (MeasureTheory.nonempty_of_isProbabilityMeasure
      (GeneratedBootstrapRoundLaw.originalLaw p))
  have hfactor :
      (sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a) =
        sourceShiftedDownBlockCountFactor p ids rewards C_star C_h eta time a e₀ ∘
          GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time := by
    funext e
    exact sourceShiftedDownBlockCount_eq_sourcePrefixFactor
      p ids rewards C_star C_h eta time a e₀ e
  let _ : MeasurableSpace (Coordinates p) :=
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p time
  have hsource : Measurable
      (GeneratedBootstrapBlockFiltrationRepair.sourcePrefix p time) :=
    comap_measurable _
  rw [hfactor]
  exact (measurable_sourceShiftedDownBlockCountFactor
    p ids rewards C_star C_h eta time a e₀).comp hsource

/-- Mathlib's strongly adapted Nat process on the same accepted source-prefix
boundary filtration. -/
theorem sourceShiftedDownBlockCount_stronglyAdapted (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    StronglyAdapted (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (sourceShiftedDownBlockCount p ids rewards C_star C_h eta · a) := by
  intro time
  exact (measurable_sourceShiftedDownBlockCount_at_boundary
    p ids rewards C_star C_h eta time a).stronglyMeasurable

/-- The ordinary Mathlib adaptedness consequence for the source-shifted Nat
count process. -/
theorem sourceShiftedDownBlockCount_adapted (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    Adapted (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (sourceShiftedDownBlockCount p ids rewards C_star C_h eta · a) :=
  (sourceShiftedDownBlockCount_stronglyAdapted p ids rewards C_star C_h eta a).adapted

/-- The accepted real `downBlockTest` itself is measurable at the source
boundary `s.val + 1`. The proof identifies it with the cast of the actual
reference-counter increment, then uses the literal source-prefix factor above. -/
theorem measurable_downBlockTest_at_boundary (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) :
    @Measurable (Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)) inferInstance
      (GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta s a) := by
  let _ : MeasurableSpace (Coordinates p) :=
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p (s.val + 1)
  have hcount := measurable_sourceShiftedDownBlockCount_at_boundary
    p ids rewards C_star C_h eta (s.val + 1) a
  have hcast : Measurable (fun e : Coordinates p =>
      (sourceShiftedDownBlockCount p ids rewards C_star C_h eta
        (s.val + 1) a e : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hcount
  have hEq :
      (GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta s a) =
        (fun e : Coordinates p =>
          (sourceShiftedDownBlockCount p ids rewards C_star C_h eta
            (s.val + 1) a e : ℝ)) := by
    funext e
    rw [sourceShiftedDownBlockCount_succ_eq_increment
      p ids rewards C_star C_h eta s.val s.isLt a e]
    exact downBlockTest_eq_referenceCounterIncrement p ids rewards C_star C_h eta s a e
  rw [hEq]
  exact hcast

/-- Original complete-coordinate-law measurability of the accepted real
`downBlockTest` at its source-shifted boundary. -/
theorem measurable_downBlockTest_originalLaw (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) :
    Measurable (GeneratedDownBlockBoundaryMean.downBlockTest
      p ids rewards C_star C_h eta s a) := by
  have h := measurable_downBlockTest_at_boundary p ids rewards C_star C_h eta s a
  exact h.mono
    (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient
      p (s.val + 1)) le_rfl

/-- Integrability of the accepted real `downBlockTest` under the original
complete-row/private-coordinate law, using its accepted `[0, B_boot]` bound. -/
theorem integrable_downBlockTest_originalLaw (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) :
    Integrable (GeneratedDownBlockBoundaryMean.downBlockTest
      p ids rewards C_star C_h eta s a) (GeneratedBootstrapRoundLaw.originalLaw p) := by
  apply Integrable.of_mem_Icc 0 (B_boot p)
  · exact (measurable_downBlockTest_originalLaw p ids rewards C_star C_h eta s a).aemeasurable
  · exact MeasureTheory.ae_of_all _ fun e =>
      GeneratedDownBlockBoundaryMean.downBlockTest_nonneg_le_boot
        ids rewards C_star C_h eta s a e

/-- The source-shifted actual DOWN count normalized by the genuine maximum
calendar block length. -/
def sourceShiftedDownBlockTest (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K)
    (e : Coordinates p) : ℝ :=
  (sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a e : ℝ) /
    (B_boot p : ℝ)

/-- At source time `s.val + 1`, the normalized Nat process is literally the
accepted generated `downBlockTest` divided by `B_boot`. -/
theorem sourceShiftedDownBlockTest_at_block (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (s : Fin (n_boot p))
    (a : Fin p.K) (e : Coordinates p) :
    sourceShiftedDownBlockTest p ids rewards C_star C_h eta (s.val + 1) a e =
      GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta s a e /
        (B_boot p : ℝ) := by
  have hshift := sourceShiftedDownBlockCount_succ_eq_increment p ids rewards C_star C_h eta
    s.val s.isLt a e
  have htest := downBlockTest_eq_referenceCounterIncrement p ids rewards C_star C_h eta s a e
  unfold sourceShiftedDownBlockTest
  rw [hshift, htest]

/-- Every normalized source-shifted count lies in the unit interval. The
finite opportunity bound is the accepted bound for `downBlockTest`; extension
times are exactly zero. -/
theorem sourceShiftedDownBlockTest_mem_unitInterval (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ)
    (a : Fin p.K) (e : Coordinates p) :
    sourceShiftedDownBlockTest p ids rewards C_star C_h eta time a e ∈ Set.Icc 0 1 := by
  by_cases hzero : time = 0
  · simp [sourceShiftedDownBlockTest, sourceShiftedDownBlockCount, hzero]
  · by_cases htime : time ≤ n_boot p
    · have hidx : time - 1 < n_boot p := by omega
      let s : Fin (n_boot p) := ⟨time - 1, hidx⟩
      have hcount :
          sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a e =
            referenceDownBlockCounterIncrementAt p ids rewards C_star C_h eta
              s.val a e := by
        simp [sourceShiftedDownBlockCount, hzero, htime, s]
      have htest := downBlockTest_eq_referenceCounterIncrement
        p ids rewards C_star C_h eta s a e
      have htest' :
          GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta s a e =
            (sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a e : ℝ) := by
        rw [hcount]
        exact htest
      have hbound := GeneratedDownBlockBoundaryMean.downBlockTest_nonneg_le_boot
        ids rewards C_star C_h eta s a e
      rw [sourceShiftedDownBlockTest, ← htest']
      have hB : 0 < (B_boot p : ℝ) := by exact_mod_cast B_boot_pos p
      simp only [Set.mem_Icc]
      constructor
      · exact div_nonneg hbound.1 (le_of_lt hB)
      · exact (div_le_one hB).2 hbound.2
    · simp [sourceShiftedDownBlockTest, sourceShiftedDownBlockCount,
        hzero, htime]

/-- Measurability of the normalized process in the exact same boundary
filtration as its Nat-valued source. -/
theorem measurable_sourceShiftedDownBlockTest_at_boundary (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K) :
    @Measurable (Coordinates p) ℝ
      (GeneratedBootstrapBlockFiltrationRepair.boundarySigma p time) inferInstance
      (sourceShiftedDownBlockTest p ids rewards C_star C_h eta time a) := by
  let _ : MeasurableSpace (Coordinates p) :=
    GeneratedBootstrapBlockFiltrationRepair.boundarySigma p time
  have hcount := measurable_sourceShiftedDownBlockCount_at_boundary
    p ids rewards C_star C_h eta time a
  have hcast : Measurable (fun e : Coordinates p =>
      (sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a e : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hcount
  change Measurable (fun e =>
    (sourceShiftedDownBlockCount p ids rewards C_star C_h eta time a e : ℝ) /
      (B_boot p : ℝ))
  exact hcast.div_const _

/-- Mathlib's strongly adapted normalized process on the accepted boundary
filtration. -/
theorem sourceShiftedDownBlockTest_stronglyAdapted (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    StronglyAdapted (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (sourceShiftedDownBlockTest p ids rewards C_star C_h eta · a) := by
  intro time
  exact (measurable_sourceShiftedDownBlockTest_at_boundary
    p ids rewards C_star C_h eta time a).stronglyMeasurable

/-- Mathlib adaptedness of the normalized actual DOWN count. -/
theorem sourceShiftedDownBlockTest_adapted (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (a : Fin p.K) :
    Adapted (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration p)
      (sourceShiftedDownBlockTest p ids rewards C_star C_h eta · a) :=
  (sourceShiftedDownBlockTest_stronglyAdapted p ids rewards C_star C_h eta a).adapted

/-- Original-law measurability of the normalized source-shifted process. -/
theorem measurable_sourceShiftedDownBlockTest_originalLaw (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K) :
    Measurable (sourceShiftedDownBlockTest p ids rewards C_star C_h eta time a) := by
  have h := measurable_sourceShiftedDownBlockTest_at_boundary
    p ids rewards C_star C_h eta time a
  exact h.mono
    (GeneratedBootstrapBlockFiltrationRepair.boundaryFiltration_le_ambient p time) le_rfl

/-- Integrability under the same original complete-row/private-coordinate law.
It follows from original-law measurability and the proved unit bound. -/
theorem integrable_sourceShiftedDownBlockTest_originalLaw (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (time : ℕ) (a : Fin p.K) :
    Integrable (sourceShiftedDownBlockTest p ids rewards C_star C_h eta time a)
      (GeneratedBootstrapRoundLaw.originalLaw p) := by
  apply Integrable.of_mem_Icc 0 1
  · exact (measurable_sourceShiftedDownBlockTest_originalLaw
      p ids rewards C_star C_h eta time a).aemeasurable
  · exact MeasureTheory.ae_of_all _ fun e =>
      sourceShiftedDownBlockTest_mem_unitInterval p ids rewards C_star C_h eta time a e

/-- Exact Nat finite-prefix identity for every prefix ending by the final
opportunity. Summation is over blocks `0 ≤ s < r`, observed at source times
`s.val + 1`; it equals the same accepted run's zero-based counter. -/
theorem sourceShiftedDownBlockCount_sum_eq_counter (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (r : ℕ)
    (hr : r ≤ n_boot p) (a : Fin p.K) (e : Coordinates p) :
    (∑ s : Fin r,
      sourceShiftedDownBlockCount p ids rewards C_star C_h eta (s.val + 1) a e) =
      (ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) r).counters a := by
  let x := GeneratedBootstrapBlockFiltrationRepair.referenceInput
    p ids rewards C_star C_h eta e
  let f : ℕ → ℝ := fun n => (ReferenceInitializationRun.run x n).counters a
  have hcast :
      ((∑ s : Fin r,
        sourceShiftedDownBlockCount p ids rewards C_star C_h eta (s.val + 1) a e : ℕ) : ℝ) = f r := by
    rw [Nat.cast_sum, Finset.sum_fin_eq_sum_range]
    calc
      (∑ i ∈ Finset.range r,
          if hi : i < r then
            (sourceShiftedDownBlockCount p ids rewards C_star C_h eta
              ((⟨i, hi⟩ : Fin r).val + 1) a e : ℝ) else 0) =
        ∑ i ∈ Finset.range r, (f (i + 1) - f i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < r := Finset.mem_range.mp hi
          have hiBoot : i < n_boot p := Nat.lt_of_lt_of_le hi' hr
          simp only [dite_eq_left hi']
          rw [sourceShiftedDownBlockCount_succ_eq_increment
            p ids rewards C_star C_h eta i hiBoot a e,
            cast_referenceDownBlockCounterIncrementAt]
      _ = f r := by
        have htel := Finset.eq_sum_range_sub f r
        have hf0 : f 0 = 0 := by
          simp [f, x, GeneratedBootstrapBlockFiltrationRepair.referenceInput,
            ReferenceInitializationRun.run_zero, ReferenceInitializationRun.initial]
        rw [htel, hf0, zero_add]
  exact Nat.cast_injective hcast

/-- The finite-prefix Nat sum also equals the exact accepted stopped-block
history sum. This explicitly consumes the generated-monitor decomposition of
the cumulative counter; no independent count/history identity is assumed. -/
theorem sourceShiftedDownBlockCount_sum_eq_stoppedBlockSum (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (r : ℕ)
    (hr : r ≤ n_boot p) (a : Fin p.K) (e : Coordinates p) :
    (∑ s : Fin r,
      sourceShiftedDownBlockCount p ids rewards C_star C_h eta (s.val + 1) a e) =
      ∑ s : Fin (ReferenceInitializationRun.run
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e) r).completed,
        GeneratedBootstrapMonitor.runBlockCount
          (GeneratedBootstrapBlockFiltrationRepair.referenceInput
            p ids rewards C_star C_h eta e)
          (ReferenceInitializationRun.run
            (GeneratedBootstrapBlockFiltrationRepair.referenceInput
              p ids rewards C_star C_h eta e) r) s a := by
  rw [sourceShiftedDownBlockCount_sum_eq_counter p ids rewards C_star C_h eta r hr a e]
  exact GeneratedBootstrapMonitor.run_counters_eq_stoppedBlockSum
    (GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e)
    r a

/-- Exact real finite-prefix sum of the accepted DOWN block tests equals the
same reference run counter, through every boundary `r ≤ n_boot p`. -/
theorem downBlockTest_sum_eq_counter (p : Parameters)
    (ids : CompletePublicTable.IDArray p)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (C_star C_h : ℝ)
    (eta : ReferencePrelaunchFollower.LearningRate) (r : ℕ)
    (hr : r ≤ n_boot p) (a : Fin p.K) (e : Coordinates p) :
    (∑ s : Fin r,
      GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta
        ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩ a e) =
      ((ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) r).counters a : ℝ) := by
  calc
    _ = ∑ s : Fin r,
        (sourceShiftedDownBlockCount p ids rewards C_star C_h eta (s.val + 1) a e : ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      let sb : Fin (n_boot p) := ⟨s.val, Nat.lt_of_lt_of_le s.isLt hr⟩
      have hinc := sourceShiftedDownBlockCount_succ_eq_increment
        p ids rewards C_star C_h eta sb.val sb.isLt a e
      have htest := downBlockTest_eq_referenceCounterIncrement
        p ids rewards C_star C_h eta sb a e
      change GeneratedDownBlockBoundaryMean.downBlockTest p ids rewards C_star C_h eta sb a e =
        (sourceShiftedDownBlockCount p ids rewards C_star C_h eta (sb.val + 1) a e : ℝ)
      rw [hinc]
      exact htest
    _ = ((∑ s : Fin r,
          sourceShiftedDownBlockCount p ids rewards C_star C_h eta (s.val + 1) a e : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    _ = ((ReferenceInitializationRun.run
        (GeneratedBootstrapBlockFiltrationRepair.referenceInput
          p ids rewards C_star C_h eta e) r).counters a : ℝ) := by
      exact congrArg Nat.cast
        (sourceShiftedDownBlockCount_sum_eq_counter p ids rewards C_star C_h eta r hr a e)

end Bandits.Support.GeneratedMonitorCountAdaptedness

end
