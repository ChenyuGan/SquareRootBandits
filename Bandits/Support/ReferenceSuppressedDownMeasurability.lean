/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSuppressedDownTail
public import Bandits.Support.InitializationFailureProvenance
public import Bandits.Support.GeneratedBootstrapRoundLaw
import Bandits.Support.ReferenceInitializationMeasurability

/-!
# Measurability of the literal suppressed DOWN event

The literal prelaunch suppressed-DOWN event is measurable on the original
continuous complete-row and private-coordinate space. Its exact per-follower
history is characterized by the generated run's accumulated failure bit with
forced-correction bits kept separate.

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:724-735`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:111-155`,
`sources/zip4/manuscript/05_binary_transport.tex:7-53`,
`sources/zip4/manuscript/07_public_setup.tex:129-140`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.InitializationFailureProvenance
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceInitializationMeasurability
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open scoped Classical

namespace Bandits.Support.ReferenceSuppressedDownMeasurability

variable (p : ConstructorDimensions.Parameters) (ids : IDArray p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
  (C_star C_h : ℝ) (eta : LearningRate)

private def outputFailureCode
    (z : ReferenceInitializationMeasurability.InputCoordinates p)
    (i : Fin (p.m - 1)) : Bool × Bool :=
  let x := ReferenceInitializationMeasurability.inputOfCoordinates
    p C_star C_h eta rewards z
  let b := ReferenceInitializationRun.output x
  (ReferenceInitializationRun.initializationFailure x b i, b.forcedFailure i)

private theorem run_active_false_succ (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (i : ActiveRoundActions.Follower p.m) (a : Activation p)
    (ha : (ReferenceInitializationRun.run x r).activation i = some a)
    (hf : (ReferenceInitializationRun.run x r).forcedFailure i = false) :
    (ReferenceInitializationRun.run x (r + 1)).activation i = some a ∧
      (ReferenceInitializationRun.run x (r + 1)).forcedFailure i = false := by
  by_cases hc : (ReferenceInitializationRun.run x r).crossing.isSome = true
  · rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_crossing x _ hc]
    exact ⟨ha, hf⟩
  · have hnone : (ReferenceInitializationRun.run x r).crossing = none := by
      cases hcross : (ReferenceInitializationRun.run x r).crossing with
      | none => rfl
      | some c => simp [hcross] at hc
    by_cases hex : n_boot p ≤ (ReferenceInitializationRun.run x r).completed
    · rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_exhausted x _ hex]
      exact ⟨ha, hf⟩
    · have hblock : (ReferenceInitializationRun.run x r).completed < n_boot p :=
        Nat.lt_of_not_ge hex
      rw [ReferenceInitializationRun.run_succ,
        ReferenceInitializationRun.advance_of_no_crossing x _ hnone hblock]
      constructor
      · exact ReferenceInitializationRun.activated_activation x _ hblock i a ha
      · change ((ReferenceInitializationRun.run x r).forcedFailure i ||
          ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x r) hblock i) = false
        rw [hf, ReferenceInitializationRun.activated_not_forced x _ hblock i a ha]
        rfl

private theorem run_active_false_future (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (i : ActiveRoundActions.Follower p.m) (a : Activation p)
    (ha : (ReferenceInitializationRun.run x r).activation i = some a)
    (hf : (ReferenceInitializationRun.run x r).forcedFailure i = false) :
    ∀ k : ℕ,
      (ReferenceInitializationRun.run x (r + k)).activation i = some a ∧
        (ReferenceInitializationRun.run x (r + k)).forcedFailure i = false := by
  intro k
  induction k with
  | zero => simpa using And.intro ha hf
  | succ k ih =>
      simpa only [Nat.add_succ] using
        run_active_false_succ p x (r + k) i a ih.1 ih.2

private theorem forcedCorrectionAt_output_forced (x : ReferenceInitializationRun.Input p)
    (s : Fin (n_boot p)) (i : ActiveRoundActions.Follower p.m)
    (hcause : InitializationFailureProvenance.forcedCorrectionAt x s i) :
    (ReferenceInitializationRun.output x).forcedFailure i = true := by
  rcases hcause with ⟨h, hcross, _, _, _, _, hforce, hfinish⟩
  let b := ReferenceInitializationRun.run x s.val
  have hnone : b.crossing = none := by simpa [b] using hcross
  have hforced := (ReferenceInitializationRun.forced_iff x b h i).mp hforce
  have hnext : ReferenceInitializationRun.run x (s.val + 1) =
      ReferenceInitializationRun.finishBlock x b h := by
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x b hnone h]
  have hstop : (ReferenceInitializationRun.run x (s.val + 1)).crossing.isSome = true := by
    rw [hnext]
    change (if ReferenceInitializationRun.crosses x b h then
      some (ReferenceInitializationRun.nextBlock b h) else none).isSome = true
    simp [hforced.1]
  have hout := ReferenceInitializationRun.output_eq_of_crossing x (s.val + 1)
    (Nat.succ_le_of_lt s.isLt) hstop
  rw [hout, hnext]
  exact hfinish

/-- The accumulated failure bit is equivalent to a literal suppressed DOWN
witness precisely when no exceptional correction bit is set. This is proved
from the per-block recursion; it is not inferred from measurability of the
combined two-cause event. -/
theorem suppressedDown_before_iff_outputFailure (x : ReferenceInitializationRun.Input p)
    (i : ActiveRoundActions.Follower p.m) :
    (∃ s : Fin (n_boot p),
      InitializationFailureProvenance.suppressedDownAt x s i) ↔
      ReferenceInitializationRun.initializationFailure x
          (ReferenceInitializationRun.output x) i = true ∧
        (ReferenceInitializationRun.output x).forcedFailure i = false := by
  constructor
  · rintro ⟨s, hs⟩
    have hcauses : InitializationFailureProvenance.failureCausesBefore x
        (n_boot p) i := ⟨s, s.isLt, Or.inr hs⟩
    rcases hs with ⟨h, hcross, _, hforced, a, ha, d, hd, hdown, htime⟩
    have hfailure := (InitializationFailureProvenance.run_initializationFailure_iff_causesBefore
      x i (n_boot p) le_rfl).2 hcauses
    have hstable := run_active_false_future p x s.val i a ha hforced
      (n_boot p - s.val)
    have hindex : s.val + (n_boot p - s.val) = n_boot p :=
      Nat.add_sub_of_le (Nat.le_of_lt s.isLt)
    have hterminal : (ReferenceInitializationRun.output x).forcedFailure i = false := by
      change (ReferenceInitializationRun.run x (n_boot p)).forcedFailure i = false
      rw [← hindex]
      exact hstable.2
    exact ⟨by simpa [ReferenceInitializationRun.output] using hfailure, hterminal⟩
  · rintro ⟨hfailure, hforced⟩
    have hcauses :=
      (InitializationFailureProvenance.run_initializationFailure_iff_causesBefore
        x i (n_boot p) le_rfl).1 (by
          simpa [ReferenceInitializationRun.output] using hfailure)
    rcases hcauses with ⟨s, hs, hcause⟩
    rcases hcause with hcorrection | hdown
    · have hterminal := forcedCorrectionAt_output_forced p x s i hcorrection
      change (ReferenceInitializationRun.run x (n_boot p)).forcedFailure i = false at hforced
      have hterminal' : (ReferenceInitializationRun.run x (n_boot p)).forcedFailure i = true := by
        simpa [ReferenceInitializationRun.output] using hterminal
      rw [hterminal'] at hforced
      cases hforced
    · exact ⟨s, hdown⟩

private theorem measurable_outputFailureCode_at (i : Fin (p.m - 1)) :
    Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      outputFailureCode p rewards C_star C_h eta z i) := by
  have hfailure := ReferenceInitializationMeasurability.measurable_output_initializationFailure
    p C_star C_h eta rewards i
  have hforced : Measurable (fun z : ReferenceInitializationMeasurability.InputCoordinates p =>
      (ReferenceInitializationRun.output
        (ReferenceInitializationMeasurability.inputOfCoordinates
          p C_star C_h eta rewards z)).forcedFailure i) :=
    (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
      b.forcedFailure i)).comp
      (ReferenceInitializationMeasurability.measurable_output p C_star C_h eta rewards)
  simpa only [outputFailureCode] using hfailure.prodMk hforced

/-- For a fixed original follower, the union over its actual processed blocks
of suppressed DOWN decisions is measurable on the original coordinates. -/
theorem measurableSet_suppressedDownAt_follower (i : Fin (p.m - 1)) :
    MeasurableSet {e : GeneratedBootstrapRoundLaw.Coordinates p |
      ∃ s : Fin (n_boot p),
        InitializationFailureProvenance.suppressedDownAt
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s i} := by
  let f := fun e : GeneratedBootstrapRoundLaw.Coordinates p =>
    outputFailureCode p rewards C_star C_h eta (ids, e) i
  have hf : Measurable f :=
    (measurable_outputFailureCode_at p rewards C_star C_h eta i).comp
      (measurable_const.prodMk measurable_id)
  have hsingle : MeasurableSet ({(true, false)} : Set (Bool × Bool)) :=
    measurableSet_singleton _
  have hpre : MeasurableSet (f ⁻¹' {(true, false)}) := hf hsingle
  have hset :
      {e : GeneratedBootstrapRoundLaw.Coordinates p |
        ∃ s : Fin (n_boot p),
          InitializationFailureProvenance.suppressedDownAt
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s i} =
        f ⁻¹' {(true, false)} := by
    ext e
    change (∃ s : Fin (n_boot p),
        InitializationFailureProvenance.suppressedDownAt
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s i) ↔ _
    simpa only [Set.mem_preimage, Set.mem_singleton_iff,
      f, outputFailureCode, Prod.mk.injEq,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates] using
      suppressedDown_before_iff_outputFailure p
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) i
  rw [hset]
  exact hpre

/-- Ambient measurability of the unchanged literal event
`ReferenceSuppressedDownTail.E_down`, on the entire original coordinates. -/
theorem measurableSet_E_down :
    MeasurableSet (ReferenceSuppressedDownTail.E_down p ids rewards C_star C_h eta) := by
  have hset :
      ReferenceSuppressedDownTail.E_down p ids rewards C_star C_h eta =
        ⋃ i : Fin (p.m - 1), {e : GeneratedBootstrapRoundLaw.Coordinates p |
          ∃ s : Fin (n_boot p),
            InitializationFailureProvenance.suppressedDownAt
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s i} := by
    ext e
    change (∃ i : ActiveRoundActions.Follower p.m,
        ∃ s : Fin (n_boot p),
          InitializationFailureProvenance.suppressedDownAt
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s i) ↔ _
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    rfl
  rw [hset]
  exact MeasurableSet.iUnion fun i =>
    measurableSet_suppressedDownAt_follower p ids rewards C_star C_h eta i

end Bandits.Support.ReferenceSuppressedDownMeasurability

end
