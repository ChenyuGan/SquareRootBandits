/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ReferenceInitializationOriginLocality

/-!
# Stopped past locality for original-source reference initialization

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-164`,
`sources/zip4/manuscript/06_interruptions.tex:376-423`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

These deterministic results compare the existing corrected reference on its
original source inputs. A computed strict crossing makes the stopped output
local to reads before its generated elapsed boundary. At a calendar boundary,
the literal stopped-crossing event is itself determined by the strict past.
No source law, Borel claim, good-domain restriction, or manuscript closure is
asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.InitializationFailureProvenance
open scoped Classical

namespace Bandits.Support.ReferenceInitializationStoppedLocality

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

private theorem selectedIndex_eq_of_private_eq
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (hprivate : source.2 = source'.2) :
    ActualInitializationPhysicalStep.selectedRowIndex p source =
      ActualInitializationPhysicalStep.selectedRowIndex p source' := by
  change PrivateSourceStreams.coordinatorIndex p source.2.1.2 =
    PrivateSourceStreams.coordinatorIndex p source'.2.1.2
  rw [hprivate]

/-- A computed crossing of the original-source run fixes its genuine stopped
output from strict-past selected-row reads. The complete generated boundary,
ordinary follower states, and both operational failure causes are retained. -/
theorem source_stopped_output_eq_of_crossing
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ t : Fin p.T,
      t.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t)
    (hcontrol : ∀ t : Fin p.T,
      t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t)
    (hcross : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      r).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
    ReferenceInitializationRun.run x r = ReferenceInitializationRun.run y r ∧
    ReferenceInitializationRun.output x = ReferenceInitializationRun.output y ∧
    ReferenceInitializationRun.launchRound x = ReferenceInitializationRun.launchRound y ∧
    (ReferenceInitializationRun.output x).completed =
      (ReferenceInitializationRun.output y).completed ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) i =
        ReferenceInitializationRun.ordinary y (ReferenceInitializationRun.output y) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.output x) i =
      ReferenceInitializationRun.initializationFailure y
        (ReferenceInitializationRun.output y) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).forcedFailure i =
        (ReferenceInitializationRun.output y).forcedFailure i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).activation i =
        (ReferenceInitializationRun.output y).activation i) ∧
    (InitializationFailureProvenance.operationalInitializationFailure x ↔
      InitializationFailureProvenance.operationalInitializationFailure y) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
  have hboundary := ReferenceInitializationOriginLocality.source_run_boundary_eq
    rate rewards C_star C_h source source' r hids hprivate hforward hcontrol
  have hcross' : (ReferenceInitializationRun.run y r).crossing.isSome = true := by
    rw [← hboundary]
    exact hcross
  have hordinary := ReferenceInitializationOriginLocality.source_run_ordinary_eq
    rate rewards C_star C_h source source' r hids hprivate hforward hcontrol
  have hfailure := ReferenceInitializationOriginLocality.source_run_failure_eq
    rate rewards C_star C_h source source' r hr hids hprivate hforward hcontrol
  have houtputX : ReferenceInitializationRun.output x =
      ReferenceInitializationRun.run x r :=
    ReferenceInitializationRun.output_eq_of_crossing x r hr hcross
  have houtputY : ReferenceInitializationRun.output y =
      ReferenceInitializationRun.run y r :=
    ReferenceInitializationRun.output_eq_of_crossing y r hr hcross'
  have houtput := houtputX.trans (hboundary.trans houtputY.symm)
  have hordinaryOutput : ∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) i =
        ReferenceInitializationRun.ordinary y (ReferenceInitializationRun.output y) i := by
    intro i
    rw [houtputX, houtputY]
    simpa only [x, y] using hordinary i
  have hfailureOutput : ∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure x
          (ReferenceInitializationRun.output x) i =
        ReferenceInitializationRun.initializationFailure y
          (ReferenceInitializationRun.output y) i := by
    intro i
    calc
      ReferenceInitializationRun.initializationFailure x
          (ReferenceInitializationRun.output x) i =
          ReferenceInitializationRun.initializationFailure x
            (ReferenceInitializationRun.run x r) i := by rw [houtputX]
      _ = ReferenceInitializationRun.initializationFailure y
            (ReferenceInitializationRun.run y r) i := hfailure.1 i
      _ = ReferenceInitializationRun.initializationFailure y
            (ReferenceInitializationRun.output y) i := by rw [← houtputY]
  have hforced : ∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).forcedFailure i =
        (ReferenceInitializationRun.output y).forcedFailure i := by
    intro i
    exact congrArg (fun b : ReferenceInitializationRun.Boundary p => b.forcedFailure i)
      houtput
  have hactivation : ∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).activation i =
        (ReferenceInitializationRun.output y).activation i := by
    intro i
    exact congrArg (fun b : ReferenceInitializationRun.Boundary p => b.activation i)
      houtput
  have hany :
      (∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure x
          (ReferenceInitializationRun.output x) i = true) ↔
      (∃ i : ActiveRoundActions.Follower p.m,
        ReferenceInitializationRun.initializationFailure y
          (ReferenceInitializationRun.output y) i = true) := by
    constructor
    · rintro ⟨i, hi⟩
      rw [hfailureOutput i] at hi
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      rw [← hfailureOutput i] at hi
      exact ⟨i, hi⟩
  have hoper :=
    (InitializationFailureProvenance.initializationFailure_iff_operational x).symm.trans
      (hany.trans
        (InitializationFailureProvenance.initializationFailure_iff_operational y))
  refine ⟨hboundary, houtput, ?_, ?_, hordinaryOutput, hfailureOutput,
    hforced, hactivation, hoper⟩
  · change (if (ReferenceInitializationRun.output x).crossing.isSome = true then
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output x).completed + 1
      else p.T + 1) =
      (if (ReferenceInitializationRun.output y).crossing.isSome = true then
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output y).completed + 1
      else p.T + 1)
    exact congrArg (fun b : ReferenceInitializationRun.Boundary p =>
      if b.crossing.isSome = true then ReferenceInitializationRun.elapsed p b.completed + 1
      else p.T + 1) houtput
  · exact congrArg (fun b : ReferenceInitializationRun.Boundary p => b.completed) houtput

private theorem source_calendar_output_eq_of_one_event
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (t : ℕ)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ s : Fin p.T, s.val < t →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s)
    (hcontrol : ∀ s : Fin p.T, s.val < t →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s)
    (hevent :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ t) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
    ReferenceInitializationRun.run x (ReferenceInitializationRun.output x).completed =
      ReferenceInitializationRun.run y (ReferenceInitializationRun.output x).completed ∧
    ReferenceInitializationRun.output x = ReferenceInitializationRun.output y ∧
    ReferenceInitializationRun.launchRound x = ReferenceInitializationRun.launchRound y ∧
    (ReferenceInitializationRun.output x).completed =
      (ReferenceInitializationRun.output y).completed ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) i =
        ReferenceInitializationRun.ordinary y (ReferenceInitializationRun.output y) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.output x) i =
      ReferenceInitializationRun.initializationFailure y
        (ReferenceInitializationRun.output y) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).forcedFailure i =
        (ReferenceInitializationRun.output y).forcedFailure i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).activation i =
        (ReferenceInitializationRun.output y).activation i) ∧
    (InitializationFailureProvenance.operationalInitializationFailure x ↔
      InitializationFailureProvenance.operationalInitializationFailure y) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
  let r := (ReferenceInitializationRun.output x).completed
  have hr : r ≤ n_boot p := (ReferenceInitializationRun.output x).completed_le
  have hrunX : ReferenceInitializationRun.run x r = ReferenceInitializationRun.output x := by
    change ReferenceInitializationRun.run x
      (ReferenceInitializationRun.run x (n_boot p)).completed =
        ReferenceInitializationRun.run x (n_boot p)
    exact ReferenceInitializationPrefixInvariance.run_at_completed x (n_boot p) le_rfl
  have hcross : (ReferenceInitializationRun.run x r).crossing.isSome = true := by
    rw [hrunX]
    exact hevent.1
  have hforwardR : ∀ s : Fin p.T,
      s.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s := by
    intro s hs u
    exact hforward s (Nat.lt_of_lt_of_le hs hevent.2) u
  have hcontrolR : ∀ s : Fin p.T,
      s.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s := by
    intro s hs
    exact hcontrol s (Nat.lt_of_lt_of_le hs hevent.2)
  simpa only [x, y, r] using
    (source_stopped_output_eq_of_crossing rate rewards C_star C_h source source' r hr
      hids hprivate hforwardR hcontrolR hcross)

/-- At every calendar boundary through `T`, the literal event that the
generated terminal output has crossed and completed by that boundary is
determined by IDs, the full private input, and selected-row reads strictly
before the boundary. The reverse direction uses the other run's generated
completed-block witness. -/
theorem source_calendar_stopped_event_iff
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (t : ℕ) (_ht : t ≤ p.T)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ s : Fin p.T, s.val < t →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s)
    (hcontrol : ∀ s : Fin p.T, s.val < t →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
    ((ReferenceInitializationRun.output x).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed ≤ t) ↔
    ((ReferenceInitializationRun.output y).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output y).completed ≤ t) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
  have hJ := selectedIndex_eq_of_private_eq source source' hprivate
  have hforward' : ∀ s : Fin p.T, s.val < t →
      ∀ u : Fin (A_id p),
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).1 u s =
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).1 u s := by
    intro s hs u
    rw [← hJ]
    exact (hforward s hs u).symm
  have hcontrol' : ∀ s : Fin p.T, s.val < t →
      (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 s =
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 s := by
    intro s hs
    rw [← hJ]
    exact (hcontrol s hs).symm
  constructor
  · intro hevent
    have hresult := source_calendar_output_eq_of_one_event rate rewards C_star C_h
      source source' t hids hprivate hforward hcontrol hevent
    have hout := hresult.2.1
    have hcrossEq := congrArg
      (fun b : ReferenceInitializationRun.Boundary p => b.crossing.isSome) hout
    have helapsedEq := congrArg
      (fun b : ReferenceInitializationRun.Boundary p =>
        ReferenceInitializationRun.elapsed p b.completed) hout
    have hcross : (ReferenceInitializationRun.output y).crossing.isSome = true :=
      hcrossEq.symm.trans hevent.1
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output y).completed ≤ t := by
      rw [← helapsedEq]
      exact hevent.2
    exact ⟨hcross, helapsed⟩
  · intro hevent
    have hresult := source_calendar_output_eq_of_one_event rate rewards C_star C_h
      source' source t hids.symm hprivate.symm hforward' hcontrol' hevent
    have hout := hresult.2.1
    have hcrossEq := congrArg
      (fun b : ReferenceInitializationRun.Boundary p => b.crossing.isSome) hout
    have helapsedEq := congrArg
      (fun b : ReferenceInitializationRun.Boundary p =>
        ReferenceInitializationRun.elapsed p b.completed) hout
    have hcross : (ReferenceInitializationRun.output x).crossing.isSome = true :=
      hcrossEq.symm.trans hevent.1
    have helapsed : ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output x).completed ≤ t := by
      rw [← helapsedEq]
      exact hevent.2
    exact ⟨hcross, helapsed⟩

/-- If either side has crossed by calendar boundary `t`, the complete terminal
outputs and ordinary states agree. The event equivalence itself has no event
premise; this implication packages only the branch-dependent object equality. -/
theorem source_calendar_stopped_output_eq_of_event
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (t : ℕ) (ht : t ≤ p.T)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ s : Fin p.T, s.val < t →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u s)
    (hcontrol : ∀ s : Fin p.T, s.val < t →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 s)
    (heither :
      ((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ t) ∨
      ((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).completed ≤ t)) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
    ReferenceInitializationRun.run x (ReferenceInitializationRun.output x).completed =
      ReferenceInitializationRun.run y (ReferenceInitializationRun.output x).completed ∧
    ReferenceInitializationRun.output x = ReferenceInitializationRun.output y ∧
    ReferenceInitializationRun.launchRound x = ReferenceInitializationRun.launchRound y ∧
    (ReferenceInitializationRun.output x).completed =
      (ReferenceInitializationRun.output y).completed ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) i =
        ReferenceInitializationRun.ordinary y (ReferenceInitializationRun.output y) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.output x) i =
      ReferenceInitializationRun.initializationFailure y
        (ReferenceInitializationRun.output y) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).forcedFailure i =
        (ReferenceInitializationRun.output y).forcedFailure i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      (ReferenceInitializationRun.output x).activation i =
        (ReferenceInitializationRun.output y).activation i) ∧
    (InitializationFailureProvenance.operationalInitializationFailure x ↔
      InitializationFailureProvenance.operationalInitializationFailure y) := by
  dsimp only
  have heventIff := source_calendar_stopped_event_iff rate rewards C_star C_h
    source source' t ht hids hprivate hforward hcontrol
  have heventX := Or.elim heither id heventIff.mpr
  exact source_calendar_output_eq_of_one_event rate rewards C_star C_h
    source source' t hids hprivate hforward hcontrol heventX

end Bandits.Support.ReferenceInitializationStoppedLocality

end
