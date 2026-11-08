/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bandits Lean regret formalization contributors.
-/
module

public import Bandits.Support.ActualReferenceInitializationHorizon
public import Bandits.Support.ReferenceInitializationPrefixInvariance
public import Bandits.Support.ReferenceSelectedAffinePairLaw

/-!
# Original-source locality for corrected reference initialization

Sources: `sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:112-137`,
`sources/zip4/manuscript/06_interruptions.tex:376-423`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The proofs compare the existing generated reference run on complete original
source inputs. They preserve the selected row, whole private input, saved
ordinary replay state, and the generated exceptional failure causes. A fixed
original pair can be varied only at or after the elapsed prefix boundary.
These are deterministic internal locality results; they do not assert a source
law, conditional freshness, a launch-state characterization, or manuscript
closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.InitializationFailureProvenance
open scoped Classical

namespace Bandits.Support.ReferenceInitializationOriginLocality

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

private theorem source_runPrefixInputEq_of_coordinates
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t)
    (hcontrol : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) :
    ReferenceInitializationCausality.runPrefixInputEq
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r := by
  have hJ : ActualInitializationPhysicalStep.selectedRowIndex p source =
      ActualInitializationPhysicalStep.selectedRowIndex p source' := by
    change PrivateSourceStreams.coordinatorIndex p source.2.1.2 =
      PrivateSourceStreams.coordinatorIndex p source'.2.1.2
    rw [hprivate]
  refine ⟨hids, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro u
      change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).1 u t
      rw [← hJ]
      exact hforward t ht u
    · change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 t
      rw [← hJ]
      exact hcontrol t ht
  · intro s hs j
    change source.2.1.1 s j = source'.2.1.1 s j
    rw [hprivate]
  · intro s hs
    change source.2.2.2 s = source'.2.2.2 s
    rw [hprivate]
  · intro i t ht
    change source.2.2.1 (i, t) = source'.2.2.1 (i, t)
    rw [hprivate]

private theorem run_boundary_eq_of_source_coordinates
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t)
    (hcontrol : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) :
    ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r =
      ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r := by
  apply ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq
  exact source_runPrefixInputEq_of_coordinates rate rewards C_star C_h source source' r
    hids hprivate hforward hcontrol

private theorem ordinary_eq_of_run_boundary_eq
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ) (i : ActiveRoundActions.Follower p.m)
    (hboundary : ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r =
      ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r)
    (hprivate : source.2 = source'.2)
    (hcontrol : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) :
    ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.run
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i =
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
        (ReferenceInitializationRun.run
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r) i := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
  rw [← hboundary]
  let b := ReferenceInitializationRun.run x r
  change ReferenceInitializationRun.ordinary x b i = ReferenceInitializationRun.ordinary y b i
  cases hforced : b.forcedFailure i with
  | true =>
      simp [ReferenceInitializationRun.ordinary, hforced, x, y,
        ActualReferenceInitializationBlock.referenceInput]
  | false =>
      cases hactivation : b.activation i with
      | none =>
          simp [ReferenceInitializationRun.ordinary, hforced, hactivation, x, y,
            ActualReferenceInitializationBlock.referenceInput]
      | some a =>
          have hcompleted : b.completed ≤ r :=
            ReferenceInitializationPrefixInvariance.run_completed_le x r
          have hElapsed : ReferenceInitializationRun.elapsed p b.completed ≤
              ReferenceInitializationRun.elapsed p r :=
            ReferenceInitializationRun.elapsed_mono p hcompleted
          have hreplay := ReferencePrelaunchFollower.replay_eq_of_past_reads
            x.eta (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row y.row a
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m i))
            (ReferenceInitializationRun.elapsed_le_T p b.completed)
            (by
              intro u _ha
              have hu : u.val < ReferenceInitializationRun.elapsed p r :=
                Nat.lt_of_lt_of_le u.isLt hElapsed
              have hxy := hcontrol (ReferencePrelaunchFollower.calendar
                (ReferenceInitializationRun.elapsed_le_T p b.completed) u) (by
                  simpa only [ReferencePrelaunchFollower.calendar] using hu)
              have hJ : ActualInitializationPhysicalStep.selectedRowIndex p source =
                  ActualInitializationPhysicalStep.selectedRowIndex p source' := by
                change PrivateSourceStreams.coordinatorIndex p source.2.1.2 =
                  PrivateSourceStreams.coordinatorIndex p source'.2.1.2
                rw [hprivate]
              have hxy' : x.row.2 (ReferencePrelaunchFollower.calendar
                  (ReferenceInitializationRun.elapsed_le_T p b.completed) u) =
                  y.row.2 (ReferencePrelaunchFollower.calendar
                    (ReferenceInitializationRun.elapsed_le_T p b.completed) u) := by
                change (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 _ =
                  (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 _
                rw [← hJ]
                exact hxy
              unfold ReferencePrelaunchFollower.reads_agree
              rw [hxy']
              exact ⟨rfl, rfl, rfl, rfl, (fun _ _ => rfl), rfl⟩)
            (by intro u _ha; rfl)
          simpa [ReferenceInitializationRun.ordinary, hforced, hactivation, x, y,
            ActualReferenceInitializationBlock.referenceInput] using
            congrArg ReferencePrelaunchFollower.atLaunch hreplay

/-- Equality of generated corrected boundaries follows from the original
coordinate equalities alone. The selected row is derived from the same whole
extended private input, including its separate coordinator scalar. -/
theorem source_run_boundary_eq
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t)
    (hcontrol : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) :
    ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r =
      ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r :=
  run_boundary_eq_of_source_coordinates rate rewards C_star C_h source source' r
    hids hprivate hforward hcontrol

/-- Every follower's complete ordinary state, including saved data and decoder
batches and the suppressed-acceptance flag, agrees at a generated prefix. The
replay equality is derived from the common generated history and actual past
control reads. -/
theorem source_run_ordinary_eq
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t)
    (hcontrol : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) :
    ∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i =
        ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r) i := by
  have hboundary := source_run_boundary_eq rate rewards C_star C_h source source' r
    hids hprivate hforward hcontrol
  intro i
  exact ordinary_eq_of_run_boundary_eq
    rate rewards C_star C_h source source' r i hboundary hprivate hcontrol

/-- Generated initialization-failure flags and their provenance causes agree
on every prefix in the explicit domain `r ≤ n_boot`. Failure flags are outputs:
forced post-declaration corrections and suppressed ordinary DOWN acceptances
remain present in the equivalence. -/
theorem source_run_failure_eq
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hforward : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t)
    (hcontrol : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t) :
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i =
        ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r i ↔
        InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r i) := by
  have hboundary := source_run_boundary_eq rate rewards C_star C_h source source' r
    hids hprivate hforward hcontrol
  have hordinary := source_run_ordinary_eq rate rewards C_star C_h source source' r
    hids hprivate hforward hcontrol
  have hflagEq : ∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i =
        ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r) i := by
    intro i
    unfold ReferenceInitializationRun.initializationFailure
    exact congrArg₂ (fun (b : ReferenceInitializationRun.Boundary p)
        (s : ReferencePrelaunchFollower.State p rate.eta) =>
      b.forcedFailure i || s.initializationFailure)
      hboundary (hordinary i)
  refine ⟨hflagEq, ?_⟩
  intro i
  have hflag := (InitializationFailureProvenance.run_initializationFailure_iff_causesBefore
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) i r) hr
  have hflag' := (InitializationFailureProvenance.run_initializationFailure_iff_causesBefore
    (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) i r) hr
  constructor
  · intro hcause
    apply hflag'.mp
    exact (hflagEq i).symm.trans (hflag.mpr hcause)
  · intro hcause
    apply hflag.mp
    exact (hflagEq i).trans (hflag'.mpr hcause)

/-- At the completed horizon, equality of IDs, the entire original private
input, and the same selected complete row gives equal output, launch round,
every ordinary follower state, and operational `E_init`. The selected row is
derived from the original coordinator scalar; other complete rows are
unrestricted. -/
theorem source_terminal_output_eq
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source source' : BootstrapPrivateRoundStreams.SourceInput p)
    (hids : source.1.1 = source'.1.1)
    (hprivate : source.2 = source'.2)
    (hrow : source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) =
      source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
    ReferenceInitializationRun.output x = ReferenceInitializationRun.output y ∧
    ReferenceInitializationRun.launchRound x = ReferenceInitializationRun.launchRound y ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.output x) i =
        ReferenceInitializationRun.ordinary y (ReferenceInitializationRun.output y) i) ∧
    (InitializationFailureProvenance.operationalInitializationFailure x ↔
      InitializationFailureProvenance.operationalInitializationFailure y) := by
  dsimp only
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let y := ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate
  have hrow' : x.row = y.row := by
    change source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) =
      source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')
    exact hrow
  have hJ : ActualInitializationPhysicalStep.selectedRowIndex p source =
      ActualInitializationPhysicalStep.selectedRowIndex p source' := by
    change PrivateSourceStreams.coordinatorIndex p source.2.1.2 =
      PrivateSourceStreams.coordinatorIndex p source'.2.1.2
    rw [hprivate]
  have hrowCommon := hrow
  rw [← hJ] at hrowCommon
  have hforwardAll : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p (n_boot p) →
      ∀ u : Fin (A_id p),
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t =
          (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 u t := by
    intro t _ u
    exact congrArg (fun row : CompletePublicTable.CompleteRow p => row.1 u t) hrowCommon
  have hcontrolAll : ∀ t : Fin p.T, t.val < ReferenceInitializationRun.elapsed p (n_boot p) →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t := by
    intro t _
    exact congrArg (fun row : CompletePublicTable.CompleteRow p => row.2 t) hrowCommon
  have hrun := source_run_boundary_eq rate rewards C_star C_h source source' (n_boot p)
    hids hprivate hforwardAll hcontrolAll
  have hordinary := source_run_ordinary_eq rate rewards C_star C_h source source' (n_boot p)
    hids hprivate hforwardAll hcontrolAll
  have hfailure := source_run_failure_eq rate rewards C_star C_h source source' (n_boot p)
    le_rfl hids hprivate hforwardAll hcontrolAll
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [ReferenceInitializationRun.output] using hrun
  · change (if (ReferenceInitializationRun.run x (n_boot p)).crossing.isSome = true then
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run x (n_boot p)).completed + 1
      else p.T + 1) =
      (if (ReferenceInitializationRun.run y (n_boot p)).crossing.isSome = true then
        ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.run y (n_boot p)).completed + 1
      else p.T + 1)
    exact congrArg (fun b : ReferenceInitializationRun.Boundary p =>
      if b.crossing.isSome = true then ReferenceInitializationRun.elapsed p b.completed + 1
      else p.T + 1) hrun
  · simpa only [ReferenceInitializationRun.output] using hordinary
  · have hflags := hfailure.1
    have hexists :
        (∃ i : ActiveRoundActions.Follower p.m,
          ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i = true) ↔
        (∃ i : ActiveRoundActions.Follower p.m,
          ReferenceInitializationRun.initializationFailure y (ReferenceInitializationRun.output y) i = true) := by
      constructor
      · rintro ⟨i, hi⟩
        have hflags' :
            ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i =
              ReferenceInitializationRun.initializationFailure y (ReferenceInitializationRun.output y) i := by
          simpa only [ReferenceInitializationRun.output] using hflags i
        exact ⟨i, hflags' ▸ hi⟩
      · rintro ⟨i, hi⟩
        have hflags' :
            ReferenceInitializationRun.initializationFailure x (ReferenceInitializationRun.output x) i =
              ReferenceInitializationRun.initializationFailure y (ReferenceInitializationRun.output y) i := by
          simpa only [ReferenceInitializationRun.output] using hflags i
        exact ⟨i, hflags'.symm ▸ hi⟩
    exact (InitializationFailureProvenance.initializationFailure_iff_operational x).symm.trans
      (hexists.trans (InitializationFailureProvenance.initializationFailure_iff_operational y))

/-- No current finite round has index at least the completed full horizon. -/
theorem source_pair_prefix_terminal_cut_impossible (t : Fin p.T)
    (hcut : ReferenceInitializationRun.elapsed p (n_boot p) ≤ t.val) : False := by
  rw [ReferenceInitializationRun.elapsed_all_blocks] at hcut
  exact (Nat.not_le_of_gt t.isLt) hcut

/-- Vary the pair at one original selected-row coordinate only after the
completed prefix boundary. The literal bound is `elapsed p r ≤ t.val`; it does
not admit an artificial sample at elapsed `T`, and arbitrary changes in the
past can change both ordinary replay batches and initialization failure. -/
theorem source_pair_prefix_invariant
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (t : Fin p.T) (c : ContinuousLearningRows.Channel p)
    (a : ReferenceSelectedAffinePairLaw.Pair p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (hcut : ReferenceInitializationRun.elapsed p r ≤ t.val) :
    let q := ActualInitializationPhysicalStep.selectedRowIndex p source
    let remainder := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c source).2
    let source' := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, remainder)
    ActualInitializationPhysicalStep.selectedRowIndex p source' = q ∧
    ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c source' = (a, remainder) ∧
    ((source'.1.2 q).2 t).2 c = a ∧
    (∀ k : ReferenceSelectedAffinePairLaw.Other c,
      ((source'.1.2 q).2 t).2 k = ((source.1.2 q).2 t).2 k) ∧
    ((source'.1.2 q).2 t).1 = ((source.1.2 q).2 t).1 ∧
    ContinuousControlSlice.assignmentVector ((source'.1.2 q).2 t).1 =
      ContinuousControlSlice.assignmentVector ((source.1.2 q).2 t).1 ∧
    (∀ s : ReferenceSelectedAffinePairLaw.Other t,
      (source'.1.2 q).2 s = (source.1.2 q).2 s) ∧
    (∀ j : ReferenceSelectedAffinePairLaw.Other q,
      source'.1.2 j = source.1.2 j) ∧
    (source'.1.2 q).1 = (source.1.2 q).1 ∧
    source'.1.1 = source.1.1 ∧ source'.2 = source.2 ∧
    ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r =
      ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i =
        ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r) i =
        ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r i ↔
        InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) r i) := by
  dsimp only
  let q := ActualInitializationPhysicalStep.selectedRowIndex p source
  let remainder := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c source).2
  let source' := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, remainder)
  have hcoords := ReferenceSelectedAffinePairLaw.fixedPairSplit_inverse_coordinates
    p q t c a remainder
  dsimp only at hcoords
  rcases hcoords with ⟨hpair, hids', hprivate', hforward', hslice', hchannel', htime', hrow'⟩
  have hJScalar : source'.2.1.2 = source.2.1.2 := by
    calc
      source'.2.1.2 = remainder.2.1.2 := congrArg (fun z : ExtendedPrivateCoordinates p => z.1.2) hprivate'
      _ = source.2.1.2 := ReferenceSelectedAffinePairLaw.fixedPairSplit_jScalar p q t c source
  have hJ : ActualInitializationPhysicalStep.selectedRowIndex p source' = q := by
    change PrivateSourceStreams.coordinatorIndex p source'.2.1.2 = q
    rw [hJScalar]
    rfl
  have hids : source.1.1 = source'.1.1 := by
    calc
      source.1.1 = remainder.1.1 := (ReferenceSelectedAffinePairLaw.fixedPairSplit_id
        p q t c source).symm
      _ = source'.1.1 := hids'.symm
  have hprivate : source.2 = source'.2 := by
    calc
      source.2 = remainder.2 := (ReferenceSelectedAffinePairLaw.fixedPairSplit_private
        p q t c source).symm
      _ = source'.2 := hprivate'.symm
  have hforward : ∀ s : Fin p.T, s.val < ReferenceInitializationRun.elapsed p r →
      ∀ u : Fin (A_id p),
        (source.1.2 q).1 u s = (source'.1.2 q).1 u s := by
    intro s _ u
    have hrowForward : (source.1.2 q).1 = (source'.1.2 q).1 := by
      calc
        (source.1.2 q).1 = remainder.1.2.1.1 :=
          (ReferenceSelectedAffinePairLaw.fixedPairSplit_forward p q t c source).symm
        _ = (source'.1.2 q).1 := hforward'.symm
    exact congrArg (fun row : CompletePublicTable.ForwardRow p => row u s) hrowForward
  have hcontrol : ∀ s : Fin p.T, s.val < ReferenceInitializationRun.elapsed p r →
      (source.1.2 q).2 s = (source'.1.2 q).2 s := by
    intro s hs
    have hst : s ≠ t := by
      intro hst
      have hlt : s.val < t.val := Nat.lt_of_lt_of_le hs hcut
      have hval := congrArg Fin.val hst
      omega
    let s' : ReferenceSelectedAffinePairLaw.Other t := ⟨s, hst⟩
    calc
      (source.1.2 q).2 s = remainder.1.2.1.2.2 s' :=
        (ReferenceSelectedAffinePairLaw.fixedPairSplit_other_time p q t c source s').symm
      _ = (source'.1.2 q).2 s := (htime' s').symm
  have hotherChannel : ∀ k : ReferenceSelectedAffinePairLaw.Other c,
      ((source'.1.2 q).2 t).2 k = ((source.1.2 q).2 t).2 k := by
    intro k
    calc
      ((source'.1.2 q).2 t).2 k = remainder.1.2.1.2.1.2 k := hchannel' k
      _ = ((source.1.2 q).2 t).2 k :=
        ReferenceSelectedAffinePairLaw.fixedPairSplit_other_channel p q t c source k
  have hslice : ((source'.1.2 q).2 t).1 = ((source.1.2 q).2 t).1 := by
    calc
      ((source'.1.2 q).2 t).1 = remainder.1.2.1.2.1.1 := hslice'
      _ = ((source.1.2 q).2 t).1 :=
        ReferenceSelectedAffinePairLaw.fixedPairSplit_slice p q t c source
  have hassignment :
      ContinuousControlSlice.assignmentVector ((source'.1.2 q).2 t).1 =
        ContinuousControlSlice.assignmentVector ((source.1.2 q).2 t).1 :=
    congrArg ContinuousControlSlice.assignmentVector hslice
  have hotherTime : ∀ s : ReferenceSelectedAffinePairLaw.Other t,
      (source'.1.2 q).2 s = (source.1.2 q).2 s := by
    intro s
    calc
      (source'.1.2 q).2 s = remainder.1.2.1.2.2 s := htime' s
      _ = (source.1.2 q).2 s :=
        ReferenceSelectedAffinePairLaw.fixedPairSplit_other_time p q t c source s
  have hotherRow : ∀ j : ReferenceSelectedAffinePairLaw.Other q,
      source'.1.2 j = source.1.2 j := by
    intro j
    calc
      source'.1.2 j = remainder.1.2.2 j := hrow' j
      _ = source.1.2 j :=
        ReferenceSelectedAffinePairLaw.fixedPairSplit_other_row p q t c source j
  have hforwardAll : (source'.1.2 q).1 = (source.1.2 q).1 := by
    calc
      (source'.1.2 q).1 = remainder.1.2.1.1 := hforward'
      _ = (source.1.2 q).1 :=
        ReferenceSelectedAffinePairLaw.fixedPairSplit_forward p q t c source
  have hcoord := source_runPrefixInputEq_of_coordinates rate rewards C_star C_h
    source source' r hids hprivate hforward hcontrol
  have hboundary := ReferenceInitializationPrefixInvariance.run_eq_of_runPrefixInputEq
    _ _ r hcoord
  have hordinary := source_run_ordinary_eq rate rewards C_star C_h source source' r
    hids hprivate hforward hcontrol
  have hfailure := source_run_failure_eq rate rewards C_star C_h source source' r
    hr hids hprivate hforward hcontrol
  refine ⟨hJ, ?_, hpair, hotherChannel, hslice, hassignment, hotherTime, hotherRow, hforwardAll,
    hids.symm, hprivate.symm, hboundary, hordinary, hfailure.1, hfailure.2⟩
  exact ReferenceSelectedAffinePairLaw.fixedPairSplit_split_reconstruct p q t c (a, remainder)

end Bandits.Support.ReferenceInitializationOriginLocality

end
