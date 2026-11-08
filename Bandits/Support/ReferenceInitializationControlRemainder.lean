/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFixedTimeSourceControlCoupling
public import Bandits.Support.ReferenceInitializationStoppedLocality

/-!
# Original-source initialization observations on a fixed-control remainder

Sources: `sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/06_interruptions.tex:376-423`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module records actual generated initialization prefixes and stopped
outputs on the original complete source. Their observations factor through
the admitted selected-row/current-time split when its removed control is at
or after the observed boundary. The stopped observation uses `none` when no
crossing has occurred by that boundary; it does not create an operational
fallback state.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.InitializationFailureProvenance
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical

namespace Bandits.Support.ReferenceInitializationControlRemainder

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The generated boundary and complete ordinary follower states after `r`
actual reference initialization blocks on the original source. -/
def prefixObservation
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (r : ℕ) :=
  let x := ActualReferenceInitializationBlock.referenceInput
    source rewards C_star C_h rate
  (ReferenceInitializationRun.run x r,
    fun i : ActiveRoundActions.Follower p.m =>
      ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.run x r) i)

/-- The original-source event that reference initialization has crossed and
completed its generated boundary by calendar time `s`. -/
def stoppedCrossedBy
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (s : ℕ) : Prop :=
  let x := ActualReferenceInitializationBlock.referenceInput
    source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  b.crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p b.completed ≤ s

/-- The literal stopped output observation: retain the generated terminal
boundary and ordinary states exactly when crossing has occurred by `s`. -/
def stoppedObservation
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (s : ℕ) :
    Option (ReferenceInitializationRun.Boundary p ×
      (ActiveRoundActions.Follower p.m →
        ReferencePrelaunchFollower.State p rate.eta)) :=
  let x := ActualReferenceInitializationBlock.referenceInput
    source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  if stoppedCrossedBy rate rewards C_star C_h source s then
    some (b, fun i => ReferenceInitializationRun.ordinary x b i)
  else
    none

/-- Literal evaluation of the prefix observation at the inverse of the
admitted original-source fixed-control split. -/
def prefixObservationFactor
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t) (r : ℕ) :=
  prefixObservation rate rewards C_star C_h
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control, remainder)) r

/-- Literal evaluation of the stopped event at the inverse of the admitted
original-source fixed-control split. -/
def stoppedCrossingFactor
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (control : TimeControl p)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t) : Prop :=
  stoppedCrossedBy rate rewards C_star C_h
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control, remainder)) s

/-- Literal evaluation of the stopped observation at the inverse of the
admitted original-source fixed-control split. -/
def stoppedObservationFactor
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (control : TimeControl p)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t) :=
  stoppedObservation rate rewards C_star C_h
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
      (control, remainder)) s

/-- The literal stopped-crossing event on the admitted original-source
remainder, obtained by evaluating `stoppedCrossedBy` at its inverse split. -/
def stoppedCrossingRemainderEvent
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (control : TimeControl p) :
    Set (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
  {remainder | stoppedCrossingFactor rate rewards C_star C_h q t s control remainder}

/-- The exact generated launch-start fibre on a selected-row remainder.
Membership is defined using the stopped option observation, retaining the
boundary and ordinary states that witness a launch at elapsed time `s`. -/
def launchStartRemainderEvent
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (control : TimeControl p) :
    Set (ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t) :=
  {remainder | ∃ observed : ReferenceInitializationRun.Boundary p ×
      (ActiveRoundActions.Follower p.m →
        ReferencePrelaunchFollower.State p rate.eta),
    stoppedObservationFactor rate rewards C_star C_h q t t.val control remainder =
      some observed ∧
    observed.1.crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p observed.1.completed = s}

private theorem replaceSourceControl_frames_before
    (t : Fin p.T) (source : SourceInput p) (control : TimeControl p)
    (bound : ℕ) (hbound : bound ≤ t.val) :
    source.1.1 = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t source control).1.1 ∧
    source.2 = (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
      p t source control).2 ∧
    ActualInitializationPhysicalStep.selectedRowIndex p source =
      ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control) ∧
    (∀ v : Fin p.T, v.val < bound → ∀ a : Fin (A_id p),
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 a v =
        ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 a v) ∧
    (∀ v : Fin p.T, v.val < bound →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v =
        ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v) := by
  let source' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
    p t source control
  have hids : source.1.1 = source'.1.1 :=
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_id
      p t source control).symm
  have hprivate : source.2 = source'.2 :=
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_private
      p t source control).symm
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source =
      ActualInitializationPhysicalStep.selectedRowIndex p source' := by
    change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source =
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source'
    unfold ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex
    rw [← hprivate]
  refine ⟨hids, hprivate, hselected, ?_, ?_⟩
  · intro v _ a
    change (source.1.2
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)).1 a v =
      ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
        p t source control).1.2
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)).1 a v
    exact congrArg (fun f : Fin (A_id p) → Fin p.T → Bool => f a v)
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl_forward
        p t source control).symm
  · intro v hv
    have hne : v ≠ t := by
      intro h
      subst v
      exact (Nat.not_lt_of_ge hbound) hv
    change (source.1.2
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)).2 v =
      ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
        p t source control).1.2
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source)).2 v
    simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
      Function.update_self, Function.update_of_ne hne]

/-- Prefix observations and both generated initialization-failure outputs are
unchanged by replacing the selected row's control at time `t`, provided that
the observed prefix ends no later than `t`. -/
theorem prefix_observation_replaceSourceControl
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p) (r : ℕ) (hr : r ≤ n_boot p)
    (hcut : ReferenceInitializationRun.elapsed p r ≤ t.val) :
    prefixObservation rate rewards C_star C_h
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control) r =
      prefixObservation rate rewards C_star C_h source r ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            r) i =
        ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
              p t source control) rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
                p t source control) rewards C_star C_h rate) r) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          r i ↔
        InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
              p t source control) rewards C_star C_h rate) r i) := by
  let source' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
    p t source control
  have hframes := replaceSourceControl_frames_before t source control
    (ReferenceInitializationRun.elapsed p r) hcut
  rcases hframes with ⟨hids, hprivate, _, hforward, hcontrol⟩
  have hboundary := ReferenceInitializationOriginLocality.source_run_boundary_eq
    rate rewards C_star C_h source source' r hids hprivate hforward hcontrol
  have hordinary := ReferenceInitializationOriginLocality.source_run_ordinary_eq
    rate rewards C_star C_h source source' r hids hprivate hforward hcontrol
  have hfailure := ReferenceInitializationOriginLocality.source_run_failure_eq
    rate rewards C_star C_h source source' r hr hids hprivate hforward hcontrol
  refine ⟨?_, hfailure.1, hfailure.2⟩
  unfold prefixObservation
  exact Prod.ext hboundary.symm (funext fun i => (hordinary i).symm)

/-- The exact stopped-crossing event and stopped option observation are
unchanged by replacing the selected row's control at any time at or after the
observation boundary. The option equality includes the genuine none/none
branch and requires no supplied crossing hypothesis. -/
theorem stopped_observation_replaceSourceControl
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p) (s : ℕ) (hs : s ≤ t.val) :
    (stoppedCrossedBy rate rewards C_star C_h source s ↔
      stoppedCrossedBy rate rewards C_star C_h
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control) s) ∧
    stoppedObservation rate rewards C_star C_h source s =
      stoppedObservation rate rewards C_star C_h
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control) s := by
  let source' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
    p t source control
  have hframes := replaceSourceControl_frames_before t source control s hs
  rcases hframes with ⟨hids, hprivate, _, hforward, hcontrol⟩
  have ht : s ≤ p.T := hs.trans (Nat.le_of_lt t.isLt)
  have hevent := ReferenceInitializationStoppedLocality.source_calendar_stopped_event_iff
    rate rewards C_star C_h source source' s ht hids hprivate hforward hcontrol
  have hA : stoppedCrossedBy rate rewards C_star C_h source s ↔
      stoppedCrossedBy rate rewards C_star C_h source' s := by
    simpa only [stoppedCrossedBy] using hevent
  refine ⟨hA, ?_⟩
  by_cases hleft : stoppedCrossedBy rate rewards C_star C_h source s
  · have hright := hA.mp hleft
    have hleftRaw :
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              source rewards C_star C_h rate)).completed ≤ s := by
      simpa only [stoppedCrossedBy] using hleft
    have hterminal :=
      ReferenceInitializationStoppedLocality.source_calendar_stopped_output_eq_of_event
        rate rewards C_star C_h source source' s ht hids hprivate hforward hcontrol
        (Or.inl hleftRaw)
    rcases hterminal with ⟨_, hboundary, _, _, hordinary, _, _, _, _⟩
    have hpayload :
        (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              source rewards C_star C_h rate),
          fun i => ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput
              source rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput
                source rewards C_star C_h rate)) i) =
        (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              source' rewards C_star C_h rate),
          fun i => ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput
              source' rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput
                source' rewards C_star C_h rate)) i) := by
      exact Prod.ext hboundary (funext hordinary)
    simpa only [stoppedObservation, source',
      ActualReferenceInitializationBlock.referenceInput,
      hleft, hright, ↓reduceIte] using congrArg some hpayload
  · have hright : ¬ stoppedCrossedBy rate rewards C_star C_h source' s := by
      intro h
      exact hleft (hA.mpr h)
    have hright' : ¬ stoppedCrossedBy rate rewards C_star C_h
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
          p t source control) s := by
      simpa only [source'] using hright
    simp only [stoppedObservation, hleft, hright', ↓reduceIte]

private theorem split_reconstruction_replaceSourceControl
    (q : Fin (M p)) (t : Fin p.T)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) :
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control', remainder) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (control, remainder)) control' := by
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let source := e.symm (control, remainder)
  have hq := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
    p q t control remainder hremainder
  have hreplace := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t source control' hq
  have hrem : (e source).2 = remainder := by
    exact congrArg Prod.snd (e.apply_symm_apply (control, remainder))
  calc
    e.symm (control', remainder) = e.symm (control', (e source).2) := by rw [hrem]
    _ = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control' :=
      hreplace

private theorem split_reconstruction_replaceSourceControl_of_source
    (q : Fin (M p)) (t : Fin p.T) (source : SourceInput p)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (control : TimeControl p) :
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control,
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2) =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control := by
  have hq' : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hq
  exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t source control hq'

/-- A source-generated prefix observation, its per-follower failure flags, and
its failure-cause events factor through the admitted original fixed-control
split on the source's actual selected-row stratum. -/
theorem prefix_observation_fixedControl_factor
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (source : SourceInput p)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (r : ℕ) (hr : r ≤ n_boot p)
    (hcut : ReferenceInitializationRun.elapsed p r ≤ t.val) :
    prefixObservation rate rewards C_star C_h source r =
      prefixObservationFactor rate rewards C_star C_h q t control
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 r ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            r) i =
        ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (control,
                (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2))
            rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput
              ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
                (control,
                  (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2))
              rewards C_star C_h rate) r) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          r i ↔
        InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (control,
                (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2))
            rewards C_star C_h rate) r i) := by
  have hreplace := split_reconstruction_replaceSourceControl_of_source q t source hq control
  dsimp only [prefixObservationFactor]
  rw [hreplace]
  have hprefix := prefix_observation_replaceSourceControl
    rate rewards C_star C_h t source control r hr hcut
  refine ⟨hprefix.1.symm, hprefix.2.1, hprefix.2.2⟩

/-- The actual stopped event and option observation factor through the
admitted original fixed-control split on the source's selected-row stratum. -/
theorem stopped_observation_fixedControl_factor
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (source : SourceInput p)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (s : ℕ) (hs : s ≤ t.val) :
    (stoppedCrossedBy rate rewards C_star C_h source s ↔
      stoppedCrossingFactor rate rewards C_star C_h q t s control
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2) ∧
    stoppedObservation rate rewards C_star C_h source s =
      stoppedObservationFactor rate rewards C_star C_h q t s control
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 := by
  have hreplace := split_reconstruction_replaceSourceControl_of_source q t source hq control
  dsimp only [stoppedCrossingFactor, stoppedObservationFactor]
  rw [hreplace]
  exact stopped_observation_replaceSourceControl
    rate rewards C_star C_h t source control s hs

/-- On the original remainder stratum, the prefix factor is independent of the
removed continuous control, including all initialization-failure data. -/
theorem prefixObservationFactor_control_independent
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) (r : ℕ) (hr : r ≤ n_boot p)
    (hcut : ReferenceInitializationRun.elapsed p r ≤ t.val) :
    prefixObservationFactor rate rewards C_star C_h q t control remainder r =
      prefixObservationFactor rate rewards C_star C_h q t control' remainder r ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (control, remainder)) rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput
              ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
                (control, remainder)) rewards C_star C_h rate) r) i =
        ReferenceInitializationRun.initializationFailure
          (ActualReferenceInitializationBlock.referenceInput
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (control', remainder)) rewards C_star C_h rate)
          (ReferenceInitializationRun.run
            (ActualReferenceInitializationBlock.referenceInput
              ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
                (control', remainder)) rewards C_star C_h rate) r) i) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (control, remainder)) rewards C_star C_h rate) r i ↔
        InitializationFailureProvenance.failureCausesBefore
          (ActualReferenceInitializationBlock.referenceInput
            ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
              (control', remainder)) rewards C_star C_h rate) r i) := by
  have hsource := split_reconstruction_replaceSourceControl
    q t remainder hremainder control control'
  dsimp only [prefixObservationFactor]
  rw [hsource]
  have hprefix := prefix_observation_replaceSourceControl
    rate rewards C_star C_h t
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control, remainder)) control' r hr hcut
  refine ⟨hprefix.1.symm, hprefix.2.1, hprefix.2.2⟩

/-- On the original remainder stratum, both the stopped event and the full
stopped option observation are independent of the removed continuous control. -/
theorem stoppedObservationFactor_control_independent
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) (s : ℕ) (hs : s ≤ t.val) :
    (stoppedCrossingFactor rate rewards C_star C_h q t s control remainder ↔
      stoppedCrossingFactor rate rewards C_star C_h q t s control' remainder) ∧
    stoppedObservationFactor rate rewards C_star C_h q t s control remainder =
      stoppedObservationFactor rate rewards C_star C_h q t s control' remainder := by
  have hsource := split_reconstruction_replaceSourceControl
    q t remainder hremainder control control'
  dsimp only [stoppedCrossingFactor, stoppedObservationFactor]
  rw [hsource]
  exact stopped_observation_replaceSourceControl
    rate rewards C_star C_h t
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        (control, remainder)) control' s hs

/-- The stopped remainder event is independent of its reconstruction control
on the original selected-row remainder stratum. -/
theorem stoppedCrossingRemainderEvent_control_independent
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) (hs : s ≤ t.val) :
    remainder ∈ stoppedCrossingRemainderEvent rate rewards C_star C_h q t s control ↔
      remainder ∈ stoppedCrossingRemainderEvent rate rewards C_star C_h q t s control' := by
  change stoppedCrossingFactor rate rewards C_star C_h q t s control remainder ↔
    stoppedCrossingFactor rate rewards C_star C_h q t s control' remainder
  exact (stoppedObservationFactor_control_independent rate rewards C_star C_h q t
    remainder hremainder control control' s hs).1

/-- The launch-start fibre event is independent of its reconstruction control
because it is defined from the control-independent full stopped observation
at the current coordinate `t.val`. -/
theorem launchStartRemainderEvent_control_independent
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (remainder : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder
      p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) :
    remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control ↔
      remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control' := by
  change (∃ observed : ReferenceInitializationRun.Boundary p ×
      (ActiveRoundActions.Follower p.m →
        ReferencePrelaunchFollower.State p rate.eta),
      stoppedObservationFactor rate rewards C_star C_h q t t.val control remainder =
        some observed ∧
      observed.1.crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p observed.1.completed = s) ↔
    (∃ observed : ReferenceInitializationRun.Boundary p ×
      (ActiveRoundActions.Follower p.m →
        ReferencePrelaunchFollower.State p rate.eta),
      stoppedObservationFactor rate rewards C_star C_h q t t.val control' remainder =
        some observed ∧
      observed.1.crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p observed.1.completed = s)
  have hD := (stoppedObservationFactor_control_independent rate rewards C_star C_h
    q t remainder hremainder control control' t.val (Nat.le_refl _)).2
  rw [hD]

/-- The original source launch-start fibre is represented on its remainder by
the exact boundary-and-ordinary witness in `D_(t.val)`. -/
theorem launchStartRemainderEvent_iff_source
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p) (source : SourceInput p)
    (hq : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (s : ℕ) (hs : s ≤ t.val) :
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 ∈
      launchStartRemainderEvent rate rewards C_star C_h q t s control) ↔
    ((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s) := by
  have hfactor := stopped_observation_fixedControl_factor
    rate rewards C_star C_h q t control source hq t.val (Nat.le_refl _)
  have hD := hfactor.2
  change (∃ observed : ReferenceInitializationRun.Boundary p ×
      (ActiveRoundActions.Follower p.m →
        ReferencePrelaunchFollower.State p rate.eta),
      stoppedObservationFactor rate rewards C_star C_h q t t.val control
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2 =
          some observed ∧
      observed.1.crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p observed.1.completed = s) ↔ _
  rw [← hD]
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  constructor
  · rintro ⟨observed, hobserved, hcross, helapsed⟩
    unfold stoppedObservation at hobserved
    by_cases hcrossed : stoppedCrossedBy rate rewards C_star C_h source t.val
    · simp only [hcrossed, ↓reduceIte] at hobserved
      have hdata := Option.some.inj hobserved
      subst observed
      exact ⟨hcross, helapsed⟩
    · simp only [hcrossed, ↓reduceIte] at hobserved
      contradiction
  · rintro ⟨hcross, helapsed⟩
    have hcrossed : stoppedCrossedBy rate rewards C_star C_h source t.val := by
      exact ⟨hcross, by rw [helapsed]; exact hs⟩
    have hobserved : stoppedObservation rate rewards C_star C_h source t.val =
        some (b, fun i => ReferenceInitializationRun.ordinary x b i) := by
      unfold stoppedObservation
      change (if stoppedCrossedBy rate rewards C_star C_h source t.val then
          some (b, fun i => ReferenceInitializationRun.ordinary x b i) else none) = _
      simp only [hcrossed, ↓reduceIte]
    exact ⟨(b, fun i => ReferenceInitializationRun.ordinary x b i),
      hobserved, hcross, helapsed⟩

/-- At the natural horizon `T`, the stopped event is exactly the existence of
an actual reference crossing. This statement has no removed `Fin T` coordinate. -/
theorem stoppedCrossedBy_at_horizon_iff
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    stoppedCrossedBy rate rewards C_star C_h source p.T ↔
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
  constructor
  · exact fun h => h.1
  · intro hcross
    exact ⟨hcross, ReferenceInitializationRun.elapsed_le_T p _⟩

/-- At horizon `T`, `some` retains a terminal crossing and `none` retains
exhaustion. Both remain distinguishable even though their launch round is `T+1`. -/
theorem stoppedObservation_at_horizon
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    stoppedObservation rate rewards C_star C_h source p.T =
      if (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true then
        some (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate),
          fun i => ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) i)
      else none := by
  unfold stoppedObservation
  by_cases hcrossed : stoppedCrossedBy rate rewards C_star C_h source p.T
  · have hcross := (stoppedCrossedBy_at_horizon_iff rate rewards C_star C_h source).mp
      hcrossed
    simp only [hcrossed, hcross, ↓reduceIte]
    rfl
  · have hcross : ¬((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) := by
      intro h
      exact hcrossed
        ((stoppedCrossedBy_at_horizon_iff rate rewards C_star C_h source).mpr h)
    cases hvalue : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome with
    | false =>
        simp only [hcrossed, Bool.false_eq_true, ↓reduceIte]
        rfl
    | true =>
        have hA : stoppedCrossedBy rate rewards C_star C_h source p.T :=
          (stoppedCrossedBy_at_horizon_iff rate rewards C_star C_h source).mpr
            (by rw [hvalue])
        exact False.elim (hcrossed hA)

/-- A crossing at elapsed time `T` and exhaustion both have launch round `T+1`;
the stopped option above still distinguishes their generated outputs. -/
theorem launchRound_eq_horizon_on_terminal_or_exhausted
    (rate : ActiveFollowerDownAcceptance.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) :
    (((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T) →
      ReferenceInitializationRun.launchRound
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) = p.T + 1) ∧
    ((ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = false →
      ReferenceInitializationRun.launchRound
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) = p.T + 1) := by
  constructor
  · rintro ⟨hcross, helapsed⟩
    simp [ReferenceInitializationRun.launchRound, hcross, helapsed]
  · intro hnone
    simp [ReferenceInitializationRun.launchRound, hnone]

end Bandits.Support.ReferenceInitializationControlRemainder

end
