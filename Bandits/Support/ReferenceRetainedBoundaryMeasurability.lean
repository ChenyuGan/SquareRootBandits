/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedActivePrefixFactor
public import Bandits.Support.ReferenceCorrectedLaunchMeasurability
public import Bandits.Support.ReferenceActiveHorizonMeasurability

import Lean.Elab.Tactic.Omega

/-!
# Borel retained incoming boundaries on the original fixed-control remainder

Sources: `sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/06_interruptions.tex:376-423`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

On a fixed selected-row/current-time remainder, this module retains the
original launch-start fibre, its actual corrected seed and active prefix, and
the literal incoming `RoundInput` template. Every source coordinate except
the removed current `TimeControl` remains in the original remainder. This is
deterministic Borel support mathematics; it proves no adaptive law or regret
assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceInitializationControlRemainder
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open scoped Classical

namespace Bandits.Support.ReferenceRetainedBoundaryMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceGeneratedActivePrefixFactor.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Remainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t

variable {p : Parameters}

/-- The literal launch-start event retained inside the original selected-row
and current-time remainder stratum. -/
def retainedLaunchStartSet
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (control0 : TimeControl p) : Set (Remainder p q t) :=
  ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
    ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control0

/-- The actual launch-start stratum, with the measurable space inherited from
the original remainder. -/
abbrev RetainedLaunchStart
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (_hs : s ≤ t.val) (control0 : TimeControl p) :=
  {r : Remainder p q t // r ∈ retainedLaunchStartSet rate rewards C_star C_h q t s control0}

private def generatedLaunchStartFiber
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (s : ℕ) : Set (SourceInput p) :=
  {z | (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s}

/-- On the original selected-row stratum, the baseline launch event is
exactly the generated crossing with elapsed start `s`. This uses both the
accepted fixed-control inverse and the exact event/source characterization. -/
theorem retainedLaunchStart_source_facts
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (r : Remainder p q t)
    (hrem : r ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (hstart : r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control0) :
    let z0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 r
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z0 rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z0 rewards C_star C_h rate)).completed = s := by
  exact ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control0 r hrem s hs hstart

/-- The existing baseline launch event is independent of its reconstruction
control on the original remainder stratum. -/
theorem launchStart_control_independent_on_remainder
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (r : Remainder p q t)
    (hrem : r ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) :
    r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control ↔
    r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control' :=
  ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s r hrem control control'

/-- The launch-start subtype has the inherited Borel structure of the
original fixed-control remainder. -/
theorem measurableSpace_retainedLaunchStart_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    (inferInstance : MeasurableSpace
      (RetainedLaunchStart rate rewards C_star C_h q t s hs control0)) =
      MeasurableSpace.comap Subtype.val inferInstance := rfl

/-- The literal intersection defining the retained set is Borel. Its launch
component is measured by pulling L's complete source fibre through F's
measurable inverse, after identifying it on the selected-row stratum. -/
theorem measurableSet_retainedLaunchStartSet
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    MeasurableSet (retainedLaunchStartSet rate rewards C_star C_h q t s control0) := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let z0 : Remainder p q t → SourceInput p :=
    fun r => ReferenceGeneratedActivePrefixFactor.splitSource q t control0 r
  have hz0 : Measurable z0 := by
    change Measurable (fun r : Remainder p q t => split.symm (control0, r))
    exact split.symm.measurable.comp (measurable_const.prodMk measurable_id)
  have hfiber : MeasurableSet (generatedLaunchStartFiber rate rewards C_star C_h s) := by
    simpa [generatedLaunchStartFiber] using
      ReferenceCorrectedLaunchMeasurability.measurableSet_generated_launch_start_fiber
        rate rewards C_star C_h s
  have hpull : MeasurableSet (z0 ⁻¹' generatedLaunchStartFiber rate rewards C_star C_h s) :=
    hz0 hfiber
  have hstratum := ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
    p q t
  have hset : retainedLaunchStartSet rate rewards C_star C_h q t s control0 =
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t ∩
        z0 ⁻¹' generatedLaunchStartFiber rate rewards C_star C_h s := by
    ext r
    constructor
    · rintro ⟨hrem, hstart⟩
      exact ⟨hrem, retainedLaunchStart_source_facts rate rewards C_star C_h q t s
        hs control0 r hrem hstart⟩
    · rintro ⟨hrem, hfacts⟩
      have hindex : ActualInitializationPhysicalStep.selectedRowIndex p (z0 r) = q := by
        calc
          ActualInitializationPhysicalStep.selectedRowIndex p (z0 r) =
              ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (z0 r) :=
            (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
              p (z0 r)).symm
          _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
            p q t control0 r hrem
      have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t (z0 r) =
          (control0, r) := by
        change split (split.symm (control0, r)) = (control0, r)
        exact split.apply_symm_apply (control0, r)
      have hiff := ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control0 (z0 r) hindex s hs
      have hstart : r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
          rate rewards C_star C_h q t s control0 := by
        have hmem := hiff.mpr hfacts
        rw [hsplit] at hmem
        exact hmem
      exact ⟨hrem, hstart⟩
  rw [hset]
  exact hstratum.inter hpull

/-- The source-derived corrected seed on the retained subtype. Its option
payload is the actual value of the accepted corrected-launch constructor. -/
def retainedGeneratedActiveSeed
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalStep.State p rate :=
  ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2

universe u

private theorem option_get_mem_iff_sum_inl
    {α : Type u} (o : Option α) (ho : o.isSome = true) (u : Set α) :
    o.get ho ∈ u ↔
      Equiv.optionEquivSumPUnit.{u, u} α o ∈ Sum.inl '' u := by
  cases o with
  | none => simp at ho
  | some a => simp [Equiv.optionEquivSumPUnit]

private theorem measurable_option_get_of_isSome
    {Ω : Type*} {α : Type u} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : Ω → Option α) (hf : Measurable f)
    (hsome : ∀ x, (f x).isSome = true) :
    Measurable (fun x => (f x).get (hsome x)) := by
  let optionSumEquiv : Option α ≃ α ⊕ PUnit.{u + 1} :=
    Equiv.optionEquivSumPUnit.{u, u} α
  have hsum : Measurable (fun x => optionSumEquiv (f x)) := by
    change Measurable (fun x => Equiv.optionEquivSumPUnit.{u, u} α (f x))
    exact measurable_comap_iff.mp hf
  intro u hu
  have hsumset : MeasurableSet ((Sum.inl : α → α ⊕ PUnit.{u + 1}) '' u) :=
    MeasurableSet.inl_image hu
  have hpre := hsum hsumset
  have hpreEq : (fun x => (f x).get (hsome x)) ⁻¹' u =
      (fun x => optionSumEquiv (f x)) ⁻¹' (Sum.inl '' u) := by
    ext x
    exact option_get_mem_iff_sum_inl (f x) (hsome x) u
  rw [hpreEq]
  exact hpre

/-- The actual G seed is Borel on the retained launch-start subtype. The
proof extracts `Option.get` only after the retained crossing establishes the
nonempty branch, using L's Borel map into the existing Option code. -/
theorem measurable_retainedGeneratedActiveSeed
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (retainedGeneratedActiveSeed rate rewards C_star C_h q t s hs control0) := by
  let source := fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hsource : Measurable source := by
    change Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm (control0, x.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk (measurable_subtype_coe))
  let launchCode := fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
    (ReferenceCorrectedInitializationLaunch.correctedLaunch rate (source x) rewards C_star C_h).map
      (ReferenceActivePhysicalStepMeasurability.encodeState (p := p) (rate := rate))
  have hlaunchCode : Measurable launchCode := by
    exact (ReferenceCorrectedLaunchMeasurability.measurable_correctedLaunch_encodeState
      rate rewards C_star C_h).comp hsource
  have hsome : ∀ x, (launchCode x).isSome = true := by
    intro x
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (source x) rewards C_star C_h = some
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2) := by
      simpa [source] using (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).1
    simp [launchCode, hlaunch]
  have hget : Measurable (fun x => (launchCode x).get (hsome x)) :=
    measurable_option_get_of_isSome launchCode hlaunchCode hsome
  have hgetEq : (fun x => (launchCode x).get (hsome x)) =
      fun x => ReferenceActivePhysicalStepMeasurability.encodeState
        (retainedGeneratedActiveSeed rate rewards C_star C_h q t s hs control0 x) := by
    funext x
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (source x) rewards C_star C_h = some
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
            rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2) := by
      simpa [source] using (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
        rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).1
    simp [launchCode, retainedGeneratedActiveSeed, hlaunch]
  have hencoded : Measurable (fun x =>
      ReferenceActivePhysicalStepMeasurability.encodeState
        (retainedGeneratedActiveSeed rate rewards C_star C_h q t s hs control0 x)) := by
    rw [← hgetEq]
    exact hget
  exact measurable_comap_iff.mpr hencoded

/-- Borel measurability of the actual retained prefix's final state, by
composing H's finite-fold producer on the true all-active run input. -/
theorem measurable_retainedPrefixFinalState
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s (t.val - s) hs x.2.2
        (by omega)).finalState) := by
  let source := fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let seed := retainedGeneratedActiveSeed rate rewards C_star C_h q t s hs control0
  let selected := fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
    ActualInitializationPhysicalStep.selectedRowIndex p (source x)
  have hsource : Measurable source := by
    change Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm (control0, x.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hseed : Measurable seed :=
    measurable_retainedGeneratedActiveSeed rate rewards C_star C_h q t s hs control0
  have hselected : Measurable selected := by
    have heq : selected = fun _ : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 => q := by
      funext x
      calc
        ActualInitializationPhysicalStep.selectedRowIndex p (source x) =
            ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source x) :=
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
            p (source x)).symm
        _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
          p q t control0 x.1 x.2.1
    rw [heq]
    exact measurable_const
  have hrows : Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (source x).1.2) := measurable_snd.comp (measurable_fst.comp hsource)
  let mode := fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
    (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
      rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  have hdata : Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (seed x, ((source x).1.2, (selected x, rewards)))) :=
    hseed.prodMk (hrows.prodMk (hselected.prodMk measurable_const))
  let runInput : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 →
      ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s :=
    fun x => ⟨(seed x, ((source x).1.2, (selected x, rewards))), mode x⟩
  have hrunInput : Measurable runInput := hdata.subtype_mk
  have hcount : s + (t.val - s) ≤ t.val := by omega
  have hspan : s + (t.val - s) ≤ p.T := by omega
  have hrunFinal := (ReferenceActiveHorizonMeasurability.measurable_runFinalState
    (p := p) (rate := rate) s (t.val - s) hspan).comp hrunInput
  have heq : (fun x =>
      (ReferenceActiveHorizonMeasurability.runOfInput (p := p) (rate := rate)
        s (t.val - s) hspan (runInput x)).finalState) =
    (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s (t.val - s) hs x.2.2
        hcount).finalState) := by
    funext x
    rfl
  rw [← heq]
  exact hrunFinal

/-- The literal fixed-baseline incoming boundary template. Its state is the
same generated prefix final state; its rows and private selected index are
those of the reconstructed original source, and it retains the whole reward
table. -/
def retainedIncomingBoundary
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    ReferenceActivePhysicalStep.RoundInput p rate := by
  let z0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2).2.1
  let count := t.val - s
  let hcount : s + count ≤ t.val := by omega
  let hspan : s + count ≤ p.T := by omega
  let hsum : s + count = t.val := by omega
  have hmodeEnd : ReferenceActivePhysicalHorizon.allActiveAtStart
      ((ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s count hs x.2.2 hcount).finalState)
      t.val := by
    rw [← hsum]
    exact ReferenceActivePhysicalHorizon.run_allActiveAtEnd seed z0.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z0) rewards s count hspan hmode
  exact {
    state := (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
      rate rewards C_star C_h q t control0 x.1 x.2.1 s count hs x.2.2 hcount).finalState
    rows := z0.1.2
    selected := ActualInitializationPhysicalStep.selectedRowIndex p z0
    time := t
    active := hmodeEnd
    rewards := rewards
  }

@[simp] theorem retainedIncomingBoundary_state
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x).state =
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s (t.val - s) hs x.2.2
        (by omega)).finalState := rfl

@[simp] theorem retainedIncomingBoundary_time
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x).time = t := rfl

@[simp] theorem retainedIncomingBoundary_rows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x).rows =
      (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1).1.2 := rfl

@[simp] theorem retainedIncomingBoundary_selected
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x).selected =
      ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) := rfl

@[simp] theorem retainedIncomingBoundary_selected_eq_q
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0) :
    (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x).selected = q := by
  rw [retainedIncomingBoundary_selected]
  calc
    ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) =
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1) :=
      (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
        p (ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1)).symm
    _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.1 x.2.1

/-- The boundary template is Borel in the existing canonical `RoundInput`
comap/product space. The active proof is derived from the actual fold's
activation preservation at `s + (t-s) = t`. -/
theorem measurable_retainedIncomingBoundary
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0) := by
  let boundary := retainedIncomingBoundary rate rewards C_star C_h q t s hs control0
  let source := fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
    ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  have hsource : Measurable source := by
    change Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm (control0, x.1))
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm.measurable.comp
      (measurable_const.prodMk measurable_subtype_coe)
  have hstate : Measurable (fun x => (boundary x).state) := by
    simpa [boundary, retainedIncomingBoundary_state] using
      measurable_retainedPrefixFinalState rate rewards C_star C_h q t s hs control0
  have hrows : Measurable (fun x => (boundary x).rows) := by
    change Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      (source x).1.2)
    exact measurable_snd.comp (measurable_fst.comp hsource)
  have hselected : Measurable (fun x => (boundary x).selected) := by
    have heq : (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
        (boundary x).selected) = fun _ => q := by
      funext x
      change ActualInitializationPhysicalStep.selectedRowIndex p (source x) = q
      calc
        ActualInitializationPhysicalStep.selectedRowIndex p (source x) =
            ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source x) :=
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
            p (source x)).symm
        _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
          p q t control0 x.1 x.2.1
    rw [heq]
    exact measurable_const
  have hcoordinates : Measurable (fun x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0 =>
      ((boundary x).state,
        ((boundary x).rows,
          ((boundary x).selected, ((boundary x).time, (boundary x).rewards))))) := by
    exact hstate.prodMk (hrows.prodMk (hselected.prodMk
      ((measurable_const : Measurable (fun _ : RetainedLaunchStart
        rate rewards C_star C_h q t s hs control0 => t)).prodMk measurable_const)))
  have hencoded : Measurable (fun x =>
      ReferenceActivePhysicalStepMeasurability.encodeRoundInput (boundary x)) := by
    exact hcoordinates.subtype_mk (h := fun x => (boundary x).active)
  change Measurable (fun x => boundary x)
  exact measurable_comap_iff.mpr hencoded

/-- The actual next input computed after changing only the removed current
control. The seed, all-active mode, run and calendar input are all generated
from that reconstructed original source. -/
def retainedGeneratedNextInput
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) : ReferenceActivePhysicalStep.RoundInput p rate := by
  let remainder := x.1
  let hrem := x.2.1
  let hstart0 := x.2.2
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s remainder hrem control0 control).mp hstart0
  let zu := ReferenceGeneratedActivePrefixFactor.splitSource q t control remainder
  let seed := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t control remainder hrem s hs hstart
  let hmode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control remainder hrem s hs hstart).2.1
  let count := t.val - s
  let hspan : s + count ≤ p.T := by omega
  let acc := ReferenceActivePhysicalHorizon.run seed zu.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p zu) rewards s count hspan hmode
  exact ReferenceActivePhysicalHorizon.roundInputAt seed zu.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p zu) rewards s hmode acc
    ⟨t.val, by constructor <;> omega⟩

private theorem roundInput_ext
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

/-- For each control, the actual next active input is the fixed baseline
boundary with every original row and the original private selected index
restored from that reconstructed source. -/
theorem retainedGeneratedNextInput_eq_roundInputAtSource
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStart rate rewards C_star C_h q t s hs control0)
    (control : TimeControl p) :
    retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 x control =
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x)
        (ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1) := by
  let hstart0 := x.2.2
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.1 x.2.1 control0 control).mp hstart0
  have hprefix := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
    rate rewards C_star C_h q t x.1 x.2.1 control0 s (t.val - s) hs
    (by omega) hstart0 control control0
  rcases hprefix with ⟨active, _, _, _, _, _, hstate, _⟩
  let zu := ReferenceGeneratedActivePrefixFactor.splitSource q t control x.1
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p zu = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p zu =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p zu :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p zu).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control x.1 x.2.1
  have hsourceSelected : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p zu = q := by
    rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact hselected
  have hstate' : (retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 x
      control).state = (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x).state := by
    change (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control x.1 x.2.1 s (t.val - s) hs hstart
        (by omega)).finalState =
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0 x.1 x.2.1 s (t.val - s) hs hstart0
        (by omega)).finalState
    exact hstate
  apply roundInput_ext
  · exact hstate'
  · rfl
  · exact hselected.trans hsourceSelected.symm
  · rfl
  · rfl

/-- Package an actual original source into the retained subtype when its own
selected index, generated crossing and elapsed start identify the branch.
The current source control may differ from the baseline reconstruction. -/
def retainedLaunchStartInputOfSource
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    RetainedLaunchStart rate rewards C_star C_h q t s hs control0 := by
  let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let r := (split z).2
  have hrem : r ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
    change PrivateSourceStreams.coordinatorIndex p r.2.1.2 = q
    have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z = q := by
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    change PrivateSourceStreams.coordinatorIndex p (split z).2.2.1.2 = q
    rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private]
    exact hindex
  let control := (split z).1
  have hstart : r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control := by
    apply (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
      rate rewards C_star C_h q t control z hselected s hs).2
    exact ⟨hcross, helapsed⟩
  have hstart0 : r ∈ ReferenceInitializationControlRemainder.launchStartRemainderEvent
      rate rewards C_star C_h q t s control0 :=
    (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
      rate rewards C_star C_h q t s r hrem control control0).mp hstart
  exact ⟨r, hrem, hstart0⟩

/-- The actual-source selector has the original fixed-control remainder as
its value. -/
theorem retainedLaunchStartInputOfSource_val
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    (retainedLaunchStartInputOfSource rate rewards C_star C_h q t s hs control0
      z hselected hcross helapsed : Remainder p q t) =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2 := rfl

/-- The original source remainder belongs to the literal retained launch
stratum, including when its current control differs from the baseline. -/
theorem retainedLaunchStartInputOfSource_mem
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2 ∈
      retainedLaunchStartSet rate rewards C_star C_h q t s control0 := by
  let x := retainedLaunchStartInputOfSource rate rewards C_star C_h q t s hs control0
    z hselected hcross helapsed
  have hx : x.1 ∈ retainedLaunchStartSet rate rewards C_star C_h q t s control0 := x.2
  rw [← retainedLaunchStartInputOfSource_val rate rewards C_star C_h q t s hs control0
    z hselected hcross helapsed]
  exact hx

/-- Specializing the computed next input to an actual source gives the same
incoming input after literally restoring its whole rows and original J. -/
theorem retainedGeneratedNextInput_eq_of_source
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s) :
    let x := retainedLaunchStartInputOfSource rate rewards C_star C_h q t s hs control0
      z hselected hcross helapsed
    retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 x
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1) =
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
      (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x) z := by
  let x := retainedLaunchStartInputOfSource rate rewards C_star C_h q t s hs control0
    z hselected hcross helapsed
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1) x.1 = z := by
    change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1,
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2) = z
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t z
  change retainedGeneratedNextInput rate rewards C_star C_h q t s hs control0 x
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1) =
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
      (retainedIncomingBoundary rate rewards C_star C_h q t s hs control0 x) z
  rw [retainedGeneratedNextInput_eq_roundInputAtSource rate rewards C_star C_h q t s hs
    control0 x ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1)]
  rw [hsource]

end Bandits.Support.ReferenceRetainedBoundaryMeasurability

end
