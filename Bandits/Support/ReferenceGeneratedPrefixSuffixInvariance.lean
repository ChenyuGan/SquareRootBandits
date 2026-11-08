/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceRetainedAssignmentReleaseHistory

import Lean.Elab.Tactic.Omega

/-!
# Strict-past generated-prefix invariance under selected-row suffix replacement

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The literal update below changes every selected-row control from the incoming
time onward while retaining the original private coordinates, including the
selected-row scalar. The results in this module concern only actual corrected
launches and strict-past physical states and chronological evidence. They do
not assert independence, a probability law, or filtration measurability.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceGeneratedActivePrefixFactor
open Bandits.Support.ReferenceRetainedAssignmentReleaseHistory
open Bandits.Support.ReferenceRetainedBoundaryMeasurability
open Bandits.Support.ReferenceInitializationControlRemainder
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceInitializationStoppedLocality
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceRetainedAssignmentReleaseHistory.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

/-- Replace the whole selected-row control suffix in the original source.
The selected row is still chosen by the unchanged original private scalar. -/
def replaceSelectedControlSuffix (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) : SourceInput p :=
  ((source.1.1,
      Function.update source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)
        ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1,
          fun v => if v.val < t.val then
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v
          else suffix v)),
    source.2)

theorem replaceSelectedControlSuffix_id (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) :
    (replaceSelectedControlSuffix source t suffix).1.1 = source.1.1 := rfl

theorem replaceSelectedControlSuffix_private (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) :
    (replaceSelectedControlSuffix source t suffix).2 = source.2 := rfl

theorem replaceSelectedControlSuffix_selected (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) :
    ActualInitializationPhysicalStep.selectedRowIndex p
      (replaceSelectedControlSuffix source t suffix) =
    ActualInitializationPhysicalStep.selectedRowIndex p source := rfl

theorem replaceSelectedControlSuffix_forward (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) :
    ((replaceSelectedControlSuffix source t suffix).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 =
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 := by
  simp [replaceSelectedControlSuffix]

theorem replaceSelectedControlSuffix_otherRow (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) (j : Fin (M p))
    (hne : j ≠ ActualInitializationPhysicalStep.selectedRowIndex p source) :
    (replaceSelectedControlSuffix source t suffix).1.2 j = source.1.2 j := by
  simp [replaceSelectedControlSuffix, hne]

theorem replaceSelectedControlSuffix_control_before (source : SourceInput p)
    (t v : Fin p.T) (suffix : Fin p.T → TimeControl p) (hv : v.val < t.val) :
    ((replaceSelectedControlSuffix source t suffix).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v =
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v := by
  dsimp only [replaceSelectedControlSuffix]
  rw [Function.update_self]
  simp [hv]

theorem replaceSelectedControlSuffix_control_from (source : SourceInput p)
    (t v : Fin p.T) (suffix : Fin p.T → TimeControl p) (hv : t.val ≤ v.val) :
    ((replaceSelectedControlSuffix source t suffix).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v = suffix v := by
  dsimp only [replaceSelectedControlSuffix]
  rw [Function.update_self]
  have hnot : ¬ v.val < t.val := by omega
  simp [hnot]

/-- Replacing a suffix by the source's own selected-row controls leaves the
original source unchanged. -/
theorem replaceSelectedControlSuffix_same_source (source : SourceInput p)
    (t : Fin p.T) :
    replaceSelectedControlSuffix source t
      (fun v => (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v) =
      source := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext j
      by_cases hj : j = ActualInitializationPhysicalStep.selectedRowIndex p source
      · subst j
        dsimp only [replaceSelectedControlSuffix]
        rw [Function.update_self]
        congr 1
        funext v
        split_ifs <;> rfl
      · simp [replaceSelectedControlSuffix]
  · rfl

private theorem correctedLaunch_eq_of_initialization_reads
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (leftSource rightSource : SourceInput p)
    (hleft : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)).crossing.isSome = true)
    (hright : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)).crossing.isSome = true)
    (hboundary : ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate) =
      ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate))
    (hordinary : ∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)) i =
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)) i) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate leftSource rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate rightSource rewards C_star C_h := by
  obtain ⟨left, hleftSpec, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate leftSource rewards C_star C_h hleft
  obtain ⟨right, hrightSpec, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate rightSource rewards C_star C_h hright
  rcases hleftSpec with ⟨hleftLaunch, hleftCoordinator, hleftBank, hleftActivations,
    hleftFollowers⟩
  rcases hrightSpec with ⟨hrightLaunch, hrightCoordinator, hrightBank, hrightActivations,
    hrightFollowers⟩
  have hcoordinator : left.coordinator = right.coordinator :=
    hleftCoordinator.trans hrightCoordinator.symm
  have hbank : left.upDecoderBank = right.upDecoderBank :=
    hleftBank.trans hrightBank.symm
  have hactivations : left.activations = right.activations := by
    funext i
    apply Option.some.inj
    calc
      some (left.activations i) =
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)).activation
              (ActualReferenceInitializationBlock.refFollower i) := hleftActivations i
      _ = (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)).activation
              (ActualReferenceInitializationBlock.refFollower i) :=
        congrArg (fun b : ReferenceInitializationRun.Boundary p =>
          b.activation (ActualReferenceInitializationBlock.refFollower i)) hboundary
      _ = some (right.activations i) := (hrightActivations i).symm
  have hfollowers : left.followers = right.followers := by
    funext i
    calc
      left.followers i = .ordinary
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) := hleftFollowers i
      _ = .ordinary
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i))
          (ActiveFollowerLifecycle.initialMemory p) :=
        congrArg (fun state => DeclaredFollowerLocalRound.LocalConfiguration.ordinary
          state (ActiveFollowerLifecycle.initialMemory p)) (hordinary i)
      _ = right.followers i := (hrightFollowers i).symm
  have hstate : left = right := by
    cases left with
    | mk lc lb la lf =>
      cases right with
      | mk rc rb ra rf =>
        have hc : lc = rc := hcoordinator
        have hb : lb = rb := hbank
        have ha : la = ra := hactivations
        have hf : lf = rf := hfollowers
        cases hc
        cases hb
        cases ha
        cases hf
        rfl
  calc
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate leftSource rewards C_star C_h =
        some left := hleftLaunch
    _ = some right := congrArg some hstate
    _ = ReferenceCorrectedInitializationLaunch.correctedLaunch rate rightSource rewards C_star C_h :=
      hrightLaunch.symm

private theorem replaceSelectedControlSuffix_initialization
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → TimeControl p) (s : ℕ) (hs : s ≤ t.val)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s) :
    let source' := replaceSelectedControlSuffix source t suffix
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).completed = s ∧
    ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) =
    ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate) ∧
    (∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) i =
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i) ∧
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h := by
  dsimp only
  let source' := replaceSelectedControlSuffix source t suffix
  have hids : source.1.1 = source'.1.1 :=
    (replaceSelectedControlSuffix_id source t suffix).symm
  have hprivate : source.2 = source'.2 :=
    (replaceSelectedControlSuffix_private source t suffix).symm
  have hforward : ∀ v : Fin p.T, v.val < t.val →
      ∀ a : Fin (BootstrapDimensions.A_id p),
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 a v =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).1 a v := by
    intro v hv a
    exact congrArg (fun row : CompletePublicTable.ForwardRow p => row a v)
      (replaceSelectedControlSuffix_forward source t suffix).symm
  have hcontrol : ∀ v : Fin p.T, v.val < t.val →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v := by
    intro v hv
    exact (replaceSelectedControlSuffix_control_before source t v suffix hv).symm
  have hby : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ t.val := by
    rw [helapsed]
    exact hs
  have hcalendar :=
    ReferenceInitializationStoppedLocality.source_calendar_stopped_output_eq_of_event
      rate rewards C_star C_h source source' t.val (Nat.le_of_lt t.isLt)
      hids hprivate hforward hcontrol (Or.inl ⟨hcross, hby⟩)
  rcases hcalendar with ⟨_, hboundary, _, _, hord, _⟩
  have hcross' : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).crossing.isSome = true := by
    have h := congrArg (fun b : ReferenceInitializationRun.Boundary p => b.crossing.isSome) hboundary
    exact h.symm.trans hcross
  have helapsed' : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).completed = s := by
    have h := congrArg (fun b : ReferenceInitializationRun.Boundary p =>
      ReferenceInitializationRun.elapsed p b.completed) hboundary
    exact h.symm.trans helapsed
  exact ⟨hcross', helapsed', hboundary, hord,
    correctedLaunch_eq_of_initialization_reads rewards C_star C_h source source'
      hcross hcross' hboundary hord⟩

/-- A successful corrected launch at elapsed time `s` stays the same launch,
including its complete corrected seed, after replacing the selected-row suffix
starting at any `t` with `s ≤ t`. -/
theorem replaceSelectedControlSuffix_preserves_actual_launch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (source : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (suffix : Fin p.T → TimeControl p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s) :
    let source' := replaceSelectedControlSuffix source t suffix
    ActualInitializationPhysicalStep.selectedRowIndex p source' = q ∧
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).completed = s ∧
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h := by
  dsimp only
  have hlaunch := replaceSelectedControlSuffix_initialization
    (rate := rate) rewards C_star C_h source t suffix s hs hcross helapsed
  rcases hlaunch with ⟨hcross', helapsed', _, _, hseed⟩
  exact ⟨(replaceSelectedControlSuffix_selected source t suffix).trans hselected,
    hcross', helapsed', hseed⟩

/-- On an actual retained launch stratum, replacing the entire selected-row
control suffix produces another member of the actual retained launch domain,
with the same corrected seed and every strict-past state and chronological
evidence coordinate unchanged. The universal index is bounded exactly by
`s + k ≤ t.val`; no row-bearing record equality is asserted. -/
theorem retainedGeneratedPrefix_suffix_invariant
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs control0)
    (suffix : Fin p.T → TimeControl p) :
    let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
    let source' := replaceSelectedControlSuffix source t suffix
    ∃ x' : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs (suffix t),
      x'.val = (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source').2 ∧
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
        control0 x.1 x.2.1 s hs x.2.2 =
      ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
        (suffix t) x'.1 x'.2.1 s hs x'.2.2 ∧
      ∀ k : Fin (t.val - s + 1),
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          k.val (by have hk := k.isLt; omega)).finalState =
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs (suffix t) x' (suffix t)
          k.val (by have hk := k.isLt; omega)).finalState ∧
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
          k.val (by have hk := k.isLt; omega)).records.map RoundRecord.evidence =
        (retainedGeneratedPrefix rate rewards C_star C_h q t s hs (suffix t) x' (suffix t)
          k.val (by have hk := k.isLt; omega)).records.map RoundRecord.evidence := by
  dsimp only
  let source := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.1
  let source' := replaceSelectedControlSuffix source t suffix
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q := by
    calc
      ActualInitializationPhysicalStep.selectedRowIndex p source =
          ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source :=
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex
          p source).symm
      _ = q := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
        p q t control0 x.1 x.2.1
  have hbranch := ReferenceGeneratedActivePrefixFactor.launchStart_source_facts
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  have hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [source] using hbranch.1
  have helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
    simpa [source] using hbranch.2
  have hinit := replaceSelectedControlSuffix_initialization
    (rate := rate) rewards C_star C_h source t suffix s hs hcross helapsed
  rcases hinit with ⟨hcross', helapsed', hboundary, hord, hlaunch⟩
  have hselected' : ActualInitializationPhysicalStep.selectedRowIndex p source' = q := by
    rw [replaceSelectedControlSuffix_selected, hselected]
  let x' : RetainedLaunchStartInput (p := p) rate rewards C_star C_h q t s hs (suffix t) :=
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
      rate rewards C_star C_h q t s hs (suffix t) source' hselected' hcross' helapsed'
  have hxval : x'.val =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source').2 :=
    ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
      rate rewards C_star C_h q t s hs (suffix t) source' hselected' hcross' helapsed'
  have hsplit : ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source' =
      (suffix t, x'.val) := by
    apply Prod.ext
    · calc
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source').1 =
            (source'.1.2 q).2 t :=
          ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_control p q t source'
        _ = (source'.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source')).2 t := by
          rw [← hselected']
        _ = suffix t := replaceSelectedControlSuffix_control_from source t t suffix (by omega)
    · exact hxval.symm
  have hsource' : ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.val = source' := by
    dsimp [ReferenceGeneratedActivePrefixFactor.splitSource]
    calc
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (suffix t, x'.val) =
        (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
          (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source') := by
            rw [hsplit]
      _ = source' :=
        ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_reconstruct p q t source'
  let active := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
    q t control0 x.1 x.2.1 s hs x.2.2
  let active' := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h
    q t (suffix t) x'.1 x'.2.1 s hs x'.2.2
  have hspec := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.1 x.2.1 s hs x.2.2
  have hspec' := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t (suffix t) x'.1 x'.2.1 s hs x'.2.2
  have hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart active' s := hspec'.2.1
  have hlaunchOld : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some active := by
    simpa [active, source] using hspec.1
  have hlaunchNew : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h =
      some active' := by
    simpa [active, hsource'] using hspec'.1
  have hactive : active = active' := Option.some.inj <| by
    calc
      some active = ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h :=
        hlaunchOld.symm
      _ = ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h := hlaunch
      _ = some active' := hlaunchNew
  refine ⟨x', hxval, hactive, ?_⟩
  intro k
  let count := k.val
  have hcount : s + count ≤ t.val := by
    have hk := k.isLt
    omega
  have hspan : s + count ≤ p.T := hcount.trans (Nat.le_of_lt t.isLt)
  let leftInitial : {u : ReferenceActivePhysicalHorizon.State p rate //
      ReferenceActivePhysicalHorizon.allActiveAtStart u s} := ⟨active', hmode'⟩
  let rightInitial : {u : ReferenceActivePhysicalHorizon.State p rate //
      ReferenceActivePhysicalHorizon.allActiveAtStart u s} := ⟨active, hspec.2.1⟩
  have hinitial : leftInitial = rightInitial := by
    apply Subtype.ext
    exact hactive.symm
  have hrightRunState :
      (ReferenceActivePhysicalHorizon.run active' source'.1.2 q rewards s count hspan
        hmode').finalState =
        (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspan
          hspec.2.1).finalState := by
    exact congrArg (fun initial : {u : ReferenceActivePhysicalHorizon.State p rate //
        ReferenceActivePhysicalHorizon.allActiveAtStart u s} =>
      (ReferenceActivePhysicalHorizon.run initial.val source'.1.2 q rewards s count hspan
        initial.property).finalState) hinitial
  have hrightRunEvidence :
      (ReferenceActivePhysicalHorizon.run active' source'.1.2 q rewards s count hspan
        hmode').records.map RoundRecord.evidence =
        (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspan
          hspec.2.1).records.map RoundRecord.evidence := by
    exact congrArg (fun initial : {u : ReferenceActivePhysicalHorizon.State p rate //
        ReferenceActivePhysicalHorizon.allActiveAtStart u s} =>
      (ReferenceActivePhysicalHorizon.run initial.val source'.1.2 q rewards s count hspan
        initial.property).records.map RoundRecord.evidence) hinitial
  have hcontrols : ∀ j : Fin p.T, s ≤ j.val → j.val < s + count →
      (source.1.2 q).2 j = (source'.1.2 q).2 j := by
    intro j hstart hend
    have hjt : j.val < t.val := by omega
    rw [← hselected]
    exact (replaceSelectedControlSuffix_control_before source t j suffix hjt).symm
  have hrewards : ∀ j : Fin p.T, s ≤ j.val → j.val < s + count →
      rewards j = rewards j := fun _ _ _ => rfl
  have hbefore : 0 < count → ∀ j : Fin p.T, j.val < s →
      ((source.1.2 q).2 j).1 ContinuousControlSlice.Label.prop =
        ((source'.1.2 q).2 j).1 ContinuousControlSlice.Label.prop := by
    intro hpositive j hj
    have hjt : j.val < t.val := by omega
    rw [← hselected]
    exact congrArg (fun u : TimeControl p =>
      u.1 ContinuousControlSlice.Label.prop)
      ((replaceSelectedControlSuffix_control_before source t j suffix hjt).symm)
  have hrun := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
    active source.1.2 source'.1.2 q rewards rewards s count hspan hspec.2.1
    hcontrols hrewards hbefore
  have hleftState :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
        count hcount).finalState =
      (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspan
        hspec.2.1).finalState := by
    change (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        hspec.2.1).finalState =
      (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspan
        hspec.2.1).finalState
    rw [hselected]
  have hleftEvidence :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs control0 x control0
        count hcount).records.map RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspan
        hspec.2.1).records.map RoundRecord.evidence := by
    change (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        hspec.2.1).records.map RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run active source.1.2 q rewards s count hspan
        hspec.2.1).records.map RoundRecord.evidence
    rw [hselected]
  have hrightState :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs (suffix t) x' (suffix t)
        count hcount).finalState =
      (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspan
        hspec.2.1).finalState := by
    change (ReferenceActivePhysicalHorizon.run active'
        (ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.1).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.1))
        rewards s count hspan hmode').finalState =
      (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspan
        hspec.2.1).finalState
    rw [hsource', hselected']
    exact hrightRunState
  have hrightEvidence :
      (retainedGeneratedPrefix rate rewards C_star C_h q t s hs (suffix t) x' (suffix t)
        count hcount).records.map RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspan
        hspec.2.1).records.map RoundRecord.evidence := by
    change (ReferenceActivePhysicalHorizon.run active'
        (ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.1).1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p
          (ReferenceGeneratedActivePrefixFactor.splitSource q t (suffix t) x'.1))
        rewards s count hspan hmode').records.map RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run active source'.1.2 q rewards s count hspan
        hspec.2.1).records.map RoundRecord.evidence
    rw [hsource', hselected']
    exact hrightRunEvidence
  exact ⟨hleftState.trans (hrun.1.trans hrightState.symm),
    hleftEvidence.trans (hrun.2.trans hrightEvidence.symm)⟩

end Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance
