/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationControlRemainder
public import Bandits.Support.ReferenceCorrectedInitializationLaunch
public import Bandits.Support.ReferenceActiveTemporalAssembly

import Lean.Elab.Tactic.Omega

/-!
# Generated canonical seeds and incoming active prefixes on a fixed-control fibre

Sources: `sources/zip4/manuscript/07_public_setup.tex:121-164`,
`sources/zip4/manuscript/06_interruptions.tex:197-209,235-297,376-423`,
`sources/zip4/manuscript/08_main_theorem.tex:29-42`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.

On the literal generated launch-start event, this module factors the actual
corrected launch state and the existing physical incoming-prefix run through
the admitted original-source fixed-control remainder. The factor is defined
only on that event; it asserts no measurability or probability statement.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceInitializationControlRemainder
open Bandits.Support.ReferenceCorrectedInitializationLaunch
open Bandits.Support.ReferenceActivePhysicalHorizon
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedActivePrefixFactor

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceCorrectedInitializationLaunch.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Remainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t

variable {p : Parameters}

def splitSource (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t) : SourceInput p :=
  (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm
    (control, remainder)

private theorem splitSource_index (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t) :
    ActualInitializationPhysicalStep.selectedRowIndex p
      (splitSource q t control remainder) = q := by
  have hindex := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
    p q t control remainder hremainder
  rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  exact hindex

private theorem splitSource_replacement (q : Fin (M p)) (t : Fin p.T)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control control' : TimeControl p) :
    splitSource q t control' remainder =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (splitSource q t control remainder) control' := by
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  let source := e.symm (control, remainder)
  have hindex := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
    p q t control remainder hremainder
  have hreplace := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
    p q t source control' hindex
  have hrem : (e source).2 = remainder := by
    exact congrArg Prod.snd (e.apply_symm_apply (control, remainder))
  calc
    e.symm (control', remainder) = e.symm (control', (e source).2) := by rw [hrem]
    _ = ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control' :=
      hreplace

/-- The accepted launch-start event is exactly the original-source generated
crossing with elapsed boundary `s`. -/
theorem launchStart_source_facts
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (s : ℕ) (hs : s ≤ t.val)
    (hstart : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control) :
    let source := splitSource q t control remainder
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s := by
  let source := splitSource q t control remainder
  have hindex := splitSource_index q t control remainder hremainder
  let e := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
  have hsplit : e source = (control, remainder) := e.apply_symm_apply (control, remainder)
  have hstart' : (e source).2 ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control := by
    rw [hsplit]
    exact hstart
  exact (launchStartRemainderEvent_iff_source rate rewards C_star C_h q t control
    source hindex s hs).mp hstart'

/-- The actual corrected launch state on the inverse source of a launch-start
fibre. The value is obtained from C's nonempty `correctedLaunch` option. -/
def generatedActiveSeed
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (s : ℕ) (hs : s ≤ t.val)
    (hstart : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control) :
    ReferenceActivePhysicalStep.State p rate := by
  let source := splitSource q t control remainder
  have hc := (launchStart_source_facts rate rewards C_star C_h q t control remainder
    hremainder s hs hstart).1
  exact (ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h).get
    ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).2 hc)

private theorem generatedActiveSeed_eq_of_launch
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (s : ℕ) (hs : s ≤ t.val)
    (hstart : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      (splitSource q t control remainder) rewards C_star C_h = some active) :
    generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart =
      active := by
  unfold generatedActiveSeed
  dsimp only
  simp [hlaunch]

/-- C's exact constructor produces the canonical seed, its all-active mode at
the generated elapsed start, and the existing DOWN-batch seed. -/
theorem generatedActiveSeed_spec
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (s : ℕ) (hs : s ≤ t.val)
    (hstart : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control) :
    let source := splitSource q t control remainder
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      some (generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart) ∧
    ReferenceActivePhysicalHorizon.allActiveAtStart
      (generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart) s ∧
    ReferenceFollowerDecoderChronology.downBatchSeed
      (generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart) s := by
  let source := splitSource q t control remainder
  obtain ⟨hc, helapsed⟩ := launchStart_source_facts rate rewards C_star C_h q t control
    remainder hremainder s hs hstart
  obtain ⟨active, hchar, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate source rewards C_star C_h hc
  rcases hchar with ⟨hlaunch, _, _, _, _⟩
  have hseed : generatedActiveSeed rate rewards C_star C_h q t control remainder
      hremainder s hs hstart = active :=
    generatedActiveSeed_eq_of_launch rate rewards C_star C_h q t control remainder
      hremainder s hs hstart active hlaunch
  obtain ⟨activeMode, hlaunchMode, hmode⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_all_active_at_start
      rate source rewards C_star C_h hc
  have hmodeEq : activeMode = active := Option.some.inj (hlaunchMode.symm.trans hlaunch)
  subst activeMode
  obtain ⟨activeSeed, hlaunchSeed, hdown⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_downBatchSeed
      rate source rewards C_star C_h hc
  have hseedEq : activeSeed = active := Option.some.inj (hlaunchSeed.symm.trans hlaunch)
  subst activeSeed
  refine ⟨?_, ?_, ?_⟩
  · simpa [hseed] using hlaunch
  · rw [hseed, ← helapsed]
    exact hmode
  · rw [hseed, ← helapsed]
    exact hdown

/-- The existing horizon run from the source-generated seed over the actual
selected row, all original rows, and the whole reward grid. Its domain is the
literal launch-start fibre and `s + count ≤ t.val`. -/
def generatedActivePrefixFactor
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (control : TimeControl p)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (s count : ℕ) (hs : s ≤ t.val)
    (hstart : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control)
    (hcount : s + count ≤ t.val) :
    ReferenceActivePhysicalHorizon.Run
      (generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart) := by
  let source := splitSource q t control remainder
  exact ReferenceActivePhysicalHorizon.run
    (generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart)
    source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count
    (by omega)
    (generatedActiveSeed_spec rate rewards C_star C_h q t control remainder hremainder
      s hs hstart).2.1

private theorem activeState_ext {rate : RateInput p}
    {left right : ReferenceActivePhysicalStep.State p rate}
    (hcoord : left.coordinator = right.coordinator)
    (hbank : left.upDecoderBank = right.upDecoderBank)
    (hactivation : ∀ i, left.activations i = right.activations i)
    (hfollowers : ∀ i, left.followers i = right.followers i) :
    left = right := by
  cases left with
  | mk lc lb la lf =>
    cases right with
    | mk rc rb ra rf =>
      have hla : la = ra := funext hactivation
      have hlf : lf = rf := funext hfollowers
      cases hcoord
      cases hbank
      cases hla
      cases hlf
      rfl

private theorem correctedLaunch_eq_of_stopped_payload
    (rate : RateInput p)
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
  obtain ⟨left, ⟨hlaunch, hcoord, hbank, hactivation, hfollowers⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate leftSource rewards C_star C_h hleft
  obtain ⟨right, ⟨hrlaunch, hrcoord, hrbank, hractivation, hrfollowers⟩, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_crossing_characterization
      rate rightSource rewards C_star C_h hright
  have hstate : left = right := by
    apply activeState_ext
    · exact hcoord.trans hrcoord.symm
    · exact hbank.trans hrbank.symm
    · intro i
      apply Option.some.inj
      calc
        some (left.activations i) =
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)).activation
                (ActualReferenceInitializationBlock.refFollower i) := hactivation i
        _ = (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)).activation
                (ActualReferenceInitializationBlock.refFollower i) :=
              congrArg (fun b : ReferenceInitializationRun.Boundary p =>
                b.activation (ActualReferenceInitializationBlock.refFollower i)) hboundary
        _ = some (right.activations i) := (hractivation i).symm
    · intro i
      calc
        left.followers i = .ordinary
            (ReferenceInitializationRun.ordinary
              (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate)
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput leftSource rewards C_star C_h rate))
              (ActualReferenceInitializationBlock.refFollower i))
            (ActiveFollowerLifecycle.initialMemory p) := hfollowers i
        _ = .ordinary
            (ReferenceInitializationRun.ordinary
              (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate)
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput rightSource rewards C_star C_h rate))
              (ActualReferenceInitializationBlock.refFollower i))
            (ActiveFollowerLifecycle.initialMemory p) :=
              congrArg (fun state => DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                state (ActiveFollowerLifecycle.initialMemory p)) (hordinary i)
        _ = right.followers i := (hrfollowers i).symm
  calc
    _ = some left := hlaunch
    _ = some right := congrArg some hstate
    _ = _ := hrlaunch.symm

private theorem correctedLaunch_replaceSourceControl_eq
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p)
    (s : ℕ) (hs : s ≤ t.val)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s) :
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control)
      rewards C_star C_h := by
  let source' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control
  have hstop := stopped_observation_replaceSourceControl rate rewards C_star C_h t source control s hs
  have hleft : stoppedCrossedBy rate rewards C_star C_h source s := by
    change (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true ∧
        ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed ≤ s
    exact ⟨hcross, by rw [helapsed]⟩
  have hright : stoppedCrossedBy rate rewards C_star C_h source' s := hstop.1.mp hleft
  have hrightFacts := hright
  change (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).crossing.isSome = true ∧
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)).completed ≤ s
    at hrightFacts
  have hobs := hstop.2
  have hobs' : stoppedObservation rate rewards C_star C_h source s =
      stoppedObservation rate rewards C_star C_h source' s := by
    change stoppedObservation rate rewards C_star C_h source s =
      stoppedObservation rate rewards C_star C_h source' s at hobs
    exact hobs
  have hpayload :
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate),
        fun i => ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) i) =
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate),
        fun i => ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i) := by
    simp only [stoppedObservation, hleft, hright, ↓reduceIte] at hobs'
    exact Option.some.inj hobs'
  have hboundary := congrArg Prod.fst hpayload
  have hordinary : ∀ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) i =
      ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source' rewards C_star C_h rate)) i := by
    intro i
    exact congrFun (congrArg Prod.snd hpayload) i
  exact correctedLaunch_eq_of_stopped_payload rate rewards C_star C_h source source'
    hcross hrightFacts.1 hboundary hordinary

private theorem sourceControl_before_replacement
    (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p)
    (v : Fin p.T) (hv : v.val < t.val) :
    (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v =
      ((ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source
        control).1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 v := by
  have hne : v ≠ t := by
    intro h
    subst v
    omega
  rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
  simp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    Function.update_self, Function.update_of_ne hne]

private theorem horizonRun_views_congr_initial
    {rate : RateInput p}
    (initial initial' : ReferenceActivePhysicalStep.State p rate)
    (hinitial : initial = initial')
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart initial' start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState =
      (ReferenceActivePhysicalHorizon.run initial' rows selected rewards start count hspan hmode').finalState ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run initial' rows selected rewards start count hspan hmode').records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  cases hinitial
  have hmodeEq : hmode = hmode' := Subsingleton.elim _ _
  cases hmodeEq
  exact ⟨rfl, rfl⟩

private theorem horizonRun_views_congr_selected
    {rate : RateInput p}
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected selected' : Fin (M p))
    (hselected : selected = selected')
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).finalState =
      (ReferenceActivePhysicalHorizon.run initial rows selected' rewards start count hspan hmode).finalState ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan hmode).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run initial rows selected' rewards start count hspan hmode).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  cases hselected
  exact ⟨rfl, rfl⟩

/-- On one original remainder stratum, every removed current-control value
has the same generated seed and the same incoming active prefix on the actual
selected row. The initial seed is produced by C; A compares the existing fold.
-/
theorem generatedActivePrefixFactor_control_independent
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (remainder : Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control0 : TimeControl p)
    (s count : ℕ) (hs : s ≤ t.val) (hcount : s + count ≤ t.val)
    (hstart0 : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control0)
    (control control' : TimeControl p) :
    let hstart := (launchStartRemainderEvent_control_independent rate rewards C_star C_h q t s
      remainder hremainder control0 control).mp hstart0
    let hstart' := (launchStartRemainderEvent_control_independent rate rewards C_star C_h q t s
      remainder hremainder control0 control').mp hstart0
    ∃ active : ReferenceActivePhysicalStep.State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
          (splitSource q t control0 remainder) rewards C_star C_h = some active ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
          (splitSource q t control remainder) rewards C_star C_h = some active ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate
          (splitSource q t control' remainder) rewards C_star C_h = some active ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart active s ∧
      ReferenceFollowerDecoderChronology.downBatchSeed active s ∧
      (generatedActivePrefixFactor rate rewards C_star C_h q t control remainder
        hremainder s count hs hstart hcount).finalState =
      (generatedActivePrefixFactor rate rewards C_star C_h q t control' remainder
        hremainder s count hs hstart' hcount).finalState ∧
      (generatedActivePrefixFactor rate rewards C_star C_h q t control remainder
        hremainder s count hs hstart hcount).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (generatedActivePrefixFactor rate rewards C_star C_h q t control' remainder
        hremainder s count hs hstart' hcount).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  intro hstart hstart'
  let source0 := splitSource q t control0 remainder
  let source := splitSource q t control remainder
  let source' := splitSource q t control' remainder
  obtain ⟨hc0, helapsed0⟩ := launchStart_source_facts rate rewards C_star C_h q t control0
    remainder hremainder s hs hstart0
  obtain ⟨hc, helapsed⟩ := launchStart_source_facts rate rewards C_star C_h q t control
    remainder hremainder s hs hstart
  obtain ⟨hc', helapsed'⟩ := launchStart_source_facts rate rewards C_star C_h q t control'
    remainder hremainder s hs hstart'
  have hreplace := splitSource_replacement q t remainder hremainder control control'
  have hreplace0 := splitSource_replacement q t remainder hremainder control0 control
  have hlaunchEq0 := correctedLaunch_replaceSourceControl_eq rate rewards C_star C_h t
    source0 control s hs hc0 helapsed0
  have hlaunchEq0' :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source0 rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h := by
    rw [← hreplace0] at hlaunchEq0
    exact hlaunchEq0
  have hlaunchEq := correctedLaunch_replaceSourceControl_eq rate rewards C_star C_h t
    source control' s hs hc helapsed
  have hlaunchEq' :
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source' rewards C_star C_h := by
    rw [← hreplace] at hlaunchEq
    exact hlaunchEq
  have h0 := generatedActiveSeed_spec rate rewards C_star C_h q t control0 remainder
    hremainder s hs hstart0
  let active := generatedActiveSeed rate rewards C_star C_h q t control0 remainder
    hremainder s hs hstart0
  have hlaunch0 : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source0
      rewards C_star C_h = some active := h0.1
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source
      rewards C_star C_h = some active := hlaunchEq0'.symm.trans h0.1
  have hlaunch' : ReferenceCorrectedInitializationLaunch.correctedLaunch rate source'
      rewards C_star C_h = some active :=
    hlaunchEq'.symm.trans (hlaunchEq0'.symm.trans h0.1)
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active s := h0.2.1
  have hdown : ReferenceFollowerDecoderChronology.downBatchSeed active s := h0.2.2
  have hseed : generatedActiveSeed rate rewards C_star C_h q t control remainder
      hremainder s hs hstart = active :=
    generatedActiveSeed_eq_of_launch rate rewards C_star C_h q t control remainder
      hremainder s hs hstart active hlaunch
  have hseed' : generatedActiveSeed rate rewards C_star C_h q t control' remainder
      hremainder s hs hstart' = active :=
    generatedActiveSeed_eq_of_launch rate rewards C_star C_h q t control' remainder
      hremainder s hs hstart' active hlaunch'
  have hsource' : source' =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control' :=
    hreplace
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p source' =
      ActualInitializationPhysicalStep.selectedRowIndex p source := by
    exact (splitSource_index q t control' remainder hremainder).trans
      (splitSource_index q t control remainder hremainder).symm
  have hcontrols : ∀ j : Fin p.T, s ≤ j.val → j.val < s + count →
      (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 j =
        (source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 j := by
    intro j hjstart hjend
    rw [hsource']
    exact sourceControl_before_replacement t source control' j (by omega)
  have hrewards : ∀ j : Fin p.T, s ≤ j.val → j.val < s + count → rewards j = rewards j :=
    fun _ _ _ => rfl
  have hbefore : 0 < count → ∀ j : Fin p.T, j.val < s →
      ((source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 j).1
          ContinuousControlSlice.Label.prop =
        ((source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 j).1
          ContinuousControlSlice.Label.prop := by
    intro hpositive j hj
    rw [hsource']
    exact congrArg
      (fun u : TimeControl p =>
        u.1 ContinuousControlSlice.Label.prop)
      (sourceControl_before_replacement t source control' j (by omega))
  have hspan : s + count ≤ p.T := by omega
  have hrun := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads active
    source.1.2 source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards rewards s count hspan hmode hcontrols hrewards hbefore
  have hleftViews := horizonRun_views_congr_initial
    (generatedActiveSeed rate rewards C_star C_h q t control remainder hremainder s hs hstart)
    active hseed source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards s count hspan
    (generatedActiveSeed_spec rate rewards C_star C_h q t control remainder hremainder
      s hs hstart).2.1 hmode
  have hrightViews := horizonRun_views_congr_initial
    (generatedActiveSeed rate rewards C_star C_h q t control' remainder hremainder s hs hstart')
    active hseed' source'.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source')
    rewards s count hspan
    (generatedActiveSeed_spec rate rewards C_star C_h q t control' remainder hremainder
      s hs hstart').2.1 hmode
  have hrightSelected := horizonRun_views_congr_selected active source'.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source')
    (ActualInitializationPhysicalStep.selectedRowIndex p source) hselected
    rewards s count hspan hmode
  refine ⟨active, hlaunch0, hlaunch, hlaunch', hmode, hdown, ?_, ?_⟩
  · calc
      _ = (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode).finalState := by
        simpa [generatedActivePrefixFactor, source] using hleftViews.1
      _ = (ReferenceActivePhysicalHorizon.run active source'.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode).finalState :=
        hrun.1
      _ = (ReferenceActivePhysicalHorizon.run active source'.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source') rewards s count hspan hmode).finalState :=
        hrightSelected.1.symm
      _ = _ := by
        simpa [generatedActivePrefixFactor, source'] using hrightViews.1.symm
  · calc
      _ = (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
        simpa [generatedActivePrefixFactor, source] using hleftViews.2
      _ = (ReferenceActivePhysicalHorizon.run active source'.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan hmode).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
        exact hrun.2
      _ = (ReferenceActivePhysicalHorizon.run active source'.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source') rewards s count hspan hmode).records.map
            ReferenceActivePhysicalHorizon.RoundRecord.evidence :=
        hrightSelected.2.symm
      _ = _ := by
        simpa [generatedActivePrefixFactor, source'] using hrightViews.2.symm

/-- Re-evaluating the factor at a real source's split coordinates reconstructs
that original source exactly. This is the source-facing on-fibre specialization
of the internal launch-event factor. -/
theorem generatedActivePrefixFactor_on_source
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (source : SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (s count : ℕ) (hs : s ≤ t.val) (hcount : s + count ≤ t.val)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s) :
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source
    let control := split.1
    let remainder := split.2
    let hrem : remainder ∈ ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t source]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    let hstart : remainder ∈ launchStartRemainderEvent rate rewards C_star C_h q t s control := by
      exact (launchStartRemainderEvent_iff_source rate rewards C_star C_h q t control
        source hselected s hs).mpr ⟨hcross, helapsed⟩
    (generatedActivePrefixFactor rate rewards C_star C_h q t control remainder hrem
      s count hs hstart hcount).finalState =
      (ReferenceActivePhysicalHorizon.run
        (generatedActiveSeed rate rewards C_star C_h q t control remainder hrem s hs hstart)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count (by omega)
        (generatedActiveSeed_spec rate rewards C_star C_h q t control remainder hrem
          s hs hstart).2.1).finalState ∧
    (generatedActivePrefixFactor rate rewards C_star C_h q t control remainder hrem
      s count hs hstart hcount).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence =
      (ReferenceActivePhysicalHorizon.run
        (generatedActiveSeed rate rewards C_star C_h q t control remainder hrem s hs hstart)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count (by omega)
        (generatedActiveSeed_spec rate rewards C_star C_h q t control remainder hrem
          s hs hstart).2.1).records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence := by
  intro split control remainder hrem hstart
  have hsource : splitSource q t control remainder = source := by
    dsimp [split, control, remainder, splitSource]
    exact (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).symm_apply_apply source
  have hrows : (splitSource q t control remainder).1.2 = source.1.2 :=
    congrArg (fun input : SourceInput p => input.1.2) hsource
  have hselected' : ActualInitializationPhysicalStep.selectedRowIndex p
      (splitSource q t control remainder) = ActualInitializationPhysicalStep.selectedRowIndex p source :=
    congrArg (ActualInitializationPhysicalStep.selectedRowIndex p) hsource
  constructor
  · change (ReferenceActivePhysicalHorizon.run
      (generatedActiveSeed rate rewards C_star C_h q t control remainder hrem s hs hstart)
      (splitSource q t control remainder).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p (splitSource q t control remainder))
      rewards s count (by omega)
      (generatedActiveSeed_spec rate rewards C_star C_h q t control remainder hrem s hs hstart).2.1).finalState = _
    rw [hrows, hselected']
  · change (ReferenceActivePhysicalHorizon.run
      (generatedActiveSeed rate rewards C_star C_h q t control remainder hrem s hs hstart)
      (splitSource q t control remainder).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p (splitSource q t control remainder))
      rewards s count (by omega)
      (generatedActiveSeed_spec rate rewards C_star C_h q t control remainder hrem s hs hstart).2.1).records.map
        ReferenceActivePhysicalHorizon.RoundRecord.evidence = _
    rw [hrows, hselected']

/-- A terminal crossing at the natural elapsed endpoint still has the actual
C seed and the zero-length existing horizon run; this is separate from the
factor above, whose `t : Fin T` domain excludes elapsed start `T`. -/
theorem terminal_crossing_generated_seed_run_zero
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hterminal : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T) :
    ReferenceInitializationControlRemainder.stoppedObservation rate rewards C_star C_h source p.T =
      some (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate),
        fun i => ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) i) ∧
    (∃ active, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h =
        some active ∧
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T 0
        (by omega) hmode).finalState = active ∧
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T 0
        (by omega) hmode).records = []) ∧
    ReferenceInitializationRun.launchRound
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) = p.T + 1 := by
  have hobs := ReferenceInitializationControlRemainder.stoppedObservation_at_horizon
    rate rewards C_star C_h source
  have hobs' := by simpa [hcross] using hobs
  have hzero := ReferenceCorrectedInitializationLaunch.correctedLaunch_terminal_run_zero
    rate source rewards C_star C_h hcross hterminal
  rcases hzero with ⟨active, hmode, hlaunch, hfinal, hrecords⟩
  refine ⟨hobs', ⟨active, hmode, hlaunch, hfinal, hrecords⟩, ?_⟩
  exact (ReferenceInitializationControlRemainder.launchRound_eq_horizon_on_terminal_or_exhausted
      rate rewards C_star C_h source).1 ⟨hcross, hterminal⟩

/-- Exhaustion keeps `correctedLaunch = none` at the natural endpoint even
though its sentinel launch round also equals `T+1`. -/
theorem exhausted_generated_launch_none
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hnoCross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = false) :
    ReferenceInitializationControlRemainder.stoppedObservation rate rewards C_star C_h source p.T = none ∧
    ReferenceCorrectedInitializationLaunch.correctedLaunch rate source rewards C_star C_h = none ∧
    ReferenceInitializationRun.launchRound
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) = p.T + 1 := by
  have hobs := ReferenceInitializationControlRemainder.stoppedObservation_at_horizon
    rate rewards C_star C_h source
  have hobs' := by simpa [hnoCross] using hobs
  have hcrossNone : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing = none := by
    cases h : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing with
    | none => rfl
    | some crossing => simp [h] at hnoCross
  refine ⟨hobs', (ReferenceCorrectedInitializationLaunch.correctedLaunch_eq_none_iff
    rate source rewards C_star C_h).2 hcrossNone, ?_⟩
  exact (ReferenceInitializationControlRemainder.launchRound_eq_horizon_on_terminal_or_exhausted
    rate rewards C_star C_h source).2 hnoCross

end Bandits.Support.ReferenceGeneratedActivePrefixFactor

end
