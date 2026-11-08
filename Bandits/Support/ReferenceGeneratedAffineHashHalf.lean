/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Bandits.Support.ReferenceRetainedBoundaryMeasurability
public import Bandits.Support.ReferenceSourceAffineHashHalf

/-!
# Source-generated active-round affine hash-half law
Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-150`,
`sources/zip4/manuscript/05_binary_transport.tex:7-42,74-124`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:26-42`.
On a genuine generated launch stratum, the incoming active physical input is
constructed from the original source.  This module integrates the actual
selected affine pair while retaining the full original remainder and proves
the active-round DOWN and UP half laws.  It asserts no batch recurrence or
source-error probability.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ReferenceSelectedAffinePairLaw
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActiveAffinePositiveTest
open Bandits.Support.ReferenceSourceAffineHashHalf
namespace Bandits.Support.ReferenceGeneratedAffineHashHalf
abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RoundInput := ReferenceActivePhysicalStep.RoundInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev Pair := ReferenceSelectedAffinePairLaw.Pair
abbrev PairRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T)
    (c : Channel p) := ReferenceSelectedAffinePairLaw.Remainder p q t c
abbrev ControlRemainder (p : Parameters) (q : Fin (M p)) (t : Fin p.T) :=
  ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t
variable {p : Parameters} {rate : RateInput p}

/-- Retain the original control except the selected current slice and pairs. -/
def retainedControlProjection {q : Fin (M p)} {t : Fin p.T} {c : Channel p}
    (r : PairRemainder p q t c) : ControlRemainder p q t :=
  ((r.1.1, ((r.1.2.1.1, r.1.2.1.2.2), r.1.2.2)), r.2)
/-- The projection is Borel in the original remainder coordinates. -/
theorem measurable_retainedControlProjection {q : Fin (M p)} {t : Fin p.T}
    {c : Channel p} :
    Measurable (retainedControlProjection (p := p) (q := q) (t := t) (c := c)) := by
  change Measurable (fun r : PairRemainder p q t c =>
    ((r.1.1, ((r.1.2.1.1, r.1.2.1.2.2), r.1.2.2)), r.2))
  fun_prop
/-- Reconstructing and projecting preserves the literal retained remainder. -/
theorem fixedControlSplit_pair_remainder {q : Fin (M p)} {t : Fin p.T}
    {c : Channel p} (a : Pair p) (r : PairRemainder p q t c) :
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t
      ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r))).2 =
      retainedControlProjection (p := p) (q := q) (t := t) (c := c) r := by
  let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r)
  rcases ReferenceSelectedAffinePairLaw.fixedPairSplit_inverse_coordinates
      p q t c a r with
    ⟨_, hid, hprivate, hforward, _, _, htimes, hrows⟩
  have hid' : z.1.1 = r.1.1 := hid
  have hprivate' : z.2 = r.2 := hprivate
  have hforward' : (z.1.2 q).1 = r.1.2.1.1 := hforward
  have htimes' : (fun s : ReferenceSelectedAffinePairLaw.Other t =>
      (z.1.2 q).2 s) = r.1.2.1.2.2 := funext htimes
  have hrows' : (fun j : ReferenceSelectedAffinePairLaw.Other q => z.1.2 j) =
      r.1.2.2 := funext hrows
  change ((z.1.1, (((z.1.2 q).1,
      fun s : ReferenceSelectedAffinePairLaw.Other t => (z.1.2 q).2 s),
      fun j : ReferenceSelectedAffinePairLaw.Other q => z.1.2 j)), z.2) = _
  rw [hid', hprivate', hforward', htimes', hrows']
  rfl

/-- Select the original row and channel, a crossing, and the exact launch start. -/
def generatedLaunchBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ) :
    Set (SourceInput p) :=
  {z | ReferenceSelectedAffinePairLaw.selector p t z = (q, some c) ∧
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed = s}
/-- The selector-and-launch set in the original pair remainder. -/
def generatedLaunchRemainderSet
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p)
    (s : ℕ) (control0 : TimeControl p) : Set (PairRemainder p q t c) :=
  ReferenceSelectedAffinePairLaw.remainderSelectorEvent p q t c ∩
    retainedControlProjection (p := p) (q := q) (t := t) (c := c) ⁻¹'
      ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
        rate rewards C_star C_h q t s control0
/-- Pull back the selected remainder and retained whole-control launch event. -/
theorem generatedLaunchBranch_fixedPairSplit_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p) (a : Pair p)
    (r : PairRemainder p q t c) :
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r) ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s ↔
    r ∈ generatedLaunchRemainderSet (rate := rate) rewards C_star C_h q t c s control0 := by
  let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r)
  have hsplit : ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c z = (a, r) := by
    exact (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).apply_symm_apply (a, r)
  have hrem : (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2 =
      retainedControlProjection (p := p) (q := q) (t := t) (c := c) r := by
    exact fixedControlSplit_pair_remainder (a := a) r
  constructor
  · rintro ⟨hselector, hcross, helapsed⟩
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
      have hindex := congrArg Prod.fst hselector
      change ActualInitializationPhysicalStep.selectedRowIndex p z = q at hindex
      exact hindex
    have hlaunch :=
      ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_mem
        rate rewards C_star C_h q t s hs control0 z hselected hcross helapsed
    rw [hrem] at hlaunch
    have hselectorR :=
      (ReferenceSelectedAffinePairLaw.selector_remainder_iff p q t c z).mp hselector
    rw [hsplit] at hselectorR
    have hlaunchR : retainedControlProjection
        (p := p) (q := q) (t := t) (c := c) r ∈
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0 := hlaunch
    exact ⟨hselectorR, hlaunchR⟩
  · rintro ⟨⟨hJ, hchannel⟩, hretained⟩
    have hselector : ReferenceSelectedAffinePairLaw.selector p t z = (q, some c) := by
      exact (ReferenceSelectedAffinePairLaw.selector_remainder_iff p q t c z).mpr
        (by simpa [hsplit] using ⟨hJ, hchannel⟩)
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z = q := by
      have hindex := congrArg Prod.fst hselector
      change ActualInitializationPhysicalStep.selectedRowIndex p z = q at hindex
      exact hindex
    change retainedControlProjection
        (p := p) (q := q) (t := t) (c := c) r ∈
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0 at hretained
    have hlaunchR := hretained
    have hretained' : (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit
        p q t z).2 ∈ ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0 := by
      rw [hrem]
      exact hlaunchR
    rcases hretained' with ⟨hfixed, hstart0⟩
    have hcontrol := (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).1
    have hstart :=
      ReferenceRetainedBoundaryMeasurability.launchStart_control_independent_on_remainder
        rate rewards C_star C_h q t s (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit
          p q t z).2 hfixed control0 hcontrol |>.mp hstart0
    have hfacts :=
      ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t hcontrol z hselected s hs |>.mp hstart
    exact ⟨hselector, hfacts.1, hfacts.2⟩
/-- The source branch is Borel by the retained source event. -/
theorem measurableSet_generatedLaunchBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p) :
    MeasurableSet (generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s) := by
  have hset : generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s =
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c) ⁻¹'
        (Set.univ ×ˢ generatedLaunchRemainderSet
          (rate := rate) rewards C_star C_h q t c s control0) := by
    ext z
    rcases hval : ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c z with ⟨a, r⟩
    have hy : (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c z) = (a, r) := hval
    have hz : (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r) = z := by
      rw [← hy]
      exact (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm_apply_apply z
    rw [← hz]
    have hpair :=
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).apply_symm_apply (a, r)
    change (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r) ∈
        generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s ↔
      ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c)
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r))).1 ∈ Set.univ ∧
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c)
          ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).symm (a, r))).2 ∈
          generatedLaunchRemainderSet (rate := rate) rewards C_star C_h q t c s control0
    simp only [Set.mem_univ, true_and, hpair]
    exact generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h q t c s hs control0 a r
  rw [hset]
  exact (MeasurableSet.univ.prod
      ((ReferenceSelectedAffinePairLaw.measurableSet_remainderSelectorEvent p q t c).inter
        ((ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
          rate rewards C_star C_h q t s hs control0).preimage
          measurable_retainedControlProjection))).preimage
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t c).measurable
/-- Construct B's retained launch state from the original branch source. -/
def retainedLaunchStartInputOfBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :=
  ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource
    rate rewards C_star C_h q t s hs control0 z.1
    (by
      have h := z.2.1
      have hidx := congrArg Prod.fst h
      change ActualInitializationPhysicalStep.selectedRowIndex p z.1 = q at hidx
      exact hidx)
    z.2.2.1 z.2.2.2
/-- Recover the original private coordinator index on the branch. -/
theorem selectedRowIndex_of_generatedLaunchBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    ActualInitializationPhysicalStep.selectedRowIndex p z.1 = q := by
  have hidx := congrArg Prod.fst z.2.1
  change ActualInitializationPhysicalStep.selectedRowIndex p z.1 = q at hidx
  exact hidx
/-- Transport the source branch into B's retained launch subtype. -/
theorem fixedControlRemainder_mem_retainedLaunchStartSet
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).2 ∈
      ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
        rate rewards C_star C_h q t s control0 :=
  ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_mem
    rate rewards C_star C_h q t s hs control0 z.1
    (selectedRowIndex_of_generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s z)
    z.2.2.1 z.2.2.2
/-- The retained input has the original fixed-control remainder as its value. -/
theorem retainedLaunchStartInputOfBranch_val
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s
      hs control0 z : ControlRemainder p q t) =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).2 := by
  exact ReferenceRetainedBoundaryMeasurability.retainedLaunchStartInputOfSource_val
    rate rewards C_star C_h q t s hs control0 z.1
    (selectedRowIndex_of_generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s z)
    z.2.2.1 z.2.2.2

/-- Generate the actual next input from the branch source and computed prefix. -/
def generatedNextInputOfBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    RoundInput p rate :=
  ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
    rate rewards C_star C_h q t s hs control0
    (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0 z)
    ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).1)
/-- Identify the branch input with B's generated input on the original source. -/
theorem generatedNextInputOfBranch_eq_roundInputAtSource
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0 z =
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0
          (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0 z))
        z.1 := by
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.1 = q := by
    have hidx := congrArg Prod.fst z.2.1
    change ActualInitializationPhysicalStep.selectedRowIndex p z.1 = q at hidx
    exact hidx
  simpa only [generatedNextInputOfBranch, retainedLaunchStartInputOfBranch] using
    ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput_eq_of_source
      rate rewards C_star C_h q t s hs control0 z.1 hselected z.2.2.1 z.2.2.2
/-- The input state is the final state of the generated active prefix. -/
theorem generatedNextInputOfBranch_state
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    (generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0 z).state =
      (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor
        rate rewards C_star C_h q t control0
        (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s
          hs control0 z).1
        (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s
          hs control0 z).2.1
        s (t.val - s) hs
        (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s
          hs control0 z).2.2
        (by omega)).finalState := by
  rw [generatedNextInputOfBranch_eq_roundInputAtSource]
  exact (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_state
    rate rewards C_star C_h q t s hs control0
    (retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s
      hs control0 z))
/-- The generated input retains the original rows, index, time, and rewards. -/
theorem generatedNextInputOfBranch_original_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s}) :
    let x := generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0 z
    x.rows = z.1.1.2 ∧
      x.selected = ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.1 ∧
      x.time = t ∧ x.rewards = rewards := by
  rw [generatedNextInputOfBranch_eq_roundInputAtSource]
  exact ⟨rfl, rfl, rfl, rfl⟩
/-- Measurability of the variable-boundary original-source round input. -/
private theorem measurable_roundInputAtVariableSource
    {Ω : Type*} [MeasurableSpace Ω]
    (boundary : Ω → RoundInput p rate) (source : Ω → SourceInput p)
    (hb : Measurable boundary) (hz : Measurable source) :
    Measurable (fun x => ReferenceFixedTimeSourceControlCoupling.roundInputAtSource
      p rate (boundary x) (source x)) := by
  have hselected : Measurable (fun x =>
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source x)) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      ((measurable_snd.comp (measurable_fst.comp measurable_snd)).comp hz)
  have hcoordinates : Measurable (fun x =>
      ((boundary x).state,
        ((source x).1.2,
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source x),
            ((boundary x).time, (boundary x).rewards))))) := by
    exact (ReferenceActivePhysicalStepMeasurability.measurable_state.comp hb).prodMk
      ((measurable_snd.comp (measurable_fst.comp hz)).prodMk
        (hselected.prodMk
          ((ReferenceActivePhysicalStepMeasurability.measurable_time.comp hb).prodMk
            (ReferenceActivePhysicalStepMeasurability.measurable_rewards.comp hb))))
  have hactive : Measurable (fun x =>
      (⟨((boundary x).state,
        ((source x).1.2,
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p (source x),
            ((boundary x).time, (boundary x).rewards)))), (boundary x).active⟩ :
        ReferenceActivePhysicalStepMeasurability.ActiveRoundCoordinates p rate)) :=
    hcoordinates.subtype_mk (h := fun x => (boundary x).active)
  have hdecode :=
    ReferenceActivePhysicalStepMeasurability.measurable_decodeRoundInput.comp hactive
  convert hdecode using 1
  rfl
/-- The actual branch input map is Borel on the inherited branch subtype. -/
theorem measurable_generatedNextInputOfBranch
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (c : Channel p) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) :
    Measurable (generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0) := by
  let launch := retainedLaunchStartInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0
  let boundary := fun z => ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 (launch z)
  have hlaunch : Measurable launch := by
    have hEq : launch = fun z =>
        (⟨(ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).2,
          by
            have hval := retainedLaunchStartInputOfBranch_val
              (rate := rate) rewards C_star C_h q t c s hs control0 z
            change (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z.1).2 ∈
              ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
                rate rewards C_star C_h q t s control0
            rw [← hval]
            exact (launch z).2⟩ :
          ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
            rate rewards C_star C_h q t s hs control0) := by
      funext z
      apply Subtype.ext
      exact retainedLaunchStartInputOfBranch_val
        (rate := rate) rewards C_star C_h q t c s hs control0 z
    rw [hEq]
    apply Measurable.subtype_mk
    exact measurable_snd.comp
      ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t).measurable.comp
        measurable_subtype_coe)
  have hboundary : Measurable boundary := by
    exact (ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
      rate rewards C_star C_h q t s hs control0).comp hlaunch
  have hsource : Measurable (fun z : {z : SourceInput p // z ∈
      generatedLaunchBranch (rate := rate) rewards C_star C_h q t c s} => z.1) :=
    measurable_subtype_coe
  have hround := measurable_roundInputAtVariableSource boundary (fun z => z.1)
    hboundary hsource
  have heq : generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t c s hs control0 =
      fun z => ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (boundary z) z.1 := by
    funext z
    exact generatedNextInputOfBranch_eq_roundInputAtSource
      rewards C_star C_h q t c s hs control0 z
  rw [heq]
  exact hround
def directionPositive (direction : Fin 2) (x : RoundInput p rate) : Bool :=
  if direction = 0 then ReferenceActiveAffinePositiveTest.downPositive x
  else ReferenceActiveAffinePositiveTest.upPositive x
def directionSent (direction : Fin 2) (x : RoundInput p rate) :
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  if direction = 0 then ReferenceActiveAffinePositiveTest.downSent x
  else ReferenceActiveAffinePositiveTest.upSent x
private def referencePairSample : Pair p := (fun _ => 0, 0)
private theorem measurable_upSent_generated :
    Measurable (fun x : RoundInput p rate =>
      ReferenceActiveAffinePositiveTest.upSent x) := by
  have hmap : Measurable
      (ReferenceCollectionServiceTailMeasurability.collectionExpectedMap rate
        (fun x : RoundInput p rate => x)) :=
    ReferenceCollectionServiceTailMeasurability.measurable_collectionExpectedMap
      (p := p) (round := fun x : RoundInput p rate => x) measurable_id
  have heq : (fun x : RoundInput p rate =>
      ReferenceCollectionServiceTailMeasurability.collectionExpectedMap rate
        (fun y : RoundInput p rate => y) x) =
      fun x => ReferenceActiveAffinePositiveTest.upSent x := by
    funext x
    change ReferenceCollectionServiceTailMeasurability.collectionExpectedMap rate
        (fun _ : Unit => x) () =
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x)
    have hprepared := ReferenceCollectionServiceTailMeasurability.selectedUpPrepared_reconstruct x
    exact congrArg (fun sender : DeclaredFollowerLocalRound.PreparedRound p rate =>
      ReferenceUpReception.currentOfferWord rate sender.row sender.follower sender.time
        sender rfl rfl rfl) hprepared
  exact heq ▸ hmap
/- The pair-replacement identity is proved in the original product
coordinates. Its selector premise identifies both the original coordinator
and the follower used by the physical UP coordinate. -/
private theorem roundInputAtPairSplit_eq_replaceCurrentPair
    (boundary : RoundInput p rate) (q : Fin (M p)) (direction : Fin 2)
    (i : Fin (p.m - 1)) (a₀ a : Pair p)
    (r : PairRemainder p q boundary.time (direction, i))
    (hr : r ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent
      p q boundary.time (direction, i)) :
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time
          (direction, i)).symm (a, r)) =
      ReferenceActiveAffinePositiveTest.replaceCurrentPair
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary
          ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time
            (direction, i)).symm (a₀, r))) direction a := by
  let iChannel : Fin (d p) :=
    ⟨i.val, by simpa only [d] using i.isLt⟩
  let c : Channel p := (direction, iChannel)
  change ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary
      ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time c).symm (a, r)) =
    ReferenceActiveAffinePositiveTest.replaceCurrentPair
      (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time c).symm (a₀, r)))
      direction a
  change r ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent
    p q boundary.time c at hr
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q boundary.time c
  let source₀ := split.symm (a₀, r)
  let source := split.symm (a, r)
  rcases ReferenceSelectedAffinePairLaw.fixedPairSplit_inverse_coordinates
      p q boundary.time c a₀ r with
    ⟨_, _, hprivate₀, hforward₀, hslice₀, hchannels₀, htimes₀, hrows₀⟩
  rcases ReferenceSelectedAffinePairLaw.fixedPairSplit_inverse_coordinates
      p q boundary.time c a r with
    ⟨hpair, _, hprivate, hforward, hslice, hchannels, htimes, hrows⟩
  have hselected₀ : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀ = q := by
    change PrivateSourceStreams.coordinatorIndex p source₀.2.1.2 = q
    rw [hprivate₀]
    exact hr.1
  have hselected : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q := by
    change PrivateSourceStreams.coordinatorIndex p source.2.1.2 = q
    rw [hprivate]
    exact hr.1
  have hdrawR : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      r.1.2.1.2.1.1 = i := by
    have hchannel := hr.2
    by_cases hdown : PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1 =
        PublicDiscreteDraws.downSlot
    · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_down p _ hdown] at hchannel
      exact congrArg Prod.snd (Option.some.inj hchannel)
    · by_cases hup : PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1 =
          PublicDiscreteDraws.upSlot
      · rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ hup] at hchannel
        exact congrArg Prod.snd (Option.some.inj hchannel)
      · have hdata : PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1 =
            PublicDiscreteDraws.dataSlot := by
          have hbound := (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).isLt
          have hdownVal : (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).val ≠ 1 := by
            intro hv
            apply hdown
            exact Fin.ext hv
          have hupVal : (PublicDiscreteDraws.slotDraw r.1.2.1.2.1.1).val ≠ 2 := by
            intro hv
            apply hup
            exact Fin.ext hv
          apply Fin.ext
          simp only [PublicDiscreteDraws.dataSlot]
          omega
        rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_data p _ hdata] at hchannel
        cases hchannel
  let follower : Fin (p.m - 1) :=
    ⟨i.val, by simpa only [ContinuousLearningRows.d] using i.isLt⟩
  have hindex : ReferenceActivePhysicalStep.upSenderIndex
      (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary source₀) = follower := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((source₀.1.2 (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
        boundary.time).1 = follower
    rw [hselected₀, hslice₀]
    exact Fin.ext (congrArg Fin.val hdrawR)
  have hrows : source.1.2 = Function.update source₀.1.2 q
      ((source₀.1.2 q).1,
        Function.update (source₀.1.2 q).2 boundary.time
          (((source₀.1.2 q).2 boundary.time).1,
            Function.update ((source₀.1.2 q).2 boundary.time).2 c a)) := by
    funext j
    by_cases hj : j = q
    · subst j
      simp only [Function.update_self]
      apply Prod.ext
      · exact hforward.trans hforward₀.symm
      · funext t'
        by_cases ht : t' = boundary.time
        · subst t'
          simp only [Function.update_self]
          apply Prod.ext
          · exact hslice.trans hslice₀.symm
          · funext channel
            by_cases hc : channel = c
            · subst channel
              simp only [Function.update_self]
              exact hpair
            · let other : ReferenceSelectedAffinePairLaw.Other c := ⟨channel, hc⟩
              simp only [Function.update_of_ne hc]
              exact (hchannels other).trans (hchannels₀ other).symm
        · let other : ReferenceSelectedAffinePairLaw.Other boundary.time := ⟨t', ht⟩
          simp only [Function.update_of_ne ht]
          exact (htimes other).trans (htimes₀ other).symm
    · let other : ReferenceSelectedAffinePairLaw.Other q := ⟨j, hj⟩
      simp only [Function.update_of_ne hj]
      exact (hrows other).trans (hrows₀ other).symm
  have hinput : ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary source =
      ReferenceActiveAffinePositiveTest.replaceCurrentPair
        (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary source₀)
        direction a := by
    have input_ext (left right : RoundInput p rate)
        (hs : left.state = right.state) (hr : left.rows = right.rows)
        (hj : left.selected = right.selected) (ht : left.time = right.time)
        (hw : left.rewards = right.rewards) : left = right := by
      cases left
      cases right
      simp_all
    apply input_ext
    · rfl
    · change source.1.2 = Function.update source₀.1.2
        (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)
        ((source₀.1.2
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).1,
          Function.update (source₀.1.2
            (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
            boundary.time
            (((source₀.1.2
              (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
              boundary.time).1,
              Function.update ((source₀.1.2
                (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀)).2
                boundary.time).2
                (direction, ReferenceActivePhysicalStep.upSenderIndex
                  (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary
                    source₀)) a))
      have hchannel : (direction, ReferenceActivePhysicalStep.upSenderIndex
          (ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate boundary source₀)) = c := by
        apply Prod.ext
        · rfl
        exact hindex
      have hrows' := hrows
      rw [← hchannel] at hrows'
      rw [hselected₀]
      exact hrows'
    · change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source =
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source₀
      rw [hselected, hselected₀]
    · rfl
    · rfl
  simpa [split, source, source₀] using hinput
private def activeRemainderSet
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i))) :
    Set (PairRemainder p q t (direction, i)) :=
  generatedLaunchRemainderSet (rate := rate) rewards C_star C_h q t
      (direction, i) s control0 ∩ C
private abbrev activeRetainedLaunch
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (_hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i))) :=
  {r : PairRemainder p q t (direction, i) //
    r ∈ activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C}
private def activeRetainedLaunchInput
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i)))
    (r : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :
    ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0 := by
  refine ⟨retainedControlProjection (p := p) (q := q) (t := t) (c := (direction, i)) r.1, ?_⟩
  exact r.2.1.2
private def activeBoundary
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i)))
    (r : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :
    RoundInput p rate :=
  ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0
      (activeRetainedLaunchInput (rate := rate) rewards C_star C_h q t direction i s hs
        control0 C r)
private theorem measurable_activeBoundary
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i))) :
    Measurable (activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs control0 C) := by
  have hlaunch : Measurable (activeRetainedLaunchInput (rate := rate)
      rewards C_star C_h q t direction i s hs control0 C) := by
    apply Measurable.subtype_mk
    · exact (measurable_retainedControlProjection.comp measurable_subtype_coe)
  exact (ReferenceRetainedBoundaryMeasurability.measurable_retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0).comp hlaunch
private def activeReferenceInput
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i)))
    (r : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :
    RoundInput p rate :=
  ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
    (activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs control0 C r)
    ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm
      (referencePairSample (p := p), r.1))
private theorem directionSent_replace (direction : Fin 2) (x : RoundInput p rate)
    (sample : Pair p) :
    directionSent direction
        (ReferenceActiveAffinePositiveTest.replaceCurrentPair x direction sample) =
      directionSent direction x := by
  fin_cases direction
  · simpa [directionSent] using
      ReferenceAffineDispatchPairInvariance.downSent_replace x 0 sample
  · simpa [directionSent] using
      ReferenceActiveAffinePositiveTest.upSent_replace x 1 sample
private theorem measurable_directionPositive :
    Measurable (fun z : Fin 2 × RoundInput p rate =>
      directionPositive z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro direction
  fin_cases direction
  · simpa [directionPositive] using ReferenceSourceAffineHashHalf.measurable_downPositive
  · simpa [directionPositive] using ReferenceSourceAffineHashHalf.measurable_upPositive
private theorem measurable_directionSent :
    Measurable (fun z : Fin 2 × RoundInput p rate =>
      directionSent z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro direction
  fin_cases direction
  · simpa [directionSent] using ReferenceSourceAffineHashHalf.measurable_downSent
  · simpa [directionSent] using measurable_upSent_generated

/-- Use the executed positive and sent values, including later failures. -/
def generatedPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) : Set (SourceInput p) :=
  {z | ∃ hz : z ∈ generatedLaunchBranch (rate := rate) rewards C_star C_h q t
      (direction, i) s,
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i) z).2 ∈ C ∧
      directionPositive direction
        (generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t
          (direction, i) s hs control0 ⟨z, hz⟩) = true ∧
      directionSent direction
        (generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t
          (direction, i) s hs control0 ⟨z, hz⟩) ≠ some candidate}

/-- Add the original removed affine pair's hash-one event. -/
def generatedPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) : Set (SourceInput p) :=
  {z | z ∈ generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
      s hs control0 candidate C ∧
    AffineChannelLaw.affineHash
      (((z.1.2 q).2 t).2 (direction, i)) candidate = 1}
private theorem generatedNextInput_eq_activeReferenceInput
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i)))
    (a : Pair p)
    (r : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :
    let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm (a, r.1)
    generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t (direction, i) s hs
        control0 ⟨z, (generatedLaunchBranch_fixedPairSplit_iff
          (rate := rate) rewards C_star C_h q t (direction, i) s hs control0 a r.1).2 r.2.1⟩ =
      ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
        (activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs control0 C r)
        ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm (a, r.1)) := by
  dsimp
  let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm (a, r.1)
  let hz : z ∈ generatedLaunchBranch (rate := rate) rewards C_star C_h q t
      (direction, i) s :=
    (generatedLaunchBranch_fixedPairSplit_iff
      (rate := rate) rewards C_star C_h q t (direction, i) s hs control0 a r.1).2 r.2.1
  let branchInput := retainedLaunchStartInputOfBranch (rate := rate)
    rewards C_star C_h q t (direction, i) s hs control0 ⟨z, hz⟩
  have hbranchVal : (branchInput : ControlRemainder p q t) =
      (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2 :=
    retainedLaunchStartInputOfBranch_val (rate := rate)
      rewards C_star C_h q t (direction, i) s hs control0 ⟨z, hz⟩
  have hfixed : (ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t z).2 =
      retainedControlProjection (p := p) (q := q) (t := t) (c := (direction, i)) r.1 := by
    simpa [z] using fixedControlSplit_pair_remainder (p := p) (q := q) (t := t)
      (c := (direction, i)) a r.1
  have hretainedVal : (activeRetainedLaunchInput (rate := rate)
      rewards C_star C_h q t direction i s hs control0 C r : ControlRemainder p q t) =
      retainedControlProjection (p := p) (q := q) (t := t) (c := (direction, i)) r.1 := rfl
  have hlaunch : branchInput = activeRetainedLaunchInput (rate := rate)
      rewards C_star C_h q t direction i s hs control0 C r :=
    Subtype.ext (hbranchVal.trans (hfixed.trans hretainedVal.symm))
  rw [generatedNextInputOfBranch_eq_roundInputAtSource (rate := rate)
    rewards C_star C_h q t (direction, i) s hs control0 ⟨z, hz⟩]
  simp only [activeBoundary]
  rw [← hlaunch]
private theorem actualGeneratedInput_eq_replacement
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i)))
    (a : Pair p)
    (r : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :
    let z := (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm (a, r.1)
    generatedNextInputOfBranch (rate := rate)
      rewards C_star C_h q t (direction, i) s hs control0
      ⟨z, (generatedLaunchBranch_fixedPairSplit_iff
        (rate := rate) rewards C_star C_h q t (direction, i) s hs control0 a r.1).2 r.2.1⟩ =
      ReferenceActiveAffinePositiveTest.replaceCurrentPair
        (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs control0 C r)
        direction a := by
  have hrSelector : r.1 ∈ ReferenceSelectedAffinePairLaw.remainderSelectorEvent
      p q t (direction, i) := r.2.1.1
  dsimp
  rw [generatedNextInput_eq_activeReferenceInput (rate := rate) rewards C_star C_h q t
    direction i s hs control0 C a r]
  exact roundInputAtPairSplit_eq_replaceCurrentPair
    (activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs control0 C r)
    q direction i referencePairSample a r.1 hrSelector
private def generatedInputOnFiber
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i)))
    (z : Pair p × activeRetainedLaunch (rate := rate) rewards C_star C_h q t
      direction i s hs control0 C) : RoundInput p rate :=
  ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate
    (activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs control0 C z.2)
    ((ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm
      (z.1, z.2.1))
private theorem measurable_generatedInputOnFiber
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i))) (_hC : MeasurableSet C) :
    Measurable (fun z => generatedInputOnFiber (rate := rate) rewards C_star C_h q t
      direction i s hs control0 C z) := by
  let S := activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C
  let boundary := fun z : Pair p × S =>
    activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs control0 C z.2
  let source := fun z : Pair p × S =>
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm
      (z.1, z.2.1)
  have hb : Measurable boundary :=
    (measurable_activeBoundary (rate := rate) rewards C_star C_h q t direction i s hs
      control0 C).comp measurable_snd
  have hz : Measurable source :=
    (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).symm.measurable.comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  change Measurable (fun z : Pair p × S =>
    ReferenceFixedTimeSourceControlCoupling.roundInputAtSource p rate (boundary z) (source z))
  exact measurable_roundInputAtVariableSource boundary source hb hz
private def generatedFiberBase
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) :
    Set (Pair p × activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :=
  {z | directionPositive direction
      (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C z) = true ∧
    directionSent direction
      (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C z) ≠
        some candidate}
private def generatedFiberHash
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) :
    Set (Pair p × activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C) :=
  generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0 candidate C ∩
    {z | AffineChannelLaw.affineHash z.1 candidate = 1}
private theorem measurableSet_activeRemainderSet
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (C : Set (PairRemainder p q t (direction, i))) (hC : MeasurableSet C) :
    MeasurableSet
      (activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C) := by
  have hselector := ReferenceSelectedAffinePairLaw.measurableSet_remainderSelectorEvent
    p q t (direction, i)
  have hlaunch := (ReferenceRetainedBoundaryMeasurability.measurableSet_retainedLaunchStartSet
    rate rewards C_star C_h q t s hs control0).preimage
      (measurable_retainedControlProjection (p := p) (q := q) (t := t)
        (c := (direction, i)))
  have hbranch : MeasurableSet
      (generatedLaunchRemainderSet (rate := rate) rewards C_star C_h q t
        (direction, i) s control0) := by
    change MeasurableSet (ReferenceSelectedAffinePairLaw.remainderSelectorEvent
        p q t (direction, i) ∩
      retainedControlProjection (p := p) (q := q) (t := t) (c := (direction, i)) ⁻¹'
        ReferenceRetainedBoundaryMeasurability.retainedLaunchStartSet
          rate rewards C_star C_h q t s control0)
    exact hselector.inter hlaunch
  change MeasurableSet
    (generatedLaunchRemainderSet (rate := rate) rewards C_star C_h q t
      (direction, i) s control0 ∩ C)
  exact hbranch.inter hC
private theorem measurableSet_generatedFiberBase
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) (hC : MeasurableSet C) :
    MeasurableSet
      (generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0
        candidate C) := by
  let S := activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C
  let input := fun z : Pair p × S => generatedInputOnFiber (rate := rate) rewards C_star C_h
    q t direction i s hs control0 C z
  have hinput : Measurable input := measurable_generatedInputOnFiber (rate := rate)
    rewards C_star C_h q t direction i s hs control0 C hC
  have hpositive : Measurable (fun z : Pair p × S =>
      directionPositive direction (input z)) := by
    exact measurable_directionPositive.comp (measurable_const.prodMk hinput)
  have hsent : Measurable (fun z : Pair p × S =>
      directionSent direction (input z)) := by
    exact measurable_directionSent.comp (measurable_const.prodMk hinput)
  have hp : MeasurableSet {z : Pair p × S |
      directionPositive direction (input z) = true} :=
    hpositive (measurableSet_singleton true)
  have hsent' : MeasurableSet {z : Pair p × S |
      directionSent direction (input z) ≠ some candidate} := by
    change MeasurableSet ((fun z : Pair p × S => directionSent direction (input z)) ⁻¹'
      ({some candidate}ᶜ))
    exact hsent ((measurableSet_singleton (some candidate)).compl)
  change MeasurableSet
    ({z : Pair p × S |
      directionPositive direction (input z) = true} ∩
      {z | directionSent direction (input z) ≠ some candidate})
  exact hp.inter hsent'
private theorem measurableSet_generatedFiberHash
    {rate : RateInput p}
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) (hC : MeasurableSet C) :
    MeasurableSet
      (generatedFiberHash (rate := rate) rewards C_star C_h q t direction i s hs control0
        candidate C) := by
  have hbase := measurableSet_generatedFiberBase (rate := rate) rewards C_star C_h q t
    direction i s hs control0 candidate C hC
  have hhash : Measurable (fun z : Pair p ×
      activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i s hs control0 C =>
      AffineChannelLaw.affineHash z.1 candidate) :=
    (measurable_of_finite fun a : Pair p => AffineChannelLaw.affineHash a candidate).comp
      measurable_fst
  change MeasurableSet (generatedFiberBase (rate := rate) rewards C_star C_h q t direction i
    s hs control0 candidate C ∩ {z | AffineChannelLaw.affineHash z.1 candidate = 1})
  exact hbase.inter (hhash (measurableSet_singleton (1 : AffineChannelLaw.Bit)))
private def activePairRemainderMap {q : Fin (M p)} {t : Fin p.T} {direction : Fin 2}
    {i : Fin (p.m - 1)} {S : Set (PairRemainder p q t (direction, i))} :
    Pair p × {r : PairRemainder p q t (direction, i) // r ∈ S} →
      Pair p × PairRemainder p q t (direction, i) :=
  fun z => (z.1, z.2.1)
private theorem activePairRemainderMap_image_iff
    {q : Fin (M p)} {t : Fin p.T} {direction : Fin 2} {i : Fin (p.m - 1)}
    {S : Set (PairRemainder p q t (direction, i))}
    (F : Set (Pair p × {r : PairRemainder p q t (direction, i) // r ∈ S}))
    (a : Pair p) (r : PairRemainder p q t (direction, i)) :
    (a, r) ∈ activePairRemainderMap (S := S) '' F ↔
      ∃ hr : r ∈ S, (a, (⟨r, hr⟩ : {r : PairRemainder p q t (direction, i) // r ∈ S})) ∈ F := by
  constructor
  · rintro ⟨⟨a', r'⟩, hF, hmap⟩
    dsimp [activePairRemainderMap] at hmap
    rcases Prod.mk.inj hmap with ⟨rfl, hval⟩
    have hr : r ∈ S := hval ▸ r'.property
    have hr' : r' = (⟨r, hr⟩ : {r : PairRemainder p q t (direction, i) // r ∈ S}) :=
      Subtype.ext hval
    exact ⟨hr, by simpa [hr'] using hF⟩
  · rintro ⟨hr, hF⟩
    exact ⟨(a, ⟨r, hr⟩), hF, rfl⟩
private theorem generatedPositiveSourceEvent_pair_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i)))
    (a : Pair p) (r : PairRemainder p q t (direction, i)) :
    let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
    split.symm (a, r) ∈ generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t
      direction i s hs control0 candidate C ↔
    ∃ hr : r ∈ activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C,
      (a, (⟨r, hr⟩ : activeRetainedLaunch (rate := rate) rewards C_star C_h q t
        direction i s hs control0 C)) ∈
          generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0
            candidate C := by
  dsimp
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
  let source := split.symm (a, r)
  constructor
  · intro hevent
    change ∃ hsource : source ∈ generatedLaunchBranch (rate := rate) rewards C_star C_h q t
        (direction, i) s,
      (split source).2 ∈ C ∧
        directionPositive direction
          (generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t (direction, i)
            s hs control0 ⟨source, hsource⟩) = true ∧
        directionSent direction
          (generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t (direction, i)
            s hs control0 ⟨source, hsource⟩) ≠ some candidate at hevent
    rcases hevent with ⟨hsource, hC, hpositive, hsent⟩
    have hcoord : split source = (a, r) := split.apply_symm_apply (a, r)
    rw [hcoord] at hC
    have hbranch := (generatedLaunchBranch_fixedPairSplit_iff (rate := rate) rewards
      C_star C_h q t (direction, i) s hs control0 a r).mp hsource
    have hr : r ∈ activeRemainderSet (rate := rate) rewards C_star C_h q t direction i
        s control0 C := ⟨hbranch, hC⟩
    let retained : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i
        s hs control0 C := ⟨r, hr⟩
    have hcanonical : source ∈ generatedLaunchBranch (rate := rate) rewards C_star C_h q t
        (direction, i) s :=
      (generatedLaunchBranch_fixedPairSplit_iff (rate := rate) rewards C_star C_h q t
        (direction, i) s hs control0 a r).2 hbranch
    have hproof : hsource = hcanonical := Subsingleton.elim _ _
    subst hsource
    have hinput : generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t
        (direction, i) s hs control0 ⟨source, hcanonical⟩ =
        generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C
          (a, retained) := by
      simpa [generatedInputOnFiber, activeBoundary] using
        generatedNextInput_eq_activeReferenceInput (rate := rate) rewards C_star C_h q t
          direction i s hs control0 C a retained
    refine ⟨hr, ?_⟩
    change directionPositive direction
        (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C
          (a, retained)) = true ∧
      directionSent direction
        (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C
          (a, retained)) ≠ some candidate
    exact ⟨by rw [← hinput]; exact hpositive,
      by rw [← hinput]; exact hsent⟩
  · rintro ⟨hr, hfiber⟩
    let retained : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i
        s hs control0 C := ⟨r, hr⟩
    have hbranch : source ∈ generatedLaunchBranch (rate := rate) rewards C_star C_h q t
        (direction, i) s :=
      (generatedLaunchBranch_fixedPairSplit_iff (rate := rate) rewards C_star C_h q t
        (direction, i) s hs control0 a r).2 hr.1
    have hinput : generatedNextInputOfBranch (rate := rate) rewards C_star C_h q t
        (direction, i) s hs control0 ⟨source, hbranch⟩ =
        generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C
          (a, retained) := by
      simpa [generatedInputOnFiber, activeBoundary] using
        generatedNextInput_eq_activeReferenceInput (rate := rate) rewards C_star C_h q t
          direction i s hs control0 C a retained
    change directionPositive direction
        (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C
          (a, retained)) = true ∧
      directionSent direction
        (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs control0 C
          (a, retained)) ≠ some candidate at hfiber
    have hcoord : split source = (a, r) := split.apply_symm_apply (a, r)
    refine ⟨hbranch, ?_, ?_, ?_⟩
    · simpa [hcoord] using hr.2
    · rw [hinput]
      exact hfiber.1
    · rw [hinput]
      exact hfiber.2
private theorem generatedPositiveSourceEvent_eq_splitPreimage
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) :
    let S := activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C
    generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i s hs
      control0 candidate C =
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)) ⁻¹'
        (activePairRemainderMap (S := S) ''
          generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0
            candidate C) := by
  dsimp
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
  let S := activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C
  let fiber := generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0
    candidate C
  ext source
  rcases hcoord : split source with ⟨a, r⟩
  have hrec : split.symm (a, r) = source := by
    rw [← hcoord]
    exact split.symm_apply_apply source
  rw [← hrec]
  change split.symm (a, r) ∈ generatedPositiveSourceEvent
      (rate := rate) rewards C_star C_h q t direction i s hs control0 candidate C ↔
    split (split.symm (a, r)) ∈ activePairRemainderMap (S := S) '' fiber
  rw [split.apply_symm_apply]
  rw [activePairRemainderMap_image_iff]
  exact generatedPositiveSourceEvent_pair_iff (rate := rate) rewards C_star C_h q t
    direction i s hs control0 candidate C a r
private theorem generatedPositiveHashOneSourceEvent_pair_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i)))
    (a : Pair p) (r : PairRemainder p q t (direction, i)) :
    let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
    split.symm (a, r) ∈ generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t
      direction i s hs control0 candidate C ↔
    ∃ hr : r ∈ activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C,
      (a, (⟨r, hr⟩ : activeRetainedLaunch (rate := rate) rewards C_star C_h q t
        direction i s hs control0 C)) ∈
          generatedFiberHash (rate := rate) rewards C_star C_h q t direction i s hs control0
            candidate C := by
  dsimp
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
  have hpair : (((split.symm (a, r)).1.2 q).2 t).2 (direction, i) = a := by
    have hx := ReferenceSelectedAffinePairLaw.fixedPairSplit_pair p q t (direction, i)
      (split.symm (a, r))
    rw [split.apply_symm_apply] at hx
    exact hx.symm
  have hbaseIff := generatedPositiveSourceEvent_pair_iff (rate := rate) rewards C_star C_h
    q t direction i s hs control0 candidate C a r
  change (split.symm (a, r) ∈ generatedPositiveSourceEvent (rate := rate) rewards C_star C_h
      q t direction i s hs control0 candidate C ∧
    AffineChannelLaw.affineHash ((((split.symm (a, r)).1.2 q).2 t).2 (direction, i)) candidate = 1) ↔
    ∃ hr : r ∈ activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s
        control0 C,
      (a, (⟨r, hr⟩ : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i
        s hs control0 C)) ∈ generatedFiberHash (rate := rate) rewards C_star C_h q t direction i
          s hs control0 candidate C
  constructor
  · rintro ⟨hbase, hhash⟩
    rcases hbaseIff.mp hbase with ⟨hr, hfiber⟩
    refine ⟨hr, ?_⟩
    change (a, (⟨r, hr⟩ : activeRetainedLaunch (rate := rate) rewards C_star C_h q t
      direction i s hs control0 C)) ∈
        generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0
          candidate C ∧ AffineChannelLaw.affineHash a candidate = 1
    refine ⟨hfiber, ?_⟩
    simpa [hpair] using hhash
  · rintro ⟨hr, hfiber⟩
    change (a, (⟨r, hr⟩ : activeRetainedLaunch (rate := rate) rewards C_star C_h q t direction i
      s hs control0 C)) ∈
        generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs control0
          candidate C ∧ AffineChannelLaw.affineHash a candidate = 1 at hfiber
    rcases hfiber with ⟨hpositive, hhash⟩
    refine ⟨?_, ?_⟩
    · exact hbaseIff.mpr ⟨hr, hpositive⟩
    · simpa [hpair] using hhash
private theorem generatedPositiveHashOneSourceEvent_eq_splitPreimage
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2)
    (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) :
    let S := activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C
    generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t direction i s hs
      control0 candidate C =
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)) ⁻¹'
        (activePairRemainderMap (S := S) ''
          generatedFiberHash (rate := rate) rewards C_star C_h q t direction i s hs control0
            candidate C) := by
  dsimp
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
  let S := activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C
  let fiber := generatedFiberHash (rate := rate) rewards C_star C_h q t direction i s hs control0
    candidate C
  ext source
  rcases hcoord : split source with ⟨a, r⟩
  have hrec : split.symm (a, r) = source := by
    rw [← hcoord]
    exact split.symm_apply_apply source
  rw [← hrec]
  change split.symm (a, r) ∈ generatedPositiveHashOneSourceEvent
      (rate := rate) rewards C_star C_h q t direction i s hs control0 candidate C ↔
    split (split.symm (a, r)) ∈ activePairRemainderMap (S := S) '' fiber
  rw [split.apply_symm_apply]
  rw [activePairRemainderMap_image_iff]
  exact generatedPositiveHashOneSourceEvent_pair_iff (rate := rate) rewards C_star C_h
    q t direction i s hs control0 candidate C a r

/-- The literal generated active event is Borel. -/
theorem measurableSet_generatedPositiveSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) (hC : MeasurableSet C) :
    MeasurableSet (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t
      direction i s hs control0 candidate C) := by
  let S := activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C
  let fiber := generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs
    control0 candidate C
  have hS : MeasurableSet S :=
    measurableSet_activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s hs
      control0 C hC
  have hfiber : MeasurableSet fiber :=
    measurableSet_generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs
      control0 candidate C hC
  have hj : MeasurableEmbedding (activePairRemainderMap (S := S)) := by
    change MeasurableEmbedding (Prod.map (fun a : Pair p => a) (fun r : {r :
      PairRemainder p q t (direction, i) // r ∈ S} => (r : PairRemainder p q t (direction, i))))
    exact MeasurableEmbedding.prodMap MeasurableEmbedding.id
      (MeasurableEmbedding.subtype_coe hS)
  have himage : MeasurableSet (activePairRemainderMap (S := S) '' fiber) :=
    hj.measurableSet_image.mpr hfiber
  rw [generatedPositiveSourceEvent_eq_splitPreimage (rate := rate) rewards C_star C_h q t
    direction i s hs control0 candidate C]
  exact himage.preimage (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t
    (direction, i)).measurable

/-- The generated active event with affine hash value one is Borel. -/
theorem measurableSet_generatedPositiveHashOneSourceEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) (hC : MeasurableSet C) :
    MeasurableSet (generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t
      direction i s hs control0 candidate C) := by
  have hbase := measurableSet_generatedPositiveSourceEvent (rate := rate) rewards C_star C_h
    q t direction i s hs control0 candidate C hC
  have hpair : Measurable (fun z : SourceInput p => ((z.1.2 q).2 t).2 (direction, i)) := by
    convert measurable_fst.comp
      (ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)).measurable using 1
    funext z
    exact (ReferenceSelectedAffinePairLaw.fixedPairSplit_pair p q t (direction, i) z).symm
  have hhash : Measurable (fun z : SourceInput p =>
      AffineChannelLaw.affineHash (((z.1.2 q).2 t).2 (direction, i)) candidate) :=
    (measurable_of_finite fun a : Pair p => AffineChannelLaw.affineHash a candidate).comp hpair
  change MeasurableSet (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t
    direction i s hs control0 candidate C ∩
      {z | AffineChannelLaw.affineHash (((z.1.2 q).2 t).2 (direction, i)) candidate = 1})
  exact hbase.inter (hhash (measurableSet_singleton (1 : AffineChannelLaw.Bit)))
private theorem lintegral_affineSample_indicator (P : Pair p → Prop) :
    ∫⁻ a, AdaptiveAffineBatchTail.indicator (P a) ∂
        (AffineChannelLaw.jointLaw (B p)).toMeasure =
      ∑ a : Pair p, AffineChannelLaw.jointLaw (B p) a *
        AdaptiveAffineBatchTail.indicator (P a) := by
  classical
  rw [MeasureTheory.lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a ha
  rw [PMF.toMeasure_apply_singleton (AffineChannelLaw.jointLaw (B p)) a
    (measurableSet_singleton a)]
  ac_rfl

/-- Integrate the produced input over the genuine retained remainder. -/
private theorem generatedActiveRound_direction_hash_half
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (direction : Fin 2) (i : Fin (p.m - 1))
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (direction, i))) (hC : MeasurableSet C) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t
          direction i s hs control0 candidate C) =
      ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t
            direction i s hs control0 candidate C) := by
  classical
  let split := ReferenceSelectedAffinePairLaw.fixedPairSplit p q t (direction, i)
  let pairMeasure := (AffineChannelLaw.jointLaw (B p)).toMeasure
  let remainderMeasure := ReferenceSelectedAffinePairLaw.remainderLaw p q t (direction, i)
  let productMeasure := pairMeasure.prod remainderMeasure
  let S := activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s control0 C
  let fiberBase := generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs
    control0 candidate C
  let fiberHash := generatedFiberHash (rate := rate) rewards C_star C_h q t direction i s hs
    control0 candidate C
  let fullBase := activePairRemainderMap (S := S) '' fiberBase
  let fullHash := activePairRemainderMap (S := S) '' fiberHash
  have hS : MeasurableSet S :=
    measurableSet_activeRemainderSet (rate := rate) rewards C_star C_h q t direction i s hs
      control0 C hC
  have hFiberBase : MeasurableSet fiberBase :=
    measurableSet_generatedFiberBase (rate := rate) rewards C_star C_h q t direction i s hs
      control0 candidate C hC
  have hFiberHash : MeasurableSet fiberHash :=
    measurableSet_generatedFiberHash (rate := rate) rewards C_star C_h q t direction i s hs
      control0 candidate C hC
  have hEmbedding : MeasurableEmbedding (activePairRemainderMap (S := S)) := by
    change MeasurableEmbedding (Prod.map (fun a : Pair p => a) (fun r : {r :
      PairRemainder p q t (direction, i) // r ∈ S} => (r : PairRemainder p q t (direction, i))))
    exact MeasurableEmbedding.prodMap MeasurableEmbedding.id
      (MeasurableEmbedding.subtype_coe hS)
  have hFullBase : MeasurableSet fullBase := hEmbedding.measurableSet_image.mpr hFiberBase
  have hFullHash : MeasurableSet fullHash := hEmbedding.measurableSet_image.mpr hFiberHash
  have hBaseEvent : MeasurableSet
      (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
        s hs control0 candidate C) :=
    measurableSet_generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
      s hs control0 candidate C hC
  have hHashEvent : MeasurableSet
      (generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t direction i
        s hs control0 candidate C) :=
    measurableSet_generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t
      direction i s hs control0 candidate C hC
  have hBasePreimage : split.symm ⁻¹'
      generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
        s hs control0 candidate C = fullBase := by
    rw [generatedPositiveSourceEvent_eq_splitPreimage (rate := rate) rewards C_star C_h q t
      direction i s hs control0 candidate C]
    ext z
    change split (split.symm z) ∈ fullBase ↔ z ∈ fullBase
    rw [split.apply_symm_apply]
  have hHashPreimage : split.symm ⁻¹'
      generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t direction i
        s hs control0 candidate C = fullHash := by
    rw [generatedPositiveHashOneSourceEvent_eq_splitPreimage
      (rate := rate) rewards C_star C_h q t direction i s hs control0 candidate C]
    ext z
    change split (split.symm z) ∈ fullHash ↔ z ∈ fullHash
    rw [split.apply_symm_apply]
  have hBaseIntegrand : Measurable (fullBase.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hFullBase
  have hHashIntegrand : Measurable (fullHash.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hFullHash
  have hOneStep (x : RoundInput p rate) :
      (∑ a : Pair p, AffineChannelLaw.jointLaw (B p) a *
        AdaptiveAffineBatchTail.indicator
          (directionPositive direction
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair x direction a) = true ∧
            directionSent direction x ≠ some candidate ∧
            AffineChannelLaw.affineHash a candidate = 1)) =
      ((1 : ℝ≥0∞) / 2) * ∑ a : Pair p,
        AffineChannelLaw.jointLaw (B p) a * AdaptiveAffineBatchTail.indicator
          (directionPositive direction
              (ReferenceActiveAffinePositiveTest.replaceCurrentPair x direction a) = true ∧
            directionSent direction x ≠ some candidate) := by
    fin_cases direction
    · exact ReferenceDownPhysicalHashRule.down_jointLaw_hash_half x candidate
    · exact ReferenceUpPhysicalHashRule.upPositive_one_step_half x candidate
  have hFiberHalf (r : PairRemainder p q t (direction, i)) :
      ∫⁻ a, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) (a, r) ∂pairMeasure =
        ((1 : ℝ≥0∞) / 2) *
          ∫⁻ a, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) (a, r) ∂pairMeasure := by
    have hhashConvert :
        (fun a : Pair p => fullHash.indicator (fun _ => (1 : ℝ≥0∞)) (a, r)) =
          fun a => AdaptiveAffineBatchTail.indicator ((a, r) ∈ fullHash) := by
      funext a
      simp [Set.indicator, AdaptiveAffineBatchTail.indicator]
    have hbaseConvert :
        (fun a : Pair p => fullBase.indicator (fun _ => (1 : ℝ≥0∞)) (a, r)) =
          fun a => AdaptiveAffineBatchTail.indicator ((a, r) ∈ fullBase) := by
      funext a
      simp [Set.indicator, AdaptiveAffineBatchTail.indicator]
    rw [hhashConvert, hbaseConvert,
      lintegral_affineSample_indicator (fun a => (a, r) ∈ fullHash),
      lintegral_affineSample_indicator (fun a => (a, r) ∈ fullBase)]
    by_cases hr : r ∈ S
    · let retained : activeRetainedLaunch
        (rate := rate) rewards C_star C_h q t direction i s hs control0 C := ⟨r, hr⟩
      have hinput (a : Pair p) :
          generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
              control0 C (a, retained) =
            ReferenceActiveAffinePositiveTest.replaceCurrentPair
              (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs
                control0 C retained) direction a := by
        have hgen := generatedNextInput_eq_activeReferenceInput
          (rate := rate) rewards C_star C_h q t direction i s hs control0 C a retained
        have hrep := actualGeneratedInput_eq_replacement
          (rate := rate) rewards C_star C_h q t direction i s hs control0 C a retained
        change _ = _ at hgen
        change _ = _ at hrep
        exact hgen.symm.trans hrep
      have hbaseMem (a : Pair p) :
          (a, r) ∈ fullBase ↔
            directionPositive direction
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair
                  (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs
                    control0 C retained) direction a) = true ∧
              directionSent direction
                (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C retained) ≠ some candidate := by
        change (a, r) ∈ activePairRemainderMap (S := S) '' fiberBase ↔ _
        rw [activePairRemainderMap_image_iff]
        constructor
        · rintro ⟨hr', hfiber⟩
          have hrEq : (⟨r, hr'⟩ : activeRetainedLaunch
              (rate := rate) rewards C_star C_h q t direction i s hs control0 C) = retained :=
            Subtype.ext rfl
          rw [hrEq] at hfiber
          change directionPositive direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) = true ∧
              directionSent direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) ≠ some candidate at hfiber
          rw [hinput, directionSent_replace] at hfiber
          exact hfiber
        · intro h
          refine ⟨hr, ?_⟩
          change directionPositive direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) = true ∧
              directionSent direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) ≠ some candidate
          rw [hinput, directionSent_replace]
          exact h
      have hhashMem (a : Pair p) :
          (a, r) ∈ fullHash ↔
            directionPositive direction
                (ReferenceActiveAffinePositiveTest.replaceCurrentPair
                  (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs
                    control0 C retained) direction a) = true ∧
              directionSent direction
                (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C retained) ≠ some candidate ∧
              AffineChannelLaw.affineHash a candidate = 1 := by
        change (a, r) ∈ activePairRemainderMap (S := S) '' fiberHash ↔ _
        rw [activePairRemainderMap_image_iff]
        constructor
        · rintro ⟨hr', hfiber⟩
          have hrEq : (⟨r, hr'⟩ : activeRetainedLaunch
              (rate := rate) rewards C_star C_h q t direction i s hs control0 C) = retained :=
            Subtype.ext rfl
          rw [hrEq] at hfiber
          change ((a, retained) ∈ fiberBase ∧ AffineChannelLaw.affineHash a candidate = 1)
            at hfiber
          rcases hfiber with ⟨hbase, hhash⟩
          change directionPositive direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) = true ∧
              directionSent direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) ≠ some candidate at hbase
          rw [hinput, directionSent_replace] at hbase
          exact ⟨hbase.1, hbase.2, hhash⟩
        · rintro ⟨hpositive, hsent, hhash⟩
          refine ⟨hr, ?_⟩
          change ((a, retained) ∈ fiberBase ∧ AffineChannelLaw.affineHash a candidate = 1)
          refine ⟨?_, hhash⟩
          change directionPositive direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) = true ∧
              directionSent direction
                (generatedInputOnFiber (rate := rate) rewards C_star C_h q t direction i s hs
                  control0 C (a, retained)) ≠ some candidate
          rw [hinput, directionSent_replace]
          exact ⟨hpositive, hsent⟩
      simpa [AdaptiveAffineBatchTail.indicator, hhashMem, hbaseMem] using
        hOneStep (activeReferenceInput (rate := rate) rewards C_star C_h q t direction i s hs
          control0 C retained)
    · have hfalseBase (a : Pair p) : (a, r) ∉ fullBase := by
        intro h
        rcases (activePairRemainderMap_image_iff (S := S) fiberBase a r).mp h with
          ⟨hr', _⟩
        exact hr hr'
      have hfalseHash (a : Pair p) : (a, r) ∉ fullHash := by
        intro h
        rcases (activePairRemainderMap_image_iff (S := S) fiberHash a r).mp h with
          ⟨hr', _⟩
        exact hr hr'
      simp [AdaptiveAffineBatchTail.indicator, hfalseBase, hfalseHash]
  have hBaseInnerMeas : Measurable (fun r =>
      ∫⁻ a, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) (a, r) ∂pairMeasure) :=
    (measurable_swap_iff.mpr hBaseIntegrand).lintegral_prod_right'
  have hProductIdentity :
      ∫⁻ z, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure =
        ((1 : ℝ≥0∞) / 2) *
          ∫⁻ z, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
    calc
      ∫⁻ z, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure =
          ∫⁻ r, ∫⁻ a, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) (a, r)
            ∂pairMeasure ∂remainderMeasure :=
        MeasureTheory.lintegral_prod_symm' _ hHashIntegrand
      _ = ∫⁻ r, ((1 : ℝ≥0∞) / 2) *
            ∫⁻ a, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) (a, r)
              ∂pairMeasure ∂remainderMeasure := by
        apply MeasureTheory.lintegral_congr
        exact hFiberHalf
      _ = ((1 : ℝ≥0∞) / 2) *
            ∫⁻ r, ∫⁻ a, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) (a, r)
              ∂pairMeasure ∂remainderMeasure :=
        MeasureTheory.lintegral_const_mul _ hBaseInnerMeas
      _ = ((1 : ℝ≥0∞) / 2) *
            ∫⁻ z, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
        rw [← MeasureTheory.lintegral_prod_symm' _ hBaseIntegrand]
  have hMeasureHash :
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t
            direction i s hs control0 candidate C) =
        ∫⁻ z, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
    calc
      _ = productMeasure (split.symm ⁻¹'
          generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t
            direction i s hs control0 candidate C) := by
        rw [← (ReferenceSelectedAffinePairLaw.fixedPairSplit_measurePreserving_symm
          p q t (direction, i)).map_eq,
          Measure.map_apply split.symm.measurable hHashEvent]
      _ = productMeasure fullHash := by rw [hHashPreimage]
      _ = ∫⁻ z, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure :=
        (MeasureTheory.lintegral_indicator_one hFullHash).symm
  have hMeasureBase :
      BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
            s hs control0 candidate C) =
        ∫⁻ z, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := by
    calc
      _ = productMeasure (split.symm ⁻¹'
          generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
            s hs control0 candidate C) := by
        rw [← (ReferenceSelectedAffinePairLaw.fixedPairSplit_measurePreserving_symm
          p q t (direction, i)).map_eq,
          Measure.map_apply split.symm.measurable hBaseEvent]
      _ = productMeasure fullBase := by rw [hBasePreimage]
      _ = ∫⁻ z, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure :=
        (MeasureTheory.lintegral_indicator_one hFullBase).symm
  calc
    _ = ∫⁻ z, fullHash.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := hMeasureHash
    _ = ((1 : ℝ≥0∞) / 2) *
        ∫⁻ z, fullBase.indicator (fun _ => (1 : ℝ≥0∞)) z ∂productMeasure := hProductIdentity
    _ = ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t direction i
            s hs control0 candidate C) := by
      rw [hMeasureBase]

/-- Source-generated active-round DOWN hash-half identity. -/
theorem downGeneratedPositive_hash_half
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (0, i))) (hC : MeasurableSet C) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t 0 i
          s hs control0 candidate C) =
      ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t 0 i
            s hs control0 candidate C) :=
  generatedActiveRound_direction_hash_half (rate := rate) rewards C_star C_h q t 0 i s hs control0 candidate C hC

/-- Source-generated active-round UP hash-half identity. -/
theorem upGeneratedPositive_hash_half
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (i : Fin (p.m - 1)) (s : ℕ) (hs : s ≤ t.val)
    (control0 : TimeControl p) (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (C : Set (PairRemainder p q t (1, i))) (hC : MeasurableSet C) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
        (generatedPositiveHashOneSourceEvent (rate := rate) rewards C_star C_h q t 1 i
          s hs control0 candidate C) =
      ((1 : ℝ≥0∞) / 2) *
        BootstrapPrivateRoundStreams.sourceInputLaw p
          (generatedPositiveSourceEvent (rate := rate) rewards C_star C_h q t 1 i
            s hs control0 candidate C) :=
  generatedActiveRound_direction_hash_half (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate C hC
end Bandits.Support.ReferenceGeneratedAffineHashHalf
end
