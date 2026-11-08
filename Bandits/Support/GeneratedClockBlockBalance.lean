/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDownCountMean
public import Bandits.Support.BootstrapIntervalBounds
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapOriginalScalarLaw
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ConstructorDimensions
public import Bandits.Support.GeneratedBootstrapFiltration
public import Bandits.Support.GeneratedBootstrapRoundLaw
public import Bandits.Support.GeneratedClockConditionalMeans
public import Bandits.Support.IdentificationLocalRowBalance
public import Bandits.Support.IdentificationRectangleExclusion
public import Bandits.Support.ReferenceInitializationRun

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generated clock block balance

The actual generated one-clock conditional means have the appendix B block
budget on the literal positive rounded-reward support, and the actual generated
discovery clock inherits the physical DATA-positive cap from ID property (ii).

Sources: `sources/zip4/manuscript/appendix_b_communication.tex:192-207,398-451`
and `sources/zip4/manuscript/07_public_setup.tex:87-112`.

These are internal results for the original coordinate law and the accepted
generated run. They assert neither a probability tail nor a productive-block
probability, a gain bound, decoder acceptance, or manuscript closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.GeneratedClockBlockBalance

open MeasureTheory
open ConstructorDimensions BootstrapDimensions CompletePublicTable
open BootstrapPhysicalBlock BootstrapModeService FiniteBanditModel
open ActiveRoundActions BootstrapOriginalScalarLaw BootstrapPrivateRoundStreams
open GeneratedBootstrapFiltration GeneratedBootstrapRoundLaw
open ReferenceInitializationRun
open scoped BigOperators Classical

variable {p : ConstructorDimensions.Parameters}

/-- Every clipped calendar block has a positive integer length. -/
theorem calendarBlock_start_lt_stop_local
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p)) :
    s.val * B_boot p < min p.T ((s.val + 1) * B_boot p) := by
  rcases BootstrapDimensions.calendarBlock_nonempty p s with ⟨t, ht⟩
  rcases (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht with
    ⟨hstart, hstop⟩
  exact Nat.lt_of_le_of_lt hstart hstop

/-- The literal rounded-reward support on one clipped calendar block. -/
def positiveRewardSupport (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a : Fin p.K) : Finset (Fin p.T) :=
  (calendarBlock p s).filter fun t =>
    0 < RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t a)

/-- The support set packaged in the existing local-row-balance carrier. -/
def positiveRewardBlockSupport (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (a : Fin p.K) : IdentificationLocalRowBalance.BlockSupport p s :=
  ⟨positiveRewardSupport p s rewards a, Finset.filter_subset _ _⟩

/-- The paper's `S_s(a)` is the cardinality of the literal rounded-reward
support used by the local ID-row predicate. -/
theorem rewardSupportCount_eq_positiveRewardSupport_card
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K) :
    BootstrapDownCountMean.rewardSupportCount p s rewards a =
      (positiveRewardSupport p s rewards a).card := by
  classical
  simp [BootstrapDownCountMean.rewardSupportCount,
    BootstrapDownCountMean.rewardSupport, positiveRewardSupport,
    Finset.sum_boole]

/-- The left endpoint of the actual clipped calendar block. -/
def blockStartEndpoint (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) : IdentificationLocalRowBalance.BlockEndpoint p s :=
  ⟨s.val * B_boot p, le_rfl,
    Nat.le_of_lt (calendarBlock_start_lt_stop_local p s)⟩

/-- The right endpoint of the actual clipped calendar block. -/
def blockStopEndpoint (p : ConstructorDimensions.Parameters)
    (s : Fin (n_boot p)) : IdentificationLocalRowBalance.BlockEndpoint p s :=
  ⟨min p.T ((s.val + 1) * B_boot p),
    Nat.le_of_lt (calendarBlock_start_lt_stop_local p s), le_rfl⟩

/-- The honest phase endpoint: the first block round whose actual physical
pre-choice mode is MULTICAST, or the clipped block stop if no such round
exists. This definition handles an empty prefix and an empty suffix directly. -/
noncomputable def firstMulticastEndpoint
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    {r : Fin (n_boot p)} (x : BootstrapPhysicalBlock.Input p r) :
    IdentificationLocalRowBalance.BlockEndpoint p s := by
  classical
  let multicastRounds := (calendarBlock p s).filter fun t =>
    (BootstrapPhysicalBlock.run x t.val).mode = BootstrapPhysicalBlock.Mode.multicast
  by_cases hm : multicastRounds.Nonempty
  · let t := multicastRounds.min' hm
    have htm : t ∈ multicastRounds := multicastRounds.min'_mem hm
    have ht := (Finset.mem_filter.mp htm).1
    rcases (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht with
      ⟨hstart, hstop⟩
    exact ⟨t.val, hstart, Nat.le_of_lt hstop⟩
  · exact blockStopEndpoint p s

/-- The two disjoint calendar phases in the actual generated block, weighted
by the original private ID row and the literal rounded-reward support. -/
def blockPhaseIndicator
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    {r : Fin (n_boot p)} (x : BootstrapPhysicalBlock.Input p r)
    (theta : IdentificationLocalRowBalance.BlockEndpoint p s)
    (j : {j // j ∈ x.uninformed}) (t : Fin p.T) : ℝ :=
  (if t ∈ IdentificationLocalRowBalance.calendarInterval p s
        (blockStartEndpoint p s) theta ∧
      t ∈ positiveRewardSupport p s rewards a ∧
      x.ids (x.privateId j) t = true then (1 : ℝ) else 0) +
    (if t ∈ IdentificationLocalRowBalance.calendarInterval p s theta
        (blockStopEndpoint p s) ∧
      t ∈ positiveRewardSupport p s rewards a ∧
      x.ids (x.privateId j) t = false then (1 : ℝ) else 0)

private theorem firstMulticastEndpoint_mode_split
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    {r : Fin (n_boot p)} (x : BootstrapPhysicalBlock.Input p r)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    (t.val < (firstMulticastEndpoint p s x).val →
      (BootstrapPhysicalBlock.run x t.val).mode = BootstrapPhysicalBlock.Mode.discover) ∧
    ((firstMulticastEndpoint p s x).val ≤ t.val →
      (BootstrapPhysicalBlock.run x t.val).mode = BootstrapPhysicalBlock.Mode.multicast) := by
  classical
  let multicastRounds := (calendarBlock p s).filter fun u =>
    (BootstrapPhysicalBlock.run x u.val).mode = BootstrapPhysicalBlock.Mode.multicast
  by_cases hm : multicastRounds.Nonempty
  · let first := multicastRounds.min' hm
    have hfirstMem : first ∈ multicastRounds := multicastRounds.min'_mem hm
    have hfirstBlock := (Finset.mem_filter.mp hfirstMem).1
    have hfirstMode := (Finset.mem_filter.mp hfirstMem).2
    have hfirstVal : (firstMulticastEndpoint p s x).val = first.val := by
      simp [firstMulticastEndpoint, multicastRounds, hm, first]
    constructor
    · intro hlt
      by_contra hnot
      have hmode : (BootstrapPhysicalBlock.run x t.val).mode =
          BootstrapPhysicalBlock.Mode.multicast := by
        cases hcase : (BootstrapPhysicalBlock.run x t.val).mode <;> simp_all
      have htmem : t ∈ multicastRounds := Finset.mem_filter.mpr ⟨ht, hmode⟩
      have hmin := multicastRounds.min'_le t htmem
      have hminval : (firstMulticastEndpoint p s x).val ≤ t.val := by
        rw [hfirstVal]
        exact Fin.le_iff_val_le_val.mp hmin
      exact (not_lt_of_ge hminval) hlt
    · intro hle
      have hle' : first.val ≤ t.val := by
        rw [hfirstVal] at hle
        exact hle
      have hstartMode :
          (BootstrapPhysicalBlock.run x first.val).mode =
            BootstrapPhysicalBlock.Mode.multicast := hfirstMode
      have hstep : t.val = first.val + (t.val - first.val) := by omega
      rw [hstep, BootstrapPhysicalBlock.run_eq_of_multicast x first.val
        (t.val - first.val) hstartMode]
      exact hstartMode
  · have htheta : (firstMulticastEndpoint p s x).val =
        min p.T ((s.val + 1) * B_boot p) := by
      simp [firstMulticastEndpoint, multicastRounds, hm, blockStopEndpoint]
    constructor
    · intro _
      have hnot : (BootstrapPhysicalBlock.run x t.val).mode ≠
          BootstrapPhysicalBlock.Mode.multicast := by
        intro hmode
        exact hm ⟨t, Finset.mem_filter.mpr ⟨ht, hmode⟩⟩
      cases hmode : (BootstrapPhysicalBlock.run x t.val).mode <;> simp_all
    · intro hle
      have htstop := (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht |>.2
      rw [htheta] at hle
      omega

/-- The actual generated boundary guard for one focal follower and one arm.
The boundary must process opportunity `s`; the incoming set, activity, held
arm, coordinator target, isolation of the other incoming followers, and the
original ID row's existing local-balance predicate are all evaluated on the
accepted physical input of that boundary. -/
def generatedClockBlockGuard
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (e : Coordinates p) : Prop :=
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  boundary.crossing = none ∧
    ∀ h : boundary.completed < n_boot p,
      let x := ReferenceInitializationRun.physical source boundary h
      focal ∈ x.uninformed ∧
        ∀ hm : focal ∈ x.uninformed,
          let j : {j // j ∈ x.uninformed} := ⟨focal, hm⟩
          x.active j = true ∧ x.held j = a ∧ x.target = a ∧
            (∀ k : {j // j ∈ x.uninformed}, k ≠ j → x.active k = false) ∧
            IdentificationLocalRowBalance.localBalanceRowPredicate p s
              (positiveRewardBlockSupport p s rewards a)
              (ids (x.privateId j))

theorem processedBoundary_valid
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (e : Coordinates p)
    (hcross : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none) :
    (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).completed < n_boot p := by
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  have hnot : ¬ boundary.crossing.isSome = true := by
    rw [hcross]
    exact Bool.false_ne_true
  have hprogress := (ReferenceInitializationRun.run_progress source s.val s.isLt.le).resolve_left hnot
  exact hprogress.symm ▸ s.isLt

private theorem processedDescriptor_eq_actual
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (s : Fin (n_boot p)) (e : Coordinates p)
    (hcross : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none)
    (t : Fin p.T) :
    GeneratedBootstrapRoundLaw.descriptor p ids rewards C_star C_h eta s t e =
      some ((ReferenceInitializationRun.run
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val),
        (BootstrapPhysicalInput.currentBlockDrawProfile p s
          (ReferenceInitializationRun.run
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).numerators
          (ReferenceInitializationRun.run
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).weight_ge_one
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e).coordinates,
          ((ReferenceInitializationRun.physical
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
            (ReferenceInitializationRun.run
              (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)
            (processedBoundary_valid ids rewards C_star C_h eta s e hcross)).target,
            BootstrapPhysicalBlock.run
              (ReferenceInitializationRun.physical
                (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
                (ReferenceInitializationRun.run
                  (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)
                (processedBoundary_valid ids rewards C_star C_h eta s e hcross)) t.val))) := by
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hcross
  have hnext : ReferenceInitializationRun.nextBlock boundary hvalid = s :=
    GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e hcross hvalid
  change GeneratedBootstrapRoundLaw.descriptorAtBoundary p source boundary t = _
  apply (GeneratedBootstrapRoundLaw.descriptorAtBoundary_eq_some_iff p source boundary boundary t
    (BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators
      boundary.weight_ge_one source.coordinates)
    (ReferenceInitializationRun.physical source boundary hvalid).target
    (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical source boundary hvalid) t.val)).2
  refine ⟨rfl, hcross, ⟨hvalid, ?_, rfl, rfl⟩⟩
  rw [hnext]

private theorem generatedDiscoveryClock_sourceIndex_eq_physical
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (e : Coordinates p)
    (hcross : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    GeneratedClockConditionalMeans.discoveryClock ids rewards C_star C_h eta
      rowCompletion scalarCompletion s (GeneratedClockConditionalMeans.sourceClockIndex t) e =
    if t ∈ BootstrapPhysicalBlock.discoveryPositiveRounds
      (ReferenceInitializationRun.physical
        (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
        (ReferenceInitializationRun.run
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)
        (processedBoundary_valid ids rewards C_star C_h eta s e hcross))
    then 1 else 0 := by
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hcross
  let x := ReferenceInitializationRun.physical source boundary hvalid
  let profile := BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators
    boundary.weight_ge_one source.coordinates
  let st := BootstrapPhysicalBlock.run x t.val
  have hdesc := processedDescriptor_eq_actual ids rewards C_star C_h eta s e hcross t
  have htest := GeneratedClockConditionalMeans.actual_discoveryTest_eq_physical
    ids rewards C_star C_h eta rowCompletion scalarCompletion s t e boundary profile x.target st
    hdesc hvalid
  rw [GeneratedClockConditionalMeans.discoveryClock_at_sourceIndex ids rewards C_star C_h eta
    rowCompletion scalarCompletion s t ht e]
  simp [GeneratedBootstrapFiltration.testValue, hdesc,
    GeneratedBootstrapRoundLaw.current] at htest ⊢
  have hnext : ReferenceInitializationRun.nextBlock boundary hvalid = s :=
    GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e hcross hvalid
  have hpositive : t ∈ BootstrapPhysicalBlock.discoveryPositiveRounds x ↔
      st.mode = BootstrapPhysicalBlock.Mode.discover ∧
        BootstrapPhysicalBlock.slot x t = PublicDiscreteDraws.dataSlot ∧
        0 < BootstrapPhysicalBlock.feedback x st t
          (ActiveRoundActions.coordinator p.two_le_m) := by
    simp only [BootstrapPhysicalBlock.discoveryPositiveRounds, Finset.mem_filter]
    constructor
    · rintro ⟨_, hmode, hslot, hfeedback⟩
      exact ⟨hmode, hslot, hfeedback⟩
    · rintro ⟨hmode, hslot, hfeedback⟩
      refine ⟨?_, hmode, hslot, hfeedback⟩
      simpa [hnext] using ht
  simpa [hpositive, x, source, boundary, st] using htest

private theorem generatedDiscoveryClock_sourceIndex_eq_zero_of_stopped
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (e : Coordinates p)
    (hcross : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing ≠ none)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    GeneratedClockConditionalMeans.discoveryClock ids rewards C_star C_h eta
      rowCompletion scalarCompletion s (GeneratedClockConditionalMeans.sourceClockIndex t) e = 0 := by
  rw [GeneratedClockConditionalMeans.discoveryClock_at_sourceIndex ids rewards C_star C_h eta
    rowCompletion scalarCompletion s t ht e]
  have hnone := (GeneratedBootstrapRoundLaw.descriptor_eq_none_iff ids rewards C_star C_h eta s t e).2 hcross
  simp [GeneratedBootstrapFiltration.testValue, hnone,
    GeneratedClockConditionalMeans.discoveryTest]

/-- Pointwise transport from the generated source-indexed discovery clock to
the accepted physical DISCOVER DATA-positive set, on a processed boundary. -/
theorem generatedDiscoveryClock_blockSum_eq_physicalCount
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (e : Coordinates p)
    (hcross : (ReferenceInitializationRun.run
      (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val).crossing = none) :
    (∑ t ∈ calendarBlock p s,
      GeneratedClockConditionalMeans.discoveryClock ids rewards C_star C_h eta
        rowCompletion scalarCompletion s (GeneratedClockConditionalMeans.sourceClockIndex t) e) =
      (BootstrapPhysicalBlock.discoveryPositiveRounds
        (ReferenceInitializationRun.physical
          (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e)
          (ReferenceInitializationRun.run
            (GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e) s.val)
          (processedBoundary_valid ids rewards C_star C_h eta s e hcross))).card := by
  classical
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hcross
  let x := ReferenceInitializationRun.physical source boundary hvalid
  have hnext : ReferenceInitializationRun.nextBlock boundary hvalid = s :=
    GeneratedBootstrapRoundLaw.processed_nextBlock ids rewards C_star C_h eta s e hcross hvalid
  have hpoint := fun t ht => generatedDiscoveryClock_sourceIndex_eq_physical
    ids rewards C_star C_h eta rowCompletion scalarCompletion s e hcross t ht
  calc
    _ = ∑ t ∈ calendarBlock p s,
        if t ∈ BootstrapPhysicalBlock.discoveryPositiveRounds x then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hpoint t ht
    _ = ((calendarBlock p s).filter
        (fun t => t ∈ BootstrapPhysicalBlock.discoveryPositiveRounds x)).card := by
      rw [Finset.sum_boole]
    _ = (BootstrapPhysicalBlock.discoveryPositiveRounds x).card := by
      have hsubset : BootstrapPhysicalBlock.discoveryPositiveRounds x ⊆ calendarBlock p s :=
        fun t ht => by
          have hblock := (Finset.mem_filter.mp ht).1
          simpa [hnext] using hblock
      have hfilter : (calendarBlock p s).filter
          (fun t => t ∈ BootstrapPhysicalBlock.discoveryPositiveRounds x) =
            BootstrapPhysicalBlock.discoveryPositiveRounds x := by
        ext t
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun ht => ⟨hsubset ht, ht⟩⟩
      rw [hfilter]

/-- The generated discovery clock's block cap is the existing physical
discovery-positive cap transported through pointwise actual descriptor and
clock identities. It requires the literal source ID-array property (ii). -/
theorem generatedDiscoveryClock_blockSum_le_of_idArrayPropertyII
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (e : Coordinates p)
    (hid : IdentificationRectangleExclusion.idArrayPropertyII p ids) :
    (∑ t ∈ calendarBlock p s,
      GeneratedClockConditionalMeans.discoveryClock ids rewards C_star C_h eta
        rowCompletion scalarCompletion s (GeneratedClockConditionalMeans.sourceClockIndex t) e) ≤
      (6 * b_N p : ℝ) := by
  classical
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  by_cases hcross : boundary.crossing = none
  · rw [generatedDiscoveryClock_blockSum_eq_physicalCount ids rewards C_star C_h eta
      rowCompletion scalarCompletion s e hcross]
    let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hcross
    let x := ReferenceInitializationRun.physical source boundary hvalid
    have hids : x.ids = ids := by
      simp [x, source, boundary, ReferenceInitializationRun.physical,
        GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates,
        BootstrapPhysicalInput.blockInput]
    have hrect : BootstrapPhysicalBlock.rectangle_exclusion x.ids := by
      simpa [BootstrapPhysicalBlock.rectangle_exclusion,
        IdentificationRectangleExclusion.idArrayPropertyII, hids] using hid
    exact_mod_cast BootstrapPhysicalBlock.discoveryPositiveRounds_card_le x hrect
  · have hzero : ∀ t ∈ calendarBlock p s,
        GeneratedClockConditionalMeans.discoveryClock ids rewards C_star C_h eta
          rowCompletion scalarCompletion s (GeneratedClockConditionalMeans.sourceClockIndex t) e = 0 :=
      fun t ht => generatedDiscoveryClock_sourceIndex_eq_zero_of_stopped ids rewards C_star C_h eta
        rowCompletion scalarCompletion s e (by simpa [boundary, source] using hcross) t ht
    calc
      _ = ∑ t ∈ calendarBlock p s, (0 : ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hzero t ht
      _ = 0 := by simp
      _ ≤ (6 * b_N p : ℝ) := by positivity

private theorem localBalance_two_phase_counts
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (support : IdentificationLocalRowBalance.BlockSupport p s)
    (row : Fin p.T → Bool)
    (theta : IdentificationLocalRowBalance.BlockEndpoint p s)
    (hrow : IdentificationLocalRowBalance.localBalanceRowPredicate p s support row) :
    ((IdentificationLocalRowBalance.localBalanceIDCount
        (IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta)
        support.1 true row : ℕ) : ℝ) +
      ((IdentificationLocalRowBalance.localBalanceIDCount
        (IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s))
        support.1 false row : ℕ) : ℝ) ≥
      (support.1.card : ℝ) / 3 - 16 * (b_N p : ℝ) := by
  classical
  let prefixInterval := IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta
  let suffixInterval := IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s)
  have hprefix := hrow (blockStartEndpoint p s) theta
    (by exact theta.property.1) true
  have hsuffix := hrow theta (blockStopEndpoint p s)
    (by exact theta.property.2) false
  have hprefixSupport :
      IdentificationLocalRowBalance.localBalanceSupportCount prefixInterval support.1 =
        (support.1.filter fun t => t.val < theta.val).card := by
    unfold IdentificationLocalRowBalance.localBalanceSupportCount
    have hset : prefixInterval ∩ support.1 = support.1.filter fun t => t.val < theta.val := by
      unfold prefixInterval
      ext t
      simp only [Finset.mem_inter, Finset.mem_filter]
      rw [IdentificationLocalRowBalance.mem_calendarInterval_iff]
      constructor
      · rintro ⟨⟨_, _, hstart, htheta⟩, hsupport⟩
        exact ⟨hsupport, htheta⟩
      · rintro ⟨hsupport, htheta⟩
        have htblock := support.property hsupport
        rcases (BootstrapDimensions.mem_calendarBlock_iff p s t).mp htblock with
          ⟨hstart, hstop⟩
        exact ⟨⟨hstart, hstop, hstart, htheta⟩,
          hsupport⟩
    rw [hset]
  have hsuffixSupport :
      IdentificationLocalRowBalance.localBalanceSupportCount suffixInterval support.1 =
        (support.1.filter fun t => theta.val ≤ t.val).card := by
    unfold IdentificationLocalRowBalance.localBalanceSupportCount
    have hset : suffixInterval ∩ support.1 = support.1.filter fun t => theta.val ≤ t.val := by
      unfold suffixInterval
      ext t
      simp only [Finset.mem_inter, Finset.mem_filter]
      rw [IdentificationLocalRowBalance.mem_calendarInterval_iff]
      constructor
      · rintro ⟨⟨_, _, htheta, _⟩, hsupport⟩
        exact ⟨hsupport, htheta⟩
      · rintro ⟨hsupport, htheta⟩
        have htblock := support.property hsupport
        rcases (BootstrapDimensions.mem_calendarBlock_iff p s t).mp htblock with
          ⟨hstart, hstop⟩
        exact ⟨⟨hstart, hstop, htheta, hstop⟩,
          hsupport⟩
    rw [hset]
  have hsupportSplit :
      IdentificationLocalRowBalance.localBalanceSupportCount prefixInterval support.1 +
        IdentificationLocalRowBalance.localBalanceSupportCount suffixInterval support.1 = support.1.card := by
    rw [hprefixSupport, hsuffixSupport]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := support.1) (p := fun t => t.val < theta.val)
    convert hsplit using 1
    simp [not_lt]
  have hprefixID :
      IdentificationLocalRowBalance.localBalanceIDCount prefixInterval support.1 true row =
        ((prefixInterval ∩ support.1).filter fun t => row t = true).card := rfl
  have hsuffixID :
      IdentificationLocalRowBalance.localBalanceIDCount suffixInterval support.1 false row =
        ((suffixInterval ∩ support.1).filter fun t => row t = false).card := rfl
  have hprefixBound := hrow (blockStartEndpoint p s) theta
    (by exact theta.property.1) true
  have hsuffixBound := hrow theta (blockStopEndpoint p s)
    (by exact theta.property.2) false
  have hprefixBound' :
      ((IdentificationLocalRowBalance.localBalanceIDCount prefixInterval support.1 true row : ℕ) : ℝ) ≥
        (IdentificationLocalRowBalance.localBalanceSupportCount prefixInterval support.1 : ℝ) / 3 -
          8 * (b_N p : ℝ) := by
    simpa [prefixInterval, IdentificationLocalRowBalance.localBalanceRowPredicate,
      IdentificationLocalRowBalance.localBalanceIDCount,
      IdentificationLocalRowBalance.localBalanceSupportCount] using hprefixBound
  have hsuffixBound' :
      ((IdentificationLocalRowBalance.localBalanceIDCount suffixInterval support.1 false row : ℕ) : ℝ) ≥
        (IdentificationLocalRowBalance.localBalanceSupportCount suffixInterval support.1 : ℝ) / 3 -
          8 * (b_N p : ℝ) := by
    simpa [suffixInterval, IdentificationLocalRowBalance.localBalanceRowPredicate,
      IdentificationLocalRowBalance.localBalanceIDCount,
      IdentificationLocalRowBalance.localBalanceSupportCount] using hsuffixBound
  have hsplitReal :
      (IdentificationLocalRowBalance.localBalanceSupportCount prefixInterval support.1 : ℝ) +
        (IdentificationLocalRowBalance.localBalanceSupportCount suffixInterval support.1 : ℝ) =
          (support.1.card : ℝ) := by exact_mod_cast hsupportSplit
  linarith

private theorem intervalSum_eq_calendarBlock_sum
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (Y : ℕ → Coordinates p → ℝ) (e : Coordinates p) :
    BootstrapIntervalBounds.intervalSum Y (s.val * B_boot p + 1) p.T
        (min p.T ((s.val + 1) * B_boot p)) e =
      ∑ t ∈ calendarBlock p s, Y (t.val + 1) e := by
  classical
  rw [BootstrapIntervalBounds.intervalSum_eq_sum_Icc Y (Nat.min_le_left _ _) e]
  symm
  apply Finset.sum_bij (fun t _ => t.val + 1)
  · intro t ht
    rcases (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht with ⟨hstart, hstop⟩
    simp only [Finset.mem_Icc]
    omega
  · intro t₁ ht₁ t₂ ht₂ h
    apply Fin.ext
    exact Nat.add_right_cancel h
  · intro k hk
    rcases Finset.mem_Icc.mp hk with ⟨hlo, hhi⟩
    have hkpos : 0 < k := by omega
    have hkt : k - 1 < p.T := by
      have : k ≤ p.T := hhi.trans (Nat.min_le_left _ _)
      omega
    refine ⟨⟨k - 1, hkt⟩, ?_, ?_⟩
    · rw [BootstrapDimensions.mem_calendarBlock_iff]
      constructor
      · change s.val * B_boot p ≤ k - 1
        omega
      · change k - 1 < min p.T ((s.val + 1) * B_boot p)
        omega
    · change k - 1 + 1 = k
      omega
  · intro t ht
    rfl

private theorem oneClock_mean_ge_blockPhaseIndicator
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K)
    (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      ∀ hguard : generatedClockBlockGuard ids rewards C_star C_h eta s focal a e,
        let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
        let boundary := ReferenceInitializationRun.run source s.val
        let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hguard.1
        let x := ReferenceInitializationRun.physical source boundary hvalid
        let hm := hguard.2 hvalid
        let j : {j // j ∈ x.uninformed} := ⟨focal, hm.1⟩
        let theta := firstMulticastEndpoint p s x
        BootstrapIntervalBounds.conditionalMean (GeneratedBootstrapRoundLaw.originalLaw p)
          (GeneratedBootstrapFiltration.analysisFiltration p)
          (GeneratedClockConditionalMeans.oneClock ids rewards C_star C_h eta
            rowCompletion scalarCompletion s focal) (t.val + 1) e ≥
          (1 / 64 : ℝ) * blockPhaseIndicator p s rewards a x theta j t := by
  classical
  have hone := GeneratedClockConditionalMeans.actual_oneClock_conditional_mean_ge
    ids rewards C_star C_h eta s t ht focal a rowCompletion scalarCompletion
  filter_upwards [hone] with e he
  intro hg
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hg.1
  let x := ReferenceInitializationRun.physical source boundary hvalid
  let hm := hg.2 hvalid
  have hmem : focal ∈ x.uninformed := hm.1
  let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
  rcases hm.2 hmem with ⟨hactive, hheld, htarget, hinactive, hrow⟩
  let profile := BootstrapPhysicalInput.currentBlockDrawProfile p s boundary.numerators
    boundary.weight_ge_one source.coordinates
  let st := BootstrapPhysicalBlock.run x t.val
  have hdesc := processedDescriptor_eq_actual ids rewards C_star C_h eta s e hg.1 t
  have hraw := he boundary profile x.target st
      (by simpa [source, boundary, x, profile, st] using hdesc)
      hvalid hmem ⟨hactive, hheld, htarget, hinactive⟩
  have hsource := GeneratedClockConditionalMeans.oneClock_conditionalMean_sourceIndex
    ids rewards C_star C_h eta rowCompletion scalarCompletion s t ht focal
  have hsource' :
      BootstrapIntervalBounds.conditionalMean (GeneratedBootstrapRoundLaw.originalLaw p)
          (GeneratedBootstrapFiltration.analysisFiltration p)
          (GeneratedClockConditionalMeans.oneClock ids rewards C_star C_h eta
            rowCompletion scalarCompletion s focal) (t.val + 1) =
        condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
          (GeneratedBootstrapRoundLaw.originalLaw p)
          (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
            (GeneratedClockConditionalMeans.oneClockTest ids rewards rowCompletion
              scalarCompletion s t focal)) := by
    simpa [GeneratedClockConditionalMeans.sourceClockIndex] using hsource
  rw [hsource']
  let theta := firstMulticastEndpoint p s x
  change condExp (GeneratedBootstrapFiltration.analysisFiltration p t.val)
      (GeneratedBootstrapRoundLaw.originalLaw p)
      (GeneratedBootstrapFiltration.testValue p ids rewards C_star C_h eta s t
        (GeneratedClockConditionalMeans.oneClockTest ids rewards rowCompletion
          scalarCompletion s t focal)) e ≥
    (1 / 64 : ℝ) *
      ((if t ∈ IdentificationLocalRowBalance.calendarInterval p s
            (blockStartEndpoint p s) theta ∧
            t ∈ positiveRewardSupport p s rewards a ∧ x.ids (x.privateId j) t = true
        then (1 : ℝ) else 0) +
       (if t ∈ IdentificationLocalRowBalance.calendarInterval p s theta
            (blockStopEndpoint p s) ∧
            t ∈ positiveRewardSupport p s rewards a ∧ x.ids (x.privateId j) t = false
        then (1 : ℝ) else 0))
  have hmodeSplit := firstMulticastEndpoint_mode_split p s x t ht
  have hchi : BootstrapModeService.chi x t a =
      if t ∈ positiveRewardSupport p s rewards a then (1 : ℝ) else 0 := by
    simp [BootstrapModeService.chi, positiveRewardSupport, ht, x, source,
      ReferenceInitializationRun.physical, BootstrapPhysicalInput.blockInput,
      GeneratedBootstrapRoundLaw.input, ReferenceInitializationMeasurability.inputOfCoordinates]
  by_cases hprefix : t ∈ IdentificationLocalRowBalance.calendarInterval p s
      (blockStartEndpoint p s) theta
  · rcases (IdentificationLocalRowBalance.mem_calendarInterval_iff p s
      (blockStartEndpoint p s) theta t).mp hprefix with ⟨_, _, _, hbefore⟩
    have hmode : st.mode = BootstrapPhysicalBlock.Mode.discover := by
      simpa [st] using hmodeSplit.1 hbefore
    have hnotSuffix : t ∉ IdentificationLocalRowBalance.calendarInterval p s theta
        (blockStopEndpoint p s) := by
      intro hsuffix
      rcases (IdentificationLocalRowBalance.mem_calendarInterval_iff p s
        theta (blockStopEndpoint p s) t).mp hsuffix with ⟨_, _, hafter, _⟩
      omega
    simp only [hchi, x, source, boundary] at hraw
    have heq :
        (if t ∈ positiveRewardSupport p s rewards a then (1 : ℝ) else 0) / 64 *
            ((if st.mode = .discover ∧ x.ids (x.privateId j) t = true then (1 : ℝ) else 0) +
             (if st.mode = .multicast ∧ x.ids (x.privateId j) t = false then (1 : ℝ) else 0)) =
          (1 / 64 : ℝ) *
            ((if t ∈ IdentificationLocalRowBalance.calendarInterval p s
                  (blockStartEndpoint p s) theta ∧
                  t ∈ positiveRewardSupport p s rewards a ∧ x.ids (x.privateId j) t = true
              then (1 : ℝ) else 0) +
             (if t ∈ IdentificationLocalRowBalance.calendarInterval p s theta
                  (blockStopEndpoint p s) ∧
                  t ∈ positiveRewardSupport p s rewards a ∧ x.ids (x.privateId j) t = false
              then (1 : ℝ) else 0)) := by
      by_cases hsupp : t ∈ positiveRewardSupport p s rewards a <;>
        by_cases hid : x.ids (x.privateId j) t = true <;>
        simp [hmode, hnotSuffix, hprefix, hsupp, hid]
    rw [heq] at hraw
    exact hraw
  · have hsuffix : t ∈ IdentificationLocalRowBalance.calendarInterval p s theta
        (blockStopEndpoint p s) := by
      rcases (BootstrapDimensions.mem_calendarBlock_iff p s t).mp ht with ⟨hstart, hstop⟩
      have htheta : theta.val ≤ t.val := by
        by_contra hthetaNot
        have hprefix' : t ∈ IdentificationLocalRowBalance.calendarInterval p s
            (blockStartEndpoint p s) theta := by
          rw [IdentificationLocalRowBalance.mem_calendarInterval_iff]
          exact ⟨hstart, hstop, hstart, by omega⟩
        exact hprefix hprefix'
      rw [IdentificationLocalRowBalance.mem_calendarInterval_iff]
      exact ⟨hstart, hstop, htheta, hstop⟩
    rcases (IdentificationLocalRowBalance.mem_calendarInterval_iff p s
      theta (blockStopEndpoint p s) t).mp hsuffix with ⟨_, _, hafter, _⟩
    have hmode : st.mode = BootstrapPhysicalBlock.Mode.multicast := by
      simpa [st] using hmodeSplit.2 hafter
    have hnotPrefix : t ∉ IdentificationLocalRowBalance.calendarInterval p s
        (blockStartEndpoint p s) theta := hprefix
    simp only [hchi, x, source, boundary] at hraw
    have heq :
        (if t ∈ positiveRewardSupport p s rewards a then (1 : ℝ) else 0) / 64 *
            ((if st.mode = .discover ∧ x.ids (x.privateId j) t = true then (1 : ℝ) else 0) +
             (if st.mode = .multicast ∧ x.ids (x.privateId j) t = false then (1 : ℝ) else 0)) =
          (1 / 64 : ℝ) *
            ((if t ∈ IdentificationLocalRowBalance.calendarInterval p s
                  (blockStartEndpoint p s) theta ∧
                  t ∈ positiveRewardSupport p s rewards a ∧ x.ids (x.privateId j) t = true
              then (1 : ℝ) else 0) +
             (if t ∈ IdentificationLocalRowBalance.calendarInterval p s theta
                  (blockStopEndpoint p s) ∧
                  t ∈ positiveRewardSupport p s rewards a ∧ x.ids (x.privateId j) t = false
              then (1 : ℝ) else 0)) := by
      by_cases hsupp : t ∈ positiveRewardSupport p s rewards a <;>
        by_cases hid : x.ids (x.privateId j) t = true <;>
        simp [hmode, hnotPrefix, hsuffix, hsupp, hid]
    rw [heq] at hraw
    exact hraw

private theorem blockPhaseIndicator_sum_eq
    (p : ConstructorDimensions.Parameters) (s : Fin (n_boot p))
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (a : Fin p.K)
    {r : Fin (n_boot p)} (x : BootstrapPhysicalBlock.Input p r)
    (theta : IdentificationLocalRowBalance.BlockEndpoint p s)
    (j : {j // j ∈ x.uninformed}) :
    (∑ t ∈ calendarBlock p s, blockPhaseIndicator p s rewards a x theta j t) =
      ((IdentificationLocalRowBalance.localBalanceIDCount
        (IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta)
        (positiveRewardBlockSupport p s rewards a).1 true
        (x.ids (x.privateId j)) : ℕ) : ℝ) +
      ((IdentificationLocalRowBalance.localBalanceIDCount
        (IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s))
        (positiveRewardBlockSupport p s rewards a).1 false
        (x.ids (x.privateId j)) : ℕ) : ℝ) := by
  classical
  let support := positiveRewardSupport p s rewards a
  let prefixInterval := IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta
  let suffixInterval := IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s)
  have hprefixSubset : prefixInterval ⊆ calendarBlock p s := by
    intro t ht
    rcases (IdentificationLocalRowBalance.mem_calendarInterval_iff p s
      (blockStartEndpoint p s) theta t).mp ht with ⟨hstart, hstop, _, _⟩
    rw [BootstrapDimensions.mem_calendarBlock_iff]
    exact ⟨hstart, hstop⟩
  have hsuffixSubset : suffixInterval ⊆ calendarBlock p s := by
    intro t ht
    rcases (IdentificationLocalRowBalance.mem_calendarInterval_iff p s
      theta (blockStopEndpoint p s) t).mp ht with ⟨hstart, hstop, _, _⟩
    rw [BootstrapDimensions.mem_calendarBlock_iff]
    exact ⟨hstart, hstop⟩
  have hprefixSet :
      (calendarBlock p s).filter
        (fun t => t ∈ prefixInterval ∧ t ∈ support ∧ x.ids (x.privateId j) t = true) =
        (prefixInterval ∩ support).filter (fun t => x.ids (x.privateId j) t = true) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨_, hp, hs, hid⟩
      exact ⟨⟨hp, hs⟩, hid⟩
    · rintro ⟨⟨hp, hs⟩, hid⟩
      exact ⟨hprefixSubset hp, hp, hs, hid⟩
  have hsuffixSet :
      (calendarBlock p s).filter
        (fun t => t ∈ suffixInterval ∧ t ∈ support ∧ x.ids (x.privateId j) t = false) =
        (suffixInterval ∩ support).filter (fun t => x.ids (x.privateId j) t = false) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨_, hs, hsup, hid⟩
      exact ⟨⟨hs, hsup⟩, hid⟩
    · rintro ⟨⟨hs, hsup⟩, hid⟩
      exact ⟨hsuffixSubset hs, hs, hsup, hid⟩
  simp only [blockPhaseIndicator, Finset.sum_add_distrib, Finset.sum_boole]
  rw [hprefixSet, hsuffixSet]
  simp [support, prefixInterval, suffixInterval, positiveRewardBlockSupport,
    IdentificationLocalRowBalance.localBalanceIDCount]

/-- Almost everywhere on the actual generated boundary/profile/target and
ID-row guard, the original source-indexed one-clock conditional means over the
whole clipped block sum to at least S_s(a)/192 - b_N/4. The interval is
exactly [s.val * B_boot + 1, min T ((s.val + 1) * B_boot)]; no per-round
descriptor or conditional mean is an input. -/
theorem generated_oneClock_conditionalMean_intervalSum_ge
    (ids : IDArray p) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (C_star C_h : ℝ) (eta : ReferencePrelaunchFollower.LearningRate)
    (rowCompletion : CompleteRow p) (scalarCompletion : PlayerRoundScalars p)
    (s : Fin (n_boot p)) (focal : Follower p.m) (a : Arm p.K) :
    ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      generatedClockBlockGuard ids rewards C_star C_h eta s focal a e →
      BootstrapIntervalBounds.intervalSum
          (BootstrapIntervalBounds.conditionalMean (GeneratedBootstrapRoundLaw.originalLaw p)
            (GeneratedBootstrapFiltration.analysisFiltration p)
            (GeneratedClockConditionalMeans.oneClock ids rewards C_star C_h eta
              rowCompletion scalarCompletion s focal))
          (s.val * B_boot p + 1) p.T (min p.T ((s.val + 1) * B_boot p)) e ≥
        BootstrapDownCountMean.rewardSupportCount p s rewards a / 192 - (b_N p : ℝ) / 4 := by
  classical
  let clock := GeneratedClockConditionalMeans.oneClock ids rewards C_star C_h eta
    rowCompletion scalarCompletion s focal
  let means := BootstrapIntervalBounds.conditionalMean
    (GeneratedBootstrapRoundLaw.originalLaw p)
    (GeneratedBootstrapFiltration.analysisFiltration p) clock
  have hphaseAtAll : ∀ᵐ e ∂GeneratedBootstrapRoundLaw.originalLaw p,
      ∀ t : Fin p.T, t ∈ calendarBlock p s →
        ∀ hguard : generatedClockBlockGuard ids rewards C_star C_h eta s focal a e,
          let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
          let boundary := ReferenceInitializationRun.run source s.val
          let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hguard.1
          let x := ReferenceInitializationRun.physical source boundary hvalid
          let hm := hguard.2 hvalid
          let j : {j // j ∈ x.uninformed} := ⟨focal, hm.1⟩
          let theta := firstMulticastEndpoint p s x
          means (t.val + 1) e ≥ (1 / 64 : ℝ) *
            blockPhaseIndicator p s rewards a x theta j t := by
    apply ae_all_iff.mpr
    intro t
    by_cases ht : t ∈ calendarBlock p s
    · have h := oneClock_mean_ge_blockPhaseIndicator ids rewards C_star C_h eta
        rowCompletion scalarCompletion s focal a t ht
      filter_upwards [h] with e he
      intro _ hg
      simpa [means, clock] using he hg
    · filter_upwards [] with e
      intro hmem hg
      exact (ht hmem).elim
  filter_upwards [hphaseAtAll] with e hphase
  intro hguard
  let source := GeneratedBootstrapRoundLaw.input p ids rewards C_star C_h eta e
  let boundary := ReferenceInitializationRun.run source s.val
  let hvalid := processedBoundary_valid ids rewards C_star C_h eta s e hguard.1
  let x := ReferenceInitializationRun.physical source boundary hvalid
  let hm := hguard.2 hvalid
  have hmem : focal ∈ x.uninformed := hm.1
  let j : {j // j ∈ x.uninformed} := ⟨focal, hmem⟩
  rcases hm.2 hmem with ⟨hactive, hheld, htarget, hinactive, hrow⟩
  let support := positiveRewardBlockSupport p s rewards a
  let theta := firstMulticastEndpoint p s x
  have hround : ∀ t ∈ calendarBlock p s,
      means (t.val + 1) e ≥
        (1 / 64 : ℝ) * blockPhaseIndicator p s rewards a x theta j t := by
    intro t ht
    have hphaseRound := hphase t ht hguard
    simpa [source, boundary, hvalid, x, j, theta] using hphaseRound
  have hphaseSum := blockPhaseIndicator_sum_eq p s rewards a x theta j
  have hphaseCount := localBalance_two_phase_counts p s support
    (x.ids (x.privateId j)) theta hrow
  have hsum :
      (∑ t ∈ calendarBlock p s, means (t.val + 1) e) ≥
        (1 / 64 : ℝ) *
          (((IdentificationLocalRowBalance.localBalanceIDCount
              (IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta)
              support.1 true (x.ids (x.privateId j)) : ℕ) : ℝ) +
            ((IdentificationLocalRowBalance.localBalanceIDCount
              (IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s))
              support.1 false (x.ids (x.privateId j)) : ℕ) : ℝ)) := by
    calc
      _ ≥ ∑ t ∈ calendarBlock p s,
          (1 / 64 : ℝ) * blockPhaseIndicator p s rewards a x theta j t :=
        Finset.sum_le_sum hround
      _ = (1 / 64 : ℝ) *
          (((IdentificationLocalRowBalance.localBalanceIDCount
              (IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta)
              support.1 true (x.ids (x.privateId j)) : ℕ) : ℝ) +
            ((IdentificationLocalRowBalance.localBalanceIDCount
              (IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s))
              support.1 false (x.ids (x.privateId j)) : ℕ) : ℝ)) := by
        rw [← Finset.mul_sum, hphaseSum]
  have hcount :
      (((IdentificationLocalRowBalance.localBalanceIDCount
          (IdentificationLocalRowBalance.calendarInterval p s (blockStartEndpoint p s) theta)
          support.1 true (x.ids (x.privateId j)) : ℕ) : ℝ) +
        ((IdentificationLocalRowBalance.localBalanceIDCount
          (IdentificationLocalRowBalance.calendarInterval p s theta (blockStopEndpoint p s))
          support.1 false (x.ids (x.privateId j)) : ℕ) : ℝ)) ≥
        (support.1.card : ℝ) / 3 - 16 * (b_N p : ℝ) := hphaseCount
  have hsupportCard : (support.1.card : ℝ) =
      BootstrapDownCountMean.rewardSupportCount p s rewards a := by
    simpa [support, positiveRewardBlockSupport] using
      (rewardSupportCount_eq_positiveRewardSupport_card p s rewards a).symm
  have hcalendarSum : BootstrapIntervalBounds.intervalSum means
      (s.val * B_boot p + 1) p.T (min p.T ((s.val + 1) * B_boot p)) e =
        ∑ t ∈ calendarBlock p s, means (t.val + 1) e :=
    intervalSum_eq_calendarBlock_sum p s means e
  rw [hcalendarSum]
  calc
    _ ≥ (1 / 64 : ℝ) * ((support.1.card : ℝ) / 3 - 16 * (b_N p : ℝ)) :=
      (mul_le_mul_of_nonneg_left hcount (by norm_num)).trans hsum
    _ = BootstrapDownCountMean.rewardSupportCount p s rewards a / 192 -
        (b_N p : ℝ) / 4 := by rw [hsupportCard]; ring

end Bandits.Support.GeneratedClockBlockBalance

end
