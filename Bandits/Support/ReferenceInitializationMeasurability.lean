/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceInitializationRun

/-!
# Measurable observables of the reference initialization producer

The input coordinates are the existing identification array, one complete
continuous row, and `ExtendedPrivateCoordinates`.  The observable log pads the
actual generated prefix by `none` and stores both the played arm and the
observation's exact grid index.  It does not supply a history or append a
physical tail. The complete observable encoding characterizes the existing
boundary; countable case decomposition then proves the actual adaptive run,
output, launch round and both initialization-failure causes measurable. Ordinary
DATA logging retains continuous thinning scalars and both partial/completed
DOWN batches are encoded exactly. These are internal deterministic results,
not stopping-time, freshness, probability, coupling or manuscript closure.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-40,55-144` and
`sources/zip4/manuscript/appendix_b_communication.tex:723-744,786-798`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActiveRoundActions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.PublicDiscreteDraws
open scoped Classical

namespace Bandits.Support.ReferenceInitializationMeasurability

/-- Only countable option outputs receive the discrete measurable space. -/
instance optionCountableMeasurableSpace (α : Type*) [Countable α] :
    MeasurableSpace (Option α) := ⊤

instance optionCountableMeasurableSingletonClass (α : Type*) [Countable α] :
    MeasurableSingletonClass (Option α) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

/-- The actual varying coordinates of one fixed-parameter reference run. -/
abbrev InputCoordinates (p : Parameters) :=
  IDArray p × (CompleteRow p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)

/-- Insert the actual varying coordinates into the accepted reference-run input. -/
def inputOfCoordinates (p : Parameters) (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (z : InputCoordinates p) :
    ReferenceInitializationRun.Input p where
  ids := z.1
  row := z.2.1
  rewards := rewards
  coordinates := z.2.2
  C_star := C_star
  C_h := C_h
  eta := eta

/-- The producer's actual arm-and-grid-index log, padded only after its prefix. -/
abbrev PaddedPhysicalLog (p : Parameters) :=
  Fin p.m → Fin p.T → Option (Fin p.K × Fin (D p + 1))

/-- The unique accepted grid index representing one existing rounded observation. -/
def observationGridIndex (p : Parameters) (y : Observation p) : Fin (D p + 1) :=
  Classical.choose y.property

/-- Reconstruction of the real value from the stored observation index. -/
theorem observationGridIndex_value (p : Parameters) (y : Observation p) :
    y.val.val = (observationGridIndex p y).val / (D p : ℝ) :=
  Classical.choose_spec y.property

/-- The real-grid encoding is injective at the accepted positive denominator. -/
theorem observationGridIndex_eq_of_value_eq (p : Parameters) (y z : Observation p)
    (h : y.val.val = z.val.val) : observationGridIndex p y = observationGridIndex p z := by
  apply RealRewardGridCount.realRewardGridValue_injective (D p) (D_pos p)
  rw [RealRewardGridCount.realRewardGridValue, RealRewardGridCount.realRewardGridValue]
  rw [← observationGridIndex_value p y, ← observationGridIndex_value p z]
  exact h

/-- The log uses the physical block's original integer feedback index. -/
theorem observationGridIndex_ownObservation {p : Parameters} {s : Fin (n_boot p)}
    (v : BootstrapPhysicalBlock.Input p s) (i : Fin p.m) (t : Fin p.T) :
    observationGridIndex p (ReferenceInitializationRun.ownObservation v i t) =
      BootstrapPhysicalBlock.observationIndex v (BootstrapPhysicalBlock.run v t.val) t i := by
  apply RealRewardGridCount.realRewardGridValue_injective (D p) (D_pos p)
  rw [RealRewardGridCount.realRewardGridValue, RealRewardGridCount.realRewardGridValue]
  rw [← observationGridIndex_value p (ReferenceInitializationRun.ownObservation v i t)]
  change BootstrapPhysicalBlock.feedback v (BootstrapPhysicalBlock.run v t.val) t i = _
  exact (BootstrapPhysicalBlock.observationIndex_value v _ t i).symm

/-- Read the actual generated boundary history as a padded arm/grid-index log. -/
def boundaryLog (p : Parameters) (b : Boundary p) : PaddedPhysicalLog p := fun i t =>
  if ht : t.val < elapsed p b.completed then
    let entry := b.history i ⟨t.val, ht⟩
    some (entry.1, observationGridIndex p entry.2)
  else none

/-- On every generated round, the padded encoding is exactly the actual
boundary-history arm and grid witness. -/
theorem boundaryLog_prefix (p : Parameters) (b : Boundary p) (i : Fin p.m)
    (t : Fin (elapsed p b.completed)) :
    boundaryLog p b i ⟨t.val, Nat.lt_of_lt_of_le t.isLt (elapsed_le_T p b.completed)⟩ =
      some ((b.history i t).1, observationGridIndex p (b.history i t).2) := by
  simp only [boundaryLog, dite_eq_left t.isLt]

/-- The encoded grid index reconstructs the original real feedback exactly. -/
theorem boundaryLog_value (p : Parameters) (b : Boundary p) (i : Fin p.m)
    (t : Fin (elapsed p b.completed)) :
    (observationGridIndex p (b.history i t).2).val / (D p : ℝ) =
      ((b.history i t).2).val.val := by
  exact (observationGridIndex_value p (b.history i t).2).symm

/-- The padded encoding is empty precisely outside the actually generated prefix. -/
theorem boundaryLog_none_of_outside (p : Parameters) (b : Boundary p) (i : Fin p.m)
    (t : Fin p.T) (ht : ¬ t.val < elapsed p b.completed) :
    boundaryLog p b i t = none := by
  simp only [boundaryLog, dite_eq_right ht]

/-- The finite block-start draws produced by the accepted input adapter. -/
abbrev BlockDrawCode (p : Parameters) (incoming : Finset (Follower p.m)) :=
  ({j // j ∈ incoming} → Bool) ×
    (({j // j ∈ incoming} → Fin p.K) ×
      (({j // j ∈ incoming} → Fin (A_id p)) × Fin p.K))

/-- The block-start activity, held arms, private IDs and target are computed
from the existing private-coordinate product and current natural numerators. -/
def blockDrawCode (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (z : InputCoordinates p) : BlockDrawCode p incoming :=
  (BootstrapPhysicalInput.activityMap p s incoming numerators hpos z.2.2,
    (BootstrapPhysicalInput.heldMap p s incoming numerators hpos z.2.2,
      (BootstrapPhysicalInput.privateIDMap p s incoming numerators hpos z.2.2,
        BootstrapPhysicalInput.targetArmMap p s z.2.2)))

/-- The accepted finite draw adapter is measurable on the genuine extended
private-coordinate product, with its natural product sigma algebra. -/
theorem measurable_blockDrawCode (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) :
    Measurable (blockDrawCode p s incoming numerators hpos) := by
  let hcoordinates : Measurable (fun z : InputCoordinates p => z.2.2) :=
    (measurable_snd.comp measurable_snd)
  unfold blockDrawCode
  have hactivity :=
    (BootstrapPhysicalInput.measurable_activityMap p s incoming numerators hpos).comp hcoordinates
  have hheld :=
    (BootstrapPhysicalInput.measurable_heldMap p s incoming numerators hpos).comp hcoordinates
  have hprivateID :=
    (BootstrapPhysicalInput.measurable_privateIDMap p s incoming numerators hpos).comp hcoordinates
  have htarget := (BootstrapPhysicalInput.measurable_targetArmMap p s).comp hcoordinates
  exact hactivity.prodMk (hheld.prodMk (hprivateID.prodMk htarget))

/-- Actual per-round private draw values, placed in the accepted block
causality carrier after fixing the block-start finite draws. -/
def localCoordinatesOf (p : Parameters) (incoming : Finset (Follower p.m))
    (draws : BlockDrawCode p incoming) (z : InputCoordinates p) :
    BootstrapBlockCausality.LocalCoordinates p incoming draws.2.1
      draws.2.2.2 :=
  let coordinatorAvoid := fun t => BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
    draws.2.2.2 (BootstrapPhysicalInput.playerRoundScalarAt p z.2.2
      (coordinator p.two_le_m) t)
  let followerAvoid := fun j t => BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
    (draws.2.1 j) (BootstrapPhysicalInput.playerRoundScalarAt p z.2.2
      (followerPlayer p.two_le_m j.1) t)
  (z.2.1,
    (BootstrapPhysicalInput.uniformArmMap p z.2.2, (coordinatorAvoid, followerAvoid)))

/-- The local block input retains the complete continuous row and uses the
same scalar coordinate for each mutually exclusive arm alternative. -/
theorem measurable_localCoordinatesOf (p : Parameters)
    (incoming : Finset (Follower p.m)) (draws : BlockDrawCode p incoming) :
    Measurable (localCoordinatesOf p incoming draws) := by
  have hrow : Measurable (fun z : InputCoordinates p => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hprivate : Measurable (fun z : InputCoordinates p => z.2.2) :=
    measurable_snd.comp measurable_snd
  have huniform : Measurable (fun z : InputCoordinates p =>
      BootstrapPhysicalInput.uniformArmMap p z.2.2) :=
    (BootstrapPhysicalInput.measurable_uniformArmMap p).comp hprivate
  have hcoordinatorAvoid : Measurable (fun z : InputCoordinates p =>
      fun t => BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p draws.2.2.2
        (BootstrapPhysicalInput.playerRoundScalarAt p z.2.2
          (coordinator p.two_le_m) t)) := by
    apply measurable_pi_iff.mpr
    intro t
    have hscalar :=
      (BootstrapPhysicalInput.measurable_playerRoundScalarAt p (coordinator p.two_le_m) t).comp
        hprivate
    exact (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p draws.2.2.2).comp
      hscalar
  have hfollowerAvoid : Measurable (fun z : InputCoordinates p =>
      fun j t => BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p (draws.2.1 j)
        (BootstrapPhysicalInput.playerRoundScalarAt p z.2.2
          (followerPlayer p.two_le_m j.1) t)) := by
    apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro t
    have hscalar :=
      (BootstrapPhysicalInput.measurable_playerRoundScalarAt p
        (followerPlayer p.two_le_m j.1) t).comp hprivate
    exact (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p (draws.2.1 j)).comp
      hscalar
  exact hrow.prodMk (huniform.prodMk (hcoordinatorAvoid.prodMk hfollowerAvoid))

/-- Countable case decomposition on the original input space. -/
private theorem measurable_by_countable_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right (f := fun v : β × α => branch v.1 v.2)
    hbranch).comp (hkey.prodMk measurable_id)

/-- The fixed-start physical action map obtained from the accepted
`BootstrapBlockCausality` run, for one actual initialization block. -/
def fixedBlockActions (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    InputCoordinates p → Fin p.T → Player p.m → Fin p.K := fun z t =>
  BootstrapPhysicalBlock.actions
    (BootstrapBlockCausality.blockInput (s := s) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards (localCoordinatesOf p incoming c.2 z))
    (BootstrapBlockCausality.blockRun (s := s) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards (localCoordinatesOf p incoming c.2 z) t.val) t

/-- The case key contains only finite source values: the actual ID array and
the accepted block adapter's activity, held arms, private IDs and target. -/
def blockCaseKey (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m)) (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ j a, (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a) :
    InputCoordinates p → IDArray p × BlockDrawCode p incoming := fun z =>
  (z.1, blockDrawCode p s incoming numerators hpos z)

/-- A fixed case of the accepted block action map is measurable through the
existing `BootstrapBlockCausality` theorem. -/
theorem measurable_fixedBlockActions (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    Measurable (fun z : InputCoordinates p => fixedBlockActions p s incoming c rewards z) := by
  apply measurable_pi_iff.mpr
  intro t
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp
    ((BootstrapBlockCausality.measurable_actions_run (s := s) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards t).comp
      (measurable_localCoordinatesOf p incoming c.2)))

/-- At any fixed actual initialization boundary, each next-block physical
action is measurable in the varying ID array, complete row and accepted
extended private coordinates. -/
theorem measurable_physicalAction_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) (t : Fin p.T) (i : Player p.m) :
    Measurable (fun z : InputCoordinates p =>
      BootstrapPhysicalBlock.actions
        (ReferenceInitializationRun.physical (inputOfCoordinates p C_star C_h eta rewards z) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (inputOfCoordinates p C_star C_h eta rewards z) b h) t.val) t i) := by
  let s := ReferenceInitializationRun.nextBlock b h
  let incoming := ReferenceInitializationRun.uninformed b
  let key := blockCaseKey p s incoming b.numerators b.weight_ge_one
  have hkey : Measurable key := by
    exact measurable_fst.prodMk
      (measurable_blockDrawCode p s incoming b.numerators b.weight_ge_one)
  have hbranch : ∀ c : IDArray p × BlockDrawCode p incoming,
      Measurable (fun z : InputCoordinates p =>
        fixedBlockActions p s incoming c rewards z t i) := by
    intro c
    exact (measurable_pi_apply i).comp
      ((measurable_pi_apply t).comp (measurable_fixedBlockActions p s incoming c rewards))
  have hmeas := measurable_by_countable_cases key hkey
    (fun c z => fixedBlockActions p s incoming c rewards z t i) hbranch
  change Measurable (fun z : InputCoordinates p =>
    fixedBlockActions p s incoming (key z) rewards z t i)
  exact hmeas

/-- The integer observation index from the actual physical block is also
measurable; its grid witness is retained by the observable log. -/
def fixedBlockObservationIndex (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    InputCoordinates p → Fin p.T → Player p.m → Fin (D p + 1) := fun z t i =>
  BootstrapBlockCausality.runObservationIndex (s := s) incoming c.2.1 c.2.2.1
    c.2.2.2.1 c.1 c.2.2.2.2 rewards t i (localCoordinatesOf p incoming c.2 z)

/-- Measurability of the exact integer feedback index for one fixed block case. -/
theorem measurable_fixedBlockObservationIndex (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    Measurable (fixedBlockObservationIndex p s incoming c rewards) := by
  apply measurable_pi_iff.mpr
  intro t
  apply measurable_pi_iff.mpr
  intro i
  exact (BootstrapBlockCausality.measurable_observationIndex_run (s := s)
    incoming c.2.1 c.2.2.1 c.2.2.2.1 c.1 c.2.2.2.2 rewards t i).comp
      (measurable_localCoordinatesOf p incoming c.2)

/-- At any fixed actual initialization boundary, each next-block grid feedback
index is measurable in the actual product input. -/
theorem measurable_physicalObservationIndex_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) :
    Measurable (fun z : InputCoordinates p =>
      fun t i => BootstrapPhysicalBlock.observationIndex
        (ReferenceInitializationRun.physical
          (inputOfCoordinates p C_star C_h eta rewards z) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (inputOfCoordinates p C_star C_h eta rewards z) b h) t.val) t i) := by
  let s := ReferenceInitializationRun.nextBlock b h
  let incoming := ReferenceInitializationRun.uninformed b
  let key := blockCaseKey p s incoming b.numerators b.weight_ge_one
  have hkey : Measurable key := by
    exact measurable_fst.prodMk
      (measurable_blockDrawCode p s incoming b.numerators b.weight_ge_one)
  have hbranch : ∀ c : IDArray p × BlockDrawCode p incoming,
      Measurable (fixedBlockObservationIndex p s incoming c rewards) := by
    intro c
    exact measurable_fixedBlockObservationIndex p s incoming c rewards
  have hmeas := measurable_by_countable_cases key hkey
    (fun c z => fixedBlockObservationIndex p s incoming c rewards z) hbranch
  change Measurable (fun z : InputCoordinates p =>
    fixedBlockObservationIndex p s incoming (key z) rewards z)
  exact hmeas

/-- Fixed-case slot decoding from the actual complete row. -/
def fixedBlockSlot (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    InputCoordinates p → Fin p.T → Slot := fun z t =>
  BootstrapPhysicalBlock.slot
    (BootstrapBlockCausality.blockInput (s := s) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards (localCoordinatesOf p incoming c.2 z)) t

/-- Slot measurability in a fixed block-start case uses the accepted
continuous complete-row slice. -/
theorem measurable_fixedBlockSlot (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m)) (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    Measurable (fixedBlockSlot p s incoming c rewards) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (BootstrapBlockCausality.measurable_slotInput (s := s) incoming c.2.1
    c.2.2.1 c.2.2.2.1 c.1 c.2.2.2.2 rewards t).comp
      (measurable_localCoordinatesOf p incoming c.2)

/-- Actual next-block slot at a fixed physical initialization boundary. -/
theorem measurable_physicalSlot_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) :
    Measurable (fun z : InputCoordinates p => fun t =>
      BootstrapPhysicalBlock.slot
        (ReferenceInitializationRun.physical
          (inputOfCoordinates p C_star C_h eta rewards z) b h) t) := by
  let s := ReferenceInitializationRun.nextBlock b h
  let incoming := ReferenceInitializationRun.uninformed b
  let key := blockCaseKey p s incoming b.numerators b.weight_ge_one
  have hkey : Measurable key :=
    measurable_fst.prodMk
      (measurable_blockDrawCode p s incoming b.numerators b.weight_ge_one)
  have hbranch : ∀ c : IDArray p × BlockDrawCode p incoming,
      Measurable (fixedBlockSlot p s incoming c rewards) := by
    intro c
    exact measurable_fixedBlockSlot p s incoming c rewards
  have hmeas := measurable_by_countable_cases key hkey
    (fun c z => fixedBlockSlot p s incoming c rewards z) hbranch
  change Measurable (fun z : InputCoordinates p =>
    fixedBlockSlot p s incoming (key z) rewards z)
  exact hmeas

/-- Fixed-case ordered tuple read from the same accepted complete-row slice. -/
def fixedBlockTuple (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    InputCoordinates p → Fin p.T → OrderedTupleSampler.Tuple p.m p.K := fun z t =>
  BootstrapPhysicalBlock.tuple
    (BootstrapBlockCausality.blockInput (s := s) incoming c.2.1 c.2.2.1
      c.2.2.2.1 c.1 c.2.2.2.2 rewards (localCoordinatesOf p incoming c.2 z)) t

/-- The full ordered tuple, not merely its coordinator arm, is measurable in
the fixed-case complete-row coordinates. -/
theorem measurable_fixedBlockTuple (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m)) (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    Measurable (fixedBlockTuple p s incoming c rewards) := by
  apply measurable_pi_iff.mpr
  intro t
  exact (BootstrapBlockCausality.measurable_tupleInput (s := s) incoming c.2.1
    c.2.2.1 c.2.2.2.1 c.1 c.2.2.2.2 rewards t).comp
      (measurable_localCoordinatesOf p incoming c.2)

/-- Actual next-block tuple at a fixed physical initialization boundary. -/
theorem measurable_physicalTuple_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) :
    Measurable (fun z : InputCoordinates p => fun t =>
      BootstrapPhysicalBlock.tuple
        (ReferenceInitializationRun.physical
          (inputOfCoordinates p C_star C_h eta rewards z) b h) t) := by
  let s := ReferenceInitializationRun.nextBlock b h
  let incoming := ReferenceInitializationRun.uninformed b
  let key := blockCaseKey p s incoming b.numerators b.weight_ge_one
  have hkey : Measurable key :=
    measurable_fst.prodMk
      (measurable_blockDrawCode p s incoming b.numerators b.weight_ge_one)
  have hbranch : ∀ c : IDArray p × BlockDrawCode p incoming,
      Measurable (fixedBlockTuple p s incoming c rewards) := by
    intro c
    exact measurable_fixedBlockTuple p s incoming c rewards
  have hmeas := measurable_by_countable_cases key hkey
    (fun c z => fixedBlockTuple p s incoming c rewards z) hbranch
  change Measurable (fun z : InputCoordinates p =>
    fixedBlockTuple p s incoming (key z) rewards z)
  exact hmeas

/-- The reference monitor's DOWN credit, expressed using the actual integer
grid feedback index, true-row slot and ordered tuple arm. -/
def physicalDownArmIndex (p : Parameters) (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) (z : InputCoordinates p) (t : Fin p.T) :
    Option (Fin p.K) :=
  if BootstrapPhysicalBlock.slot
        (ReferenceInitializationRun.physical (inputOfCoordinates p C_star C_h eta rewards z) b h) t =
          downSlot ∧
      0 < (BootstrapPhysicalBlock.observationIndex
        (ReferenceInitializationRun.physical
          (inputOfCoordinates p C_star C_h eta rewards z) b h)
        (BootstrapPhysicalBlock.run
          (ReferenceInitializationRun.physical
            (inputOfCoordinates p C_star C_h eta rewards z) b h) t.val) t
        (coordinator p.two_le_m)).val then
    some ((BootstrapPhysicalBlock.tuple
      (ReferenceInitializationRun.physical (inputOfCoordinates p C_star C_h eta rewards z) b h)
      t).val (coordinator p.two_le_m))
  else none

/-- The integer-index form retains exactly the reference producer's DOWN
credit, since positivity is equivalent to positivity of the actual feedback. -/
theorem physicalDownArmIndex_eq_downArm (p : Parameters) (x : Input p)
    (b : Boundary p) (h : b.completed < n_boot p) (t : Fin p.T) :
    physicalDownArmIndex p x.C_star x.C_h x.eta x.rewards b h
        (⟨x.ids, (x.row, x.coordinates)⟩) t = ReferenceInitializationRun.downArm x b h t := by
  have hpos := BootstrapPhysicalBlock.observationIndex_pos_iff
    (ReferenceInitializationRun.physical x b h)
    (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
    (coordinator p.two_le_m)
  unfold physicalDownArmIndex ReferenceInitializationRun.downArm
  have hcond :
      (BootstrapPhysicalBlock.slot (ReferenceInitializationRun.physical x b h) t = downSlot ∧
        0 < (BootstrapPhysicalBlock.observationIndex
          (ReferenceInitializationRun.physical x b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
          (coordinator p.two_le_m)).val) ↔
      (BootstrapPhysicalBlock.slot (ReferenceInitializationRun.physical x b h) t = downSlot ∧
        0 < BootstrapPhysicalBlock.feedback (ReferenceInitializationRun.physical x b h)
          (BootstrapPhysicalBlock.run (ReferenceInitializationRun.physical x b h) t.val) t
          (coordinator p.two_le_m)) := by
    constructor
    · rintro ⟨hs, hp⟩
      exact ⟨hs, hpos.mp hp⟩
    · rintro ⟨hs, hp⟩
      exact ⟨hs, hpos.mpr hp⟩
  exact if_congr hcond rfl rfl

/-- Fixed-case DOWN credit is measurable as a function of the actual complete
row and private coordinates. -/
def fixedBlockDownArmIndex (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m))
    (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) :
    InputCoordinates p → Fin p.T → Option (Fin p.K) := fun z t =>
  if fixedBlockSlot p s incoming c rewards z t = downSlot ∧
      0 < (fixedBlockObservationIndex p s incoming c rewards z t
        (coordinator p.two_le_m)).val then
    some ((fixedBlockTuple p s incoming c rewards z t).val (coordinator p.two_le_m))
  else none

/-- Measurability of the fixed-case DOWN credit follows by splitting on the
measurable finite slot, grid-index and tuple outputs. -/
theorem measurable_fixedBlockDownArmIndex (p : Parameters) (s : Fin (n_boot p))
    (incoming : Finset (Follower p.m)) (c : IDArray p × BlockDrawCode p incoming)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (t : Fin p.T) :
    Measurable (fun z : InputCoordinates p => fixedBlockDownArmIndex p s incoming c rewards z t) := by
  let key := fun z : InputCoordinates p =>
    (fixedBlockSlot p s incoming c rewards z t,
      (fixedBlockObservationIndex p s incoming c rewards z t (coordinator p.two_le_m),
        fixedBlockTuple p s incoming c rewards z t))
  have hkey : Measurable key := by
    have hslot := (measurable_pi_apply t).comp
      (measurable_fixedBlockSlot p s incoming c rewards)
    have hobs := (measurable_pi_apply (coordinator p.two_le_m)).comp
      ((measurable_pi_apply t).comp
        (measurable_fixedBlockObservationIndex p s incoming c rewards))
    have htuple := (measurable_pi_apply t).comp
      (measurable_fixedBlockTuple p s incoming c rewards)
    exact hslot.prodMk (hobs.prodMk htuple)
  have hbranch : ∀ v : Slot × (Fin (D p + 1) × OrderedTupleSampler.Tuple p.m p.K),
      Measurable (fun _ : InputCoordinates p =>
        if v.1 = downSlot ∧ 0 < v.2.1.val then
          some (v.2.2.val (coordinator p.two_le_m)) else none) := by
    intro v
    exact measurable_const
  have hmeas := measurable_by_countable_cases key hkey
    (fun v _ => if v.1 = downSlot ∧ 0 < v.2.1.val then
      some (v.2.2.val (coordinator p.two_le_m)) else none) hbranch
  change Measurable (fun z : InputCoordinates p =>
    (fun v : Slot × (Fin (D p + 1) × OrderedTupleSampler.Tuple p.m p.K) =>
      if v.1 = downSlot ∧ 0 < v.2.1.val then
        some (v.2.2.val (coordinator p.two_le_m)) else none) (key z))
  exact hmeas

/-- The actual DOWN-credit map at a fixed boundary is measurable on the
accepted product input. -/
theorem measurable_physicalDownArmIndex_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) (t : Fin p.T) :
    Measurable (fun z : InputCoordinates p => physicalDownArmIndex p C_star C_h eta
      rewards b h z t) := by
  let s := ReferenceInitializationRun.nextBlock b h
  let incoming := ReferenceInitializationRun.uninformed b
  let key := blockCaseKey p s incoming b.numerators b.weight_ge_one
  have hkey : Measurable key :=
    measurable_fst.prodMk
      (measurable_blockDrawCode p s incoming b.numerators b.weight_ge_one)
  have hbranch : ∀ c : IDArray p × BlockDrawCode p incoming,
      Measurable (fun z : InputCoordinates p => fixedBlockDownArmIndex p s incoming c rewards z t) := by
    intro c
    exact measurable_fixedBlockDownArmIndex p s incoming c rewards t
  have hmeas := measurable_by_countable_cases key hkey
    (fun c z => fixedBlockDownArmIndex p s incoming c rewards z t) hbranch
  change Measurable (fun z : InputCoordinates p =>
    fixedBlockDownArmIndex p s incoming (key z) rewards z t)
  exact hmeas

/-- The actual cumulative DOWN counters produced at the next block boundary
are measurable when the incoming boundary is fixed. -/
theorem measurable_updatedCounters_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) :
    Measurable (fun z : InputCoordinates p =>
      ReferenceInitializationRun.updatedCounters
        (inputOfCoordinates p C_star C_h eta rewards z) b h) := by
  let s := ReferenceInitializationRun.nextBlock b h
  have hdown (t : Fin p.T) : Measurable (fun z : InputCoordinates p =>
      physicalDownArmIndex p C_star C_h eta rewards b h z t) :=
    measurable_physicalDownArmIndex_at_fixedBoundary p C_star C_h eta rewards b h t
  apply measurable_pi_iff.mpr
  intro a
  have hsum : Measurable (fun z : InputCoordinates p =>
      ∑ t ∈ calendarBlock p s,
        if physicalDownArmIndex p C_star C_h eta rewards b h z t = some a then 1 else 0) := by
    apply Finset.measurable_sum (calendarBlock p s)
    intro t ht
    have hcondition : MeasurableSet {z : InputCoordinates p |
        physicalDownArmIndex p C_star C_h eta rewards b h z t = some a} :=
      measurableSet_eq_fun (hdown t) measurable_const
    exact Measurable.ite hcondition measurable_const measurable_const
  have heq : (fun z : InputCoordinates p =>
      ReferenceInitializationRun.updatedCounters
        (inputOfCoordinates p C_star C_h eta rewards z) b h a) =
      (fun z => b.counters a + ∑ t ∈ calendarBlock p s,
        if physicalDownArmIndex p C_star C_h eta rewards b h z t = some a then 1 else 0) := by
    funext z
    simp only [ReferenceInitializationRun.updatedCounters]
    congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [← physicalDownArmIndex_eq_downArm p
      (inputOfCoordinates p C_star C_h eta rewards z) b h t]
    simp only [inputOfCoordinates]
    simp only [Prod.eta]
    rfl
  rw [heq]
  exact measurable_const.add hsum

/-- The actual cumulative threshold crossing is measurable at a fixed
incoming boundary, using the true source monitor and launch budget. -/
theorem measurable_crosses_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) :
    Measurable (fun z : InputCoordinates p =>
      ReferenceInitializationRun.crosses
        (inputOfCoordinates p C_star C_h eta rewards z) b h) := by
  have hcounts := measurable_updatedCounters_at_fixedBoundary p C_star C_h eta rewards b h
  have hbranch : ∀ c : Fin p.K → ℕ, Measurable (fun _ : InputCoordinates p =>
      decide (BootstrapLaunchMonitor.monitorValue p c >
        4 * BootstrapStartupCostScale.Q C_star C_h p)) := by
    intro c
    exact measurable_const
  have hmeas := measurable_by_countable_cases
    (fun z : InputCoordinates p =>
      ReferenceInitializationRun.updatedCounters
        (inputOfCoordinates p C_star C_h eta rewards z) b h) hcounts
    (fun c _ => decide (BootstrapLaunchMonitor.monitorValue p c >
      4 * BootstrapStartupCostScale.Q C_star C_h p)) hbranch
  change Measurable (fun z : InputCoordinates p =>
    (fun c : Fin p.K → ℕ => decide (BootstrapLaunchMonitor.monitorValue p c >
      4 * BootstrapStartupCostScale.Q C_star C_h p))
        (ReferenceInitializationRun.updatedCounters
          (inputOfCoordinates p C_star C_h eta rewards z) b h))
  exact hmeas

/-- Finite/natural observables characterizing the entire existing boundary. -/
abbrev BoundaryCode (p : Parameters) :=
  ℕ × PaddedPhysicalLog p × (Follower p.m → Option (Activation p)) ×
    (Fin (p.m - 1) → Fin p.K → ℕ) × (Fin p.K → ℕ) ×
      Option (Fin (n_boot p)) × (Follower p.m → Bool)

/-- This is an encoding, not another state or another recursion. -/
def boundaryCode (p : Parameters) (b : Boundary p) : BoundaryCode p :=
  (b.completed, boundaryLog p b, b.activation, b.numerators,
    b.counters, b.crossing, b.forcedFailure)

theorem observationGridIndex_injective (p : Parameters) :
    Function.Injective (observationGridIndex p) := by
  intro y z h
  apply Subtype.ext
  apply Subtype.ext
  rw [observationGridIndex_value p y, observationGridIndex_value p z, h]

/-- Exact arm/index equality recovers even the real observation and all proof
fields. The padding and completed index recover the dependent history length. -/
theorem boundaryCode_injective (p : Parameters) :
    Function.Injective (boundaryCode p) := by
  intro b c he
  have hc : b.completed = c.completed := congrArg Prod.fst he
  have hl : boundaryLog p b = boundaryLog p c := congrArg (fun v => v.2.1) he
  have ha : b.activation = c.activation := congrArg (fun v => v.2.2.1) he
  have hn : b.numerators = c.numerators := congrArg (fun v => v.2.2.2.1) he
  have hct : b.counters = c.counters := congrArg (fun v => v.2.2.2.2.1) he
  have hx : b.crossing = c.crossing := congrArg (fun v => v.2.2.2.2.2.1) he
  have hf : b.forcedFailure = c.forcedFailure := congrArg (fun v => v.2.2.2.2.2.2) he
  cases b with
  | mk n nb hist act ab num wb counts cross fail =>
    cases c with
    | mk n' nb' hist' act' ab' num' wb' counts' cross' fail' =>
      dsimp only at hc ha hn hct hx hf
      subst n'
      have hh : hist = hist' := by
        funext i t
        let t' : Fin p.T := ⟨t.val, Nat.lt_of_lt_of_le t.isLt (elapsed_le_T p n)⟩
        have he' := congrFun (congrFun hl i) t'
        simp only [boundaryLog, t', dite_eq_left t.isLt, Option.some.injEq,
          Prod.mk.injEq] at he'
        apply Prod.ext he'.1
        exact observationGridIndex_injective p he'.2
      subst hist'
      subst act'
      subst num'
      subst counts'
      subst cross'
      subst fail'
      rfl

/-- Countability is proved from the complete observable encoding, before any
measurable space is put on `Boundary`. No real buffer is made discrete. -/
instance boundaryCountable (p : Parameters) : Countable (Boundary p) :=
  (boundaryCode_injective p).countable

instance boundaryMeasurableSpace (p : Parameters) : MeasurableSpace (Boundary p) := ⊤
instance boundaryMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (Boundary p) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

private theorem measurable_of_encoding {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (encode : β → γ) (hinj : Function.Injective encode) (f : α → β)
    (hf : Measurable (fun x => encode (f x))) : Measurable f := by
  apply measurable_to_countable'
  intro b
  have he : f ⁻¹' {b} = (fun x => encode (f x)) ⁻¹' {encode b} := by
    ext x
    exact hinj.eq_iff.symm
  rw [he]
  exact hf (measurableSet_singleton _)

/-- All fields, including the literal dependent history, are determined by
these observables. -/
theorem boundaryCode_eq_iff (p : Parameters) (b c : Boundary p) :
    boundaryCode p b = boundaryCode p c ↔ b = c :=
  (boundaryCode_injective p).eq_iff

/-- The exact none criterion excludes padding anywhere inside the prefix. -/
theorem boundaryLog_eq_none_iff (p : Parameters) (b : Boundary p)
    (i : Fin p.m) (t : Fin p.T) :
    boundaryLog p b i t = none ↔ elapsed p b.completed ≤ t.val := by
  unfold boundaryLog
  split_ifs with ht
  · simp only [false_iff, not_le]
    exact ht
  · simp only [true_iff]
    exact Nat.le_of_not_gt ht

instance registersCountable : Countable BootstrapTruePrefixController.Registers := by
  apply Function.Injective.countable (f := fun r : BootstrapTruePrefixController.Registers =>
    (r.count, r.dead, r.pending))
  intro a b h
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

instance registersMeasurableSpace : MeasurableSpace BootstrapTruePrefixController.Registers := ⊤
instance registersMeasurableSingletonClass :
    MeasurableSingletonClass BootstrapTruePrefixController.Registers where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

section FixedCandidate

variable (p : Parameters) (s : Fin (n_boot p))
  (incoming : Finset (Follower p.m)) (c : IDArray p × BlockDrawCode p incoming)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))

def fixedPhysical (z : InputCoordinates p) : BootstrapPhysicalBlock.Input p s :=
  BootstrapBlockCausality.blockInput (s := s) incoming c.2.1 c.2.2.1
    c.2.2.2.1 c.1 c.2.2.2.2 rewards (localCoordinatesOf p incoming c.2 z)

private theorem measurable_fixedEligible (i : {i // i ∈ incoming}) (t : Fin p.T) :
    Measurable (fun z : InputCoordinates p =>
      BootstrapTruePrefixController.eligibleFlag (fixedPhysical p s incoming c rewards z) i t) := by
  classical
  let encode := fun v : Slot × Fin (D p + 1) =>
    decide (t ∈ calendarBlock p s ∧ c.2.1 i = true ∧ c.1 (c.2.2.2.1 i) t = false ∧
      v.1 = dataSlot ∧ 0 < v.2.val)
  have hs := (measurable_pi_apply t).comp (measurable_fixedBlockSlot p s incoming c rewards)
  have ho := (measurable_pi_apply (followerPlayer p.two_le_m i.val)).comp
    ((measurable_pi_apply t).comp (measurable_fixedBlockObservationIndex p s incoming c rewards))
  have hm := (measurable_of_countable encode).comp (hs.prodMk ho)
  have heq : (fun z : InputCoordinates p =>
      BootstrapTruePrefixController.eligibleFlag (fixedPhysical p s incoming c rewards z) i t) =
      (fun z => encode (fixedBlockSlot p s incoming c rewards z t,
        fixedBlockObservationIndex p s incoming c rewards z t
          (followerPlayer p.two_le_m i.val))) := by
    funext z
    simp only [encode, BootstrapTruePrefixController.eligibleFlag,
      BootstrapTruePrefixController.eligible, fixedPhysical, fixedBlockSlot,
      fixedBlockObservationIndex, BootstrapBlockCausality.runObservationIndex,
      BootstrapBlockCausality.blockRun, BootstrapBlockCausality.blockInput,
      BootstrapBlockCausality.inputOf]
    exact decide_eq_decide.mpr Iff.rfl
  rw [heq]
  exact hm

/-- Induction on the accepted candidate recursion, including frozen pending
registers. No candidate-output assumption is supplied. -/
theorem measurable_fixedCandidate (i : {i // i ∈ incoming}) (k : ℕ) :
    Measurable (fun z : InputCoordinates p =>
      BootstrapTruePrefixController.run (fixedPhysical p s incoming c rewards z) i k) := by
  classical
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hk : k < p.T
    · let t : Fin p.T := ⟨k, hk⟩
      have he := measurable_fixedEligible p s incoming c rewards i t
      have hb : Measurable (fun z : InputCoordinates p =>
          BootstrapTruePrefixController.trueForwardBit
            (fixedPhysical p s incoming c rewards z) i t) := by
        change Measurable (fun z : InputCoordinates p => z.2.1.1 (c.2.2.2.1 i) t)
        exact (measurable_pi_apply t).comp ((measurable_pi_apply (c.2.2.2.1 i)).comp
          (measurable_fst.comp (measurable_fst.comp measurable_snd)))
      let update := fun v : Bool × Bool × BootstrapTruePrefixController.Registers =>
        if v.1 = true then
          if v.2.2.pending = false then
            let dead := v.2.2.dead || decide (v.2.1 = false)
            let count := v.2.2.count + 1
            (⟨count, dead, decide (q_dec p ≤ count ∧ dead = false)⟩ :
              BootstrapTruePrefixController.Registers)
          else v.2.2
        else v.2.2
      have hm := (measurable_of_countable update).comp (he.prodMk (hb.prodMk ih))
      simpa only [BootstrapTruePrefixController.run, hk, dite_true,
        BootstrapTruePrefixController.advance, t, update, Function.comp_def] using hm
    · simpa only [BootstrapTruePrefixController.run, hk, dite_false] using ih

end FixedCandidate

/-- The actual candidate registers at a fixed boundary are measurable, with
all activity/held-arm/ID draws made by the accepted private adapter. -/
theorem measurable_candidate_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b}) :
    Measurable (fun z : InputCoordinates p =>
      candidate (inputOfCoordinates p C_star C_h eta rewards z) b h i) := by
  let s := nextBlock b h
  let incoming := uninformed b
  let key := blockCaseKey p s incoming b.numerators b.weight_ge_one
  have hkey : Measurable key := measurable_fst.prodMk
    (measurable_blockDrawCode p s incoming b.numerators b.weight_ge_one)
  exact measurable_by_countable_cases key hkey
    (fun c z => BootstrapTruePrefixController.run (fixedPhysical p s incoming c rewards z) i p.T)
    (fun c => measurable_fixedCandidate p s incoming c rewards i p.T)

/-- These are the actual updater's fields. The raw gain counts the entire
block, including positive stays after saving, and the activity gate is exact. -/
theorem weightInput_fields {p : Parameters} (x : Input p) (b : Boundary p)
    (h : b.completed < n_boot p) (i : {i // i ∈ uninformed b}) :
    (weightInput x b h i).enabled = (physical x b h).active i ∧
    (weightInput x b h i).held = (physical x b h).held i ∧
    (weightInput x b h i).gain =
      (BootstrapPhysicalBlock.physicalStayRounds (physical x b h) i).card := by
  refine ⟨?_, rfl, ?_⟩
  · exact BootstrapPhysicalBlock.observationTrace_blockEnabled _ _ _ _
  · change BootstrapBlockConstruction.calendarBlockGain
      (BootstrapPhysicalBlock.observationTrace (physical x b h) i
        (BootstrapTruePrefixController.savedAt (physical x b h) i) false) (nextBlock b h) = _
    exact BootstrapPhysicalBlock.calendarBlockGain_eq_physical_count _ _ _ _

section FixedBoundary

variable (p : Parameters) (C_star C_h : ℝ) (eta : LearningRate)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p)
  (h : b.completed < n_boot p)

local notation "X" => inputOfCoordinates p C_star C_h eta rewards

/-- The full held-arm raw gain is measurable without truncating at pending. -/
theorem measurable_weightGain_at_fixedBoundary (i : {i // i ∈ uninformed b}) :
    Measurable (fun z : InputCoordinates p => (weightInput (X z) b h i).gain) := by
  let s := nextBlock b h
  let draws := blockDrawCode p s (uninformed b) b.numerators b.weight_ge_one
  have hd := measurable_blockDrawCode p s (uninformed b) b.numerators b.weight_ge_one
  have hi : Measurable (fun z : InputCoordinates p => (draws z).2.2.1 i) :=
    (measurable_pi_apply i).comp ((measurable_fst.comp measurable_snd).comp
      (measurable_snd.comp hd))
  have ho := measurable_physicalObservationIndex_at_fixedBoundary p C_star C_h eta rewards b h
  have hoi : Measurable (fun z : InputCoordinates p => fun t =>
      BootstrapPhysicalBlock.observationIndex (physical (X z) b h)
        (BootstrapPhysicalBlock.run (physical (X z) b h) t.val) t
        (followerPlayer p.two_le_m i.val)) := by
    apply measurable_pi_iff.mpr
    intro t
    exact (measurable_pi_apply (followerPlayer p.two_le_m i.val)).comp
      ((measurable_pi_apply t).comp ho)
  let gain := fun v : IDArray p × Fin (A_id p) × (Fin p.T → Fin (D p + 1)) =>
    ((calendarBlock p s).filter fun t => v.1 v.2.1 t = false ∧ 0 < (v.2.2 t).val).card
  have hm := (measurable_of_countable gain).comp (measurable_fst.prodMk (hi.prodMk hoi))
  have heq : (fun z : InputCoordinates p => (weightInput (X z) b h i).gain) =
      (fun z => gain (z.1, (draws z).2.2.1 i, fun t =>
        BootstrapPhysicalBlock.observationIndex (physical (X z) b h)
          (BootstrapPhysicalBlock.run (physical (X z) b h) t.val) t
          (followerPlayer p.two_le_m i.val))) := by
    funext z
    rw [(weightInput_fields (X z) b h i).2.2]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro t ht
    exact and_congr Iff.rfl (BootstrapPhysicalBlock.observationIndex_pos_iff _ _ _ _).symm
  rw [heq]
  exact hm

/-- The actual natural numerator update is measurable; no weight-update
conclusion is a premise. -/
theorem measurable_updatedNumerators_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => updatedNumerators (X z) b h) := by
  apply measurable_pi_iff.mpr
  intro j
  let i : Follower p.m := ⟨j.val, j.isLt⟩
  by_cases hi : i ∈ uninformed b
  · let i' : {i // i ∈ uninformed b} := ⟨i, hi⟩
    let draws := blockDrawCode p (nextBlock b h) (uninformed b) b.numerators b.weight_ge_one
    have hd := measurable_blockDrawCode p (nextBlock b h) (uninformed b)
      b.numerators b.weight_ge_one
    have ha : Measurable (fun z : InputCoordinates p => (draws z).1 i') :=
      (measurable_pi_apply i').comp (measurable_fst.comp hd)
    have hh : Measurable (fun z : InputCoordinates p => (draws z).2.1 i') :=
      (measurable_pi_apply i').comp ((measurable_fst.comp measurable_snd).comp hd)
    have hg := measurable_weightGain_at_fixedBoundary p C_star C_h eta rewards b h i'
    let update := fun v : Bool × Fin p.K × ℕ => fun a : Fin p.K =>
      if v.1 = true ∧ v.2.1 = a then
        ⌊(b.numerators j a : ℝ) * (1 + (v.2.2 : ℝ) /
          (4 * p.K * B_boot p * BootstrapWeightPotential.probability
            (b_N p) (b.numerators j) a))⌋₊
      else b.numerators j a
    have hm := (measurable_of_countable update).comp (ha.prodMk (hh.prodMk hg))
    have heq : (fun z : InputCoordinates p => updatedNumerators (X z) b h j) =
        (fun z => update ((draws z).1 i', (draws z).2.1 i',
          (weightInput (X z) b h i').gain)) := by
      funext z a
      change (if hi : i ∈ uninformed b then
        BootstrapWeightPotential.next (b_N p) (b.numerators j)
          (weightInput (X z) b h ⟨i, hi⟩) else b.numerators j) a = _
      rw [dite_eq_left hi]
      unfold BootstrapWeightPotential.next
      rw [(weightInput_fields (X z) b h i').1,
        (weightInput_fields (X z) b h i').2.1]
      rfl
    rw [heq]
    exact hm
  · have heq : (fun z : InputCoordinates p => updatedNumerators (X z) b h j) =
        (fun _ => b.numerators j) := by
      funext z
      change (if hi : i ∈ uninformed b then
        BootstrapWeightPotential.next (b_N p) (b.numerators j)
          (weightInput (X z) b h ⟨i, hi⟩) else b.numerators j) = _
      exact dite_eq_right hi
    rw [heq]
    exact measurable_const

theorem measurable_declaredActivation_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => declaredActivation (X z) b h) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases hi : i ∈ uninformed b
  · have hp := (measurable_of_countable
        (fun r : BootstrapTruePrefixController.Registers =>
          if r.pending then some (boundaryActivation b) else none)).comp
      (measurable_candidate_at_fixedBoundary p C_star C_h eta rewards b h ⟨i, hi⟩)
    simpa only [declaredActivation, hi, dite_true, Function.comp_def] using hp
  · simpa only [declaredActivation, hi, dite_false] using
      (measurable_const : Measurable fun _ : InputCoordinates p => b.activation i)

theorem measurable_forced_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => forced (X z) b h) := by
  apply measurable_pi_iff.mpr
  intro i
  have hc := measurable_crosses_at_fixedBoundary p C_star C_h eta rewards b h
  have ha := (measurable_pi_apply i).comp
    (measurable_declaredActivation_at_fixedBoundary p C_star C_h eta rewards b h)
  exact (measurable_of_countable (fun v : Bool × Option (Activation p) =>
    v.1 && v.2.isNone)).comp (hc.prodMk ha)

theorem measurable_finalActivation_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => finalActivation (X z) b h) := by
  apply measurable_pi_iff.mpr
  intro i
  have hf := (measurable_pi_apply i).comp
    (measurable_forced_at_fixedBoundary p C_star C_h eta rewards b h)
  have ha := (measurable_pi_apply i).comp
    (measurable_declaredActivation_at_fixedBoundary p C_star C_h eta rewards b h)
  exact (measurable_of_countable (fun v : Bool × Option (Activation p) =>
    if v.1 then some (boundaryActivation b) else v.2)).comp (hf.prodMk ha)

/-- Exact generated history extension on the original input product. -/
theorem measurable_finishBlock_log_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => boundaryLog p (finishBlock (X z) b h)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro t
  by_cases ht : t.val < elapsed p (b.completed + 1)
  · by_cases hp : t.val < elapsed p b.completed
    · have heq : (fun z : InputCoordinates p => boundaryLog p (finishBlock (X z) b h) i t) =
          (fun _ => some ((b.history i ⟨t.val, hp⟩).1,
            observationGridIndex p (b.history i ⟨t.val, hp⟩).2)) := by
        funext z
        simp only [boundaryLog, finishBlock, ht, dite_true, extendedHistory, hp]
      rw [heq]
      exact measurable_const
    · have ha := measurable_physicalAction_at_fixedBoundary p C_star C_h eta rewards b h t i
      have ho := (measurable_pi_apply i).comp ((measurable_pi_apply t).comp
        (measurable_physicalObservationIndex_at_fixedBoundary p C_star C_h eta rewards b h))
      have hm := (measurable_of_countable
        (fun v : Fin p.K × Fin (D p + 1) => some v)).comp (ha.prodMk ho)
      simpa only [boundaryLog, finishBlock, ht, dite_true, extendedHistory, hp,
        dite_false, ownEntry, observationGridIndex_ownObservation, Function.comp_def] using hm
  · have heq : (fun z : InputCoordinates p => boundaryLog p (finishBlock (X z) b h) i t) =
        (fun _ => none) := by
      funext z
      exact boundaryLog_none_of_outside p _ i t ht
    rw [heq]
    exact measurable_const

/-- All fields of the actual successor boundary, rather than only its fixed
block feedback, are measurable. -/
theorem measurable_finishBlock_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => finishBlock (X z) b h) := by
  apply measurable_of_encoding (boundaryCode p) (boundaryCode_injective p)
  have hl := measurable_finishBlock_log_at_fixedBoundary p C_star C_h eta rewards b h
  have ha := measurable_finalActivation_at_fixedBoundary p C_star C_h eta rewards b h
  have hn := measurable_updatedNumerators_at_fixedBoundary p C_star C_h eta rewards b h
  have hc := measurable_updatedCounters_at_fixedBoundary p C_star C_h eta rewards b h
  have hx := (measurable_of_countable (fun v : Bool =>
    if v then some (nextBlock b h) else none)).comp
      (measurable_crosses_at_fixedBoundary p C_star C_h eta rewards b h)
  have hf : Measurable (fun z : InputCoordinates p => fun i =>
      b.forcedFailure i || forced (X z) b h i) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_of_countable (fun v : Bool => b.forcedFailure i || v)).comp
      ((measurable_pi_apply i).comp
        (measurable_forced_at_fixedBoundary p C_star C_h eta rewards b h))
  exact measurable_const.prodMk (hl.prodMk (ha.prodMk (hn.prodMk (hc.prodMk (hx.prodMk hf)))))

/-- Stopped and exhausted branches preserve the actual boundary. -/
theorem measurable_advance_at_fixedBoundary :
    Measurable (fun z : InputCoordinates p => advance (X z) b) := by
  unfold advance
  split_ifs with hc hn
  · exact measurable_const
  · exact measurable_finishBlock_at_fixedBoundary p C_star C_h eta rewards b hn
  · exact measurable_const

end FixedBoundary

section ActualRun

variable (p : Parameters) (C_star C_h : ℝ) (eta : LearningRate)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
local notation "X" => inputOfCoordinates p C_star C_h eta rewards

/-- Adaptive induction on the EXISTING stopped physical producer, at every
opportunity, including opportunities after an early stop or exhaustion. -/
theorem measurable_run (r : ℕ) :
    Measurable (fun z : InputCoordinates p => ReferenceInitializationRun.run (X z) r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    exact measurable_by_countable_cases
      (fun z : InputCoordinates p => ReferenceInitializationRun.run (X z) r) ih
      (fun b z => advance (X z) b)
      (fun b => measurable_advance_at_fixedBoundary p C_star C_h eta rewards b)

theorem measurable_run_completed (r : ℕ) :
    Measurable (fun z : InputCoordinates p => (ReferenceInitializationRun.run (X z) r).completed) :=
  (measurable_of_countable (fun b : Boundary p => b.completed)).comp
    (measurable_run p C_star C_h eta rewards r)

theorem measurable_run_activation (r : ℕ) :
    Measurable (fun z : InputCoordinates p => (ReferenceInitializationRun.run (X z) r).activation) :=
  (measurable_of_countable (fun b : Boundary p => b.activation)).comp
    (measurable_run p C_star C_h eta rewards r)

theorem measurable_run_numerators (r : ℕ) :
    Measurable (fun z : InputCoordinates p => (ReferenceInitializationRun.run (X z) r).numerators) :=
  (measurable_of_countable (fun b : Boundary p => b.numerators)).comp
    (measurable_run p C_star C_h eta rewards r)

theorem measurable_run_counters (r : ℕ) :
    Measurable (fun z : InputCoordinates p => (ReferenceInitializationRun.run (X z) r).counters) :=
  (measurable_of_countable (fun b : Boundary p => b.counters)).comp
    (measurable_run p C_star C_h eta rewards r)

theorem measurable_run_crossing (r : ℕ) :
    Measurable (fun z : InputCoordinates p => (ReferenceInitializationRun.run (X z) r).crossing) :=
  (measurable_of_countable (fun b : Boundary p => b.crossing)).comp
    (measurable_run p C_star C_h eta rewards r)

theorem measurable_run_forcedFailure (r : ℕ) :
    Measurable (fun z : InputCoordinates p =>
      (ReferenceInitializationRun.run (X z) r).forcedFailure) :=
  (measurable_of_countable (fun b : Boundary p => b.forcedFailure)).comp
    (measurable_run p C_star C_h eta rewards r)

/-- The entire generated physical history, keeping arms AND exact feedback
indices; its padding is characterized below. -/
theorem measurable_run_log (r : ℕ) :
    Measurable (fun z : InputCoordinates p =>
      boundaryLog p (ReferenceInitializationRun.run (X z) r)) :=
  (measurable_of_countable (boundaryLog p)).comp (measurable_run p C_star C_h eta rewards r)

/-- Literal correspondence with the existing run's history on every generated
round, with no supplied-history premise. -/
theorem run_log_prefix (z : InputCoordinates p) (r : ℕ) (i : Fin p.m)
    (t : Fin (elapsed p (ReferenceInitializationRun.run (X z) r).completed)) :
    let b := ReferenceInitializationRun.run (X z) r
    boundaryLog p b i ⟨t.val, Nat.lt_of_lt_of_le t.isLt (elapsed_le_T p b.completed)⟩ =
      some ((b.history i t).1, observationGridIndex p (b.history i t).2) :=
  boundaryLog_prefix p _ i t

theorem run_log_value (z : InputCoordinates p) (r : ℕ) (i : Fin p.m)
    (t : Fin (elapsed p (ReferenceInitializationRun.run (X z) r).completed)) :
    let b := ReferenceInitializationRun.run (X z) r
    (observationGridIndex p (b.history i t).2).val / (D p : ℝ) =
      (b.history i t).2.val.val := boundaryLog_value p _ i t

theorem run_log_eq_none_iff (z : InputCoordinates p) (r : ℕ) (i : Fin p.m) (t : Fin p.T) :
    boundaryLog p (ReferenceInitializationRun.run (X z) r) i t = none ↔
      elapsed p (ReferenceInitializationRun.run (X z) r).completed ≤ t.val :=
  boundaryLog_eq_none_iff p _ i t

/-- The actual terminal boundary, including all early-stopped outputs. -/
theorem measurable_output :
    Measurable (fun z : InputCoordinates p => output (X z)) :=
  measurable_run p C_star C_h eta rewards (n_boot p)

/-- The literal source launch map, including no launch and terminal `T+1`. -/
theorem measurable_launchRound :
    Measurable (fun z : InputCoordinates p => launchRound (X z)) :=
  (measurable_of_countable (fun b : Boundary p =>
    if b.crossing.isSome then elapsed p b.completed + 1 else p.T + 1)).comp
      (measurable_output p C_star C_h eta rewards)

end ActualRun

/-- A countable observable key suffices when the output is constant on its
fibers. This does not require a discrete space on the original input. -/
private theorem measurable_of_countable_key {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] (key : α → β) (hk : Measurable key) (f : α → γ)
    (hf : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  intro s _
  have he : f ⁻¹' s = key ⁻¹' (key '' (f ⁻¹' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      change f x ∈ s
      rw [hf x y he.symm]
      exact hy
  rw [he]
  exact hk (Set.to_countable _).measurableSet

/-- The ordinary decoder reads these finite row values. Thinning scalars and
DATA buffers remain continuous and are not part of this discrete key. -/
def ordinaryRowCode (p : Parameters) (i : Fin (p.m - 1)) (row : CompleteRow p) :=
  fun t : Fin p.T => (slotDraw (row.2 t).1,
    selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1,
    (row.2 t).2 (0, i))

theorem measurable_ordinaryRowCode (p : Parameters) (i : Fin (p.m - 1)) :
    Measurable (ordinaryRowCode p i) := by
  apply measurable_pi_iff.mpr
  intro t
  have hs : Measurable (fun row : CompleteRow p => (row.2 t).1) :=
    measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)
  exact (measurable_slotDraw.comp hs).prodMk
    (((measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp hs).prodMk
      ((measurable_pi_apply (0, i)).comp
        (measurable_snd.comp ((measurable_pi_apply t).comp measurable_snd))))

private theorem downInput_eq_of_rowCode {p : Parameters} (i : Fin (p.m - 1))
    (row row' : CompleteRow p) (alpha : Activation p) (t : Fin p.T)
    (own : Fin p.K × Observation p) (he : ordinaryRowCode p i row = ordinaryRowCode p i row') :
    downInput i row alpha t own = downInput i row' alpha t own := by
  have hs := congrArg Prod.fst (congrFun he t)
  have hi := congrArg (fun v => v.2.1) (congrFun he t)
  have ha := congrArg (fun v => v.2.2) (congrFun he t)
  dsimp only [ordinaryRowCode] at hs hi ha
  simp only [downInput, hs, hi, ha]

/-- The accepted replay's decoder and failure projections ignore the buffer's
contents; its buffer itself is still carried by the same replay. -/
private theorem replay_run_down_eq {p : Parameters} {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (row row' : CompleteRow p) (alpha : Activation p)
    (hist : LocalHistory p n) (hn : n ≤ p.T) (us : List (Fin n))
    (he : ordinaryRowCode p i row = ordinaryRowCode p i row')
    (s s' : State p eta) (hb : s.downBatch = s'.downBatch)
    (hf : s.initializationFailure = s'.initializationFailure) (hs : s.status = s'.status) :
    (ReferencePrelaunchFollower.run i row alpha hist hn us s).downBatch =
      (ReferencePrelaunchFollower.run i row' alpha hist hn us s').downBatch ∧
    (ReferencePrelaunchFollower.run i row alpha hist hn us s).initializationFailure =
      (ReferencePrelaunchFollower.run i row' alpha hist hn us s').initializationFailure := by
  induction us generalizing s s' with
  | nil => exact ⟨hb, hf⟩
  | cons u us ih =>
    let t := calendar hn u
    have hd : decodeAt i row alpha t (hist u) s.downBatch =
        decodeAt i row' alpha t (hist u) s'.downBatch := by
      unfold decodeAt traceAt
      rw [hb, downInput_eq_of_rowCode i row row' alpha t (hist u) he]
    have hp : passing_at eta i row alpha t (hist u) s.downBatch ↔
        passing_at eta i row' alpha t (hist u) s'.downBatch := by
      unfold passing_at parsedAt
      rw [hd]
    apply ih
    · simp only [step, hs]
      split_ifs
      · exact congrArg Prod.fst hd
      · exact hb
    · simp only [step, hs]
      split_ifs
      · rw [hf, decide_eq_decide.mpr hp]
      · exact hf
    · rw [(step_registers i row alpha t (hist u) s).2.2.2.2,
        (step_registers i row' alpha t (hist u) s').2.2.2.2, hs]

/-- The suppressed ordinary acceptance flag is measurable on the original
continuous row, by induction through the accepted decoder with carried batches. -/
theorem measurable_replay_down_projection (p : Parameters) {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (alpha : Activation p) (hist : LocalHistory p n) (hn : n ≤ p.T) :
    Measurable (fun row : CompleteRow p =>
      (replay eta i row alpha hist hn).initializationFailure) := by
  apply measurable_of_countable_key (ordinaryRowCode p i) (measurable_ordinaryRowCode p i)
  intro row row' he
  exact (replay_run_down_eq eta i row row' alpha hist hn _ he
    (ReferencePrelaunchFollower.initial p eta) (ReferencePrelaunchFollower.initial p eta)
    rfl rfl rfl).2

/-- Ordinary suppressed acceptance on a fixed generated boundary; the carried
history is the actual boundary history, not a caller-supplied physical run. -/
theorem measurable_ordinaryFailure_at_fixedBoundary (p : Parameters)
    (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (b : Boundary p) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      (ordinary (inputOfCoordinates p C_star C_h eta rewards z) b i).initializationFailure) := by
  unfold ordinary
  split_ifs
  · exact measurable_const
  · cases ha : b.activation i with
    | none => exact measurable_const
    | some a =>
      exact (measurable_replay_down_projection p eta
        (BootstrapPhysicalInput.sourceFollowerIndex p i) a
        (b.history (followerPlayer p.two_le_m i)) (elapsed_le_T p b.completed)).comp
          (measurable_fst.comp measurable_snd)

/-- The ACTUAL failure output, including both forced correction and ordinary
suppressed prelaunch DOWN acceptance. No such acceptance is assumed measurable. -/
theorem measurable_initializationFailure (p : Parameters) (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (r : ℕ) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      let x := inputOfCoordinates p C_star C_h eta rewards z
      initializationFailure x (ReferenceInitializationRun.run x r) i) := by
  apply measurable_by_countable_cases
    (fun z : InputCoordinates p =>
      ReferenceInitializationRun.run (inputOfCoordinates p C_star C_h eta rewards z) r)
    (measurable_run p C_star C_h eta rewards r)
    (fun b z => initializationFailure (inputOfCoordinates p C_star C_h eta rewards z) b i)
  intro b
  exact (measurable_of_countable (fun v : Bool => b.forcedFailure i || v)).comp
    (measurable_ordinaryFailure_at_fixedBoundary p C_star C_h eta rewards b i)

theorem measurable_output_initializationFailure (p : Parameters) (C_star C_h : ℝ)
    (eta : LearningRate) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      let x := inputOfCoordinates p C_star C_h eta rewards z
      initializationFailure x (output x) i) :=
  measurable_initializationFailure p C_star C_h eta rewards (n_boot p) i

/-- Discrete lists are used only when their elements are actually countable;
this instance does not apply to buffers carrying real thinning scalars. -/
instance listCountableMeasurableSpace (α : Type*) [Countable α] : MeasurableSpace (List α) := ⊤
instance listCountableMeasurableSingletonClass (α : Type*) [Countable α] :
    MeasurableSingletonClass (List α) where
  measurableSet_singleton _ := MeasurableSpace.measurableSet_top

/-- Exact observable encoding of the decoder's partial AND completed batches. -/
def downBatchCode {T B : ℕ} (s : AffineBatchDecoder.State T B) :=
  (s.pending.map (fun e => (e.time, e.sample)),
    s.completed.map (fun es => es.map (fun e => (e.time, e.sample))))

theorem downBatchCode_injective (T B : ℕ) :
    Function.Injective (@downBatchCode T B) := by
  have hi : Function.Injective (fun e : AffineBatchDecoder.Entry T B => (e.time, e.sample)) := by
    intro a b he
    cases a
    cases b
    cases he
    rfl
  intro a b he
  have hp := List.map_injective_iff.mpr hi (congrArg Prod.fst he)
  have hc := List.map_injective_iff.mpr (List.map_injective_iff.mpr hi) (congrArg Prod.snd he)
  cases a
  cases b
  dsimp only at hp hc
  cases hp
  cases hc
  rfl

/-- Measurability of the complete decoder state code, retaining pending
batches that can straddle launch. -/
theorem measurable_replay_downBatchCode (p : Parameters) {n : ℕ} (eta : LearningRate)
    (i : Fin (p.m - 1)) (alpha : Activation p) (hist : LocalHistory p n) (hn : n ≤ p.T) :
    Measurable (fun row : CompleteRow p => downBatchCode (replay eta i row alpha hist hn).downBatch) := by
  apply measurable_of_countable_key (ordinaryRowCode p i) (measurable_ordinaryRowCode p i)
  intro row row' he
  exact congrArg downBatchCode (replay_run_down_eq eta i row row' alpha hist hn _ he
    (ReferencePrelaunchFollower.initial p eta) (ReferencePrelaunchFollower.initial p eta)
    rfl rfl rfl).1

theorem measurable_ordinary_downBatchCode (p : Parameters) (C_star C_h : ℝ)
    (eta : LearningRate) (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
    (r : ℕ) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      let x := inputOfCoordinates p C_star C_h eta rewards z
      downBatchCode (ordinary x (ReferenceInitializationRun.run x r) i).downBatch) := by
  apply measurable_by_countable_cases
    (fun z : InputCoordinates p =>
      ReferenceInitializationRun.run (inputOfCoordinates p C_star C_h eta rewards z) r)
    (measurable_run p C_star C_h eta rewards r)
    (fun b z => downBatchCode (ordinary (inputOfCoordinates p C_star C_h eta rewards z) b i).downBatch)
  intro b
  unfold ordinary
  split_ifs
  · change Measurable (fun _ : InputCoordinates p => downBatchCode (AffineBatchDecoder.initial p))
    exact measurable_const
  · cases ha : b.activation i with
    | none =>
      change Measurable (fun _ : InputCoordinates p => downBatchCode (AffineBatchDecoder.initial p))
      exact measurable_const
    | some a =>
      exact (measurable_replay_downBatchCode p eta (BootstrapPhysicalInput.sourceFollowerIndex p i)
        a (b.history (followerPlayer p.two_le_m i)) (elapsed_le_T p b.completed)).comp
          (measurable_fst.comp measurable_snd)

open SparseCalendarReplay

/-- A product encoding of one logged record, including the continuous saved
thinning scalar. The sum's left branch means no record at this calendar time. -/
abbrev LoggingCode (p : Parameters) :=
  Unit ⊕ (ℕ × Fin p.K × SparseCalendarReward × SparseCalendarThinScalar)

def loggingEntryCode {p : Parameters} (i : Fin (p.m - 1)) (row : CompleteRow p)
    (a : Activation p) (t : Fin p.T) (own : Fin p.K × Observation p) : LoggingCode p :=
  if loggingTestsPass (loggingRound i row a t own) then
    Sum.inr (t.val + 1, own.1, own.2.val, (row.2 t).1 ContinuousControlSlice.Label.thin)
  else Sum.inl ()

def decodeLoggingCode {p : Parameters} : LoggingCode p → List (SparseCalendarRecord p.K)
  | Sum.inl _ => []
  | Sum.inr v => [⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩]

theorem decode_loggingEntryCode {p : Parameters} (i : Fin (p.m - 1)) (row : CompleteRow p)
    (a : Activation p) (t : Fin p.T) (own : Fin p.K × Observation p) :
    decodeLoggingCode (loggingEntryCode i row a t own) = logAt i row a t own := by
  unfold loggingEntryCode logAt
  split_ifs <;> rfl

theorem measurable_loggingEntryCode {p : Parameters} (i : Fin (p.m - 1))
    (a : Activation p) (t : Fin p.T) (own : Fin p.K × Observation p) :
    Measurable (fun row : CompleteRow p => loggingEntryCode i row a t own) := by
  have hs : Measurable (fun row : CompleteRow p => (row.2 t).1) :=
    measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)
  have hpilots : Measurable (fun row : CompleteRow p => fun j : Fin (p.m - 1) =>
      pilotDraw (K_pos p) (otherPlayer p i j) (row.2 t).1) :=
    measurable_pi_iff.mpr fun j => (measurable_pilotDraw (K_pos p) (otherPlayer p i j)).comp hs
  let test := fun v : Slot × Fin p.m × (Fin (p.m - 1) → Fin p.K) =>
    decide (a.val ≤ t.val + 1 ∧ v.1 = dataSlot ∧ v.2.1 = followerPlayer p.two_le_m i ∧
      ∀ j, v.2.2 j ≠ own.1)
  have hm := (measurable_of_countable test).comp
    ((measurable_slotDraw.comp hs).prodMk
      (((measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp hs).prodMk hpilots))
  have hp : MeasurableSet {row : CompleteRow p | loggingTestsPass (loggingRound i row a t own)} := by
    have he : {row : CompleteRow p | loggingTestsPass (loggingRound i row a t own)} =
        {row | test (slotDraw (row.2 t).1,
          recorderSourceDraw p.two_le_m p.m_lt_K (row.2 t).1,
          fun j => pilotDraw (K_pos p) (otherPlayer p i j) (row.2 t).1) = true} := by
      ext row
      simp only [test, loggingTestsPass, loggingRound, sourceMaskPasses,
        decide_eq_true_eq, true_and]
    rw [he]
    exact measurableSet_eq_fun hm measurable_const
  exact Measurable.ite hp (measurable_inr.comp
    (measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk
      ((measurable_pi_apply ContinuousControlSlice.Label.thin).comp hs))))) measurable_const

/-- Calendar-indexed ordinary logging from the ACTUAL physical prefix. DATA
records retain exact observations and continuous thins; no buffer is discrete. -/
def ordinaryLogging (p : Parameters) (x : Input p) (b : Boundary p) (i : Follower p.m) :
    Fin p.T → LoggingCode p := fun t =>
  if b.forcedFailure i then Sum.inl () else
    match b.activation i with
    | none => Sum.inl ()
    | some a => if ht : t.val < elapsed p b.completed then
        loggingEntryCode (BootstrapPhysicalInput.sourceFollowerIndex p i) x.row a t
          (b.history (followerPlayer p.two_le_m i) ⟨t.val, ht⟩)
      else Sum.inl ()

/-- Reconstruct exactly the accepted replay buffer, in chronological order.
Earlier DATA records are carried and unused thins are retained verbatim. -/
theorem ordinaryLogging_buffer (p : Parameters) (x : Input p) (b : Boundary p) (i : Follower p.m) :
    (ordinary x b i).buffer = (List.ofFn (fun u : Fin (elapsed p b.completed) => u)).flatMap
      (fun u => decodeLoggingCode (ordinaryLogging p x b i
        ⟨u.val, Nat.lt_of_lt_of_le u.isLt (elapsed_le_T p b.completed)⟩)) := by
  unfold ordinary ordinaryLogging
  split_ifs with hf
  · simp only [forcedAtLaunch, ReferencePrelaunchFollower.initial, decodeLoggingCode]
    exact (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)).symm
  · cases ha : b.activation i with
    | none =>
      simp only [ReferencePrelaunchFollower.initial, decodeLoggingCode]
      exact (List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)).symm
    | some a =>
      simp only [atLaunch, replay_buffer]
      apply List.flatMap_congr
      intro u hu
      rw [dite_eq_left u.isLt, decode_loggingEntryCode]
      rfl

theorem measurable_ordinaryLogging (p : Parameters) (C_star C_h : ℝ) (eta : LearningRate)
    (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (r : ℕ) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      let x := inputOfCoordinates p C_star C_h eta rewards z
      ordinaryLogging p x (ReferenceInitializationRun.run x r) i) := by
  apply measurable_by_countable_cases
    (fun z : InputCoordinates p =>
      ReferenceInitializationRun.run (inputOfCoordinates p C_star C_h eta rewards z) r)
    (measurable_run p C_star C_h eta rewards r)
    (fun b z => ordinaryLogging p (inputOfCoordinates p C_star C_h eta rewards z) b i)
  intro b
  apply measurable_pi_iff.mpr
  intro t
  by_cases hf : b.forcedFailure i = true
  · simp only [ordinaryLogging, hf, ite_true]
    exact measurable_const
  · simp only [ordinaryLogging, ite_eq_right hf]
    cases ha : b.activation i with
    | none => exact measurable_const
    | some a =>
      by_cases ht : t.val < elapsed p b.completed
      · simp only [ht, dite_true]
        exact (measurable_loggingEntryCode _ a t _).comp (measurable_fst.comp measurable_snd)
      · simp only [ht, dite_false]
        exact measurable_const

theorem measurable_output_downBatchCode (p : Parameters) (C_star C_h : ℝ)
    (eta : LearningRate) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      let x := inputOfCoordinates p C_star C_h eta rewards z
      downBatchCode (ordinary x (output x) i).downBatch) :=
  measurable_ordinary_downBatchCode p C_star C_h eta rewards (n_boot p) i

theorem measurable_output_ordinaryLogging (p : Parameters) (C_star C_h : ℝ)
    (eta : LearningRate) (rewards : Fin p.T → Fin p.K → Fin (D p + 1)) (i : Follower p.m) :
    Measurable (fun z : InputCoordinates p =>
      let x := inputOfCoordinates p C_star C_h eta rewards z
      ordinaryLogging p x (output x) i) :=
  measurable_ordinaryLogging p C_star C_h eta rewards (n_boot p) i

end Bandits.Support.ReferenceInitializationMeasurability

end
