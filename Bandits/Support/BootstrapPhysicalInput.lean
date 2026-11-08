/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.PrivateSourceStreams
public import Bandits.Support.BootstrapPrivateRoundStreams

/-!
# Deterministic input adapter for one physical bootstrap block

The adapter maps the already-labelled private block, round, and coordinator
target scalars to the existing `BootstrapPhysicalBlock.Input`. Its incoming
uninformed set, numerator vectors, ID array, complete row, and rounded reward
matrix are explicit finite boundary data. In particular, this file does not
construct a boundary history, a second private carrier, or a physical run.

The block activity, held-arm, and private-ID values are the accepted
`PrivateSourceStreams.blockDrawProfileMap` on the current block's existing
triples. A player's round scalar is reused for its full-arm and forbidden-arm
alternatives, and the coordinator target scalar is reused for its target and
DATA-avoidance alternatives. No joint law between those alternatives is
asserted here.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,61-92` and
`sources/zip4/manuscript/appendix_b_communication.tex:107,138-146,308-314`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapPhysicalBlock

namespace Bandits.Support.BootstrapPhysicalInput

/-- The accepted block sampler indexes followers by `Fin (m - 1)`, while the
physical action module names the same carrier through `followerCount m`. -/
def sourceFollowerIndex (p : Parameters) (j : Follower p.m) : Fin (p.m - 1) :=
  ⟨j.val, by simpa only [PublicDiscreteDraws.followerCount] using j.isLt⟩

/-- The exact fixed-block draw profile supplied by the accepted private
source-stream sampler. Only its entries indexed by the incoming uninformed
set are installed in the physical block input. -/
def currentBlockDrawProfile (p : Parameters) (s : Fin (n_boot p))
    (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
    (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
      (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
    (coordinates : ExtendedPrivateCoordinates p) : BlockDrawProfile p :=
  PrivateSourceStreams.blockDrawProfileMap p numerators hpos (coordinates.1.1 s)

/-- The one player's existing round scalar, projected by its player-round
label. -/
def playerRoundScalarAt (p : Parameters)
    (coordinates : ExtendedPrivateCoordinates p) (i : Player p.m) (t : Fin p.T) :
    BootstrapPrivateRoundStreams.Scalar :=
  coordinates.2.1 (i, t)

/-- The existing target scalar for this calendar block. -/
def coordinatorTargetScalarAt (p : Parameters)
    (s : Fin (n_boot p)) (coordinates : ExtendedPrivateCoordinates p) :
    BootstrapPrivateRoundStreams.Scalar :=
  coordinates.2.2 s

variable (p : Parameters) (s : Fin (n_boot p))
  (incoming : Finset (Follower p.m))
  (numerators : Fin (p.m - 1) → Fin p.K → ℕ)
  (hpos : ∀ (j : Fin (p.m - 1)) (a : Fin p.K),
    (1 : ℝ) ≤ BootstrapWeightPotential.weight (b_N p) (numerators j) a)
  (ids : CompletePublicTable.IDArray p)
  (row : CompletePublicTable.CompleteRow p)
  (rewards : Fin p.T → Fin p.K → Fin (D p + 1))

/-- Current block draws, projected from the accepted scalar triples and
parameterized by the explicit incoming weight state. -/
def currentBlockDrawProfileMap : ExtendedPrivateCoordinates p →
    BlockDrawProfile p :=
  currentBlockDrawProfile p s numerators hpos

/-- Activity values on exactly the incoming uninformed follower subtype. -/
def activityMap (coordinates : ExtendedPrivateCoordinates p) :
    {j // j ∈ incoming} → Bool := fun j =>
  (currentBlockDrawProfileMap p s numerators hpos coordinates
    (sourceFollowerIndex p j.1)).1

/-- Held-arm values on exactly the incoming uninformed follower subtype. -/
def heldMap (coordinates : ExtendedPrivateCoordinates p) :
    {j // j ∈ incoming} → Fin p.K := fun j =>
  ((currentBlockDrawProfileMap p s numerators hpos coordinates
    (sourceFollowerIndex p j.1)).2).1

/-- Private-ID values on exactly the incoming uninformed follower subtype. -/
def privateIDMap (coordinates : ExtendedPrivateCoordinates p) :
    {j // j ∈ incoming} → Fin (A_id p) := fun j =>
  ((currentBlockDrawProfileMap p s numerators hpos coordinates
    (sourceFollowerIndex p j.1)).2).2

/-- The coordinator's target from the already-labelled target scalar. -/
def targetArmMap (coordinates : ExtendedPrivateCoordinates p) : Fin p.K :=
  coordinatorTargetDraw p (coordinatorTargetScalarAt p s coordinates)

/-- Full-arm values, using each player's same round scalar for every
full-arm branch in that round. -/
def uniformArmMap (coordinates : ExtendedPrivateCoordinates p) :
    Player p.m → Fin p.T → Fin p.K := fun i t =>
  fullArmScalarDraw p (playerRoundScalarAt p coordinates i t)

/-- The value of the coordinator's forbidden-arm alternative, using the same
target scalar for its current target and the same round scalar as its full-arm
alternative. -/
def coordinatorAvoidArmValueMap (coordinates : ExtendedPrivateCoordinates p) :
    Fin p.T → Fin p.K := fun t =>
  (forbiddenArmScalarDraw p (targetArmMap p s coordinates)
    (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t)).val

/-- Values of the follower's forbidden-arm alternatives, using the held arm
from its accepted block triple and the same scalar as its full-arm alternative. -/
def followerAvoidArmValueMap (coordinates : ExtendedPrivateCoordinates p) :
    (j : {j // j ∈ incoming}) → Fin p.T → Fin p.K := fun j t =>
  (forbiddenArmScalarDraw p (heldMap p s incoming numerators hpos coordinates j)
    (playerRoundScalarAt p coordinates
      (followerPlayer p.two_le_m j.1) t)).val

/-- Deterministic map from existing labelled private scalars to the existing
physical block input. -/
def blockInput (coordinates : ExtendedPrivateCoordinates p) :
    BootstrapPhysicalBlock.Input p s where
  uninformed := incoming
  active := activityMap p s incoming numerators hpos coordinates
  held := heldMap p s incoming numerators hpos coordinates
  privateId := privateIDMap p s incoming numerators hpos coordinates
  ids := ids
  row := row
  target := targetArmMap p s coordinates
  uniform := uniformArmMap p coordinates
  coordinatorAvoid := fun t => forbiddenArmScalarDraw p
    (targetArmMap p s coordinates)
    (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t)
  followerAvoid := fun j t => forbiddenArmScalarDraw p
    (heldMap p s incoming numerators hpos coordinates j)
    (playerRoundScalarAt p coordinates (followerPlayer p.two_le_m j.1) t)
  rewards := rewards

theorem blockInput_uninformed (coordinates : ExtendedPrivateCoordinates p) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).uninformed = incoming := rfl

theorem blockInput_active (coordinates : ExtendedPrivateCoordinates p)
    (j : {j // j ∈ incoming}) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).active j =
      (currentBlockDrawProfile p s numerators hpos coordinates
        (sourceFollowerIndex p j.1)).1 := rfl

theorem blockInput_held (coordinates : ExtendedPrivateCoordinates p)
    (j : {j // j ∈ incoming}) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).held j =
      ((currentBlockDrawProfile p s numerators hpos coordinates
        (sourceFollowerIndex p j.1)).2).1 := rfl

theorem blockInput_privateID (coordinates : ExtendedPrivateCoordinates p)
    (j : {j // j ∈ incoming}) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).privateId j =
      ((currentBlockDrawProfile p s numerators hpos coordinates
        (sourceFollowerIndex p j.1)).2).2 := rfl

theorem blockInput_ids (coordinates : ExtendedPrivateCoordinates p) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).ids = ids := rfl

theorem blockInput_row (coordinates : ExtendedPrivateCoordinates p) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).row = row := rfl

theorem blockInput_target (coordinates : ExtendedPrivateCoordinates p) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).target =
      coordinatorTargetDraw p (coordinatorTargetScalarAt p s coordinates) := rfl

theorem blockInput_uniform (coordinates : ExtendedPrivateCoordinates p)
    (i : Player p.m) (t : Fin p.T) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).uniform i t =
      fullArmScalarDraw p (playerRoundScalarAt p coordinates i t) := rfl

theorem blockInput_coordinatorAvoid (coordinates : ExtendedPrivateCoordinates p)
    (t : Fin p.T) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).coordinatorAvoid t =
      forbiddenArmScalarDraw p
        (coordinatorTargetDraw p (coordinatorTargetScalarAt p s coordinates))
        (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t) := rfl

theorem blockInput_followerAvoid (coordinates : ExtendedPrivateCoordinates p)
    (j : {j // j ∈ incoming}) (t : Fin p.T) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).followerAvoid j t =
      forbiddenArmScalarDraw p
        (((currentBlockDrawProfile p s numerators hpos coordinates
          (sourceFollowerIndex p j.1)).2).1)
        (playerRoundScalarAt p coordinates (followerPlayer p.two_le_m j.1) t) := rfl

theorem blockInput_rewards (coordinates : ExtendedPrivateCoordinates p) :
    (blockInput p s incoming numerators hpos ids row rewards coordinates).rewards = rewards := rfl

/-- Each incoming follower's three block fields are exactly the corresponding
entry of the accepted profile map on the current block's actual scalar triple.
The profile is independent of the row and all round coordinates. -/
theorem incoming_blockDraw_eq_accepted_map (coordinates : ExtendedPrivateCoordinates p)
    (j : {j // j ∈ incoming}) :
    ((blockInput p s incoming numerators hpos ids row rewards coordinates).active j,
      (blockInput p s incoming numerators hpos ids row rewards coordinates).held j,
      (blockInput p s incoming numerators hpos ids row rewards coordinates).privateId j) =
      PrivateSourceStreams.blockDrawProfileMap p numerators hpos (coordinates.1.1 s)
        (sourceFollowerIndex p j.1) := rfl

/-- If this follower's own labelled block triple agrees, its complete accepted
activity/held-arm/private-ID draw agrees, regardless of other followers'
triples. -/
theorem incoming_blockDraw_eq_of_own_triple_eq
    (x y : ExtendedPrivateCoordinates p) (j : {j // j ∈ incoming})
    (htriple : x.1.1 s (sourceFollowerIndex p j.1) =
      y.1.1 s (sourceFollowerIndex p j.1)) :
    currentBlockDrawProfile p s numerators hpos x (sourceFollowerIndex p j.1) =
      currentBlockDrawProfile p s numerators hpos y (sourceFollowerIndex p j.1) := by
  simp only [currentBlockDrawProfile, PrivateSourceStreams.blockDrawProfileMap,
    PrivateSourceStreams.privateBlockDrawMap, htriple]

/-- The target is unchanged when its one existing block scalar is unchanged. -/
theorem targetArmMap_eq_of_target_scalar_eq
    (x y : ExtendedPrivateCoordinates p)
    (hscalar : coordinatorTargetScalarAt p s x = coordinatorTargetScalarAt p s y) :
    targetArmMap p s x =
      targetArmMap p s y := by
  simp only [targetArmMap, hscalar]

/-- A follower's own uniform and avoidance-arm values are unchanged when its
single player-round scalar and incoming held arm agree. -/
theorem follower_roundDraws_eq_of_own_coordinates_eq
    (x y : ExtendedPrivateCoordinates p) (j : {j // j ∈ incoming}) (t : Fin p.T)
    (htriple : x.1.1 s (sourceFollowerIndex p j.1) =
      y.1.1 s (sourceFollowerIndex p j.1))
    (hround : playerRoundScalarAt p x (followerPlayer p.two_le_m j.1) t =
      playerRoundScalarAt p y (followerPlayer p.two_le_m j.1) t) :
    (uniformArmMap p x
        (followerPlayer p.two_le_m j.1) t =
      uniformArmMap p y
        (followerPlayer p.two_le_m j.1) t) ∧
    (followerAvoidArmValueMap p s incoming numerators hpos x j t =
      followerAvoidArmValueMap p s incoming numerators hpos y j t) := by
  have hdraw := incoming_blockDraw_eq_of_own_triple_eq p s incoming numerators hpos
    x y j htriple
  have hheld : heldMap p s incoming numerators hpos x j =
      heldMap p s incoming numerators hpos y j :=
    congrArg (fun d : BlockDraw p => d.2.1) hdraw
  constructor
  · change fullArmScalarDraw p (playerRoundScalarAt p x (followerPlayer p.two_le_m j.1) t) =
      fullArmScalarDraw p (playerRoundScalarAt p y (followerPlayer p.two_le_m j.1) t)
    exact congrArg (fullArmScalarDraw p) hround
  · change (forbiddenArmScalarDraw p (heldMap p s incoming numerators hpos x j)
      (playerRoundScalarAt p x (followerPlayer p.two_le_m j.1) t)).val =
      (forbiddenArmScalarDraw p (heldMap p s incoming numerators hpos y j)
        (playerRoundScalarAt p y (followerPlayer p.two_le_m j.1) t)).val
    rw [hheld, hround]

/-- A coordinator's target and both round-draw alternatives are unchanged
when its target scalar and this round's coordinator scalar agree. -/
theorem coordinator_roundDraws_eq_of_own_coordinates_eq
    (x y : ExtendedPrivateCoordinates p) (t : Fin p.T)
    (htarget : coordinatorTargetScalarAt p s x = coordinatorTargetScalarAt p s y)
    (hround : playerRoundScalarAt p x (coordinator p.two_le_m) t =
      playerRoundScalarAt p y (coordinator p.two_le_m) t) :
    (targetArmMap p s x =
      targetArmMap p s y) ∧
    (uniformArmMap p x
        (coordinator p.two_le_m) t =
      uniformArmMap p y
        (coordinator p.two_le_m) t) ∧
    (coordinatorAvoidArmValueMap p s x t =
      coordinatorAvoidArmValueMap p s y t) := by
  have htargetArm := targetArmMap_eq_of_target_scalar_eq p s x y htarget
  refine ⟨htargetArm, ?_, ?_⟩
  · change fullArmScalarDraw p (playerRoundScalarAt p x (coordinator p.two_le_m) t) =
      fullArmScalarDraw p (playerRoundScalarAt p y (coordinator p.two_le_m) t)
    exact congrArg (fullArmScalarDraw p) hround
  · change (forbiddenArmScalarDraw p (targetArmMap p s x)
      (playerRoundScalarAt p x (coordinator p.two_le_m) t)).val =
      (forbiddenArmScalarDraw p (targetArmMap p s y)
        (playerRoundScalarAt p y (coordinator p.two_le_m) t)).val
    rw [htargetArm, hround]

/-- Measurability of the current-block scalar-triple projection followed by
the accepted fixed-state sampler. -/
theorem measurable_currentBlockDrawProfileMap :
    Measurable (currentBlockDrawProfileMap p s numerators hpos) := by
  exact (PrivateSourceStreams.measurable_blockDrawProfileMap p numerators hpos).comp
    ((measurable_pi_apply s).comp (measurable_fst.comp measurable_fst))

theorem measurable_activityMap : Measurable
    (activityMap p s incoming numerators hpos) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun coordinates =>
    (currentBlockDrawProfileMap p s numerators hpos coordinates
      (sourceFollowerIndex p j.1)).1)
  exact measurable_fst.comp
    ((measurable_pi_apply j.1).comp
      (measurable_currentBlockDrawProfileMap p s numerators hpos))

theorem measurable_heldMap : Measurable
    (heldMap p s incoming numerators hpos) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun coordinates =>
    ((currentBlockDrawProfileMap p s numerators hpos coordinates
      (sourceFollowerIndex p j.1)).2).1)
  exact (measurable_fst.comp measurable_snd).comp
    ((measurable_pi_apply j.1).comp
      (measurable_currentBlockDrawProfileMap p s numerators hpos))

theorem measurable_privateIDMap : Measurable
    (privateIDMap p s incoming numerators hpos) := by
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun coordinates =>
    ((currentBlockDrawProfileMap p s numerators hpos coordinates
      (sourceFollowerIndex p j.1)).2).2)
  exact (measurable_snd.comp measurable_snd).comp
    ((measurable_pi_apply j.1).comp
      (measurable_currentBlockDrawProfileMap p s numerators hpos))

theorem measurable_fixedIDs :
    Measurable (fun _ : ExtendedPrivateCoordinates p => ids) := measurable_const

theorem measurable_fixedRow :
    Measurable (fun _ : ExtendedPrivateCoordinates p => row) := measurable_const

theorem measurable_fixedRewards :
    Measurable (fun _ : ExtendedPrivateCoordinates p => rewards) := measurable_const

theorem measurable_playerRoundScalarAt (i : Player p.m) (t : Fin p.T) :
    Measurable (fun coordinates => playerRoundScalarAt p coordinates i t) :=
  (measurable_pi_apply (i, t)).comp (measurable_fst.comp measurable_snd)

theorem measurable_coordinatorTargetScalarAt :
    Measurable (coordinatorTargetScalarAt p s) :=
  (measurable_pi_apply s).comp (measurable_snd.comp measurable_snd)

theorem measurable_targetArmMap :
    Measurable (targetArmMap p s) :=
  (measurable_fullArmScalarDraw p).comp (measurable_coordinatorTargetScalarAt p s)

theorem measurable_uniformArmMap : Measurable
    (uniformArmMap p) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro t
  exact (measurable_fullArmScalarDraw p).comp
    (measurable_playerRoundScalarAt p i t)

theorem measurable_coordinatorAvoidArmValueMap_at (t : Fin p.T) :
    Measurable (fun coordinates =>
      coordinatorAvoidArmValueMap p s coordinates t) := by
  classical
  apply measurable_to_countable'
  intro b
  have hpreimage :
      {coordinates : ExtendedPrivateCoordinates p |
        coordinatorAvoidArmValueMap p s coordinates t = b} =
      ⋃ a : Fin p.K,
        {coordinates : ExtendedPrivateCoordinates p | targetArmMap p s coordinates = a} ∩
        {coordinates : ExtendedPrivateCoordinates p |
          (forbiddenArmScalarDraw p a (playerRoundScalarAt p coordinates
            (coordinator p.two_le_m) t)).val = b} := by
    ext coordinates
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hb
      exact ⟨targetArmMap p s coordinates, rfl, hb⟩
    · rintro ⟨a, ha, hb⟩
      change (forbiddenArmScalarDraw p
        (targetArmMap p s coordinates)
        (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t)).val = b
      rw [ha]
      exact hb
  change MeasurableSet {coordinates : ExtendedPrivateCoordinates p |
    coordinatorAvoidArmValueMap p s coordinates t = b}
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro a
  apply (measurableSet_eq_fun
      (measurable_targetArmMap p s)
      measurable_const).inter
  change MeasurableSet ((fun coordinates : ExtendedPrivateCoordinates p =>
    (forbiddenArmScalarDraw p a
      (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t)).val) ⁻¹' {b})
  exact ((measurable_subtype_coe.comp
    (measurable_forbiddenArmScalarDraw p a)).comp
      (measurable_playerRoundScalarAt p (coordinator p.two_le_m) t))
    (measurableSet_singleton b)

theorem measurable_coordinatorAvoidArmValueMap : Measurable
    (coordinatorAvoidArmValueMap p s) := by
  apply measurable_pi_iff.mpr
  intro t
  exact measurable_coordinatorAvoidArmValueMap_at p s t

theorem measurable_followerAvoidArmValueMap_at
    (j : {j // j ∈ incoming}) (t : Fin p.T) :
    Measurable (fun coordinates =>
      followerAvoidArmValueMap p s incoming numerators hpos coordinates j t) := by
  classical
  apply measurable_to_countable'
  intro b
  have hpreimage :
      {coordinates : ExtendedPrivateCoordinates p |
        followerAvoidArmValueMap p s incoming numerators hpos coordinates j t = b} =
      ⋃ a : Fin p.K,
        {coordinates : ExtendedPrivateCoordinates p |
          heldMap p s incoming numerators hpos coordinates j = a} ∩
        {coordinates : ExtendedPrivateCoordinates p |
          (forbiddenArmScalarDraw p a (playerRoundScalarAt p coordinates
            (followerPlayer p.two_le_m j.1) t)).val = b} := by
    ext coordinates
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hb
      exact ⟨heldMap p s incoming numerators hpos coordinates j, rfl, hb⟩
    · rintro ⟨a, ha, hb⟩
      change (forbiddenArmScalarDraw p
        (heldMap p s incoming numerators hpos coordinates j)
        (playerRoundScalarAt p coordinates (followerPlayer p.two_le_m j.1) t)).val = b
      rw [ha]
      exact hb
  change MeasurableSet {coordinates : ExtendedPrivateCoordinates p |
    followerAvoidArmValueMap p s incoming numerators hpos coordinates j t = b}
  rw [hpreimage]
  apply MeasurableSet.iUnion
  intro a
  have hheld : Measurable (fun coordinates : ExtendedPrivateCoordinates p =>
      heldMap p s incoming numerators hpos coordinates j) :=
    (measurable_pi_apply j).comp (measurable_heldMap p s incoming numerators hpos)
  apply (measurableSet_eq_fun hheld measurable_const).inter
  change MeasurableSet ((fun coordinates : ExtendedPrivateCoordinates p =>
    (forbiddenArmScalarDraw p a
      (playerRoundScalarAt p coordinates (followerPlayer p.two_le_m j.1) t)).val) ⁻¹' {b})
  exact ((measurable_subtype_coe.comp
    (measurable_forbiddenArmScalarDraw p a)).comp
      (measurable_playerRoundScalarAt p (followerPlayer p.two_le_m j.1) t))
    (measurableSet_singleton b)

theorem measurable_followerAvoidArmValueMap : Measurable
    (followerAvoidArmValueMap p s incoming numerators hpos) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro t
  exact measurable_followerAvoidArmValueMap_at p s incoming numerators hpos j t

/-- The accepted full-source coordinates projection is the only composition used
to present this adapter to a later causality producer. The bundled physical
input itself is not assigned a measurable space. -/
def sourceExtendedPrivateCoordinates
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    ExtendedPrivateCoordinates p := source.2

theorem measurable_sourceExtendedPrivateCoordinates :
    Measurable (sourceExtendedPrivateCoordinates p) := measurable_snd

def sourceBlockInput (source : BootstrapPrivateRoundStreams.SourceInput p) :
    BootstrapPhysicalBlock.Input p s :=
  blockInput p s incoming numerators hpos ids row rewards
    (sourceExtendedPrivateCoordinates p source)

theorem sourceBlockInput_privateProjection (source : BootstrapPrivateRoundStreams.SourceInput p) :
    sourceBlockInput p s incoming numerators hpos ids row rewards source =
      blockInput p s incoming numerators hpos ids row rewards source.2 := rfl

theorem measurable_sourceActivityMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      activityMap p s incoming numerators hpos source.2) :=
  (measurable_activityMap p s incoming numerators hpos).comp measurable_snd

theorem measurable_sourceHeldMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      heldMap p s incoming numerators hpos source.2) :=
  (measurable_heldMap p s incoming numerators hpos).comp measurable_snd

theorem measurable_sourcePrivateIDMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      privateIDMap p s incoming numerators hpos source.2) :=
  (measurable_privateIDMap p s incoming numerators hpos).comp measurable_snd

theorem measurable_sourceTargetArmMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      targetArmMap p s source.2) :=
  (measurable_targetArmMap p s).comp measurable_snd

theorem measurable_sourceUniformArmMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      uniformArmMap p source.2) :=
  (measurable_uniformArmMap p).comp measurable_snd

theorem measurable_sourceCoordinatorAvoidArmValueMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      coordinatorAvoidArmValueMap p s source.2) :=
  (measurable_coordinatorAvoidArmValueMap p s).comp
    measurable_snd

theorem measurable_sourceFollowerAvoidArmValueMap : Measurable
    (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
      followerAvoidArmValueMap p s incoming numerators hpos source.2) :=
  (measurable_followerAvoidArmValueMap p s incoming numerators hpos).comp
    measurable_snd

/-- Physical coordinator actions reduce to the existing coordinator formula. -/
theorem actions_coordinator (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (coordinator p.two_le_m) =
    BootstrapPhysicalBlock.coordinatorAction
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t :=
  BootstrapPhysicalBlock.actions_coordinator _ _ _

theorem actions_coordinator_discover_data (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (hm : st.mode = .discover)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = dataSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (coordinator p.two_le_m) =
      coordinatorTargetDraw p (coordinatorTargetScalarAt p s coordinates) := by
  rw [actions_coordinator]
  exact BootstrapPhysicalBlock.coordinatorAction_discover_data _ _ _ hm ht

theorem actions_coordinator_multicast_data (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (hm : st.mode = .multicast)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = dataSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (coordinator p.two_le_m) =
      if BootstrapPhysicalBlock.forwardProduct
          (blockInput p s incoming numerators hpos ids row rewards coordinates) st t = 1 then
        (forbiddenArmScalarDraw p
          (coordinatorTargetDraw p (coordinatorTargetScalarAt p s coordinates))
          (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t)).val
      else coordinatorTargetDraw p (coordinatorTargetScalarAt p s coordinates) := by
  rw [actions_coordinator, BootstrapPhysicalBlock.coordinatorAction_multicast_data _ _ _ hm ht]
  rfl

theorem actions_coordinator_down (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = downSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (coordinator p.two_le_m) =
      (BootstrapPhysicalBlock.tuple
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t).val
        (coordinator p.two_le_m) := by
  rw [actions_coordinator]
  exact BootstrapPhysicalBlock.coordinatorAction_down _ _ _ ht

theorem actions_coordinator_up (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = upSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (coordinator p.two_le_m) =
      fullArmScalarDraw p (playerRoundScalarAt p coordinates (coordinator p.two_le_m) t) := by
  rw [actions_coordinator]
  exact BootstrapPhysicalBlock.coordinatorAction_up _ _ _ ht

/-- The existing follower action specializes to its uninformed branch on the
incoming subtype. -/
theorem followerAction_eq_uninformed (coordinates : ExtendedPrivateCoordinates p)
    (t : Fin p.T) (j : {j // j ∈ incoming}) :
    BootstrapPhysicalBlock.followerAction
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t j.1 =
      BootstrapPhysicalBlock.uninformedAction
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t j := by
  change (if hj : j.1 ∈ incoming then
      BootstrapPhysicalBlock.uninformedAction
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t ⟨j.1, hj⟩
    else BootstrapPhysicalBlock.unoccupiedAction
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t j.1) = _
  exact dite_eq_left j.2

/-- The existing follower action specializes to its unoccupied branch outside
the incoming uninformed set. -/
theorem followerAction_eq_unoccupied (coordinates : ExtendedPrivateCoordinates p)
    (t : Fin p.T) (j : Follower p.m) (hnot : j ∉ incoming) :
    BootstrapPhysicalBlock.followerAction
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t j =
      BootstrapPhysicalBlock.unoccupiedAction
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t j := by
  change (if hj : j ∈ incoming then
      BootstrapPhysicalBlock.uninformedAction
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t ⟨j, hj⟩
    else BootstrapPhysicalBlock.unoccupiedAction
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t j) = _
  exact dite_eq_right hnot

/-- Uninformed follower action equations inherit the existing physical
formula and reuse one round scalar in the mutually exclusive alternatives. -/
theorem actions_incoming_stay (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ incoming}) (ha :
      (blockInput p s incoming numerators hpos ids row rewards coordinates).active j = true)
    (hid : ids ((blockInput p s incoming numerators hpos ids row rewards coordinates).privateId j) t = false) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m j.1) =
      ((currentBlockDrawProfile p s numerators hpos coordinates
        (sourceFollowerIndex p j.1)).2).1 := by
  rw [BootstrapPhysicalBlock.actions_follower, followerAction_eq_uninformed]
  exact BootstrapPhysicalBlock.uninformedAction_stay _ _ _ ha hid

theorem actions_incoming_avoid (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ incoming}) (ha :
      (blockInput p s incoming numerators hpos ids row rewards coordinates).active j = true)
    (hid : ids ((blockInput p s incoming numerators hpos ids row rewards coordinates).privateId j) t = true) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m j.1) =
      (forbiddenArmScalarDraw p
        (((currentBlockDrawProfile p s numerators hpos coordinates
          (sourceFollowerIndex p j.1)).2).1)
        (playerRoundScalarAt p coordinates (followerPlayer p.two_le_m j.1) t)).val := by
  rw [BootstrapPhysicalBlock.actions_follower, followerAction_eq_uninformed]
  have hid' := hid
  rw [blockInput_privateID] at hid'
  simp only [BootstrapPhysicalBlock.uninformedAction, ha, blockInput_ids,
    blockInput_privateID, hid']
  rw [blockInput_followerAvoid]
  rfl

theorem actions_incoming_inactive (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : {j // j ∈ incoming}) (ha :
      (blockInput p s incoming numerators hpos ids row rewards coordinates).active j = false) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m j.1) =
      fullArmScalarDraw p (playerRoundScalarAt p coordinates (followerPlayer p.two_le_m j.1) t) := by
  rw [BootstrapPhysicalBlock.actions_follower, followerAction_eq_uninformed]
  exact BootstrapPhysicalBlock.uninformedAction_inactive _ _ _ ha

/-- Informed followers retain the accepted true-row DATA, DOWN, and UP
formulas. Their behavior uses no block activity/held/ID coordinates. -/
theorem actions_informed_data (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : Follower p.m) (hnot : j ∉ incoming)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = dataSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m j) =
      BootstrapPhysicalBlock.pilot
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t
        (followerPlayer p.two_le_m j) := by
  rw [BootstrapPhysicalBlock.actions_follower,
    followerAction_eq_unoccupied p s incoming numerators hpos ids row rewards coordinates t j hnot]
  simp [BootstrapPhysicalBlock.unoccupiedAction, ht]

theorem actions_informed_down (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : Follower p.m) (hnot : j ∉ incoming)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = downSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m j) =
      (BootstrapPhysicalBlock.tuple
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t).val
        (followerPlayer p.two_le_m j) := by
  rw [BootstrapPhysicalBlock.actions_follower,
    followerAction_eq_unoccupied p s incoming numerators hpos ids row rewards coordinates t j hnot]
  exact BootstrapPhysicalBlock.unoccupiedAction_down _ _ _ ht

theorem actions_informed_selected_up (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (hnot : BootstrapPhysicalBlock.selected
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t ∉ incoming)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = upSlot) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m (BootstrapPhysicalBlock.selected
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t)) =
      sendArm (BootstrapPhysicalBlock.initialUpBit
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t
        (BootstrapPhysicalBlock.selected
          (blockInput p s incoming numerators hpos ids row rewards coordinates) t))
        ((BootstrapPhysicalBlock.tuple
          (blockInput p s incoming numerators hpos ids row rewards coordinates) t).val
          (followerPlayer p.two_le_m (BootstrapPhysicalBlock.selected
            (blockInput p s incoming numerators hpos ids row rewards coordinates) t)))
        ((BootstrapPhysicalBlock.tuple
          (blockInput p s incoming numerators hpos ids row rewards coordinates) t).val
          (coordinator p.two_le_m)) := by
  rw [BootstrapPhysicalBlock.actions_follower,
    followerAction_eq_unoccupied p s incoming numerators hpos ids row rewards coordinates t
      (BootstrapPhysicalBlock.selected
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t) hnot]
  rw [BootstrapPhysicalBlock.unoccupiedAction_selected_up _ _ ht,
    ← BootstrapPhysicalBlock.initialUpBit_eq_offset]

theorem actions_informed_unselected_up (coordinates : ExtendedPrivateCoordinates p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (j : Follower p.m) (hnot : j ∉ incoming)
    (ht : BootstrapPhysicalBlock.slot
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t = upSlot)
    (hnotSelected : j ≠ BootstrapPhysicalBlock.selected
      (blockInput p s incoming numerators hpos ids row rewards coordinates) t) :
    BootstrapPhysicalBlock.actions
      (blockInput p s incoming numerators hpos ids row rewards coordinates) st t
      (followerPlayer p.two_le_m j) =
      (BootstrapPhysicalBlock.tuple
        (blockInput p s incoming numerators hpos ids row rewards coordinates) t).val
        (followerPlayer p.two_le_m j) := by
  rw [BootstrapPhysicalBlock.actions_follower,
    followerAction_eq_unoccupied p s incoming numerators hpos ids row rewards coordinates t j hnot]
  have hnotdata : upSlot ≠ dataSlot := by decide
  simp [BootstrapPhysicalBlock.unoccupiedAction, ht, hnotdata, hnotSelected.symm]

end Bandits.Support.BootstrapPhysicalInput

end
