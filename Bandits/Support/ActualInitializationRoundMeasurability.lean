/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualBootstrapObservationCode
public import Bandits.Support.BootstrapCoordinatorRoundMeasurability
public import Bandits.Support.FollowerVaryingActivationMeasurability
public import Bandits.Support.ActualInitializationPhysicalStep
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Source-faithful inputs for one actual initialization physical round

This module starts from the existing heterogeneous follower state and
prelaunch coordinator, retains the full original source and fixed grid table,
and supplies a lossless code for the one-round input.  It proves the explicit
runtime readiness test measurable, and derives actions and grid feedback from
the prepared arms and the fixed reward table.  The joint physical-vector code
is exactly reconstructed from the existing prepared-round operations.  This
module does not yet compose prepared arms with the full follower and
coordinator observation continuations; no run or manuscript theorem is
asserted here.

Sources: `sources/zip4/manuscript/07_public_setup.tex:27-38,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-165`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.BootstrapAllCandidateController
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActiveRoundActions
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ContinuousControlSlice

namespace Bandits.Support.ActualInitializationRoundMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

/-! ## Lossless heterogeneous input coordinates -/

/-- Direct code for an existing follower coordinate.  Startup state is kept
in its existing countable carrier.  Declared state keeps its row and activation
and uses the accepted carried-state decomposition, including its ordered buffer
skeleton and original continuous scalar family. -/
abbrev FollowerCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  Sum (ActualBootstrapObservationCode.StartupCode p block)
    (Fin (M p) × (Activation p × IncomingConfiguration p rate))

instance followerCodeMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) : MeasurableSpace (FollowerCode p rate block) := by
  unfold FollowerCode
  infer_instance

/-- Encode one existing heterogeneous follower without changing its own row,
activation, startup cursor, candidate registers, memory, or buffer scalars. -/
def followerCodeOfState (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    ActualInitializationPhysicalStep.FollowerState p rate block →
      FollowerCode p rate block
  | .bootstrap state => .inl state
  | .declared row activation configuration =>
      .inr (row, (activation,
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate configuration))

/-- Reconstruct the existing heterogeneous follower state from its literal
code. -/
def followerStateOfCode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    FollowerCode p rate block → ActualInitializationPhysicalStep.FollowerState p rate block
  | .inl state => .bootstrap state
  | .inr (row, (activation, configuration)) =>
      .declared row activation
        (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate configuration)

/-- Decoding an encoded follower state is exact, including the entire
declared ordinary/dagger payload. -/
theorem followerStateOfCode_encode (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (state : ActualInitializationPhysicalStep.FollowerState p rate block) :
    followerStateOfCode p rate block (followerCodeOfState p rate block state) = state := by
  cases state with
  | bootstrap startup => rfl
  | declared row activation configuration =>
      simp [followerStateOfCode, followerCodeOfState,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming_incomingOfLocalConfiguration]

/-- A map into the existing follower state is measurable exactly when its
lossless representation is measurable. -/
instance followerStateMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    MeasurableSpace (ActualInitializationPhysicalStep.FollowerState p rate block) :=
  MeasurableSpace.comap (followerCodeOfState p rate block) inferInstance

theorem measurable_followerCodeOfState (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    Measurable (followerCodeOfState p rate block) := comap_measurable _

/-- The full input coordinates for one fixed block and fixed rate.  The
coordinator's row and ID array are retained separately from the original
source so that even an invalid alignment remains represented and can take the
physical step's `inputNotReady` branch. -/
structure RoundInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) where
  time : Fin p.T
  coordinatorRow : CompleteRow p
  coordinatorIDs : IDArray p
  coordinator : CoordinatorLocalCode p
  followers : Fin (p.m - 1) → FollowerCode p rate block
  source : ActualBootstrapObservationCode.ActualSource p
  rewards : ActualInitializationPhysicalStep.GridRewardTable p

def roundCompleteRowMeasurableSpace (p : Parameters) :
    MeasurableSpace (CompleteRow p) := inferInstance

def roundTimeMeasurableSpace (p : Parameters) :
    MeasurableSpace (Fin p.T) := inferInstance

def roundIDArrayMeasurableSpace (p : Parameters) :
    MeasurableSpace (IDArray p) := inferInstance

def roundCoordinatorMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorLocalCode p) := inferInstance

def roundSourceMeasurableSpace (p : Parameters) :
    MeasurableSpace (ActualBootstrapObservationCode.ActualSource p) := inferInstance

def roundRewardMeasurableSpace (p : Parameters) :
    MeasurableSpace (ActualInitializationPhysicalStep.GridRewardTable p) := inferInstance

def roundFollowerFamilyMeasurableSpace (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) :
    MeasurableSpace (Fin (p.m - 1) → FollowerCode p rate block) := inferInstance

/-- The nested product coordinate carrier, keeping every original component
separate. -/
abbrev RoundCoordinates (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :=
  Fin p.T × (CompleteRow p × (IDArray p × (CoordinatorLocalCode p ×
    ((Fin (p.m - 1) → FollowerCode p rate block) ×
      (ActualBootstrapObservationCode.ActualSource p ×
        ActualInitializationPhysicalStep.GridRewardTable p)))))

@[instance_reducible] instance roundCoordinatesMeasurableSpace (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) :
    MeasurableSpace (RoundCoordinates p rate block) := by
  let sourceRewards : MeasurableSpace
      (ActualBootstrapObservationCode.ActualSource p ×
        ActualInitializationPhysicalStep.GridRewardTable p) :=
    @Prod.instMeasurableSpace _ _ (roundSourceMeasurableSpace p)
      (roundRewardMeasurableSpace p)
  let followersTail : MeasurableSpace
      ((Fin (p.m - 1) → FollowerCode p rate block) ×
        (ActualBootstrapObservationCode.ActualSource p ×
          ActualInitializationPhysicalStep.GridRewardTable p)) :=
    @Prod.instMeasurableSpace _ _ (roundFollowerFamilyMeasurableSpace p rate block)
      sourceRewards
  let coordinatorTail : MeasurableSpace
      (CoordinatorLocalCode p ×
        ((Fin (p.m - 1) → FollowerCode p rate block) ×
          (ActualBootstrapObservationCode.ActualSource p ×
            ActualInitializationPhysicalStep.GridRewardTable p))) :=
    @Prod.instMeasurableSpace _ _ (roundCoordinatorMeasurableSpace p) followersTail
  let idsTail : MeasurableSpace
      (IDArray p × (CoordinatorLocalCode p ×
        ((Fin (p.m - 1) → FollowerCode p rate block) ×
          (ActualBootstrapObservationCode.ActualSource p ×
            ActualInitializationPhysicalStep.GridRewardTable p)))) :=
    @Prod.instMeasurableSpace _ _ (roundIDArrayMeasurableSpace p) coordinatorTail
  let rowTail : MeasurableSpace
      (CompleteRow p × (IDArray p × (CoordinatorLocalCode p ×
        ((Fin (p.m - 1) → FollowerCode p rate block) ×
          (ActualBootstrapObservationCode.ActualSource p ×
            ActualInitializationPhysicalStep.GridRewardTable p))))) :=
    @Prod.instMeasurableSpace _ _ (roundCompleteRowMeasurableSpace p) idsTail
  exact @Prod.instMeasurableSpace _ _ (roundTimeMeasurableSpace p) rowTail

/-- The observable product coordinates defining the measurable structure on
`RoundInput`.  The source remains the complete nested source product. -/
def roundInputCoordinates (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) : RoundCoordinates p rate block :=
  (x.time, (x.coordinatorRow, (x.coordinatorIDs,
    (x.coordinator, (x.followers, (x.source, x.rewards))))))

instance roundInputMeasurableSpace (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSpace (RoundInput p rate block C_star C_h) :=
  MeasurableSpace.comap (roundInputCoordinates p rate block C_star C_h)
    (roundCoordinatesMeasurableSpace p rate block)

theorem measurable_roundInputCoordinates (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    Measurable (roundInputCoordinates p rate block C_star C_h) := comap_measurable _

/-- Reassemble the accepted coordinator carrier with the same fixed
`C_star` and `C_h` used by its launch test. -/
def coordinatorBaseOfInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) : CoordinatorContinuousBase p :=
  (((x.coordinatorRow, x.coordinatorIDs), (C_star, C_h)))

/-- Exact existing prelaunch coordinator state represented by the separate
continuous base and local code. -/
def coordinatorOfInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) :
    BootstrapCoordinatorLocalRound.PrelaunchBlock p :=
  BootstrapCoordinatorRoundMeasurability.assemblePrelaunch p
    (coordinatorBaseOfInput p rate block C_star C_h x) x.coordinator

/-- Reconstruct every existing follower coordinate from the direct codes. -/
def followersOfInput (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p))
    (codes : Fin (p.m - 1) → FollowerCode p rate block) :=
  fun i => followerStateOfCode p rate block (codes i)

/-- The existing physical operation on an assembled round input. -/
def actualRoundStep (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) :=
  ActualInitializationPhysicalStep.step rate block x.time
    (coordinatorOfInput p rate block C_star C_h x)
    (followersOfInput p rate block x.followers) x.source x.rewards

/-- The input assembler reconstructs the very same existing one-round step;
it introduces no second transition or altered source. -/
theorem actualRoundStep_reconstructs (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) :
    actualRoundStep p rate block C_star C_h x =
      ActualInitializationPhysicalStep.step rate block x.time
        (coordinatorOfInput p rate block C_star C_h x)
        (followersOfInput p rate block x.followers) x.source x.rewards := rfl

/-! ## Runtime readiness is an explicit measurable test -/

/-- The literal runtime readiness proposition checked by the existing
physical `prepare`. -/
def roundInputReady (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) : Prop :=
  ActualInitializationPhysicalStep.ActualInputReady p rate block x.time
    (coordinatorOfInput p rate block C_star C_h x)
    (followersOfInput p rate block x.followers) x.source

/-- The source-aligned expansion of readiness.  Only these explicit fields
are tested: current block and calendar time, coordinator IDs/row/target, and
each follower's own startup cursor or activation time. -/
def roundInputReadyFields (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) : Prop :=
  x.coordinator.block = block ∧
  x.time ∈ calendarBlock p block ∧
  x.coordinatorIDs = ActualBootstrapObservationCode.sourceIDs p x.source ∧
  x.coordinatorRow = ActualBootstrapObservationCode.sourceRows p x.source
    (ActualInitializationPhysicalStep.selectedRowIndex p x.source) ∧
  x.coordinator.target = BootstrapPhysicalInput.targetArmMap p block
    (ActualBootstrapObservationCode.sourcePrivate p x.source) ∧
  ∀ i, ActualInitializationPhysicalStep.followerAtNextCursor x.time
    (followerStateOfCode p rate block (x.followers i))

/-- The expanded readiness test reconstructs the physical step's exact
`ActualInputReady`; there is no readiness assumption in the adapter. -/
theorem roundInputReady_iff_fields (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ)
    (x : RoundInput p rate block C_star C_h) :
    roundInputReady p rate block C_star C_h x ↔
      roundInputReadyFields p rate block C_star C_h x := by
  simp [roundInputReady, roundInputReadyFields, ActualInitializationPhysicalStep.ActualInputReady,
    coordinatorOfInput, coordinatorBaseOfInput, followersOfInput,
    BootstrapCoordinatorRoundMeasurability.assemblePrelaunch,
    followersOfInput,
    ActualBootstrapObservationCode.sourceRows, ActualBootstrapObservationCode.sourceIDs,
    ActualBootstrapObservationCode.sourcePrivate]

local instance roundScalarMeasurableEq : MeasurableEq ContinuousControlSlice.Scalar where
  measurableSet_diagonal := by
    have hval : Measurable (fun z : ContinuousControlSlice.Scalar ×
        ContinuousControlSlice.Scalar => ((z.1 : ℝ), (z.2 : ℝ))) :=
      (measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_subtype_coe.comp measurable_snd)
    convert (measurableSet_diagonal : MeasurableSet (Set.diagonal ℝ)).preimage hval using 1
    ext z
    simp only [Set.mem_diagonal_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h

local instance roundPiMeasurableEq {ι β : Type*} [Countable ι]
    [MeasurableSpace β] [MeasurableEq β] : MeasurableEq (ι → β) where
  measurableSet_diagonal := by
    have hcoord (i : ι) : MeasurableSet
        {z : (ι → β) × (ι → β) | z.1 i = z.2 i} :=
      measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst)
        ((measurable_pi_apply i).comp measurable_snd)
    have hdecomp : Set.diagonal (ι → β) =
        ⋂ i, {z : (ι → β) × (ι → β) | z.1 i = z.2 i} := by
      ext z
      simp [Set.mem_diagonal_iff, funext_iff]
    rw [hdecomp]
    exact MeasurableSet.iInter hcoord

local instance roundProdMeasurableEq {α β : Type*} [MeasurableSpace α]
    [MeasurableEq α] [MeasurableSpace β] [MeasurableEq β] :
    MeasurableEq (α × β) where
  measurableSet_diagonal := by
    have hleft : MeasurableSet
        {z : (α × β) × (α × β) | z.1.1 = z.2.1} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd)
    have hright : MeasurableSet
        {z : (α × β) × (α × β) | z.1.2 = z.2.2} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd)
    have hdecomp : Set.diagonal (α × β) =
        {z : (α × β) × (α × β) | z.1.1 = z.2.1} ∩
          {z : (α × β) × (α × β) | z.1.2 = z.2.2} := by
      ext z
      simp [Set.mem_diagonal_iff, Prod.ext_iff]
    rw [hdecomp]
    exact hleft.inter hright

private theorem measurable_of_countable_key {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (f : α → γ)
    (hf : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  intro t ht
  have hpre : f ⁻¹' t = key ⁻¹' (key '' (f ⁻¹' t)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      change f x ∈ t
      rw [hf x y heq.symm]
      exact hy
  rw [hpre]
  exact hkey (Set.to_countable _).measurableSet

private def followerCursorKey (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (z : Fin p.T × FollowerCode p rate block) :=
  match z.2 with
  | .inl startup => (z.1, Sum.inl startup.processed.val)
  | .inr (_, (activation, _)) => (z.1, Sum.inr activation)

private instance activationCursorSumMeasurableSingletonClass (p : Parameters) :
    MeasurableSingletonClass (ℕ ⊕ Activation p) where
  measurableSet_singleton cursor := by
    rw [measurableSet_sum_iff]
    cases cursor with
    | inl n =>
        constructor
        · convert (measurableSet_singleton n) using 1 <;> ext m <;> simp
        · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Activation p))) using 1
          ext a
          simp
    | inr activation =>
        constructor
        · convert (MeasurableSet.empty : MeasurableSet (∅ : Set ℕ)) using 1
          ext n
          simp
        · convert (measurableSet_singleton activation) using 1 <;> ext a <;> simp

def followerCursorProjection (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (code : FollowerCode p rate block) :
    Sum ℕ (Activation p) :=
  match code with
  | .inl startup => .inl startup.processed.val
  | .inr (_, (activation, _)) => .inr activation

private theorem measurable_followerCursorProjection (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p)) :
    Measurable (followerCursorProjection p rate block) := by
  apply Measurable.sumElim
  · exact measurable_inl.comp
      (measurable_of_countable (fun startup : ActualBootstrapObservationCode.StartupCode p block =>
        startup.processed.val))
  · exact measurable_inr.comp (measurable_fst.comp measurable_snd)

private theorem followerCursorKey_measurable (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    Measurable (fun z : Fin p.T × FollowerCode p rate block =>
      followerCursorKey p rate block z) := by
  have hkey : (fun z : Fin p.T × FollowerCode p rate block =>
      followerCursorKey p rate block z) =
      fun z => (z.1, followerCursorProjection p rate block z.2) := by
    funext z
    rcases z with ⟨time, code⟩
    cases code <;> rfl
  rw [hkey]
  exact measurable_fst.prodMk
    ((measurable_followerCursorProjection p rate block).comp measurable_snd)

noncomputable def followerCursorOk (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (z : Fin p.T × FollowerCode p rate block) : Bool := by
  classical
  exact match followerCursorProjection p rate block z.2 with
    | .inl cursor => decide (z.1 ∈ calendarBlock p block ∧
        cursor < BootstrapObservedFollower.blockLength p block ∧
        z.1.val = BootstrapObservedFollower.blockStart p block + cursor)
    | .inr activation => decide (activation.val ≤ z.1.val + 1)

/-- The countable cursor classifier is exactly the physical next-cursor test
after decoding an existing follower coordinate. -/
theorem followerCursorOk_reconstructs (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (z : Fin p.T × FollowerCode p rate block) :
    followerCursorOk p rate block z = true ↔
      ActualInitializationPhysicalStep.followerAtNextCursor z.1
        (followerStateOfCode p rate block z.2) := by
  classical
  rcases z with ⟨time, code⟩
  cases code <;>
    simp [followerCursorOk, followerCursorProjection, followerStateOfCode,
      ActualInitializationPhysicalStep.followerAtNextCursor]

/-- The next-cursor predicate is measurable from the explicit time, startup
cursor or declared activation coordinate.  The entire ordinary/dagger buffer
does not enter this test. -/
theorem measurable_followerAtNextCursor (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) :
    Measurable (fun z : Fin p.T × FollowerCode p rate block =>
      followerCursorOk p rate block z) := by
  classical
  apply measurable_of_countable_key
    (followerCursorKey p rate block) (followerCursorKey_measurable p rate block)
  intro x y h
  rcases x with ⟨tx, cx⟩
  rcases y with ⟨ty, cy⟩
  cases cx with
  | inl sx =>
      cases cy with
      | inl sy =>
          simp only [followerCursorKey, Sum.inl.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, hcursor⟩
          simp only [followerCursorOk, followerCursorProjection] at ⊢
          exact congrArg (fun cursor : ℕ => decide (tx ∈ calendarBlock p block ∧
            cursor < BootstrapObservedFollower.blockLength p block ∧
            tx.val = BootstrapObservedFollower.blockStart p block + cursor)) hcursor
      | inr dy => cases h
  | inr dx =>
      cases cy with
      | inl sy => cases h
      | inr dy =>
          simp only [followerCursorKey, Sum.inr.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, hactivation⟩
          simp only [followerCursorOk, followerCursorProjection] at ⊢
          exact congrArg (fun activation : Activation p =>
            decide (activation.val ≤ tx.val + 1)) hactivation

/-- The actual readiness set on the full input carrier. -/
theorem measurableSet_roundInputReady (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (C_star C_h : ℝ) :
    MeasurableSet {x : RoundInput p rate block C_star C_h |
      roundInputReady p rate block C_star C_h x} := by
  classical
  have hset :
      {x : RoundInput p rate block C_star C_h |
        roundInputReady p rate block C_star C_h x} =
      {x : RoundInput p rate block C_star C_h |
        roundInputReadyFields p rate block C_star C_h x} := by
    ext x
    exact roundInputReady_iff_fields p rate block C_star C_h x
  rw [hset]
  let hcoords := measurable_roundInputCoordinates p rate block C_star C_h
  have htime : Measurable (fun x : RoundInput p rate block C_star C_h => x.time) :=
    measurable_fst.comp hcoords
  have hrow : Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinatorRow) :=
    measurable_fst.comp (measurable_snd.comp hcoords)
  have hids : Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinatorIDs) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hcoords))
  have hlocal : Measurable (fun x : RoundInput p rate block C_star C_h => x.coordinator) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hcoords)))
  have hfollowers : Measurable
      (fun x : RoundInput p rate block C_star C_h => x.followers) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp hcoords))))
  have hsource : Measurable
      (fun x : RoundInput p rate block C_star C_h => x.source) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hcoords)))))
  have hcoordBlock : Measurable
      (fun x : RoundInput p rate block C_star C_h => x.coordinator.block) :=
    (measurable_of_countable _).comp hlocal
  have hcoordTarget : Measurable
      (fun x : RoundInput p rate block C_star C_h => x.coordinator.target) :=
    (measurable_of_countable _).comp hlocal
  have hsourceIDs : Measurable
      (fun x : RoundInput p rate block C_star C_h =>
        ActualBootstrapObservationCode.sourceIDs p x.source) :=
    (ActualBootstrapObservationCode.measurable_sourceIDs p).comp hsource
  have hsourceRows : Measurable
      (fun x : RoundInput p rate block C_star C_h =>
        ActualBootstrapObservationCode.sourceRows p x.source) :=
    (ActualBootstrapObservationCode.measurable_sourceRows p).comp hsource
  have hselected : Measurable
      (fun x : RoundInput p rate block C_star C_h =>
        ActualInitializationPhysicalStep.selectedRowIndex p x.source) :=
    (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p).comp hsource
  have hselectedRow : Measurable
      (fun x : RoundInput p rate block C_star C_h =>
        ActualBootstrapObservationCode.sourceRows p x.source
          (ActualInitializationPhysicalStep.selectedRowIndex p x.source)) := by
    have heval : Measurable (fun z : CompleteRows p × Fin (M p) => z.1 z.2) := by
      exact measurable_from_prod_countable_left fun j =>
        measurable_pi_apply j
    exact heval.comp (hsourceRows.prodMk hselected)
  have htarget : Measurable
      (fun x : RoundInput p rate block C_star C_h =>
        BootstrapPhysicalInput.targetArmMap p block
          (ActualBootstrapObservationCode.sourcePrivate p x.source)) :=
    (BootstrapPhysicalInput.measurable_targetArmMap p block).comp
      ((ActualBootstrapObservationCode.measurable_sourcePrivate p).comp hsource)
  have htimeSet : MeasurableSet {x : RoundInput p rate block C_star C_h |
      x.time ∈ calendarBlock p block} := by
    exact htime ((Set.to_countable _).measurableSet)
  have hcursor (i : Fin (p.m - 1)) : MeasurableSet
      {x : RoundInput p rate block C_star C_h |
        ActualInitializationPhysicalStep.followerAtNextCursor x.time
          (followerStateOfCode p rate block (x.followers i))} := by
    have hfi : Measurable
        (fun x : RoundInput p rate block C_star C_h => x.followers i) :=
      (measurable_pi_apply i).comp hfollowers
    have hpair : Measurable (fun x : RoundInput p rate block C_star C_h =>
        (x.time, x.followers i)) := htime.prodMk hfi
    let cursorBit : RoundInput p rate block C_star C_h → Bool := fun x =>
      followerCursorOk p rate block (x.time, x.followers i)
    have hbit : Measurable cursorBit :=
      (measurable_followerAtNextCursor p rate block).comp hpair
    have hpred : {x : RoundInput p rate block C_star C_h |
        ActualInitializationPhysicalStep.followerAtNextCursor x.time
          (followerStateOfCode p rate block (x.followers i))} = cursorBit ⁻¹' {true} := by
      ext x
      change ActualInitializationPhysicalStep.followerAtNextCursor x.time
          (followerStateOfCode p rate block (x.followers i)) ↔
        cursorBit x = true
      dsimp [cursorBit]
      exact (followerCursorOk_reconstructs p rate block
        (x.time, x.followers i)).symm
    rw [hpred]
    exact hbit (MeasurableSet.singleton true)
  have hfieldsSet :
      {x : RoundInput p rate block C_star C_h |
        roundInputReadyFields p rate block C_star C_h x} =
      {x | x.coordinator.block = block} ∩
        ({x | x.time ∈ calendarBlock p block} ∩
          ({x | x.coordinatorIDs = ActualBootstrapObservationCode.sourceIDs p x.source} ∩
            ({x | x.coordinatorRow = ActualBootstrapObservationCode.sourceRows p x.source
              (ActualInitializationPhysicalStep.selectedRowIndex p x.source)} ∩
              ({x | x.coordinator.target = BootstrapPhysicalInput.targetArmMap p block
                (ActualBootstrapObservationCode.sourcePrivate p x.source)} ∩
                (⋂ i, {x : RoundInput p rate block C_star C_h |
                  ActualInitializationPhysicalStep.followerAtNextCursor x.time
                    (followerStateOfCode p rate block (x.followers i))}))))) := by
    ext x
    simp [roundInputReadyFields]
  rw [hfieldsSet]
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun hcoordBlock measurable_const
  · apply MeasurableSet.inter
    · exact htimeSet
    · apply MeasurableSet.inter
      · exact measurableSet_eq_fun hids hsourceIDs
      · apply MeasurableSet.inter
        · exact measurableSet_eq_fun hrow hselectedRow
        · apply MeasurableSet.inter
          · exact measurableSet_eq_fun hcoordTarget htarget
          · exact MeasurableSet.iInter hcursor

/-! ## Simultaneous physical actions and derived grid feedback -/

/-- Assemble the joint physical profile from the already prepared coordinator
arm and each follower's own prepared arm. -/
def actionProfileFromPreparedArms (p : Parameters)
    (coordinatorArm : Fin p.K) (followerArms : Fin (p.m - 1) → Fin p.K) :
    ActionProfile p.m p.K := fun player =>
  if h : player = ActiveRoundActions.coordinator p.two_le_m then coordinatorArm
  else followerArms (ActiveRoundActions.followerIndex p.two_le_m player h)

/-- The action profile assembled from the prepared arms is measurable from
the coordinator's and followers' own finite arm maps. -/
theorem measurable_actionProfileFromPreparedArms {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters)
    (coordinatorArm : Ω → Fin p.K)
    (followerArms : Ω → Fin (p.m - 1) → Fin p.K)
    (hcoordinator : Measurable coordinatorArm) (hfollowers : Measurable followerArms) :
    Measurable (fun ω => actionProfileFromPreparedArms p
      (coordinatorArm ω) (followerArms ω)) := by
  apply measurable_pi_iff.mpr
  intro player
  by_cases h : player = ActiveRoundActions.coordinator p.two_le_m
  · simp [actionProfileFromPreparedArms, h]
    exact hcoordinator
  · simp [actionProfileFromPreparedArms, h]
    exact (measurable_pi_apply (ActiveRoundActions.followerIndex p.two_le_m player h)).comp
      hfollowers

/-- Derive one player's finite grid observation using the actual collision
rule, the simultaneous profile, and the unchanged fixed reward table. -/
def gridFeedbackFromProfile (p : Parameters) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (time : Fin p.T) (profile : ActionProfile p.m p.K) (player : Fin p.m) :
    Fin (D p + 1) := by
  classical
  exact if FiniteBanditModel.collisionFreeFor profile player then
    rewards time (profile player) else 0

/-- The derived finite feedback vector, with no separately supplied reward or
feedback input. -/
def feedbackProfileFromActions (p : Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (time : Fin p.T) (profile : ActionProfile p.m p.K) :
    Fin p.m → Fin (D p + 1) :=
  fun player => gridFeedbackFromProfile p rewards time profile player

/-- The same finite action and reward key determines the collision-grid
feedback, so feedback is measurable jointly in prepared arms, calendar time,
and the fixed reward table. -/
theorem measurable_gridFeedbackFromProfile {Ω : Type*} [MeasurableSpace Ω]
    (p : Parameters) (rewards : Ω → ActualInitializationPhysicalStep.GridRewardTable p)
    (time : Ω → Fin p.T) (profile : Ω → ActionProfile p.m p.K)
    (hrewards : Measurable rewards) (htime : Measurable time)
    (hprofile : Measurable profile) :
    Measurable (fun ω => feedbackProfileFromActions p (rewards ω) (time ω) (profile ω)) := by
  apply measurable_pi_iff.mpr
  intro player
  let key := fun ω => (rewards ω, (time ω, profile ω))
  have hkey : Measurable key := hrewards.prodMk (htime.prodMk hprofile)
  have hcode : Measurable (fun z : ActualInitializationPhysicalStep.GridRewardTable p ×
      (Fin p.T × ActionProfile p.m p.K) =>
        gridFeedbackFromProfile p z.1 z.2.1 z.2.2 player) := by
    exact measurable_of_countable _
  exact hcode.comp hkey

/-- The joint profile assembled from prepared arms is exactly the accepted
physical step profile. -/
theorem actionProfileFromPreparedArms_reconstructs (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p))
    (prepared : ActualInitializationPhysicalStep.PreparedRound p rate block) :
    actionProfileFromPreparedArms p prepared.coordinator.arm
      (fun i => (prepared.followers i).arm) =
        ActualInitializationPhysicalStep.actionProfile prepared := by
  funext player
  by_cases h : player = ActiveRoundActions.coordinator p.two_le_m
  · simp [actionProfileFromPreparedArms, ActualInitializationPhysicalStep.actionProfile, h]
  · simp [actionProfileFromPreparedArms, ActualInitializationPhysicalStep.actionProfile, h]

/-- The derived profile operations agree definitionally with the accepted
physical step's action and grid-feedback definitions once the accepted
prepared arms are supplied. -/
theorem gridFeedbackFromProfile_reconstructs (p : Parameters) (rate : RateInput p)
    (block : Fin (n_boot p)) (prepared :
    ActualInitializationPhysicalStep.PreparedRound p rate block) :
    feedbackProfileFromActions p prepared.rewards prepared.time
      (ActualInitializationPhysicalStep.actionProfile prepared) =
        ActualInitializationPhysicalStep.physicalFeedback prepared := by
  funext player
  change gridFeedbackFromProfile p prepared.rewards prepared.time
      (ActualInitializationPhysicalStep.actionProfile prepared) player =
    ActualInitializationPhysicalStep.gridFeedback prepared player
  rfl

/-! ## Joint simultaneous play code -/

/-- The joint finite physical output for one prepared round: the complete
simultaneous action profile and the feedback vector derived from that same
profile and the unchanged fixed grid table. -/
abbrev JointPhysicalCode (p : Parameters) :=
  ActionProfile p.m p.K × (Fin p.m → Fin (D p + 1))

/-- Assemble the physical output from separate prepared arm maps, time, and
the original fixed grid table. No feedback coordinate is supplied. -/
def jointPhysicalCodeFromComponents (p : Parameters)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (time : Fin p.T) (coordinatorArm : Fin p.K)
    (followerArms : Fin (p.m - 1) → Fin p.K) : JointPhysicalCode p :=
  let profile := actionProfileFromPreparedArms p coordinatorArm followerArms
  (profile, feedbackProfileFromActions p rewards time profile)

/-- On any base measurable space, separate measurable arm maps, time, and
fixed-table maps suffice for the joint simultaneous action and derived
feedback code. -/
theorem measurable_jointPhysicalCodeFromComponents {Ω : Type*}
    [MeasurableSpace Ω] (p : Parameters)
    (rewards : Ω → ActualInitializationPhysicalStep.GridRewardTable p)
    (time : Ω → Fin p.T) (coordinatorArm : Ω → Fin p.K)
    (followerArms : Ω → Fin (p.m - 1) → Fin p.K)
    (hrewards : Measurable rewards) (htime : Measurable time)
    (hcoordinatorArm : Measurable coordinatorArm)
    (hfollowerArms : Measurable followerArms) :
    Measurable (fun ω => jointPhysicalCodeFromComponents p (rewards ω)
      (time ω) (coordinatorArm ω) (followerArms ω)) := by
  let profile := fun ω => actionProfileFromPreparedArms p
    (coordinatorArm ω) (followerArms ω)
  have hprofile : Measurable profile :=
    measurable_actionProfileFromPreparedArms p coordinatorArm followerArms
      hcoordinatorArm hfollowerArms
  have hfeedback : Measurable (fun ω =>
      feedbackProfileFromActions p (rewards ω) (time ω) (profile ω)) :=
    measurable_gridFeedbackFromProfile p rewards time profile hrewards htime hprofile
  have hcode : (fun ω => jointPhysicalCodeFromComponents p (rewards ω)
      (time ω) (coordinatorArm ω) (followerArms ω)) =
      fun ω => (profile ω, feedbackProfileFromActions p (rewards ω)
        (time ω) (profile ω)) := by
    funext ω
    rfl
  rw [hcode]
  exact hprofile.prodMk hfeedback

/-- Exact connection to the accepted prepared physical round. This code
reconstructs its real simultaneous profile and the collision-derived
denominator-`D` feedback vector. -/
theorem jointPhysicalCodeFromPrepared_reconstructs (p : Parameters)
    (rate : RateInput p) (block : Fin (n_boot p))
    (prepared : ActualInitializationPhysicalStep.PreparedRound p rate block) :
    jointPhysicalCodeFromComponents p prepared.rewards prepared.time
      prepared.coordinator.arm (fun i => (prepared.followers i).arm) =
      (ActualInitializationPhysicalStep.actionProfile prepared,
        ActualInitializationPhysicalStep.physicalFeedback prepared) := by
  apply Prod.ext
  · exact actionProfileFromPreparedArms_reconstructs p rate block prepared
  · rw [← gridFeedbackFromProfile_reconstructs p rate block prepared]
    rfl

end Bandits.Support.ActualInitializationRoundMeasurability

end
