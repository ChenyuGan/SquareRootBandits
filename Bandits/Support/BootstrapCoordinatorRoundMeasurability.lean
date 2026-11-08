/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapCoordinatorLocalRound

/-!
# Measurable adapters for the actual coordinator-local bootstrap round

The source row and shared ID array remain separate, unchanged coordinates.
Only the coordinator's finite local state and transition tags are encoded.
The adapters below concern the existing `BootstrapCoordinatorLocalRound`
operations; they do not define a physical run or its block recursion.

Sources: `sources/zip4/manuscript/07_public_setup.tex:39-57,63-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-99`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapStartupCostScale
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.PublicDiscreteDraws
open scoped BigOperators Classical

namespace Bandits.Support.BootstrapCoordinatorRoundMeasurability

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

instance coordinatorModeMeasurableSpace :
    MeasurableSpace BootstrapPhysicalBlock.Mode := ⊤

instance coordinatorModeCountable : Countable BootstrapPhysicalBlock.Mode := by
  apply Function.Injective.countable (f := fun mode : BootstrapPhysicalBlock.Mode =>
    match mode with | .discover => false | .multicast => true)
  intro a b h
  cases a <;> cases b <;> simp_all

instance coordinatorOptionalArmMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Fin p.K)) := ⊤

instance coordinatorOptionalTimeMeasurableSpace (p : Parameters) :
    MeasurableSpace (Option (Fin p.T)) := ⊤

/-- A countable key proves measurability whenever the result is constant on
its fibers; the original domain may still contain continuous coordinates. -/
private theorem measurable_of_countable_key {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (f : α → γ)
    (hf : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  intro s hs
  have hpre : f ⁻¹' s = key ⁻¹' (key '' (f ⁻¹' s)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      change f x ∈ s
      rw [hf x y heq.symm]
      exact hy
  rw [hpre]
  exact hkey (Set.to_countable _).measurableSet

/-- The exact discrete projection of the existing coordinator list/mode/audit
state. -/
abbrev CoordinatorStateCode (p : Parameters) :=
  Finset (Fin (A_id p)) × (BootstrapPhysicalBlock.Mode × Finset (Fin p.T))

/-- Encode only the finite local fields of the existing coordinator state. -/
def coordinatorStateCode (p : Parameters)
    (state : BootstrapPhysicalBlock.State p) : CoordinatorStateCode p :=
  (state.list, (state.mode, state.positives))

/-- Reconstruct the existing state from its three unchanged local fields. -/
def coordinatorStateOfCode (p : Parameters)
    (code : CoordinatorStateCode p) : BootstrapPhysicalBlock.State p :=
  ⟨code.1, code.2.1, code.2.2⟩

theorem coordinatorStateOfCode_encode (p : Parameters)
    (state : BootstrapPhysicalBlock.State p) :
    coordinatorStateOfCode p (coordinatorStateCode p state) = state := by
  cases state
  rfl

instance coordinatorStateMeasurableSpace (p : Parameters) :
    MeasurableSpace (BootstrapPhysicalBlock.State p) :=
  MeasurableSpace.comap (coordinatorStateCode p) inferInstance

/-- The monitor's entire countable local state, including its no-launch
sentinel or first-crossing tag. -/
structure MonitorCode (p : Parameters) where
  counters : Fin p.K → ℕ
  crossingBlock : Option (Fin (n_boot p))
  launchPosition : ℕ

theorem monitorCodeFields_injective (p : Parameters) :
    Function.Injective (fun c : MonitorCode p =>
      (c.counters, (c.crossingBlock, c.launchPosition))) := by
  intro a b h
  cases a
  cases b
  simp_all

instance monitorCodeCountable (p : Parameters) : Countable (MonitorCode p) :=
  (monitorCodeFields_injective p).countable

instance monitorCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (MonitorCode p) := ⊤

def monitorCode (p : Parameters) (state : BootstrapLaunchMonitor.State p) :
    MonitorCode p :=
  ⟨state.counters, state.crossingBlock, state.launchPosition⟩

def monitorStateOfCode (p : Parameters) (code : MonitorCode p) :
    BootstrapLaunchMonitor.State p :=
  ⟨code.counters, code.crossingBlock, code.launchPosition⟩

theorem monitorStateOfCode_encode (p : Parameters)
    (state : BootstrapLaunchMonitor.State p) :
    monitorStateOfCode p (monitorCode p state) = state := by
  cases state
  rfl

/-- The real carrier of a coordinator's prelaunch continuous information. -/
abbrev CoordinatorContinuousBase (p : Parameters) :=
  (CompletePublicTable.CompleteRow p × CompletePublicTable.IDArray p) × (ℝ × ℝ)

/-- Countable local fields of one existing block-start coordinator state.
The monitor is a faithful encoding of `UnlaunchedMonitor`, retaining both
the `crossingBlock = none` and `launchPosition = T` subtype checks. -/
structure CoordinatorLocalCode (p : Parameters) where
  block : Fin (n_boot p)
  target : Fin p.K
  coordinator : CoordinatorStateCode p
  monitor : {m : MonitorCode p // m.crossingBlock = none ∧ m.launchPosition = p.T}

theorem coordinatorLocalCodeFields_injective (p : Parameters) :
    Function.Injective (fun c : CoordinatorLocalCode p =>
      (c.block, (c.target, (c.coordinator, c.monitor)))) := by
  intro a b h
  cases a
  cases b
  simp_all

instance coordinatorLocalCodeCountable (p : Parameters) :
    Countable (CoordinatorLocalCode p) :=
  (coordinatorLocalCodeFields_injective p).countable

instance coordinatorLocalCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorLocalCode p) := ⊤

/-- Project the unchanged continuous base and countable local fields from the
existing prelaunch block. -/
def prelaunchCoordinates (p : Parameters)
    (before : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    CoordinatorContinuousBase p × CoordinatorLocalCode p :=
  (((before.data.row, before.data.ids),
      (before.data.C_star, before.data.C_h)),
    ⟨before.data.block, before.data.target,
      coordinatorStateCode p before.data.coordinator,
      ⟨monitorCode p before.monitor.1, before.monitor.2⟩⟩)

instance prelaunchBlockMeasurableSpace (p : Parameters) :
    MeasurableSpace (BootstrapCoordinatorLocalRound.PrelaunchBlock p) :=
  MeasurableSpace.comap (prelaunchCoordinates p) inferInstance

theorem measurable_prelaunchCoordinates (p : Parameters) :
    Measurable (prelaunchCoordinates p) := by
  exact comap_measurable (prelaunchCoordinates p)

theorem measurable_prelaunchBase (p : Parameters) :
    Measurable (fun before : BootstrapCoordinatorLocalRound.PrelaunchBlock p =>
      (prelaunchCoordinates p before).1) :=
  measurable_fst.comp (measurable_prelaunchCoordinates p)

theorem measurable_prelaunchLocalCode (p : Parameters) :
    Measurable (fun before : BootstrapCoordinatorLocalRound.PrelaunchBlock p =>
      (prelaunchCoordinates p before).2) :=
  measurable_snd.comp (measurable_prelaunchCoordinates p)

/-- Reassemble the same local state using the original complete row and ID
array. `C_star` and `C_h` are fixed arguments, shared with the launch test. -/
def assemblePrelaunch (p : Parameters)
    (base : CoordinatorContinuousBase p) (code : CoordinatorLocalCode p) :
    BootstrapCoordinatorLocalRound.PrelaunchBlock p :=
  ⟨⟨code.block, base.1.1, base.1.2, code.target,
      coordinatorStateOfCode p code.coordinator, base.2.1, base.2.2⟩,
    ⟨monitorStateOfCode p code.monitor.1, by
      simpa [monitorStateOfCode] using code.monitor.2⟩⟩

theorem assemblePrelaunch_coordinates (p : Parameters)
    (base : CoordinatorContinuousBase p) (code : CoordinatorLocalCode p) :
    prelaunchCoordinates p (assemblePrelaunch p base code) =
      (base, code) := by
  cases base with
  | mk row ids =>
    cases code with
    | mk block target coordinator monitor =>
      cases coordinator
      cases monitor with
      | mk monitor hvalid =>
        cases monitor with
        | mk counters crossingBlock launchPosition =>
          simp [prelaunchCoordinates, assemblePrelaunch, coordinatorStateCode,
            coordinatorStateOfCode, monitorCode, monitorStateOfCode]

theorem reconstructPrelaunch (p : Parameters)
    (before : BootstrapCoordinatorLocalRound.PrelaunchBlock p) :
    assemblePrelaunch p (prelaunchCoordinates p before).1
      (prelaunchCoordinates p before).2 = before := by
  cases before with
  | mk data monitor =>
    cases data with
    | mk block row ids target coordinator C₁ C₂ =>
      cases coordinator
      cases monitor with
      | mk monitor hvalid =>
        cases monitor with
        | mk counters crossingBlock launchPosition =>
          simp [assemblePrelaunch, prelaunchCoordinates, coordinatorStateCode,
            coordinatorStateOfCode, monitorCode, monitorStateOfCode]

/-- The source round and complete-row slice, with time retained as a separate
finite input. -/
def rowTimeSlice (p : Parameters)
    (z : CompletePublicTable.CompleteRow p × Fin p.T) : Slice p :=
  (z.1.2 z.2).1

theorem measurable_rowTimeSlice (p : Parameters) :
    Measurable (rowTimeSlice p) := by
  apply measurable_from_prod_countable_left
  intro t
  exact measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)

/-- Joint source slot read from the existing selected complete row. -/
theorem measurable_coordinatorSlot_joint (p : Parameters) :
    Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
      BootstrapCoordinatorLocalRound.coordinatorSlot p z.1 z.2) := by
  change Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
    PublicDiscreteDraws.slotDraw (rowTimeSlice p z))
  exact measurable_slotDraw.comp (measurable_rowTimeSlice p)

/-- Joint source tuple arm read from the existing ordered tuple sampler. -/
theorem measurable_coordinatorTupleArm_joint (p : Parameters) :
    Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
      BootstrapCoordinatorLocalRound.coordinatorTupleArm p z.1 z.2) := by
  change Measurable (fun z : CompletePublicTable.CompleteRow p × Fin p.T =>
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (rowTimeSlice p z)).val
      (ActiveRoundActions.coordinator p.two_le_m))
  exact (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
    (measurable_subtype_coe.comp
      ((OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp
        (measurable_rowTimeSlice p)))

/-- The pointwise finite-product formula on the actual forward row, list, and
calendar round. The empty finset keeps Mathlib's empty-product value one. -/
def forwardProductFromFields (p : Parameters)
    (forward : CompletePublicTable.ForwardRow p)
    (list : Finset (Fin (A_id p))) (t : Fin p.T) : ℕ :=
  ∏ u ∈ list, if forward u t = true then 1 else 0

theorem measurable_forwardProduct_joint (p : Parameters) :
    Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (Finset (Fin (A_id p)) × Fin p.T) =>
        forwardProductFromFields p z.1.1 z.2.1 z.2.2) := by
  have hforward : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (Finset (Fin (A_id p)) × Fin p.T) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hlist : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (Finset (Fin (A_id p)) × Fin p.T) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have ht : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (Finset (Fin (A_id p)) × Fin p.T) => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hkey : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (Finset (Fin (A_id p)) × Fin p.T) => (z.1.1, (z.2.1, z.2.2))) :=
    hforward.prodMk (hlist.prodMk ht)
  have hdiscrete : Measurable (fun z :
      CompletePublicTable.ForwardRow p × (Finset (Fin (A_id p)) × Fin p.T) =>
        forwardProductFromFields p z.1 z.2.1 z.2.2) :=
    measurable_of_countable _
  exact hdiscrete.comp hkey

/-- The finite source key used to separate row-dependent sampler outputs from
the unmodified continuous coordinates. -/
abbrev ArmChoiceKey (p : Parameters) :=
  Slot × (Fin p.K × (ℕ × (Fin p.K × Fin p.K)))

theorem measurable_coordinatorArmChoice_at_time (p : Parameters)
    (target : Fin p.K) (state : BootstrapPhysicalBlock.State p) (t : Fin p.T) :
    Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      BootstrapCoordinatorLocalRound.coordinatorArmChoice p z.1 target state t z.2) := by
  let key : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar → ArmChoiceKey p := fun z =>
    (BootstrapCoordinatorLocalRound.coordinatorSlot p z.1 t,
      (BootstrapCoordinatorLocalRound.coordinatorTupleArm p z.1 t,
        (BootstrapCoordinatorLocalRound.localForwardProduct p z.1 state t,
          (BootstrapPrivateRoundStreams.fullArmScalarDraw p z.2,
            (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p target z.2).val))))
  have hslot : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      BootstrapCoordinatorLocalRound.coordinatorSlot p z.1 t) := by
    change Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      PublicDiscreteDraws.slotDraw (z.1.2 t).1)
    have htime : Measurable (fun z : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.Scalar => (z.1, t)) :=
      measurable_fst.prodMk (measurable_const : Measurable
        (fun _ : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.Scalar => t))
    exact measurable_slotDraw.comp ((measurable_rowTimeSlice p).comp htime)
  have htuple : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      BootstrapCoordinatorLocalRound.coordinatorTupleArm p z.1 t) := by
    change Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (z.1.2 t).1).val
        (ActiveRoundActions.coordinator p.two_le_m))
    have htime : Measurable (fun z : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.Scalar => (z.1, t)) :=
      measurable_fst.prodMk (measurable_const : Measurable
        (fun _ : CompletePublicTable.CompleteRow p ×
          BootstrapPrivateRoundStreams.Scalar => t))
    exact (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp
        ((OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp
          ((measurable_rowTimeSlice p).comp htime)))
  have hforward : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      BootstrapCoordinatorLocalRound.localForwardProduct p z.1 state t) := by
    change Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      forwardProductFromFields p z.1.1 state.list t)
    have hfield : Measurable (fun z : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.Scalar =>
        (z.1, (state.list, t))) :=
      measurable_fst.prodMk (measurable_const.prodMk measurable_const)
    exact (measurable_forwardProduct_joint p).comp hfield
  have hfull : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      BootstrapPrivateRoundStreams.fullArmScalarDraw p z.2) :=
    BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p |>.comp measurable_snd
  have havoid : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar =>
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p target z.2).val) := by
    exact (measurable_subtype_coe.comp
      (BootstrapPrivateRoundStreams.measurable_forbiddenArmScalarDraw p target)).comp
        measurable_snd
  have hkey : Measurable key :=
    hslot.prodMk (htuple.prodMk (hforward.prodMk (hfull.prodMk havoid)))
  have hfactor : ∀ x y, key x = key y →
      BootstrapCoordinatorLocalRound.coordinatorArmChoice p x.1 target state t x.2 =
        BootstrapCoordinatorLocalRound.coordinatorArmChoice p y.1 target state t y.2 := by
    intro x y h
    have hs := congrArg Prod.fst h
    have ht := congrArg (fun z => z.2.1) h
    have hf := congrArg (fun z => z.2.2.1) h
    have hu := congrArg (fun z => z.2.2.2.1) h
    have hv := congrArg (fun z => z.2.2.2.2) h
    simp only [key] at hs ht hf hu hv
    simp [BootstrapCoordinatorLocalRound.coordinatorArmChoice, hs, ht, hf, hu, hv]
  exact measurable_of_countable_key key hkey _ hfactor

/-- Joint measurability in the original complete row, private arm scalar, and
the separate countable target/list/mode/time inputs. -/
theorem measurable_coordinatorArmChoice_joint (p : Parameters) :
    Measurable (fun z : (CompletePublicTable.CompleteRow p ×
      BootstrapPrivateRoundStreams.Scalar) ×
      (Fin p.K × (CoordinatorStateCode p × Fin p.T)) =>
        BootstrapCoordinatorLocalRound.coordinatorArmChoice p z.1.1 z.2.1
          (coordinatorStateOfCode p z.2.2.1) z.2.2.2 z.1.2) := by
  apply measurable_from_prod_countable_left
  intro q
  cases q with
  | mk target rest =>
    cases rest with
    | mk state t =>
      change Measurable (fun z : CompletePublicTable.CompleteRow p ×
        BootstrapPrivateRoundStreams.Scalar =>
          BootstrapCoordinatorLocalRound.coordinatorArmChoice p z.1 target
            (coordinatorStateOfCode p state) t z.2)
      exact measurable_coordinatorArmChoice_at_time p target
        (coordinatorStateOfCode p state) t

/-- A source-faithful round input: block-time is a genuine restricted domain,
while the continuous row, ID array, and fixed constants remain in their own
base coordinate. -/
structure CoordinatorRoundInput (p : Parameters) where
  base : CoordinatorContinuousBase p
  localState : CoordinatorLocalCode p
  round : Fin p.T
  round_mem : round ∈ calendarBlock p localState.block

def coordinatorRoundInputCoordinates (p : Parameters)
    (input : CoordinatorRoundInput p) :
    CoordinatorContinuousBase p × (CoordinatorLocalCode p × Fin p.T) :=
  (input.base, (input.localState, input.round))

instance coordinatorRoundInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorRoundInput p) :=
  MeasurableSpace.comap (coordinatorRoundInputCoordinates p) inferInstance

theorem measurable_coordinatorRoundInputCoordinates (p : Parameters) :
    Measurable (coordinatorRoundInputCoordinates p) :=
  comap_measurable (coordinatorRoundInputCoordinates p)

theorem measurable_assembleCoordinatorInput (p : Parameters) :
    Measurable (fun input : CoordinatorRoundInput p =>
      assemblePrelaunch p input.base input.localState) := by
  apply (measurable_comap_iff).2
  have hcoord := measurable_coordinatorRoundInputCoordinates p
  have hbase : Measurable (fun input : CoordinatorRoundInput p => input.base) :=
    measurable_fst.comp hcoord
  have hlocal : Measurable (fun input : CoordinatorRoundInput p => input.localState) :=
    measurable_fst.comp (measurable_snd.comp hcoord)
  simpa [Function.comp_def, assemblePrelaunch_coordinates] using hbase.prodMk hlocal

def coordinatorPreparedRound (p : Parameters) (input : CoordinatorRoundInput p)
    (ownArmScalar : BootstrapPrivateRoundStreams.Scalar) :
    BootstrapCoordinatorLocalRound.PreparedRound p :=
  BootstrapCoordinatorLocalRound.prepare p (assemblePrelaunch p input.base input.localState)
    input.round input.round_mem ownArmScalar

/-- Countable output code for the existing `PreparedRound`. Its before-state
code contains every local field; row, IDs, and constants stay in the original
base. The restricted round proof is retained by `CoordinatorRoundInput`. -/
abbrev PreparedRoundCode (p : Parameters) :=
  CoordinatorLocalCode p × (Fin p.T × Fin p.K)

instance preparedRoundCodeCountable (p : Parameters) : Countable (PreparedRoundCode p) :=
  inferInstance

def encodePreparedRound (p : Parameters) (prepared :
    BootstrapCoordinatorLocalRound.PreparedRound p) : PreparedRoundCode p :=
  ((prelaunchCoordinates p prepared.before).2,
    (prepared.round, prepared.arm))

def reconstructPreparedRound (p : Parameters) (input : CoordinatorRoundInput p)
    (code : PreparedRoundCode p) : Option (BootstrapCoordinatorLocalRound.PreparedRound p) :=
  if hlocal : code.1 = input.localState then
    if hround : code.2.1 = input.round then
      have hblock : code.1.block = input.localState.block :=
        congrArg CoordinatorLocalCode.block hlocal
      have hmem : input.round ∈ calendarBlock p code.1.block := by
        rw [hblock]
        exact input.round_mem
      some ⟨assemblePrelaunch p input.base code.1, input.round, hmem, code.2.2⟩
    else none
  else none

def coordinatorPreparedRoundCode (p : Parameters) (input : CoordinatorRoundInput p)
    (ownArmScalar : BootstrapPrivateRoundStreams.Scalar) : PreparedRoundCode p :=
  encodePreparedRound p (coordinatorPreparedRound p input ownArmScalar)

theorem reconstruct_coordinatorPreparedRoundCode (p : Parameters)
    (input : CoordinatorRoundInput p)
    (ownArmScalar : BootstrapPrivateRoundStreams.Scalar) :
    reconstructPreparedRound p input
      (coordinatorPreparedRoundCode p input ownArmScalar) =
        some (coordinatorPreparedRound p input ownArmScalar) := by
  have hcoordinates :
      prelaunchCoordinates p
          (assemblePrelaunch p input.base input.localState) =
        (input.base, input.localState) :=
    assemblePrelaunch_coordinates p input.base input.localState
  have hlocal :
      (prelaunchCoordinates p (coordinatorPreparedRound p input ownArmScalar).before).2 =
        input.localState := by
    change (prelaunchCoordinates p
      (assemblePrelaunch p input.base input.localState)).2 = input.localState
    rw [hcoordinates]
  have hround :
      (coordinatorPreparedRound p input ownArmScalar).round = input.round := rfl
  have hencoded :
      coordinatorPreparedRoundCode p input ownArmScalar =
        Prod.mk input.localState
          (Prod.mk input.round (coordinatorPreparedRound p input ownArmScalar).arm) := by
    simp [coordinatorPreparedRoundCode, encodePreparedRound, coordinatorPreparedRound,
      BootstrapCoordinatorLocalRound.prepare, assemblePrelaunch_coordinates]
  rw [hencoded]
  simp [reconstructPreparedRound, coordinatorPreparedRound,
    BootstrapCoordinatorLocalRound.prepare]

theorem measurable_coordinatorPreparedRoundCode (p : Parameters) :
    Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      coordinatorPreparedRoundCode p z.1 z.2) := by
  let localMap := fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
    z.1.localState
  let roundMap := fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
    z.1.round
  let armInput := fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
    Prod.mk (Prod.mk z.1.base.1.1 z.2)
      (Prod.mk z.1.localState.target
        (Prod.mk z.1.localState.coordinator z.1.round))
  have hcoords : Measurable (coordinatorRoundInputCoordinates p ∘ Prod.fst) :=
    (measurable_coordinatorRoundInputCoordinates p).comp
      (measurable_fst : Measurable
        (Prod.fst : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar →
          CoordinatorRoundInput p))
  have hlocal : Measurable localMap := by
    change Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorRoundInputCoordinates p z.1).2.1)
    exact measurable_fst.comp (measurable_snd.comp hcoords)
  have hround : Measurable roundMap := by
    change Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorRoundInputCoordinates p z.1).2.2)
    exact measurable_snd.comp (measurable_snd.comp hcoords)
  have hbase : Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorRoundInputCoordinates p z.1).1) := measurable_fst.comp hcoords
  have hrow : Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorRoundInputCoordinates p z.1).1.1.1) :=
    measurable_fst.comp (measurable_fst.comp hbase)
  have hlocalTargetCode : Measurable (fun c : CoordinatorLocalCode p => c.target) :=
    measurable_of_countable _
  have hlocalStateCode : Measurable (fun c : CoordinatorLocalCode p => c.coordinator) :=
    measurable_of_countable _
  have hlocalTarget : Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorRoundInputCoordinates p z.1).2.1.target) :=
    hlocalTargetCode.comp hlocal
  have hlocalState : Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorRoundInputCoordinates p z.1).2.1.coordinator) :=
    hlocalStateCode.comp hlocal
  have harmInput : Measurable armInput := by
    change Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      Prod.mk (Prod.mk ((coordinatorRoundInputCoordinates p z.1).1.1.1) z.2)
        (Prod.mk ((coordinatorRoundInputCoordinates p z.1).2.1.target)
          (Prod.mk ((coordinatorRoundInputCoordinates p z.1).2.1.coordinator)
            ((coordinatorRoundInputCoordinates p z.1).2.2)))
      )
    exact (hrow.prodMk measurable_snd).prodMk
      (hlocalTarget.prodMk (hlocalState.prodMk hround))
  have harm : Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (coordinatorPreparedRound p z.1 z.2).arm) := by
    change Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      BootstrapCoordinatorLocalRound.coordinatorArmChoice p
        (coordinatorRoundInputCoordinates p z.1).1.1.1
        (coordinatorRoundInputCoordinates p z.1).2.1.target
        (coordinatorStateOfCode p (coordinatorRoundInputCoordinates p z.1).2.1.coordinator)
        (coordinatorRoundInputCoordinates p z.1).2.2 z.2)
    exact (measurable_coordinatorArmChoice_joint p).comp harmInput
  let armMap := fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
    (coordinatorPreparedRound p z.1 z.2).arm
  have harmMap : Measurable armMap := harm
  have hcode : Measurable (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      (localMap z, (roundMap z, armMap z))) :=
    hlocal.prodMk (hround.prodMk harmMap)
  have heq : (fun z : CoordinatorRoundInput p × BootstrapPrivateRoundStreams.Scalar =>
      coordinatorPreparedRoundCode p z.1 z.2) = fun z =>
        (localMap z, (roundMap z, armMap z)) := by
    funext z
    dsimp [coordinatorPreparedRoundCode, encodePreparedRound, coordinatorPreparedRound,
      localMap, roundMap, armMap]
    apply Prod.ext
    · change (prelaunchCoordinates p
        (assemblePrelaunch p z.1.base z.1.localState)).2 = z.1.localState
      rw [assemblePrelaunch_coordinates]
    · apply Prod.ext <;> rfl
  rw [heq]
  exact hcode

/-- The actual DOWN-positive arm credit is measurable in the original row,
physical round, and separate denominator-D feedback. -/
theorem measurable_downCreditArm_joint (p : Parameters) :
    Measurable (fun z : (CompletePublicTable.CompleteRow p × Fin p.T) ×
      Fin (D p + 1) =>
        BootstrapCoordinatorLocalRound.downCreditArm p z.1.1 z.1.2 z.2) := by
  let key := fun z : (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
    (BootstrapCoordinatorLocalRound.coordinatorSlot p z.1.1 z.1.2,
      (BootstrapCoordinatorLocalRound.coordinatorTupleArm p z.1.1 z.1.2, z.2))
  have hrowTime : Measurable (fun z :
      (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) => z.1) :=
    measurable_fst
  have hslot : Measurable (fun z :
      (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
        BootstrapCoordinatorLocalRound.coordinatorSlot p z.1.1 z.1.2) :=
    (measurable_coordinatorSlot_joint p).comp hrowTime
  have htuple : Measurable (fun z :
      (CompletePublicTable.CompleteRow p × Fin p.T) × Fin (D p + 1) =>
        BootstrapCoordinatorLocalRound.coordinatorTupleArm p z.1.1 z.1.2) :=
    (measurable_coordinatorTupleArm_joint p).comp hrowTime
  have hkey : Measurable key := hslot.prodMk (htuple.prodMk measurable_snd)
  have hfactor : ∀ x y, key x = key y →
      BootstrapCoordinatorLocalRound.downCreditArm p x.1.1 x.1.2 x.2 =
        BootstrapCoordinatorLocalRound.downCreditArm p y.1.1 y.1.2 y.2 := by
    intro x y h
    have hs := congrArg Prod.fst h
    have ha := congrArg (fun q => q.2.1) h
    have hy := congrArg (fun q => q.2.2) h
    simp only [key] at hs ha hy
    simp [BootstrapCoordinatorLocalRound.downCreditArm, hs, ha, hy]
  exact measurable_of_countable_key key hkey _ hfactor

/-- The list retained by the literal positive-DISCOVER update, keyed by the
entire finite ID array and round. -/
def coordinatorFilteredList (p : Parameters)
    (ids : CompletePublicTable.IDArray p) (list : Finset (Fin (A_id p)))
    (t : Fin p.T) : Finset (Fin (A_id p)) :=
  list.filter (fun u => ids u t = true)

/-- A countable input key for the literal observation update: the actual slot,
whole finite ID array, encoded coordinator state, calendar time and feedback. -/
abbrev CoordinatorObservationKey (p : Parameters) :=
  PublicDiscreteDraws.Slot ×
    (CompletePublicTable.IDArray p ×
      (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1))))

theorem measurable_observationUpdateCode_joint (p : Parameters) :
    Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) =>
      coordinatorStateCode p
        (BootstrapCoordinatorLocalRound.observationUpdate p z.1 z.2.1
          (coordinatorStateOfCode p z.2.2.1) z.2.2.2.1 z.2.2.2.2)) := by
  let key : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) →
        CoordinatorObservationKey p := fun z =>
    (BootstrapCoordinatorLocalRound.coordinatorSlot p z.1 z.2.2.2.1,
      (z.2.1, (z.2.2.1, z.2.2.2)))
  have hrowTime : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) =>
        (z.1, z.2.2.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_snd)))
  have hslot : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) =>
        BootstrapCoordinatorLocalRound.coordinatorSlot p z.1 z.2.2.2.1) :=
    (measurable_coordinatorSlot_joint p).comp hrowTime
  have hids : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hstate : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) => z.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have htime : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) => z.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hfeedback : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) => z.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hkey : Measurable key :=
    hslot.prodMk (hids.prodMk (hstate.prodMk (htime.prodMk hfeedback)))
  have hfactor : ∀ x y, key x = key y →
      coordinatorStateCode p
        (BootstrapCoordinatorLocalRound.observationUpdate p x.1 x.2.1
          (coordinatorStateOfCode p x.2.2.1) x.2.2.2.1 x.2.2.2.2) =
      coordinatorStateCode p
        (BootstrapCoordinatorLocalRound.observationUpdate p y.1 y.2.1
          (coordinatorStateOfCode p y.2.2.1) y.2.2.2.1 y.2.2.2.2) := by
    intro x y h
    have hs := congrArg Prod.fst h
    have hi := congrArg (fun q => q.2.1) h
    have hl := congrArg (fun q => q.2.2.1) h
    have ht := congrArg (fun q => q.2.2.2.1) h
    have hy := congrArg (fun q => q.2.2.2.2) h
    simp only [key] at hs hi hl ht hy
    have hs' : BootstrapCoordinatorLocalRound.coordinatorSlot p x.1 y.2.2.2.1 =
        BootstrapCoordinatorLocalRound.coordinatorSlot p y.1 y.2.2.2.1 := by
      simpa only [ht] using hs
    simp [BootstrapCoordinatorLocalRound.observationUpdate, hs', hi, hl, ht, hy]
  exact measurable_of_countable_key key hkey _ hfactor

/-- Measurability of the literal coordinator list/mode/audit update, with its
finite state measured through the lossless field code. -/
theorem measurable_observationUpdate_joint (p : Parameters) :
    Measurable (fun z : CompletePublicTable.CompleteRow p ×
      (CompletePublicTable.IDArray p ×
        (CoordinatorStateCode p × (Fin p.T × Fin (D p + 1)))) =>
      BootstrapCoordinatorLocalRound.observationUpdate p z.1 z.2.1
        (coordinatorStateOfCode p z.2.2.1) z.2.2.2.1 z.2.2.2.2) := by
  apply (measurable_comap_iff).2
  simpa [Function.comp_def] using measurable_observationUpdateCode_joint p

/-- Joint measurability of the literal post-DOWN-credit counters. -/
theorem measurable_countersAfterObservation_joint (p : Parameters) :
    Measurable (fun z : CompletePublicTable.CompleteRow p ×
      ((Fin p.K → ℕ) × (Fin p.T × Fin (D p + 1))) =>
        BootstrapCoordinatorLocalRound.countersAfterObservation p z.1 z.2.1
          z.2.2.1 z.2.2.2) := by
  let key := fun z : CompletePublicTable.CompleteRow p ×
      ((Fin p.K → ℕ) × (Fin p.T × Fin (D p + 1))) =>
    (BootstrapCoordinatorLocalRound.coordinatorSlot p z.1 z.2.2.1,
      (BootstrapCoordinatorLocalRound.coordinatorTupleArm p z.1 z.2.2.1,
        (z.2.1, z.2.2)))
  have hrowTime : Measurable (fun z : CompletePublicTable.CompleteRow p ×
      ((Fin p.K → ℕ) × (Fin p.T × Fin (D p + 1))) => (z.1, z.2.2.1)) :=
    measurable_fst.prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hslot := (measurable_coordinatorSlot_joint p).comp hrowTime
  have htuple := (measurable_coordinatorTupleArm_joint p).comp hrowTime
  have hkey : Measurable key :=
    hslot.prodMk (htuple.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_snd)))
  have hfactor : ∀ x y, key x = key y →
      BootstrapCoordinatorLocalRound.countersAfterObservation p x.1 x.2.1
          x.2.2.1 x.2.2.2 =
        BootstrapCoordinatorLocalRound.countersAfterObservation p y.1 y.2.1
          y.2.2.1 y.2.2.2 := by
    intro x y h
    have hs := congrArg Prod.fst h
    have ha := congrArg (fun q => q.2.1) h
    have hc := congrArg (fun q => q.2.2.1) h
    have ht := congrArg (fun q => q.2.2.2.1) h
    have hy := congrArg (fun q => q.2.2.2.2) h
    simp only [key] at hs ha hc ht hy
    have hs' : BootstrapCoordinatorLocalRound.coordinatorSlot p x.1 y.2.2.1 =
        BootstrapCoordinatorLocalRound.coordinatorSlot p y.1 y.2.2.1 := by
      simpa only [ht] using hs
    have ha' : BootstrapCoordinatorLocalRound.coordinatorTupleArm p x.1 y.2.2.1 =
        BootstrapCoordinatorLocalRound.coordinatorTupleArm p y.1 y.2.2.1 := by
      simpa only [ht] using ha
    simp [BootstrapCoordinatorLocalRound.countersAfterObservation,
      BootstrapCoordinatorLocalRound.downCreditArm, hs', ha', hc, ht, hy]
  exact measurable_of_countable_key key hkey _ hfactor

/-- A fixed-constant round input constrains both real coordinates to the same
external source constants used by the strict launch test. -/
structure CoordinatorFixedRoundInput (p : Parameters) (C_star C_h : ℝ) where
  input : CoordinatorRoundInput p
  constants : input.base.2 = (C_star, C_h)

def coordinatorFixedRoundInputProjection (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorFixedRoundInput p C_star C_h) : CoordinatorRoundInput p :=
  input.input

instance coordinatorFixedRoundInputMeasurableSpace (p : Parameters)
    (C_star C_h : ℝ) :
    MeasurableSpace (CoordinatorFixedRoundInput p C_star C_h) :=
  MeasurableSpace.comap (coordinatorFixedRoundInputProjection p C_star C_h) inferInstance

theorem measurable_coordinatorFixedRoundInputProjection (p : Parameters)
    (C_star C_h : ℝ) :
    Measurable (coordinatorFixedRoundInputProjection p C_star C_h) :=
  comap_measurable _

/-- The literal strict launch decision after the current observation's DOWN
credit, on a domain where `C_star` and `C_h` are the same fixed constants. -/
def coordinatorLaunchDecision (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorFixedRoundInput p C_star C_h)
    (feedback : Fin (D p + 1)) : Bool :=
  let before := assemblePrelaunch p input.input.base input.input.localState
  BootstrapCoordinatorLocalRound.launchDecision p before.data before.monitor
    input.input.round feedback

theorem measurable_coordinatorLaunchDecision (p : Parameters) (C_star C_h : ℝ) :
    Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h × Fin (D p + 1) =>
      coordinatorLaunchDecision p C_star C_h z.1 z.2) := by
  let key := fun z : CoordinatorFixedRoundInput p C_star C_h × Fin (D p + 1) =>
    (BootstrapCoordinatorLocalRound.coordinatorSlot p
        z.1.input.base.1.1 z.1.input.round,
      (BootstrapCoordinatorLocalRound.coordinatorTupleArm p
          z.1.input.base.1.1 z.1.input.round,
        (z.1.input.localState.monitor.1.counters,
          (z.1.input.round, z.2))))
  have hfixed : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => z.1.input) :=
    (measurable_coordinatorFixedRoundInputProjection p C_star C_h).comp measurable_fst
  have hcoords : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => coordinatorRoundInputCoordinates p (z.1.input)) :=
    (measurable_coordinatorRoundInputCoordinates p).comp hfixed
  have hbase : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => (coordinatorRoundInputCoordinates p z.1.input).1) :=
    measurable_fst.comp hcoords
  have hrow : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => (coordinatorRoundInputCoordinates p z.1.input).1.1.1) :=
    measurable_fst.comp (measurable_fst.comp hbase)
  have htime : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => (coordinatorRoundInputCoordinates p z.1.input).2.2) :=
    measurable_snd.comp (measurable_snd.comp hcoords)
  have hrowTime := hrow.prodMk htime
  have hslot : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => BootstrapCoordinatorLocalRound.coordinatorSlot p
        z.1.input.base.1.1 z.1.input.round) :=
    (measurable_coordinatorSlot_joint p).comp hrowTime
  have htuple : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => BootstrapCoordinatorLocalRound.coordinatorTupleArm p
        z.1.input.base.1.1 z.1.input.round) :=
    (measurable_coordinatorTupleArm_joint p).comp hrowTime
  have hlocal : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => (coordinatorRoundInputCoordinates p z.1.input).2.1) :=
    measurable_fst.comp (measurable_snd.comp hcoords)
  have hlocalCounters : Measurable (fun c : CoordinatorLocalCode p => c.monitor.1.counters) :=
    measurable_of_countable _
  have hcounter : Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => z.1.input.localState.monitor.1.counters) := by
    change Measurable (fun z : CoordinatorFixedRoundInput p C_star C_h ×
      Fin (D p + 1) => ((coordinatorRoundInputCoordinates p z.1.input).2.1).monitor.1.counters)
    exact hlocalCounters.comp hlocal
  have hkey : Measurable key :=
    hslot.prodMk (htuple.prodMk (hcounter.prodMk (htime.prodMk measurable_snd)))
  have hfactor : ∀ x y, key x = key y →
      coordinatorLaunchDecision p C_star C_h x.1 x.2 =
        coordinatorLaunchDecision p C_star C_h y.1 y.2 := by
    intro x y h
    have hs := congrArg Prod.fst h
    have ha := congrArg (fun q => q.2.1) h
    have hc := congrArg (fun q => q.2.2.1) h
    have ht := congrArg (fun q => q.2.2.2.1) h
    have hy := congrArg (fun q => q.2.2.2.2) h
    simp only [key] at hs ha hc ht hy
    have hs' : BootstrapCoordinatorLocalRound.coordinatorSlot p
        x.1.input.base.1.1 y.1.input.round =
      BootstrapCoordinatorLocalRound.coordinatorSlot p
        y.1.input.base.1.1 y.1.input.round := by simpa only [ht] using hs
    have ha' : BootstrapCoordinatorLocalRound.coordinatorTupleArm p
        x.1.input.base.1.1 y.1.input.round =
      BootstrapCoordinatorLocalRound.coordinatorTupleArm p
        y.1.input.base.1.1 y.1.input.round := by simpa only [ht] using ha
    have hxconst : x.1.input.base.2 = (C_star, C_h) := x.1.constants
    have hyconst : y.1.input.base.2 = (C_star, C_h) := y.1.constants
    simp [coordinatorLaunchDecision, BootstrapCoordinatorLocalRound.launchDecision,
      BootstrapCoordinatorLocalRound.launchTest,
      BootstrapCoordinatorLocalRound.countersAfterObservation,
      BootstrapCoordinatorLocalRound.downCreditArm, assemblePrelaunch,
      monitorStateOfCode, hs', ha', hc, ht, hy, hxconst, hyconst]
  exact measurable_of_countable_key key hkey _ hfactor

/-- Separate coordinator inputs for the local physical-round operation. The
arm scalar and denominator-D feedback remain distinct coordinates. -/
structure CoordinatorObserveInput (p : Parameters) (C_star C_h : ℝ) where
  fixed : CoordinatorFixedRoundInput p C_star C_h
  ownArmScalar : BootstrapPrivateRoundStreams.Scalar
  feedback : Fin (D p + 1)

def coordinatorObserveInputCoordinates (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorObserveInput p C_star C_h) :
    CoordinatorFixedRoundInput p C_star C_h ×
      (BootstrapPrivateRoundStreams.Scalar × Fin (D p + 1)) :=
  (input.fixed, (input.ownArmScalar, input.feedback))

instance coordinatorObserveInputMeasurableSpace (p : Parameters)
    (C_star C_h : ℝ) : MeasurableSpace (CoordinatorObserveInput p C_star C_h) :=
  MeasurableSpace.comap (coordinatorObserveInputCoordinates p C_star C_h) inferInstance

theorem measurable_coordinatorObserveInputCoordinates (p : Parameters)
    (C_star C_h : ℝ) :
    Measurable (coordinatorObserveInputCoordinates p C_star C_h) :=
  comap_measurable _

/-- Countable code for every output-local field and continuation constructor.
The complete row, ID array, constants, and time remain in the original input. -/
structure CoordinatorObservationCode (p : Parameters) where
  arm : Fin p.K
  block : Fin (n_boot p)
  target : Fin p.K
  coordinator : CoordinatorStateCode p
  monitor : MonitorCode p
  trigger : Option (Fin p.T)

def coordinatorObservationCodeFields (p : Parameters)
    (code : CoordinatorObservationCode p) :
    Fin p.K × (Fin (n_boot p) ×
      (Fin p.K × (CoordinatorStateCode p × (MonitorCode p × Option (Fin p.T))))) :=
  (code.arm, (code.block, (code.target,
    (code.coordinator, (code.monitor, code.trigger)))))

theorem coordinatorObservationCodeFields_injective (p : Parameters) :
    Function.Injective (coordinatorObservationCodeFields p) := by
  intro a b h
  cases a
  cases b
  simp_all [coordinatorObservationCodeFields]

instance coordinatorObservationCodeCountable (p : Parameters) :
    Countable (CoordinatorObservationCode p) :=
  (coordinatorObservationCodeFields_injective p).countable

instance coordinatorObservationCodeMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorObservationCode p) :=
  MeasurableSpace.comap (coordinatorObservationCodeFields p) inferInstance

def coordinatorObservationDataOfCode (p : Parameters)
    (base : CoordinatorContinuousBase p) (code : CoordinatorObservationCode p) :
    BootstrapCoordinatorLocalRound.LocalData p :=
  ⟨code.block, base.1.1, base.1.2, code.target,
    coordinatorStateOfCode p code.coordinator, base.2.1, base.2.2⟩

/-- Decode only validated continuation tags. Every launched witness is rebuilt
from the original round's block membership and the actual strict source
threshold; invalid codes return `none`, never a fabricated fallback state. -/
def reconstructCoordinatorObservationCode (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorFixedRoundInput p C_star C_h)
    (code : CoordinatorObservationCode p) :
    Option (BootstrapCoordinatorLocalRound.ObservationResult p) := by
  classical
  have hCstar : input.input.base.2.1 = C_star := congrArg Prod.fst input.constants
  have hCh : input.input.base.2.2 = C_h := congrArg Prod.snd input.constants
  exact if hblock : code.block = input.input.localState.block then
    if htarget : code.target = input.input.localState.target then
      if hpre : code.trigger = none then
        if hcross : code.monitor.crossingBlock = none then
          if hposition : code.monitor.launchPosition = p.T then
            some ⟨code.arm, .prelaunch
              ⟨coordinatorObservationDataOfCode p input.input.base code,
                ⟨monitorStateOfCode p code.monitor, by
                  simpa [monitorStateOfCode] using hcross,
                  by simpa [monitorStateOfCode] using hposition⟩⟩⟩
          else none
        else none
      else if htrigger : code.trigger = some input.input.round then
        have hmem : input.input.round ∈ calendarBlock p code.block := by
          rw [hblock]
          exact input.input.round_mem
        if hend : BootstrapLaunchMonitor.calendarBlockEnd p input.input.round then
          if hcross : code.monitor.crossingBlock = some code.block then
            if hposition : code.monitor.launchPosition = manuscriptRound p input.input.round then
              if hthreshold : BootstrapLaunchMonitor.monitorValue p code.monitor.counters >
                  4 * BootstrapStartupCostScale.Q C_star C_h p then
                some ⟨code.arm, .launched
                  ⟨coordinatorObservationDataOfCode p input.input.base code,
                    input.input.round, hmem, monitorStateOfCode p code.monitor,
                    by simpa [monitorStateOfCode,
                      coordinatorObservationDataOfCode] using hcross,
                    hend, by simpa [monitorStateOfCode,
                      coordinatorObservationDataOfCode, hCstar, hCh] using hthreshold,
                    by simpa [monitorStateOfCode,
                      coordinatorObservationDataOfCode] using hposition⟩⟩
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- The literal existing local `observe (prepare ...)` result. -/
def coordinatorObserveResult (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorObserveInput p C_star C_h) :
    BootstrapCoordinatorLocalRound.ObservationResult p :=
  BootstrapCoordinatorLocalRound.observe
    (coordinatorPreparedRound p input.fixed.input input.ownArmScalar) input.feedback

/-- Direct countable encoding of `observe (prepare ...)`, preserving the arm
chosen before feedback and encoding the post-credit continuation. -/
def coordinatorObserveCode (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorObserveInput p C_star C_h) : CoordinatorObservationCode p := by
  let prepared := coordinatorPreparedRound p input.fixed.input input.ownArmScalar
  let before := prepared.before
  let updated := BootstrapCoordinatorLocalRound.observationUpdate p
    before.data.row before.data.ids before.data.coordinator prepared.round input.feedback
  let counters := BootstrapCoordinatorLocalRound.countersAfterObservation p
    before.data.row before.monitor.1.counters prepared.round input.feedback
  let launched := coordinatorLaunchDecision p C_star C_h input.fixed input.feedback
  exact ⟨prepared.arm, before.data.block, before.data.target,
    coordinatorStateCode p updated,
    ⟨counters,
      (if launched then some before.data.block else none),
      (if launched then manuscriptRound p prepared.round else p.T)⟩,
    if launched then some prepared.round else none⟩

theorem measurable_coordinatorObserveCode (p : Parameters) (C_star C_h : ℝ) :
    Measurable (fun input : CoordinatorObserveInput p C_star C_h =>
      coordinatorObserveCode p C_star C_h input) := by
  let hcoords := measurable_coordinatorObserveInputCoordinates p C_star C_h
  let hfixed : Measurable (fun z : CoordinatorObserveInput p C_star C_h => z.fixed) :=
    measurable_fst.comp hcoords
  let hroundInput : Measurable
      (fun z : CoordinatorObserveInput p C_star C_h => z.fixed.input) :=
    (measurable_coordinatorFixedRoundInputProjection p C_star C_h).comp hfixed
  let hscalar : Measurable
      (fun z : CoordinatorObserveInput p C_star C_h => z.ownArmScalar) :=
    measurable_fst.comp (measurable_snd.comp hcoords)
  let hfeedback : Measurable
      (fun z : CoordinatorObserveInput p C_star C_h => z.feedback) :=
    measurable_snd.comp (measurable_snd.comp hcoords)
  let hroundCoords := (measurable_coordinatorRoundInputCoordinates p).comp hroundInput
  let hbase : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      (coordinatorRoundInputCoordinates p z.fixed.input).1) := measurable_fst.comp hroundCoords
  let hrow : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      (coordinatorRoundInputCoordinates p z.fixed.input).1.1.1) :=
    measurable_fst.comp (measurable_fst.comp hbase)
  let hids : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      (coordinatorRoundInputCoordinates p z.fixed.input).1.1.2) :=
    measurable_snd.comp (measurable_fst.comp hbase)
  let hlocal : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      (coordinatorRoundInputCoordinates p z.fixed.input).2.1) :=
    measurable_fst.comp (measurable_snd.comp hroundCoords)
  let htime : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      (coordinatorRoundInputCoordinates p z.fixed.input).2.2) :=
    measurable_snd.comp (measurable_snd.comp hroundCoords)
  let hlocalBlock : Measurable (fun c : CoordinatorLocalCode p => c.block) :=
    measurable_of_countable _
  let hlocalTarget : Measurable (fun c : CoordinatorLocalCode p => c.target) :=
    measurable_of_countable _
  let blockMap := fun z : CoordinatorObserveInput p C_star C_h =>
    (coordinatorRoundInputCoordinates p z.fixed.input).2.1.block
  let targetMap := fun z : CoordinatorObserveInput p C_star C_h =>
    (coordinatorRoundInputCoordinates p z.fixed.input).2.1.target
  have hblock : Measurable blockMap := hlocalBlock.comp hlocal
  have htarget : Measurable targetMap := hlocalTarget.comp hlocal
  let hpreparedInput : Measurable
      (fun z : CoordinatorObserveInput p C_star C_h =>
        (z.fixed.input, z.ownArmScalar)) := hroundInput.prodMk hscalar
  let hpreparedCode :=
    (measurable_coordinatorPreparedRoundCode p).comp hpreparedInput
  let armMap := fun z : CoordinatorObserveInput p C_star C_h =>
    (coordinatorPreparedRound p z.fixed.input z.ownArmScalar).arm
  have harm : Measurable armMap :=
    measurable_snd.comp (measurable_snd.comp hpreparedCode)
  let hstate : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      (coordinatorRoundInputCoordinates p z.fixed.input).2.1.coordinator) := by
    let hstateCode : Measurable (fun c : CoordinatorLocalCode p => c.coordinator) :=
      measurable_of_countable _
    exact hstateCode.comp hlocal
  let htimeFeedback := htime.prodMk hfeedback
  let hrowTime := hrow.prodMk htime
  let hslot := (measurable_coordinatorSlot_joint p).comp hrowTime
  let htuple := (measurable_coordinatorTupleArm_joint p).comp hrowTime
  let hupdateInput : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.1,
        ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.2,
          ((coordinatorRoundInputCoordinates p z.fixed.input).2.1.coordinator,
            ((coordinatorRoundInputCoordinates p z.fixed.input).2.2, z.feedback))))) :=
    hrow.prodMk (hids.prodMk (hstate.prodMk htimeFeedback))
  let hupdatedState :=
    (measurable_observationUpdateCode_joint p).comp hupdateInput
  let hmonitorCountersCode : Measurable
      (fun c : CoordinatorLocalCode p => c.monitor.1.counters) := measurable_of_countable _
  let counterMap := fun z : CoordinatorObserveInput p C_star C_h =>
    (coordinatorRoundInputCoordinates p z.fixed.input).2.1.monitor.1.counters
  have hcounter : Measurable counterMap := hmonitorCountersCode.comp hlocal
  let hcounterInput : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.1,
        (counterMap z,
          ((coordinatorRoundInputCoordinates p z.fixed.input).2.2, z.feedback)))) :=
    hrow.prodMk (hcounter.prodMk htimeFeedback)
  have hupdatedCounters : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      BootstrapCoordinatorLocalRound.countersAfterObservation p
        ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.1)
        (counterMap z) ((coordinatorRoundInputCoordinates p z.fixed.input).2.2) z.feedback) :=
    (measurable_countersAfterObservation_joint p).comp hcounterInput
  let hlaunchInput := hfixed.prodMk hfeedback
  have hlaunch : Measurable (fun z : CoordinatorObserveInput p C_star C_h =>
      coordinatorLaunchDecision p C_star C_h z.fixed z.feedback) :=
    (measurable_coordinatorLaunchDecision p C_star C_h).comp hlaunchInput
  let updatedCounterMap := fun z : CoordinatorObserveInput p C_star C_h =>
    BootstrapCoordinatorLocalRound.countersAfterObservation p
      ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.1)
      (counterMap z) ((coordinatorRoundInputCoordinates p z.fixed.input).2.2) z.feedback
  let launchMap := fun z : CoordinatorObserveInput p C_star C_h =>
    coordinatorLaunchDecision p C_star C_h z.fixed z.feedback
  let timeMap := fun z : CoordinatorObserveInput p C_star C_h =>
    (coordinatorRoundInputCoordinates p z.fixed.input).2.2
  let feedbackMap := fun z : CoordinatorObserveInput p C_star C_h => z.feedback
  let hmonitorKey := fun z : CoordinatorObserveInput p C_star C_h =>
    (updatedCounterMap z, (launchMap z, (blockMap z, timeMap z)))
  have hmonitorKeyMeasurable : Measurable hmonitorKey :=
    hupdatedCounters.prodMk (hlaunch.prodMk (hblock.prodMk htime))
  let hmonitorMap := fun z : CoordinatorObserveInput p C_star C_h =>
    MonitorCode.mk (updatedCounterMap z)
      (if launchMap z then some (blockMap z) else none)
      (if launchMap z then manuscriptRound p (timeMap z) else p.T)
  have hmonitorFactor : ∀ x y, hmonitorKey x = hmonitorKey y →
      hmonitorMap x = hmonitorMap y := by
    intro x y h
    have hc := congrArg Prod.fst h
    have hl := congrArg (fun q => q.2.1) h
    have hb := congrArg (fun q => q.2.2.1) h
    have ht := congrArg (fun q => q.2.2.2) h
    simp only [hmonitorKey] at hc hl hb ht
    simp [hmonitorMap, hc, hl, hb, ht]
  have hmonitor : Measurable hmonitorMap :=
    measurable_of_countable_key hmonitorKey hmonitorKeyMeasurable _ hmonitorFactor
  let htriggerKey := fun z : CoordinatorObserveInput p C_star C_h =>
    (launchMap z, timeMap z)
  have htriggerKeyMeasurable : Measurable htriggerKey := hlaunch.prodMk htime
  let htriggerMap := fun z : CoordinatorObserveInput p C_star C_h =>
    if launchMap z then some (timeMap z) else none
  have htriggerFactor : ∀ x y, htriggerKey x = htriggerKey y →
      htriggerMap x = htriggerMap y := by
    intro x y h
    have hl := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    simp only [htriggerKey] at hl ht
    simp [htriggerMap, hl, ht]
  have htrigger : Measurable htriggerMap :=
    measurable_of_countable_key htriggerKey htriggerKeyMeasurable _ htriggerFactor
  let fieldsMap := fun z : CoordinatorObserveInput p C_star C_h =>
    (armMap z, (blockMap z, (targetMap z,
      (coordinatorStateCode p (BootstrapCoordinatorLocalRound.observationUpdate p
        ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.1)
        ((coordinatorRoundInputCoordinates p z.fixed.input).1.1.2)
        ((coordinatorStateOfCode p
          (coordinatorRoundInputCoordinates p z.fixed.input).2.1.coordinator))
        ((coordinatorRoundInputCoordinates p z.fixed.input).2.2) z.feedback),
        (hmonitorMap z, htriggerMap z)))))
  have hfields : Measurable fieldsMap :=
    harm.prodMk (hblock.prodMk (htarget.prodMk
      (hupdatedState.prodMk (hmonitor.prodMk htrigger))))
  have hfieldsEq : (fun z : CoordinatorObserveInput p C_star C_h =>
      coordinatorObservationCodeFields p (coordinatorObserveCode p C_star C_h z)) =
      fieldsMap := by
    funext z
    simp [fieldsMap, coordinatorObservationCodeFields, coordinatorObserveCode,
      coordinatorPreparedRound, BootstrapCoordinatorLocalRound.prepare,
      assemblePrelaunch, observationUpdate, countersAfterObservation,
      launchDecision, launchTest, coordinatorLaunchDecision,
      coordinatorRoundInputCoordinates, monitorStateOfCode, counterMap,
      hmonitorMap, htriggerMap, blockMap,
      targetMap, armMap, updatedCounterMap, launchMap, timeMap]
    rfl
  apply (measurable_comap_iff).2
  simpa only [Function.comp_def, hfieldsEq] using hfields

/-- Any measurable assembly of the separate actual inputs may be composed
with the local observation code while retaining its original source domain. -/
theorem measurable_coordinatorObserveCode_comp {α : Type*} [MeasurableSpace α]
    (p : Parameters) (C_star C_h : ℝ)
    (inputs : α → CoordinatorObserveInput p C_star C_h) (hinputs : Measurable inputs) :
    Measurable (fun x => coordinatorObserveCode p C_star C_h (inputs x)) :=
  (measurable_coordinatorObserveCode p C_star C_h).comp hinputs

/-- The observe code decodes exactly to the existing `observe (prepare ...)`
result, with no replacement state or strengthened hypothesis. -/
theorem reconstruct_coordinatorObserveCode (p : Parameters) (C_star C_h : ℝ)
    (input : CoordinatorObserveInput p C_star C_h) :
    reconstructCoordinatorObservationCode p C_star C_h input.fixed
      (coordinatorObserveCode p C_star C_h input) =
        some (coordinatorObserveResult p C_star C_h input) := by
  let prepared := coordinatorPreparedRound p input.fixed.input input.ownArmScalar
  let before := prepared.before
  have hCstar : before.data.C_star = C_star := by
    change input.fixed.input.base.2.1 = C_star
    exact congrArg Prod.fst input.fixed.constants
  have hCh : before.data.C_h = C_h := by
    change input.fixed.input.base.2.2 = C_h
    exact congrArg Prod.snd input.fixed.constants
  by_cases htest : BootstrapCoordinatorLocalRound.launchTest p before.data
      before.monitor.1 prepared.round input.feedback
  · have hdecision : BootstrapCoordinatorLocalRound.launchDecision p before.data
        before.monitor prepared.round input.feedback = true := by
      exact (BootstrapCoordinatorLocalRound.launchDecision_true_iff p before.data
        before.monitor prepared.round input.feedback).2 htest
    have hcodeDecision : coordinatorLaunchDecision p C_star C_h input.fixed
        input.feedback = true := by
      simpa [coordinatorLaunchDecision, coordinatorPreparedRound,
        BootstrapCoordinatorLocalRound.prepare, prepared, before, assemblePrelaunch] using
        hdecision
    let expandedData : BootstrapCoordinatorLocalRound.LocalData p :=
      ⟨input.fixed.input.localState.block, input.fixed.input.base.1.1,
        input.fixed.input.base.1.2, input.fixed.input.localState.target,
        coordinatorStateOfCode p input.fixed.input.localState.coordinator,
        input.fixed.input.base.2.1, input.fixed.input.base.2.2⟩
    let expandedMonitor : BootstrapLaunchMonitor.State p :=
      monitorStateOfCode p input.fixed.input.localState.monitor.1
    have htestExpanded : BootstrapCoordinatorLocalRound.launchTest p
        expandedData expandedMonitor input.fixed.input.round input.feedback := by
      simpa [expandedData, expandedMonitor, prepared, before, coordinatorPreparedRound,
        BootstrapCoordinatorLocalRound.prepare, assemblePrelaunch,
        monitorStateOfCode] using htest
    simp [reconstructCoordinatorObservationCode, coordinatorObserveCode,
      coordinatorObserveResult, coordinatorPreparedRound,
      BootstrapCoordinatorLocalRound.prepare, BootstrapCoordinatorLocalRound.observe,
      BootstrapCoordinatorLocalRound.continuationAfterObservation,
      BootstrapCoordinatorLocalRound.launchTest,
      assemblePrelaunch, monitorStateOfCode,
      coordinatorObservationDataOfCode,
      hcodeDecision]
    simp only [BootstrapCoordinatorLocalRound.launchTest] at htestExpanded
    rcases htestExpanded with ⟨hend, hstrict⟩
    have hstrict' : 4 * BootstrapStartupCostScale.Q C_star C_h p <
        BootstrapLaunchMonitor.monitorValue p
          (BootstrapCoordinatorLocalRound.countersAfterObservation p
            input.fixed.input.base.1.1
            input.fixed.input.localState.monitor.1.counters
            input.fixed.input.round input.feedback) := by
      simpa [expandedData, expandedMonitor, monitorStateOfCode,
        input.fixed.constants] using hstrict
    refine ⟨hend, hstrict', ?_⟩
    have hcross : BootstrapLaunchMonitor.calendarBlockEnd p input.fixed.input.round ∧
        BootstrapLaunchMonitor.monitorValue p
          (BootstrapCoordinatorLocalRound.countersAfterObservation p
            input.fixed.input.base.1.1
            input.fixed.input.localState.monitor.1.counters
            input.fixed.input.round input.feedback) >
          4 * BootstrapStartupCostScale.Q input.fixed.input.base.2.1
            input.fixed.input.base.2.2 p := by
      refine ⟨hend, ?_⟩
      simpa [input.fixed.constants] using hstrict'
    simp [hcross, coordinatorStateOfCode_encode]
  · have hdecision : BootstrapCoordinatorLocalRound.launchDecision p before.data
        before.monitor prepared.round input.feedback = false := by
      cases hv : BootstrapCoordinatorLocalRound.launchDecision p before.data
          before.monitor prepared.round input.feedback with
      | false => rfl
      | true =>
        have hcross := (BootstrapCoordinatorLocalRound.launchDecision_true_iff p before.data
          before.monitor prepared.round input.feedback).1 hv
        exact (htest hcross).elim
    have hcodeDecision : coordinatorLaunchDecision p C_star C_h input.fixed
        input.feedback = false := by
      simpa [coordinatorLaunchDecision, coordinatorPreparedRound,
        BootstrapCoordinatorLocalRound.prepare, prepared, before, assemblePrelaunch] using
        hdecision
    let expandedData : BootstrapCoordinatorLocalRound.LocalData p :=
      ⟨input.fixed.input.localState.block, input.fixed.input.base.1.1,
        input.fixed.input.base.1.2, input.fixed.input.localState.target,
        coordinatorStateOfCode p input.fixed.input.localState.coordinator,
        input.fixed.input.base.2.1, input.fixed.input.base.2.2⟩
    let expandedMonitor : BootstrapLaunchMonitor.State p :=
      monitorStateOfCode p input.fixed.input.localState.monitor.1
    have hnotExpanded : ¬ BootstrapCoordinatorLocalRound.launchTest p
        expandedData expandedMonitor input.fixed.input.round input.feedback := by
      intro hcross
      apply htest
      simpa [expandedData, expandedMonitor, prepared, before, coordinatorPreparedRound,
        BootstrapCoordinatorLocalRound.prepare, assemblePrelaunch,
        monitorStateOfCode] using hcross
    have hnotExplicit : ¬ (BootstrapLaunchMonitor.calendarBlockEnd p input.fixed.input.round ∧
        BootstrapLaunchMonitor.monitorValue p
          (BootstrapCoordinatorLocalRound.countersAfterObservation p
            input.fixed.input.base.1.1
            input.fixed.input.localState.monitor.1.counters
            input.fixed.input.round input.feedback) >
          4 * BootstrapStartupCostScale.Q input.fixed.input.base.2.1
            input.fixed.input.base.2.2 p) := by
      simpa [BootstrapCoordinatorLocalRound.launchTest, expandedData, expandedMonitor,
        monitorStateOfCode] using hnotExpanded
    simp [reconstructCoordinatorObservationCode, coordinatorObserveCode,
      coordinatorObserveResult, coordinatorPreparedRound,
      BootstrapCoordinatorLocalRound.prepare, BootstrapCoordinatorLocalRound.observe,
      BootstrapCoordinatorLocalRound.continuationAfterObservation,
      BootstrapCoordinatorLocalRound.launchTest,
      assemblePrelaunch, monitorStateOfCode,
      coordinatorObservationDataOfCode, hcodeDecision]
    by_cases hcross : BootstrapLaunchMonitor.calendarBlockEnd p input.fixed.input.round ∧
        BootstrapLaunchMonitor.monitorValue p
          (BootstrapCoordinatorLocalRound.countersAfterObservation p
            input.fixed.input.base.1.1
            input.fixed.input.localState.monitor.1.counters
            input.fixed.input.round input.feedback) >
          4 * BootstrapStartupCostScale.Q input.fixed.input.base.2.1
            input.fixed.input.base.2.2 p
    · exact (hnotExplicit hcross).elim
    · simp [hcross, coordinatorStateOfCode_encode]

/-- Inputs to the existing block-start operation. The row, IDs, and fixed
constants remain in the continuous base; only the carried local state and
the no-launch monitor are encoded. -/
structure CoordinatorBeginBlockInput (p : Parameters) where
  base : CoordinatorContinuousBase p
  block : Fin (n_boot p)
  carried : CoordinatorStateCode p
  monitor : {m : MonitorCode p // m.crossingBlock = none ∧ m.launchPosition = p.T}
  targetScalar : PrivateSourceStreams.Scalar

def coordinatorBeginBlockInputCoordinates (p : Parameters)
    (input : CoordinatorBeginBlockInput p) :
    CoordinatorContinuousBase p ×
      (Fin (n_boot p) × (CoordinatorStateCode p ×
        ({m : MonitorCode p // m.crossingBlock = none ∧ m.launchPosition = p.T} ×
          PrivateSourceStreams.Scalar))) :=
  (input.base, (input.block, (input.carried, (input.monitor, input.targetScalar))))

instance coordinatorBeginBlockInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (CoordinatorBeginBlockInput p) :=
  MeasurableSpace.comap (coordinatorBeginBlockInputCoordinates p) inferInstance

theorem measurable_coordinatorBeginBlockInputCoordinates (p : Parameters) :
    Measurable (coordinatorBeginBlockInputCoordinates p) := comap_measurable _

def coordinatorBeginBlock (p : Parameters) (input : CoordinatorBeginBlockInput p) :
    BootstrapCoordinatorLocalRound.PrelaunchBlock p :=
  BootstrapCoordinatorLocalRound.beginBlock p input.block input.base.1.1 input.base.1.2
    (coordinatorStateOfCode p input.carried)
    ⟨monitorStateOfCode p input.monitor.1, input.monitor.2⟩
    input.base.2.1 input.base.2.2 input.targetScalar

/-- The output code retains the same row, IDs, constants, monitor, block, and
target arm; reset coordinator fields are the literal initial state. -/
def coordinatorBeginBlockCode (p : Parameters) (input : CoordinatorBeginBlockInput p) :
    CoordinatorContinuousBase p × CoordinatorLocalCode p :=
  (input.base, ⟨input.block,
    BootstrapPrivateRoundStreams.coordinatorTargetDraw p input.targetScalar,
    coordinatorStateCode p (BootstrapPhysicalBlock.initialState p), input.monitor⟩)

theorem measurable_coordinatorBeginBlockCode (p : Parameters) :
    Measurable (coordinatorBeginBlockCode p) := by
  let coordinates := coordinatorBeginBlockInputCoordinates p
  have hc := measurable_coordinatorBeginBlockInputCoordinates p
  have hbase : Measurable (fun x : CoordinatorBeginBlockInput p => x.base) :=
    measurable_fst.comp hc
  have hblock : Measurable (fun x : CoordinatorBeginBlockInput p => x.block) :=
    measurable_fst.comp (measurable_snd.comp hc)
  have hmonitor : Measurable (fun x : CoordinatorBeginBlockInput p => x.monitor) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp hc)))
  have htarget : Measurable (fun x : CoordinatorBeginBlockInput p =>
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p x.targetScalar) := by
    change Measurable (fun x : CoordinatorBeginBlockInput p =>
      BootstrapPrivateRoundStreams.fullArmScalarDraw p x.targetScalar)
    exact (BootstrapPrivateRoundStreams.measurable_fullArmScalarDraw p).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
        (measurable_snd.comp hc))))
  have hlocal : Measurable (fun x : CoordinatorBeginBlockInput p =>
      (x.block, (BootstrapPrivateRoundStreams.coordinatorTargetDraw p x.targetScalar,
        (coordinatorStateCode p (BootstrapPhysicalBlock.initialState p), x.monitor)))) := by
    exact hblock.prodMk (htarget.prodMk
      ((measurable_const : Measurable (fun _ : CoordinatorBeginBlockInput p =>
        coordinatorStateCode p (BootstrapPhysicalBlock.initialState p))).prodMk hmonitor))
  let key := fun x : CoordinatorBeginBlockInput p =>
    (x.block, (BootstrapPrivateRoundStreams.coordinatorTargetDraw p x.targetScalar,
      (coordinatorStateCode p (BootstrapPhysicalBlock.initialState p), x.monitor)))
  have hcode : Measurable (fun x : CoordinatorBeginBlockInput p =>
      ({ block := x.block,
         target := BootstrapPrivateRoundStreams.coordinatorTargetDraw p x.targetScalar,
         coordinator := coordinatorStateCode p (BootstrapPhysicalBlock.initialState p),
         monitor := x.monitor } : CoordinatorLocalCode p)) :=
    measurable_of_countable_key key hlocal _ (by
      intro x y h
      simp [key] at h
      rcases h with ⟨hb, ht, hm⟩
      simp [hb, ht, hm])
  exact hbase.prodMk hcode

theorem reconstruct_coordinatorBeginBlockCode (p : Parameters)
    (input : CoordinatorBeginBlockInput p) :
    assemblePrelaunch p (coordinatorBeginBlockCode p input).1
        (coordinatorBeginBlockCode p input).2 = coordinatorBeginBlock p input := by
  simp only [coordinatorBeginBlockCode, coordinatorBeginBlock, assemblePrelaunch,
    BootstrapCoordinatorLocalRound.beginBlock, monitorStateOfCode,
    BootstrapCoordinatorLocalRound.resetCoordinatorBlockState]
  congr 1

/-- The coordinator index is read from the original scalar coordinate while
the entire published row family and ID array stay attached to the base. -/
def selectedCoordinatorBase (p : Parameters)
    (x : BootstrapPrivateRoundStreams.SourceInput p) (C_star C_h : ℝ) :
    CoordinatorContinuousBase p :=
  ((x.1.2 (PrivateSourceStreams.coordinatorIndex p x.2.1.2), x.1.1),
    (C_star, C_h))

theorem measurable_selectedCoordinatorBase (p : Parameters) (C_star C_h : ℝ) :
    Measurable (selectedCoordinatorBase p · C_star C_h) := by
  have hJ : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p =>
      PrivateSourceStreams.coordinatorIndex p x.2.1.2) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hrows : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p => x.1.2) :=
    measurable_snd.comp measurable_fst
  have hid : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p => x.1.1) :=
    measurable_fst.comp measurable_fst
  have hselected : Measurable (fun x : BootstrapPrivateRoundStreams.SourceInput p =>
      x.1.2 (PrivateSourceStreams.coordinatorIndex p x.2.1.2)) := by
    intro s hs
    rw [show (fun x : BootstrapPrivateRoundStreams.SourceInput p =>
      x.1.2 (PrivateSourceStreams.coordinatorIndex p x.2.1.2)) ⁻¹' s =
        ⋃ j : Fin (M p), {x | PrivateSourceStreams.coordinatorIndex p x.2.1.2 = j} ∩
          {x | x.1.2 j ∈ s} by
      ext x
      simp]
    exact MeasurableSet.iUnion fun j =>
      (measurableSet_eq_fun hJ measurable_const).inter
        (((measurable_pi_apply j).comp hrows) hs)
  exact ((hselected.prodMk hid).prodMk (measurable_const.prodMk measurable_const))

/-- The lossless source carrier for composing selected-row adapters. The
selected base is a separate measurable map, so no row or private coordinate is
discarded from this retained source point. -/
def selectedCoordinatorSourceBase (p : Parameters)
    (x : BootstrapPrivateRoundStreams.SourceInput p) :
    BootstrapPrivateRoundStreams.SourceInput p := x

theorem measurable_selectedCoordinatorSourceBase (p : Parameters) :
    Measurable (selectedCoordinatorSourceBase p) := measurable_id

@[simp] theorem selectedCoordinatorSourceBase_fst (p : Parameters)
    (x : BootstrapPrivateRoundStreams.SourceInput p) :
    selectedCoordinatorSourceBase p x = x := rfl

@[simp] theorem selectedCoordinatorSourceBase_row (p : Parameters)
    (x : BootstrapPrivateRoundStreams.SourceInput p) (C_star C_h : ℝ) :
    (selectedCoordinatorBase p (selectedCoordinatorSourceBase p x) C_star C_h).1.1 =
      x.1.2 (PrivateSourceStreams.coordinatorIndex p x.2.1.2) := rfl


end Bandits.Support.BootstrapCoordinatorRoundMeasurability
