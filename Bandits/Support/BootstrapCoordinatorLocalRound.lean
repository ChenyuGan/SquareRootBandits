/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapDimensions
public import Bandits.Support.BootstrapLaunchMonitor
public import Bandits.Support.BootstrapPhysicalBlock
public import Bandits.Support.BootstrapPrivateRoundStreams
public import Bandits.Support.BootstrapStartupCostScale
public import Bandits.Support.PrivateSourceStreams

/-!
# Coordinator-local bootstrap round operations

Internal, observation-parametric coordinator operations for one prelaunch
calendar block. The coordinator sees only its selected complete row, the
shared ID array, its carried local list/mode, its own round scalar, and its
own finite observation. No follower history, active learner state, assignment,
or aggregate physical execution is an input.

Sources: `sources/zip4/manuscript/07_public_setup.tex:40-50,55-113` and
`sources/zip4/manuscript/appendix_b_communication.tex:128-131`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapStartupCostScale
open Bandits.Support.CompletePublicTable
open Bandits.Support.FiniteBanditModel
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.PrivateSourceStreams
open Bandits.Support.PublicDiscreteDraws
open scoped BigOperators Classical

namespace Bandits.Support.BootstrapCoordinatorLocalRound

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- A no-launch monitor state is carried whole between blocks. The sentinel
position is part of the phase check, so a recorded launch cannot re-enter the
prelaunch interface. -/
abbrev UnlaunchedMonitor (p : Parameters) :=
  {s : BootstrapLaunchMonitor.State p //
    s.crossingBlock = none ∧ s.launchPosition = p.T}

/-- The coordinator's local data for one calendar block. The stored target is
drawn once by `beginBlock`; later rounds have no target scalar input. -/
structure LocalData (p : Parameters) where
  block : Fin (n_boot p)
  row : CompletePublicTable.CompleteRow p
  ids : CompletePublicTable.IDArray p
  target : Fin p.K
  coordinator : BootstrapPhysicalBlock.State p
  C_star : ℝ
  C_h : ℝ

/-- A live local block can be prepared only while the supplied monitor still
has the no-launch sentinel. -/
structure PrelaunchBlock (p : Parameters) where
  data : LocalData p
  monitor : UnlaunchedMonitor p

/-- The checked phase transition preserves the complete monitor witness after
launch, including a final-boundary crossing whose source launch round is
`T + 1`. -/
structure LaunchedBlock (p : Parameters) where
  data : LocalData p
  triggerRound : Fin p.T
  triggerInBlock : triggerRound ∈ calendarBlock p data.block
  monitor : BootstrapLaunchMonitor.State p
  crossing : monitor.crossingBlock = some data.block
  triggerAtBlockEnd : BootstrapLaunchMonitor.calendarBlockEnd p triggerRound
  strictThreshold : BootstrapLaunchMonitor.monitorValue p monitor.counters >
    4 * BootstrapStartupCostScale.Q data.C_star data.C_h p
  launchPosition : monitor.launchPosition = manuscriptRound p triggerRound

/-- The two honest post-observation phases. Only the `prelaunch` constructor
can be passed to `prepare`. -/
inductive Continuation (p : Parameters) where
  | prelaunch : PrelaunchBlock p → Continuation p
  | launched : LaunchedBlock p → Continuation p

namespace Continuation

/-- The sole monitor witness retained by either post-observation phase. -/
def monitorState (result : Continuation p) : BootstrapLaunchMonitor.State p :=
  match result with
  | .prelaunch live => live.monitor.1
  | .launched active => active.monitor

/-- The coordinator's updated local list/mode carrier, including its audit
positives, retained by either continuation phase. -/
def coordinatorState (result : Continuation p) : BootstrapPhysicalBlock.State p :=
  match result with
  | .prelaunch live => live.data.coordinator
  | .launched active => active.data.coordinator

end Continuation

/-- The arm is returned separately from the continuation so its preservation
across feedback processing is part of the public interface. -/
structure ObservationResult (p : Parameters) where
  arm : Fin p.K
  next : Continuation p

/-- The source slot, read only from the coordinator's selected continuous row.
This is the accepted row-sampler input used by the physical reference module. -/
def coordinatorSlot (p : Parameters) (row : CompletePublicTable.CompleteRow p)
    (t : Fin p.T) : PublicDiscreteDraws.Slot :=
  PublicDiscreteDraws.slotDraw (row.2 t).1

/-- The actual coordinator tuple arm `R_{0,t}` from its own selected row. -/
def coordinatorTupleArm (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) : Fin p.K :=
  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
    (ActiveRoundActions.coordinator p.two_le_m)

/-- Product of the selected row's forward bits over the actual carried list.
The empty product is the source value one. -/
def localForwardProduct (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T) : ℕ :=
  ∏ u ∈ st.list, if row.1 u t = true then 1 else 0

theorem localForwardProduct_empty (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (h : st.list = ∅) : localForwardProduct p row st t = 1 := by
  simp [localForwardProduct, h]

/-- Coordinator arm choice made before observing round `t`. The same own
scalar `v` supplies the mutually exclusive complement and full-uniform
branches. -/
def coordinatorArmChoice (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (v : PrivateSourceStreams.Scalar) : Fin p.K :=
  if coordinatorSlot p row t = PublicDiscreteDraws.dataSlot then
    if st.mode = BootstrapPhysicalBlock.Mode.multicast ∧
        localForwardProduct p row st t = 1 then
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p target v).val
    else target
  else if coordinatorSlot p row t = PublicDiscreteDraws.downSlot then
    coordinatorTupleArm p row t
  else BootstrapPrivateRoundStreams.fullArmScalarDraw p v

theorem coordinatorArmChoice_discover_data (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (v : PrivateSourceStreams.Scalar)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.dataSlot)
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.discover) :
    coordinatorArmChoice p row target st t v =
      target := by
  simp [coordinatorArmChoice, hslot, hmode]

theorem coordinatorArmChoice_multicast_data (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (v : PrivateSourceStreams.Scalar)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.dataSlot)
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.multicast) :
    coordinatorArmChoice p row target st t v =
      if localForwardProduct p row st t = 1 then
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p target v).val
      else target := by
  simp [coordinatorArmChoice, hslot, hmode]

theorem coordinatorArmChoice_down (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (v : PrivateSourceStreams.Scalar)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.downSlot) :
    coordinatorArmChoice p row target st t v = coordinatorTupleArm p row t := by
  simp [coordinatorArmChoice, hslot, PublicDiscreteDraws.dataSlot,
    PublicDiscreteDraws.downSlot]

theorem coordinatorArmChoice_up (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (target : Fin p.K)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (v : PrivateSourceStreams.Scalar)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.upSlot) :
    coordinatorArmChoice p row target st t v =
      BootstrapPrivateRoundStreams.fullArmScalarDraw p v := by
  simp [coordinatorArmChoice, hslot, PublicDiscreteDraws.dataSlot,
    PublicDiscreteDraws.downSlot, PublicDiscreteDraws.upSlot]

/-- Audit positives are carried only as audit data: changing them while
holding the actual list and mode fixed cannot change the selected arm. -/
theorem coordinatorArmChoice_audit_positives_irrelevant (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (target : Fin p.K)
    (s₁ s₂ : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (v : PrivateSourceStreams.Scalar)
    (hlist : s₁.list = s₂.list) (hmode : s₁.mode = s₂.mode) :
    coordinatorArmChoice p row target s₁ t v =
      coordinatorArmChoice p row target s₂ t v := by
  simp [coordinatorArmChoice, localForwardProduct, hlist, hmode]

/-- Apply the selected-row coordinator's only list/mode transition. The
`positives` field is updated as an audit record but is never consulted by the
arm policy or transition condition. -/
def observationUpdate (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1)) : BootstrapPhysicalBlock.State p :=
  if st.mode = BootstrapPhysicalBlock.Mode.discover ∧
      coordinatorSlot p row t = PublicDiscreteDraws.dataSlot ∧ 0 < y.val then
    let kept := st.list.filter (fun u => ids u t = true)
    ⟨kept,
      if kept.card ≤ L0 p then BootstrapPhysicalBlock.Mode.multicast
      else BootstrapPhysicalBlock.Mode.discover,
      insert t st.positives⟩
  else st

theorem observationUpdate_discovery_positive (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.discover)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.dataSlot)
    (hy : 0 < y.val) :
    observationUpdate p row ids st t y =
      ⟨st.list.filter (fun u => ids u t = true),
        (if (st.list.filter (fun u => ids u t = true)).card ≤ L0 p then
          BootstrapPhysicalBlock.Mode.multicast else BootstrapPhysicalBlock.Mode.discover),
        insert t st.positives⟩ := by
  simp [observationUpdate, hmode, hslot, hy]

theorem observationUpdate_no_change (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (h : ¬ (st.mode = BootstrapPhysicalBlock.Mode.discover ∧
      coordinatorSlot p row t = PublicDiscreteDraws.dataSlot ∧ 0 < y.val)) :
    observationUpdate p row ids st t y = st := by
  unfold observationUpdate
  by_cases hc : st.mode = BootstrapPhysicalBlock.Mode.discover ∧
      coordinatorSlot p row t = PublicDiscreteDraws.dataSlot ∧ 0 < y.val
  · exact (h hc).elim
  · rw [ite_eq_right hc]

theorem observationUpdate_no_change_of_non_data (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hslot : coordinatorSlot p row t ≠ PublicDiscreteDraws.dataSlot) :
    observationUpdate p row ids st t y = st := by
  apply observationUpdate_no_change
  intro hchange
  exact hslot hchange.2.1

theorem observationUpdate_no_change_of_multicast (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.multicast) :
    observationUpdate p row ids st t y = st := by
  simp [observationUpdate, hmode]

theorem observationUpdate_filter_mem (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.discover)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.dataSlot)
    (hy : 0 < y.val) (u : Fin (A_id p)) :
    u ∈ (observationUpdate p row ids st t y).list ↔
      u ∈ st.list ∧ ids u t = true := by
  simp [observationUpdate, hmode, hslot, hy, Finset.mem_filter]

/-- The list filter's computed cardinality controls the mode stored for the
next prepared round. -/
theorem observationUpdate_multicast_mode_of_small_filter (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.discover)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.dataSlot)
    (hy : 0 < y.val)
    (hcard : (st.list.filter (fun u => ids u t = true)).card ≤ L0 p) :
    (observationUpdate p row ids st t y).mode =
      BootstrapPhysicalBlock.Mode.multicast := by
  simp [observationUpdate, hmode, hslot, hy, hcard]

theorem next_selector_uses_multicast_after_switch (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t tNext : Fin p.T)
    (y : Fin (D p + 1)) (v : PrivateSourceStreams.Scalar)
    (target : Fin p.K)
    (hmode : st.mode = BootstrapPhysicalBlock.Mode.discover)
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.dataSlot)
    (hy : 0 < y.val)
    (hcard : (st.list.filter (fun u => ids u t = true)).card ≤ L0 p)
    (hnext : coordinatorSlot p row tNext = PublicDiscreteDraws.dataSlot) :
    coordinatorArmChoice p row target
        (observationUpdate p row ids st t y) tNext v =
      if localForwardProduct p row (observationUpdate p row ids st t y) tNext = 1 then
        (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p target v).val
      else target := by
  apply coordinatorArmChoice_multicast_data p row target
    (observationUpdate p row ids st t y) tNext v hnext
  exact observationUpdate_multicast_mode_of_small_filter p row ids st t y
    hmode hslot hy hcard

/-- The optional arm credited by the coordinator monitor on this observation.
DATA and UP have no credit; DOWN credits the actual selected-row `R_{0,t}`
exactly when the coordinator's own finite observation is positive. -/
def downCreditArm (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (y : Fin (D p + 1)) : Option (Fin p.K) :=
  if coordinatorSlot p row t = PublicDiscreteDraws.downSlot ∧ 0 < y.val then
    some (coordinatorTupleArm p row t)
  else none

theorem downCreditArm_none_of_non_down (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hslot : coordinatorSlot p row t ≠ PublicDiscreteDraws.downSlot) :
    downCreditArm p row t y = none := by
  simp [downCreditArm, hslot]

theorem downCreditArm_eq_some_of_positive_down (p : Parameters)
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.downSlot)
    (hy : 0 < y.val) :
    downCreditArm p row t y = some (coordinatorTupleArm p row t) := by
  simp [downCreditArm, hslot, hy]

/-- The monitor's exact post-observation counter vector. -/
def countersAfterObservation (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1)) : Fin p.K → ℕ :=
  BootstrapLaunchMonitor.creditCounter counters (downCreditArm p row t y)

theorem countersAfterObservation_eq_self_of_non_down (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1))
    (hslot : coordinatorSlot p row t ≠ PublicDiscreteDraws.downSlot) :
    countersAfterObservation p row counters t y = counters := by
  funext a
  simp [countersAfterObservation, downCreditArm, hslot,
    BootstrapLaunchMonitor.creditCounter]

theorem countersAfterObservation_eq_down_increment (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1))
    (hslot : coordinatorSlot p row t = PublicDiscreteDraws.downSlot)
    (hy : 0 < y.val) :
    countersAfterObservation p row counters t y =
      fun a => counters a + if coordinatorTupleArm p row t = a then 1 else 0 := by
  funext a
  simp [countersAfterObservation, downCreditArm, hslot, hy,
    BootstrapLaunchMonitor.creditCounter]

theorem countersAfterObservation_mono (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1)) (a : Fin p.K) :
    counters a ≤ countersAfterObservation p row counters t y a :=
  BootstrapLaunchMonitor.creditCounter_mono counters
    (downCreditArm p row t y) a

theorem countersAfterObservation_le_succ (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1)) (a : Fin p.K) :
    countersAfterObservation p row counters t y a ≤ counters a + 1 :=
  BootstrapLaunchMonitor.creditCounter_le_succ counters
    (downCreditArm p row t y) a

theorem monitorValueAfterObservation_mono (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1)) :
    BootstrapLaunchMonitor.monitorValue p counters ≤
      BootstrapLaunchMonitor.monitorValue p
        (countersAfterObservation p row counters t y) :=
  BootstrapLaunchMonitor.monitorValue_credit_mono p counters
    (downCreditArm p row t y)

theorem monitorValueAfterObservation_le (p : Parameters)
    (row : CompletePublicTable.CompleteRow p)
    (counters : Fin p.K → ℕ) (t : Fin p.T) (y : Fin (D p + 1)) :
    BootstrapLaunchMonitor.monitorValue p
        (countersAfterObservation p row counters t y) ≤
      BootstrapLaunchMonitor.monitorValue p counters + p.K :=
  BootstrapLaunchMonitor.monitorValue_credit_le p counters
    (downCreditArm p row t y)

/-- The exact block-boundary test after applying the current DOWN-positive
credit. Its inequality is strict, as in the source. -/
def launchTest (p : Parameters) (data : LocalData p)
    (monitor : BootstrapLaunchMonitor.State p) (t : Fin p.T)
    (y : Fin (D p + 1)) : Prop :=
  BootstrapLaunchMonitor.calendarBlockEnd p t ∧
    BootstrapLaunchMonitor.monitorValue p
      (countersAfterObservation p data.row monitor.counters t y) >
        4 * BootstrapStartupCostScale.Q data.C_star data.C_h p

/-- One-round continuation is formed only after the prepared arm has been
stored. The output monitor is either the updated no-launch sentinel or the
complete first-crossing witness. -/
def continuationAfterObservation (p : Parameters) (data : LocalData p)
    (monitor : UnlaunchedMonitor p) (coordinator : BootstrapPhysicalBlock.State p)
    (t : Fin p.T) (ht : t ∈ calendarBlock p data.block)
    (y : Fin (D p + 1)) : Continuation p := by
  classical
  let counters := countersAfterObservation p data.row monitor.1.counters t y
  let updatedCoordinator := observationUpdate p data.row data.ids coordinator t y
  by_cases hcross : launchTest p data monitor.1 t y
  · let updatedMonitor : BootstrapLaunchMonitor.State p :=
      ⟨counters, some data.block, manuscriptRound p t⟩
    exact .launched
      ⟨{ data with coordinator := updatedCoordinator }, t, ht, updatedMonitor,
        by simp [updatedMonitor], hcross.1,
        by simpa [updatedMonitor, counters] using hcross.2,
        by simp [updatedMonitor]⟩
  · let updatedMonitor : BootstrapLaunchMonitor.State p :=
      ⟨counters, none, p.T⟩
    exact .prelaunch
      ⟨{ data with coordinator := updatedCoordinator },
        ⟨updatedMonitor, by simp [updatedMonitor], by simp [updatedMonitor]⟩⟩

theorem continuationAfterObservation_coordinator_eq (p : Parameters)
    (data : LocalData p) (monitor : UnlaunchedMonitor p)
    (coordinator : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (ht : t ∈ calendarBlock p data.block) (y : Fin (D p + 1)) :
    Continuation.coordinatorState
      (continuationAfterObservation p data monitor coordinator t ht y) =
        observationUpdate p data.row data.ids coordinator t y := by
  classical
  by_cases hcross : launchTest p data monitor.1 t y
  · simp [continuationAfterObservation, Continuation.coordinatorState, hcross]
  · simp [continuationAfterObservation, Continuation.coordinatorState, hcross]

theorem continuationAfterObservation_monitor_counters (p : Parameters)
    (data : LocalData p) (monitor : UnlaunchedMonitor p)
    (coordinator : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (ht : t ∈ calendarBlock p data.block) (y : Fin (D p + 1)) :
    (Continuation.monitorState
      (continuationAfterObservation p data monitor coordinator t ht y)).counters =
        countersAfterObservation p data.row monitor.1.counters t y := by
  classical
  by_cases hcross : launchTest p data monitor.1 t y
  · simp [continuationAfterObservation, Continuation.monitorState, hcross]
  · simp [continuationAfterObservation, Continuation.monitorState, hcross]

theorem continuationAfterObservation_monitor_crossing (p : Parameters)
    (data : LocalData p) (monitor : UnlaunchedMonitor p)
    (coordinator : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (ht : t ∈ calendarBlock p data.block) (y : Fin (D p + 1)) :
    (Continuation.monitorState
      (continuationAfterObservation p data monitor coordinator t ht y)).crossingBlock =
        if launchTest p data monitor.1 t y then some data.block else none := by
  classical
  by_cases hcross : launchTest p data monitor.1 t y
  · simp [continuationAfterObservation, Continuation.monitorState, hcross]
  · simp [continuationAfterObservation, Continuation.monitorState, hcross]

theorem continuationAfterObservation_monitor_position (p : Parameters)
    (data : LocalData p) (monitor : UnlaunchedMonitor p)
    (coordinator : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (ht : t ∈ calendarBlock p data.block) (y : Fin (D p + 1)) :
    (Continuation.monitorState
      (continuationAfterObservation p data monitor coordinator t ht y)).launchPosition =
        if launchTest p data monitor.1 t y then manuscriptRound p t else p.T := by
  classical
  by_cases hcross : launchTest p data monitor.1 t y
  · simp [continuationAfterObservation, Continuation.monitorState, hcross]
  · simp [continuationAfterObservation, Continuation.monitorState, hcross]

/-- The pre-choice continuation contains the arm and the source round. No
observation is available to `prepare`. -/
structure PreparedRound (p : Parameters) where
  before : PrelaunchBlock p
  round : Fin p.T
  round_mem : round ∈ calendarBlock p before.data.block
  arm : Fin p.K

/-- Choose the coordinator arm from the pre-choice local state. The actual
block membership proof is carried to the observation boundary. -/
def prepare (p : Parameters) (before : PrelaunchBlock p)
    (t : Fin p.T) (ht : t ∈ calendarBlock p before.data.block)
    (ownRoundScalar : PrivateSourceStreams.Scalar) : PreparedRound p :=
  ⟨before, t, ht,
    coordinatorArmChoice p before.data.row before.data.target
      before.data.coordinator t ownRoundScalar⟩

/-- Process only the coordinator's own finite grid observation. The arm field
is copied from the already prepared continuation, so feedback cannot change
the current arm. -/
def observe (prepared : PreparedRound p) (y : Fin (D p + 1)) : ObservationResult p :=
  ⟨prepared.arm,
    continuationAfterObservation p prepared.before.data prepared.before.monitor
      prepared.before.data.coordinator prepared.round prepared.round_mem y⟩

theorem observe_preserves_prepared_arm (prepared : PreparedRound p)
    (y : Fin (D p + 1)) :
    (observe prepared y).arm = prepared.arm := rfl

theorem prepare_arm_eq_choice (p : Parameters) (before : PrelaunchBlock p)
    (t : Fin p.T) (ht : t ∈ calendarBlock p before.data.block)
    (v : PrivateSourceStreams.Scalar) :
    (prepare p before t ht v).arm =
      coordinatorArmChoice p before.data.row before.data.target
        before.data.coordinator t v := rfl

/-- The block-start reset of the reference coordinator carrier. Every field is
overwritten: the ID list becomes all IDs, mode becomes DISCOVER, and the old
block's audit positives are cleared. -/
def resetCoordinatorBlockState (p : Parameters)
    (carried : BootstrapPhysicalBlock.State p) : BootstrapPhysicalBlock.State p :=
  match carried with
  | ⟨_, _, _⟩ => BootstrapPhysicalBlock.initialState p

/-- Beginning a new block uses the accepted original target scalar once,
resets only this coordinator's block-local list/mode/audit state, and copies
the one cumulative monitor state unchanged. -/
def beginBlock (p : Parameters) (block : Fin (n_boot p))
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (carried : BootstrapPhysicalBlock.State p)
    (monitor : UnlaunchedMonitor p) (C_star C_h : ℝ)
    (targetScalar : PrivateSourceStreams.Scalar) : PrelaunchBlock p :=
  ⟨⟨block, row, ids,
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p targetScalar,
      resetCoordinatorBlockState p carried,
      C_star, C_h⟩,
    monitor⟩

theorem beginBlock_resets_list_mode_and_audit (p : Parameters)
    (block : Fin (n_boot p)) (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (carried : BootstrapPhysicalBlock.State p)
    (monitor : UnlaunchedMonitor p) (C_star C_h : ℝ)
    (targetScalar : PrivateSourceStreams.Scalar) :
    (beginBlock p block row ids carried monitor C_star C_h targetScalar).data.coordinator =
      BootstrapPhysicalBlock.initialState p := by
  cases carried
  rfl

theorem beginBlock_target_draw_once (p : Parameters)
    (block : Fin (n_boot p)) (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (carried : BootstrapPhysicalBlock.State p)
    (monitor : UnlaunchedMonitor p) (C_star C_h : ℝ)
    (targetScalar : PrivateSourceStreams.Scalar) :
    (beginBlock p block row ids carried monitor C_star C_h targetScalar).data.target =
      BootstrapPrivateRoundStreams.coordinatorTargetDraw p targetScalar := rfl

theorem beginBlock_monitor_preserved (p : Parameters)
    (block : Fin (n_boot p)) (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (carried : BootstrapPhysicalBlock.State p)
    (monitor : UnlaunchedMonitor p) (C_star C_h : ℝ)
    (targetScalar : PrivateSourceStreams.Scalar) :
    (beginBlock p block row ids carried monitor C_star C_h targetScalar).monitor = monitor := by
  simp [beginBlock]

theorem beginBlock_counters_preserved (p : Parameters)
    (block : Fin (n_boot p)) (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (carried : BootstrapPhysicalBlock.State p)
    (monitor : UnlaunchedMonitor p) (C_star C_h : ℝ)
    (targetScalar : PrivateSourceStreams.Scalar) :
    (beginBlock p block row ids carried monitor C_star C_h targetScalar).monitor.1.counters =
      monitor.1.counters := by
  simp [beginBlock]

/-- Boolean view of the strict post-credit boundary test. The continuation
constructor below branches on the same proposition `launchTest`. -/
def launchDecision (p : Parameters) (data : LocalData p)
    (monitor : UnlaunchedMonitor p) (t : Fin p.T)
    (y : Fin (D p + 1)) : Bool :=
  if launchTest p data monitor.1 t y then true else false

theorem launchDecision_true_iff (p : Parameters) (data : LocalData p)
    (monitor : UnlaunchedMonitor p) (t : Fin p.T) (y : Fin (D p + 1)) :
    launchDecision p data monitor t y = true ↔
      BootstrapLaunchMonitor.calendarBlockEnd p t ∧
        BootstrapLaunchMonitor.monitorValue p
          (countersAfterObservation p data.row monitor.1.counters t y) >
            4 * BootstrapStartupCostScale.Q data.C_star data.C_h p := by
  simp [launchDecision, launchTest]

theorem launchDecision_false_iff (p : Parameters) (data : LocalData p)
    (monitor : UnlaunchedMonitor p) (t : Fin p.T) (y : Fin (D p + 1)) :
    launchDecision p data monitor t y = false ↔
      ¬ BootstrapLaunchMonitor.calendarBlockEnd p t ∨
        BootstrapLaunchMonitor.monitorValue p
          (countersAfterObservation p data.row monitor.1.counters t y) ≤
            4 * BootstrapStartupCostScale.Q data.C_star data.C_h p := by
  simp [launchDecision, launchTest]
  by_cases hend : BootstrapLaunchMonitor.calendarBlockEnd p t <;> simp [hend]

theorem launched_source_round_eq (p : Parameters) (launched : LaunchedBlock p) :
    launched.monitor.launchPosition + 1 = manuscriptRound p launched.triggerRound + 1 := by
  rw [launched.launchPosition]

theorem launched_source_round_bounds (p : Parameters) (launched : LaunchedBlock p) :
    2 ≤ launched.monitor.launchPosition + 1 ∧
      launched.monitor.launchPosition + 1 ≤ p.T + 1 := by
  rw [launched.launchPosition]
  have h := BootstrapDimensions.manuscriptRound_bounds p launched.triggerRound
  omega

theorem launched_at_horizon_is_terminal (p : Parameters) (launched : LaunchedBlock p)
    (hend : manuscriptRound p launched.triggerRound = p.T) :
    launched.monitor.launchPosition + 1 = p.T + 1 := by
  rw [launched.launchPosition, hend]

/-- The prepared coordinator selector specializes to the existing physical
reference selector when that genuine reference input has the same selected
row, target, and explicit values of its own complement and uniform draws.
This is only a deterministic selector identity, not a feedback provenance
claim. -/
theorem coordinatorArmChoice_eq_physical_selector (p : Parameters) {s : Fin (n_boot p)}
    (x : BootstrapPhysicalBlock.Input p s)
    (row : CompletePublicTable.CompleteRow p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (targetScalar ownRoundScalar : PrivateSourceStreams.Scalar)
    (hrow : x.row = row)
    (htarget : x.target = BootstrapPrivateRoundStreams.coordinatorTargetDraw p targetScalar)
    (havoid : (x.coordinatorAvoid t).val =
      (BootstrapPrivateRoundStreams.forbiddenArmScalarDraw p
        (BootstrapPrivateRoundStreams.coordinatorTargetDraw p targetScalar) ownRoundScalar).val)
    (huniform : x.uniform (ActiveRoundActions.coordinator p.two_le_m) t =
      BootstrapPrivateRoundStreams.fullArmScalarDraw p ownRoundScalar) :
    coordinatorArmChoice p row
      (BootstrapPrivateRoundStreams.coordinatorTargetDraw p targetScalar) st t ownRoundScalar =
      BootstrapPhysicalBlock.coordinatorAction x st t := by
  have hslot : coordinatorSlot p row t = BootstrapPhysicalBlock.slot x t := by
    change PublicDiscreteDraws.slotDraw (row.2 t).1 =
      PublicDiscreteDraws.slotDraw (x.row.2 t).1
    rw [← hrow]
  have hproduct : localForwardProduct p row st t =
      BootstrapPhysicalBlock.forwardProduct x st t := by
    unfold localForwardProduct BootstrapPhysicalBlock.forwardProduct
    rw [← hrow]
  have htuple : coordinatorTupleArm p row t =
      (BootstrapPhysicalBlock.tuple x t).val
        (ActiveRoundActions.coordinator p.two_le_m) := by
    unfold coordinatorTupleArm BootstrapPhysicalBlock.tuple
    rw [← hrow]
  unfold coordinatorArmChoice BootstrapPhysicalBlock.coordinatorAction
  rw [hslot, hproduct]
  by_cases hdata : BootstrapPhysicalBlock.slot x t = PublicDiscreteDraws.dataSlot
  · simp only [ite_eq_left hdata]
    by_cases hrelease : st.mode = BootstrapPhysicalBlock.Mode.multicast ∧
        BootstrapPhysicalBlock.forwardProduct x st t = 1
    · simp only [ite_eq_left hrelease]
      exact havoid.symm
    · simp only [ite_eq_right hrelease]
      exact htarget.symm
  · simp only [ite_eq_right hdata]
    by_cases hdown : BootstrapPhysicalBlock.slot x t = PublicDiscreteDraws.downSlot
    · simp only [ite_eq_left hdown]
      exact htuple
    · simp only [ite_eq_right hdown]
      exact huniform.symm

/-- The observation-only coordinator list/mode update agrees with the
reference physical step when its actual profile is explicitly supplied and
the local grid observation is that profile's own coordinator observation.
This does not certify that the reference profile's follower feedback is an
actual heterogeneous execution. -/
theorem observationUpdate_eq_physical_step (p : Parameters) {s : Fin (n_boot p)}
    (x : BootstrapPhysicalBlock.Input p s)
    (row : CompletePublicTable.CompleteRow p)
    (ids : CompletePublicTable.IDArray p)
    (st : BootstrapPhysicalBlock.State p) (t : Fin p.T)
    (y : Fin (D p + 1))
    (hrow : x.row = row) (hids : x.ids = ids)
    (ht : t ∈ calendarBlock p s)
    (hy : y = BootstrapPhysicalBlock.observationIndex x st t
      (ActiveRoundActions.coordinator p.two_le_m)) :
    observationUpdate p row ids st t y = BootstrapPhysicalBlock.step x st t := by
  have hpositive :
      (0 < y.val) =
        (0 < BootstrapPhysicalBlock.feedback x st t
          (ActiveRoundActions.coordinator p.two_le_m)) := by
    rw [hy]
    exact propext (BootstrapPhysicalBlock.observationIndex_pos_iff x st t
      (ActiveRoundActions.coordinator p.two_le_m))
  simp [observationUpdate, BootstrapPhysicalBlock.step,
    BootstrapPhysicalBlock.discoveryPositive, BootstrapPhysicalBlock.slot,
    coordinatorSlot, hrow, hids, ht, hpositive]

end Bandits.Support.BootstrapCoordinatorLocalRound

end
