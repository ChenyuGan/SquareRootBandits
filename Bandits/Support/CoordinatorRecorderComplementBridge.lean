/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CoordinatorRecordingOperation
public import Bandits.Support.FastComplementLocality

import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Coordinator recorder from fast-complement weights

This adapter supplies the accepted coordinator recorder with a proof-only
extension of the coordinator's locally known current weights. On the retained
slow set it uses the assignment anchor; on the actual fast complement it uses
the supplied current weights. The adapter always calls the original checked
recorder, so malformed local complement data and an invalid grid boundary
retain its `none` failure result.

The extension is not a physical score register and asserts nothing about
hidden slow scores. The conditional comparison theorem exposes the fast
complement envelope and compares against any globally valid extension that
agrees there. It makes no physical action, feedback, chronology, or provenance
claim.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:16-37,96-113`,
`sources/zip4/manuscript/05_binary_transport.tex:352-393`,
`sources/zip4/manuscript/06_interruptions.tex:257-269`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

namespace Bandits.Support.CoordinatorRecorderComplementBridge

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CanonicalOrientedSetLaw
open Bandits.Support.ActiveRoundActions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.FastComplementLocality
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.RealRewardGridCount
open Bandits.Support.SnapshotRecordingKernel

abbrev Parameters := ConstructorDimensions.Parameters

/-- A local coordinator call retains only the weights indexed by the actual
fast-arm complement. The time, row, selected arm, and typed observation are
local supplied inputs; the mode records either collection or the assignment
start's live regime with its local confirmation bit. -/
inductive LocalMode {p : Parameters} {eta : LearningRate}
    (s : AssignmentStartPayload.Input p eta) where
  | collection
  | live (confirmationsEmpty : Bool)

/-- The coordinator-local inputs for one call to the accepted recorder.
`gridBoundary` is the source one-based endpoint and may be the `T+1` sentinel.
No source weights are supplied on the retained slow set. -/
structure Input {p : Parameters} {eta : LearningRate}
    (s : AssignmentStartPayload.Input p eta) where
  currentWeights : FastArm s.slowSet → ℝ
  time : Fin p.T
  gridBoundary : ℕ
  row : CompleteRow p
  ownArm : Fin p.K
  observation : Fin (D p + 1)
  mode : LocalMode s

/-- The source one-based assignment start represented by the payload's
zero-based finite index. -/
def sourceStart {p : Parameters} {eta : LearningRate}
    (s : AssignmentStartPayload.Input p eta) : ℕ :=
  s.sigma.val + 1

/-- The source one-based calendar round represented by the local finite time. -/
def sourceRound {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : ℕ :=
  input.time.val + 1

/-- Every payload's source start lies in `[1,T]`, before any caller-supplied
grid-boundary comparison is made. -/
theorem sourceStart_mem_horizon {p : Parameters} {eta : LearningRate}
    (s : AssignmentStartPayload.Input p eta) : sourceStart s ≤ p.T := by
  simp only [sourceStart]
  exact Nat.succ_le_of_lt s.sigma.isLt

/-- A finite local time denotes a source round in `[1,T]`. -/
theorem sourceRound_mem_horizon {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) :
    1 ≤ sourceRound input ∧ sourceRound input ≤ p.T := by
  simp only [sourceRound]
  constructor
  · omega
  · exact Nat.succ_le_of_lt input.time.isLt

/-- Extend local complement weights by the frozen anchor on the retained slow
set. This is only a proof device for the existing recorder input. -/
def extendedCurrentWeights {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (j : Fin p.K) : ℝ :=
  if hj : j ∈ s.slowSet.val then s.anchor j else
    input.currentWeights ⟨j, by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩

/-- The extension equals the known anchor on every slow coordinate. -/
theorem extendedCurrentWeights_eq_anchor {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (j : Fin p.K) (hj : j ∈ s.slowSet.val) :
    extendedCurrentWeights input j = s.anchor j := by
  simp [extendedCurrentWeights, hj]

/-- On every actual fast coordinate the extension is exactly the supplied
local current weight. -/
theorem extendedCurrentWeights_eq_complement {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (j : FastArm s.slowSet) :
    extendedCurrentWeights input j.1 = input.currentWeights j := by
  have hj : j.1 ∉ s.slowSet.val := (Finset.mem_sdiff.mp j.2).2
  simp [extendedCurrentWeights, hj]

/-- Translate the local collection/live bit to the accepted recorder mode,
retaining exactly `s.assignment` in the live branch. -/
noncomputable def operationMode {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (mode : LocalMode s) :
    CoordinatorRecordingOperation.LocalMode p :=
  match mode with
  | .collection => .collection
  | .live confirmationsEmpty => .live s.assignment confirmationsEmpty

/-- The literal accepted recorder input when a particular global weight
extension is supplied. Every field except `currentWeights` comes from the
local adapter input and the assignment-start payload. -/
noncomputable def recorderInputWithWeights {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (weights : Fin p.K → ℝ) : CoordinatorRecordingOperation.Input p where
  eta := eta.val
  anchor := s.anchor
  currentWeights := weights
  sigma := sourceStart s
  time := input.time
  gridBoundary := input.gridBoundary
  row := input.row
  ownArm := input.ownArm
  observation := input.observation
  mode := operationMode input.mode

/-- The accepted recorder input with the proof-only slow-coordinate
extension. -/
noncomputable def recorderInput {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) :
    CoordinatorRecordingOperation.Input p :=
  recorderInputWithWeights input (extendedCurrentWeights input)

/-- Literal source-local input-domain checks: the declared source boundary is
within `[0,T+1]`, and supplied complement weights obey the source envelope.
These facts are not assumed by `Input` or used to bypass the recorder's run
time checks. -/
def LocalInputsValid {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : Prop :=
  input.gridBoundary ≤ p.T + 1 ∧
    ∀ j : FastArm s.slowSet,
      s.anchor j.1 ≤ input.currentWeights j ∧
        input.currentWeights j ≤ 2 * s.anchor j.1

/-- The proof extension satisfies `InputsValid` exactly when the local source
boundary and complement envelope checks hold. Payload rate, anchor, and source
start checks are discharged from `s`; the complement lower bound derives
positivity, and slow coordinates use the anchor by construction. -/
theorem recorderInput_inputsValid_iff {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) :
    CoordinatorRecordingOperation.InputsValid (recorderInput input) ↔
      LocalInputsValid input := by
  constructor
  · intro hvalid
    refine ⟨hvalid.boundary_le_terminal, ?_⟩
    intro j
    have hlow : s.anchor j.1 ≤ extendedCurrentWeights input j.1 :=
      hvalid.anchor_le_current j.1
    have hhigh : extendedCurrentWeights input j.1 ≤ 2 * s.anchor j.1 :=
      hvalid.current_le_twice_anchor j.1
    rw [extendedCurrentWeights_eq_complement input j] at hlow hhigh
    exact ⟨hlow, hhigh⟩
  · rintro ⟨hboundary, hcomplement⟩
    refine ⟨?_, hboundary, eta.property, s.eta_le_source_cap,
      s.anchor_pos, ?_, ?_, ?_⟩
    · change s.sigma.val + 1 ≤ p.T + 1
      omega
    · intro j
      change 0 < extendedCurrentWeights input j
      by_cases hj : j ∈ s.slowSet.val
      · rw [extendedCurrentWeights_eq_anchor input j hj]
        exact s.anchor_pos j
      · let k : FastArm s.slowSet := ⟨j, by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩
        rw [extendedCurrentWeights_eq_complement input k]
        exact (s.anchor_pos j).trans_le (hcomplement k).1
    · intro j
      change s.anchor j ≤ extendedCurrentWeights input j
      by_cases hj : j ∈ s.slowSet.val
      · rw [extendedCurrentWeights_eq_anchor input j hj]
      · let k : FastArm s.slowSet := ⟨j, by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩
        rw [extendedCurrentWeights_eq_complement input k]
        exact (hcomplement k).1
    · intro j
      change extendedCurrentWeights input j ≤ 2 * s.anchor j
      by_cases hj : j ∈ s.slowSet.val
      · rw [extendedCurrentWeights_eq_anchor input j hj]
        have hone : (1 : ℝ) ≤ 2 := by norm_num
        calc
          s.anchor j = 1 * s.anchor j := (one_mul _).symm
          _ ≤ 2 * s.anchor j :=
            mul_le_mul_of_nonneg_right hone (le_of_lt (s.anchor_pos j))
      · let k : FastArm s.slowSet := ⟨j, by
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩⟩
        rw [extendedCurrentWeights_eq_complement input k]
        exact (hcomplement k).2

/-- A local time/envelope validity proof supplies the exact runtime input
certificate consumed by the original recorder. -/
theorem recorderInput_inputsValid {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input) :
    CoordinatorRecordingOperation.InputsValid (recorderInput input) :=
  (recorderInput_inputsValid_iff input).2 hvalid

/-- The adapter runs the accepted checked operation on its proof extension;
its output and failure option are unchanged. -/
noncomputable def run {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) :
    Option (CoordinatorRecordingOperation.Output p) :=
  CoordinatorRecordingOperation.run (recorderInput input)

/-- Exact comparison with the accepted checked recorder. -/
theorem run_eq_accepted {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) :
    run input = CoordinatorRecordingOperation.run (recorderInput input) := rfl

/-- The local run exposes the original `executeValid` branch equations once
the source time and complement checks hold. -/
theorem run_eq_executeValid {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input) :
    run input = CoordinatorRecordingOperation.executeValid (recorderInput input)
      (recorderInput_inputsValid input hvalid) := by
  simp [run, CoordinatorRecordingOperation.run,
    recorderInput_inputsValid input hvalid]

/-- Invalid source boundary data is rejected by the accepted run. -/
theorem run_none_of_invalid_boundary {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hbad : ¬ input.gridBoundary ≤ p.T + 1) : run input = none := by
  apply CoordinatorRecordingOperation.run_none_of_invalid
  intro hvalid
  exact hbad ((recorderInput_inputsValid_iff input).mp hvalid).1

/-- Complement data below its source lower envelope is rejected by the
accepted run's actual `InputsValid` check. -/
theorem run_none_of_invalid_complement_lower {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (j : FastArm s.slowSet)
    (hbad : ¬ s.anchor j.1 ≤ input.currentWeights j) : run input = none := by
  apply CoordinatorRecordingOperation.run_none_of_invalid
  intro hvalid
  exact hbad (((recorderInput_inputsValid_iff input).mp hvalid).2 j).1

/-- Complement data above its source upper envelope is rejected by the
accepted run's actual `InputsValid` check. -/
theorem run_none_of_invalid_complement_upper {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (j : FastArm s.slowSet)
    (hbad : ¬ input.currentWeights j ≤ 2 * s.anchor j.1) : run input = none := by
  apply CoordinatorRecordingOperation.run_none_of_invalid
  intro hvalid
  exact hbad (((recorderInput_inputsValid_iff input).mp hvalid).2 j).2

/-- Nonpositive complement data fails the lower-envelope runtime check because
the assignment anchor is positive. -/
theorem run_none_of_nonpositive_complement {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (j : FastArm s.slowSet) (hbad : input.currentWeights j ≤ 0) :
    run input = none := by
  apply run_none_of_invalid_complement_lower input j
  intro hlow
  exact (not_le_of_gt ((s.anchor_pos j.1).trans_le hlow)) hbad

/-- The mode and arm-ownership tests are exactly those of the accepted local
recorder. A live slow-arm choice is therefore unowned by literal membership,
with no added reachability premise. -/
def ownsArm {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : Prop :=
  CoordinatorRecordingOperation.ownsArm (operationMode input.mode) input.ownArm

/-- Source frozen status on the proof-extended recorder input. -/
def isFrozen {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : Prop :=
  CoordinatorRecordingOperation.isFrozen (recorderInput input)

/-- A source round exactly at its one-based grid boundary is frozen whenever
the payload start is nonzero. -/
theorem isFrozen_at_grid_boundary {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hround : sourceRound input = input.gridBoundary) : isFrozen input := by
  apply CoordinatorRecordingOperation.isFrozen_at_source_boundary
  · simp [recorderInput, recorderInputWithWeights, sourceStart]
  · simpa [recorderInput, recorderInputWithWeights, sourceRound,
      CoordinatorRecordingOperation.sourceCalendarRound] using hround

/-- The source `T+1` boundary is a sentinel and never freezes an actual finite
calendar round. -/
theorem not_isFrozen_at_terminal_boundary {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hboundary : input.gridBoundary = p.T + 1) : ¬ isFrozen input := by
  apply CoordinatorRecordingOperation.not_isFrozen_at_terminal_boundary
  exact hboundary

/-- The local DATA slot selected from the supplied coordinator row. -/
noncomputable def selectedSlot {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : Slot :=
  CoordinatorRecordingOperation.selectedSlot (recorderInput input)

/-- The public recorder source selected from the supplied coordinator row. -/
noncomputable def selectedRecorder {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : Fin p.m :=
  CoordinatorRecordingOperation.selectedRecorder (recorderInput input)

/-- The accepted recorder's literal own-arm source-mask test. -/
def ownMaskPasses {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : Prop :=
  CoordinatorRecordingOperation.ownMaskPasses (recorderInput input)

/-- The thinning scalar from the coordinator's supplied complete row. -/
def thinScalar {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : ℝ :=
  (coordinate Label.thin (sliceAt input.time input.row.2)).val

/-- The accepted recorder's actual inclusive thinning threshold. -/
noncomputable def threshold {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input) : ℝ :=
  CoordinatorRecordingOperation.coordinatorThreshold (recorderInput input)
    (recorderInput_inputsValid input hvalid)

/-- The accepted recorder's actual integer arrival floor. -/
noncomputable def floorArrival {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s) : ℕ :=
  CoordinatorRecordingOperation.floorArrival (recorderInput input)

/-- A valid non-DATA row returns the accepted zero output with no gate. -/
theorem run_zero_of_not_data {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input ≠ dataSlot) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  rw [run_eq_executeValid input hvalid]
  exact CoordinatorRecordingOperation.executeValid_zero_of_not_data
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)

/-- A valid row selecting another recorder source returns no coordinator gate
or arrival. -/
theorem run_zero_of_other_source {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input ≠ coordinator p.two_le_m) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  rw [run_eq_executeValid input hvalid]
  exact CoordinatorRecordingOperation.executeValid_zero_of_other_source
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)
    (by simpa [selectedRecorder, recorderInput, recorderInputWithWeights] using hsource)

/-- A valid, DATA-selected source call is stopped at the source cutoff. -/
theorem run_zero_of_frozen {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hfrozen : isFrozen input) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  rw [run_eq_executeValid input hvalid]
  exact CoordinatorRecordingOperation.executeValid_zero_of_frozen
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)
    (by simpa [selectedRecorder, recorderInput, recorderInputWithWeights] using hsource)
    (by simpa [isFrozen, recorderInput, recorderInputWithWeights] using hfrozen)

/-- A live choice of a slow-assignment arm follows the accepted literal
ownership rejection branch. -/
theorem run_zero_of_unowned {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotFrozen : ¬ isFrozen input)
    (hnotOwned : ¬ ownsArm input) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  rw [run_eq_executeValid input hvalid]
  exact CoordinatorRecordingOperation.executeValid_zero_of_unowned
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)
    (by simpa [selectedRecorder, recorderInput, recorderInputWithWeights] using hsource)
    (by simpa [isFrozen, recorderInput, recorderInputWithWeights] using hnotFrozen)
    (by simpa [ownsArm, operationMode, recorderInput, recorderInputWithWeights] using hnotOwned)

/-- An owned source arm rejected by the complete-row mask retains the accepted
zero output. -/
theorem run_zero_of_mask_rejected {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotFrozen : ¬ isFrozen input) (howned : ownsArm input)
    (hmask : ¬ ownMaskPasses input) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  rw [run_eq_executeValid input hvalid]
  exact CoordinatorRecordingOperation.executeValid_zero_of_mask_rejected
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)
    (by simpa [selectedRecorder, recorderInput, recorderInputWithWeights] using hsource)
    (by simpa [isFrozen, recorderInput, recorderInputWithWeights] using hnotFrozen)
    (by simpa [ownsArm, operationMode, recorderInput, recorderInputWithWeights] using howned)
    (by simpa [ownMaskPasses, recorderInput, recorderInputWithWeights] using hmask)

/-- A valid owned source call that fails the inclusive thinning comparison
retains the accepted zero output and carries no gate arm. -/
theorem run_zero_of_thinning_rejected {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotFrozen : ¬ isFrozen input) (howned : ownsArm input)
    (hmask : ownMaskPasses input)
    (hthin : ¬ thinScalar input ≤ threshold input hvalid) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  rw [run_eq_executeValid input hvalid]
  exact CoordinatorRecordingOperation.executeValid_zero_of_thinning_rejected
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)
    (by simpa [selectedRecorder, recorderInput, recorderInputWithWeights] using hsource)
    (by simpa [isFrozen, recorderInput, recorderInputWithWeights] using hnotFrozen)
    (by simpa [ownsArm, operationMode, recorderInput, recorderInputWithWeights] using howned)
    (by simpa [ownMaskPasses, recorderInput, recorderInputWithWeights] using hmask)
    (by simpa [threshold, thinScalar, recorderInput, recorderInputWithWeights] using hthin)

/-- A successful inclusive thinning test returns both the gate arm and the
literal floor arrival, retaining a zero arrival as a successful gate. -/
theorem run_gate_and_floor {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotFrozen : ¬ isFrozen input) (howned : ownsArm input)
    (hmask : ownMaskPasses input)
    (hthin : thinScalar input ≤ threshold input hvalid) :
    ∃ out, run input = some out ∧ out.gateArm = some input.ownArm ∧
      out.rawArrival = floorArrival input := by
  rw [run_eq_executeValid input hvalid]
  obtain ⟨out, hout, hgate, harrival⟩ :=
    CoordinatorRecordingOperation.executeValid_gate_and_floor
      (recorderInput input) (recorderInput_inputsValid input hvalid)
      (by simpa [selectedSlot, recorderInput, recorderInputWithWeights] using hdata)
      (by simpa [selectedRecorder, recorderInput, recorderInputWithWeights] using hsource)
      (by simpa [isFrozen, recorderInput, recorderInputWithWeights] using hnotFrozen)
      (by simpa [ownsArm, operationMode, recorderInput, recorderInputWithWeights] using howned)
      (by simpa [ownMaskPasses, recorderInput, recorderInputWithWeights] using hmask)
      (by simpa [threshold, thinScalar, recorderInput, recorderInputWithWeights] using hthin)
  exact ⟨out, hout, hgate, by simpa [floorArrival, recorderInput, recorderInputWithWeights] using harrival⟩

/-- The zero grid observation has exactly zero source reward and hence zero
integer floor, without suppressing a successful gate. -/
def zeroObservation (p : Parameters) : Fin (D p + 1) :=
  ⟨0, Nat.succ_pos _⟩

theorem floorArrival_zeroObservation {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hzero : input.observation = zeroObservation p) : floorArrival input = 0 := by
  unfold floorArrival CoordinatorRecordingOperation.floorArrival
  simp [recorderInput, recorderInputWithWeights, hzero, zeroObservation,
    RealRewardGridCount.realRewardGridValue]

/-- A successful gate at the zero observation is represented by
`some ownArm` together with raw arrival `0`, distinct from the no-gate output. -/
theorem run_gate_with_zero_observation {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotFrozen : ¬ isFrozen input) (howned : ownsArm input)
    (hmask : ownMaskPasses input)
    (hthin : thinScalar input ≤ threshold input hvalid)
    (hzero : input.observation = zeroObservation p) :
    ∃ out, run input = some out ∧ out.gateArm = some input.ownArm ∧
      out.rawArrival = 0 := by
  obtain ⟨out, hout, hgate, harrival⟩ := run_gate_and_floor input hvalid
    hdata hsource hnotFrozen howned hmask hthin
  exact ⟨out, hout, hgate, by rw [harrival, floorArrival_zeroObservation input hzero]⟩

/-- The assignment-induced slow set is precisely the supplied payload set. -/
theorem assignmentSlowSet_eq_payload {p : Parameters} {eta : LearningRate}
    (s : AssignmentStartPayload.Input p eta) :
    SnapshotRecordingKernel.assignmentSlowSet p s.assignment = s.slowSet := by
  apply Subtype.ext
  exact s.assignment_image

/-- A supplied live arm in the payload's slow set fails the accepted literal
ownership test. This uses the payload's exact assignment-set equality and no
arm-choice or reachability premise. -/
theorem run_zero_of_live_slow_arm {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (hdata : selectedSlot input = dataSlot)
    (hsource : selectedRecorder input = coordinator p.two_le_m)
    (hnotFrozen : ¬ isFrozen input)
    (confirmationsEmpty : Bool)
    (hmode : input.mode = .live confirmationsEmpty)
    (hslow : input.ownArm ∈ s.slowSet.val) :
    run input = some (CoordinatorRecordingOperation.zeroOutput p) := by
  apply run_zero_of_unowned input hvalid hdata hsource hnotFrozen
  intro howned
  have howned' : CoordinatorRecordingOperation.ownsArm
      (.live s.assignment confirmationsEmpty) input.ownArm := by
    simpa [ownsArm, operationMode, hmode] using howned
  have hfast : input.ownArm ∉ s.slowSet.val := by
    simpa [CoordinatorRecordingOperation.ownsArm,
      assignmentSlowSet_eq_payload s] using howned'
  exact hfast hslow

/-- The coordinator's qGamma probability in the collection branch is `1/K`,
so it does not inspect the supplied current weights. -/
theorem armProbability_collection {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input) (hmode : input.mode = .collection) :
    CoordinatorRecordingOperation.coordinatorArmProbability (recorderInput input)
      (recorderInput_inputsValid input hvalid) = 1 / (p.K : ℝ) := by
  have hmode' : (recorderInput input).mode =
      CoordinatorRecordingOperation.LocalMode.collection := by
    simp [recorderInput, recorderInputWithWeights, operationMode, hmode]
  exact CoordinatorRecordingOperation.coordinatorArmProbability_collection
    (recorderInput input) (recorderInput_inputsValid input hvalid) hmode'

/-- With live confirmations still missing, the coordinator uses `1/K` and
the current weights are again irrelevant to its action probability. -/
theorem armProbability_live_confirmations_missing {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input) :
    input.mode = .live false →
      CoordinatorRecordingOperation.coordinatorArmProbability (recorderInput input)
        (recorderInput_inputsValid input hvalid) = 1 / (p.K : ℝ) := by
  intro hmode
  have hmode' : (recorderInput input).mode =
      CoordinatorRecordingOperation.LocalMode.live s.assignment false := by
    simp [recorderInput, recorderInputWithWeights, operationMode, hmode]
  exact CoordinatorRecordingOperation.coordinatorArmProbability_live_confirmations_missing
    (recorderInput input) (recorderInput_inputsValid input hvalid)
    s.assignment hmode'

/-- The recorder output and the accepted run of every other globally valid
extension agreeing on the supplied complement are equal. The visible local
envelope premises remain explicit; this comparison claims no hidden slow
current-weight fact. -/
theorem run_eq_of_valid_extension {p : Parameters} {eta : LearningRate}
    {s : AssignmentStartPayload.Input p eta} (input : Input s)
    (hvalid : LocalInputsValid input)
    (weights' : Fin p.K → ℝ)
    (hvalid' : CoordinatorRecordingOperation.InputsValid
      (recorderInputWithWeights input weights'))
    (heq : ∀ j : FastArm s.slowSet,
      weights' j.1 = input.currentWeights j) :
    run input = CoordinatorRecordingOperation.run
      (recorderInputWithWeights input weights') := by
  let original := recorderInput input
  let alternate := recorderInputWithWeights input weights'
  have horiginalValid : CoordinatorRecordingOperation.InputsValid original :=
    recorderInput_inputsValid input hvalid
  have hslow : SnapshotRecordingKernel.assignmentSlowSet p s.assignment =
      s.slowSet := assignmentSlowSet_eq_payload s
  have hprob : CoordinatorRecordingOperation.coordinatorArmProbability original
        horiginalValid =
      CoordinatorRecordingOperation.coordinatorArmProbability alternate hvalid' := by
    cases hmode : input.mode with
    | collection =>
        simp [CoordinatorRecordingOperation.coordinatorArmProbability,
          original, alternate, recorderInput, recorderInputWithWeights,
          operationMode, hmode]
    | live confirmationsEmpty =>
        cases confirmationsEmpty with
        | false =>
            simp [CoordinatorRecordingOperation.coordinatorArmProbability,
              original, alternate, recorderInput, recorderInputWithWeights,
              operationMode, hmode]
        | true =>
            have hmodeOriginal : original.mode =
                CoordinatorRecordingOperation.LocalMode.live s.assignment true := by
              simp [original, recorderInput, recorderInputWithWeights,
                operationMode, hmode]
            have hmodeAlternate : alternate.mode =
                CoordinatorRecordingOperation.LocalMode.live s.assignment true := by
              simp [alternate, recorderInputWithWeights, operationMode, hmode]
            by_cases hfast : input.ownArm ∈
                CanonicalFastSampling.fastArmFinset
                  (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
            · have hfastOriginal : input.ownArm ∈
                  CanonicalFastSampling.fastArmFinset
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment) := hfast
              have hfastAlternate := hfast
              have hweightEq : ∀ j : Fin p.K,
                  j ∉ (SnapshotRecordingKernel.assignmentSlowSet p s.assignment).val →
                    extendedCurrentWeights input j = weights' j := by
                intro j hj
                have hj' : j ∉ s.slowSet.val := by
                  simpa [hslow] using hj
                let k : FastArm s.slowSet := ⟨j, by
                  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj'⟩⟩
                rw [extendedCurrentWeights_eq_complement input k]
                exact (heq k).symm
              have hfastOriginalMem : original.ownArm ∈
                  (Finset.univ : Finset (Fin p.K)) \
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment).val := by
                simpa [CanonicalFastSampling.fastArmFinset, original,
                  recorderInput, recorderInputWithWeights] using hfastOriginal
              have hfastAlternateMem : alternate.ownArm ∈
                  (Finset.univ : Finset (Fin p.K)) \
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment).val := by
                simpa [CanonicalFastSampling.fastArmFinset, alternate,
                  recorderInputWithWeights] using hfastAlternate
              have hfastMem : input.ownArm ∈
                  (Finset.univ : Finset (Fin p.K)) \
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment).val := by
                simpa [CanonicalFastSampling.fastArmFinset] using hfast
              let originalFast : FastArm
                  (SnapshotRecordingKernel.assignmentSlowSet p s.assignment) :=
                ⟨original.ownArm, hfastOriginalMem⟩
              let alternateFast : FastArm
                  (SnapshotRecordingKernel.assignmentSlowSet p s.assignment) :=
                ⟨alternate.ownArm, hfastAlternateMem⟩
              let suppliedFast : FastArm
                  (SnapshotRecordingKernel.assignmentSlowSet p s.assignment) :=
                ⟨input.ownArm, hfastMem⟩
              have hq := FastComplementLocality.qGamma_eq_of_eq_on_complement
                p eta.property s.eta_le_source_cap s.anchor
                (extendedCurrentWeights input) weights' s.anchor_pos
                horiginalValid.current_pos
                hvalid'.current_pos horiginalValid.anchor_le_current
                hvalid'.anchor_le_current horiginalValid.current_le_twice_anchor
                hvalid'.current_le_twice_anchor
                (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                hweightEq suppliedFast
              have hprobOriginal :=
                CoordinatorRecordingOperation.coordinatorArmProbability_live_confirmed
                  original horiginalValid s.assignment hmodeOriginal hfastOriginal
              have hprobAlternate :=
                CoordinatorRecordingOperation.coordinatorArmProbability_live_confirmed
                  alternate hvalid' s.assignment hmodeAlternate hfastAlternate
              have hq' :
                  CanonicalFastSampling.qGamma p eta.val eta.property
                    s.eta_le_source_cap s.anchor original.currentWeights
                    horiginalValid.anchor_pos horiginalValid.current_pos
                    horiginalValid.anchor_le_current
                    horiginalValid.current_le_twice_anchor
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                    originalFast =
                  CanonicalFastSampling.qGamma p eta.val eta.property
                    s.eta_le_source_cap s.anchor alternate.currentWeights
                    hvalid'.anchor_pos hvalid'.current_pos hvalid'.anchor_le_current
                    hvalid'.current_le_twice_anchor
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                    alternateFast := by
                have hOriginalIndex : originalFast = suppliedFast := by
                  apply Subtype.ext
                  rfl
                have hAlternateIndex : alternateFast = suppliedFast := by
                  apply Subtype.ext
                  rfl
                simpa [original, alternate, recorderInput, recorderInputWithWeights,
                  originalFast, alternateFast, suppliedFast, hOriginalIndex,
                  hAlternateIndex] using hq
              have hprobOriginal' :
                  CoordinatorRecordingOperation.coordinatorArmProbability original
                    horiginalValid =
                  CanonicalFastSampling.qGamma p original.eta
                    horiginalValid.eta_pos horiginalValid.eta_source_cap
                    original.anchor original.currentWeights horiginalValid.anchor_pos
                    horiginalValid.current_pos horiginalValid.anchor_le_current
                    horiginalValid.current_le_twice_anchor
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                    originalFast := by
                rw [hprobOriginal]
              have hprobAlternate' :
                  CoordinatorRecordingOperation.coordinatorArmProbability alternate hvalid' =
                  CanonicalFastSampling.qGamma p alternate.eta
                    hvalid'.eta_pos hvalid'.eta_source_cap alternate.anchor alternate.currentWeights
                    hvalid'.anchor_pos hvalid'.current_pos hvalid'.anchor_le_current
                    hvalid'.current_le_twice_anchor
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                    alternateFast := by
                rw [hprobAlternate]
              have hqFinal :
                  CanonicalFastSampling.qGamma p original.eta
                    horiginalValid.eta_pos horiginalValid.eta_source_cap
                    original.anchor original.currentWeights horiginalValid.anchor_pos
                    horiginalValid.current_pos horiginalValid.anchor_le_current
                    horiginalValid.current_le_twice_anchor
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                    originalFast =
                  CanonicalFastSampling.qGamma p alternate.eta
                    hvalid'.eta_pos hvalid'.eta_source_cap alternate.anchor
                    alternate.currentWeights hvalid'.anchor_pos hvalid'.current_pos
                    hvalid'.anchor_le_current hvalid'.current_le_twice_anchor
                    (SnapshotRecordingKernel.assignmentSlowSet p s.assignment)
                    alternateFast := by
                simpa [original, alternate, recorderInput, recorderInputWithWeights] using hq'
              rw [hprobOriginal', hprobAlternate', hqFinal]
            · have hprobOriginal :
                  CoordinatorRecordingOperation.coordinatorArmProbability original
                    horiginalValid = 0 := by
                have hnotfast : original.ownArm ∉
                    CanonicalFastSampling.fastArmFinset
                      (SnapshotRecordingKernel.assignmentSlowSet p s.assignment) := by
                  simpa [original, recorderInput, recorderInputWithWeights] using hfast
                simp [CoordinatorRecordingOperation.coordinatorArmProbability,
                  hmodeOriginal, hnotfast]
              have hprobAlternate :
                  CoordinatorRecordingOperation.coordinatorArmProbability alternate
                    hvalid' = 0 := by
                have hnotfast : alternate.ownArm ∉
                    CanonicalFastSampling.fastArmFinset
                      (SnapshotRecordingKernel.assignmentSlowSet p s.assignment) := by
                  simpa [alternate, recorderInputWithWeights] using hfast
                simp [CoordinatorRecordingOperation.coordinatorArmProbability,
                  hmodeAlternate, hnotfast]
              rw [hprobOriginal, hprobAlternate]

  have hraw : CoordinatorRecordingOperation.coordinatorRawGateMass original
      horiginalValid = CoordinatorRecordingOperation.coordinatorRawGateMass
        alternate hvalid' := by
    simp [CoordinatorRecordingOperation.coordinatorRawGateMass, hprob]
  have heta : original.eta = alternate.eta := rfl
  have hanchor : original.anchor = alternate.anchor := rfl
  have harm : original.ownArm = alternate.ownArm := rfl
  have htime : original.time = alternate.time := rfl
  have hboundary : original.gridBoundary = alternate.gridBoundary := rfl
  have hsigma : original.sigma = alternate.sigma := rfl
  have hrow : original.row = alternate.row := rfl
  have hmodeInput : original.mode = alternate.mode := rfl
  have hobs : original.observation = alternate.observation := rfl
  have hfloor : CoordinatorRecordingOperation.floorArrival original =
      CoordinatorRecordingOperation.floorArrival alternate := by
    simp only [CoordinatorRecordingOperation.floorArrival]
    rw [heta, hanchor, harm, hobs]
  have hslot : CoordinatorRecordingOperation.selectedSlot original =
      CoordinatorRecordingOperation.selectedSlot alternate := by
    simp [CoordinatorRecordingOperation.selectedSlot, htime, hrow]
  have hsource : CoordinatorRecordingOperation.selectedRecorder original =
      CoordinatorRecordingOperation.selectedRecorder alternate := by
    simp [CoordinatorRecordingOperation.selectedRecorder, htime, hrow]
  have hfrozen : CoordinatorRecordingOperation.isFrozen original =
      CoordinatorRecordingOperation.isFrozen alternate := by
    simp [CoordinatorRecordingOperation.isFrozen,
      CoordinatorRecordingOperation.sourceCalendarRound,
      htime, hboundary, hsigma]
  have howns : CoordinatorRecordingOperation.ownsArm original.mode original.ownArm =
      CoordinatorRecordingOperation.ownsArm alternate.mode alternate.ownArm := by
    rw [hmodeInput, harm]
  have hmask : CoordinatorRecordingOperation.ownMaskPasses original =
      CoordinatorRecordingOperation.ownMaskPasses alternate := by
    unfold CoordinatorRecordingOperation.ownMaskPasses
    rw [harm, htime, hrow]
  have hthinValue :
      (coordinate Label.thin (sliceAt original.time original.row.2)).val =
        (coordinate Label.thin (sliceAt alternate.time alternate.row.2)).val := by
    rw [htime, hrow]
  have hexecute : CoordinatorRecordingOperation.executeValid original horiginalValid =
      CoordinatorRecordingOperation.executeValid alternate hvalid' := by
    unfold CoordinatorRecordingOperation.executeValid
    rw [hslot, hsource, hfrozen, howns, hmask, hraw,
      heta, hanchor, harm, hthinValue, hfloor]
  simp [run, original, alternate, CoordinatorRecordingOperation.run,
    horiginalValid, hvalid', hexecute]

end Bandits.Support.CoordinatorRecorderComplementBridge

end
