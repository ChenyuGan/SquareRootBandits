/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.AssignmentStartPayload
public import Bandits.Support.CompletePublicTable
public import Bandits.Support.ContinuousLearningRows
public import Bandits.Support.FastComplementLocality
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.OrderedTupleSampler
public import Bandits.Support.PublicDiscreteDraws
public import Bandits.Support.RealRewardGridCount

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Lean.Elab.Tactic.Omega

/-!
# Literal coordinator local arm choice and DOWN confirmation

The branch order is the coordinator part of
`sources/zip4/manuscript/05_binary_transport.tex:94-103`. Live confirmation
removal is `sources/zip4/manuscript/05_binary_transport.tex:74-80` and
`sources/zip4/manuscript/06_interruptions.tex:286-289`; local time and typed
input rules are `sources/zip4/manuscript/06_interruptions.tex:46-61` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The operation consumes only the coordinator's stored assignment payload,
pending set, optional finite cutoff, current complement weights, its declared
row/time control, and (for confirmation) its own typed grid observation.
Input checks return `none` before an arm is sampled or a pending set is
stored. This file constructs no shared run, status, history, feedback source,
or physical provenance claim.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorLocalArmChoice

open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.CanonicalRecordingRates
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.FastComplementLocality
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ConstructorDimensions
open Bandits.Support.FiniteBanditModel

variable {p : ConstructorDimensions.Parameters} {eta : LearningRate}

local instance optionFinMeasurableSpace (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤
local instance optionPendingMeasurableSpace :
    MeasurableSpace (Option (Finset (Follower p.m))) := ⊤

private theorem measurable_some_arm :
    Measurable (fun a : Arm p.K => some a) :=
  measurable_of_countable _

private theorem measurable_some_pending :
    Measurable (fun P : Finset (Follower p.m) => some P) :=
  measurable_of_countable _

/-- A cutoff uses the existing one-based finite endpoint carrier `[1,T+1]`;
`none` denotes the source sentinel `T+1`. -/
abbrev Cutoff (p : ConstructorDimensions.Parameters) :=
  ReferencePrelaunchFollower.Activation p

/-- The source one-based round represented by a calendar index. -/
def sourceRound (t : Fin p.T) : ℕ := t.val + 1

/-- The assignment's source one-based start, from its stored zero-based index. -/
def assignmentStart (s : AssignmentStartPayload.Input p eta) : ℕ :=
  s.sigma.val + 1

/-- A missing cutoff is the manuscript's terminal endpoint `T+1`. -/
def cutoffRound (u : Option (Cutoff p)) : ℕ :=
  u.elim (p.T + 1) fun v => v.val

/-- The assignment is live precisely before its local cutoff. -/
def assignmentIsLive (s : AssignmentStartPayload.Input p eta)
    (u : Option (Cutoff p)) (t : Fin p.T) : Prop :=
  assignmentStart s ≤ sourceRound t ∧ sourceRound t < cutoffRound u

/-- Honest source time checks for one stored assignment and one declared
calendar slot. No assertion is made that the payload or cutoff came from a
physical history. -/
structure SourceTimeValid (s : AssignmentStartPayload.Input p eta)
    (u : Option (Cutoff p)) (t : Fin p.T) : Prop where
  source_round_pos : 1 ≤ sourceRound t
  source_round_le_horizon : sourceRound t ≤ p.T
  cutoff_pos : 1 ≤ cutoffRound u
  cutoff_le_terminal : cutoffRound u ≤ p.T + 1
  assignment_started : assignmentStart s ≤ sourceRound t
  cutoff_after_start : assignmentStart s ≤ cutoffRound u

/-- Checked positive source parameters and the literal current-weight envelope
on the actual fast complement only. -/
structure ChoiceInputsValid (s : AssignmentStartPayload.Input p eta)
    (u : Option (Cutoff p)) (t : Fin p.T)
    (w : FastArm s.slowSet → ℝ) : Prop where
  time : SourceTimeValid s u t
  learning_rate_pos : 0 < eta.val
  learning_rate_le_source_cap : eta.val ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))
  anchor_pos : ∀ a, 0 < s.anchor a
  current_weight_pos : ∀ j, 0 < w j
  anchor_le_current : ∀ j, s.anchor j.1 ≤ w j
  current_le_twice_anchor : ∀ j, w j ≤ 2 * s.anchor j.1

/-- The confirmation update needs no current weights: it checks the same
one-based time and stored positive source parameters before storing `P`. -/
structure ConfirmationInputsValid
    (s : AssignmentStartPayload.Input p eta) (u : Option (Cutoff p))
    (t : Fin p.T) : Prop where
  time : SourceTimeValid s u t
  learning_rate_pos : 0 < eta.val
  learning_rate_le_source_cap : eta.val ≤
    1 / (1024 * (p.m : ℝ) * (p.K : ℝ) * (L_stab p : ℝ))
  anchor_pos : ∀ a, 0 < s.anchor a

/-- All checks hold when the source time relations and current fast-arm
envelope hold. The source-parameter fields are checked from the carried
payload fields themselves. -/
theorem choiceInputsValid_mk (s : AssignmentStartPayload.Input p eta)
    (u : Option (Cutoff p)) (t : Fin p.T) (w : FastArm s.slowSet → ℝ)
    (hstarted : assignmentStart s ≤ sourceRound t)
    (hcutoff : assignmentStart s ≤ cutoffRound u)
    (hw : ∀ j, 0 < w j ∧ s.anchor j.1 ≤ w j ∧ w j ≤ 2 * s.anchor j.1) :
    ChoiceInputsValid s u t w := by
  refine ⟨?_, eta.property, s.eta_le_source_cap, s.anchor_pos,
    (fun j => (hw j).1), (fun j => (hw j).2.1), (fun j => (hw j).2.2)⟩
  refine ⟨by simp [sourceRound], ?_, ?_, ?_, hstarted, hcutoff⟩
  · have ht := t.isLt
    simp only [sourceRound]
    omega
  · cases u with
    | none => simp [cutoffRound]
    | some v => exact v.property.1
  · cases u with
    | none => simp [cutoffRound]
    | some v => exact v.property.2

/-- The source parameters and times needed by the confirmation storage step. -/
theorem confirmationInputsValid_mk (s : AssignmentStartPayload.Input p eta)
    (u : Option (Cutoff p)) (t : Fin p.T)
    (hstarted : assignmentStart s ≤ sourceRound t)
    (hcutoff : assignmentStart s ≤ cutoffRound u) :
    ConfirmationInputsValid s u t := by
  refine ⟨?_, eta.property, s.eta_le_source_cap, s.anchor_pos⟩
  refine ⟨by simp [sourceRound], ?_, ?_, ?_, hstarted, hcutoff⟩
  · have ht := t.isLt
    simp only [sourceRound]
    omega
  · cases u with
    | none => simp [cutoffRound]
    | some v => exact v.property.1
  · cases u with
    | none => simp [cutoffRound]
    | some v => exact v.property.2

/-- The reserved DOWN affine channel is direction `0`, follower `i`. -/
def downChannel (i : Follower p.m) : Channel p := (0, i)

/-- The coordinator's actual stored outgoing DOWN word at follower `i`,
flattened through the accepted five-block codec equivalence. -/
def storedDownFlatWord (s : AssignmentStartPayload.Input p eta)
    (i : Follower p.m) : Word (B p) :=
  wordEquivFlat (codecParams p eta) (s.downWord i)

/-- The current affine hash of the coordinator's own stored DOWN word. -/
def currentDownHash (s : AssignmentStartPayload.Input p eta)
    (timeInput : TimeControl p) (i : Follower p.m) : Bit :=
  affineHash (timeInput.2 (downChannel i)) (storedDownFlatWord s i)

/-- The inverse-CDF fast draw uses the existing reserved `fast` slice
coordinate and receives current weights only on `FastArm s.slowSet`. -/
noncomputable def localFastDraw
    (s : AssignmentStartPayload.Input p eta) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ)
    (hvalid : ChoiceInputsValid s u t w) (timeInput : TimeControl p) :
    FastArm s.slowSet :=
  sampleLocalFast p eta.val hvalid.learning_rate_pos
    hvalid.learning_rate_le_source_cap s.anchor hvalid.anchor_pos s.slowSet w
    hvalid.current_weight_pos hvalid.anchor_le_current hvalid.current_le_twice_anchor
    (coordinate ContinuousControlSlice.Label.fast timeInput.1)

/-- Literal coordinator arm-choice operation on one local time control. Input
checks precede every draw. The branch order is live-and-empty, DATA, selected
DOWN, then `R₀`; collection therefore keeps sending old DOWN words. -/
noncomputable def coordinatorArmChoiceCore
    (s : AssignmentStartPayload.Input p eta) (pendingAtChoice : Finset (Follower p.m))
    (u : Option (Cutoff p)) (t : Fin p.T) (w : FastArm s.slowSet → ℝ)
    (timeInput : TimeControl p) : Option (Arm p.K) := by
  classical
  exact if hvalid : ChoiceInputsValid s u t w then
    if assignmentIsLive s u t ∧ pendingAtChoice = ∅ then
      some (localFastDraw s u t w hvalid timeInput).1
    else if slotDraw timeInput.1 = dataSlot then
      some (pilotDraw (K_pos p) (coordinator p.two_le_m) timeInput.1)
    else if slotDraw timeInput.1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈ pendingAtChoice then
      let i := selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1
      let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1
      some (sendArm (currentDownHash s timeInput i)
        (tuple.val (coordinator p.two_le_m))
        (tuple.val (followerPlayer p.two_le_m i)))
    else
      some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
        (coordinator p.two_le_m))
  else none

/-- Complete-row coordinator choice reads only `row`'s declared current
learning/control slice. -/
noncomputable def coordinatorArmChoice
    (s : AssignmentStartPayload.Input p eta) (pendingAtChoice : Finset (Follower p.m))
    (u : Option (Cutoff p)) (t : Fin p.T) (w : FastArm s.slowSet → ℝ)
    (row : CompleteRow p) : Option (Arm p.K) :=
  coordinatorArmChoiceCore s pendingAtChoice u t w (row.2 t)

/-- Collection and live status are derived only from the one-based source
calendar time and the stored cutoff. -/
def confirmationLive (s : AssignmentStartPayload.Input p eta)
    (u : Option (Cutoff p)) (t : Fin p.T) : Prop :=
  assignmentIsLive s u t

/-- The coordinator's typed grid observation as its actual source reward in
`[0,1]`. -/
def ownGridObservationValue (observation : Fin (D p + 1)) : ℝ :=
  realRewardGridValue (D p) (D_pos p) observation

/-- The locally computed live confirmation event. No accept flag, supplied
hash, receiver record, or collision premise is an input. -/
def downConfirmationEvent
    (s : AssignmentStartPayload.Input p eta) (pendingAtChoice : Finset (Follower p.m))
    (u : Option (Cutoff p)) (t : Fin p.T) (timeInput : TimeControl p)
    (observation : Fin (D p + 1)) : Prop :=
  confirmationLive s u t ∧ pendingAtChoice.Nonempty ∧
    slotDraw timeInput.1 = downSlot ∧
    selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈ pendingAtChoice ∧
    currentDownHash s timeInput
      (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1) = 0 ∧
    0 < ownGridObservationValue observation

/-- Apply exactly the ordinary live DOWN confirmation rule to the pending set
at choice. Collection returns it unchanged, including while old DOWN words
continue to be sent. -/
noncomputable def confirmationUpdateCore
    (s : AssignmentStartPayload.Input p eta) (pendingAtChoice : Finset (Follower p.m))
    (u : Option (Cutoff p)) (t : Fin p.T) (timeInput : TimeControl p)
    (observation : Fin (D p + 1)) : Option (Finset (Follower p.m)) := by
  classical
  exact if _hvalid : ConfirmationInputsValid s u t then
    some (if downConfirmationEvent s pendingAtChoice u t timeInput observation then
      pendingAtChoice.erase (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1)
    else pendingAtChoice)
  else none

/-- Complete-row confirmation reads only the coordinator's declared current
time control and its own typed grid observation. -/
noncomputable def confirmationUpdate
    (s : AssignmentStartPayload.Input p eta) (pendingAtChoice : Finset (Follower p.m))
    (u : Option (Cutoff p)) (t : Fin p.T) (row : CompleteRow p)
    (observation : Fin (D p + 1)) : Option (Finset (Follower p.m)) :=
  confirmationUpdateCore s pendingAtChoice u t (row.2 t) observation

/-- The typed grid observation is positive exactly when its natural index is
positive. -/
theorem ownGridObservationValue_pos_iff (observation : Fin (D p + 1)) :
    0 < ownGridObservationValue (p := p) observation ↔ 0 < observation.val := by
  unfold ownGridObservationValue realRewardGridValue
  have hD : (0 : ℝ) < D p := by exact_mod_cast D_pos p
  constructor
  · intro h
    by_contra hn
    have hz : observation.val = 0 := by omega
    simp [hz] at h
  · intro h
    exact div_pos (by exact_mod_cast h) hD

/-- Invalid required local time/parameter/weight domains fail explicitly
before sampling. -/
theorem coordinatorArmChoiceCore_none_of_invalid
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (timeInput : TimeControl p)
    (hvalid : ¬ ChoiceInputsValid s u t w) :
    coordinatorArmChoiceCore s pendingAtChoice u t w timeInput = none := by
  simp [coordinatorArmChoiceCore, hvalid]

/-- A valid live assignment with no missing confirmations uses the reserved
fast scalar on every slot. -/
theorem coordinatorArmChoiceCore_live_empty
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (timeInput : TimeControl p)
    (hvalid : ChoiceInputsValid s u t w)
    (hlive : assignmentIsLive s u t) (hempty : pendingAtChoice = ∅) :
    coordinatorArmChoiceCore s pendingAtChoice u t w timeInput =
      some (localFastDraw s u t w hvalid timeInput).1 := by
  simp [coordinatorArmChoiceCore, hvalid, hlive, hempty]

/-- With missing confirmations, DATA uses the coordinator's own pilot. -/
theorem coordinatorArmChoiceCore_data
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (timeInput : TimeControl p)
    (hvalid : ChoiceInputsValid s u t w)
    (hnotfast : ¬ (assignmentIsLive s u t ∧ pendingAtChoice = ∅))
    (hdata : slotDraw timeInput.1 = dataSlot) :
    coordinatorArmChoiceCore s pendingAtChoice u t w timeInput =
      some (pilotDraw (K_pos p) (coordinator p.two_le_m) timeInput.1) := by
  simp [coordinatorArmChoiceCore, hvalid, hnotfast, hdata]

/-- On a selected pending DOWN, SendArm uses the actual stored word flattened
to the accepted affine carrier and the current `(DOWN,i)` sample. -/
theorem coordinatorArmChoiceCore_down
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (timeInput : TimeControl p)
    (hvalid : ChoiceInputsValid s u t w)
    (hnotfast : ¬ (assignmentIsLive s u t ∧ pendingAtChoice = ∅))
    (hnotdata : slotDraw timeInput.1 ≠ dataSlot)
    (hdown : slotDraw timeInput.1 = downSlot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈
      pendingAtChoice) :
    coordinatorArmChoiceCore s pendingAtChoice u t w timeInput =
      some (sendArm
        (currentDownHash s timeInput
          (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (followerPlayer p.two_le_m
            (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1)))) := by
  have hdownNeData : downSlot ≠ dataSlot := fun heq =>
    hnotdata (hdown.trans heq)
  simp [coordinatorArmChoiceCore, hvalid, hnotfast, hdownNeData, hdown, hselected]

/-- The default branch returns the current coordinator tuple arm. -/
theorem coordinatorArmChoiceCore_other
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (timeInput : TimeControl p)
    (hvalid : ChoiceInputsValid s u t w)
    (hnotfast : ¬ (assignmentIsLive s u t ∧ pendingAtChoice = ∅))
    (hnotdata : slotDraw timeInput.1 ≠ dataSlot)
    (hnotdown : ¬ (slotDraw timeInput.1 = downSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈ pendingAtChoice)) :
    coordinatorArmChoiceCore s pendingAtChoice u t w timeInput =
      some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
        (coordinator p.two_le_m)) := by
  simp [coordinatorArmChoiceCore, hvalid, hnotfast, hnotdata, hnotdown]

/-- In collection, old DOWN records remain selected from the retained local
pending set; the cutoff only disables the fast-confirmed live branch. -/
theorem coordinatorArmChoiceCore_collection_down
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (timeInput : TimeControl p)
    (hvalid : ChoiceInputsValid s u t w)
    (hcollection : ¬ assignmentIsLive s u t)
    (hnotdata : slotDraw timeInput.1 ≠ dataSlot)
    (hdown : slotDraw timeInput.1 = downSlot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈
      pendingAtChoice) :
    coordinatorArmChoiceCore s pendingAtChoice u t w timeInput =
      some (sendArm
        (currentDownHash s timeInput
          (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (coordinator p.two_le_m))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (followerPlayer p.two_le_m
            (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1)))) := by
  apply coordinatorArmChoiceCore_down s pendingAtChoice u t w timeInput hvalid
  · exact fun h => hcollection h.1
  · exact hnotdata
  · exact hdown
  · exact hselected

/-- The task-facing choice is definitionally the core operation on the
declared row's current `TimeControl`. -/
theorem coordinatorArmChoice_eq_core
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) (row : CompleteRow p) :
    coordinatorArmChoice s pendingAtChoice u t w row =
      coordinatorArmChoiceCore s pendingAtChoice u t w (row.2 t) := rfl

/-- Complete-row choice factors through the current local control: rows with
the same declared `row.2 t` give exactly the same arm. -/
theorem coordinatorArmChoice_eq_of_same_current_timeControl
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ)
    (row₁ row₂ : CompleteRow p) (hcurrent : row₁.2 t = row₂.2 t) :
    coordinatorArmChoice s pendingAtChoice u t w row₁ =
      coordinatorArmChoice s pendingAtChoice u t w row₂ := by
  rw [coordinatorArmChoice_eq_core, coordinatorArmChoice_eq_core, hcurrent]

/-- Complete-row confirmation also factors through the same current local
control, with the coordinator's own typed grid observation held fixed. -/
theorem confirmationUpdate_eq_of_same_current_timeControl
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (row₁ row₂ : CompleteRow p)
    (observation : Fin (D p + 1)) (hcurrent : row₁.2 t = row₂.2 t) :
    confirmationUpdate s pendingAtChoice u t row₁ observation =
      confirmationUpdate s pendingAtChoice u t row₂ observation := by
  unfold confirmationUpdate
  rw [hcurrent]

/-- The control slice is the actual continuous coordinate used by the
original product measurable space, with no replacement domain. -/
theorem measurable_localFastDraw
    (s : AssignmentStartPayload.Input p eta) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ)
    (hvalid : ChoiceInputsValid s u t w) :
    Measurable (fun x : TimeControl p => localFastDraw s u t w hvalid x) := by
  exact (measurable_sampleLocalFast p eta.val hvalid.learning_rate_pos
    hvalid.learning_rate_le_source_cap s.anchor hvalid.anchor_pos s.slowSet w
    hvalid.current_weight_pos hvalid.anchor_le_current hvalid.current_le_twice_anchor).comp
      (ContinuousControlSlice.measurable_coordinate ContinuousControlSlice.Label.fast |>.comp
        measurable_fst)

/-- The ordinary coordinate maps remain measurable on the original product
`TimeControl = Slice × AffineSamples`. -/
private theorem measurable_currentDownSample (i : Follower p.m) :
    Measurable (fun x : TimeControl p => x.2 (downChannel i)) :=
  (measurable_pi_apply (downChannel i)).comp measurable_snd

private theorem measurable_currentDownHash (s : AssignmentStartPayload.Input p eta)
    (i : Follower p.m) :
    Measurable (fun x : TimeControl p => currentDownHash s x i) := by
  have hbit : Measurable
      (fun z : Sample (B p) => affineHash z (storedDownFlatWord s i)) := measurable_from_top
  exact hbit.comp (measurable_currentDownSample i)

private theorem measurable_selectedDownHash (s : AssignmentStartPayload.Input p eta) :
    Measurable (fun x : TimeControl p => currentDownHash s x
      (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)) := by
  classical
  apply measurable_to_countable'
  intro b
  have hdecomp :
      {x : TimeControl p | currentDownHash s x
        (selectedFollowerDraw p.two_le_m p.m_lt_K x.1) = b} =
      ⋃ i : Follower p.m, {x : TimeControl p |
        selectedFollowerDraw p.two_le_m p.m_lt_K x.1 = i ∧ currentDownHash s x i = b} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hb
      exact ⟨selectedFollowerDraw p.two_le_m p.m_lt_K x.1, rfl, hb⟩
    · rintro ⟨i, hi, hb⟩
      rw [hi]
      exact hb
  change MeasurableSet {x : TimeControl p | currentDownHash s x
    (selectedFollowerDraw p.two_le_m p.m_lt_K x.1) = b}
  rw [hdecomp]
  exact MeasurableSet.iUnion fun i =>
    ((((measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp measurable_fst)
      (measurableSet_singleton i)).inter
      ((measurable_currentDownHash s i) (measurableSet_singleton b)))

/-- A selected follower's current tuple arm is measurable; the index is the
actual `sel` draw, so no follower value is supplied externally. -/
private theorem measurable_selectedTupleArm :
    Measurable (fun x : TimeControl p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
        (followerPlayer p.two_le_m (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))) := by
  classical
  apply measurable_to_countable'
  intro a
  have hdecomp :
      {x : TimeControl p |
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
          (followerPlayer p.two_le_m (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)) = a} =
      ⋃ i : Follower p.m, {x : TimeControl p |
        selectedFollowerDraw p.two_le_m p.m_lt_K x.1 = i ∧
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
          (followerPlayer p.two_le_m i) = a} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro ha
      exact ⟨selectedFollowerDraw p.two_le_m p.m_lt_K x.1, rfl, ha⟩
    · rintro ⟨i, hi, ha⟩
      rw [hi]
      exact ha
  change MeasurableSet {x : TimeControl p |
    (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
      (followerPlayer p.two_le_m (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)) = a}
  rw [hdecomp]
  have hselectedLocal : Measurable (fun x : TimeControl p =>
      selectedFollowerDraw p.two_le_m p.m_lt_K x.1) :=
    (measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp measurable_fst
  have hfixedTupleArm (i : Follower p.m) :
      Measurable (fun x : TimeControl p =>
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
          (followerPlayer p.two_le_m i)) :=
    ((measurable_pi_apply (followerPlayer p.two_le_m i)).comp
      (measurable_subtype_coe.comp
        (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))).comp measurable_fst
  exact MeasurableSet.iUnion fun i =>
    (hselectedLocal (measurableSet_singleton i)).inter
      (hfixedTupleArm i (measurableSet_singleton a))

/-- The tuple coordinator arm is measurable on the same slice product. -/
private theorem measurable_coordinatorTupleArm :
    Measurable (fun x : TimeControl p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
        (coordinator p.two_le_m)) := by
  exact ((measurable_pi_apply (coordinator p.two_le_m)).comp
    (measurable_subtype_coe.comp
      (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K))).comp measurable_fst

/-- The complete arm-choice operation is measurable in its current local
`TimeControl`, with all incoming local data fixed. The product control and
affine-sample measurable spaces are the existing ones. -/
theorem measurable_coordinatorArmChoiceCore
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) :
    Measurable (coordinatorArmChoiceCore s pendingAtChoice u t w) := by
  classical
  by_cases hvalid : ChoiceInputsValid s u t w
  · by_cases hfast : assignmentIsLive s u t ∧ pendingAtChoice = ∅
    · rcases hfast with ⟨hlive, hempty⟩
      have heq : coordinatorArmChoiceCore s pendingAtChoice u t w =
          fun x : TimeControl p => some (localFastDraw s u t w hvalid x).1 := by
        funext x
        exact coordinatorArmChoiceCore_live_empty s pendingAtChoice u t w x
          hvalid hlive hempty
      rw [heq]
      exact (measurable_some_arm.comp (measurable_subtype_coe.comp
        (measurable_localFastDraw s u t w hvalid)))
    · have hslot : Measurable (fun x : TimeControl p => slotDraw x.1) :=
        measurable_slotDraw.comp measurable_fst
      have hselected : Measurable
          (fun x : TimeControl p => selectedFollowerDraw p.two_le_m p.m_lt_K x.1) :=
        (measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp measurable_fst
      have hpilot : Measurable (fun x : TimeControl p =>
          pilotDraw (K_pos p) (coordinator p.two_le_m) x.1) :=
        measurable_pilotDraw (K_pos p) (coordinator p.two_le_m) |>.comp measurable_fst
      have hdataSet : MeasurableSet {x : TimeControl p | slotDraw x.1 = dataSlot} :=
        hslot (measurableSet_singleton dataSlot)
      have hdownSet : MeasurableSet {x : TimeControl p |
          slotDraw x.1 = downSlot ∧
            selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice} := by
        exact (hslot (measurableSet_singleton downSlot)).inter
          (hselected pendingAtChoice.measurableSet)
      have hsend : Measurable (fun x : TimeControl p =>
          sendArm
            (currentDownHash s x
              (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (coordinator p.two_le_m))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (followerPlayer p.two_le_m
                (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)))) := by
        have hpairs : Measurable (fun x : TimeControl p =>
            (currentDownHash s x
                (selectedFollowerDraw p.two_le_m p.m_lt_K x.1),
              (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                (coordinator p.two_le_m),
              (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                (followerPlayer p.two_le_m
                  (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)))) := by
          exact (measurable_selectedDownHash s).prodMk
            ((measurable_coordinatorTupleArm).prodMk measurable_selectedTupleArm)
        have hsendInput : Measurable
            (fun z : Bit × Arm p.K × Arm p.K => sendArm z.1 z.2.1 z.2.2) :=
          measurable_of_finite _
        exact hsendInput.comp hpairs
      have hdownOption : Measurable (fun x : TimeControl p =>
          some (sendArm
            (currentDownHash s x
              (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (coordinator p.two_le_m))
            ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (followerPlayer p.two_le_m
                (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))))) :=
        measurable_some_arm.comp hsend
      have hpilotOption : Measurable (fun x : TimeControl p => some
          (pilotDraw (K_pos p) (coordinator p.two_le_m) x.1)) :=
        measurable_some_arm.comp hpilot
      have htupleOption : Measurable (fun x : TimeControl p => some
          ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
            (coordinator p.two_le_m))) :=
        measurable_some_arm.comp measurable_coordinatorTupleArm
      have hrest : Measurable (fun x : TimeControl p =>
          if slotDraw x.1 = downSlot ∧
              selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice then
            some (sendArm
              (currentDownHash s x
                (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                (coordinator p.two_le_m))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                (followerPlayer p.two_le_m
                  (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))))
          else some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
            (coordinator p.two_le_m))) := by
        exact Measurable.ite hdownSet hdownOption htupleOption
      have hbody : Measurable (fun x : TimeControl p =>
          if slotDraw x.1 = dataSlot then
            some (pilotDraw (K_pos p) (coordinator p.two_le_m) x.1)
          else if slotDraw x.1 = downSlot ∧
              selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice then
            some (sendArm
              (currentDownHash s x
                (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                (coordinator p.two_le_m))
              ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                (followerPlayer p.two_le_m
                  (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))))
          else some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
            (coordinator p.two_le_m))) :=
        Measurable.ite hdataSet hpilotOption hrest
      have heq : coordinatorArmChoiceCore s pendingAtChoice u t w =
          fun x : TimeControl p =>
            if slotDraw x.1 = dataSlot then
              some (pilotDraw (K_pos p) (coordinator p.two_le_m) x.1)
            else if slotDraw x.1 = downSlot ∧
                selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice then
              some (sendArm
                (currentDownHash s x
                  (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                  (coordinator p.two_le_m))
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                  (followerPlayer p.two_le_m
                    (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))))
            else some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (coordinator p.two_le_m)) := by
        funext x
        by_cases hxdata : slotDraw x.1 = dataSlot
        · rw [coordinatorArmChoiceCore_data s pendingAtChoice u t w x
            hvalid hfast hxdata]
          simp [hxdata]
        · by_cases hxdown : slotDraw x.1 = downSlot ∧
              selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice
          · rw [coordinatorArmChoiceCore_down s pendingAtChoice u t w x
              hvalid hfast hxdata hxdown.1 hxdown.2]
            have hxdownNeData : downSlot ≠ dataSlot := fun heq =>
              hxdata (hxdown.1.trans heq)
            simp [hxdown, hxdownNeData]
          · rw [coordinatorArmChoiceCore_other s pendingAtChoice u t w x
              hvalid hfast hxdata hxdown]
            simp [hxdata, hxdown]
      rw [heq]
      exact hbody
  · have heq : coordinatorArmChoiceCore s pendingAtChoice u t w =
        fun _ : TimeControl p => none := by
      funext x
      exact coordinatorArmChoiceCore_none_of_invalid s pendingAtChoice u t w x hvalid
    rw [heq]
    exact measurable_const

/-- The complete-row arm choice is measurable by composition with the
declared current learning/control coordinate. -/
theorem measurable_coordinatorArmChoice
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (w : FastArm s.slowSet → ℝ) :
    Measurable (coordinatorArmChoice s pendingAtChoice u t w) := by
  exact (measurable_coordinatorArmChoiceCore s pendingAtChoice u t w).comp
    (measurable_pi_apply t |>.comp measurable_snd)

/-- The locally restricted fast draw is pointwise the accepted canonical fast
draw whenever the comparison theorem is given one global positive envelope
vector. The operation itself has no global current-weight input. -/
theorem localFastDraw_eq_canonical
    (s : AssignmentStartPayload.Input p eta) (u : Option (Cutoff p))
    (t : Fin p.T) (localWeights : FastArm s.slowSet → ℝ)
    (hvalid : ChoiceInputsValid s u t localWeights)
    (globalWeights : Fin p.K → ℝ)
    (hglobalPos : ∀ a, 0 < globalWeights a)
    (hglobalLower : ∀ a, s.anchor a ≤ globalWeights a)
    (hglobalUpper : ∀ a, globalWeights a ≤ 2 * s.anchor a)
    (hrestrict : localWeights = fun j => globalWeights j.1)
    (timeInput : TimeControl p) :
    localFastDraw s u t localWeights hvalid timeInput =
      CanonicalFastSampling.sampleFast p eta.val hvalid.learning_rate_pos
        hvalid.learning_rate_le_source_cap s.anchor globalWeights hvalid.anchor_pos
        hglobalPos hglobalLower hglobalUpper s.slowSet
        (coordinate ContinuousControlSlice.Label.fast timeInput.1) := by
  subst localWeights
  exact FastComplementLocality.sampleLocalFast_eq_sampleFast p eta.property
    s.eta_le_source_cap s.anchor globalWeights s.anchor_pos hglobalPos hglobalLower
    hglobalUpper s.slowSet
    (coordinate ContinuousControlSlice.Label.fast timeInput.1)

/-- Conditional comparison with the existing coordinator action on a live
compatible snapshot. Compatibility is stated as explicit equalities for the
actual local slot, selected index, tuple, coordinator pilot, and selected DOWN
word/channel. No snapshot, global fast vector, receiver state, or physical
history enters arm choice itself. -/
theorem coordinatorArmChoiceCore_eq_coordinatorAction
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (localWeights : FastArm s.slowSet → ℝ)
    (timeInput : TimeControl p) (hvalid : ChoiceInputsValid s u t localWeights)
    (snapshot : Snapshot s.assignment) (r : RoundInput s.assignment (B p))
    (hlive : assignmentIsLive s u t) (hsnapshot : snapshot.missing = pendingAtChoice)
    (globalWeights : Fin p.K → ℝ)
    (hglobalPos : ∀ a, 0 < globalWeights a)
    (hglobalLower : ∀ a, s.anchor a ≤ globalWeights a)
    (hglobalUpper : ∀ a, globalWeights a ≤ 2 * s.anchor a)
    (hrestrict : localWeights = fun j => globalWeights j.1)
    (hfast : pendingAtChoice = ∅ → r.fast =
      (CanonicalFastSampling.sampleFast p eta.val hvalid.learning_rate_pos
        hvalid.learning_rate_le_source_cap s.anchor globalWeights hvalid.anchor_pos
        hglobalPos hglobalLower hglobalUpper s.slowSet
        (coordinate ContinuousControlSlice.Label.fast timeInput.1)).1)
    (hslot : slotDraw timeInput.1 = r.slot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = r.selected)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1 = r.tuple)
    (hpilot : pilotDraw (K_pos p) (coordinator p.two_le_m) timeInput.1 =
      r.pilots (coordinator p.two_le_m))
    (hdown : r.selected ∈ pendingAtChoice → r.down =
      ⟨timeInput.2 (downChannel r.selected),
        storedDownFlatWord s r.selected⟩) :
    coordinatorArmChoiceCore s pendingAtChoice u t localWeights timeInput =
      some (ActiveRoundActions.coordinatorAction p.two_le_m snapshot r) := by
  classical
  by_cases hempty : pendingAtChoice = ∅
  · have hdraw := localFastDraw_eq_canonical s u t localWeights hvalid
      globalWeights hglobalPos hglobalLower hglobalUpper hrestrict timeInput
    have hfast' :
        (localFastDraw s u t localWeights hvalid timeInput).1 = r.fast := by
      rw [hdraw]
      exact (hfast hempty).symm
    have hSnapshotEmpty : snapshot.missing = ∅ := by rw [hsnapshot, hempty]
    rw [coordinatorArmChoiceCore_live_empty s pendingAtChoice u t localWeights
      timeInput hvalid hlive hempty, ActiveRoundActions.coordinatorAction_fast
      p.two_le_m snapshot r hSnapshotEmpty, hfast']
  · have hnotfast : ¬ (assignmentIsLive s u t ∧ pendingAtChoice = ∅) :=
      fun h => hempty h.2
    have hnotempty : pendingAtChoice ≠ ∅ := hempty
    by_cases hdata : slotDraw timeInput.1 = dataSlot
    · rw [coordinatorArmChoiceCore_data s pendingAtChoice u t localWeights timeInput
        hvalid hnotfast hdata]
      have hrdata : r.slot = dataSlot := hslot.symm.trans hdata
      have hsnapshotNonempty : snapshot.missing ≠ ∅ := by
        rw [hsnapshot]
        exact hnotempty
      rw [ActiveRoundActions.coordinatorAction_data
        p.two_le_m snapshot r hsnapshotNonempty hrdata, hpilot]
    · by_cases hdownBranch : slotDraw timeInput.1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈ pendingAtChoice
      · have hchoice := coordinatorArmChoiceCore_down s pendingAtChoice u t
          localWeights timeInput hvalid hnotfast hdata hdownBranch.1 hdownBranch.2
        have hrslot : r.slot = downSlot := hslot.symm.trans hdownBranch.1
        have hrselected : r.selected ∈ pendingAtChoice := hselected ▸ hdownBranch.2
        have hrsnapshot : r.selected ∈ snapshot.missing := by
          rw [hsnapshot]
          exact hrselected
        rw [hchoice, hselected, htuple]
        rw [ActiveRoundActions.coordinatorAction_down p.two_le_m snapshot r
          hrslot hrsnapshot]
        have hhash : currentDownHash s timeInput r.selected = r.down.bit := by
          rw [hdown hrselected]
          rfl
        rw [hhash]
      · have hchoice := coordinatorArmChoiceCore_other s pendingAtChoice u t
          localWeights timeInput hvalid hnotfast hdata hdownBranch
        rw [hchoice]
        have hrnotdata : r.slot ≠ dataSlot := fun h => hdata (hslot.trans h)
        have hrnotdown : ¬ (r.slot = downSlot ∧ r.selected ∈ pendingAtChoice) := by
          intro h
          apply hdownBranch
          exact ⟨hslot.trans h.1, hselected.symm ▸ h.2⟩
        have hsnapshotNonempty : snapshot.missing ≠ ∅ := by
          rw [hsnapshot]
          exact hnotempty
        rw [htuple]
        simp [ActiveRoundActions.coordinatorAction, hsnapshot,
          hnotempty, hrnotdata, hrnotdown]

/-- The row-facing operation has the same conditional comparison on its own
declared current time, under the same explicit local compatibility data. -/
theorem coordinatorArmChoice_eq_coordinatorAction
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (localWeights : FastArm s.slowSet → ℝ)
    (row : CompleteRow p) (hvalid : ChoiceInputsValid s u t localWeights)
    (snapshot : Snapshot s.assignment) (r : RoundInput s.assignment (B p))
    (hlive : assignmentIsLive s u t) (hsnapshot : snapshot.missing = pendingAtChoice)
    (globalWeights : Fin p.K → ℝ)
    (hglobalPos : ∀ a, 0 < globalWeights a)
    (hglobalLower : ∀ a, s.anchor a ≤ globalWeights a)
    (hglobalUpper : ∀ a, globalWeights a ≤ 2 * s.anchor a)
    (hrestrict : localWeights = fun j => globalWeights j.1)
    (hfast : pendingAtChoice = ∅ → r.fast =
      (CanonicalFastSampling.sampleFast p eta.val hvalid.learning_rate_pos
        hvalid.learning_rate_le_source_cap s.anchor globalWeights hvalid.anchor_pos
        hglobalPos hglobalLower hglobalUpper s.slowSet
        (coordinate ContinuousControlSlice.Label.fast (row.2 t).1)).1)
    (hslot : slotDraw (row.2 t).1 = r.slot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = r.selected)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1 = r.tuple)
    (hpilot : pilotDraw (K_pos p) (coordinator p.two_le_m) (row.2 t).1 =
      r.pilots (coordinator p.two_le_m))
    (hdown : r.selected ∈ pendingAtChoice → r.down =
      ⟨(row.2 t).2 (downChannel r.selected), storedDownFlatWord s r.selected⟩) :
    coordinatorArmChoice s pendingAtChoice u t localWeights row =
      some (ActiveRoundActions.coordinatorAction p.two_le_m snapshot r) := by
  exact coordinatorArmChoiceCore_eq_coordinatorAction s pendingAtChoice u t
    localWeights (row.2 t) hvalid snapshot r hlive hsnapshot globalWeights
    hglobalPos hglobalLower hglobalUpper hrestrict hfast hslot hselected htuple hpilot hdown

/-- The exact condition that removes the selected follower from the pending
set at choice. It includes the live cutoff, nonempty set, DOWN slot, membership,
actual current encoded-word hash zero, and positive own observation. -/
theorem downConfirmationEvent_iff
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (timeInput : TimeControl p) (observation : Fin (D p + 1)) :
    downConfirmationEvent s pendingAtChoice u t timeInput observation ↔
      assignmentIsLive s u t ∧ pendingAtChoice.Nonempty ∧
        slotDraw timeInput.1 = downSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 ∈ pendingAtChoice ∧
        currentDownHash s timeInput
          (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1) = 0 ∧
        0 < ownGridObservationValue observation := Iff.rfl

/-- Valid collection rounds never apply the live DOWN confirmation removal;
old DOWN records may still be transmitted by the choice operation. -/
theorem confirmationUpdateCore_collection
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (timeInput : TimeControl p) (observation : Fin (D p + 1))
    (hvalid : ConfirmationInputsValid s u t)
    (hcollection : ¬ assignmentIsLive s u t) :
    confirmationUpdateCore s pendingAtChoice u t timeInput observation =
      some pendingAtChoice := by
  simp [confirmationUpdateCore, hvalid, downConfirmationEvent, confirmationLive,
    hcollection]

/-- A positive, selected, zero-hash live DOWN confirmation removes exactly
that selected index. -/
theorem confirmationUpdateCore_removes
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (timeInput : TimeControl p) (observation : Fin (D p + 1))
    (hvalid : ConfirmationInputsValid s u t)
    (hevent : downConfirmationEvent s pendingAtChoice u t timeInput observation) :
    confirmationUpdateCore s pendingAtChoice u t timeInput observation =
      some (pendingAtChoice.erase
        (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1)) := by
  simp [confirmationUpdateCore, hvalid, hevent]

/-- If any exact local confirmation conjunct fails, the coordinator stores the
same pending set. -/
theorem confirmationUpdateCore_preserves
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (timeInput : TimeControl p) (observation : Fin (D p + 1))
    (hvalid : ConfirmationInputsValid s u t)
    (hnoevent : ¬ downConfirmationEvent s pendingAtChoice u t timeInput observation) :
    confirmationUpdateCore s pendingAtChoice u t timeInput observation =
      some pendingAtChoice := by
  simp [confirmationUpdateCore, hvalid, hnoevent]

/-- Under a successful confirmation, membership changes only by deleting the
selected index. -/
theorem confirmationUpdateCore_mem_after_removal
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (timeInput : TimeControl p) (observation : Fin (D p + 1))
    (hvalid : ConfirmationInputsValid s u t)
    (hevent : downConfirmationEvent s pendingAtChoice u t timeInput observation)
    (j : Follower p.m) :
    j ∈ (Option.getD (confirmationUpdateCore s pendingAtChoice u t timeInput observation)
      pendingAtChoice) ↔ j ∈ pendingAtChoice ∧
        j ≠ selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 := by
  rw [confirmationUpdateCore_removes s pendingAtChoice u t timeInput observation
    hvalid hevent]
  simp only [Option.getD_some, Finset.mem_erase, and_comm]

/-- With no confirmation event, every pending membership bit is unchanged. -/
theorem confirmationUpdateCore_mem_after_preservation
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (timeInput : TimeControl p) (observation : Fin (D p + 1))
    (hvalid : ConfirmationInputsValid s u t)
    (hnoevent : ¬ downConfirmationEvent s pendingAtChoice u t timeInput observation)
    (j : Follower p.m) :
    j ∈ (Option.getD (confirmationUpdateCore s pendingAtChoice u t timeInput observation)
      pendingAtChoice) ↔ j ∈ pendingAtChoice := by
  rw [confirmationUpdateCore_preserves s pendingAtChoice u t timeInput observation
    hvalid hnoevent]
  rfl

/-- The confirmation update reads only the slot, selected follower, and that
selected follower's current DOWN affine sample. -/
theorem confirmationUpdateCore_eq_of_same_local_reads
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (time₁ time₂ : TimeControl p)
    (observation : Fin (D p + 1))
    (hslot : slotDraw time₁.1 = slotDraw time₂.1)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1 =
      selectedFollowerDraw p.two_le_m p.m_lt_K time₂.1)
    (hsample : time₁.2 (downChannel
        (selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1)) =
      time₂.2 (downChannel
        (selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1))) :
    confirmationUpdateCore s pendingAtChoice u t time₁ observation =
      confirmationUpdateCore s pendingAtChoice u t time₂ observation := by
  classical
  have hsample₂ : time₁.2 (downChannel
      (selectedFollowerDraw p.two_le_m p.m_lt_K time₂.1)) =
    time₂.2 (downChannel (selectedFollowerDraw p.two_le_m p.m_lt_K time₂.1)) := by
    simpa only [hselected] using hsample
  have hevent : downConfirmationEvent s pendingAtChoice u t time₁ observation =
      downConfirmationEvent s pendingAtChoice u t time₂ observation := by
    apply propext
    simp [downConfirmationEvent, currentDownHash, hslot, hselected, hsample₂]
  simp [confirmationUpdateCore, hevent, hselected]

/-- The confirmation map is measurable on the original current-control
product, for fixed local incoming data and the coordinator's typed observation.
-/
theorem measurable_confirmationUpdateCore
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (observation : Fin (D p + 1)) :
    Measurable (confirmationUpdateCore s pendingAtChoice u t · observation) := by
  classical
  by_cases hvalid : ConfirmationInputsValid s u t
  · by_cases hlive : confirmationLive s u t
    · by_cases hnonempty : pendingAtChoice.Nonempty
      · by_cases hobs : 0 < ownGridObservationValue observation
        · have hslot : Measurable (fun x : TimeControl p => slotDraw x.1) :=
            measurable_slotDraw.comp measurable_fst
          have hselected : Measurable
              (fun x : TimeControl p => selectedFollowerDraw p.two_le_m p.m_lt_K x.1) :=
            (measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp measurable_fst
          have hhash := measurable_selectedDownHash (s := s)
          have htrigger : MeasurableSet {x : TimeControl p |
              slotDraw x.1 = downSlot ∧
                selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice ∧
                currentDownHash s x
                  (selectedFollowerDraw p.two_le_m p.m_lt_K x.1) = 0} := by
            have hslotSet := hslot (measurableSet_singleton downSlot)
            have hselectedSet := hselected pendingAtChoice.measurableSet
            have hhashSet := hhash (measurableSet_singleton 0)
            exact MeasurableSet.inter hslotSet <| MeasurableSet.inter hselectedSet hhashSet
          have heraseInput : Measurable (fun i : Follower p.m =>
              pendingAtChoice.erase i) := measurable_of_finite _
          have herase := heraseInput.comp hselected
          have hshape : ∀ x : TimeControl p,
              downConfirmationEvent s pendingAtChoice u t x observation ↔
                (slotDraw x.1 = downSlot ∧
                  selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice ∧
                  currentDownHash s x
                    (selectedFollowerDraw p.two_le_m p.m_lt_K x.1) = 0) := by
            intro x
            simp only [downConfirmationEvent]
            constructor
            · rintro ⟨_, _, hslot, hmember, hhash, _⟩
              exact ⟨hslot, hmember, hhash⟩
            · rintro ⟨hslot, hmember, hhash⟩
              exact ⟨hlive, hnonempty, hslot, hmember, hhash, hobs⟩
          have hinside : Measurable (fun x : TimeControl p =>
              if downConfirmationEvent s pendingAtChoice u t x observation then
                pendingAtChoice.erase (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)
              else pendingAtChoice) := by
            have hite : Measurable (fun x : TimeControl p =>
                if slotDraw x.1 = downSlot ∧
                    selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice ∧
                    currentDownHash s x
                      (selectedFollowerDraw p.two_le_m p.m_lt_K x.1) = 0 then
                  pendingAtChoice.erase (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)
                else pendingAtChoice) :=
              Measurable.ite htrigger herase measurable_const
            have heq : (fun x : TimeControl p =>
                if downConfirmationEvent s pendingAtChoice u t x observation then
                  pendingAtChoice.erase (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)
                else pendingAtChoice) =
              (fun x => if slotDraw x.1 = downSlot ∧
                  selectedFollowerDraw p.two_le_m p.m_lt_K x.1 ∈ pendingAtChoice ∧
                  currentDownHash s x
                    (selectedFollowerDraw p.two_le_m p.m_lt_K x.1) = 0 then
                pendingAtChoice.erase (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)
              else pendingAtChoice) := by
              funext x
              simp only [hshape x]
            rw [heq]
            exact hite
          have hcore : (fun x : TimeControl p =>
              confirmationUpdateCore s pendingAtChoice u t x observation) =
              fun x : TimeControl p => some
                (if downConfirmationEvent s pendingAtChoice u t x observation then
                  pendingAtChoice.erase
                    (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)
                else pendingAtChoice) := by
            funext x
            simp [confirmationUpdateCore, hvalid]
          rw [hcore]
          exact measurable_some_pending.comp hinside
        · simp [confirmationUpdateCore, hvalid, downConfirmationEvent,
            confirmationLive, hnonempty, hobs]
      · simp [confirmationUpdateCore, hvalid, downConfirmationEvent,
          confirmationLive, hnonempty]
    · simp [confirmationUpdateCore, hvalid, downConfirmationEvent, hlive]
  · simp [confirmationUpdateCore, hvalid]

/-- The complete-row confirmation operation is measurable by reading only
`row.2 t` and the separately typed local observation. -/
theorem measurable_confirmationUpdate
    (s : AssignmentStartPayload.Input p eta)
    (pendingAtChoice : Finset (Follower p.m)) (u : Option (Cutoff p))
    (t : Fin p.T) (observation : Fin (D p + 1)) :
    Measurable (confirmationUpdate s pendingAtChoice u t · observation) := by
  exact (measurable_confirmationUpdateCore s pendingAtChoice u t observation).comp
    (measurable_pi_apply t |>.comp measurable_snd)

end Bandits.Support.CoordinatorLocalArmChoice

end
