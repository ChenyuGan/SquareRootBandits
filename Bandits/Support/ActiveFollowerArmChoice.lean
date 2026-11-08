/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveRoundActions
public import Bandits.Support.PrelaunchBufferRecovery
public import Bandits.Support.ReferencePrelaunchFollower

import Lean.Elab.Tactic.Omega

/-!
# Literal local follower arm choice

This module implements one follower's arm choice from that follower's carried
`ReferencePrelaunchFollower.State`, its current complete row and time, and the
optional UP payload supplied by the UP-offer owner. The branch order is the
follower part of `sources/zip4/manuscript/05_binary_transport.tex:105-122`.
The state fields and local offer checks use
`sources/zip4/manuscript/06_interruptions.tex:123-177` and the local domain
rules of `sources/zip4/manuscript/appendix_a_local_protocol.tex:7-16`.

Occupied arms come from this follower's own accepted DOWN record. This file
does not build a common assignment, activation, message decoder, service
operation, or physical run. The optional UP record is a supplied local
interface input; checking its fields does not authenticate its origin.
The result is `none` on a required local check failure and otherwise contains
only an arm, so arm choice performs no register mutation.
-/

public section

namespace Bandits.Support.ActiveFollowerArmChoice

open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ConstructorDimensions
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower

/-- Convert the admissible DOWN escape label to the existing zero-based arm
carrier. -/
@[expose] def downAuxiliaryArm {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) : Fin p.K := by
  have h := M.property
  simp only [downAdmissible] at h
  have he : 1 ≤ M.val.e := h.2.2.2.2.1
  have heK : M.val.e ≤ p.K := h.2.2.2.2.2.1
  exact ⟨M.val.e - 1, by omega⟩

/-- The converted auxiliary arm has exactly the DOWN record's one-based label. -/
theorem down_auxiliary_arm_one_based {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) :
    (downAuxiliaryArm eta M).val + 1 = M.val.e := by
  have h := M.property
  simp only [downAdmissible] at h
  have hval : (downAuxiliaryArm eta M).val = M.val.e - 1 := by
    simp [downAuxiliaryArm]
  rw [hval]
  omega

/-- The decoded arm and escape arm are distinct by DOWN admissibility. -/
theorem down_arm_ne_auxiliary_arm {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) :
    downArm eta M ≠ downAuxiliaryArm eta M := by
  intro heq
  have hlabels := congrArg (fun a : Fin p.K => a.val + 1) heq
  rw [down_arm_one_based, down_auxiliary_arm_one_based] at hlabels
  have h := M.property
  simp only [downAdmissible] at h
  rcases h with ⟨_, _, _, _, _, _, hae, _, _, _, _⟩
  exact hae hlabels

/-- The escape conversion remains in the source arm domain. -/
theorem down_auxiliary_arm_source_bounds {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) :
    1 ≤ (downAuxiliaryArm eta M).val + 1 ∧
      (downAuxiliaryArm eta M).val + 1 ≤ p.K := by
  rw [down_auxiliary_arm_one_based]
  have h := M.property
  simp only [downAdmissible] at h
  rcases h with ⟨_, _, _, _, helo, hehi, _, _, _, _, _⟩
  exact ⟨helo, hehi⟩

/-- The decoded DOWN arm is in the source's one-based arm domain. -/
theorem down_arm_source_bounds {p : Parameters} (eta : LearningRate)
    (M : DownRecord (codecParams p eta)) :
    1 ≤ (downArm eta M).val + 1 ∧ (downArm eta M).val + 1 ≤ p.K := by
  rw [down_arm_one_based]
  have h := M.property
  simp only [downAdmissible] at h
  rcases h with ⟨_, _, ha, haK, _, _, _, _, _, _, _⟩
  exact ⟨ha, haK⟩

/-- The flattened codec word for a supplied, locally offered UP payload. -/
@[expose] def offeredUpWord {p : Parameters} (eta : LearningRate)
    (M : UpRecord (codecParams p eta)) : Word (ContinuousLearningRows.B p) :=
  wordEquivFlat (codecParams p eta) (encodeUp (codecParams p eta) M)

/-- The actual affine bit of this follower's encoded local UP offer, using the
current row's `(UP, follower)` sample. -/
@[expose] def offeredUpBit {p : Parameters} (eta : LearningRate)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta)) : Bit :=
  affineHash (timeInput.2 (1, i)) (offeredUpWord eta M)

/-- The carried integer service fields lie in the domains needed to encode an
UP record. These checks are made only on a selected unoccupied UP branch. -/
@[expose] def upStateDomain {p : Parameters} {eta : LearningRate}
    (s : State p eta) : Prop :=
  s.S ≤ p.T * D p ∧ s.delta ≤ D p ∧ s.backlog ≤ p.T * D p

/-- All four fields of the offered UP record agree with this follower's
carried local registers. -/
@[expose] def offeredUpMatchesState {p : Parameters} {eta : LearningRate}
    (s : State p eta) (M : UpRecord (codecParams p eta)) : Prop :=
  M.val.sigma = acceptedStart s ∧ M.val.S = s.S ∧
    M.val.delta = s.delta ∧ M.val.q = s.backlog

/-- Read only the current local time input and return this follower's checked
arm. A failed required local check is `none`; successful arms are already in
the finite carrier. -/
@[expose] noncomputable def followerArmChoiceCore {p : Parameters} {eta : LearningRate}
    (s : State p eta) (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta))) : Option (Fin p.K) := by
  classical
  let slot := slotDraw timeInput.1
  let selected := selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1
  let tuple := OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1
  exact if s.status = .unoccupied then
    if slot = dataSlot then
      some (pilotDraw (K_pos p) (followerPlayer p.two_le_m i) timeInput.1)
    else if slot = upSlot ∧ selected = i then
      match offeredUp with
      | none => none
      | some M =>
        if upStateDomain s ∧ offeredUpMatchesState s M then
          some (sendArm (offeredUpBit eta timeInput i M)
            (tuple.val (followerPlayer p.two_le_m i))
            (tuple.val (coordinator p.two_le_m)))
        else none
    else some (tuple.val (followerPlayer p.two_le_m i))
  else
    match s.lastDown with
    | none => none
    | some M =>
      if s.status = .released ∨ slot = dataSlot then
        some (downArm eta M)
      else if slot = upSlot ∧ selected = i ∧
          tuple.val (coordinator p.two_le_m) = downAuxiliaryArm eta M then
        some (downAuxiliaryArm eta M)
      else if (slot = downSlot ∧
          downArm eta M = tuple.val (followerPlayer p.two_le_m selected)) ∨
          (slot = upSlot ∧
          downArm eta M = tuple.val (coordinator p.two_le_m)) then
        some (downAuxiliaryArm eta M)
      else some (downArm eta M)

/-- The task-facing operation uses exactly this follower's declared row and
current time. The complete row's forward component and every other row are
outside its interface. -/
@[expose] noncomputable def followerArmChoice {p : Parameters} {eta : LearningRate}
    (s : State p eta) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta))) : Option (Fin p.K) :=
  followerArmChoiceCore s (row.2 t) i offeredUp

private theorem upSlot_ne_dataSlot : upSlot ≠ dataSlot := by decide

private theorem upSlot_ne_downSlot : upSlot ≠ downSlot := by decide

/-- An unoccupied follower uses its current-row pilot on DATA, regardless of
the optional UP offer. -/
theorem followerArmChoiceCore_unoccupied_data {p : Parameters} {eta : LearningRate}
    (s : State p eta) (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hstatus : s.status = .unoccupied)
    (hslot : slotDraw timeInput.1 = dataSlot) :
    followerArmChoiceCore s timeInput i offeredUp =
      some (pilotDraw (K_pos p) (followerPlayer p.two_le_m i) timeInput.1) := by
  simp [followerArmChoiceCore, hstatus, hslot]

/-- An unoccupied selected-UP follower encodes the supplied local offer and
uses its current `(UP, i)` affine sample, after checking all carried fields. -/
theorem followerArmChoiceCore_unoccupied_selected_up
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta))
    (hstatus : s.status = .unoccupied)
    (hslot : slotDraw timeInput.1 = upSlot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i)
    (hvalid : upStateDomain s ∧ offeredUpMatchesState s M) :
    followerArmChoiceCore s timeInput i (some M) =
      some (sendArm (offeredUpBit eta timeInput i M)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (followerPlayer p.two_le_m i))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (coordinator p.two_le_m))) := by
  simp [followerArmChoiceCore, hstatus, hslot, hselected, hvalid,
    upSlot_ne_dataSlot]
  · intro hnot
    exact False.elim (hnot rfl)

/-- A missing selected UP offer fails before the local affine bit is evaluated. -/
theorem followerArmChoiceCore_unoccupied_selected_up_missing
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (hstatus : s.status = .unoccupied)
    (hslot : slotDraw timeInput.1 = upSlot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i) :
    followerArmChoiceCore s timeInput i none = none := by
  simp [followerArmChoiceCore, hstatus, hslot, hselected, upSlot_ne_dataSlot]
  rfl

/-- A selected UP offer with a domain failure or a field mismatch fails before
its encoded word is used. -/
theorem followerArmChoiceCore_unoccupied_selected_up_invalid
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta))
    (hstatus : s.status = .unoccupied)
    (hslot : slotDraw timeInput.1 = upSlot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i)
    (hbad : ¬ (upStateDomain s ∧ offeredUpMatchesState s M)) :
    followerArmChoiceCore s timeInput i (some M) = none := by
  simp [followerArmChoiceCore, hstatus, hslot, hselected, hbad,
    upSlot_ne_dataSlot]
  rfl

/-- Other unoccupied communication uses this follower's tuple arm and does
not inspect the optional UP offer. -/
theorem followerArmChoiceCore_unoccupied_other
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hstatus : s.status = .unoccupied)
    (hnotdata : slotDraw timeInput.1 ≠ dataSlot)
    (hnotselected : ¬ (slotDraw timeInput.1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i)) :
    followerArmChoiceCore s timeInput i offeredUp =
      some ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
        (followerPlayer p.two_le_m i)) := by
  simp [followerArmChoiceCore, hstatus, hnotdata, hnotselected]

/-- Occupied local status requires this follower's own accepted DOWN fields. -/
theorem followerArmChoiceCore_occupied_missing_down
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hstatus : s.status ≠ .unoccupied) (hdown : s.lastDown = none) :
    followerArmChoiceCore s timeInput i offeredUp = none := by
  simp [followerArmChoiceCore, hstatus, hdown]

/-- A released follower, or any occupied follower on DATA, uses its own
accepted DOWN arm. -/
theorem followerArmChoiceCore_occupied_data_or_released
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (M : DownRecord (codecParams p eta))
    (hstatus : s.status ≠ .unoccupied)
    (hdown : s.lastDown = some M)
    (hbranch : s.status = .released ∨ slotDraw timeInput.1 = dataSlot) :
    followerArmChoiceCore s timeInput i offeredUp = some (downArm eta M) := by
  simp [followerArmChoiceCore, hstatus, hdown, hbranch]

/-- A pending selected-UP follower uses its own decoded escape arm when the
coordinator tuple arm is that arm. -/
theorem followerArmChoiceCore_pending_selected_up_escape
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (M : DownRecord (codecParams p eta))
    (hstatus : s.status = .pending)
    (hdown : s.lastDown = some M)
    (hslot : slotDraw timeInput.1 = upSlot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i)
    (hcoord : (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
      (coordinator p.two_le_m) = downAuxiliaryArm eta M) :
    followerArmChoiceCore s timeInput i offeredUp = some (downAuxiliaryArm eta M) := by
  simp [followerArmChoiceCore, hstatus, hdown, hslot, hselected, hcoord,
    upSlot_ne_dataSlot, upSlot_ne_downSlot]
  intro hnot
  exact False.elim (hnot rfl)

/-- The next pending branch uses this follower's escape arm when its decoded
arm collides with the selected tuple arm on DOWN or coordinator tuple arm on UP. -/
theorem followerArmChoiceCore_pending_collision_escape
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (M : DownRecord (codecParams p eta))
    (hstatus : s.status = .pending)
    (hdown : s.lastDown = some M)
    (hcollision :
      (slotDraw timeInput.1 = downSlot ∧
        downArm eta M = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          timeInput.1).val (followerPlayer p.two_le_m
          (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1))) ∨
      (slotDraw timeInput.1 = upSlot ∧
        downArm eta M = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
          timeInput.1).val (coordinator p.two_le_m))) :
    followerArmChoiceCore s timeInput i offeredUp = some (downAuxiliaryArm eta M) := by
  have hnotdata : slotDraw timeInput.1 ≠ dataSlot := by
    rcases hcollision with ⟨hslot, _⟩ | ⟨hslot, _⟩ <;> rw [hslot] <;> decide
  simp [followerArmChoiceCore, hstatus, hdown, hnotdata, hcollision]

/-- The final pending branch retains this follower's own decoded arm. -/
theorem followerArmChoiceCore_pending_own_arm
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (M : DownRecord (codecParams p eta))
    (hstatus : s.status = .pending)
    (hdown : s.lastDown = some M)
    (hnotdata : slotDraw timeInput.1 ≠ dataSlot)
    (hnotfirst : ¬ (slotDraw timeInput.1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i ∧
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
        (coordinator p.two_le_m) = downAuxiliaryArm eta M))
    (hnotcollision : ¬ ((slotDraw timeInput.1 = downSlot ∧
      downArm eta M = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
        timeInput.1).val (followerPlayer p.two_le_m
        (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1))) ∨
      (slotDraw timeInput.1 = upSlot ∧ downArm eta M =
        (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
          (coordinator p.two_le_m)))) :
    followerArmChoiceCore s timeInput i offeredUp = some (downArm eta M) := by
  simp [followerArmChoiceCore, hstatus, hdown, hnotdata, hnotfirst, hnotcollision]

/-- Every successful local result is an arm in the existing finite carrier. -/
theorem followerArmChoiceCore_success_arm_domain {p : Parameters} {eta : LearningRate}
    (s : State p eta) (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta))) (a : Fin p.K)
    (_h : followerArmChoiceCore s timeInput i offeredUp = some a) : a.val < p.K :=
  a.isLt

/-- The task-facing operation unfolds to the current local time input only. -/
theorem followerArmChoice_eq_core {p : Parameters} {eta : LearningRate}
    (s : State p eta) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (offeredUp : Option (UpRecord (codecParams p eta))) :
    followerArmChoice s row t i offeredUp = followerArmChoiceCore s (row.2 t) i offeredUp :=
  rfl

/-- Changing forward/public proposal bits while preserving this row's local
learning row cannot change this follower's arm choice. -/
theorem followerArmChoice_eq_of_same_learning_row {p : Parameters} {eta : LearningRate}
    (s : State p eta) (row₁ row₂ : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (offeredUp : Option (UpRecord (codecParams p eta)))
    (hrow : row₁.2 = row₂.2) :
    followerArmChoice s row₁ t i offeredUp = followerArmChoice s row₂ t i offeredUp := by
  have ht := congrFun hrow t
  unfold followerArmChoice
  rw [ht]

/-- The core reads only the local control slice and this follower's current
UP-channel sample. -/
theorem followerArmChoiceCore_eq_of_same_control_and_up_sample
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (time₁ time₂ : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hcontrol : time₁.1 = time₂.1)
    (hsample : time₁.2 (1, i) = time₂.2 (1, i)) :
    followerArmChoiceCore s time₁ i offeredUp =
      followerArmChoiceCore s time₂ i offeredUp := by
  rcases time₁ with ⟨control₁, samples₁⟩
  rcases time₂ with ⟨control₂, samples₂⟩
  change control₁ = control₂ at hcontrol
  cases hcontrol
  change samples₁ (1, i) = samples₂ (1, i) at hsample
  simp only [followerArmChoiceCore, offeredUpBit, hsample]

/-- The result depends on this round's literal slot, selected follower, tuple,
own pilot, and (only if used) the `(UP, i)` affine sample. Other labels of the
continuous slice, including `prop`, `fast`, and `assign`, may differ. -/
theorem followerArmChoiceCore_eq_of_same_local_draws
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (time₁ time₂ : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hslot : slotDraw time₁.1 = slotDraw time₂.1)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1 =
      selectedFollowerDraw p.two_le_m p.m_lt_K time₂.1)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K time₁.1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K time₂.1)
    (hpilot : pilotDraw (K_pos p) (followerPlayer p.two_le_m i) time₁.1 =
      pilotDraw (K_pos p) (followerPlayer p.two_le_m i) time₂.1)
    (hsample : time₁.2 (1, i) = time₂.2 (1, i)) :
    followerArmChoiceCore s time₁ i offeredUp =
      followerArmChoiceCore s time₂ i offeredUp := by
  dsimp only [followerArmChoiceCore, offeredUpBit]
  rw [← hslot, ← hselected, ← htuple, ← hpilot, ← hsample]

/-- If this follower is not an unoccupied UP target, changing every unused
sample and control coordinate leaves the result fixed, provided the literal
draws read by arm choice agree. -/
theorem followerArmChoiceCore_eq_of_same_local_draws_when_up_unused
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (time₁ time₂ : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hslot : slotDraw time₁.1 = slotDraw time₂.1)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1 =
      selectedFollowerDraw p.two_le_m p.m_lt_K time₂.1)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K time₁.1 =
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K time₂.1)
    (hpilot : pilotDraw (K_pos p) (followerPlayer p.two_le_m i) time₁.1 =
      pilotDraw (K_pos p) (followerPlayer p.two_le_m i) time₂.1)
    (hunused : ¬ (s.status = .unoccupied ∧
      slotDraw time₁.1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1 = i)) :
    followerArmChoiceCore s time₁ i offeredUp =
      followerArmChoiceCore s time₂ i offeredUp := by
  dsimp only [followerArmChoiceCore]
  rw [← hslot, ← hselected, ← htuple, ← hpilot]
  by_cases hstatus : s.status = .unoccupied
  · by_cases hdata : slotDraw time₁.1 = dataSlot
    · simp only [ite_eq_left hstatus, ite_eq_left hdata]
    · by_cases hup : slotDraw time₁.1 = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1 = i
      · exact False.elim (hunused ⟨hstatus, hup.1, hup.2⟩)
      · simp only [ite_eq_left hstatus, ite_eq_right hdata, ite_eq_right hup]
  · simp only [ite_eq_right hstatus]

/-- When the selected-unoccupied-UP branch is false, changing this time's
affine sample family cannot affect arm choice. -/
theorem followerArmChoiceCore_eq_of_same_control_when_up_unused
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (time₁ time₂ : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (hcontrol : time₁.1 = time₂.1)
    (hunused : ¬ (s.status = .unoccupied ∧
      slotDraw time₁.1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K time₁.1 = i)) :
    followerArmChoiceCore s time₁ i offeredUp =
      followerArmChoiceCore s time₂ i offeredUp := by
  have hcontrol' : time₁.1 = time₂.1 := hcontrol
  rcases time₁ with ⟨control₁, samples₁⟩
  rcases time₂ with ⟨control₂, samples₂⟩
  change control₁ = control₂ at hcontrol'
  cases hcontrol'
  by_cases hstatus : s.status = .unoccupied
  · by_cases hdata : slotDraw control₁ = dataSlot
    · simp [followerArmChoiceCore, hstatus, hdata]
    · by_cases hup : slotDraw control₁ = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K control₁ = i
      · exact False.elim (hunused ⟨hstatus, hup.1, hup.2⟩)
      · simp [followerArmChoiceCore, hstatus, hdata, hup]
  · simp [followerArmChoiceCore, hstatus]

/-- The supplied UP payload is irrelevant whenever this local action does not
enter the unoccupied selected-UP branch. -/
theorem followerArmChoiceCore_eq_of_offer_unused
    {p : Parameters} {eta : LearningRate} (s : State p eta)
    (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offer₁ offer₂ : Option (UpRecord (codecParams p eta)))
    (hunused : ¬ (s.status = .unoccupied ∧
      slotDraw timeInput.1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i)) :
    followerArmChoiceCore s timeInput i offer₁ =
      followerArmChoiceCore s timeInput i offer₂ := by
  by_cases hstatus : s.status = .unoccupied
  · by_cases hdata : slotDraw timeInput.1 = dataSlot
    · simp [followerArmChoiceCore, hstatus, hdata]
    · by_cases hup : slotDraw timeInput.1 = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i
      · exact False.elim (hunused ⟨hstatus, hup.1, hup.2⟩)
      · simp [followerArmChoiceCore, hstatus, hdata, hup]
  · simp [followerArmChoiceCore, hstatus]

/-- Conditional comparison with the common-assignment follower action. The
hypotheses expose the local status, decoded arms, row controls, and (only on a
selected unoccupied UP branch) the supplied offer and matching UP word. They
make no claim that a full run or decoder establishes those matches. -/
theorem followerArmChoiceCore_eq_common_followerAction
    {p : Parameters} {eta : LearningRate}
    (s : State p eta) (timeInput : ContinuousLearningRows.TimeControl p) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta)))
    (a : Assignment p.m p.K) (snapshot : Snapshot a)
    (r : RoundInput a (ContinuousLearningRows.B p))
    (hstatus : s.status = snapshot.status i)
    (hslot : slotDraw timeInput.1 = r.slot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = r.selected)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1 = r.tuple)
    (hpilot : pilotDraw (K_pos p) (followerPlayer p.two_le_m i) timeInput.1 =
      r.pilots (followerPlayer p.two_le_m i))
    (hdecoded : ∀ _hoccupied : s.status ≠ .unoccupied,
      ∃ M : DownRecord (codecParams p eta),
        s.lastDown = some M ∧ downArm eta M = a.assigned i ∧
          downAuxiliaryArm eta M = a.auxiliary)
    (hoff : ∀ (_hunoccupied : s.status = .unoccupied)
      (_hup : slotDraw timeInput.1 = upSlot)
      (_hself : selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i),
      ∃ M : UpRecord (codecParams p eta),
        offeredUp = some M ∧ upStateDomain s ∧ offeredUpMatchesState s M ∧
          r.up = ⟨timeInput.2 (1, i), offeredUpWord eta M⟩) :
    followerArmChoiceCore s timeInput i offeredUp =
      some (ActiveRoundActions.followerAction p.two_le_m snapshot r i) := by
  classical
  have hstatus' : snapshot.status i = s.status := hstatus.symm
  by_cases hunoccupied : s.status = .unoccupied
  · have hsnap : snapshot.status i = .unoccupied := hstatus'.trans hunoccupied
    by_cases hdata : slotDraw timeInput.1 = dataSlot
    · rw [followerArmChoiceCore_unoccupied_data s timeInput i offeredUp hunoccupied hdata]
      have hrdata : r.slot = dataSlot := hslot.symm.trans hdata
      simp [ActiveRoundActions.followerAction, hsnap, hrdata, hpilot]
    · by_cases hselectedUp : slotDraw timeInput.1 = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i
      · obtain ⟨M, hM, hdomain, hfields, hword⟩ :=
          hoff hunoccupied hselectedUp.1 hselectedUp.2
        have hvalid : upStateDomain s ∧ offeredUpMatchesState s M :=
          ⟨hdomain, hfields⟩
        have hcore := followerArmChoiceCore_unoccupied_selected_up s timeInput i M
          hunoccupied hselectedUp.1 hselectedUp.2 hvalid
        rw [hM, hcore]
        have hrup : r.slot = upSlot := hslot.symm.trans hselectedUp.1
        have hrselected : r.selected = i := hselected.symm.trans hselectedUp.2
        have hbit : r.up.bit = offeredUpBit eta timeInput i M := by
          rw [hword]
          rfl
        have haction : ActiveRoundActions.followerAction p.two_le_m snapshot r i =
            sendArm r.up.bit (r.tuple.val (followerPlayer p.two_le_m i))
              (r.tuple.val (coordinator p.two_le_m)) := by
          simp [ActiveRoundActions.followerAction, hsnap, hrup, hrselected,
            upSlot_ne_dataSlot]
          intro hnot
          exact False.elim (hnot rfl)
        rw [haction, hbit, htuple]
      · have hrnotdata : r.slot ≠ dataSlot := by
          intro h
          exact hdata (hslot.trans h)
        have hrnotselected : ¬ (r.slot = upSlot ∧ r.selected = i) := by
          intro h
          exact hselectedUp ⟨hslot.trans h.1, hselected.trans h.2⟩
        have hcore := followerArmChoiceCore_unoccupied_other s timeInput i offeredUp
          hunoccupied hdata hselectedUp
        rw [hcore, htuple]
        simp [ActiveRoundActions.followerAction, hsnap, hrnotdata, hrnotselected]
  · obtain ⟨M, hdown, harm, haux⟩ := hdecoded hunoccupied
    by_cases hreleased : s.status = .released
    · have hcore := followerArmChoiceCore_occupied_data_or_released s timeInput i
        offeredUp M hunoccupied hdown (Or.inl hreleased)
      rw [hcore]
      have hsnapReleased : snapshot.status i = .released := hstatus'.trans hreleased
      simp [ActiveRoundActions.followerAction, hsnapReleased, harm]
    · have hpending : s.status = .pending := by
        cases hs : s.status with
        | unoccupied => exact False.elim (hunoccupied hs)
        | pending => rfl
        | released => exact False.elim (hreleased hs)
      have hsnapPending : snapshot.status i = .pending := hstatus'.trans hpending
      by_cases hdata : slotDraw timeInput.1 = dataSlot
      · have hcore := followerArmChoiceCore_occupied_data_or_released s timeInput i
          offeredUp M hunoccupied hdown (Or.inr hdata)
        rw [hcore]
        have hrdata : r.slot = dataSlot := hslot.symm.trans hdata
        simp [ActiveRoundActions.followerAction, hsnapPending, hrdata, harm]
      · by_cases hfirst : slotDraw timeInput.1 = upSlot ∧
          selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i ∧
            (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
              (coordinator p.two_le_m) = downAuxiliaryArm eta M
        · have hcore := followerArmChoiceCore_pending_selected_up_escape s timeInput i
            offeredUp M hpending hdown hfirst.1 hfirst.2.1 hfirst.2.2
          rw [hcore]
          have hrup : r.slot = upSlot := hslot.symm.trans hfirst.1
          have hrselected : r.selected = i := hselected.symm.trans hfirst.2.1
          have hcoord : r.tuple.val (coordinator p.two_le_m) = a.auxiliary := by
            calc
              r.tuple.val (coordinator p.two_le_m) =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                    (coordinator p.two_le_m) := by rw [← htuple]
              _ = downAuxiliaryArm eta M := hfirst.2.2
              _ = a.auxiliary := haux
          have haction : ActiveRoundActions.followerAction p.two_le_m snapshot r i =
              a.auxiliary := by
            simp [ActiveRoundActions.followerAction, hsnapPending, hrup, hrselected,
              hcoord, upSlot_ne_dataSlot, upSlot_ne_downSlot]
            intro hnot
            exact False.elim (hnot rfl)
          rw [haction, haux]
        · by_cases hcollision :
            (slotDraw timeInput.1 = downSlot ∧
              downArm eta M = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
                timeInput.1).val (followerPlayer p.two_le_m
                (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1))) ∨
            (slotDraw timeInput.1 = upSlot ∧ downArm eta M =
              (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                (coordinator p.two_le_m))
          · have hcore := followerArmChoiceCore_pending_collision_escape s timeInput i
              offeredUp M hpending hdown hcollision
            rw [hcore]
            have hrnotfirst : ¬ (r.slot = upSlot ∧ r.selected = i ∧
                r.tuple.val (coordinator p.two_le_m) = a.auxiliary) := by
              intro h
              apply hfirst
              refine ⟨hslot.trans h.1, hselected.trans h.2.1, ?_⟩
              calc
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                    (coordinator p.two_le_m) =
                    r.tuple.val (coordinator p.two_le_m) := by rw [htuple]
                _ = a.auxiliary := h.2.2
                _ = downAuxiliaryArm eta M := haux.symm
            have hroundcollision :
                (r.slot = downSlot ∧ a.assigned i = r.tuple.val
                  (followerPlayer p.two_le_m r.selected)) ∨
                (r.slot = upSlot ∧ a.assigned i = r.tuple.val (coordinator p.two_le_m)) := by
              rcases hcollision with ⟨hround, harmTuple⟩ | ⟨hround, harmTuple⟩
              · left
                refine ⟨hslot.symm.trans hround, ?_⟩
                calc
                  a.assigned i = downArm eta M := harm.symm
                  _ = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                      (followerPlayer p.two_le_m
                        (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1)) := harmTuple
                  _ = r.tuple.val (followerPlayer p.two_le_m r.selected) := by
                    rw [htuple, hselected]
              · right
                refine ⟨hslot.symm.trans hround, ?_⟩
                calc
                  a.assigned i = downArm eta M := harm.symm
                  _ = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                      (coordinator p.two_le_m) := harmTuple
                  _ = r.tuple.val (coordinator p.two_le_m) := by rw [htuple]
            have hrdata : r.slot ≠ dataSlot := by
              intro h
              exact hdata (hslot.trans h)
            have haction : ActiveRoundActions.followerAction p.two_le_m snapshot r i =
                a.auxiliary := by
              simp [ActiveRoundActions.followerAction, hsnapPending, hrdata,
                hrnotfirst, hroundcollision]
            rw [haction, haux]
          · have hnotfirst : ¬ (slotDraw timeInput.1 = upSlot ∧
              selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1 = i ∧
              (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                (coordinator p.two_le_m) = downAuxiliaryArm eta M) := hfirst
            have hcore := followerArmChoiceCore_pending_own_arm s timeInput i offeredUp M
              hpending hdown hdata hnotfirst hcollision
            rw [hcore]
            have hrdata : r.slot ≠ dataSlot := by
              intro h
              exact hdata (hslot.trans h)
            have hrnotfirst : ¬ (r.slot = upSlot ∧ r.selected = i ∧
                r.tuple.val (coordinator p.two_le_m) = a.auxiliary) := by
              intro h
              apply hnotfirst
              refine ⟨hslot.trans h.1, hselected.trans h.2.1, ?_⟩
              calc
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                    (coordinator p.two_le_m) =
                    r.tuple.val (coordinator p.two_le_m) := by rw [htuple]
                _ = a.auxiliary := h.2.2
                _ = downAuxiliaryArm eta M := haux.symm
            have hrnotcollision : ¬ ((r.slot = downSlot ∧ a.assigned i =
                r.tuple.val (followerPlayer p.two_le_m r.selected)) ∨
                (r.slot = upSlot ∧ a.assigned i =
                  r.tuple.val (coordinator p.two_le_m))) := by
              intro h
              apply hcollision
              rcases h with ⟨hround, harmTuple⟩ | ⟨hround, harmTuple⟩
              · left
                refine ⟨hslot.trans hround, ?_⟩
                calc
                  downArm eta M = a.assigned i := harm
                  _ = r.tuple.val (followerPlayer p.two_le_m r.selected) := harmTuple
                  _ = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                      (followerPlayer p.two_le_m
                        (selectedFollowerDraw p.two_le_m p.m_lt_K timeInput.1)) := by
                    rw [← htuple, ← hselected]
              · right
                refine ⟨hslot.trans hround, ?_⟩
                calc
                  downArm eta M = a.assigned i := harm
                  _ = r.tuple.val (coordinator p.two_le_m) := harmTuple
                  _ = (OrderedTupleSampler.sample p.two_le_m p.m_lt_K timeInput.1).val
                      (coordinator p.two_le_m) := by rw [← htuple]
            have haction : ActiveRoundActions.followerAction p.two_le_m snapshot r i =
                a.assigned i := by
              simp [ActiveRoundActions.followerAction, hsnapPending, hrdata,
                hrnotfirst, hrnotcollision]
            rw [haction, harm]

/-- The row-facing operation agrees with the common-assignment follower arm
under the same explicit local matching inputs. -/
theorem followerArmChoice_eq_common_followerAction
    {p : Parameters} {eta : LearningRate}
    (s : State p eta) (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (i : Fin (p.m - 1)) (offeredUp : Option (UpRecord (codecParams p eta)))
    (a : Assignment p.m p.K) (snapshot : Snapshot a)
    (r : RoundInput a (ContinuousLearningRows.B p))
    (hstatus : s.status = snapshot.status i)
    (hslot : slotDraw (row.2 t).1 = r.slot)
    (hselected : selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = r.selected)
    (htuple : OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1 = r.tuple)
    (hpilot : pilotDraw (K_pos p) (followerPlayer p.two_le_m i) (row.2 t).1 =
      r.pilots (followerPlayer p.two_le_m i))
    (hdecoded : ∀ _hoccupied : s.status ≠ .unoccupied,
      ∃ M : DownRecord (codecParams p eta),
        s.lastDown = some M ∧ downArm eta M = a.assigned i ∧
          downAuxiliaryArm eta M = a.auxiliary)
    (hoff : ∀ (_hunoccupied : s.status = .unoccupied)
      (_hup : slotDraw (row.2 t).1 = upSlot)
      (_hself : selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i),
      ∃ M : UpRecord (codecParams p eta),
        offeredUp = some M ∧ upStateDomain s ∧ offeredUpMatchesState s M ∧
          r.up = ⟨(row.2 t).2 (1, i), offeredUpWord eta M⟩) :
    followerArmChoice s row t i offeredUp =
      some (ActiveRoundActions.followerAction p.two_le_m snapshot r i) := by
  exact followerArmChoiceCore_eq_common_followerAction s (row.2 t) i offeredUp
    a snapshot r hstatus hslot hselected htuple hpilot hdecoded hoff

end Bandits.Support.ActiveFollowerArmChoice

end
