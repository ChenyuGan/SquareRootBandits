/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceDownReception
public import Bandits.Support.AssignmentPayloadDerivedMeasurability
public import Bandits.Support.FollowerObservationStageMeasurabilityRepair
public import Bandits.Support.FollowerDownJointMeasurability

import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Joint measurability of the reference DOWN reception cut

This module keeps the existing coordinator choice-time view, follower carried
state, complete public row, finite time, finite-grid feedback, and one fixed
rate input. Its countable observation records both the actual local DOWN
result and the exact coordinator-word comparison; reconstruction receives the
original continuous sparse buffer.

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,192-209,270-276`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,54-60`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.CompletePublicTable
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.SparseCalendarReplay
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.ReferenceDownReception

namespace Bandits.Support.ReferenceDownReceptionMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters} {rate : RateInput p}

local instance choiceCutoffMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

/-- Extend the supplied complement weights by zero on arms outside the
payload's fast complement. This retains every original real-valued complement
coordinate and gives the view a fixed finite-product observation carrier. -/
def choiceTimeViewWeightVector (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (a : Fin p.K) : ℝ :=
  if ha : a ∈ fastArmFinset view.payload.slowSet then
    view.complementWeights ⟨a, ha⟩
  else 0

/-- Lossless coordinates for the existing choice-time view. The payload keeps
its existing payload-observation measurable space; pending and cutoff are
finite/discrete, and complement weights remain real Borel coordinates. -/
def choiceTimeViewObservation (view : ReferenceDownReception.ChoiceTimeView p rate.eta) :
    AssignmentStartPayload.Input p rate.eta ×
      (Finset (Follower p.m) ×
        (Option (CoordinatorLocalArmChoice.Cutoff p) × (Fin p.K → ℝ))) :=
  (view.payload,
    (view.pendingAtChoice,
      (view.cutoff, choiceTimeViewWeightVector view)))

theorem choiceTimeViewObservation_injective :
    Function.Injective (choiceTimeViewObservation (p := p) (rate := rate)) := by
  intro left right h
  cases left with
  | mk payload pending cutoff weights =>
    cases right with
    | mk payload' pending' cutoff' weights' =>
      simp only [choiceTimeViewObservation, Prod.mk.injEq] at h
      rcases h with ⟨hpayload, hpending, hcutoff, hweights⟩
      cases hpayload
      have hweights' : weights = weights' := by
        funext a
        have hvalue := congrFun hweights a.1
        have hmem : a.1 ∈ fastArmFinset payload.slowSet := a.2
        simpa [choiceTimeViewWeightVector, hmem] using hvalue
      cases hpending
      cases hcutoff
      cases hweights'
      rfl

instance choiceTimeViewMeasurableSpace :
    MeasurableSpace (ReferenceDownReception.ChoiceTimeView p rate.eta) :=
  MeasurableSpace.comap choiceTimeViewObservation
    (inferInstance : MeasurableSpace
      (AssignmentStartPayload.Input p rate.eta ×
        (Finset (Follower p.m) ×
          (Option (CoordinatorLocalArmChoice.Cutoff p) × (Fin p.K → ℝ)))))

private theorem measurable_choiceTimeViewObservation :
    Measurable (choiceTimeViewObservation (p := p) (rate := rate)) :=
  comap_measurable _

private theorem measurable_choiceTimeViewPayload :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload) :=
  measurable_fst.comp measurable_choiceTimeViewObservation

private theorem measurable_choiceTimeViewCutoff :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.cutoff) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp measurable_choiceTimeViewObservation))

private theorem measurable_choiceTimeViewWeights :
    Measurable (choiceTimeViewWeightVector (p := p) (rate := rate)) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_choiceTimeViewObservation))

private theorem measurable_payloadObservation :
    Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) :=
  comap_measurable _

private theorem measurable_choiceViewSigma :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.sigma) := by
  have hobs : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      LaterAssignmentStartMeasurability.payloadObservation view.payload) :=
    (measurable_payloadObservation (p := p) (rate := rate)).comp
      (measurable_choiceTimeViewPayload (p := p) (rate := rate))
  change Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    (LaterAssignmentStartMeasurability.payloadObservation view.payload).2.1)
  exact measurable_fst.comp (measurable_snd.comp hobs)

private theorem measurable_choiceViewSlowSet :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.slowSet.1) := by
  have hobs : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      LaterAssignmentStartMeasurability.payloadObservation view.payload) :=
    (measurable_payloadObservation (p := p) (rate := rate)).comp
      (measurable_choiceTimeViewPayload (p := p) (rate := rate))
  change Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    (LaterAssignmentStartMeasurability.payloadObservation view.payload).2.2.1)
  exact measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp hobs))

private theorem measurable_choiceViewAnchor :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.anchor) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputAnchor.comp
    measurable_choiceTimeViewPayload

private theorem measurable_choiceViewWeightAt (a : Fin p.K) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      choiceTimeViewWeightVector view a) :=
  (measurable_pi_apply a).comp measurable_choiceTimeViewWeights

private theorem measurable_eval_fin {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {β : Type*} [MeasurableSpace β]
    (f : Ω → Fin n → β) (i : Ω → Fin n) (hf : Measurable f) (hi : Measurable i) :
    Measurable (fun x => f x (i x)) := by
  intro s hs
  have hset : (fun x => f x (i x)) ⁻¹' s =
      ⋃ j : Fin n, {x | i x = j} ∩ (fun x => f x j) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨i x, rfl, hx⟩
    · rintro ⟨j, hidx, hval⟩
      rw [hidx]
      exact hval
  rw [hset]
  apply MeasurableSet.iUnion
  intro j
  exact (hi (measurableSet_singleton j)).inter
    (((measurable_pi_apply j).comp hf) hs)

local instance choiceSlowSetMeasurableSpace :
    MeasurableSpace (CanonicalOrientedSetLaw.SlowSet p.K p.m) := ⊤

local instance choiceDownRecordMeasurableSpace :
    MeasurableSpace (OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) := ⊤

private def downFieldsCoordinates (fields : OrdinaryMessageCodec.DownFields) :=
  (fields.sigma, (fields.a, (fields.e, (fields.h, fields.q))))

private theorem downFieldsCoordinates_injective :
    Function.Injective downFieldsCoordinates := by
  intro left right h
  cases left with
  | mk ls la le lh lq =>
    cases right with
    | mk rs ra re rh rq =>
      simp only [downFieldsCoordinates, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
      rfl

private theorem measurable_choiceViewSlowSetIndex :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.slowSet) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro S
  have hset : {view : ReferenceDownReception.ChoiceTimeView p rate.eta |
      view.payload.slowSet = S} =
      {view | view.payload.slowSet.1 = S.1} := by
    ext view
    simp only [Set.mem_ofPred_eq]
    exact Subtype.ext_iff
  rw [hset]
  exact measurable_choiceViewSlowSet (measurableSet_singleton S.1)

private theorem measurable_choiceViewAssigned (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.assignment.assigned i) := by
  change Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    CanonicalAssignmentVector.followerArm p.two_le_m view.payload.slowSet i)
  have hfinite : Measurable (fun S : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
      CanonicalAssignmentVector.followerArm p.two_le_m S i) := measurable_of_countable _
  exact hfinite.comp measurable_choiceViewSlowSetIndex

private theorem measurable_choiceViewAuxiliary :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.assignment.auxiliary) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary.comp
    measurable_choiceTimeViewPayload

private theorem measurable_choiceViewExponent :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      AssignmentPayloadDerivedMeasurability.inputExponent view.payload) :=
  AssignmentPayloadDerivedMeasurability.measurable_inputExponent.comp
    measurable_choiceTimeViewPayload

private theorem measurable_choiceViewQueues :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      (LaterAssignmentStartMeasurability.payloadObservation view.payload).2.2.2.2) := by
  have hobs := (measurable_payloadObservation (p := p) (rate := rate)).comp
    (measurable_choiceTimeViewPayload (p := p) (rate := rate))
  exact measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp hobs)))

private theorem measurable_fin_val_succ {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (f : Ω → Fin n) (hf : Measurable f) : Measurable (fun x => (f x).val + 1) := by
  have hval : Measurable (fun x => (f x).val) :=
    (measurable_of_finite (fun a : Fin n => a.val)).comp hf
  exact (measurable_of_countable (fun k : ℕ => k + 1)).comp hval

private theorem measurable_choiceViewAssignedNat (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      (view.payload.assignment.assigned i).val + 1) :=
  measurable_fin_val_succ _ (measurable_choiceViewAssigned i)

private theorem measurable_choiceViewAuxiliaryNat :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.assignment.auxiliary.val + 1) :=
  measurable_fin_val_succ _ measurable_choiceViewAuxiliary

private theorem measurable_choiceViewExponentAt (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      AssignmentPayloadDerivedMeasurability.inputExponent view.payload
        (view.payload.assignment.assigned i)) :=
  measurable_eval_fin
    (f := fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      AssignmentPayloadDerivedMeasurability.inputExponent view.payload)
    (i := fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.assignment.assigned i)
    (hf := measurable_choiceViewExponent (p := p) (rate := rate))
    (hi := measurable_choiceViewAssigned i)

private theorem measurable_choiceViewQueueAt (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      (LaterAssignmentStartMeasurability.payloadObservation view.payload).2.2.2.2
        (view.payload.assignment.assigned i)) :=
  measurable_eval_fin
    (f := fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      (LaterAssignmentStartMeasurability.payloadObservation view.payload).2.2.2.2)
    (i := fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.assignment.assigned i)
    (hf := measurable_choiceViewQueues (p := p) (rate := rate))
    (hi := measurable_choiceViewAssigned i)

private theorem measurable_choiceViewSigmaNat :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.sigma.val + 1) :=
  measurable_fin_val_succ _ measurable_choiceViewSigma

private theorem measurable_choiceViewDownRecordCoordinates (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      downFieldsCoordinates (view.payload.downRecord i).val) := by
  have hexpqueue := (measurable_choiceViewExponentAt (p := p) (rate := rate) i).prodMk
    (measurable_choiceViewQueueAt (p := p) (rate := rate) i)
  have haux := (measurable_choiceViewAuxiliaryNat (p := p) (rate := rate)).prodMk hexpqueue
  have hassigned := (measurable_choiceViewAssignedNat (p := p) (rate := rate) i).prodMk haux
  have htuple := (measurable_choiceViewSigmaNat (p := p) (rate := rate)).prodMk hassigned
  have heq : (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      downFieldsCoordinates (view.payload.downRecord i).val) =
      fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
        (view.payload.sigma.val + 1,
          ((view.payload.assignment.assigned i).val + 1,
            (view.payload.assignment.auxiliary.val + 1,
              (AssignmentPayloadDerivedMeasurability.inputExponent view.payload
                (view.payload.assignment.assigned i),
               (LaterAssignmentStartMeasurability.payloadObservation view.payload).2.2.2.2
                 (view.payload.assignment.assigned i))))) := by
    funext view
    rfl
  rw [heq]
  exact htuple

private theorem measurable_choiceViewDownRecord (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      view.payload.downRecord i) := by
  have hcoordinates := measurable_choiceViewDownRecordCoordinates (p := p) (rate := rate) i
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro record
  have hset : {view : ReferenceDownReception.ChoiceTimeView p rate.eta |
      view.payload.downRecord i = record} =
      (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
        downFieldsCoordinates (view.payload.downRecord i).val) ⁻¹'
        {downFieldsCoordinates record.val} := by
    ext view
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact congrArg (fun r : OrdinaryMessageCodec.DownRecord
        (ReferencePrelaunchFollower.codecParams p rate.eta) =>
          downFieldsCoordinates r.val) h
    · intro h
      apply Subtype.ext
      exact downFieldsCoordinates_injective h
  rw [hset]
  exact hcoordinates (measurableSet_singleton _)

private theorem measurable_choiceViewStoredDownFlatWord (i : Fin (p.m - 1)) :
    Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
      CoordinatorLocalArmChoice.storedDownFlatWord view.payload i) := by
  have hencode : Measurable (fun record : OrdinaryMessageCodec.DownRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta) =>
      OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (OrdinaryMessageCodec.encodeDown
          (ReferencePrelaunchFollower.codecParams p rate.eta) record)) :=
    measurable_of_countable _
  change Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
    OrdinaryMessageCodec.wordEquivFlat
      (ReferencePrelaunchFollower.codecParams p rate.eta)
      (view.payload.downWord i))
  change Measurable
    ((fun record => OrdinaryMessageCodec.wordEquivFlat
        (ReferencePrelaunchFollower.codecParams p rate.eta)
        (OrdinaryMessageCodec.encodeDown
          (ReferencePrelaunchFollower.codecParams p rate.eta) record)) ∘
      (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
        view.payload.downRecord i))
  exact hencode.comp (measurable_choiceViewDownRecord i)

def choiceInputsValidBit
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta) (t : Fin p.T) : Bool := by
  classical
  exact decide (CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
    view.complementWeights)

private theorem choiceInputsValidBit_eq_true
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta) (t : Fin p.T) :
    choiceInputsValidBit view t = true ↔
      CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
        view.complementWeights := by
  simp [choiceInputsValidBit]

private theorem measurable_finIndex_eval {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {n : ℕ} (f : Fin n → α → β)
    (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x : α × Fin n => f x.2 x.1) := by
  intro s hs
  have hset : (fun x : α × Fin n => f x.2 x.1) ⁻¹' s =
      ⋃ j : Fin n, {x | x.2 = j} ∩ (fun x => f j x.1) ⁻¹' s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨x.2, rfl, hx⟩
    · rintro ⟨j, hidx, hvalue⟩
      rw [hidx]
      exact hvalue
  rw [hset]
  apply MeasurableSet.iUnion
  intro j
  exact (measurable_snd (measurableSet_singleton j)).inter
    (((hf j).comp measurable_fst) hs)

private theorem measurable_choiceViewDownSelection (i : Fin (p.m - 1)) :
    Measurable (fun x : CompleteRow p × Fin p.T =>
      FollowerDownJointMeasurability.downSelectionBit i x.1 x.2) := by
  exact measurable_finIndex_eval
    (fun t row => FollowerDownJointMeasurability.downSelectionBit i row t)
    (fun t => FollowerDownJointMeasurability.measurable_downSelectedAt p i t)

private def expectedDownFlatWordSome (i : Fin (p.m - 1))
    (x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T)) :
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  by
    classical
    exact if choiceInputsValidBit x.1 x.2.2 &&
        (FollowerDownJointMeasurability.downSelectionBit i x.2.1 x.2.2 &&
          decide (i ∈ x.1.pendingAtChoice)) then
      some (CoordinatorLocalArmChoice.storedDownFlatWord x.1.payload i)
    else none

private theorem expectedDownFlatWord_eq_expectedSome
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T) :
    ReferenceDownReception.expectedDownFlatWord (some view) i row t =
      expectedDownFlatWordSome i (Prod.mk view (Prod.mk row t)) := by
  classical
  have hbranchBits :
      (FollowerDownJointMeasurability.downSelectionBit i row t &&
        decide (i ∈ view.pendingAtChoice)) = true ↔
      ReferenceDownReception.selectedDownSenderBranch view i row t := by
    simp [ReferenceDownReception.selectedDownSenderBranch,
      FollowerDownJointMeasurability.downSelectionBit_eq_true,
      ActiveFollowerDownAcceptance.downSelected, and_assoc]
  by_cases hbranch : ReferenceDownReception.selectedDownSenderBranch view i row t
  · have hchoice :
        CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
          view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none ↔
        CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
          view.complementWeights := by
      constructor
      · intro hne
        by_contra hinvalid
        apply hne
        rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
        exact CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
          view.payload view.pendingAtChoice view.cutoff t view.complementWeights
          (row.2 t) hinvalid
      · intro hvalid
        rcases hbranch with ⟨hdown, hselected, hpending⟩
        have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive
            view.payload view.cutoff t ∧ view.pendingAtChoice = ∅) := by
          rintro ⟨_, hempty⟩
          exact (Finset.Nonempty.ne_empty ⟨i, hpending⟩) hempty
        have hnotdata : PublicDiscreteDraws.slotDraw (row.2 t).1 ≠
            PublicDiscreteDraws.dataSlot := by
          rw [hdown]
          decide
        have hselectedPending : PublicDiscreteDraws.selectedFollowerDraw
            p.two_le_m p.m_lt_K (row.2 t).1 ∈ view.pendingAtChoice := by
          rw [hselected]
          exact hpending
        rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
          CoordinatorLocalArmChoice.coordinatorArmChoiceCore_down
            view.payload view.pendingAtChoice view.cutoff t view.complementWeights
            (row.2 t) hvalid hnotfast hnotdata hdown hselectedPending]
        simp
    have hdownBit : FollowerDownJointMeasurability.downSelectionBit i row t = true :=
      (FollowerDownJointMeasurability.downSelectionBit_eq_true i row t).2
        ⟨hbranch.1, hbranch.2.1⟩
    have hpendingBit : decide (i ∈ view.pendingAtChoice) = true := by
      exact decide_eq_true hbranch.2.2
    simp [expectedDownFlatWordSome, ReferenceDownReception.expectedDownFlatWord,
      hchoice, hbranch, hdownBit, hpendingBit, choiceInputsValidBit_eq_true]
  · simp [expectedDownFlatWordSome, ReferenceDownReception.expectedDownFlatWord, hbranch,
      hbranchBits]

/-- On the selected DOWN-to-pending branch, the coordinator's literal choice
succeeds exactly when the payload, finite time/cutoff, and complement-weight
checks in `ChoiceInputsValid` pass. A nonempty pending set rules out the
fast-only branch. -/
theorem coordinatorArmChoice_ne_none_iff_choiceInputsValid_of_selectedDown
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (hbranch : ReferenceDownReception.selectedDownSenderBranch view i row t) :
    CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
        view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none ↔
      CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
        view.complementWeights := by
  constructor
  · intro hchoice
    have hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload
        view.cutoff t view.complementWeights := by
      by_contra hinvalid
      have hnone := CoordinatorLocalArmChoice.coordinatorArmChoiceCore_none_of_invalid
        view.payload view.pendingAtChoice view.cutoff t view.complementWeights
        (row.2 t) hinvalid
      apply hchoice
      rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core]
      exact hnone
    exact hvalid
  · intro hvalid
    rcases hbranch with ⟨hdown, hselected, hpending⟩
    have hpendingNonempty : view.pendingAtChoice.Nonempty := ⟨i, hpending⟩
    have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive
        view.payload view.cutoff t ∧ view.pendingAtChoice = ∅) := by
      rintro ⟨_, hempty⟩
      exact hpendingNonempty.ne_empty hempty
    have hnotdata : PublicDiscreteDraws.slotDraw (row.2 t).1 ≠
        PublicDiscreteDraws.dataSlot := by
      rw [hdown]
      decide
    have hselectedPending : PublicDiscreteDraws.selectedFollowerDraw
        p.two_le_m p.m_lt_K (row.2 t).1 ∈ view.pendingAtChoice := by
      rw [hselected]
      exact hpending
    rw [CoordinatorLocalArmChoice.coordinatorArmChoice_eq_core,
      CoordinatorLocalArmChoice.coordinatorArmChoiceCore_down
        view.payload view.pendingAtChoice view.cutoff t view.complementWeights
        (row.2 t) hvalid hnotfast hnotdata hdown hselectedPending]
    simp

/-- The exact reference expected word is present precisely on the selected
pending DOWN branch when the actual finite-time, positive-weight, and
current-envelope checks all pass. -/
theorem expectedDownFlatWord_eq_some_iff_choiceInputsValid
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T) :
    ReferenceDownReception.expectedDownFlatWord (some view) i row t =
        some (CoordinatorLocalArmChoice.storedDownFlatWord view.payload i) ↔
      CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
        view.complementWeights ∧
        ReferenceDownReception.selectedDownSenderBranch view i row t := by
  rw [ReferenceDownReception.expectedDownFlatWord_eq_some_iff]
  constructor
  · rintro ⟨hchoice, hbranch⟩
    exact ⟨(coordinatorArmChoice_ne_none_iff_choiceInputsValid_of_selectedDown
      view i row t hbranch).mp hchoice, hbranch⟩
  · rintro ⟨hvalid, hbranch⟩
    exact ⟨(coordinatorArmChoice_ne_none_iff_choiceInputsValid_of_selectedDown
      view i row t hbranch).mpr hvalid, hbranch⟩

private theorem choiceInputsValid_iff_envelope
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta) (t : Fin p.T) :
    CoordinatorLocalArmChoice.ChoiceInputsValid view.payload view.cutoff t
        view.complementWeights ↔
      CoordinatorLocalArmChoice.SourceTimeValid view.payload view.cutoff t ∧
        ∀ a : Fin p.K, a ∈ fastArmFinset view.payload.slowSet →
          0 < choiceTimeViewWeightVector view a ∧
            view.payload.anchor a ≤ choiceTimeViewWeightVector view a ∧
            choiceTimeViewWeightVector view a ≤
              2 * view.payload.anchor a := by
  constructor
  · intro h
    refine ⟨h.time, ?_⟩
    intro a ha
    let j : FastArm view.payload.slowSet := ⟨a, ha⟩
    have hpos := h.current_weight_pos j
    have hlow := h.anchor_le_current j
    have hhigh := h.current_le_twice_anchor j
    simpa only [choiceTimeViewWeightVector, dite_eq_left ha] using ⟨hpos, hlow, hhigh⟩
  · rintro ⟨htime, henvelope⟩
    refine ⟨htime, rate.eta.property, view.payload.eta_le_source_cap,
      view.payload.anchor_pos, ?_, ?_, ?_⟩
    · intro j
      have hj : choiceTimeViewWeightVector view j.1 = view.complementWeights j := by
        simp [choiceTimeViewWeightVector, j.2]
      simpa only [hj] using (henvelope j.1 j.2).1
    · intro j
      have hj : choiceTimeViewWeightVector view j.1 = view.complementWeights j := by
        simp [choiceTimeViewWeightVector, j.2]
      simpa only [hj] using (henvelope j.1 j.2).2.1
    · intro j
      have hj : choiceTimeViewWeightVector view j.1 = view.complementWeights j := by
        simp [choiceTimeViewWeightVector, j.2]
      simpa only [hj] using (henvelope j.1 j.2).2.2

private def sourceTimeConditions (sigma : Fin p.T)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (t : Fin p.T) : Prop :=
  1 ≤ CoordinatorLocalArmChoice.sourceRound t ∧
    CoordinatorLocalArmChoice.sourceRound t ≤ p.T ∧
    1 ≤ CoordinatorLocalArmChoice.cutoffRound cutoff ∧
    CoordinatorLocalArmChoice.cutoffRound cutoff ≤ p.T + 1 ∧
    sigma.val + 1 ≤ CoordinatorLocalArmChoice.sourceRound t ∧
    sigma.val + 1 ≤ CoordinatorLocalArmChoice.cutoffRound cutoff

private theorem sourceTimeValid_iff_conditions
    (payload : AssignmentStartPayload.Input p rate.eta)
    (cutoff : Option (CoordinatorLocalArmChoice.Cutoff p)) (t : Fin p.T) :
    CoordinatorLocalArmChoice.SourceTimeValid payload cutoff t ↔
      sourceTimeConditions payload.sigma cutoff t := by
  constructor
  · intro h
    exact ⟨h.source_round_pos, h.source_round_le_horizon, h.cutoff_pos,
      h.cutoff_le_terminal, by simpa [CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.sourceRound] using h.assignment_started,
      by simpa [CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.cutoffRound] using h.cutoff_after_start⟩
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      by simpa [CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.sourceRound] using h.2.2.2.2.1,
      by simpa [CoordinatorLocalArmChoice.assignmentStart,
        CoordinatorLocalArmChoice.cutoffRound] using h.2.2.2.2.2⟩

/-- The local choice-input predicate is Borel on the existing payload and
real-valued complement-weight fibers. Every finite arm check is a Borel
inequality, and the source-time checks factor through finite coordinates. -/
theorem measurable_choiceInputsValid :
    Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T =>
      choiceInputsValidBit x.1 x.2) := by
  classical
  have htimeData : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      Fin p.T => (x.1.payload.sigma, (x.1.cutoff, x.2))) := by
    exact (measurable_choiceViewSigma.comp measurable_fst).prodMk
      ((measurable_choiceTimeViewCutoff.comp measurable_fst).prodMk measurable_snd)
  let timeCheck : Fin p.T × (Option (CoordinatorLocalArmChoice.Cutoff p) × Fin p.T) → Bool :=
    fun z => decide (sourceTimeConditions z.1 z.2.1 z.2.2)
  have htimeCheck : Measurable timeCheck := measurable_of_countable _
  let timeValue : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T → Bool :=
    fun x => timeCheck (x.1.payload.sigma, (x.1.cutoff, x.2))
  have htimeBool : Measurable timeValue := htimeCheck.comp htimeData
  have hvalidSet : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      Fin p.T | CoordinatorLocalArmChoice.ChoiceInputsValid x.1.payload
        x.1.cutoff x.2 x.1.complementWeights} := by
    have hvalidSet_eq : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
        CoordinatorLocalArmChoice.ChoiceInputsValid x.1.payload
          x.1.cutoff x.2 x.1.complementWeights} =
        {x | CoordinatorLocalArmChoice.SourceTimeValid x.1.payload x.1.cutoff x.2 ∧
          ∀ a : Fin p.K, a ∈ fastArmFinset x.1.payload.slowSet →
            0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
                choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a} := by
      ext x
      exact choiceInputsValid_iff_envelope x.1 x.2
    rw [hvalidSet_eq]
    have htime : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
        Fin p.T | CoordinatorLocalArmChoice.SourceTimeValid x.1.payload
          x.1.cutoff x.2} := by
      have hfiber : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
          CoordinatorLocalArmChoice.SourceTimeValid x.1.payload x.1.cutoff x.2} =
          timeValue ⁻¹' {true} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change CoordinatorLocalArmChoice.SourceTimeValid x.1.payload x.1.cutoff x.2 ↔
          decide (sourceTimeConditions x.1.payload.sigma x.1.cutoff x.2) = true
        rw [sourceTimeValid_iff_conditions]
        simp
      rw [hfiber]
      exact htimeBool (measurableSet_singleton true)
    have henvelope : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
        Fin p.T | ∀ a : Fin p.K, a ∈ fastArmFinset x.1.payload.slowSet →
          0 < choiceTimeViewWeightVector x.1 a ∧
            x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
            choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a} := by
      have hfast : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
          ∀ a : Fin p.K, a ∈ fastArmFinset x.1.payload.slowSet →
            0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
                choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a} =
          {x | ∀ j : FastArm x.1.payload.slowSet,
            0 < x.1.complementWeights j ∧ x.1.payload.anchor j.1 ≤
              x.1.complementWeights j ∧ x.1.complementWeights j ≤
                2 * x.1.payload.anchor j.1} := by
        ext x
        constructor
        · intro h j
          have hgood := h j.1 j.2
          have hj : choiceTimeViewWeightVector x.1 j.1 = x.1.complementWeights j := by
            simp [choiceTimeViewWeightVector, j.2]
          simpa only [hj] using hgood
        · intro h a ha
          have hgood := h ⟨a, ha⟩
          have ha' : choiceTimeViewWeightVector x.1 a = x.1.complementWeights ⟨a, ha⟩ := by
            simp [choiceTimeViewWeightVector, ha]
          simpa only [ha'] using hgood
      have hforall : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
          ∀ j : FastArm x.1.payload.slowSet,
            0 < x.1.complementWeights j ∧ x.1.payload.anchor j.1 ≤
              x.1.complementWeights j ∧ x.1.complementWeights j ≤
                2 * x.1.payload.anchor j.1} =
          ⋂ a : Fin p.K, {x | a ∉ fastArmFinset x.1.payload.slowSet ∨
            (0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
              choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a)} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        constructor
        · intro h a
          by_cases ha : a ∈ fastArmFinset x.1.payload.slowSet
          · right
            simpa [choiceTimeViewWeightVector, ha] using h ⟨a, ha⟩
          · exact Or.inl ha
        · intro h j
          rcases h j.1 with hnot | hgood
          · exact False.elim (hnot j.2)
          · simpa [choiceTimeViewWeightVector, j.2] using hgood
      rw [hfast, hforall]
      apply MeasurableSet.iInter
      intro a
      have hmem : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
          Fin p.T | a ∈ fastArmFinset x.1.payload.slowSet} := by
        have hslow : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
            Fin p.T => x.1.payload.slowSet.1) := measurable_choiceViewSlowSet.comp measurable_fst
        have hbit : Measurable (fun x : Finset (Fin p.K) => decide (a ∉ x)) :=
          measurable_of_countable _
        let fastBit : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T → Bool :=
          fun x => decide (a ∉ x.1.payload.slowSet.1)
        have hfastBit : Measurable fastBit := hbit.comp hslow
        have hset : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
            a ∈ fastArmFinset x.1.payload.slowSet} = fastBit ⁻¹' {true} := by
          ext x
          simp [fastBit, fastArmFinset]
        rw [hset]
        exact hfastBit (measurableSet_singleton true)
      have hweight : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
          Fin p.T => choiceTimeViewWeightVector x.1 a) :=
        measurable_choiceViewWeightAt a |>.comp measurable_fst
      have hanchor : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
          Fin p.T => x.1.payload.anchor a) :=
        ((measurable_pi_apply a).comp measurable_choiceViewAnchor).comp measurable_fst
      have hpos : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
          Fin p.T | 0 < choiceTimeViewWeightVector x.1 a} :=
        measurableSet_lt measurable_const hweight
      have hlow : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
          Fin p.T | x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a} :=
        measurableSet_le hanchor hweight
      have hhigh : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
          Fin p.T | choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a} := by
        exact measurableSet_le hweight
          (measurable_const.mul hanchor)
      have hgood := hpos.inter (hlow.inter hhigh)
      let fastMembers : Set (ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T) :=
        {x | a ∈ fastArmFinset x.1.payload.slowSet}
      have hallowed : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
          a ∉ fastArmFinset x.1.payload.slowSet ∨
            (0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
              choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a)} =
          fastMembersᶜ ∪ (fastMembers ∩
            {x | 0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
              choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a}) := by
        ext x
        change (a ∉ fastArmFinset x.1.payload.slowSet ∨
            (0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
              choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a)) ↔
          (a ∉ fastArmFinset x.1.payload.slowSet ∨
            (a ∈ fastArmFinset x.1.payload.slowSet ∧
              0 < choiceTimeViewWeightVector x.1 a ∧
              x.1.payload.anchor a ≤ choiceTimeViewWeightVector x.1 a ∧
              choiceTimeViewWeightVector x.1 a ≤ 2 * x.1.payload.anchor a))
        constructor
        · rintro (hnot | hgood)
          · exact Or.inl hnot
          · by_cases hfast : a ∈ fastArmFinset x.1.payload.slowSet
            · exact Or.inr ⟨hfast, hgood⟩
            · exact Or.inl hfast
        · rintro (hnot | ⟨_, hgood⟩)
          · exact Or.inl hnot
          · exact Or.inr hgood
      rw [hallowed]
      exact hmem.compl.union (hmem.inter hgood)
    exact htime.inter henvelope
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro b
  cases b
  · have hset : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
        choiceInputsValidBit x.1 x.2 = false} =
        {x | CoordinatorLocalArmChoice.ChoiceInputsValid x.1.payload
          x.1.cutoff x.2 x.1.complementWeights}ᶜ := by
      ext x
      simp [choiceInputsValidBit]
    rw [hset]
    exact hvalidSet.compl
  · have hset : {x : ReferenceDownReception.ChoiceTimeView p rate.eta × Fin p.T |
        choiceInputsValidBit x.1 x.2 = true} =
        {x | CoordinatorLocalArmChoice.ChoiceInputsValid x.1.payload
          x.1.cutoff x.2 x.1.complementWeights} := by
      ext x
      simp [choiceInputsValidBit]
    rw [hset]
    exact hvalidSet

private theorem measurable_expectedDownFlatWordSome (i : Fin (p.m - 1)) :
    Measurable (expectedDownFlatWordSome (p := p) (rate := rate) i) := by
  classical
  let validBit : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) → Bool := fun x => choiceInputsValidBit x.1 x.2.2
  have hvalid : Measurable validBit := by
    exact (measurable_choiceInputsValid (p := p) (rate := rate)).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  let downBit : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) → Bool := fun x =>
        FollowerDownJointMeasurability.downSelectionBit i x.2.1 x.2.2
  have hdown : Measurable downBit :=
    measurable_choiceViewDownSelection i |>.comp measurable_snd
  let pendingBit : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) → Bool := fun x => decide (i ∈ x.1.pendingAtChoice)
  have hpending : Measurable pendingBit := by
    have hp : Measurable (fun view : ReferenceDownReception.ChoiceTimeView p rate.eta =>
        view.pendingAtChoice) :=
      measurable_fst.comp (measurable_snd.comp measurable_choiceTimeViewObservation)
    exact (measurable_of_finite fun P : Finset (Follower p.m) => decide (i ∈ P)).comp
      (hp.comp measurable_fst)
  let branchBit : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) → Bool := fun x => downBit x && pendingBit x
  have hbranch : Measurable branchBit :=
    (measurable_of_finite fun b : Bool × Bool => b.1 && b.2).comp
      (hdown.prodMk hpending)
  let conditionBit : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) → Bool := fun x => validBit x && branchBit x
  have hcondition : Measurable conditionBit :=
    (measurable_of_finite fun b : Bool × Bool => b.1 && b.2).comp
      (hvalid.prodMk hbranch)
  have hword : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) =>
      CoordinatorLocalArmChoice.storedDownFlatWord x.1.payload i) :=
    measurable_choiceViewStoredDownFlatWord i |>.comp measurable_fst
  have hconditionSet : MeasurableSet {x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) | conditionBit x = true} :=
    hcondition (measurableSet_singleton true)
  have hsome : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) => some
        (CoordinatorLocalArmChoice.storedDownFlatWord x.1.payload i)) :=
    (measurable_of_countable (fun word : AffineChannelLaw.Word
      (AffineBatchDecoder.width p) => some word)).comp hword
  exact Measurable.ite hconditionSet hsome measurable_const

private def optionProductMeasurableEquiv (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] :
    (Option α × β) ≃ᵐ (α × β) ⊕ (PUnit × β) := by
  let e : Option α ≃ᵐ α ⊕ PUnit := {
    toEquiv := Equiv.optionEquivSumPUnit α
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      exact measurable_id
  }
  exact (MeasurableEquiv.prodCongr e (MeasurableEquiv.refl β)).trans
    (MeasurableEquiv.sumProdDistrib α PUnit β)

/-- Joint Borel measurability of the exact expected DOWN word, including the
existing optional choice view and its real-valued complement-weight fibers. -/
theorem measurable_expectedDownFlatWord (i : Fin (p.m - 1)) :
    Measurable (fun x : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
        (CompleteRow p × Fin p.T) =>
      ReferenceDownReception.expectedDownFlatWord x.1 i x.2.1 x.2.2) := by
  let e := optionProductMeasurableEquiv
    (ReferenceDownReception.ChoiceTimeView p rate.eta)
    (CompleteRow p × Fin p.T)
  have hsome : Measurable (fun x : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompleteRow p × Fin p.T) => expectedDownFlatWordSome i x) :=
    measurable_expectedDownFlatWordSome i
  have hsum : Measurable (fun z :
      (ReferenceDownReception.ChoiceTimeView p rate.eta ×
        (CompleteRow p × Fin p.T)) ⊕
      (PUnit × (CompleteRow p × Fin p.T)) =>
      Sum.elim (fun y => expectedDownFlatWordSome i y) (fun _ => none) z) :=
    measurable_fun_sum hsome measurable_const
  have heq : (fun x : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      (CompleteRow p × Fin p.T) =>
      ReferenceDownReception.expectedDownFlatWord x.1 i x.2.1 x.2.2) =
      fun x => Sum.elim (fun y => expectedDownFlatWordSome i y) (fun _ => none) (e x) := by
    funext x
    cases x with
    | mk view rest =>
      cases view with
      | none =>
          have he : e (none, rest) = Sum.inr (PUnit.unit, rest) := by
            change Equiv.sumProdDistrib _ _ _
              (Equiv.prodCongr (Equiv.optionEquivSumPUnit _)
                (Equiv.refl _) (none, rest)) = _
            simp [Equiv.sumProdDistrib, Equiv.prodCongr, Equiv.optionEquivSumPUnit]
          rw [he]
          rfl
      | some view =>
          have he : e (some view, rest) = Sum.inl (view, rest) := by
            change Equiv.sumProdDistrib _ _ _
              (Equiv.prodCongr (Equiv.optionEquivSumPUnit _)
                (Equiv.refl _) (some view, rest)) = _
            simp [Equiv.sumProdDistrib, Equiv.prodCongr, Equiv.optionEquivSumPUnit]
          rw [he]
          exact expectedDownFlatWord_eq_expectedSome view i rest.1 rest.2
  rw [heq]
  exact hsum.comp e.measurable_toFun

/-- Rebuild the exact current decoder input from J's sufficient round read.
This is a pure local input constructor; it carries no history or recovery
assumption. -/
def currentRoundInputOfDownRoundRead (p : Parameters)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (read : FollowerDownJointMeasurability.DownRoundRead p) :
    AffineBatchDecoder.RoundInput (AffineBatchDecoder.width p) :=
  ⟨read.selected, decide (state.status = .unoccupied), read.sample,
    (FollowerDownMeasurability.feedbackAtGrid p read.feedbackIndex).val.val⟩

/-- The actual decoder result is a function of J's literal sufficient
round-read coordinates and the existing decoder batch. -/
def decodeStepOfDownRoundRead (p : Parameters) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (read : FollowerDownJointMeasurability.DownRoundRead p) :=
  AffineBatchDecoder.decodeStep p
    (ActiveFollowerDownAcceptance.currentInputExtension p
      (currentRoundInputOfDownRoundRead p state read)) state.downBatch read.time

instance decodeStepOutputMeasurableSpace (p : Parameters) :
    MeasurableSpace
      (AffineBatchDecoder.State p.T (AffineBatchDecoder.width p) ×
        Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) := ⊤

/-- The read-based decoder is measurable because J's round-read carrier is
countable and discrete. -/
theorem measurable_decodeStepOfDownRoundRead (p : Parameters) (rate : RateInput p)
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (decodeStepOfDownRoundRead p rate state) :=
  measurable_of_countable _

/-- Pointwise exactness of the round-read decoder factorization, including
the current grid feedback carried by the read. -/
theorem currentDecodeStep_eq_decodeStepOfDownRoundRead
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedbackIndex : Fin (D p + 1))
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    ActiveFollowerDownAcceptance.currentDecodeStep p i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state =
      decodeStepOfDownRoundRead p rate state
        ⟨t, feedbackIndex,
          FollowerDownJointMeasurability.downSelectionBit i row t,
          (row.2 t).2 (0, i)⟩ := by
  classical
  have hinput : ActiveFollowerDownAcceptance.currentRoundInput p i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state =
      currentRoundInputOfDownRoundRead p state
        ⟨t, feedbackIndex,
          FollowerDownJointMeasurability.downSelectionBit i row t,
          (row.2 t).2 (0, i)⟩ := by
    change AffineBatchDecoder.RoundInput.mk
        (decide (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i))
        (decide (state.status = .unoccupied)) ((row.2 t).2 (0, i))
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex).val.val =
      AffineBatchDecoder.RoundInput.mk
        (FollowerDownJointMeasurability.downSelectionBit i row t)
        (decide (state.status = .unoccupied)) ((row.2 t).2 (0, i))
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex).val.val
    simp only [AffineBatchDecoder.RoundInput.mk.injEq]
    have hselected : decide
        (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) =
        FollowerDownJointMeasurability.downSelectionBit i row t := by
      unfold FollowerDownJointMeasurability.downSelectionBit
      by_cases hpair : PublicDiscreteDraws.slotDraw (row.2 t).1 =
          PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i
      · simp [hpair, ActiveFollowerDownAcceptance.downSelected]
      · simp [hpair, ActiveFollowerDownAcceptance.downSelected]
    exact ⟨hselected, trivial, trivial, trivial⟩
  change AffineBatchDecoder.decodeStep p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (ActiveFollowerDownAcceptance.currentRoundInput p i row t
          (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state))
      state.downBatch t =
    AffineBatchDecoder.decodeStep p
      (ActiveFollowerDownAcceptance.currentInputExtension p
        (currentRoundInputOfDownRoundRead p state
          ⟨t, feedbackIndex, FollowerDownJointMeasurability.downSelectionBit i row t,
            (row.2 t).2 (0, i)⟩)) state.downBatch t
  rw [hinput]

/-- Joint measurability of the real decoder output when row, time, grid
feedback, and every saved scalar vary over J's original input carrier. -/
theorem measurable_currentDecodeStep_joint (i : Fin (p.m - 1))
    (rate : RateInput p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (fun x : FollowerDownJointMeasurability.DownJointInput p state.buffer.length =>
      ActiveFollowerDownAcceptance.currentDecodeStep p i
        (FollowerDownJointMeasurability.jointRow x)
        (FollowerDownJointMeasurability.jointTime x)
        (FollowerDownMeasurability.feedbackAtGrid p
          (FollowerDownJointMeasurability.jointFeedbackIndex x)) rate
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerDownJointMeasurability.jointValues x))) := by
  have hread : Measurable (fun x : FollowerDownJointMeasurability.DownJointInput p
      state.buffer.length => FollowerDownJointMeasurability.downRoundRead i x) :=
    FollowerDownJointMeasurability.measurable_downRoundRead i state.buffer.length
  have hfactor := (measurable_decodeStepOfDownRoundRead p rate state).comp hread
  have heq : (fun x : FollowerDownJointMeasurability.DownJointInput p state.buffer.length =>
      ActiveFollowerDownAcceptance.currentDecodeStep p i
        (FollowerDownJointMeasurability.jointRow x)
        (FollowerDownJointMeasurability.jointTime x)
        (FollowerDownMeasurability.feedbackAtGrid p
          (FollowerDownJointMeasurability.jointFeedbackIndex x)) rate
        (FollowerDownMeasurability.adaptedInputState rate state
          (FollowerDownJointMeasurability.jointValues x))) =
      fun x => decodeStepOfDownRoundRead p rate state
        (FollowerDownJointMeasurability.downRoundRead i x) := by
    funext x
    exact currentDecodeStep_eq_decodeStepOfDownRoundRead i
      (FollowerDownJointMeasurability.jointRow x)
      (FollowerDownJointMeasurability.jointTime x)
      (FollowerDownJointMeasurability.jointFeedbackIndex x)
      (FollowerDownMeasurability.adaptedInputState rate state
        (FollowerDownJointMeasurability.jointValues x))
  rw [heq]
  exact hfactor


/-- The exact countable observation of `referenceDownCut`. The Prop-valued
ordinary acceptance diagnostic is represented by its equivalent Boolean
decision; the local-result code omits only the continuous buffer, which is
supplied unchanged to reconstruction. -/
structure ReferenceDownCutCode (p : Parameters) (rate : RateInput p) where
  outcome : FollowerDownMeasurability.LocalDownResultCode p rate
  expectedWord : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  raw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  filteredRaw : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  ordinaryParse : Option (OrdinaryMessageCodec.DownRecord
    (ReferencePrelaunchFollower.codecParams p rate.eta))
  ordinaryAcceptance : Bool
  rawComparison : Option Bool
  deriving Countable

instance referenceDownCutCodeMeasurableSpace (p : Parameters) (rate : RateInput p) :
    MeasurableSpace (ReferenceDownCutCode p rate) := ⊤

/-- Encode every countable field of the reference cut, leaving its original
buffer as the continuous reconstruction argument. -/
def encodeReferenceDownCutCode (result : ReferenceDownCutOutput p rate) :
    ReferenceDownCutCode p rate := by
  classical
  exact ⟨FollowerDownMeasurability.encodeLocalDownResult result.outcome,
    result.expectedWord, result.raw, result.filteredRaw, result.ordinaryParse,
    decide result.ordinaryAcceptance, result.rawComparison⟩

/-- Reconstruct the exact reference-cut output from its countable code and
the original local buffer. -/
def reconstructReferenceDownCutCode (code : ReferenceDownCutCode p rate)
    (originalBuffer : List (SparseCalendarRecord p.K)) : ReferenceDownCutOutput p rate :=
  ⟨FollowerDownMeasurability.reconstructLocalDownResult code.outcome originalBuffer,
    code.expectedWord, code.raw, code.filteredRaw, code.ordinaryParse,
    decide (code.ordinaryAcceptance = true), code.rawComparison⟩

/-- The code and original buffer exactly reconstruct every field of the cut
whenever the literal local-buffer behavior holds. -/
theorem reconstruct_encodeReferenceDownCutCode
    (originalBuffer : List (SparseCalendarRecord p.K))
    (result : ReferenceDownCutOutput p rate)
    (hbuffer : FollowerDownMeasurability.localDownBufferBehavior
      originalBuffer result.outcome) :
    reconstructReferenceDownCutCode (encodeReferenceDownCutCode result) originalBuffer =
      result := by
  cases result with
  | mk outcome expected raw filtered parsed accepted comparison =>
      have hresult := FollowerDownMeasurability.reconstruct_encodeLocalDownResult
        originalBuffer outcome hbuffer
      unfold reconstructReferenceDownCutCode encodeReferenceDownCutCode
      simp only [hresult, decide_eq_true_eq]

/-- The reference cut preserves the complete original buffer on every branch;
acceptance clears it exactly as the source protocol prescribes. -/
theorem referenceDownCut_localDownBufferBehavior
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedback : Observation p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    FollowerDownMeasurability.localDownBufferBehavior state.buffer
      (ReferenceDownReception.referenceDownCut p view i row t feedback rate state).outcome := by
  classical
  let cut := ReferenceDownReception.referenceDownCut p view i row t feedback rate state
  by_cases hmismatch : ReferenceDownReception.rawMismatch cut
  · have hbranches :
        ActiveFollowerDownAcceptance.downSelected p i row t ∧
          state.status = .unoccupied ∧
          ActiveFollowerDownAcceptance.registerInputDomain p rate state ∧
          ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch ∧
          ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer := by
      dsimp only [cut, ReferenceDownReception.rawMismatch] at hmismatch
      unfold ReferenceDownReception.referenceDownCut at hmismatch
      split_ifs at hmismatch
      all_goals simp_all
    rcases hbranches with ⟨hselected, hstatus, hregisters, hbatch, hbuffer⟩
    have hmismatch' : ReferenceDownReception.rawMismatch
        (ReferenceDownReception.referenceDownCut p view i row t feedback rate state) := by
      simpa only [cut] using hmismatch
    have hpreserved := ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
      view i row t feedback rate state hselected hstatus hregisters hbatch hbuffer hmismatch'
    rw [hpreserved.1]
    simp [FollowerDownMeasurability.localDownBufferBehavior]
  · have hmatch : ¬ ReferenceDownReception.rawMismatch
        (ReferenceDownReception.referenceDownCut p view i row t feedback rate state) := by
      simpa only [cut] using hmismatch
    have hordinary : cut.outcome = ActiveFollowerDownAcceptance.downTransition
        p i row t feedback rate state := by
      apply ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
      exact hmatch
    rw [hordinary]
    exact FollowerDownMeasurability.downTransition_bufferBehavior i row t feedback rate state

/-- The expected-word diagnostic is preserved literally on every cut branch,
including unselected rounds and every input failure. -/
theorem referenceDownCut_expectedWord_eq
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedback : Observation p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    (ReferenceDownReception.referenceDownCut p view i row t feedback rate state).expectedWord =
      ReferenceDownReception.expectedDownFlatWord view i row t := by
  classical
  unfold ReferenceDownReception.referenceDownCut
  dsimp only
  repeat' split_ifs
  all_goals rfl

/-- The cut's expected-word field is jointly Borel in its existing optional
choice view, complete row, finite time, and any fixed grid feedback/state.
This theorem only exposes that diagnostic; the full cut-code measurability
theorem remains a separate obligation. -/
theorem measurable_referenceDownCut_expectedWord
    (i : Fin (p.m - 1)) (feedbackIndex : Fin (D p + 1))
    (state : ReferencePrelaunchFollower.State p rate.eta) :
    Measurable (fun x : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
        (CompleteRow p × Fin p.T) =>
      (ReferenceDownReception.referenceDownCut p x.1 i x.2.1 x.2.2
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).expectedWord) := by
  have heq : (fun x : Option (ReferenceDownReception.ChoiceTimeView p rate.eta) ×
      (CompleteRow p × Fin p.T) =>
      (ReferenceDownReception.referenceDownCut p x.1 i x.2.1 x.2.2
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).expectedWord) =
      fun x => ReferenceDownReception.expectedDownFlatWord x.1 i x.2.1 x.2.2 := by
    funext x
    exact referenceDownCut_expectedWord_eq x.1 i x.2.1 x.2.2
      (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) state
  rw [heq]
  exact measurable_expectedDownFlatWord i

/-- Expected words depend on the current selected DOWN-to-pending branch,
not on any other row coordinate. The literal coordinator choice is checked
against the same payload and current time on both sides. -/
private theorem expectedDownFlatWord_eq_of_downSelected_eq
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row row' : CompleteRow p) (t : Fin p.T)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row t =
      ActiveFollowerDownAcceptance.downSelected p i row' t) :
    ReferenceDownReception.expectedDownFlatWord (some view) i row t =
      ReferenceDownReception.expectedDownFlatWord (some view) i row' t := by
  have hbranch : ReferenceDownReception.selectedDownSenderBranch view i row t ↔
      ReferenceDownReception.selectedDownSenderBranch view i row' t := by
    unfold ReferenceDownReception.selectedDownSenderBranch
    unfold ActiveFollowerDownAcceptance.downSelected at hselected
    constructor
    · rintro ⟨hslot, hfollow, hpending⟩
      have hpair : (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) ↔
        (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) :=
        Iff.of_eq hselected
      rcases hpair.mp ⟨hslot, hfollow⟩ with ⟨hslot', hfollow'⟩
      exact ⟨hslot', hfollow', hpending⟩
    · rintro ⟨hslot, hfollow, hpending⟩
      have hpair : (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) ↔
        (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.downSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) :=
        Iff.of_eq hselected
      exact ⟨(hpair.mpr ⟨hslot, hfollow⟩).1,
        (hpair.mpr ⟨hslot, hfollow⟩).2, hpending⟩
  by_cases hleft : ReferenceDownReception.selectedDownSenderBranch view i row t
  · have hright : ReferenceDownReception.selectedDownSenderBranch view i row' t :=
      hbranch.mp hleft
    have hchoiceLeft := coordinatorArmChoice_ne_none_iff_choiceInputsValid_of_selectedDown
      view i row t hleft
    have hchoiceRight := coordinatorArmChoice_ne_none_iff_choiceInputsValid_of_selectedDown
      view i row' t hright
    by_cases hv : CoordinatorLocalArmChoice.ChoiceInputsValid view.payload
        view.cutoff t view.complementWeights
    · have hnleft := hchoiceLeft.mpr hv
      have hnright := hchoiceRight.mpr hv
      simp [ReferenceDownReception.expectedDownFlatWord, hnleft, hnright, hleft, hright]
    · have hnleft : ¬ CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
          view.pendingAtChoice view.cutoff t view.complementWeights row ≠ none := by
        exact fun h => hv (hchoiceLeft.mp h)
      have hnright : ¬ CoordinatorLocalArmChoice.coordinatorArmChoice view.payload
          view.pendingAtChoice view.cutoff t view.complementWeights row' ≠ none := by
        exact fun h => hv (hchoiceRight.mp h)
      simp [ReferenceDownReception.expectedDownFlatWord, hnleft, hnright, hleft, hright]
  · have hright : ¬ ReferenceDownReception.selectedDownSenderBranch view i row' t := by
      intro h
      exact hleft (hbranch.mpr h)
    simp [ReferenceDownReception.expectedDownFlatWord, hleft, hright]

/-- On the literal raw-mismatch branch, changing row proposal coordinates
while preserving the current decoder input and local receiver state leaves
the complete lossless cut code unchanged. No recovery-success condition is
used: the rejected outcome and advanced decoder batch come from R's mismatch
preservation theorem. -/
theorem referenceDownCut_mismatch_locality
    (view : ReferenceDownReception.ChoiceTimeView p rate.eta)
    (i : Fin (p.m - 1)) (row row' : CompleteRow p) (t : Fin p.T)
    (feedbackIndex : Fin (D p + 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (hselected : ActiveFollowerDownAcceptance.downSelected p i row t)
    (hstatus : state.status = .unoccupied)
    (hregisters : ActiveFollowerDownAcceptance.registerInputDomain p rate state)
    (hbatch : ActiveFollowerDownAcceptance.decoderInputDomain p state.downBatch)
    (hbuffer : ActiveFollowerDownAcceptance.bufferInputDomain p state.buffer)
    (hcurrent : ActiveFollowerDownAcceptance.currentRoundInput p i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state =
      ActiveFollowerDownAcceptance.currentRoundInput p i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state)
    (hmismatch : ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state))
    (hmismatch' : ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state)) :
    encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p (some view) i row t
          (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state) =
      encodeReferenceDownCutCode
        (ReferenceDownReception.referenceDownCut p (some view) i row' t
          (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state) := by
  classical
  have hselected' : ActiveFollowerDownAcceptance.downSelected p i row' t := by
    have hc := congrArg AffineBatchDecoder.RoundInput.selected hcurrent
    change decide (PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i) =
      decide (PublicDiscreteDraws.slotDraw (row'.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) at hc
    have hleft : PublicDiscreteDraws.slotDraw (row.2 t).1 = PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i := by
      simpa only [ActiveFollowerDownAcceptance.downSelected] using hselected
    have hright : decide (PublicDiscreteDraws.slotDraw (row'.2 t).1 =
        PublicDiscreteDraws.downSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K (row'.2 t).1 = i) = true :=
      hc.symm.trans (decide_eq_true hleft)
    have hright' := of_decide_eq_true hright
    simpa only [ActiveFollowerDownAcceptance.downSelected] using hright'
  have hselectedEq : ActiveFollowerDownAcceptance.downSelected p i row t =
      ActiveFollowerDownAcceptance.downSelected p i row' t := propext ⟨
        fun _ => hselected', fun _ => hselected⟩
  have hdecode := FollowerDownMeasurability.currentDecodeStep_eq_of_currentRoundInput_eq
    i row row' t (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex)
    (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state hcurrent
  have hexpected := expectedDownFlatWord_eq_of_downSelected_eq view i row row' t hselectedEq
  have hleft := ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
    (some view) i row t (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex)
    rate state hselected hstatus hregisters hbatch hbuffer hmismatch
  have hright := ReferenceDownReception.referenceDownCut_raw_mismatch_preserves
    (some view) i row' t (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex)
    rate state hselected' hstatus hregisters hbatch hbuffer hmismatch'
  rcases hleft with ⟨houtcome, hraw, hfiltered, hparse, haccepted, _⟩
  rcases hright with ⟨houtcome', hraw', hfiltered', hparse', haccepted', _⟩
  have houtcomeCode :
      FollowerDownMeasurability.encodeLocalDownResult
          (ReferenceDownReception.referenceDownCut p (some view) i row t
            (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).outcome =
        FollowerDownMeasurability.encodeLocalDownResult
          (ReferenceDownReception.referenceDownCut p (some view) i row' t
            (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).outcome := by
    rw [houtcome, houtcome', hdecode]
  have hrawCode :
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).raw =
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).raw := by
    rw [hraw, hraw', hdecode]
  have hfilteredCode :
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).filteredRaw =
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).filteredRaw := by
    rw [hfiltered, hfiltered']
  have hparseCode :
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).ordinaryParse =
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).ordinaryParse := by
    rw [hparse, hparse', hdecode]
  have hacceptedCode :
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).ordinaryAcceptance =
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).ordinaryAcceptance := by
    rw [haccepted, haccepted', hdecode]
  have hmismatchCode :
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).rawComparison =
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).rawComparison := by
    simpa only [ReferenceDownReception.rawMismatch] using
      (hmismatch.trans hmismatch'.symm)
  have hexpectedCode :
      (ReferenceDownReception.referenceDownCut p (some view) i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).expectedWord =
      (ReferenceDownReception.referenceDownCut p (some view) i row' t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate state).expectedWord := by
    rw [referenceDownCut_expectedWord_eq, referenceDownCut_expectedWord_eq]
    exact hexpected
  simp only [encodeReferenceDownCutCode]
  simp only [houtcomeCode, hexpectedCode, hrawCode, hfilteredCode, hparseCode,
    hacceptedCode, hmismatchCode]

/-- If the literal reference comparison has no mismatch, its complete local
outcome code is exactly the accepted ordinary DOWN outcome code on the same
row, time, grid feedback, and varying saved observations. This consumes R's
accepted ordinary-outcome equality and J's existing ordinary code API. -/
theorem referenceDownCut_outcomeCode_eq_downTransitionCode_of_no_raw_mismatch
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedbackIndex : Fin (D p + 1))
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (values : FollowerDownMeasurability.SavedScalarFamily state.buffer.length)
    (hmatch : ¬ ReferenceDownReception.rawMismatch
      (ReferenceDownReception.referenceDownCut p view i row t
        (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate
        (FollowerDownMeasurability.adaptedInputState rate state values))) :
    FollowerDownMeasurability.encodeLocalDownResult
        (ReferenceDownReception.referenceDownCut p view i row t
          (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate
          (FollowerDownMeasurability.adaptedInputState rate state values)).outcome =
      FollowerDownJointMeasurability.downTransitionCodeAt i rate state
        (⟨((row, t), feedbackIndex), values⟩ :
          FollowerDownJointMeasurability.DownJointInput p state.buffer.length) := by
  have hordinary :=
    ReferenceDownReception.referenceDownCut_outcome_eq_downTransition_of_no_raw_mismatch
      view i row t (FollowerDownMeasurability.feedbackAtGrid p feedbackIndex) rate
      (FollowerDownMeasurability.adaptedInputState rate state values) hmatch
  rw [hordinary]
  rfl

/-- Reconstruction of the actual reference cut has no conditional input:
the buffer behavior premise is discharged from the literal cut branches. -/
theorem reconstruct_encode_referenceDownCut
    (view : Option (ReferenceDownReception.ChoiceTimeView p rate.eta))
    (i : Fin (p.m - 1)) (row : CompleteRow p) (t : Fin p.T)
    (feedback : Observation p) (state : ReferencePrelaunchFollower.State p rate.eta) :
    reconstructReferenceDownCutCode
        (encodeReferenceDownCutCode
          (ReferenceDownReception.referenceDownCut p view i row t feedback rate state))
        state.buffer =
      ReferenceDownReception.referenceDownCut p view i row t feedback rate state := by
  exact reconstruct_encodeReferenceDownCutCode state.buffer _
    (referenceDownCut_localDownBufferBehavior view i row t feedback state)

end Bandits.Support.ReferenceDownReceptionMeasurability

end
