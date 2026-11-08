/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActiveFollowerArmChoice
public import Bandits.Support.ActiveFollowerQueueOperation

/-!
# Measurability of one actual active follower arm choice

The arm branches follow `sources/zip4/manuscript/05_binary_transport.tex:90-124`.
The checked local UP offer uses the carried registers as specified in
`sources/zip4/manuscript/06_interruptions.tex:108-114`. Inputs retain the
complete continuous slice and every affine sample from
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.

These results concern one fixed incoming follower state and one active stage.
They do not construct a physical run or evolving state, and do not establish
history-conditional freshness, stopping-time claims, or a source regret result.
-/

public section

noncomputable section

namespace Bandits.Support.FollowerActionMeasurability

open MeasureTheory
open Bandits.Support.ActiveFollowerArmChoice
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.ActiveRoundActions
open Bandits.Support.AffineChannelLaw
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PrelaunchBufferRecovery
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower

/-- The finite arm-or-no-arm output uses its canonical discrete measurable
space. The continuous input keeps its existing product measurable space. -/
instance optionArmMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (Fin p.K)) := ⊤

private theorem measurable_slotInput (p : ConstructorDimensions.Parameters) :
    Measurable (fun x : TimeControl p => slotDraw x.1) :=
  measurable_slotDraw.comp measurable_fst

private theorem measurable_selectedInput (p : ConstructorDimensions.Parameters) :
    Measurable (fun x : TimeControl p =>
      selectedFollowerDraw p.two_le_m p.m_lt_K x.1) :=
  (measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp measurable_fst

private theorem measurable_tupleInput (p : ConstructorDimensions.Parameters) :
    Measurable (fun x : TimeControl p =>
      OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1) :=
  (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp measurable_fst

private theorem measurable_pilotInput (p : ConstructorDimensions.Parameters)
    (i : Fin (p.m - 1)) :
    Measurable (fun x : TimeControl p =>
      pilotDraw (ConstructorDimensions.K_pos p)
        (followerPlayer p.two_le_m i) x.1) :=
  (measurable_pilotDraw (ConstructorDimensions.K_pos p)
    (followerPlayer p.two_le_m i)).comp measurable_fst

private theorem measurable_tupleFollowerInput (p : ConstructorDimensions.Parameters)
    (i : Fin (p.m - 1)) :
    Measurable (fun x : TimeControl p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
        (followerPlayer p.two_le_m i)) := by
  exact (measurable_pi_apply (followerPlayer p.two_le_m i)).comp
    (measurable_subtype_coe.comp (measurable_tupleInput p))

private theorem measurable_tupleCoordinatorInput
    (p : ConstructorDimensions.Parameters) :
    Measurable (fun x : TimeControl p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
        (coordinator p.two_le_m)) := by
  exact (measurable_pi_apply (coordinator p.two_le_m)).comp
    (measurable_subtype_coe.comp (measurable_tupleInput p))

private theorem measurable_tupleSelectedFollowerInput
    (p : ConstructorDimensions.Parameters) :
    Measurable (fun x : TimeControl p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
        (followerPlayer p.two_le_m
          (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))) := by
  have htuple : Measurable (fun x : TimeControl p =>
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val) :=
    measurable_subtype_coe.comp (measurable_tupleInput p)
  have hselected : Measurable (fun x : TimeControl p =>
      followerPlayer p.two_le_m
        (selectedFollowerDraw p.two_le_m p.m_lt_K x.1)) := by
    exact (Measurable.of_discrete (f := followerPlayer p.two_le_m)).comp
      (measurable_selectedInput p)
  have hargs : Measurable (fun x : TimeControl p =>
      ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val,
        followerPlayer p.two_le_m
          (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))) :=
    htuple.prodMk hselected
  exact (Measurable.of_discrete
    (f := fun z : (Fin p.m → Fin p.K) × Fin p.m => z.1 z.2)).comp hargs

private theorem measurable_offeredUpBitInput {p : ConstructorDimensions.Parameters}
    {eta : LearningRate} (i : Fin (p.m - 1))
    (M : UpRecord (codecParams p eta)) :
    Measurable (fun x : TimeControl p => offeredUpBit eta x i M) := by
  have hsample : Measurable (fun x : TimeControl p => x.2 (1, i)) :=
    (measurable_pi_apply (1, i)).comp measurable_snd
  have hhash : Measurable (fun sample : Sample (B p) =>
      affineHash sample (offeredUpWord eta M)) := Measurable.of_discrete
  exact hhash.comp (by simpa only [offeredUpBit] using hsample)

private theorem measurable_someArm {p : ConstructorDimensions.Parameters}
    {α : Type*} [MeasurableSpace α] (f : α → Fin p.K) (hf : Measurable f) :
    Measurable (fun x => (some (f x) : Option (Fin p.K))) := by
  exact (Measurable.of_discrete (f := fun a : Fin p.K =>
    (some a : Option (Fin p.K)))).comp hf

private theorem measurable_sendArmInput {p : ConstructorDimensions.Parameters}
    (fbit : TimeControl p → Bit) (hsend : Measurable fbit)
    (fsend freceive : TimeControl p → Fin p.K)
    (hfsend : Measurable fsend) (hfreceive : Measurable freceive) :
    Measurable (fun x => sendArm (fbit x) (fsend x) (freceive x)) := by
  have hargs : Measurable (fun x =>
      (fbit x, (fsend x, freceive x))) :=
    hsend.prodMk (hfsend.prodMk hfreceive)
  exact (Measurable.of_discrete
    (f := fun z : Bit × (Fin p.K × Fin p.K) => sendArm z.1 z.2.1 z.2.2)).comp hargs

/-- The existing literal follower operator is measurable in its genuine
current `TimeControl`: the original full scalar slice and full affine-sample
family retain their product measurable spaces. The optional payload is a fixed
admissible UP record, not a row-dependent oracle. -/
theorem measurable_followerArmChoiceCore
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta))) :
    Measurable (fun x : TimeControl p =>
      followerArmChoiceCore s x i offeredUp) := by
  classical
  have hslot := measurable_slotInput p
  have hselected := measurable_selectedInput p
  have htupleFollower := measurable_tupleFollowerInput p i
  have htupleCoordinator := measurable_tupleCoordinatorInput p
  have htupleSelected := measurable_tupleSelectedFollowerInput p
  have hpilot := measurable_pilotInput p i
  have hslotData : MeasurableSet {x : TimeControl p | slotDraw x.1 = dataSlot} :=
    measurableSet_eq_fun hslot measurable_const
  have hslotUp : MeasurableSet {x : TimeControl p | slotDraw x.1 = upSlot} :=
    measurableSet_eq_fun hslot measurable_const
  have hslotDown : MeasurableSet {x : TimeControl p | slotDraw x.1 = downSlot} :=
    measurableSet_eq_fun hslot measurable_const
  have hselectedSelf : MeasurableSet {x : TimeControl p |
      selectedFollowerDraw p.two_le_m p.m_lt_K x.1 = i} :=
    measurableSet_eq_fun hselected measurable_const
  have hselectedUp : MeasurableSet {x : TimeControl p |
      slotDraw x.1 = upSlot ∧
        selectedFollowerDraw p.two_le_m p.m_lt_K x.1 = i} :=
    hslotUp.inter hselectedSelf
  by_cases hunoccupied : s.status = .unoccupied
  · simp only [followerArmChoiceCore, hunoccupied, ite_true]
    cases hoff : offeredUp with
    | none =>
        simpa only [hoff] using
          Measurable.ite hslotData
            (measurable_someArm (fun x : TimeControl p =>
              pilotDraw (ConstructorDimensions.K_pos p)
                (followerPlayer p.two_le_m i) x.1) hpilot)
            (Measurable.ite hselectedUp measurable_const
              (measurable_someArm (fun x : TimeControl p =>
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                  (followerPlayer p.two_le_m i)) htupleFollower))
    | some M =>
        by_cases hvalid : upStateDomain s ∧ offeredUpMatchesState s M
        · have hbit := measurable_offeredUpBitInput i M
          have hsend := measurable_sendArmInput
            (fun x : TimeControl p => offeredUpBit eta x i M) hbit
            (fun x => (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (followerPlayer p.two_le_m i))
            (fun x => (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
              (coordinator p.two_le_m)) htupleFollower htupleCoordinator
          have hupArm : Measurable (fun x : TimeControl p =>
              some (sendArm (offeredUpBit eta x i M)
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                  (followerPlayer p.two_le_m i))
                ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                  (coordinator p.two_le_m)))) := measurable_someArm _ hsend
          simpa [followerArmChoiceCore, hunoccupied, hoff, hvalid] using
            Measurable.ite hslotData
              (measurable_someArm (fun x : TimeControl p =>
                pilotDraw (ConstructorDimensions.K_pos p)
                  (followerPlayer p.two_le_m i) x.1) hpilot)
              (Measurable.ite hselectedUp hupArm
                (measurable_someArm (fun x : TimeControl p =>
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                    (followerPlayer p.two_le_m i)) htupleFollower))
        · have hupArm : Measurable (fun _ : TimeControl p =>
              (none : Option (Fin p.K))) := measurable_const
          simpa [followerArmChoiceCore, hunoccupied, hoff, hvalid] using
            Measurable.ite hslotData
              (measurable_someArm (fun x : TimeControl p =>
                pilotDraw (ConstructorDimensions.K_pos p)
                  (followerPlayer p.two_le_m i) x.1) hpilot)
              (Measurable.ite hselectedUp hupArm
                (measurable_someArm (fun x : TimeControl p =>
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                    (followerPlayer p.two_le_m i)) htupleFollower))
  · cases hdown : s.lastDown with
    | none =>
        simp [followerArmChoiceCore, hunoccupied, hdown]
    | some M =>
        by_cases hreleased : s.status = .released
        · simp [followerArmChoiceCore, hdown, hreleased]
        ·
          have hescape : MeasurableSet {x : TimeControl p |
              slotDraw x.1 = upSlot ∧
                selectedFollowerDraw p.two_le_m p.m_lt_K x.1 = i ∧
                (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                  (coordinator p.two_le_m) = downAuxiliaryArm eta M} := by
            exact hslotUp.inter (hselectedSelf.inter
              (measurableSet_eq_fun htupleCoordinator measurable_const))
          have hdownCollision : MeasurableSet {x : TimeControl p |
              slotDraw x.1 = downSlot ∧
                downArm eta M =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                    (followerPlayer p.two_le_m
                      (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))} := by
            exact hslotDown.inter
              (measurableSet_eq_fun measurable_const htupleSelected)
          have hupCollision : MeasurableSet {x : TimeControl p |
              slotDraw x.1 = upSlot ∧
                downArm eta M =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                    (coordinator p.two_le_m)} := by
            exact hslotUp.inter
              (measurableSet_eq_fun measurable_const htupleCoordinator)
          have hcollisions : MeasurableSet {x : TimeControl p |
              (slotDraw x.1 = downSlot ∧
                downArm eta M =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                    (followerPlayer p.two_le_m
                      (selectedFollowerDraw p.two_le_m p.m_lt_K x.1))) ∨
              (slotDraw x.1 = upSlot ∧
                downArm eta M =
                  (OrderedTupleSampler.sample p.two_le_m p.m_lt_K x.1).val
                    (coordinator p.two_le_m))} := by
            rw [Set.ofPred_or]
            exact hdownCollision.union hupCollision
          have hdownArm : Measurable (fun _ : TimeControl p =>
              (some (downArm eta M) : Option (Fin p.K))) := measurable_const
          have hauxArm : Measurable (fun _ : TimeControl p =>
              (some (downAuxiliaryArm eta M) : Option (Fin p.K))) := measurable_const
          simpa [followerArmChoiceCore, hunoccupied, hdown, hreleased] using
            Measurable.ite hslotData hdownArm
              (Measurable.ite hescape hauxArm
                (Measurable.ite hcollisions hauxArm hdownArm))

/-- Translate the actual checked offer branches into the already accepted
follower arm operator. A failed offer remains failure (`none`); this is defined
only for an active stage, so it supplies no inactive or bootstrap default. -/
@[expose] def checkedActiveFollowerArmChoice
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (_hactive : alpha.val ≤ t.val + 1) : Option (Fin p.K) :=
  match checkedUpOffer eta i row alpha t s with
  | .failure => none
  | .noOffer => followerArmChoice s row t i none
  | .offer M => followerArmChoice s row t i (some M)

/-- Success in the actual offer constructor records the active selection,
unoccupied local status, whole-state input domain, and UP-record admissibility.
-/
theorem checkedUpOffer_offer_conditions
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : Activation p) (t : Fin p.T) (s : State p eta)
    (M : UpRecord (codecParams p eta))
    (h : checkedUpOffer eta i row alpha t s = .offer M) :
    stateInputDomain s ∧ selectedUpRound i row alpha t ∧
      s.status = .unoccupied ∧
      upAdmissible (codecParams p eta) (upOfferFields s) := by
  classical
  unfold checkedUpOffer at h
  by_cases hdomain : stateInputDomain s
  · rw [dite_eq_left hdomain] at h
    by_cases hselected : selectedUpRound i row alpha t ∧ s.status = .unoccupied
    · rw [dite_eq_left hselected] at h
      by_cases hadmissible : upAdmissible (codecParams p eta) (upOfferFields s)
      · rw [dite_eq_left hadmissible] at h
        exact ⟨hdomain, hselected.1, hselected.2, hadmissible⟩
      · rw [dite_eq_right hadmissible] at h
        cases h
    · rw [dite_eq_right hselected] at h
      cases h
  · rw [dite_eq_right hdomain] at h
    cases h

/-- A successful actual UP offer contains precisely the four carried local
registers, so the existing arm operator's field check holds directly. -/
theorem checkedUpOffer_offer_matches_state
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (i : Fin (p.m - 1)) (row : CompletePublicTable.CompleteRow p)
    (alpha : Activation p) (t : Fin p.T) (s : State p eta)
    (M : UpRecord (codecParams p eta))
    (h : checkedUpOffer eta i row alpha t s = .offer M) :
    offeredUpMatchesState s M := by
  have hfields := checkedUpOffer_fields eta i row alpha t s M h
  unfold offeredUpMatchesState
  rw [hfields]
  simp [upOfferFields]

private theorem stateInputDomain_upStateDomain
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (h : stateInputDomain s) : upStateDomain s := by
  unfold stateInputDomain at h
  unfold upStateDomain
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- On its successful actual branch, the adapter feeds the actual checked
record into the accepted arm operator. The returned arm is exactly the
operator's current `(UP, i)` affine-hash SendArm with its sampled tuple. -/
theorem checkedActiveFollowerArmChoice_offer
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (M : UpRecord (codecParams p eta))
    (h : checkedUpOffer eta i row alpha t s = .offer M) :
    checkedActiveFollowerArmChoice s i row alpha t hactive =
      some (sendArm (offeredUpBit eta (row.2 t) i M)
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
          (followerPlayer p.two_le_m i))
        ((OrderedTupleSampler.sample p.two_le_m p.m_lt_K (row.2 t).1).val
          (coordinator p.two_le_m))) := by
  have hconditions := checkedUpOffer_offer_conditions i row alpha t s M h
  rcases hconditions with ⟨hdomain, htarget, hstatus, _hadmissible⟩
  rcases htarget with ⟨_hactive, hslot, hselected⟩
  have hvalid : upStateDomain s ∧ offeredUpMatchesState s M :=
    ⟨stateInputDomain_upStateDomain s hdomain,
      checkedUpOffer_offer_matches_state i row alpha t s M h⟩
  simp only [checkedActiveFollowerArmChoice, h]
  rw [followerArmChoice_eq_core]
  exact followerArmChoiceCore_unoccupied_selected_up s (row.2 t) i M
    hstatus hslot hselected hvalid

/-- The explicit failure branch is preserved as no arm. -/
theorem checkedActiveFollowerArmChoice_failure
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (h : checkedUpOffer eta i row alpha t s = .failure) :
    checkedActiveFollowerArmChoice s i row alpha t hactive = none := by
  simp [checkedActiveFollowerArmChoice, h]

/-- The explicit no-offer branch passes no payload to the accepted arm
operator; its DATA, tuple, and accepted DOWN branches remain unchanged. -/
theorem checkedActiveFollowerArmChoice_noOffer
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (h : checkedUpOffer eta i row alpha t s = .noOffer) :
    checkedActiveFollowerArmChoice s i row alpha t hactive =
      followerArmChoice s row t i none := by
  simp [checkedActiveFollowerArmChoice, h]

/-- The explicit offer branch passes exactly the record returned by the
checked operation to the accepted arm operator. -/
theorem checkedActiveFollowerArmChoice_offer_branch
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (M : UpRecord (codecParams p eta))
    (h : checkedUpOffer eta i row alpha t s = .offer M) :
    checkedActiveFollowerArmChoice s i row alpha t hactive =
      followerArmChoice s row t i (some M) := by
  simp [checkedActiveFollowerArmChoice, h]

private theorem measurable_currentCompleteRowControl
    (p : ConstructorDimensions.Parameters) (t : Fin p.T) :
    Measurable (fun row : CompletePublicTable.CompleteRow p => row.2 t) :=
  (measurable_controlAt t).comp measurable_snd

/-- Row-facing measurability of the existing follower arm operator for any
fixed admissible optional offer. The forward-bit component is projected away;
only this complete row's learning/control component is used. -/
theorem measurable_followerArmChoice
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (t : Fin p.T) (i : Fin (p.m - 1))
    (offeredUp : Option (UpRecord (codecParams p eta))) :
    Measurable (fun row : CompletePublicTable.CompleteRow p =>
      followerArmChoice s row t i offeredUp) := by
  change Measurable (fun row : CompletePublicTable.CompleteRow p =>
    followerArmChoiceCore s (row.2 t) i offeredUp)
  exact (measurable_followerArmChoiceCore s i offeredUp).comp
    (measurable_currentCompleteRowControl p t)

private theorem measurable_selectedUpRound_of_active
    {p : ConstructorDimensions.Parameters} (i : Fin (p.m - 1))
    (alpha : Activation p) (t : Fin p.T)
    (hactive : alpha.val ≤ t.val + 1) :
    MeasurableSet {row : CompletePublicTable.CompleteRow p |
      selectedUpRound i row alpha t} := by
  have hcurrent := measurable_currentCompleteRowControl p t
  have hslot : Measurable (fun row : CompletePublicTable.CompleteRow p =>
      slotDraw (row.2 t).1) :=
    (measurable_slotInput p).comp hcurrent
  have hselected : Measurable (fun row : CompletePublicTable.CompleteRow p =>
      selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1) :=
    (measurable_selectedInput p).comp hcurrent
  have hup : MeasurableSet {row : CompletePublicTable.CompleteRow p |
      slotDraw (row.2 t).1 = upSlot} :=
    measurableSet_eq_fun hslot
      (measurable_const : Measurable fun _ : CompletePublicTable.CompleteRow p => upSlot)
  have hself : MeasurableSet {row : CompletePublicTable.CompleteRow p |
      selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i} :=
    measurableSet_eq_fun hselected
      (measurable_const : Measurable fun _ : CompletePublicTable.CompleteRow p => i)
  have hsets : MeasurableSet
      ({row : CompletePublicTable.CompleteRow p |
        slotDraw (row.2 t).1 = upSlot} ∩
       {row : CompletePublicTable.CompleteRow p |
        selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i}) :=
    hup.inter hself
  have hEq : {row : CompletePublicTable.CompleteRow p |
      selectedUpRound i row alpha t} =
      {row : CompletePublicTable.CompleteRow p |
        slotDraw (row.2 t).1 = upSlot} ∩
       {row : CompletePublicTable.CompleteRow p |
        selectedFollowerDraw p.two_le_m p.m_lt_K (row.2 t).1 = i} := by
    ext row
    simp [selectedUpRound, hactive]
  rw [hEq]
  exact hsets

/-- The actual checked-offer composition is measurable as a function of one
complete public row. The active-stage proof is explicit; each of the checked
failure, no-offer, and actual-offer branches is handled separately. -/
theorem measurable_checkedActiveFollowerArmChoice
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (alpha : Activation p) (t : Fin p.T)
    (hactive : alpha.val ≤ t.val + 1) :
    Measurable (fun row : CompletePublicTable.CompleteRow p =>
      checkedActiveFollowerArmChoice s i row alpha t hactive) := by
  classical
  have hnone : Measurable (fun _ : CompletePublicTable.CompleteRow p =>
      (none : Option (Fin p.K))) := measurable_const
  by_cases hdomain : stateInputDomain s
  · by_cases hstatus : s.status = .unoccupied
    · have hselectedSet := measurable_selectedUpRound_of_active i alpha t hactive
      by_cases hadmissible : upAdmissible (codecParams p eta) (upOfferFields s)
      · let M : UpRecord (codecParams p eta) := ⟨upOfferFields s, hadmissible⟩
        have hsome := measurable_followerArmChoice s t i (some M)
        have hnoOffer := measurable_followerArmChoice s t i none
        have hformula :
            (fun row : CompletePublicTable.CompleteRow p =>
              checkedActiveFollowerArmChoice s i row alpha t hactive) =
            fun row => if selectedUpRound i row alpha t then
              followerArmChoice s row t i (some M)
            else followerArmChoice s row t i none := by
          funext row
          by_cases hselected : selectedUpRound i row alpha t
          · simp [checkedActiveFollowerArmChoice, checkedUpOffer,
              hdomain, hstatus, hadmissible, hselected, M]
          · simp [checkedActiveFollowerArmChoice, checkedUpOffer,
              hdomain, hstatus, hselected]
        rw [hformula]
        exact Measurable.ite hselectedSet hsome hnoOffer
      · have hnoOffer := measurable_followerArmChoice s t i none
        have hformula :
            (fun row : CompletePublicTable.CompleteRow p =>
              checkedActiveFollowerArmChoice s i row alpha t hactive) =
            fun row => if selectedUpRound i row alpha t then none
              else followerArmChoice s row t i none := by
          funext row
          by_cases hselected : selectedUpRound i row alpha t
          · simp [checkedActiveFollowerArmChoice, checkedUpOffer,
              hdomain, hstatus, hadmissible, hselected]
          · simp [checkedActiveFollowerArmChoice, checkedUpOffer,
              hdomain, hstatus, hselected]
        rw [hformula]
        exact Measurable.ite hselectedSet hnone hnoOffer
    · have hnoOffer := measurable_followerArmChoice s t i none
      have hformula :
          (fun row : CompletePublicTable.CompleteRow p =>
            checkedActiveFollowerArmChoice s i row alpha t hactive) =
          fun row => followerArmChoice s row t i none := by
        funext row
        simp [checkedActiveFollowerArmChoice, checkedUpOffer, hdomain, hstatus]
      rw [hformula]
      exact hnoOffer
  · have hformula :
        (fun row : CompletePublicTable.CompleteRow p =>
          checkedActiveFollowerArmChoice s i row alpha t hactive) =
        fun _ => none := by
      funext row
      simp [checkedActiveFollowerArmChoice, checkedUpOffer, hdomain]
    rw [hformula]
    exact hnone

/-- The checked composition factors through exactly the current control
`row.2 t`. Forward bits and every other calendar time are outside this active
stage's input reads. -/
theorem checkedActiveFollowerArmChoice_eq_of_same_current_control
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row₁ row₂ : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (hcontrol : row₁.2 t = row₂.2 t) :
    checkedActiveFollowerArmChoice s i row₁ alpha t hactive =
      checkedActiveFollowerArmChoice s i row₂ alpha t hactive := by
  have hoff : checkedUpOffer eta i row₁ alpha t s =
      checkedUpOffer eta i row₂ alpha t s := by
    unfold checkedUpOffer selectedUpRound
    rw [hcontrol]
  unfold checkedActiveFollowerArmChoice
  rw [hoff]
  cases hresult : checkedUpOffer eta i row₂ alpha t s <;>
    simp [followerArmChoice, hcontrol]

/-- If this row is outside the selected-unoccupied-UP branch, all changes to
the current affine-sample family are irrelevant. This reuses the accepted arm
operator's local noninterference result. -/
theorem checkedActiveFollowerArmChoice_eq_of_same_slice_when_up_unused
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row₁ row₂ : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (hslice : (row₁.2 t).1 = (row₂.2 t).1)
    (hunused : ¬ (s.status = .unoccupied ∧
      slotDraw (row₁.2 t).1 = upSlot ∧
      selectedFollowerDraw p.two_le_m p.m_lt_K (row₁.2 t).1 = i)) :
    checkedActiveFollowerArmChoice s i row₁ alpha t hactive =
      checkedActiveFollowerArmChoice s i row₂ alpha t hactive := by
  have hoff : checkedUpOffer eta i row₁ alpha t s =
      checkedUpOffer eta i row₂ alpha t s := by
    unfold checkedUpOffer selectedUpRound
    rw [hslice]
  unfold checkedActiveFollowerArmChoice
  rw [hoff]
  cases hresult : checkedUpOffer eta i row₂ alpha t s with
  | failure => simp
  | noOffer =>
      rw [followerArmChoice_eq_core, followerArmChoice_eq_core]
      exact followerArmChoiceCore_eq_of_same_control_when_up_unused
        s (row₁.2 t) (row₂.2 t) i none hslice hunused
  | offer M =>
      have hconditions := checkedUpOffer_offer_conditions i row₂ alpha t s M hresult
      rcases hconditions with ⟨_, hselected, hstatus, _⟩
      rcases hselected with ⟨_, hslot, hself⟩
      have hslot₁ : slotDraw (row₁.2 t).1 = upSlot := by
        rw [hslice]
        exact hslot
      have hself₁ :
          selectedFollowerDraw p.two_le_m p.m_lt_K (row₁.2 t).1 = i := by
        rw [hslice]
        exact hself
      exact False.elim (hunused ⟨hstatus, hslot₁, hself₁⟩)

/-- On a selected active UP offer, the complete continuous input can vary in
all other channels while retaining the current slice and this follower's
`(UP, i)` sample; the accepted operator's locality theorem controls the arm. -/
theorem checkedActiveFollowerArmChoice_eq_of_same_slice_and_up_sample
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (row₁ row₂ : CompletePublicTable.CompleteRow p) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (hslice : (row₁.2 t).1 = (row₂.2 t).1)
    (hsample : (row₁.2 t).2 (1, i) = (row₂.2 t).2 (1, i)) :
    checkedActiveFollowerArmChoice s i row₁ alpha t hactive =
      checkedActiveFollowerArmChoice s i row₂ alpha t hactive := by
  have hoff : checkedUpOffer eta i row₁ alpha t s =
      checkedUpOffer eta i row₂ alpha t s := by
    unfold checkedUpOffer selectedUpRound
    rw [hslice]
  unfold checkedActiveFollowerArmChoice
  rw [hoff]
  cases hresult : checkedUpOffer eta i row₂ alpha t s with
  | failure => simp
  | noOffer =>
      rw [followerArmChoice_eq_core, followerArmChoice_eq_core]
      exact followerArmChoiceCore_eq_of_same_control_and_up_sample
        s (row₁.2 t) (row₂.2 t) i none hslice hsample
  | offer M =>
      rw [followerArmChoice_eq_core, followerArmChoice_eq_core]
      exact followerArmChoiceCore_eq_of_same_control_and_up_sample
        s (row₁.2 t) (row₂.2 t) i (some M) hslice hsample

/-- The same local producer applied to one row of the published complete-row
family. The actual checked offer still receives that selected `CompleteRow`.
-/
@[expose] def checkedActiveFollowerArmChoiceAtRow
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (rows : CompletePublicTable.CompleteRows p)
    (q : Fin (ConstructorDimensions.M p)) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1) : Option (Fin p.K) :=
  checkedActiveFollowerArmChoice s i (rows q) alpha t hactive

/-- Measurability after projecting a complete public-row family to the one
row selected by `q`. -/
theorem measurable_checkedActiveFollowerArmChoiceAtRow
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (q : Fin (ConstructorDimensions.M p)) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1) :
    Measurable (fun rows : CompletePublicTable.CompleteRows p =>
      checkedActiveFollowerArmChoiceAtRow s i rows q alpha t hactive) := by
  change Measurable (fun rows : CompletePublicTable.CompleteRows p =>
    checkedActiveFollowerArmChoice s i (rows q) alpha t hactive)
  exact (measurable_checkedActiveFollowerArmChoice s i alpha t hactive).comp
    (CompletePublicTable.measurable_completeRowProjection p q)

/-- Every other public row, and all noncurrent inputs in the selected row,
are immaterial: equal selected current controls give equal arm results. -/
theorem checkedActiveFollowerArmChoiceAtRow_eq_of_same_current_control
    {p : ConstructorDimensions.Parameters} {eta : LearningRate}
    (s : State p eta) (i : Fin (p.m - 1))
    (rows₁ rows₂ : CompletePublicTable.CompleteRows p)
    (q : Fin (ConstructorDimensions.M p)) (alpha : Activation p)
    (t : Fin p.T) (hactive : alpha.val ≤ t.val + 1)
    (hcontrol : (rows₁ q).2 t = (rows₂ q).2 t) :
    checkedActiveFollowerArmChoiceAtRow s i rows₁ q alpha t hactive =
      checkedActiveFollowerArmChoiceAtRow s i rows₂ q alpha t hactive :=
  checkedActiveFollowerArmChoice_eq_of_same_current_control
    s i (rows₁ q) (rows₂ q) alpha t hactive hcontrol

end Bandits.Support.FollowerActionMeasurability

end
