/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceUpReception
public import Bandits.Support.CoordinatorUpMeasurability
public import Bandits.Support.FollowerPrepareJointMeasurability
public import Bandits.Support.FollowerVaryingActivationMeasurability
public import Bandits.Support.FollowerObservationStageMeasurabilityRepair

/-!
# Measurability of reference UP reception

This module lifts the reference-only current-offer filter and the coordinator's
actual UP receiver over the full separate local inputs. The prepared offer is
computed by the accepted follower `prepare` output, including its lossless
continuous carried state. The only state reads used to determine the offer are
its countable registers and timestamp/pilot skeleton; saved scalar coordinates
remain in their original fibers.

Sources: `sources/zip4/manuscript/06_interruptions.tex:3-5,270-283` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14,60-84`.
These are local measurability results only. They assert no chronology,
provenance, authenticity, history law, or manuscript theorem closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceUpReceptionMeasurability

abbrev Parameters := ConstructorDimensions.Parameters

open MeasureTheory
open Bandits.Support.ActiveFollowerDownAcceptance
open Bandits.Support.ActiveFollowerQueueOperation
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AffineChannelLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorUpMeasurability
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.DeclaredFollowerLocalRound
open Bandits.Support.FollowerDownJointMeasurability
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.FollowerObservationStageMeasurabilityRepair
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerVaryingActivationMeasurability
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ReferenceUpReception
open Bandits.Support.SparseCalendarReplay

variable {p : ConstructorDimensions.Parameters}

abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev IncomingConfiguration := FollowerPrepareJointMeasurability.IncomingConfiguration
abbrev CarriedState := FollowerObservationStageMeasurabilityRepair.CarriedState
abbrev FollowerCarryIndex := FollowerObservationStageMeasurabilityRepair.FollowerCarryIndex

private instance followerCarryIndexMeasurableSpace {p : Parameters}
    (rate : RateInput p) :
    MeasurableSpace (FollowerCarryIndex p rate) := ⊤

private instance followerCarryIndexDiscreteMeasurableSpace {p : Parameters}
    (rate : RateInput p) :
    DiscreteMeasurableSpace (FollowerCarryIndex p rate) := ⟨fun _ => trivial⟩

private theorem measurable_of_sigma_sections {α : Type*} {β : α → Type*}
    [∀ a, MeasurableSpace (β a)] {γ : Type*} [MeasurableSpace γ]
    (f : Sigma β → γ)
    (hf : ∀ a, Measurable (fun x : β a => f ⟨a, x⟩)) : Measurable f := by
  intro s hs
  change MeasurableSet[
    (⨅ a, (inferInstance : MeasurableSpace (β a)).map (Sigma.mk a))]
    {x | f x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro a
  rw [MeasurableSpace.map_def]
  exact hf a hs

private theorem measurable_choose_finite {Ω α β : Type*}
    [MeasurableSpace Ω] [Fintype α] [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    (choice : Ω → α) (family : α → Ω → β)
    (hchoice : Measurable choice) (hfamily : ∀ a, Measurable (family a)) :
    Measurable (fun ω => family (choice ω) ω) := by
  intro s hs
  have hpre : {ω | family (choice ω) ω ∈ s} =
      ⋃ a : α, {ω | choice ω = a} ∩ {ω | family a ω ∈ s} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨choice ω, rfl, h⟩
    · rintro ⟨a, hchoice', hvalue⟩
      rw [hchoice']
      exact hvalue
  change MeasurableSet {ω | family (choice ω) ω ∈ s}
  rw [hpre]
  exact MeasurableSet.iUnion fun a =>
    (measurableSet_eq_fun hchoice measurable_const).inter
      (hfamily a hs)

private theorem measurable_controlAtVariableTime :
    Measurable (fun x : CompletePublicTable.CompleteRow p × Fin p.T =>
      (x.1).2 x.2) := by
  intro s hs
  have hpre : {x : CompletePublicTable.CompleteRow p × Fin p.T |
      (x.1).2 x.2 ∈ s} =
      ⋃ t : Fin p.T,
        {x | x.2 = t} ∩ {x | (x.1).2 t ∈ s} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨x.2, rfl, h⟩
    · rintro ⟨t, ht, h⟩
      rw [ht]
      exact h
  change MeasurableSet {x : CompletePublicTable.CompleteRow p × Fin p.T |
    (x.1).2 x.2 ∈ s}
  rw [hpre]
  exact MeasurableSet.iUnion fun t => by
    have hrow : Measurable (fun x : CompletePublicTable.CompleteRow p => x.2 t) :=
      (ContinuousLearningRows.measurable_controlAt t).comp measurable_snd
    exact (measurableSet_eq_fun measurable_snd measurable_const).inter
      (hrow.comp measurable_fst hs)

private theorem measurable_selectedFollowerIndexAtControl :
    Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      CoordinatorUpMeasurability.selectedFollowerIndex control) := by
  let convert : Fin (PublicDiscreteDraws.followerCount p.m) → Fin (p.m - 1) :=
    fun i => ⟨i.val, by simpa [PublicDiscreteDraws.followerCount] using i.isLt⟩
  have hconvert : Measurable convert := Measurable.of_discrete
  have hdraw : Measurable (fun control : ContinuousLearningRows.TimeControl p =>
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      measurable_fst
  change Measurable (convert ∘ fun control : ContinuousLearningRows.TimeControl p =>
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1)
  exact hconvert.comp hdraw

private theorem measurable_carriedStateIndex (rate : RateInput p) :
    Measurable (fun state : CarriedState p rate => state.1) := by
  apply measurable_of_sigma_sections
  intro index
  exact measurable_const

inductive IncomingOfferIndex (p : Parameters) (rate : RateInput p) where
  | dagger
  | ordinary (index : FollowerCarryIndex p rate)
  deriving Countable

instance incomingOfferIndexMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (IncomingOfferIndex p rate) := ⊤

instance incomingOfferIndexDiscreteMeasurableSpace (p : Parameters)
    (rate : RateInput p) : DiscreteMeasurableSpace (IncomingOfferIndex p rate) :=
  ⟨fun _ => trivial⟩

def incomingOfferIndex {p : Parameters} {rate : RateInput p}
    (incoming : IncomingConfiguration p rate) : IncomingOfferIndex p rate :=
  match FollowerPrepareJointMeasurability.incomingConfigurationToSum incoming with
  | Sum.inl _ => IncomingOfferIndex.dagger
  | Sum.inr data => IncomingOfferIndex.ordinary data.1.1

theorem measurable_incomingOfferIndex {p : Parameters} (rate : RateInput p) :
    Measurable (incomingOfferIndex (p := p) (rate := rate)) := by
  have hindex : Measurable (fun data : CarriedState p rate ×
      FollowerLifecycleMeasurability.LocalMemoryCode p => data.1.1) :=
    (measurable_carriedStateIndex (p := p) rate).comp measurable_fst
  have hright : Measurable (fun data : CarriedState p rate ×
      FollowerLifecycleMeasurability.LocalMemoryCode p =>
        IncomingOfferIndex.ordinary data.1.1 :
        CarriedState p rate × FollowerLifecycleMeasurability.LocalMemoryCode p →
          IncomingOfferIndex p rate) :=
    (Measurable.of_discrete.comp hindex)
  have hsum : Measurable
      (fun data : Unit ⊕ (CarriedState p rate ×
          FollowerLifecycleMeasurability.LocalMemoryCode p) =>
        match data with
        | Sum.inl _ => IncomingOfferIndex.dagger
        | Sum.inr ordinary => IncomingOfferIndex.ordinary ordinary.1.1) :=
    Measurable.sumElim measurable_const hright
  change Measurable (fun incoming : IncomingConfiguration p rate =>
    (fun data : Unit ⊕ (CarriedState p rate ×
        FollowerLifecycleMeasurability.LocalMemoryCode p) =>
      match data with
      | Sum.inl _ => IncomingOfferIndex.dagger
      | Sum.inr ordinary => IncomingOfferIndex.ordinary ordinary.1.1)
      (FollowerPrepareJointMeasurability.incomingConfigurationToSum incoming))
  exact hsum.comp
    (FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate)

private theorem bufferRoundBounds_iff_map {p : Parameters}
    (buffer : List (SparseCalendarReplay.SparseCalendarRecord p.K)) :
    (∀ record ∈ buffer, 1 ≤ record.calendarRound ∧ record.calendarRound ≤ p.T) ↔
      ∀ round ∈ (buffer.map fun record => record.calendarRound),
        1 ≤ round ∧ round ≤ p.T := by
  constructor
  · intro h round hround
    rcases List.mem_map.mp hround with ⟨record, hrecord, rfl⟩
    exact h record hrecord
  · intro h record hrecord
    apply h record.calendarRound
    exact List.mem_map.mpr ⟨record, hrecord, rfl⟩

private theorem stateInputDomain_eq_of_read_eq {p : Parameters} {eta : LearningRate}
    (left right : ReferencePrelaunchFollower.State p eta)
    (hS : left.S = right.S) (hdelta : left.delta = right.delta)
    (hbacklog : left.backlog = right.backlog)
    (hrounds : (left.buffer.map fun record => record.calendarRound) =
      (right.buffer.map fun record => record.calendarRound))
    (hkeys : left.buffer.map ActiveFollowerQueueOperation.bufferKey =
      right.buffer.map ActiveFollowerQueueOperation.bufferKey) :
    ActiveFollowerQueueOperation.stateInputDomain left =
      ActiveFollowerQueueOperation.stateInputDomain right := by
  have hbounds :
      (∀ record ∈ left.buffer, 1 ≤ record.calendarRound ∧
        record.calendarRound ≤ p.T) =
      (∀ record ∈ right.buffer, 1 ≤ record.calendarRound ∧
        record.calendarRound ≤ p.T) := by
    rw [bufferRoundBounds_iff_map, bufferRoundBounds_iff_map, hrounds]
  unfold ActiveFollowerQueueOperation.stateInputDomain
  rw [hS, hdelta, hbacklog, hbounds, hkeys]

private theorem reconstructCarriedState_register_eq {p : Parameters}
    (rate : RateInput p) (index : FollowerCarryIndex p rate)
    (leftValues rightValues : SavedScalarFamily index.2.1) :
    FollowerDownMeasurability.followerStateCode rate
        (reconstructCarriedState index leftValues) =
      FollowerDownMeasurability.followerStateCode rate
        (reconstructCarriedState index rightValues) := by
  simp [reconstructCarriedState, FollowerDownMeasurability.followerStateCode,
    FollowerDownMeasurability.followerStateOfCode]

private theorem reconstructCarriedState_rounds_eq {p : Parameters}
    {rate : RateInput p} (index : FollowerCarryIndex p rate)
    (leftValues rightValues : SavedScalarFamily index.2.1) :
    ((reconstructCarriedState index leftValues).buffer.map
        fun record => record.calendarRound) =
      ((reconstructCarriedState index rightValues).buffer.map
        fun record => record.calendarRound) := by
  simp [reconstructCarriedState, FollowerDownMeasurability.followerStateOfCode,
    FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
  funext j
  rfl

private theorem reconstructCarriedState_keys_eq {p : Parameters}
    {rate : RateInput p} (index : FollowerCarryIndex p rate)
    (leftValues rightValues : SavedScalarFamily index.2.1) :
    ((reconstructCarriedState index leftValues).buffer.map
        ActiveFollowerQueueOperation.bufferKey) =
      ((reconstructCarriedState index rightValues).buffer.map
        ActiveFollowerQueueOperation.bufferKey) := by
  simp only [reconstructCarriedState, FollowerDownMeasurability.followerStateOfCode,
    FollowerDownJointMeasurability.bufferFromSkeletonAndScalars, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  rfl

private theorem checkedUpOffer_reconstruct_eq {p : Parameters}
    (rate : RateInput p) (follower : Fin (p.m - 1))
    (row₁ row₂ : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time₁ time₂ : Fin p.T) (index : FollowerCarryIndex p rate)
    (leftValues rightValues : SavedScalarFamily index.2.1)
    (hselected : ActiveFollowerQueueOperation.selectedUpRound follower row₁
        activation time₁ =
      ActiveFollowerQueueOperation.selectedUpRound follower row₂ activation time₂) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta follower row₁ activation time₁
        (reconstructCarriedState index leftValues) =
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta follower row₂ activation time₂
        (reconstructCarriedState index rightValues) := by
  let left := reconstructCarriedState index leftValues
  let right := reconstructCarriedState index rightValues
  have hcode := reconstructCarriedState_register_eq rate index leftValues rightValues
  have hlast : left.lastDown = right.lastDown := by
    have h := congrArg FollowerDownMeasurability.FollowerStateCode.lastDown hcode
    simpa [left, right, FollowerDownMeasurability.followerStateCode] using h
  have hS : left.S = right.S := by
    have h := congrArg FollowerDownMeasurability.FollowerStateCode.S hcode
    simpa [left, right, FollowerDownMeasurability.followerStateCode] using h
  have hdelta : left.delta = right.delta := by
    have h := congrArg FollowerDownMeasurability.FollowerStateCode.delta hcode
    simpa [left, right, FollowerDownMeasurability.followerStateCode] using h
  have hbacklog : left.backlog = right.backlog := by
    have h := congrArg FollowerDownMeasurability.FollowerStateCode.backlog hcode
    simpa [left, right, FollowerDownMeasurability.followerStateCode] using h
  have hstatusCode : FollowerDownMeasurability.followerStatusCode left.status =
      FollowerDownMeasurability.followerStatusCode right.status := by
    have h := congrArg FollowerDownMeasurability.FollowerStateCode.status hcode
    simpa [left, right, FollowerDownMeasurability.followerStateCode] using h
  have hstatus : left.status = right.status := by
    calc
      left.status = FollowerDownMeasurability.followerStatusOfCode
          (FollowerDownMeasurability.followerStatusCode left.status) :=
        (FollowerDownMeasurability.followerStatusOfCode_code _).symm
      _ = FollowerDownMeasurability.followerStatusOfCode
          (FollowerDownMeasurability.followerStatusCode right.status) :=
        congrArg FollowerDownMeasurability.followerStatusOfCode hstatusCode
      _ = right.status := FollowerDownMeasurability.followerStatusOfCode_code _
  have hdom : ActiveFollowerQueueOperation.stateInputDomain left =
      ActiveFollowerQueueOperation.stateInputDomain right :=
    stateInputDomain_eq_of_read_eq left right hS hdelta hbacklog
      (reconstructCarriedState_rounds_eq index leftValues rightValues)
      (reconstructCarriedState_keys_eq index leftValues rightValues)
  have hfields : ActiveFollowerQueueOperation.upOfferFields left =
      ActiveFollowerQueueOperation.upOfferFields right := by
    simp [ActiveFollowerQueueOperation.upOfferFields,
      ReferencePrelaunchFollower.acceptedStart, hlast, hS, hdelta, hbacklog]
  unfold ActiveFollowerQueueOperation.checkedUpOffer
  rw [hdom, hselected, hstatus, hfields]

private theorem checkedUpOffer_reconstruct_eq_of_index_eq {p : Parameters}
    (rate : RateInput p) (follower : Fin (p.m - 1))
    (row₁ row₂ : CompletePublicTable.CompleteRow p) (activation : Activation p)
    (time₁ time₂ : Fin p.T)
    (index₁ index₂ : FollowerCarryIndex p rate)
    (leftValues : SavedScalarFamily index₁.2.1)
    (rightValues : SavedScalarFamily index₂.2.1)
    (hindex : index₁ = index₂)
    (hselected : ActiveFollowerQueueOperation.selectedUpRound follower row₁
        activation time₁ =
      ActiveFollowerQueueOperation.selectedUpRound follower row₂ activation time₂) :
    ActiveFollowerQueueOperation.checkedUpOffer rate.eta follower row₁ activation time₁
        (reconstructCarriedState index₁ leftValues) =
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta follower row₂ activation time₂
        (reconstructCarriedState index₂ rightValues) := by
  cases hindex
  exact checkedUpOffer_reconstruct_eq rate follower row₁ row₂ activation time₁ time₂
    index₁ leftValues rightValues hselected

structure PreparedOfferRead (p : Parameters) (rate : RateInput p) where
  calendarIndex : Fin p.T
  slot : PublicDiscreteDraws.Slot
  followerDraw : Fin (PublicDiscreteDraws.followerCount p.m)
  incomingIndex : IncomingOfferIndex p rate
  deriving Countable

private instance preparedOfferReadMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (PreparedOfferRead p rate) := ⊤

private instance preparedOfferReadDiscreteMeasurableSpace (p : Parameters)
    (rate : RateInput p) : DiscreteMeasurableSpace (PreparedOfferRead p rate) :=
  ⟨fun _ => trivial⟩

def preparedOutputOfferRead {p : Parameters} (rate : RateInput p)
    {activation : Activation p}
    (output : FollowerPrepareJointMeasurability.PrepareOutput p rate activation) :
    PreparedOfferRead p rate :=
  let row := output.1.1
  let time := output.1.2.1
  let control := row.2 time
  ⟨time, PublicDiscreteDraws.slotDraw control.1,
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K control.1,
    incomingOfferIndex output.2.2⟩

def preparedOutputCurrentOfferWord {p : Parameters} (rate : RateInput p)
    (follower : Fin (p.m - 1)) (activation : Activation p)
    (output : FollowerPrepareJointMeasurability.PrepareOutput p rate activation) :
    Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  let prepared := FollowerPrepareJointMeasurability.preparedRoundOfOutput
    rate follower activation output
  ReferenceUpReception.currentOfferWord rate output.1.1 follower output.1.2.1
    prepared rfl rfl rfl

private theorem measurable_preparedOutputOfferRead {p : Parameters}
    (rate : RateInput p) (activation : Activation p) :
    Measurable (preparedOutputOfferRead rate :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation →
        PreparedOfferRead p rate) := by
  have hrow : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation => x.1.1) :=
    measurable_fst.comp measurable_fst
  have htime : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation => x.1.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)
  have hcontrol : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation =>
        (x.1.1, x.1.2.1)) := hrow.prodMk htime
  have heval : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation =>
        (x.1.1).2 x.1.2.1) :=
    measurable_controlAtVariableTime.comp hcontrol
  have hslot : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation =>
        PublicDiscreteDraws.slotDraw ((x.1.1).2 x.1.2.1).1) :=
    (PublicDiscreteDraws.measurable_slotDraw.comp measurable_fst).comp heval
  have hselected : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation =>
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (((x.1.1).2 x.1.2.1).1)) :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      (measurable_fst.comp heval)
  have hincoming : Measurable (fun x :
      FollowerPrepareJointMeasurability.PrepareOutput p rate activation =>
        incomingOfferIndex x.2.2) :=
    (measurable_incomingOfferIndex rate).comp (measurable_snd.comp measurable_snd)
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro target
  cases target with
  | mk targetTime targetSlot targetFollower targetIncoming =>
      have hset : {x : FollowerPrepareJointMeasurability.PrepareOutput p rate activation |
          preparedOutputOfferRead rate x = ⟨targetTime, targetSlot,
            targetFollower, targetIncoming⟩} = {x |
          x.1.2.1 = targetTime ∧
          PublicDiscreteDraws.slotDraw ((x.1.1).2 x.1.2.1).1 = targetSlot ∧
          PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
            (((x.1.1).2 x.1.2.1).1) = targetFollower ∧
          incomingOfferIndex x.2.2 = targetIncoming} := by
        ext x
        simp [preparedOutputOfferRead]
      rw [hset]
      exact (measurableSet_eq_fun htime measurable_const).inter
        ((measurableSet_eq_fun hslot measurable_const).inter
          ((measurableSet_eq_fun hselected measurable_const).inter
            (measurableSet_eq_fun hincoming measurable_const)))

private theorem preparedOutputCurrentOfferWord_eq_of_offerRead_eq {p : Parameters}
    (rate : RateInput p) (follower : Fin (p.m - 1)) (activation : Activation p)
    (left right : FollowerPrepareJointMeasurability.PrepareOutput p rate activation)
    (hread : preparedOutputOfferRead rate left = preparedOutputOfferRead rate right) :
    preparedOutputCurrentOfferWord rate follower activation left =
      preparedOutputCurrentOfferWord rate follower activation right := by
  have htime := congrArg PreparedOfferRead.calendarIndex hread
  have hslot := congrArg PreparedOfferRead.slot hread
  have hselectedFollower := congrArg PreparedOfferRead.followerDraw hread
  have hincoming := congrArg PreparedOfferRead.incomingIndex hread
  change left.1.2.1 = right.1.2.1 at htime
  change PublicDiscreteDraws.slotDraw ((left.1.1).2 left.1.2.1).1 =
    PublicDiscreteDraws.slotDraw ((right.1.1).2 right.1.2.1).1 at hslot
  change PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (((left.1.1).2 left.1.2.1).1) =
    PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (((right.1.1).2 right.1.2.1).1) at hselectedFollower
  change incomingOfferIndex left.2.2 = incomingOfferIndex right.2.2 at hincoming
  have hselected : ActiveFollowerQueueOperation.selectedUpRound follower
      left.1.1 activation left.1.2.1 =
    ActiveFollowerQueueOperation.selectedUpRound follower
      right.1.1 activation right.1.2.1 := by
    unfold ActiveFollowerQueueOperation.selectedUpRound
    rw [hslot, hselectedFollower, htime]
  cases hleft : left.2.2 with
  | none =>
    cases hright : right.2.2 with
    | none =>
      simp [preparedOutputCurrentOfferWord, ReferenceUpReception.currentOfferWord,
        FollowerPrepareJointMeasurability.preparedRoundOfOutput,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
        hleft, hright]
    | some rightData =>
      simp [incomingOfferIndex, FollowerPrepareJointMeasurability.incomingConfigurationToSum,
        hleft, hright] at hincoming
  | some leftData =>
    cases hright : right.2.2 with
    | none =>
      simp [incomingOfferIndex, FollowerPrepareJointMeasurability.incomingConfigurationToSum,
        hleft, hright] at hincoming
    | some rightData =>
      have hindex : leftData.1.1 = rightData.1.1 := by
        simp [incomingOfferIndex, FollowerPrepareJointMeasurability.incomingConfigurationToSum,
          hleft, hright] at hincoming
        exact hincoming
      have hchecked := checkedUpOffer_reconstruct_eq_of_index_eq rate follower
        left.1.1 right.1.1 activation left.1.2.1 right.1.2.1
        leftData.1.1 rightData.1.1 leftData.1.2 rightData.1.2 hindex hselected
      simp [preparedOutputCurrentOfferWord, ReferenceUpReception.currentOfferWord,
        FollowerPrepareJointMeasurability.preparedRoundOfOutput,
        FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
        hleft, hright, hchecked]

private theorem measurable_preparedOutputCurrentOfferWord {p : Parameters}
    (rate : RateInput p) (follower : Fin (p.m - 1))
    (activation : Activation p) :
    Measurable (preparedOutputCurrentOfferWord rate follower activation) := by
  apply FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    (preparedOutputOfferRead rate)
    (measurable_preparedOutputOfferRead rate activation)
  intro left right hread
  exact preparedOutputCurrentOfferWord_eq_of_offerRead_eq rate follower activation
    left right hread

private theorem measurable_varyingPreparedOutputCurrentOfferWord {p : Parameters}
    (rate : RateInput p) (follower : Fin (p.m - 1)) :
    Measurable (fun output :
      FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate =>
        preparedOutputCurrentOfferWord rate follower output.1 output.2) := by
  apply measurable_of_sigma_sections
  intro activation
  exact measurable_preparedOutputCurrentOfferWord rate follower activation

theorem measurable_preparedOutputCurrentOfferWord_joint {p : Parameters}
    (rate : RateInput p) :
    Measurable (fun x : Fin (p.m - 1) ×
        FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate =>
      preparedOutputCurrentOfferWord rate x.1 x.2.1 x.2.2) := by
  let family : Fin (p.m - 1) →
      (Fin (p.m - 1) ×
        FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate) →
        Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
    fun follower x => preparedOutputCurrentOfferWord rate follower x.2.1 x.2.2
  change Measurable (fun x => family x.1 x)
  exact measurable_choose_finite (fun x => x.1) family measurable_fst
    (fun follower =>
      (measurable_varyingPreparedOutputCurrentOfferWord rate follower).comp
        measurable_snd)

/-! ## Separate-input reception maps -/

abbrev ReceptionLocalInputs (p : Parameters) (rate : RateInput p) :=
  ReferenceUpReception.ReceptionLocalInputs rate

abbrev ReceptionInput (p : Parameters) (rate : RateInput p) :=
  CoordinatorUpReception.ReceptionInput p rate.eta.val rate.eta.property
    (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale

abbrev UpDecoderBank (p : Parameters) := CoordinatorUpReception.UpDecoderBank p

structure FilteredReceptionRead (p : Parameters) (rate : RateInput p) where
  input : ReceptionInput p rate
  expected : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  deriving Countable

private instance filteredReceptionReadMeasurableSpace (p : Parameters)
    (rate : RateInput p) : MeasurableSpace (FilteredReceptionRead p rate) := ⊤

private instance filteredReceptionReadDiscreteMeasurableSpace (p : Parameters)
    (rate : RateInput p) : DiscreteMeasurableSpace (FilteredReceptionRead p rate) :=
  ⟨fun _ => trivial⟩

def receptionInputsOfComponents {p : Parameters} (rate : RateInput p)
    {Ω : Type*} (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p) (calendarIndex : Ω → Fin p.T)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1)) :
    Ω → ReceptionLocalInputs p rate :=
  fun ω => (ledger ω, (bank ω, (calendarIndex ω, feedback ω)))

private theorem measurable_receptionInputAtRow_variableTime {p : Parameters}
    (rate : RateInput p) :
    Measurable (fun x :
      (CompletePublicTable.CompleteRow p × ReceptionLocalInputs p rate) × Fin p.T =>
        ReferenceUpReception.receptionInputAtRow rate x.1.1 x.1.2 x.2) := by
  let family : Fin p.T →
      ((CompletePublicTable.CompleteRow p × ReceptionLocalInputs p rate) × Fin p.T) →
        ReceptionInput p rate :=
    fun t x => ReferenceUpReception.receptionInputAtRow rate x.1.1 x.1.2 t
  change Measurable (fun x => family x.2 x)
  exact measurable_choose_finite (fun x => x.2) family measurable_snd
    (fun t => (CoordinatorUpMeasurability.measurable_receptionInputAtRow
      (p := p) (eta := rate.eta.val) (heta := rate.eta.property)
      (hcap := ReferenceUpReception.sourceCap_forLedger rate)
      (n := rate.n) (hn := rate.n_scale) t).comp measurable_fst)

private theorem measurable_receptionInputAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => ReferenceUpReception.receptionInputAtRow rate
      (row ω) (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
      (calendarIndex ω)) := by
  have hlocal : Measurable (receptionInputsOfComponents rate ledger bank
      calendarIndex feedback) :=
    hledger.prodMk (hbank.prodMk (hcalendar.prodMk hfeedback))
  have hrowLocal : Measurable (fun ω => (row ω,
      receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)) :=
    hrow.prodMk hlocal
  exact measurable_receptionInputAtRow_variableTime rate |>.comp
    (hrowLocal.prodMk hcalendar)

theorem measurable_rawDecoderOutputAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate (row ω)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
        (calendarIndex ω))).2) := by
  have hinput := measurable_receptionInputAtComponents rate row calendarIndex
    ledger bank feedback hrow hcalendar hledger hbank hfeedback
  have hraw : Measurable (fun input : ReceptionInput p rate =>
      (CoordinatorUpReception.decoderTransition input).2) := Measurable.of_discrete
  exact hraw.comp hinput

theorem measurable_rawParsedOutputAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => ReferenceUpReception.rawParsedOutput rate
      (ReferenceUpReception.receptionInputAtRow rate (row ω)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
        (calendarIndex ω))) := by
  have hinput := measurable_receptionInputAtComponents rate row calendarIndex
    ledger bank feedback hrow hcalendar hledger hbank hfeedback
  have hparse : Measurable (ReferenceUpReception.rawParsedOutput rate) :=
    Measurable.of_discrete
  exact hparse.comp hinput

theorem measurable_rawParsedLocalAcceptanceAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback) :
    Measurable (fun ω => ReferenceUpReception.rawParsedLocalAcceptance rate
      (ReferenceUpReception.receptionInputAtRow rate (row ω)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
        (calendarIndex ω))) := by
  have hinput := measurable_receptionInputAtComponents rate row calendarIndex
    ledger bank feedback hrow hcalendar hledger hbank hfeedback
  have haccepted : Measurable
      (ReferenceUpReception.rawParsedLocalAcceptance rate) := Measurable.of_discrete
  exact haccepted.comp hinput

private theorem measurable_varyingPreparedOutput_selectedFollower {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => FollowerVaryingActivationMeasurability.varyingPreparedOutput
      rate (CoordinatorUpMeasurability.selectedFollowerIndex
        ((row ω).2 (calendarIndex ω)))
      (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω))) := by
  have hcontrol : Measurable (fun ω => (row ω, calendarIndex ω)) :=
    hrow.prodMk hcalendar
  have hselected : Measurable (fun ω =>
      CoordinatorUpMeasurability.selectedFollowerIndex
        ((row ω).2 (calendarIndex ω))) :=
    measurable_selectedFollowerIndexAtControl.comp
      (measurable_controlAtVariableTime.comp hcontrol)
  exact measurable_choose_finite
    (fun ω => CoordinatorUpMeasurability.selectedFollowerIndex
      ((row ω).2 (calendarIndex ω)))
    (fun follower ω => FollowerVaryingActivationMeasurability.varyingPreparedOutput
      rate follower (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω)))
    hselected
    (fun follower => measurable_varyingPreparedOutput_atComponents rate follower
      activation incoming row
      calendarIndex hactivation hincoming hrow hcalendar hvalid)

private theorem measurable_preparedOutputCurrentOfferWord_selected {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω => preparedOutputCurrentOfferWord rate
      (CoordinatorUpMeasurability.selectedFollowerIndex
        ((row ω).2 (calendarIndex ω)))
      ((FollowerVaryingActivationMeasurability.varyingPreparedOutput rate
        (CoordinatorUpMeasurability.selectedFollowerIndex
          ((row ω).2 (calendarIndex ω)))
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω))).1)
      ((FollowerVaryingActivationMeasurability.varyingPreparedOutput rate
        (CoordinatorUpMeasurability.selectedFollowerIndex
          ((row ω).2 (calendarIndex ω)))
        (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
          (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω))).2)) := by
  have hselected : Measurable (fun ω =>
      CoordinatorUpMeasurability.selectedFollowerIndex
        ((row ω).2 (calendarIndex ω))) := by
    have hcontrol : Measurable (fun ω => (row ω, calendarIndex ω)) :=
      hrow.prodMk hcalendar
    exact measurable_selectedFollowerIndexAtControl.comp
      (measurable_controlAtVariableTime.comp hcontrol)
  have hprepared := measurable_varyingPreparedOutput_selectedFollower rate
    activation incoming row calendarIndex hactivation hincoming hrow hcalendar hvalid
  have hpair := hselected.prodMk hprepared
  exact (measurable_preparedOutputCurrentOfferWord_joint rate).comp hpair

def currentOfferWordAtComponents {p : Parameters} (rate : RateInput p)
    {Ω : Type*} (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Ω → Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)) :=
  fun ω =>
    let follower := CoordinatorUpMeasurability.selectedFollowerIndex
      ((row ω).2 (calendarIndex ω))
    let output := FollowerVaryingActivationMeasurability.varyingPreparedOutput rate
      follower (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω))
    preparedOutputCurrentOfferWord rate follower output.1 output.2

theorem measurable_currentOfferWordAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (currentOfferWordAtComponents rate activation incoming row
      calendarIndex hvalid) := by
  have hword := measurable_preparedOutputCurrentOfferWord_selected rate
    activation incoming row calendarIndex hactivation hincoming hrow hcalendar hvalid
  change Measurable (fun ω => preparedOutputCurrentOfferWord rate
    (CoordinatorUpMeasurability.selectedFollowerIndex
      ((row ω).2 (calendarIndex ω)))
    (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate
      (CoordinatorUpMeasurability.selectedFollowerIndex
        ((row ω).2 (calendarIndex ω)))
      (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω))).1
    (FollowerVaryingActivationMeasurability.varyingPreparedOutput rate
      (CoordinatorUpMeasurability.selectedFollowerIndex
        ((row ω).2 (calendarIndex ω)))
      (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
        (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω))).2)
  exact hword

def selectedFollowerAtComponents {p : Parameters}
    (row : CompletePublicTable.CompleteRow p) (calendarIndex : Fin p.T) :
    Fin (p.m - 1) :=
  CoordinatorUpMeasurability.selectedFollowerIndex ((row.2 calendarIndex))

def preparedOutputAtComponents {p : Parameters} (rate : RateInput p)
    (activation : Activation p) (incoming : IncomingConfiguration p rate)
    (row : CompletePublicTable.CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1) :
    FollowerVaryingActivationMeasurability.VaryingPreparedOutput p rate :=
  FollowerVaryingActivationMeasurability.varyingPreparedOutput rate
    (selectedFollowerAtComponents row calendarIndex)
    (FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput
      activation incoming row calendarIndex hvalid)

def preparedRoundAtComponents {p : Parameters} (rate : RateInput p)
    (activation : Activation p) (incoming : IncomingConfiguration p rate)
    (row : CompletePublicTable.CompleteRow p) (calendarIndex : Fin p.T)
    (hvalid : activation.val ≤ calendarIndex.val + 1) :
    DeclaredFollowerLocalRound.PreparedRound p rate :=
  FollowerPrepareJointMeasurability.preparedRoundOfOutput rate
    (selectedFollowerAtComponents row calendarIndex)
    (preparedOutputAtComponents rate activation incoming row calendarIndex hvalid).1
    (preparedOutputAtComponents rate activation incoming row calendarIndex hvalid).2

theorem preparedRoundAtComponents_row {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    (incoming : IncomingConfiguration p rate) (row : CompletePublicTable.CompleteRow p)
    (calendarIndex : Fin p.T) (hvalid : activation.val ≤ calendarIndex.val + 1) :
    (preparedRoundAtComponents rate activation incoming row calendarIndex hvalid).row = row := by
  cases incoming <;>
    simp [preparedRoundAtComponents, preparedOutputAtComponents,
      selectedFollowerAtComponents,
      FollowerPrepareJointMeasurability.preparedRoundOfOutput,
      FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerPrepareJointMeasurability.prepareOutputOnInput,
      FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput,
      FollowerPrepareJointMeasurability.prepareInputRow]

theorem preparedRoundAtComponents_time {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    (incoming : IncomingConfiguration p rate) (row : CompletePublicTable.CompleteRow p)
    (calendarIndex : Fin p.T) (hvalid : activation.val ≤ calendarIndex.val + 1) :
    (preparedRoundAtComponents rate activation incoming row calendarIndex hvalid).time =
      calendarIndex := by
  cases incoming <;>
    simp [preparedRoundAtComponents, preparedOutputAtComponents,
      selectedFollowerAtComponents,
      FollowerPrepareJointMeasurability.preparedRoundOfOutput,
      FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerPrepareJointMeasurability.prepareOutputOnInput,
      FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput,
      FollowerPrepareJointMeasurability.prepareInputTime]

theorem preparedRoundAtComponents_follower {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    (incoming : IncomingConfiguration p rate) (row : CompletePublicTable.CompleteRow p)
    (calendarIndex : Fin p.T) (hvalid : activation.val ≤ calendarIndex.val + 1)
    (inputs : ReceptionLocalInputs p rate) :
    (preparedRoundAtComponents rate activation incoming row calendarIndex hvalid).follower =
      (ReferenceUpReception.receptionInputAtRow rate row inputs calendarIndex).selectedFollower := by
  simp [preparedRoundAtComponents, preparedOutputAtComponents,
    selectedFollowerAtComponents,
    FollowerPrepareJointMeasurability.preparedRoundOfOutput,
    FollowerVaryingActivationMeasurability.varyingPreparedOutput,
    FollowerPrepareJointMeasurability.prepareOutputOnInput,
    FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
    FollowerPrepareJointMeasurability.assemblePrepareInput,
    ReferenceUpReception.receptionInputAtRow,
    CoordinatorUpMeasurability.receptionInputAtRow,
    CoordinatorUpMeasurability.receptionInputAtControl]

/-- The countably-read prepared output word is exactly the accepted current-offer
map after the actual row, follower, and local-time equalities are exposed. -/
theorem currentOfferWordAtComponents_eq_reference {p : Parameters}
    (rate : RateInput p) (activation : Activation p)
    (incoming : IncomingConfiguration p rate) (row : CompletePublicTable.CompleteRow p)
    (calendarIndex : Fin p.T) (hvalid : activation.val ≤ calendarIndex.val + 1)
    (inputs : ReceptionLocalInputs p rate) (hinputTime : inputs.2.2.1 = calendarIndex) :
    preparedOutputCurrentOfferWord rate (selectedFollowerAtComponents row calendarIndex)
        activation
        (preparedOutputAtComponents rate activation incoming row calendarIndex hvalid).2 =
      ReferenceUpReception.currentOfferWord rate row
        (ReferenceUpReception.receptionInputAtRow rate row inputs calendarIndex).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate row inputs calendarIndex).time
        (preparedRoundAtComponents rate activation incoming row calendarIndex hvalid)
        (preparedRoundAtComponents_row rate activation incoming row calendarIndex hvalid)
        (preparedRoundAtComponents_follower rate activation incoming row calendarIndex hvalid inputs)
        (by
          calc
            _ = calendarIndex := preparedRoundAtComponents_time rate activation incoming row
              calendarIndex hvalid
            _ = inputs.2.2.1 := hinputTime.symm
            _ = (ReferenceUpReception.receptionInputAtRow rate row inputs calendarIndex).time := by
              rw [ReferenceUpReception.receptionInputAtRow_inputTime]) := by
  cases incoming <;>
    simp [preparedOutputCurrentOfferWord, ReferenceUpReception.currentOfferWord,
      preparedRoundAtComponents, preparedOutputAtComponents,
      selectedFollowerAtComponents,
      FollowerPrepareJointMeasurability.preparedRoundOfOutput,
      FollowerVaryingActivationMeasurability.varyingPreparedOutput,
      FollowerPrepareJointMeasurability.prepareOutputOnInput,
      FollowerVaryingActivationMeasurability.assembleVaryingPrepareInput,
      FollowerPrepareJointMeasurability.assemblePrepareInput,
      FollowerPrepareJointMeasurability.prepareInputRow,
      FollowerPrepareJointMeasurability.prepareInputTime]

/-- Measurability of the actual reference current-offer projection with the
full local input tuple assembled from its separate ledger, bank, time, and grid
feedback maps. -/
theorem measurable_referenceCurrentOfferWordAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (fun ω =>
      ReferenceUpReception.currentOfferWord rate (row ω)
        (ReferenceUpReception.receptionInputAtRow rate (row ω)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
          (calendarIndex ω)).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate (row ω)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
          (calendarIndex ω)).time
        (preparedRoundAtComponents rate (activation ω) (incoming ω) (row ω)
          (calendarIndex ω) (hvalid ω))
        (preparedRoundAtComponents_row rate (activation ω) (incoming ω) (row ω)
          (calendarIndex ω) (hvalid ω))
        (preparedRoundAtComponents_follower rate (activation ω) (incoming ω)
          (row ω) (calendarIndex ω) (hvalid ω)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω))
        (by
          calc
            _ = calendarIndex ω := preparedRoundAtComponents_time rate
              (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω)
            _ = (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω).2.2.1 := rfl
            _ = (ReferenceUpReception.receptionInputAtRow rate (row ω)
                (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
                (calendarIndex ω)).time := by
                  rw [ReferenceUpReception.receptionInputAtRow_inputTime])) := by
  have hhelper := measurable_currentOfferWordAtComponents rate activation incoming row
    calendarIndex hactivation hincoming hrow hcalendar hvalid
  have heq :
      (fun ω => ReferenceUpReception.currentOfferWord rate (row ω)
        (ReferenceUpReception.receptionInputAtRow rate (row ω)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
          (calendarIndex ω)).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate (row ω)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
          (calendarIndex ω)).time
        (preparedRoundAtComponents rate (activation ω) (incoming ω) (row ω)
          (calendarIndex ω) (hvalid ω))
        (preparedRoundAtComponents_row rate (activation ω) (incoming ω) (row ω)
          (calendarIndex ω) (hvalid ω))
        (preparedRoundAtComponents_follower rate (activation ω) (incoming ω)
          (row ω) (calendarIndex ω) (hvalid ω)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω))
        (by
          calc
            _ = calendarIndex ω := preparedRoundAtComponents_time rate
              (activation ω) (incoming ω) (row ω) (calendarIndex ω) (hvalid ω)
            _ = (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω).2.2.1 := rfl
            _ = (ReferenceUpReception.receptionInputAtRow rate (row ω)
                (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω)
                (calendarIndex ω)).time := by
                  rw [ReferenceUpReception.receptionInputAtRow_inputTime])) =
      currentOfferWordAtComponents rate activation incoming row calendarIndex hvalid := by
    funext ω
    exact (currentOfferWordAtComponents_eq_reference rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω)
      (receptionInputsOfComponents rate ledger bank calendarIndex feedback ω) rfl).symm
  rw [heq]
  exact hhelper

private theorem receiveUpFilteredAtRow_eq_of_input_expected_eq {p : Parameters}
    (rate : RateInput p)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (inputs₁ inputs₂ : ReceptionLocalInputs p rate) (time₁ time₂ : Fin p.T)
    (prepared₁ prepared₂ : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow₁ : prepared₁.row = row₁)
    (hfollower₁ : prepared₁.follower =
      (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).selectedFollower)
    (htime₁ : prepared₁.time =
      (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).time)
    (hrow₂ : prepared₂.row = row₂)
    (hfollower₂ : prepared₂.follower =
      (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).selectedFollower)
    (htime₂ : prepared₂.time =
      (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).time)
    (hinputTime₁ : inputs₁.2.2.1 = time₁)
    (hinputTime₂ : inputs₂.2.2.1 = time₂)
    (hinput : ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁ =
      ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂)
    (hexpected : ReferenceUpReception.currentOfferWord rate row₁
        (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).time
        prepared₁ hrow₁ hfollower₁ htime₁ =
      ReferenceUpReception.currentOfferWord rate row₂
        (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).time
        prepared₂ hrow₂ hfollower₂ htime₂) :
    ReferenceUpReception.receiveUpFilteredAtRow rate row₁ inputs₁ time₁
        prepared₁ hrow₁ hfollower₁ htime₁ hinputTime₁ =
      ReferenceUpReception.receiveUpFilteredAtRow rate row₂ inputs₂ time₂
        prepared₂ hrow₂ hfollower₂ htime₂ hinputTime₂ := by
  have hexpected' := by
    simpa only [hinput] using hexpected
  have hcurrent := hexpected'
  simp only [ReferenceUpReception.currentOfferWord] at hcurrent
  simp [ReferenceUpReception.receiveUpFilteredAtRow,
    ReferenceUpReception.currentOfferWord, hinput, hcurrent]

private theorem wrongUniqueAndLocalAcceptanceAtRow_eq_of_input_expected_eq
    {p : Parameters} (rate : RateInput p)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (inputs₁ inputs₂ : ReceptionLocalInputs p rate) (time₁ time₂ : Fin p.T)
    (prepared₁ prepared₂ : DeclaredFollowerLocalRound.PreparedRound p rate)
    (hrow₁ : prepared₁.row = row₁)
    (hfollower₁ : prepared₁.follower =
      (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).selectedFollower)
    (htime₁ : prepared₁.time =
      (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).time)
    (hrow₂ : prepared₂.row = row₂)
    (hfollower₂ : prepared₂.follower =
      (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).selectedFollower)
    (htime₂ : prepared₂.time =
      (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).time)
    (hinputTime₁ : inputs₁.2.2.1 = time₁)
    (hinputTime₂ : inputs₂.2.2.1 = time₂)
    (hinput : ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁ =
      ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂)
    (hexpected : ReferenceUpReception.currentOfferWord rate row₁
        (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate row₁ inputs₁ time₁).time
        prepared₁ hrow₁ hfollower₁ htime₁ =
      ReferenceUpReception.currentOfferWord rate row₂
        (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).selectedFollower
        (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂).time
        prepared₂ hrow₂ hfollower₂ htime₂) :
    ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate row₁ inputs₁ time₁
        prepared₁ hrow₁ hfollower₁ htime₁ hinputTime₁ =
      ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate row₂ inputs₂ time₂
        prepared₂ hrow₂ hfollower₂ htime₂ hinputTime₂ := by
  have hexpected' := by
    simpa only [hinput] using hexpected
  have hcurrent := hexpected'
  simp only [ReferenceUpReception.currentOfferWord] at hcurrent
  simp only [ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow,
    ReferenceUpReception.currentOfferWord, hinput]
  cases hraw : (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate row₂ inputs₂ time₂)).2 with
  | none => rfl
  | some _ =>
      simp only [hcurrent]
      rfl

def receiveUpFilteredAtComponents {p : Parameters} (rate : RateInput p)
    {Ω : Type*} (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Ω → CoordinatorCollectionLedger.Checked
      (CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale ×
        UpDecoderBank p) := fun ω =>
  let inputs := receptionInputsOfComponents rate ledger bank calendarIndex feedback ω
  let prepared := preparedRoundAtComponents rate (activation ω) (incoming ω)
    (row ω) (calendarIndex ω) (hvalid ω)
  ReferenceUpReception.receiveUpFilteredAtRow rate (row ω) inputs
    (calendarIndex ω) prepared
    (preparedRoundAtComponents_row rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω))
    (preparedRoundAtComponents_follower rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω) inputs)
    (preparedRoundAtComponents_time rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω))
    rfl

def wrongUniqueAndLocalAcceptanceAtComponents {p : Parameters} (rate : RateInput p)
    {Ω : Type*} (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Ω → Bool := fun ω =>
  let inputs := receptionInputsOfComponents rate ledger bank calendarIndex feedback ω
  let prepared := preparedRoundAtComponents rate (activation ω) (incoming ω)
    (row ω) (calendarIndex ω) (hvalid ω)
  ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow rate (row ω) inputs
    (calendarIndex ω) prepared
    (preparedRoundAtComponents_row rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω))
    (preparedRoundAtComponents_follower rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω) inputs)
    (preparedRoundAtComponents_time rate (activation ω) (incoming ω)
      (row ω) (calendarIndex ω) (hvalid ω))
    rfl

private theorem measurable_filteredReceptionRead {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (input : Ω → ReceptionInput p rate)
    (expected : Ω → Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))
    (hinput : Measurable input) (hexpected : Measurable expected) :
    Measurable (fun ω => (⟨input ω, expected ω⟩ : FilteredReceptionRead p rate)) := by
  apply FollowerDownMeasurability.measurable_of_countable_fibers
  intro target
  cases target with
  | mk targetInput targetExpected =>
      have hset : {ω | (⟨input ω, expected ω⟩ : FilteredReceptionRead p rate) =
          ⟨targetInput, targetExpected⟩} =
          {ω | input ω = targetInput} ∩ {ω | expected ω = targetExpected} := by
        ext ω
        change (⟨input ω, expected ω⟩ : FilteredReceptionRead p rate) =
          ⟨targetInput, targetExpected⟩ ↔ input ω = targetInput ∧
            expected ω = targetExpected
        constructor
        · intro h
          cases h
          exact ⟨rfl, rfl⟩
        · rintro ⟨rfl, rfl⟩
          rfl
      rw [hset]
      exact (measurableSet_eq_fun hinput measurable_const).inter
        (measurableSet_eq_fun hexpected measurable_const)

private theorem measurable_receiveUpFilteredAtComponents_core {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (receiveUpFilteredAtComponents rate activation incoming row
      calendarIndex ledger bank feedback hvalid) := by
  let inputs := receptionInputsOfComponents rate ledger bank calendarIndex feedback
  let receiverInput := fun ω => ReferenceUpReception.receptionInputAtRow rate
    (row ω) (inputs ω) (calendarIndex ω)
  let expected := fun ω => currentOfferWordAtComponents rate activation incoming row
    calendarIndex hvalid ω
  have hreceiverInput : Measurable receiverInput := by
    exact measurable_receptionInputAtComponents rate row calendarIndex ledger bank
      feedback hrow hcalendar hledger hbank hfeedback
  have hexpected : Measurable expected := by
    exact measurable_currentOfferWordAtComponents rate activation incoming row
      calendarIndex hactivation hincoming hrow hcalendar hvalid
  have hread : Measurable (fun ω : Ω =>
      (⟨receiverInput ω, expected ω⟩ : FilteredReceptionRead p rate)) :=
    measurable_filteredReceptionRead rate receiverInput expected hreceiverInput hexpected
  apply FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    (fun ω => (⟨receiverInput ω, expected ω⟩ : FilteredReceptionRead p rate)) hread
    (receiveUpFilteredAtComponents rate activation incoming row calendarIndex
      ledger bank feedback hvalid)
  intro x y hreadEq
  have hin := congrArg FilteredReceptionRead.input hreadEq
  have hex := congrArg FilteredReceptionRead.expected hreadEq
  dsimp [inputs, receiverInput] at hin
  dsimp [expected] at hex
  have hexpected : ReferenceUpReception.currentOfferWord rate (row x)
      (ReferenceUpReception.receptionInputAtRow rate (row x)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback x)
        (calendarIndex x)).selectedFollower
      (ReferenceUpReception.receptionInputAtRow rate (row x)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback x)
        (calendarIndex x)).time
      (preparedRoundAtComponents rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x))
      (preparedRoundAtComponents_row rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x))
      (preparedRoundAtComponents_follower rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback x))
      (preparedRoundAtComponents_time rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x)) =
    ReferenceUpReception.currentOfferWord rate (row y)
      (ReferenceUpReception.receptionInputAtRow rate (row y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y)
        (calendarIndex y)).selectedFollower
      (ReferenceUpReception.receptionInputAtRow rate (row y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y)
        (calendarIndex y)).time
      (preparedRoundAtComponents rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y))
      (preparedRoundAtComponents_row rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y))
      (preparedRoundAtComponents_follower rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y))
      (preparedRoundAtComponents_time rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y)) := by
    calc
      _ = currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid x :=
        (currentOfferWordAtComponents_eq_reference rate (activation x) (incoming x)
          (row x) (calendarIndex x) (hvalid x)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback x) rfl).symm
      _ = currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid y := by
        change currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid x = currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid y at hex
        exact hex
      _ = _ := currentOfferWordAtComponents_eq_reference rate (activation y) (incoming y)
        (row y) (calendarIndex y) (hvalid y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y) rfl
  exact receiveUpFilteredAtRow_eq_of_input_expected_eq rate
    (row x) (row y)
    (receptionInputsOfComponents rate ledger bank calendarIndex feedback x)
    (receptionInputsOfComponents rate ledger bank calendarIndex feedback y)
    (calendarIndex x) (calendarIndex y)
    (preparedRoundAtComponents rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x))
    (preparedRoundAtComponents rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y))
    (preparedRoundAtComponents_row rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x))
    (preparedRoundAtComponents_follower rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x)
      (receptionInputsOfComponents rate ledger bank calendarIndex feedback x))
    (preparedRoundAtComponents_time rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x))
    (preparedRoundAtComponents_row rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y))
    (preparedRoundAtComponents_follower rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y)
      (receptionInputsOfComponents rate ledger bank calendarIndex feedback y))
    (preparedRoundAtComponents_time rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y))
    rfl rfl hin hexpected

theorem measurable_receiveUpFilteredAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (receiveUpFilteredAtComponents rate activation incoming row
      calendarIndex ledger bank feedback hvalid) :=
  measurable_receiveUpFilteredAtComponents_core rate activation incoming row calendarIndex
    ledger bank feedback hactivation hincoming hrow hcalendar hledger hbank hfeedback hvalid

theorem measurable_wrongUniqueAndLocalAcceptanceAtComponents {p : Parameters}
    {Ω : Type*} [MeasurableSpace Ω] (rate : RateInput p)
    (activation : Ω → Activation p)
    (incoming : Ω → IncomingConfiguration p rate)
    (row : Ω → CompletePublicTable.CompleteRow p)
    (calendarIndex : Ω → Fin p.T)
    (ledger : Ω → CoordinatorCollectionLedger.Ledger p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
      rate.n rate.n_scale)
    (bank : Ω → UpDecoderBank p)
    (feedback : Ω → Fin (ConstructorDimensions.D p + 1))
    (hactivation : Measurable activation) (hincoming : Measurable incoming)
    (hrow : Measurable row) (hcalendar : Measurable calendarIndex)
    (hledger : Measurable ledger) (hbank : Measurable bank)
    (hfeedback : Measurable feedback)
    (hvalid : ∀ ω, (activation ω).val ≤ (calendarIndex ω).val + 1) :
    Measurable (wrongUniqueAndLocalAcceptanceAtComponents rate activation incoming row
      calendarIndex ledger bank feedback hvalid) := by
  let inputs := receptionInputsOfComponents rate ledger bank calendarIndex feedback
  let receiverInput := fun ω => ReferenceUpReception.receptionInputAtRow rate
    (row ω) (inputs ω) (calendarIndex ω)
  let expected := fun ω => currentOfferWordAtComponents rate activation incoming row
    calendarIndex hvalid ω
  have hreceiverInput : Measurable receiverInput := by
    exact measurable_receptionInputAtComponents rate row calendarIndex ledger bank
      feedback hrow hcalendar hledger hbank hfeedback
  have hexpected : Measurable expected := by
    exact measurable_currentOfferWordAtComponents rate activation incoming row
      calendarIndex hactivation hincoming hrow hcalendar hvalid
  have hread : Measurable (fun ω : Ω =>
      (⟨receiverInput ω, expected ω⟩ : FilteredReceptionRead p rate)) :=
    measurable_filteredReceptionRead rate receiverInput expected hreceiverInput hexpected
  apply FollowerDownJointMeasurability.measurable_of_countable_read_factorization
    (fun ω => (⟨receiverInput ω, expected ω⟩ : FilteredReceptionRead p rate)) hread
    (wrongUniqueAndLocalAcceptanceAtComponents rate activation incoming row
      calendarIndex ledger bank feedback hvalid)
  intro x y hreadEq
  have hin := congrArg FilteredReceptionRead.input hreadEq
  have hex := congrArg FilteredReceptionRead.expected hreadEq
  dsimp [inputs, receiverInput] at hin
  dsimp [expected] at hex
  have hexpected : ReferenceUpReception.currentOfferWord rate (row x)
      (ReferenceUpReception.receptionInputAtRow rate (row x)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback x)
        (calendarIndex x)).selectedFollower
      (ReferenceUpReception.receptionInputAtRow rate (row x)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback x)
        (calendarIndex x)).time
      (preparedRoundAtComponents rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x))
      (preparedRoundAtComponents_row rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x))
      (preparedRoundAtComponents_follower rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback x))
      (preparedRoundAtComponents_time rate (activation x) (incoming x) (row x)
        (calendarIndex x) (hvalid x)) =
    ReferenceUpReception.currentOfferWord rate (row y)
      (ReferenceUpReception.receptionInputAtRow rate (row y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y)
        (calendarIndex y)).selectedFollower
      (ReferenceUpReception.receptionInputAtRow rate (row y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y)
        (calendarIndex y)).time
      (preparedRoundAtComponents rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y))
      (preparedRoundAtComponents_row rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y))
      (preparedRoundAtComponents_follower rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y))
      (preparedRoundAtComponents_time rate (activation y) (incoming y) (row y)
        (calendarIndex y) (hvalid y)) := by
    calc
      _ = currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid x :=
        (currentOfferWordAtComponents_eq_reference rate (activation x) (incoming x)
          (row x) (calendarIndex x) (hvalid x)
          (receptionInputsOfComponents rate ledger bank calendarIndex feedback x) rfl).symm
      _ = currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid y := by
        change currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid x = currentOfferWordAtComponents rate activation incoming row calendarIndex
          hvalid y at hex
        exact hex
      _ = _ := currentOfferWordAtComponents_eq_reference rate (activation y) (incoming y)
        (row y) (calendarIndex y) (hvalid y)
        (receptionInputsOfComponents rate ledger bank calendarIndex feedback y) rfl
  exact wrongUniqueAndLocalAcceptanceAtRow_eq_of_input_expected_eq rate
    (row x) (row y)
    (receptionInputsOfComponents rate ledger bank calendarIndex feedback x)
    (receptionInputsOfComponents rate ledger bank calendarIndex feedback y)
    (calendarIndex x) (calendarIndex y)
    (preparedRoundAtComponents rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x))
    (preparedRoundAtComponents rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y))
    (preparedRoundAtComponents_row rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x))
    (preparedRoundAtComponents_follower rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x)
      (receptionInputsOfComponents rate ledger bank calendarIndex feedback x))
    (preparedRoundAtComponents_time rate (activation x) (incoming x) (row x)
      (calendarIndex x) (hvalid x))
    (preparedRoundAtComponents_row rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y))
    (preparedRoundAtComponents_follower rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y)
      (receptionInputsOfComponents rate ledger bank calendarIndex feedback y))
    (preparedRoundAtComponents_time rate (activation y) (incoming y) (row y)
      (calendarIndex y) (hvalid y))
    rfl rfl hin hexpected

end Bandits.Support.ReferenceUpReceptionMeasurability

end
