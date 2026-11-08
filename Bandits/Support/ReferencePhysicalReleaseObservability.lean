/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePhysicalReleaseQuota
public import Bandits.Support.ReferenceActiveHorizonMeasurability
public import Bandits.Support.ReferenceGeneratedActivePrefixFactor

/-!
# Borel observability of the physical incoming release tests

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-88,297-345`,
`sources/zip4/manuscript/06_interruptions.tex:435-492`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This module measures the literal pending-at-StartRound projection and the
literal collision-filtered release flags on the existing real carriers.  It
also composes that leaf with the existing actual active-run fold and proves
fixed-remainder control independence for the generated active prefix.  These
are Borel and deterministic support results: they do not identify a source
stopping time, a filtration, a conditional service law, an occupied-follower
geometry event, or a regret assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.FollowerPrepareJointMeasurability
open Bandits.Support.FollowerLifecycleMeasurability
open Bandits.Support.FollowerDownMeasurability
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.OrderedTupleSampler
open Bandits.Support.AssignmentPayloadDerivedMeasurability
open Bandits.Support.PrelaunchBufferRecovery

namespace Bandits.Support.ReferencePhysicalReleaseObservability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev Record := ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev StateCode := ReferenceActivePhysicalStepMeasurability.StateCode p rate
abbrev Incoming := FollowerPrepareJointMeasurability.IncomingConfiguration p rate

/-! ## Equality tests on the existing real payload carrier -/

private instance prodMeasurableEq {α β : Type*} [MeasurableSpace α]
    [MeasurableEq α] [MeasurableSpace β] [MeasurableEq β] :
    MeasurableEq (α × β) where
  measurableSet_diagonal := by
    change MeasurableSet {z : (α × β) × (α × β) | z.1 = z.2}
    have hfst : MeasurableSet {z : (α × β) × (α × β) | z.1.1 = z.2.1} :=
      measurableSet_eq_fun (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd)
    have hsnd : MeasurableSet {z : (α × β) × (α × β) | z.1.2 = z.2.2} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst)
        (measurable_snd.comp measurable_snd)
    have heq : {z : (α × β) × (α × β) | z.1 = z.2} =
        {z | z.1.1 = z.2.1} ∩ {z | z.1.2 = z.2.2} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Prod.ext_iff]
    rw [heq]
    exact hfst.inter hsnd

private instance finitePiMeasurableEq {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] [MeasurableEq α] : MeasurableEq (ι → α) where
  measurableSet_diagonal := by
    change MeasurableSet {z : (ι → α) × (ι → α) | z.1 = z.2}
    have hcoord (i : ι) :
        MeasurableSet {z : (ι → α) × (ι → α) | z.1 i = z.2 i} :=
      measurableSet_eq_fun
        ((measurable_pi_apply i).comp measurable_fst)
        ((measurable_pi_apply i).comp measurable_snd)
    have heq : {z : (ι → α) × (ι → α) | z.1 = z.2} =
        ⋂ i, {z | z.1 i = z.2 i} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, funext_iff]
    rw [heq]
    exact MeasurableSet.iInter hcoord

private theorem payloadObservation_injective :
    Function.Injective (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := by
  intro a b h
  cases a with
  | mk ac an ane asigma aslowset aanchor aapos aqueues aqle =>
    cases b with
    | mk bc bn bne bsigma bslowset banchor bapos bqueues bqle =>
      simp only [LaterAssignmentStartMeasurability.payloadObservation,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, hslow, rfl, rfl⟩
      have hsets : aslowset = bslowset := Subtype.ext hslow
      cases hsets
      rfl

private instance payloadMeasurableEq : MeasurableEq (Payload rate) where
  measurableSet_diagonal := by
    change MeasurableSet {z : Payload rate × Payload rate | z.1 = z.2}
    have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := rate.eta)) := comap_measurable _
    have hleft : Measurable (fun z : Payload rate × Payload rate =>
        LaterAssignmentStartMeasurability.payloadObservation z.1) :=
      hobs.comp measurable_fst
    have hright : Measurable (fun z : Payload rate × Payload rate =>
        LaterAssignmentStartMeasurability.payloadObservation z.2) :=
      hobs.comp measurable_snd
    have hdiag : MeasurableSet {z : Payload rate × Payload rate |
        LaterAssignmentStartMeasurability.payloadObservation z.1 =
          LaterAssignmentStartMeasurability.payloadObservation z.2} :=
      measurableSet_eq_fun hleft hright
    have heq : {z : Payload rate × Payload rate | z.1 = z.2} =
        {z | LaterAssignmentStartMeasurability.payloadObservation z.1 =
          LaterAssignmentStartMeasurability.payloadObservation z.2} := by
      ext z
      exact payloadObservation_injective.eq_iff.symm
    rw [heq]
    exact hdiag

private theorem measurable_sumElim_comp {X A B Y : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    (f : A × X → Y) (g : B × X → Y) (hf : Measurable f) (hg : Measurable g)
    (tag : X → A ⊕ B) (htag : Measurable tag) :
    Measurable (fun x => Sum.elim (fun a => f (a, x)) (fun b => g (b, x)) (tag x)) := by
  have h := (hf.sumElim hg).comp (MeasurableEquiv.sumProdDistrib A B X).measurable_toFun
  convert h.comp (htag.prodMk measurable_id) using 1
  funext x
  change Sum.elim _ _ (tag x) =
    Sum.elim f g ((Equiv.sumProdDistrib A B X) (tag x, x))
  cases tag x <;> rfl

private theorem decide_eq_of_iff {p q : Prop} (dp : Decidable p)
    (dq : Decidable q) (h : p ↔ q) : @decide p dp = @decide q dq := by
  cases dp with
  | isTrue hp =>
      cases dq with
      | isTrue _ => rfl
      | isFalse hn => exact False.elim (hn (h.mp hp))
  | isFalse hn =>
      cases dq with
      | isTrue hq => exact False.elim (hn (h.mpr hq))
      | isFalse _ => rfl

/-! ## The actual incoming StartRound pending projection -/

private def pendingOfStartCode (code : StartRoundResultCode p rate) : Bool :=
  match code with
  | .failure _ => false
  | .success state _ => decide (state.status = followerStatusCode .pending)

private theorem measurable_pendingOfStartCode :
    Measurable (pendingOfStartCode (p := p) (rate := rate)) := measurable_from_top

private def pendingCondition (t : Fin p.T) (incoming : Incoming (p := p) (rate := rate)) : Prop :=
  match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming with
  | .dagger => False
  | .ordinary state memory =>
      match ActiveFollowerLifecycle.startRound rate.eta t state memory with
      | .error _ => False
      | .ok (choice, _) => choice.status = .pending

private def pendingResult {α : Type} (status : α → ActiveRoundActions.FollowerStatus)
    (result : LifecycleCheck α) : Bool :=
  match result with
  | .error _ => false
  | .ok output => decide (status output = .pending)

private def pendingOfIncoming (t : Fin p.T) (incoming : Incoming (p := p) (rate := rate)) : Bool :=
  match FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate incoming with
  | .dagger => false
  | .ordinary state memory =>
      pendingResult (fun output => output.1.status)
        (ActiveFollowerLifecycle.startRound rate.eta t state memory)

private theorem pendingOfIncoming_eq_true (t : Fin p.T)
    (incoming : Incoming (p := p) (rate := rate)) :
    pendingOfIncoming (p := p) (rate := rate) t incoming = true ↔
      pendingCondition (p := p) (rate := rate) t incoming := by
  cases incoming with
  | none => simp [pendingOfIncoming, pendingResult, pendingCondition,
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming]
  | some pair =>
      rcases pair with ⟨state, memory⟩
      cases hstart : ActiveFollowerLifecycle.startRound rate.eta t
          (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
            state.1 state.2)
          (FollowerLifecycleMeasurability.localMemoryOfCode memory) <;>
        simp [pendingOfIncoming, pendingCondition, pendingResult,
          FollowerPrepareJointMeasurability.localConfigurationOfIncoming, hstart]

private def pendingOfIncomingCode (t : Fin p.T) (incoming : Incoming (p := p) (rate := rate)) : Bool :=
  match incoming with
  | none => false
  | some (state, memory) =>
      pendingOfStartCode (FollowerPrepareJointMeasurability.startRoundResultCode rate
        (FollowerPrepareJointMeasurability.assembleStartInput state memory t))

private def incomingAt (code : StateCode (p := p) (rate := rate)) (i : Fin (p.m - 1)) : Incoming (p := p) (rate := rate) :=
  code.2.2.2 i

private theorem measurable_incomingAt (i : Fin (p.m - 1)) :
    Measurable (fun code : StateCode (p := p) (rate := rate) =>
      incomingAt (p := p) (rate := rate) code i) :=
  (measurable_pi_apply i).comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id)))

private theorem pendingOfIncoming_eq_code (t : Fin p.T) (incoming : Incoming (p := p) (rate := rate)) :
    pendingOfIncoming (p := p) (rate := rate) t incoming =
      pendingOfIncomingCode (p := p) (rate := rate) t incoming := by
  cases incoming with
  | none => simp [pendingOfIncoming, pendingResult, pendingOfIncomingCode,
      FollowerPrepareJointMeasurability.localConfigurationOfIncoming]
  | some pair =>
      rcases pair with ⟨state, memory⟩
      have hrec := FollowerPrepareJointMeasurability.startRoundResultCode_atComponents_reconstruct
        rate state memory t
      change pendingResult (fun output => output.1.status)
          (ActiveFollowerLifecycle.startRound rate.eta t
            (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
              state.1 state.2)
            (FollowerLifecycleMeasurability.localMemoryOfCode memory)) =
        pendingOfStartCode (FollowerPrepareJointMeasurability.startRoundResultCode rate
          (FollowerPrepareJointMeasurability.assembleStartInput state memory t))
      calc
        pendingResult (fun output => output.1.status)
            (ActiveFollowerLifecycle.startRound rate.eta t
              (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
                state.1 state.2)
              (FollowerLifecycleMeasurability.localMemoryOfCode memory)) =
            pendingResult (fun output => output.1.status)
              (FollowerLifecycleMeasurability.startRoundResultOfCode rate
                (FollowerObservationStageMeasurabilityRepair.carriedStateBuffer state)
                (FollowerPrepareJointMeasurability.startRoundResultCode rate
                  (FollowerPrepareJointMeasurability.assembleStartInput state memory t))) :=
          congrArg (pendingResult (fun output => output.1.status)) hrec.symm
        _ = pendingOfStartCode (FollowerPrepareJointMeasurability.startRoundResultCode rate
            (FollowerPrepareJointMeasurability.assembleStartInput state memory t)) := by
          cases hcode : FollowerPrepareJointMeasurability.startRoundResultCode rate
              (FollowerPrepareJointMeasurability.assembleStartInput state memory t) with
          | failure reason =>
              simp [pendingResult, pendingOfStartCode, hcode,
                FollowerLifecycleMeasurability.startRoundResultOfCode]
          | success stateCode memoryCode =>
              have hstatus :
                  (FollowerDownMeasurability.followerStatusOfCode stateCode.status = .pending) ↔
                    stateCode.status = FollowerDownMeasurability.followerStatusCode .pending := by
                have hall : ∀ status : Fin 3,
                    (FollowerDownMeasurability.followerStatusOfCode status = .pending) ↔
                      status = FollowerDownMeasurability.followerStatusCode .pending := by
                  intro status
                  fin_cases status <;>
                    simp [FollowerDownMeasurability.followerStatusOfCode,
                      FollowerDownMeasurability.followerStatusCode]
                exact hall stateCode.status
              simp [pendingResult, pendingOfStartCode, hcode,
                FollowerLifecycleMeasurability.startRoundResultOfCode,
                FollowerDownMeasurability.followerStateOfCode,
                FollowerLifecycleMeasurability.localMemoryOfCode, hstatus]

private theorem measurable_pendingOfIncomingCode :
    Measurable (fun z : Incoming (p := p) (rate := rate) × Fin p.T =>
      pendingOfIncomingCode (p := p) (rate := rate) z.2 z.1) := by
  have htag : Measurable (fun z : Incoming (p := p) (rate := rate) × Fin p.T =>
      FollowerPrepareJointMeasurability.incomingConfigurationToSum
        (p := p) (rate := rate) z.1) :=
    (FollowerPrepareJointMeasurability.measurable_incomingConfigurationToSum rate).comp
      measurable_fst
  have hnone : Measurable (fun _ : Unit × (Incoming (p := p) (rate := rate) × Fin p.T) => false) := measurable_const
  have hstate : Measurable (fun z :
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) ×
        (Incoming (p := p) (rate := rate) × Fin p.T) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hmemory : Measurable (fun z :
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) ×
        (Incoming (p := p) (rate := rate) × Fin p.T) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have htime : Measurable (fun z :
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) ×
        (Incoming (p := p) (rate := rate) × Fin p.T) => z.2.2) :=
    measurable_snd.comp measurable_snd
  have hsome : Measurable (fun z :
      (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) ×
        (Incoming (p := p) (rate := rate) × Fin p.T) =>
        pendingOfStartCode (FollowerPrepareJointMeasurability.startRoundResultCode rate
          (FollowerPrepareJointMeasurability.assembleStartInput z.1.1 z.1.2 z.2.2))) := by
    let Ω := (FollowerPrepareJointMeasurability.CarriedState p rate ×
        FollowerPrepareJointMeasurability.LocalMemoryCode p) ×
        (Incoming (p := p) (rate := rate) × Fin p.T)
    let state : Ω → FollowerPrepareJointMeasurability.CarriedState p rate := fun z => z.1.1
    let memory : Ω → FollowerPrepareJointMeasurability.LocalMemoryCode p := fun z => z.1.2
    let time : Ω → Fin p.T := fun z => z.2.2
    have hinput : Measurable (fun z : Ω =>
        FollowerPrepareJointMeasurability.assembleStartInput (state z) (memory z) (time z)) :=
      FollowerPrepareJointMeasurability.measurable_assembleStartInput
        state memory time hstate hmemory htime
    have hcode : Measurable (fun z : Ω =>
        FollowerPrepareJointMeasurability.startRoundResultCode rate
          (FollowerPrepareJointMeasurability.assembleStartInput (state z) (memory z) (time z))) :=
      (FollowerPrepareJointMeasurability.measurable_startRoundResultCode rate).comp hinput
    exact measurable_pendingOfStartCode.comp hcode
  have hsum := measurable_sumElim_comp (X := Incoming (p := p) (rate := rate) × Fin p.T)
    (A := Unit) (B := FollowerPrepareJointMeasurability.CarriedState p rate ×
      FollowerPrepareJointMeasurability.LocalMemoryCode p) (Y := Bool)
    (fun _ => false)
    (fun z => pendingOfStartCode
      (FollowerPrepareJointMeasurability.startRoundResultCode rate
        (FollowerPrepareJointMeasurability.assembleStartInput z.1.1 z.1.2 z.2.2)))
    hnone hsome
    (fun z => FollowerPrepareJointMeasurability.incomingConfigurationToSum
      (p := p) (rate := rate) z.1) htag
  have heq : (fun z : Incoming (p := p) (rate := rate) × Fin p.T =>
      pendingOfIncomingCode (p := p) (rate := rate) z.2 z.1) =
      fun z => Sum.elim (fun _ => false)
        (fun x => pendingOfStartCode
          (FollowerPrepareJointMeasurability.startRoundResultCode rate
            (FollowerPrepareJointMeasurability.assembleStartInput x.1 x.2 z.2)))
        (FollowerPrepareJointMeasurability.incomingConfigurationToSum
          (p := p) (rate := rate) z.1) := by
    funext z
    cases z.1 with
    | none => rfl
    | some pair => rcases pair with ⟨state, memory⟩; rfl
  rw [heq]
  exact hsum

private theorem measurable_pendingOfIncoming :
    Measurable (fun z : Incoming (p := p) (rate := rate) × Fin p.T =>
      pendingOfIncoming (p := p) (rate := rate) z.2 z.1) := by
  have heq : (fun z : Incoming (p := p) (rate := rate) × Fin p.T =>
      pendingOfIncoming (p := p) (rate := rate) z.2 z.1) =
      fun z => pendingOfIncomingCode (p := p) (rate := rate) z.2 z.1 := by
    funext z
    exact pendingOfIncoming_eq_code (p := p) (rate := rate) z.2 z.1
  rw [heq]
  exact measurable_pendingOfIncomingCode

private abbrev LiveTag := Unit ⊕ (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)

private def liveCoordinatorFields : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate → LiveTag (p := p) (rate := rate)
  | .inl _ => .inl ()
  | .inr (.inl fields) => .inr fields
  | .inr (.inr _) => .inl ()

private theorem measurable_liveCoordinatorFields :
    Measurable (liveCoordinatorFields (p := p) (rate := rate)) := by
  unfold liveCoordinatorFields
  refine measurable_fun_sum ?_ ?_
  · exact measurable_const
  · refine measurable_fun_sum ?_ ?_
    · exact measurable_inr
    · refine measurable_fun_sum ?_ ?_
      · exact measurable_const
      · exact measurable_const

private def livePendingMember (fields : Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p)
    (z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) (i : Fin (p.m - 1)) : Bool :=
  decide (fields.1 = z.1) && decide (fields.2.pending = ∅) &&
    pendingOfIncoming (p := p) (rate := rate) z.2.1
      (incomingAt (p := p) (rate := rate) z.2.2 i)

private def pendingMembershipCode (z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)))
    (i : Fin (p.m - 1)) : Bool :=
  match liveCoordinatorFields (p := p) (rate := rate) z.2.2.1 with
  | .inl _ => false
  | .inr fields => livePendingMember (p := p) (rate := rate) fields z i

private theorem measurable_livePendingMember (i : Fin (p.m - 1)) :
    Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
        (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) =>
          livePendingMember (p := p) (rate := rate) z.1 z.2 i) := by
  have hleft : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hright : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) => z.2.1) :=
    measurable_fst.comp measurable_snd
  have hpayloadEq : MeasurableSet {z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) | z.1.1 = z.2.1} :=
    measurableSet_eq_fun hleft hright
  have hlivePending : Measurable (fun z : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.pending) :=
    measurable_from_top
  have hleftPending : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) => z.1.2.pending) :=
    hlivePending.comp (measurable_snd.comp measurable_fst)
  have hpendingEq : MeasurableSet {z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) | z.1.2.pending = (∅ : Finset (Fin (p.m - 1)))} :=
    measurableSet_eq_fun hleftPending measurable_const
  have hinput : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) =>
        (incomingAt (p := p) (rate := rate) z.2.2.2 i, z.2.2.1)) := by
    exact (measurable_incomingAt (p := p) (rate := rate) i).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_id))) |>.prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id)))
  have hpending :=
    (measurable_pendingOfIncoming (p := p) (rate := rate)).comp hinput
  have hpayloadBool : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) => decide (z.1.1 = z.2.1)) := by
    apply measurable_to_bool
    have hset : (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
        (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) =>
        decide (z.1.1 = z.2.1)) ⁻¹' ({true} : Set Bool) =
        {z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
          (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) | z.1.1 = z.2.1} := by
      ext z
      simp
    rw [hset]
    exact hpayloadEq
  have hpendingBool : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) => decide (z.1.2.pending = ∅)) := by
    apply measurable_to_bool
    have hset : (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
        (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) =>
        decide (z.1.2.pending = ∅)) ⁻¹' ({true} : Set Bool) =
        {z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
          (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) | z.1.2.pending = ∅} := by
      ext z
      simp
    rw [hset]
    exact hpendingEq
  have hstartBool : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) =>
        pendingOfIncoming (p := p) (rate := rate) z.2.2.1
          (incomingAt (p := p) (rate := rate) z.2.2.2 i)) :=
    (measurable_pendingOfIncoming (p := p) (rate := rate)).comp hinput
  have htuple := hpayloadBool.prodMk (hpendingBool.prodMk hstartBool)
  have hand : Measurable (fun b : Bool × (Bool × Bool) => b.1 && b.2.1 && b.2.2) :=
    measurable_of_finite _
  exact hand.comp htuple

private theorem measurable_pendingMembershipCode (i : Fin (p.m - 1)) :
    Measurable (fun z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)) =>
      pendingMembershipCode z i) := by
  have htag : Measurable (fun z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)) =>
      liveCoordinatorFields (p := p) (rate := rate) z.2.2.1) :=
    measurable_liveCoordinatorFields.comp
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_id)))
  have hnone : Measurable (fun _ : Unit ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) => false) := measurable_const
  have hsome : Measurable (fun z : (Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ×
      (Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) =>
        livePendingMember (p := p) (rate := rate) z.1 z.2 i) :=
    measurable_livePendingMember (p := p) (rate := rate) i
  have hsum := measurable_sumElim_comp
    (X := Payload rate × (Fin p.T × StateCode (p := p) (rate := rate))) (A := Unit)
    (B := Payload rate × ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) (Y := Bool)
    (fun _ => false) (fun z => livePendingMember (p := p) (rate := rate) z.1 z.2 i) hnone hsome
    (fun z => liveCoordinatorFields (p := p) (rate := rate) z.2.2.1) htag
  have heq : (fun z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)) => pendingMembershipCode z i) =
      fun z => Sum.elim (fun _ => false)
        (fun fields => livePendingMember (p := p) (rate := rate) fields z i)
        (liveCoordinatorFields (p := p) (rate := rate) z.2.2.1) := by
    funext z
    cases h : liveCoordinatorFields (p := p) (rate := rate) z.2.2.1 <;>
      simp [pendingMembershipCode, h]
  rw [heq]
  exact hsum

private def pendingAtStartCode (M : Payload rate) (t : Fin p.T) (code : StateCode (p := p) (rate := rate)) :
    Finset (Fin (p.m - 1)) :=
  match liveCoordinatorFields (p := p) (rate := rate) code.1 with
  | .inl _ => ∅
  | .inr fields =>
      if fields.1 = M ∧ fields.2.pending = ∅ then
        Finset.univ.filter fun i =>
          pendingCondition (p := p) (rate := rate) t
            (incomingAt (p := p) (rate := rate) code i)
      else ∅

private theorem pendingAtStart_decode_code (M : Payload rate) (t : Fin p.T)
    (code : StateCode (p := p) (rate := rate)) :
    ReferencePhysicalReleaseQuota.pendingAtStart M t (ReferenceActivePhysicalStepMeasurability.decodeState code) =
      pendingAtStartCode M t code := by
  rcases code with ⟨coordinator, ⟨upBank, ⟨activations, followers⟩⟩⟩
  cases coordinator with
  | inl first => rfl
  | inr remainder =>
      cases remainder with
      | inl live =>
          rcases live with ⟨payload, discrete⟩
          apply Finset.ext
          intro i
          simp [pendingAtStartCode, liveCoordinatorFields,
            ReferenceActivePhysicalStepMeasurability.decodeState,
            ReferenceActivePhysicalStepMeasurability.decodeCoordinator,
            ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters,
            ReferenceActivePhysicalStepMeasurability.decodeLiveOwned,
            ReferencePhysicalReleaseQuota.pendingAtStart, pendingCondition,
            FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
            incomingAt, Finset.mem_filter, Finset.mem_univ] <;> rfl
      | inr tail =>
          cases tail <;> rfl

private theorem pendingAtStart_code_eq (M : Payload rate) (t : Fin p.T)
    (state : ReferenceActivePhysicalStep.State p rate) :
    ReferencePhysicalReleaseQuota.pendingAtStart M t state =
      pendingAtStartCode M t (ReferenceActivePhysicalStepMeasurability.encodeState state) := by
  calc
    ReferencePhysicalReleaseQuota.pendingAtStart M t state =
        ReferencePhysicalReleaseQuota.pendingAtStart M t
          (ReferenceActivePhysicalStepMeasurability.decodeState
            (ReferenceActivePhysicalStepMeasurability.encodeState state)) := by
      rw [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState]
    _ = pendingAtStartCode M t (ReferenceActivePhysicalStepMeasurability.encodeState state) :=
      pendingAtStart_decode_code M t (ReferenceActivePhysicalStepMeasurability.encodeState state)

private theorem measurable_pendingMembershipCode_eq_true (i : Fin (p.m - 1)) :
    MeasurableSet {z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)) |
      pendingMembershipCode z i = true} := by
  exact (measurable_pendingMembershipCode i) (measurableSet_singleton true)

private theorem measurable_pendingAtStart_mem (i : Fin (p.m - 1)) :
    MeasurableSet {z : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} := by
  let encode : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) →
      Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)) :=
    fun z => (z.1, (z.2.1, ReferenceActivePhysicalStepMeasurability.encodeState z.2.2))
  have hencode : Measurable encode := by
    exact measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        (ReferenceActivePhysicalStepMeasurability.measurable_encodeState.comp (measurable_snd.comp measurable_snd)))
  have hmember : Measurable (fun z : Payload rate × (Fin p.T × StateCode (p := p) (rate := rate)) =>
      pendingMembershipCode z i) := measurable_pendingMembershipCode i
  have hcode : Measurable (fun z : Payload rate ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate) =>
      pendingMembershipCode (encode z) i) := hmember.comp hencode
  have hset : {z : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} =
      {z | pendingMembershipCode (encode z) i = true} := by
    ext z
    have hcodeEq := pendingAtStart_code_eq z.1 z.2.1 z.2.2
    simp only [Set.mem_setOf_eq]
    rw [hcodeEq]
    cases htag : liveCoordinatorFields (p := p) (rate := rate)
        (ReferenceActivePhysicalStepMeasurability.encodeState z.2.2).1 with
    | inl tag => simp [encode, pendingAtStartCode, pendingMembershipCode, htag]
    | inr fields =>
        by_cases hcond : fields.1 = z.1 ∧ fields.2.pending = ∅
        · simp [encode, pendingAtStartCode, pendingMembershipCode,
            livePendingMember, htag, hcond, pendingOfIncoming_eq_true]
        · simp [encode, pendingAtStartCode, pendingMembershipCode,
            livePendingMember, htag, hcond, pendingOfIncoming_eq_true]
  rw [hset]
  exact hcode (measurableSet_singleton true)

/-- Joint Borel measurability of the actual StartRound pending set, with both
the full real incoming payload and the complete physical state varying. -/
theorem measurable_pendingAtStart :
    Measurable (fun z : Payload rate ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate) =>
      ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2) := by
  apply measurable_to_countable'
  intro target
  change MeasurableSet {z : Payload rate ×
    (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
    ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2 = target}
  have heq : {z : Payload rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
      ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2 = target} =
      {z | ∀ i, (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2) ↔
        i ∈ target} := by
    ext z
    simp only [Set.mem_setOf_eq, Finset.ext_iff]
  rw [heq]
  have hI : {z : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
      ∀ i, (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2) ↔ i ∈ target} =
      ⋂ i, {z : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
        (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2) ↔ i ∈ target} := by
    ext z
    simp
  rw [hI]
  exact MeasurableSet.iInter fun i => by
    by_cases hi : i ∈ target
    · simpa [hi] using measurable_pendingAtStart_mem i
    · have hset : {z : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
          (i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2) ↔ i ∈ target} =
          {z | i ∉ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} := by
        ext z
        simp [hi]
      rw [hset]
      have hcompl : {z : Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
          i ∉ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} =
          ({z | i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} :
            Set (Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate)))ᶜ := by
        ext z
        simp
      rw [hcompl]
      exact (measurable_pendingAtStart_mem i).compl

/-- Fixed-incoming-payload specialization of joint pending-set
measurability. -/
theorem measurable_pendingAtStart_fixedPayload (M : Payload rate) :
    Measurable (fun z : Fin p.T × ReferenceActivePhysicalStep.State p rate =>
      ReferencePhysicalReleaseQuota.pendingAtStart M z.1 z.2) := by
  exact measurable_pendingAtStart.comp (measurable_const.prodMk measurable_id)

/-- Fixed-payload, fixed-calendar specialization of the pending projection. -/
theorem measurable_pendingAtStart_fixedPayloadTime (M : Payload rate) (t : Fin p.T) :
    Measurable (fun state : ReferenceActivePhysicalStep.State p rate =>
      ReferencePhysicalReleaseQuota.pendingAtStart M t state) := by
  exact measurable_pendingAtStart.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- Actual pending-membership event with a varying incoming payload and
state/time pair. -/
theorem measurable_pendingAtStart_mem_event (i : Fin (p.m - 1)) :
    MeasurableSet {z : Payload rate ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} :=
  measurable_pendingAtStart_mem i

/-- Fixed-payload pending-membership event. -/
theorem measurable_pendingAtStart_mem_event_fixedPayload (M : Payload rate)
    (i : Fin (p.m - 1)) :
    MeasurableSet {z : Fin p.T × ReferenceActivePhysicalStep.State p rate |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M z.1 z.2} := by
  let insertPayload : Fin p.T × ReferenceActivePhysicalStep.State p rate →
      Payload rate × (Fin p.T × ReferenceActivePhysicalStep.State p rate) :=
    fun z => (M, z)
  have hinsert : Measurable insertPayload := measurable_const.prodMk measurable_id
  have hset : {z : Fin p.T × ReferenceActivePhysicalStep.State p rate |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M z.1 z.2} =
      insertPayload ⁻¹' {z : Payload rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
          i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} := by
    ext z
    rfl
  rw [hset]
  exact (measurable_pendingAtStart_mem i).preimage hinsert

/-- Fixed-payload and fixed-calendar pending-membership event. -/
theorem measurable_pendingAtStart_mem_event_fixedPayloadTime (M : Payload rate)
    (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet {state : ReferenceActivePhysicalStep.State p rate |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M t state} := by
  have hmem : MeasurableSet {z : Payload rate ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} :=
    measurable_pendingAtStart_mem i
  let insert : ReferenceActivePhysicalStep.State p rate → Payload rate ×
      (Fin p.T × ReferenceActivePhysicalStep.State p rate) := fun state => (M, (t, state))
  have hinsert : Measurable insert :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hset : {state : ReferenceActivePhysicalStep.State p rate |
      i ∈ ReferencePhysicalReleaseQuota.pendingAtStart M t state} =
      insert ⁻¹' {z : Payload rate ×
        (Fin p.T × ReferenceActivePhysicalStep.State p rate) |
        i ∈ ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1 z.2.2} := by
    ext state
    rfl
  rw [hset]
  exact hmem.preimage hinsert

/-! ## The literal round-record projection and collision-filtered flags -/

/-- The only new record constructor: its output is the literal physical step
on the supplied complete input. -/
def recordOfInput (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Record (p := p) (rate := rate) :=
  ⟨x, ReferenceActivePhysicalStep.step x, rfl⟩

private theorem acceptedEscapeArm_downRecord (M : Payload rate)
    (i : Fin (p.m - 1)) :
    ActiveFollowerLifecycle.acceptedEscapeArm (M.downRecord i) =
      M.assignment.auxiliary := by
  have h := ActiveFollowerLifecycle.accepted_escape_arm_one_based (M.downRecord i)
  have hfield : (M.downRecord i).val.e = M.assignment.auxiliary.val + 1 := by
    rw [M.downRecord_fields i]
  have heq := h.trans hfield
  apply Fin.ext
  exact Nat.add_right_cancel heq

private theorem downArm_downRecord (M : Payload rate) (i : Fin (p.m - 1)) :
    PrelaunchBufferRecovery.downArm rate.eta (M.downRecord i) =
      M.assignment.assigned i := by
  have h := PrelaunchBufferRecovery.down_arm_one_based rate.eta (M.downRecord i)
  have hfield : (M.downRecord i).val.a = (M.assignment.assigned i).val + 1 := by
    rw [M.downRecord_fields i]
  have heq := h.trans hfield
  apply Fin.ext
  exact Nat.add_right_cancel heq

private theorem measurable_payloadSlowSet :
    Measurable (fun M : Payload rate => M.slowSet) := by
  have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hslow : Measurable (fun M : Payload rate => M.slowSet.1) := by
    change Measurable (fun M : Payload rate =>
      (LaterAssignmentStartMeasurability.payloadObservation M).2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hobs))
  exact hslow.subtype_mk (h := fun M => M.slowSet.2)

private theorem measurable_assignedArm (i : Fin (p.m - 1)) :
    Measurable (fun M : Payload rate => M.assignment.assigned i) := by
  change Measurable (fun M : Payload rate =>
    CanonicalAssignmentVector.followerArm p.two_le_m M.slowSet i)
  exact (measurable_of_finite fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
    CanonicalAssignmentVector.followerArm p.two_le_m U i).comp measurable_payloadSlowSet

private theorem measurable_evalLearningRow :
    Measurable (fun z : ContinuousLearningRows.LearningRow p × Fin p.T => z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro t
  exact measurable_pi_apply t

private theorem measurable_currentSlice : Measurable
    (fun x : ReferenceActivePhysicalStep.RoundInput p rate => (x.row.2 x.time).1) := by
  have hrow : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.row) :=
    ReferenceActivePhysicalStepMeasurability.measurable_row
  have htime : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.time) :=
    ReferenceActivePhysicalStepMeasurability.measurable_time
  have hrow' : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate => x.row.2) :=
    measurable_snd.comp hrow
  exact measurable_fst.comp
    (measurable_evalLearningRow.comp (hrow'.prodMk htime))

private theorem measurable_releaseTest (i : Fin (p.m - 1)) :
    Measurable (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferencePhysicalReleaseQuota.releaseFlag z.1 (recordOfInput z.2) i) := by
  classical
  let observation : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate →
      ReferencePrelaunchFollower.Observation p := fun z =>
        (ReferenceActivePhysicalStep.step z.2).ownEntries
          (PublicDiscreteDraws.followerPlayer p.two_le_m i) |>.2
  let slot : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate →
      PublicDiscreteDraws.Slot := fun z =>
        PublicDiscreteDraws.slotDraw ((z.2.row.2 z.2.time).1)
  let selected : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate →
      Fin (p.m - 1) := fun z =>
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          ((z.2.row.2 z.2.time).1)
  let receiver : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate → Fin p.K :=
    fun z => (OrderedTupleSampler.sample p.two_le_m p.m_lt_K
      ((z.2.row.2 z.2.time).1)).val (ActiveRoundActions.coordinator p.two_le_m)
  let pilot : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate → Fin p.K :=
    fun z => PublicDiscreteDraws.pilotDraw (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) ((z.2.row.2 z.2.time).1)
  let positive : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate → Bool :=
    fun z => decide (0 < (observation z).val.val)
  let accepted : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate → Fin p.K :=
    fun z => ActiveFollowerLifecycle.acceptedEscapeArm (z.1.downRecord i)
  let assigned : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate → Fin p.K :=
    fun z => PrelaunchBufferRecovery.downArm rate.eta (z.1.downRecord i)
  let args := fun z => (positive z, (slot z, (selected z,
    (receiver z, (accepted z, (pilot z, assigned z))))))
  let condition : Bool × (PublicDiscreteDraws.Slot ×
      (Fin (p.m - 1) × (Fin p.K × (Fin p.K × (Fin p.K × Fin p.K))))) → Bool :=
    fun z => decide (z.1 = true ∧
      ((z.2.1 = PublicDiscreteDraws.upSlot ∧ z.2.2.1 = i ∧
          z.2.2.2.1 = z.2.2.2.2.1) ∨
        (z.2.1 = PublicDiscreteDraws.dataSlot ∧
          z.2.2.2.2.2.1 = z.2.2.2.2.2.2)))
  have hslot : Measurable slot :=
    PublicDiscreteDraws.measurable_slotDraw.comp
      (measurable_currentSlice.comp measurable_snd)
  have hselected : Measurable selected :=
    (PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K).comp
      (measurable_currentSlice.comp measurable_snd)
  have htuple : Measurable (fun z : Payload rate ×
      ReferenceActivePhysicalStep.RoundInput p rate =>
        OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((z.2.row.2 z.2.time).1)) :=
    (OrderedTupleSampler.measurable_sample p.two_le_m p.m_lt_K).comp
      (measurable_currentSlice.comp measurable_snd)
  have hreceiver : Measurable receiver :=
    (measurable_pi_apply (ActiveRoundActions.coordinator p.two_le_m)).comp
      (measurable_subtype_coe.comp htuple)
  have hpilot : Measurable pilot :=
    (PublicDiscreteDraws.measurable_pilotDraw (K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m)).comp
        (measurable_currentSlice.comp measurable_snd)
  have hobs : Measurable observation :=
    (ReferenceActiveStepCompositionMeasurability.measurable_stepOwnObservation
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).comp measurable_snd
  have hobsVal : Measurable (fun z => (observation z).val.val) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.comp hobs)
  have hpositiveSet : MeasurableSet {z : Payload rate ×
      ReferenceActivePhysicalStep.RoundInput p rate | 0 < (observation z).val.val} :=
    measurableSet_lt measurable_const hobsVal
  have hpositive : Measurable positive := by
    apply measurable_to_bool
    have hset : positive ⁻¹' {true} =
        {z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate |
          0 < (observation z).val.val} := by
      ext z
      simp [positive]
    rw [hset]
    exact hpositiveSet
  have haux : Measurable (fun z : Payload rate ×
      ReferenceActivePhysicalStep.RoundInput p rate => z.1.assignment.auxiliary) :=
    (AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary
      (p := p) (eta := rate.eta)).comp
        (measurable_fst : Measurable
          (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate => z.1))
  have hassigned : Measurable assigned := by
    have h := (measurable_assignedArm (p := p) (rate := rate) i).comp
      (measurable_fst : Measurable
        (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate => z.1))
    have heq : assigned = fun z : Payload rate ×
        ReferenceActivePhysicalStep.RoundInput p rate => z.1.assignment.assigned i := by
      funext z
      exact downArm_downRecord z.1 i
    rw [heq]
    exact h
  have haccepted : Measurable accepted := by
    have heq : accepted = fun z : Payload rate ×
        ReferenceActivePhysicalStep.RoundInput p rate => z.1.assignment.auxiliary := by
      funext z
      exact acceptedEscapeArm_downRecord z.1 i
    rw [heq]
    exact haux
  have hargs : Measurable args :=
    hpositive.prodMk (hslot.prodMk
      (hselected.prodMk (hreceiver.prodMk (haccepted.prodMk (hpilot.prodMk hassigned)))))
  have hcondition : Measurable condition := measurable_of_finite _
  have heq : (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferencePhysicalReleaseQuota.releaseFlag z.1 (recordOfInput z.2) i) =
      condition ∘ args := by
    funext z
    have hprop := ActiveFollowerLifecycle.releaseCondition_complete_row rate.eta i
      z.2.time z.2.row (observation z) (z.1.downRecord i)
    let tests : Prop :=
      ((slot z = PublicDiscreteDraws.upSlot ∧ selected z = i ∧
          receiver z = accepted z) ∨
        (slot z = PublicDiscreteDraws.dataSlot ∧ pilot z = assigned z))
    have hprop' : ActiveFollowerLifecycle.releaseCondition rate.eta i
          (ActiveFollowerLifecycle.publicRowOfCompleteRow z.2.row z.2.time)
          (observation z) (z.1.downRecord i) ↔
        (0 < (observation z).val.val ∧ tests) := hprop
    have hdec : ReferencePhysicalReleaseQuota.releaseFlag z.1 (recordOfInput z.2) i =
        decide (0 < (observation z).val.val ∧ tests) := by
      change decide (ActiveFollowerLifecycle.releaseCondition rate.eta i
          (ActiveFollowerLifecycle.publicRowOfCompleteRow z.2.row z.2.time)
          (observation z) (z.1.downRecord i)) =
        decide (0 < (observation z).val.val ∧ tests)
      exact decide_eq_of_iff (inferInstance) (inferInstance) hprop'
    calc
      ReferencePhysicalReleaseQuota.releaseFlag z.1 (recordOfInput z.2) i = _ := hdec
      _ = condition (args z) := by
        have hpositive : positive z = true ↔ 0 < (observation z).val.val := by
          simp [positive]
        have hiff : (0 < (observation z).val.val ∧ tests) ↔
            (positive z = true ∧ tests) := by
          constructor
          · rintro ⟨hp, htests⟩
            exact ⟨hpositive.mpr hp, htests⟩
          · rintro ⟨hp, htests⟩
            exact ⟨hpositive.mp hp, htests⟩
        have hdec := decide_eq_of_iff (inferInstance) (inferInstance) hiff
        change decide (0 < (observation z).val.val ∧ tests) =
          decide (positive z = true ∧ tests)
        exact hdec
  rw [heq]
  exact hcondition.comp hargs

/-- Joint measurability of the actual collision-filtered release test on the
full incoming real payload and complete physical round input. -/
theorem measurable_releaseFlag (i : Fin (p.m - 1)) :
    Measurable (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferencePhysicalReleaseQuota.releaseFlag z.1 (recordOfInput z.2) i) :=
  measurable_releaseTest i

private theorem measurable_currentSlot (slot : PublicDiscreteDraws.Slot) :
    Measurable (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
      decide (PublicDiscreteDraws.slotDraw ((z.2.row.2 z.2.time).1) = slot)) := by
  let hslice := measurable_currentSlice.comp (measurable_snd : Measurable
    (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate => z.2))
  exact (measurable_of_finite fun s : PublicDiscreteDraws.Slot => decide (s = slot)).comp
    (PublicDiscreteDraws.measurable_slotDraw.comp hslice)

/-- The actual UP release flag, including the literal slot condition. -/
theorem measurable_upFlag (i : Fin (p.m - 1)) :
    Measurable (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferencePhysicalReleaseQuota.upFlag z.1 (recordOfInput z.2) i) := by
  let up := fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
    decide (PublicDiscreteDraws.slotDraw ((z.2.row.2 z.2.time).1) =
      PublicDiscreteDraws.upSlot)
  have hup : Measurable up := measurable_currentSlot PublicDiscreteDraws.upSlot
  have hpair := measurable_releaseFlag i |>.prodMk hup
  have hand : Measurable (fun b : Bool × Bool => b.1 && b.2) := measurable_of_finite _
  exact hand.comp hpair

/-- The actual DATA release flag, including the literal slot condition. -/
theorem measurable_dataFlag (i : Fin (p.m - 1)) :
    Measurable (fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferencePhysicalReleaseQuota.dataFlag z.1 (recordOfInput z.2) i) := by
  let data := fun z : Payload rate × ReferenceActivePhysicalStep.RoundInput p rate =>
    decide (PublicDiscreteDraws.slotDraw ((z.2.row.2 z.2.time).1) =
      PublicDiscreteDraws.dataSlot)
  have hdata : Measurable data := measurable_currentSlot PublicDiscreteDraws.dataSlot
  have hpair := measurable_releaseFlag i |>.prodMk hdata
  have hand : Measurable (fun b : Bool × Bool => b.1 && b.2) := measurable_of_finite _
  exact hand.comp hpair

/-! ## The actual active-run fold -/

/-- The pending projection after the existing active-run fold, jointly in the
incoming real payload and every valid initial state, row table, selected row,
and complete reward table. The time equality is the literal fold endpoint. -/
theorem measurable_runIncomingPending (start count : ℕ)
    (hspan : start + count ≤ p.T) (t : Fin p.T) (ht : t.val = start + count) :
    Measurable (fun z : Payload rate ×
      ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) start =>
      ReferencePhysicalReleaseQuota.pendingAtStart z.1 t
        (ReferenceActiveHorizonMeasurability.runOfInput start count hspan z.2).finalState) := by
  have hfinal := ReferenceActiveHorizonMeasurability.measurable_runFinalState
    (p := p) (rate := rate) start count hspan
  have hfinal' : Measurable (fun z : Payload rate ×
      ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) start =>
      (ReferenceActiveHorizonMeasurability.runOfInput start count hspan z.2).finalState) :=
    hfinal.comp measurable_snd
  have hinput : Measurable (fun z : Payload rate ×
      ReferenceActiveHorizonMeasurability.ActiveRunInput
        (p := p) (rate := rate) start =>
      (z.1, (t, (ReferenceActiveHorizonMeasurability.runOfInput start count hspan
        z.2).finalState))) :=
    measurable_fst.prodMk (measurable_const.prodMk hfinal')
  exact measurable_pendingAtStart.comp hinput

/-- Endpoint-constrained variable-calendar counterpart, composed with H's
existing calendar gluing result. -/
theorem measurable_calendarRunIncomingPending :
    Measurable (fun z : Payload rate ×
      {input : Fin p.T × ReferenceActiveHorizonMeasurability.CalendarRunInput
        (p := p) (rate := rate) //
        input.1.val = input.2.val.1 + input.2.val.2.1} =>
      ReferencePhysicalReleaseQuota.pendingAtStart z.1 z.2.1.1
        (ReferenceActiveHorizonMeasurability.calendarRunFinalState
          (p := p) (rate := rate) z.2.1.2)) := by
  have htime : Measurable (fun z : Payload rate ×
      {input : Fin p.T × ReferenceActiveHorizonMeasurability.CalendarRunInput
        (p := p) (rate := rate) //
        input.1.val = input.2.val.1 + input.2.val.2.1} => z.2.1.1) :=
    measurable_fst.comp (measurable_subtype_coe.comp measurable_snd)
  have hcalendar : Measurable (fun z : Payload rate ×
      {input : Fin p.T × ReferenceActiveHorizonMeasurability.CalendarRunInput
        (p := p) (rate := rate) //
        input.1.val = input.2.val.1 + input.2.val.2.1} => z.2.1.2) :=
    measurable_snd.comp (measurable_subtype_coe.comp measurable_snd)
  have hfinal : Measurable (fun z : Payload rate ×
      {input : Fin p.T × ReferenceActiveHorizonMeasurability.CalendarRunInput
        (p := p) (rate := rate) //
        input.1.val = input.2.val.1 + input.2.val.2.1} =>
        ReferenceActiveHorizonMeasurability.calendarRunFinalState
          (p := p) (rate := rate) z.2.1.2) :=
    (ReferenceActiveHorizonMeasurability.measurable_calendarRunFinalState
      (p := p) (rate := rate)).comp hcalendar
  have hinput : Measurable (fun z : Payload rate ×
      {input : Fin p.T × ReferenceActiveHorizonMeasurability.CalendarRunInput
        (p := p) (rate := rate) //
        input.1.val = input.2.val.1 + input.2.val.2.1} =>
        (z.1, (z.2.1.1, ReferenceActiveHorizonMeasurability.calendarRunFinalState
          (p := p) (rate := rate) z.2.1.2))) :=
    measurable_fst.prodMk (htime.prodMk hfinal)
  exact measurable_pendingAtStart.comp hinput

/-! ## Fixed-remainder generated-prefix consumers -/

/-- Pending-at-StartRound is unchanged when only the integrated time control
varies inside the same actual launch-start remainder fiber. Both start-event
proofs are derived from the original event on that same remainder. -/
theorem generated_pending_control_independent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (remainder : ReferenceGeneratedActivePrefixFactor.Remainder p q t)
    (hremainder : remainder ∈
      ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t)
    (control0 : ContinuousLearningRows.TimeControl p)
    (s : ℕ) (hs : s ≤ t.val)
    (hstart0 : remainder ∈
      ReferenceInitializationControlRemainder.launchStartRemainderEvent
        rate rewards C_star C_h q t s control0)
    (control control' : ContinuousLearningRows.TimeControl p) (M : Payload rate) :
    ReferencePhysicalReleaseQuota.pendingAtStart M t
        (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor rate rewards
          C_star C_h q t control remainder hremainder s (t.val - s) hs
          ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
            rate rewards C_star C_h q t s remainder hremainder control0 control).mp hstart0)
          (by omega)).finalState =
      ReferencePhysicalReleaseQuota.pendingAtStart M t
        (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor rate rewards
          C_star C_h q t control' remainder hremainder s (t.val - s) hs
          ((ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
            rate rewards C_star C_h q t s remainder hremainder control0 control').mp hstart0)
          (by omega)).finalState := by
  let count := t.val - s
  have hs_count : s + count = t.val := by
    dsimp [count]
    omega
  have hcount : s + count ≤ t.val := hs_count.le
  let hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s remainder hremainder control0 control).mp hstart0
  let hstart' := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s remainder hremainder control0 control').mp hstart0
  have hfactor := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
    rate rewards C_star C_h q t remainder hremainder control0 s count hs hcount hstart0 control control'
  rcases hfactor with ⟨active, _, _, _, _, _, hstate, _⟩
  exact congrArg (ReferencePhysicalReleaseQuota.pendingAtStart M t) hstate

/-- The actual source specialization of the generated-prefix factor. This
uses the original source arrays and preserves the literal selected-row,
crossing, and elapsed-start premises supplied by the source branch. -/
theorem generated_pending_on_source
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T)
    (source : ReferenceGeneratedActivePrefixFactor.SourceInput p)
    (hselected : ActualInitializationPhysicalStep.selectedRowIndex p source = q)
    (s count : ℕ) (hs : s ≤ t.val) (hcount : s + count ≤ t.val)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (helapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = s)
    (M : Payload rate) :
    let split := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source
    let control := split.1
    let remainder := split.2
    let hrem : remainder ∈
        ReferenceFixedTimeSourceControlCoupling.fixedControlRemainderStratum p q t := by
      change PrivateSourceStreams.coordinatorIndex p
        ((ReferenceFixedTimeSourceControlCoupling.fixedControlSplit p q t source).2.2).1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_private p q t source]
      change ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source = q
      rw [ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
      exact hselected
    let hstart : remainder ∈
        ReferenceInitializationControlRemainder.launchStartRemainderEvent
          rate rewards C_star C_h q t s control := by
      exact (ReferenceInitializationControlRemainder.launchStartRemainderEvent_iff_source
        rate rewards C_star C_h q t control source hselected s hs).mpr ⟨hcross, helapsed⟩
    ReferencePhysicalReleaseQuota.pendingAtStart M t
        (ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor rate rewards
          C_star C_h q t control remainder hrem s count hs hstart hcount).finalState =
      ReferencePhysicalReleaseQuota.pendingAtStart M t
        (ReferenceActivePhysicalHorizon.run
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
            control remainder hrem s hs hstart)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          s count (by omega)
          (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec rate rewards C_star C_h q t
            control remainder hrem s hs hstart).2.1).finalState := by
  have hsource := ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_on_source
    rate rewards C_star C_h q t source hselected s count hs hcount hcross helapsed
  dsimp only at hsource
  exact congrArg (ReferencePhysicalReleaseQuota.pendingAtStart M t) hsource.1

end Bandits.Support.ReferencePhysicalReleaseObservability

end

end
