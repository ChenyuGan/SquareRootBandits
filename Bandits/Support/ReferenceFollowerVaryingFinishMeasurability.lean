/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFollowerTailComposition
public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# Varying-activation composition of the reference follower finish

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14,28-64`.

This module lifts the accepted full fixed-activation reference follower tail
over the actual countable activation label. The full prepared output, original
view, own simultaneous feedback coordinate, and all four decoded follower
fields are retained. The whole-step composer takes only the actual dispatcher
view and own grid-feedback maps as conditional measurable inputs; it does not
assert full-step or manuscript measurability.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferencePrelaunchFollower

namespace Bandits.Support.ReferenceFollowerVaryingFinishMeasurability

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceFollowerTailComposition.RateInput

variable {p : Parameters} {rate : RateInput p}

private theorem decoderBatchCode_decoderBatchOfCode
    (batch : FollowerDownMeasurability.DecoderBatchCode p) :
    FollowerDownMeasurability.decoderBatchCode
      (FollowerDownMeasurability.decoderBatchOfCode batch) = batch := by
  rcases batch with ⟨pending, completed⟩
  simp [FollowerDownMeasurability.decoderBatchCode,
    FollowerDownMeasurability.decoderBatchOfCode,
    FollowerDownMeasurability.decoderEntryCode,
    FollowerDownMeasurability.decoderEntryOfCode,
    List.map_map, Function.comp_def]

private theorem bufferCodes_ofFn {n : ℕ}
    (skeleton : FollowerDownJointMeasurability.BufferSkeletonCode p n)
    (values : FollowerDownMeasurability.SavedScalarFamily n) :
    let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values
    HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer) skeleton ∧
      HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer) values := by
  dsimp only
  have hlen : (FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
      skeleton values).length = n := List.length_ofFn
  constructor
  · apply (Fin.heq_fun_iff hlen).mpr
    intro j
    change ((List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].calendarRound,
      (List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].pilot) = _
    simp only [List.getElem_ofFn]
  · apply (Fin.heq_fun_iff hlen).mpr
    intro j
    change ((List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].observation,
      (List.ofFn fun k : Fin n =>
      (⟨(skeleton k).1, (skeleton k).2, (values k).1, (values k).2⟩ :
        SparseCalendarReplay.SparseCalendarRecord p.K))[j.val].thinScalar) = _
    simp only [List.getElem_ofFn]

private theorem carriedStateOfState_reconstructCarriedState
    (carry : FollowerObservationStageMeasurabilityRepair.CarriedState p rate) :
    FollowerObservationStageMeasurabilityRepair.carriedStateOfState rate
      (FollowerObservationStageMeasurabilityRepair.reconstructCarriedState
        carry.1 carry.2) = carry := by
  cases carry with
  | mk index values =>
      rcases index with ⟨code, ⟨length, skeleton⟩⟩
      let buffer := FollowerDownJointMeasurability.bufferFromSkeletonAndScalars
        skeleton values
      have hcode : FollowerDownMeasurability.followerStateCode rate
          (FollowerDownMeasurability.followerStateOfCode rate code buffer) = code := by
        cases code with
        | mk lastDown score lastService backlog status batch failed =>
            fin_cases status <;>
              simp [FollowerDownMeasurability.followerStateCode,
                FollowerDownMeasurability.followerStateOfCode,
                FollowerDownMeasurability.followerStatusCode,
                FollowerDownMeasurability.followerStatusOfCode,
                decoderBatchCode_decoderBatchOfCode]
      have hlength : buffer.length = length := by
        simp [buffer, FollowerDownJointMeasurability.bufferFromSkeletonAndScalars]
      have hbuffer := bufferCodes_ofFn skeleton values
      have hskeleton : HEq (FollowerDownJointMeasurability.bufferSkeletonCode buffer)
          skeleton := by
        simpa only [buffer] using hbuffer.1
      have hvalues : HEq (FollowerDownJointMeasurability.bufferScalarsCode buffer)
          values := by
        simpa only [buffer] using hbuffer.2
      have hindex :
          (FollowerDownMeasurability.followerStateCode rate
            (FollowerDownMeasurability.followerStateOfCode rate code buffer),
            (⟨buffer.length, FollowerDownJointMeasurability.bufferSkeletonCode buffer⟩ :
              Sigma fun n => FollowerDownJointMeasurability.BufferSkeletonCode p n)) =
          (code, (⟨length, skeleton⟩ :
            Sigma fun n => FollowerDownJointMeasurability.BufferSkeletonCode p n)) :=
        Prod.ext hcode (Sigma.ext hlength hskeleton)
      simp only [FollowerObservationStageMeasurabilityRepair.carriedStateOfState,
        FollowerObservationStageMeasurabilityRepair.reconstructCarriedState]
      exact Sigma.ext hindex hvalues

private theorem incomingOfLocalConfiguration_localConfigurationOfIncoming
    (x : FollowerPrepareJointMeasurability.IncomingConfiguration p rate) :
    FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      (FollowerPrepareJointMeasurability.localConfigurationOfIncoming rate x) = x := by
  cases x with
  | none => rfl
  | some data =>
      rcases data with ⟨carry, memory⟩
      simp only [FollowerPrepareJointMeasurability.localConfigurationOfIncoming,
        FollowerPrepareJointMeasurability.incomingOfLocalConfiguration]
      rw [FollowerLifecycleMeasurability.localMemoryCodeOfCode,
        carriedStateOfState_reconstructCarriedState]

/-- The genuine dependent union of the accepted full follower-finish inputs
over every activation label. -/
abbrev VaryingFinishFollowerInput (p : Parameters)
    (rate : RateInput p) :=
  Sigma fun activation : Activation p =>
    ReferenceFollowerTailComposition.FinishFollowerInput p rate activation

/-- Apply the accepted full fixed-activation observable at the label carried
by its input. -/
def varyingFinishFollowerObservable (rate : RateInput p)
    (i : Fin (p.m - 1)) (x : VaryingFinishFollowerInput p rate) :
    ReferenceFollowerTailComposition.FollowerObservable p rate :=
  ReferenceFollowerTailComposition.finishFollowerObservable rate i x.1 x.2

/-- Borel measurability on the standard dependent-union structure, obtained
fiberwise from the unconditional fixed-activation theorem. -/
theorem measurable_varyingFinishFollowerObservable (rate : RateInput p)
    (i : Fin (p.m - 1)) :
    Measurable (varyingFinishFollowerObservable rate i) := by
  intro s hs
  change MeasurableSet[
    (⨅ activation : Activation p,
      (inferInstance : MeasurableSpace
        (ReferenceFollowerTailComposition.FinishFollowerInput p rate activation)).map
          (Sigma.mk activation))]
    {x | varyingFinishFollowerObservable rate i x ∈ s}
  rw [MeasurableSpace.measurableSet_iInf]
  intro activation
  rw [MeasurableSpace.map_def]
  exact ReferenceFollowerTailComposition.measurable_finishFollowerObservable
    rate i activation hs

/-- The canonical whole-step input, using the actual preparation, retained
dispatcher view, and this follower's own simultaneous grid coordinate. -/
def canonicalFinishFollowerInput
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) : VaryingFinishFollowerInput p rate :=
  ⟨x.state.activations i,
    ReferenceFollowerTailComposition.canonicalFollowerInput
      (ReferenceActivePhysicalStep.prepare x) i⟩

/-- Reconstruct exactly the canonical follower observation in the same actual
PREPARE round, including its configuration, failure, logged DOWN input, and
entire DOWN cut. -/
theorem canonicalFinishFollowerInput_reconstruct
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) :
    ReferenceFollowerTailComposition.reconstructFollowerObservable
      (varyingFinishFollowerObservable rate i (canonicalFinishFollowerInput x i)) =
        (ReferenceActivePhysicalStep.prepare x).observeFollower i := by
  exact ReferenceFollowerTailComposition.observeFollowerObservable_reconstruct
    (ReferenceActivePhysicalStep.prepare x) i

/-- Pointwise arbitrary-base reconstruction for the varying-activation
canonical map. The equality is in the original four-field follower
observation, so it retains configuration, failure, logged DOWN input, and the
entire DOWN cut. -/
theorem canonicalFinishFollowerInput_comp_reconstruct
    {Ω : Type*} (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) (ω : Ω) :
    ReferenceFollowerTailComposition.reconstructFollowerObservable
      (varyingFinishFollowerObservable rate i
        (canonicalFinishFollowerInput (input ω) i)) =
      (ReferenceActivePhysicalStep.prepare (input ω)).observeFollower i := by
  exact canonicalFinishFollowerInput_reconstruct (input ω) i

/-- The fixed-activation component is Borel on each genuine activation fiber.
Its row, incoming configuration, calendar time, PREPARE output, view and
feedback are all the actual maps of the supplied measurable round input. -/
private def canonicalFinishFollowerInputOnFiber
    {Ω : Type*} (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) (activation : Activation p)
    (ω : {ω : Ω // (input ω).state.activations i = activation}) :
    ReferenceFollowerTailComposition.FinishFollowerInput p rate activation :=
  let time : FollowerPrepareJointMeasurability.ActiveCalendarTime p activation :=
    ⟨(input ω.1).time, by
      have hactivation : activation.val = ((input ω.1).state.activations i).val :=
        congrArg Subtype.val ω.2.symm
      simpa only [hactivation] using (input ω.1).active i⟩
  ((ReferenceActivePhysicalStep.prepare (input ω.1)).coordinator.downView,
    (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
      (FollowerPrepareJointMeasurability.assemblePrepareInput
        (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
          ((input ω.1).state.followers i)) (input ω.1).row time),
      (ReferenceActivePhysicalStep.prepare (input ω.1)).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)))

private theorem measurable_canonicalFinishFollowerInput_fiber
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : Measurable input)
    (i : Fin (p.m - 1))
    (hview : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).coordinator.downView))
    (hfeedback : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
    (activation : Activation p) :
    Measurable (canonicalFinishFollowerInputOnFiber input i activation) := by
  let fiber := {ω : Ω // (input ω).state.activations i = activation}
  let hcoe : Measurable (fun ω : fiber => (ω.1 : Ω)) := measurable_subtype_coe
  have hincoming : Measurable (fun ω : fiber =>
      FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        ((input ω.1).state.followers i)) := by
    exact (ReferenceActivePhysicalStepMeasurability.measurable_incomingFollower i).comp
      (hinput.comp hcoe)
  have hrow : Measurable (fun ω : fiber => (input ω.1).row) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_row.comp hinput).comp hcoe
  have htimeValue : Measurable (fun ω : fiber => (input ω.1).time) :=
    (ReferenceActivePhysicalStepMeasurability.measurable_time.comp hinput).comp hcoe
  have htimeValid (ω : fiber) :
      activation.val ≤ (input ω.1).time.val + 1 := by
    have hactivation : activation.val = ((input ω.1).state.activations i).val :=
      congrArg Subtype.val ω.2.symm
    simpa only [hactivation] using (input ω.1).active i
  let activeTime (ω : fiber) :
      FollowerPrepareJointMeasurability.ActiveCalendarTime p activation :=
    ⟨(input ω.1).time, htimeValid ω⟩
  have htime : Measurable activeTime := htimeValue.subtype_mk
  have hprepared := FollowerPrepareJointMeasurability.measurable_prepareOutput_atComponents
    rate i activation
    (fun ω : fiber => FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
      ((input ω.1).state.followers i))
    (fun ω : fiber => (input ω.1).row) activeTime hincoming hrow htime
  have hviewFiber : Measurable (fun ω : fiber =>
      (ReferenceActivePhysicalStep.prepare (input ω.1)).coordinator.downView) :=
    hview.comp hcoe
  have hfeedbackFiber : Measurable (fun ω : fiber =>
      (ReferenceActivePhysicalStep.prepare (input ω.1)).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i)) := hfeedback.comp hcoe
  change Measurable (fun ω : fiber =>
    ((ReferenceActivePhysicalStep.prepare (input ω.1)).coordinator.downView,
      (FollowerPrepareJointMeasurability.prepareOutputOnInput rate i activation
        (FollowerPrepareJointMeasurability.assemblePrepareInput
          (FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
            ((input ω.1).state.followers i)) (input ω.1).row (activeTime ω)),
        (ReferenceActivePhysicalStep.prepare (input ω.1)).feedback.feedback
          (PublicDiscreteDraws.followerPlayer p.two_le_m i))))
  have hproduct := hviewFiber.prodMk (hprepared.prodMk hfeedbackFiber)
  simpa [canonicalFinishFollowerInputOnFiber, activeTime] using hproduct

/-- Measurability of the genuine dependent-union canonical input, assembled
on the measurable fibers of the actual varying activation map. -/
theorem measurable_canonicalFinishFollowerInput_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : Measurable input)
    (i : Fin (p.m - 1))
    (hview : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).coordinator.downView))
    (hfeedback : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    Measurable (fun ω => canonicalFinishFollowerInput (input ω) i) := by
  let activation (ω : Ω) : Activation p := (input ω).state.activations i
  let fiberSet (a : Activation p) : Set Ω := {ω | activation ω = a}
  let fiberInput (a : Activation p) (ω : fiberSet a) :
      ReferenceFollowerTailComposition.FinishFollowerInput p rate a :=
    canonicalFinishFollowerInputOnFiber input i a ω
  let fiberMap (a : Activation p) (ω : fiberSet a) :
      VaryingFinishFollowerInput p rate := ⟨a, fiberInput a ω⟩
  have hactivation : Measurable activation :=
    (ReferenceActivePhysicalStepMeasurability.measurable_activation i).comp hinput
  have hset (a : Activation p) : MeasurableSet (fiberSet a) := by
    exact (measurableSet_singleton a).preimage hactivation
  have hfiber (a : Activation p) : Measurable (fiberInput a) := by
    exact measurable_canonicalFinishFollowerInput_fiber input hinput i hview hfeedback a
  have hfiberMap (a : Activation p) : Measurable (fiberMap a) := by
    have hinclusion : Measurable
        (Sigma.mk a : ReferenceFollowerTailComposition.FinishFollowerInput p rate a →
          VaryingFinishFollowerInput p rate) := by
      rw [measurable_iff_le_map]
      change (⨅ b : Activation p,
        (inferInstance : MeasurableSpace
          (ReferenceFollowerTailComposition.FinishFollowerInput p rate b)).map
            (Sigma.mk b)) ≤ _
      exact iInf_le _ a
    exact hinclusion.comp (hfiber a)
  have hagree : ∀ (a b : Activation p) (ω : Ω)
      (ha : ω ∈ fiberSet a) (hb : ω ∈ fiberSet b),
      fiberMap a ⟨ω, ha⟩ = fiberMap b ⟨ω, hb⟩ := by
    intro a b ω ha hb
    have hab : a = b := ha.symm.trans hb
    cases hab
    exact congrArg (fiberMap a) (Subtype.ext rfl)
  have hcover : Set.univ ⊆ ⋃ a : Activation p, fiberSet a := by
    intro ω _
    exact Set.mem_iUnion.mpr ⟨activation ω, rfl⟩
  have hLift : Measurable
      (Set.iUnionLift fiberSet fiberMap hagree Set.univ hcover) :=
    measurable_iUnionLift hagree hcover hset hfiberMap
  have hinclusion : Measurable (fun ω : Ω =>
      (⟨ω, Set.mem_univ ω⟩ : Set.univ)) :=
    measurable_id.subtype_mk (h := fun _ => Set.mem_univ _)
  have hassembled : Measurable (fun ω : Ω =>
      Set.iUnionLift fiberSet fiberMap hagree Set.univ hcover
        ⟨ω, Set.mem_univ ω⟩) := hLift.comp hinclusion
  have heq : (fun ω => canonicalFinishFollowerInput (input ω) i) =
      (fun ω : Ω => Set.iUnionLift fiberSet fiberMap hagree Set.univ hcover
        ⟨ω, Set.mem_univ ω⟩) := by
    funext ω
    rw [Set.iUnionLift_of_mem (⟨ω, Set.mem_univ ω⟩ : Set.univ)
      (show ω ∈ fiberSet (activation ω) from rfl)]
    change (⟨activation ω,
      fiberInput (activation ω) ⟨ω, rfl⟩⟩ : VaryingFinishFollowerInput p rate) =
      ⟨activation ω, ReferenceFollowerTailComposition.canonicalFollowerInput
        (ReferenceActivePhysicalStep.prepare (input ω)) i⟩
    apply congrArg (Sigma.mk (activation ω))
    simp [activation, fiberInput, canonicalFinishFollowerInputOnFiber,
      ReferenceFollowerTailComposition.canonicalFollowerInput]
  rw [heq]
  exact hassembled

/-- The canonical whole-step observable is Borel for an arbitrary measurable
base and measurable actual round-input map. Only the actual dispatcher view
and own simultaneous grid-feedback maps remain conditional inputs. -/
theorem measurable_observeFollowerObservable_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : Measurable input)
    (i : Fin (p.m - 1))
    (hview : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).coordinator.downView))
    (hfeedback : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    Measurable (fun ω =>
      ReferenceFollowerTailComposition.observeFollowerObservable
        (ReferenceActivePhysicalStep.prepare (input ω)) i) := by
  have hcanonical := measurable_canonicalFinishFollowerInput_comp input hinput i hview hfeedback
  have hobservable :=
    (measurable_varyingFinishFollowerObservable rate i).comp hcanonical
  convert hobservable using 1
  funext ω
  rfl

/-- Identity-map specialization of the canonical composer on the existing
time-valid `RoundInput` carrier. -/
theorem measurable_observeFollowerObservable
    (i : Fin (p.m - 1))
    (hview : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare x).coordinator.downView))
    (hfeedback : Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      (ReferenceActivePhysicalStep.prepare x).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    Measurable (fun x : ReferenceActivePhysicalStep.RoundInput p rate =>
      ReferenceFollowerTailComposition.observeFollowerObservable
        (ReferenceActivePhysicalStep.prepare x) i) :=
  measurable_observeFollowerObservable_comp (input := id) measurable_id i hview hfeedback

/-- The follower-configuration component already present in the accepted
successor `StateCode`. -/
def successorFollowerConfigurationCode
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (i : Fin (p.m - 1)) :
    FollowerPrepareJointMeasurability.IncomingConfiguration p rate :=
  (ReferenceActivePhysicalStepMeasurability.successorCode x).2.2.2 i

/-- The actual successor follower code is the first, lossless field of the
canonical follower observable; hence its measurability follows from the same
two-producer composition. -/
theorem measurable_successorFollowerConfigurationCode_comp
    {Ω : Type*} [MeasurableSpace Ω]
    (input : Ω → ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : Measurable input)
    (i : Fin (p.m - 1))
    (hview : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).coordinator.downView))
    (hfeedback : Measurable (fun ω =>
      (ReferenceActivePhysicalStep.prepare (input ω)).feedback.feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))) :
    Measurable (fun ω => successorFollowerConfigurationCode (input ω) i) := by
  have hobservable := measurable_observeFollowerObservable_comp input hinput i hview hfeedback
  have hcode (x : ReferenceActivePhysicalStep.RoundInput p rate) :
      successorFollowerConfigurationCode x i =
        (ReferenceFollowerTailComposition.observeFollowerObservable
          (ReferenceActivePhysicalStep.prepare x) i).1 := by
    change FollowerPrepareJointMeasurability.incomingOfLocalConfiguration rate
        ((ReferenceActivePhysicalStep.step x).next.followers i) = _
    rw [(ReferenceActivePhysicalStep.step_next_fields x).2.2.2 i]
    have hdecode :=
      ReferenceFollowerTailComposition.observeFollowerObservable_reconstruct
        (ReferenceActivePhysicalStep.prepare x) i
    have hconfig := congrArg ReferenceActivePhysicalStep.FollowerObservation.configuration hdecode
    rw [← hconfig]
    exact incomingOfLocalConfiguration_localConfigurationOfIncoming
      ((ReferenceFollowerTailComposition.observeFollowerObservable
        (ReferenceActivePhysicalStep.prepare x) i).1)
  have heq : (fun ω => successorFollowerConfigurationCode (input ω) i) =
      (fun ω =>
        (ReferenceFollowerTailComposition.observeFollowerObservable
          (ReferenceActivePhysicalStep.prepare (input ω)) i).1) := by
    funext ω
    exact hcode (input ω)
  rw [heq]
  exact (measurable_fst.comp hobservable)

end Bandits.Support.ReferenceFollowerVaryingFinishMeasurability

end
