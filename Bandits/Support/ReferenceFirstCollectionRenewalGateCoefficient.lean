/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalControlFactor
public import Bandits.Support.ReferenceFirstCollectionRenewalCoordinatorGate

/-!
# One actual complement coordinator gate at the first renewal

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-423`,
`sources/zip4/manuscript/05_binary_transport.tex:352-423`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-215`.

The event below reads the original auxiliary slow set, the actual prechoice
weights, and the inserted physical control. The retained field keeps the
erased original source, the whole auxiliary array, and both entire assignment
vectors. All measures are the existing finite, unnormalized renewal pair law.
No manuscript filtration, reward identity, or main theorem is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw
  (renewalCallParameter renewalAuxiliarySample renewalCallEvent)
open Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling
  (pairLaw)
open Bandits.Support.ReferenceFirstCollectionRenewalControlFactor
  (retainedControlCoordinates insertedControlRemainder)
open Bandits.Support.ReferenceFirstCollectionRenewalPastLocality
  (renewalSourceWithSuffix)
open Bandits.Support.LaunchAssignmentCoordinateSplit
open Bandits.Support.ContinuousControlSlice
open Bandits.Support.CanonicalRecordingSlice

namespace Bandits.Support.ReferenceFirstCollectionRenewalGateCoefficient

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : ConstructorDimensions.Parameters}
local instance slowSetMeasurableSpace :
    MeasurableSpace (ReferenceFirstCollectionRenewalAuxiliaryLaw.SlowSet p) := ⊤
local instance slowSetDiscrete :
    DiscreteMeasurableSpace (ReferenceFirstCollectionRenewalAuxiliaryLaw.SlowSet p) :=
  ⟨fun _ => trivial⟩

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)

local notation "Z" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.Source rate rewards C_star C_h u t
local notation "B" =>
  ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
local notation "H" => ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p
local notation "O" => ReferenceFirstCollectionRenewalControlFactor.Remainder p
local notation "mu" => pairLaw rate rewards C_star C_h u t

/-- The actual coordinator pilot gate on a complement arm at the renewal call.
The slow set uses the whole original auxiliary array and the weight selector
is evaluated on the original source. -/
def gateEvent (j : Fin p.K) : Set B :=
  {b | j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2).val ∧
    pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) j
      (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 j /
        pilotRecordingGateRawProbability (K := p.K)
          (ActiveRoundActions.coordinator p.two_le_m))
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1}

/-- The literal complement recording coefficient, with zero precisely when
the original auxiliary slow set contains the arm. -/
def coefficient (j : Fin p.K) (b : B) : ℝ :=
  if j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2).val then
    CanonicalRecordingRates.xi p rate.eta.val
      (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 j
  else 0

private theorem measurable_selectedVector :
    Measurable (ReferenceFirstCollectionRenewalVectorInsertion.av (p := p) t) := by
  have hq : Measurable
      (ReferenceFirstCollectionRenewalVectorInsertion.q (p := p)) :=
    BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p
  have hrows : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p => source.1.2) :=
    measurable_snd.comp measurable_fst
  have hselected : Measurable
      (fun source : BootstrapPrivateRoundStreams.SourceInput p =>
        source.1.2 (ReferenceFirstCollectionRenewalVectorInsertion.q source)) :=
    (measurable_from_prod_countable_right
      (f := fun z : Fin (ConstructorDimensions.M p) ×
        BootstrapPrivateRoundStreams.SourceInput p => z.2.1.2 z.1)
      (fun j => (measurable_pi_apply j).comp hrows)).comp
        (hq.prodMk measurable_id)
  exact (LaterAssignmentStartMeasurability.measurable_ownAssignmentVector t).comp
    hselected

/-- Measurability is reproved from the exposed literal coordinates. -/
theorem measurable_retainedControlCoordinates (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (retainedControlCoordinates rate rewards C_star C_h u t control0) := by
  have hz : Measurable (fun b : B => b.1.1.val) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
  have he := (ReferenceSourceCurrentControlFreshness.measurable_c_t
    (p := p) control0 t).comp hz
  have ha : Measurable (fun b : B => b.1.2) := measurable_snd.comp measurable_fst
  have hv := (measurable_selectedVector (p := p) t).comp hz
  have hv' := (measurable_selectedVector (p := p) t).comp
    (measurable_subtype_coe.comp (measurable_snd : Measurable (fun b : B => b.2)))
  exact ((he.prodMk ha).prodMk hv).prodMk hv'

/-- This is the complete non-assignment scalar and affine remainder. -/
theorem measurable_insertedControlRemainder :
    Measurable (insertedControlRemainder rate rewards C_star C_h u t) := by
  exact measurable_snd.comp
    ((controlAssignmentSplitEquiv p).measurable.comp
      ((ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t).comp
        (measurable_subtype_coe.comp measurable_snd)))

private theorem measurable_rate (j : Fin p.K) :
    Measurable (fun v : Fin p.K → ℝ => CanonicalRecordingRates.xi p rate.eta.val v j) := by
  have hprod (S : Finset (Fin p.K)) :
      Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.setWeight v S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun v : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight v)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hprod S)
  have htheta : Measurable (fun v : Fin p.K → ℝ => ProductSetLaw.theta p.m v j) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    unfold FiniteNormalization.normalizedWeight
    exact (hprod S).div htotal
  have hf : Measurable (fun v : Fin p.K → ℝ => CanonicalRecordingRates.f p v j) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  exact AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
    (measurable_const.max hf)

private theorem measurable_varying_gate {α : Type*} [MeasurableSpace α]
    (j : Fin p.K) (v : α → Fin p.K → ℝ)
    (x : α → ContinuousControlSlice.Slice p.m p.K)
    (hv : Measurable v) (hx : Measurable x) :
    MeasurableSet {a | pilotRecordingGate p.two_le_m p.m_lt_K
      (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m) j
      (CanonicalRecordingRates.xi p rate.eta.val (v a) j /
        pilotRecordingGateRawProbability (K := p.K)
          (ActiveRoundActions.coordinator p.two_le_m)) (x a)} := by
  have hslot := (PublicDiscreteDraws.measurable_slotDraw (m := p.m) (K := p.K)).comp hx
  have hrec := (PublicDiscreteDraws.measurable_recorderSourceDraw p.two_le_m p.m_lt_K).comp hx
  have hpilot (i : Fin p.m) :=
    (PublicDiscreteDraws.measurable_pilotDraw (ConstructorDimensions.K_pos p) i).comp hx
  have hmask : MeasurableSet {a | recordingMask (ConstructorDimensions.K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) j (x a)} := by
    simp only [recordingMask, Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
      ((measurableSet_singleton j).preimage (hpilot i)).compl))
  exact ((hslot (measurableSet_singleton _)).inter
    ((hrec (measurableSet_singleton _)).inter
      ((hpilot _ (measurableSet_singleton _)).inter
        (hmask.inter (measurableSet_le
          (measurable_subtype_coe.comp ((measurable_coordinate Label.thin).comp hx))
          (((measurable_rate rate j).comp hv).div_const _))))))

theorem measurableSet_gateEvent (j : Fin p.K) :
    MeasurableSet (gateEvent rate rewards C_star C_h u t j) := by
  have hU := (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalAuxiliarySample
    rate rewards C_star C_h u t).comp (measurable_fst : Measurable (fun b : B => b.1))
  have hslow : MeasurableSet {b : B |
      j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2).val} :=
    (Set.to_countable {U : ReferenceFirstCollectionRenewalAuxiliaryLaw.SlowSet p |
      j ∉ U.val}).measurableSet.preimage hU
  exact hslow.inter (measurable_varying_gate rate j _ _
    (measurable_snd.comp
      ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalCallParameter
        rate rewards C_star C_h u t).comp (measurable_fst.comp measurable_fst)))
    (measurable_fst.comp
      ((ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t).comp
        (measurable_subtype_coe.comp measurable_snd))))

theorem measurable_coefficient (j : Fin p.K) :
    Measurable (coefficient rate rewards C_star C_h u t j) := by
  have hU := (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalAuxiliarySample
    rate rewards C_star C_h u t).comp (measurable_fst : Measurable (fun b : B => b.1))
  exact Measurable.ite ((Set.to_countable
    {U : ReferenceFirstCollectionRenewalAuxiliaryLaw.SlowSet p | j ∉ U.val}).measurableSet.preimage hU)
    ((measurable_rate rate j).comp
      (measurable_snd.comp
        ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalCallParameter
          rate rewards C_star C_h u t).comp (measurable_fst.comp measurable_fst))))
    measurable_const

private def erasedSource (control0 : ContinuousLearningRows.TimeControl p) (z : Z) : Z :=
  renewalSourceWithSuffix rate rewards C_star C_h u t z (fun _ => control0)

private theorem erasedSource_val (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    (erasedSource rate rewards C_star C_h u t control0 z).val =
      ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val := rfl

/-- Both the complete actual parameter and the actual auxiliary sample factor
through the erased source, without changing any auxiliary coordinate. -/
theorem erased_parameter_and_sample (control0 : ContinuousLearningRows.TimeControl p)
    (z : Z) (a : ReferenceFirstCollectionRenewalAuxiliaryLaw.AuxiliaryArray p) :
    renewalCallParameter rate rewards C_star C_h u t z =
        renewalCallParameter rate rewards C_star C_h u t
          (renewalSourceWithSuffix rate rewards C_star C_h u t z (fun _ => control0)) ∧
      renewalAuxiliarySample rate rewards C_star C_h u t z a =
        renewalAuxiliarySample rate rewards C_star C_h u t
          (renewalSourceWithSuffix rate rewards C_star C_h u t z (fun _ => control0)) a :=
  ⟨ReferenceFirstCollectionRenewalPastLocality.renewalCallParameter_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z (fun _ => control0),
    ReferenceFirstCollectionRenewalPastLocality.renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z (fun _ => control0) a⟩

/-- The coefficient is measurable in precisely the field generated by the
specified retained coordinates. Renewal-event membership of the erased
source is supplied by public suffix locality, rather than assumed adaptation. -/
theorem measurable_coefficient_retained (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin p.K) :
    Measurable[(inferInstance : MeasurableSpace H).comap
      (retainedControlCoordinates rate rewards C_star C_h u t control0)]
      (coefficient rate rewards C_star C_h u t j) := by
  let m := (inferInstance : MeasurableSpace H).comap
    (retainedControlCoordinates rate rewards C_star C_h u t control0)
  have hR : Measurable[m]
      (retainedControlCoordinates rate rewards C_star C_h u t control0) :=
    comap_measurable _
  have hz : Measurable[m]
      (fun b : B => erasedSource rate rewards C_star C_h u t control0 b.1.1) := by
    apply Measurable.subtype_mk
    exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).comp hR
  have ha : Measurable[m] (fun b : B => b.1.2) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).comp hR
  have hU := (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalAuxiliarySample
    rate rewards C_star C_h u t).comp (hz.prodMk ha)
  have hv := measurable_snd.comp
    ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalCallParameter
      rate rewards C_star C_h u t).comp hz)
  have he : Measurable[m] (fun b : B =>
      if j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t
          (erasedSource rate rewards C_star C_h u t control0 b.1.1) b.1.2).val then
        CanonicalRecordingRates.xi p rate.eta.val
          (renewalCallParameter rate rewards C_star C_h u t
            (erasedSource rate rewards C_star C_h u t control0 b.1.1)).2 j else 0) :=
    Measurable.ite ((Set.to_countable
      {U : ReferenceFirstCollectionRenewalAuxiliaryLaw.SlowSet p | j ∉ U.val}).measurableSet.preimage hU)
      ((measurable_rate rate j).comp hv) measurable_const
  convert he using 1
  funext b
  rcases erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2
    with ⟨hv', hU'⟩
  change (if _ then _ else _) = _
  rw [hv', hU']
  rfl

private theorem split_symm_nonAssignment (v : CheckedAssignmentSample.AssignmentVector p)
    (o : NonAssignmentScalars p) (label : NonAssignmentLabel p) :
    ((sliceAssignmentSplitEquiv p).symm (v, o)) label.val = o label := by
  change ((sliceAssignmentSplitEquiv p)
    ((sliceAssignmentSplitEquiv p).symm (v, o))).2 label = o label
  rw [(sliceAssignmentSplitEquiv p).apply_symm_apply]

private theorem gate_eq_of_nonAssignment (j : Fin p.K) (a : ℝ)
    (x y : ContinuousControlSlice.Slice p.m p.K)
    (h : ∀ label : NonAssignmentLabel p, x label.val = y label.val) :
    pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j a x ↔
      pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j a y := by
  have hs : x Label.slot = y Label.slot := h ⟨Label.slot, by
    simp [Label.slot, Label.assign]⟩
  have hr : x Label.rec = y Label.rec := h ⟨Label.rec, by
    simp [Label.rec, Label.assign]⟩
  have ht : x Label.thin = y Label.thin := h ⟨Label.thin, by
    simp [Label.thin, Label.assign]⟩
  have hp (i : Fin p.m) : x (Label.pilot i) = y (Label.pilot i) :=
    h ⟨Label.pilot i, by simp [Label.pilot, Label.assign]⟩
  simp only [pilotRecordingGate, recordingMask, PublicDiscreteDraws.slotDraw,
    PublicDiscreteDraws.recorderSourceDraw, PublicDiscreteDraws.pilotDraw,
    ContinuousControlSlice.coordinate, hs, hr, ht, hp]

private theorem remainder_gate_mass (z : Z) (j : Fin p.K)
    (v : CheckedAssignmentSample.AssignmentVector p) :
    ((nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))
      {o : O | pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j
        (CanonicalRecordingRates.xi p rate.eta.val
          (renewalCallParameter rate rewards C_star C_h u t z).2 j /
          pilotRecordingGateRawProbability (K := p.K)
            (ActiveRoundActions.coordinator p.two_le_m))
        ((sliceAssignmentSplitEquiv p).symm (v, o.1))} =
      ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t z).2 j) := by
  let a := CanonicalRecordingRates.xi p rate.eta.val
    (renewalCallParameter rate rewards C_star C_h u t z).2 j /
      pilotRecordingGateRawProbability (K := p.K)
        (ActiveRoundActions.coordinator p.two_le_m)
  let G : Set (NonAssignmentScalars p) := {o |
    pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) j a
      ((sliceAssignmentSplitEquiv p).symm (v, o))}
  have hG : MeasurableSet G :=
    (measurableSet_pilotRecordingGate p.two_le_m p.m_lt_K
      (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m) j a).preimage
      ((sliceAssignmentSplitEquiv p).symm.measurable.comp
        (measurable_const.prodMk measurable_id))
  have hpre : (sliceAssignmentSplitEquiv p) ⁻¹' (Set.univ ×ˢ G) =
      {x | pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) j a x} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
    apply gate_eq_of_nonAssignment
    intro label
    rw [split_symm_nonAssignment]
    rfl
  have hmass : (nonAssignmentScalarLaw p) G =
      ENNReal.ofReal (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t z).2 j) := by
    have hmap := (measurePreserving_sliceAssignmentSplitEquiv p).map_eq
    have heval := congrArg (fun ν => ν (Set.univ ×ˢ G)) hmap
    rw [Measure.map_apply (sliceAssignmentSplitEquiv p).measurable
      (MeasurableSet.univ.prod hG), hpre, Measure.prod_prod] at heval
    simpa only [measure_univ, one_mul] using heval.symm.trans
      (canonical_pilotRecordingGate_mass p rate.eta.property rate.sourceCap _
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewal_parameter_spec
          rate rewards C_star C_h u t z).1 _ j)
  have hevent : {o : O | pilotRecordingGate p.two_le_m p.m_lt_K
      (ConstructorDimensions.K_pos p) (ActiveRoundActions.coordinator p.two_le_m) j a
      ((sliceAssignmentSplitEquiv p).symm (v, o.1))} = G ×ˢ Set.univ := by
    ext o
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    rfl
  change ((nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))
    {o : O | pilotRecordingGate _ _ _ _ j a _} = _
  rw [hevent, Measure.prod_prod, measure_univ, mul_one, hmass]

-- The following sets live on the existing retained-coordinate/remainder
-- product. The subtype only supplies renewal-event membership of its raw
-- source coordinate. Its image is an event, never a new probability law or
-- a totalized sampler outside the renewal domain.
private def validCoordinates : Set (H × O) :=
  {w | w.1.1.1.1 ∈ renewalCallEvent rate rewards C_star C_h u t}

private def coordinateSource
    (w : validCoordinates rate rewards C_star C_h u t) : Z :=
  ⟨w.val.1.1.1.1, w.property⟩

private def coordinateGate (j : Fin p.K) :
    Set (validCoordinates rate rewards C_star C_h u t) :=
  {w | j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t
      (coordinateSource rate rewards C_star C_h u t w) w.val.1.1.1.2).val ∧
    pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
      (ActiveRoundActions.coordinator p.two_le_m) j
      (CanonicalRecordingRates.xi p rate.eta.val
        (renewalCallParameter rate rewards C_star C_h u t
          (coordinateSource rate rewards C_star C_h u t w)).2 j /
        pilotRecordingGateRawProbability (K := p.K)
          (ActiveRoundActions.coordinator p.two_le_m))
      ((sliceAssignmentSplitEquiv p).symm (w.val.1.2, w.val.2.1))}

private def jointGate (j : Fin p.K) : Set (H × O) :=
  Subtype.val '' coordinateGate rate rewards C_star C_h u t j

private theorem measurableSet_validCoordinates :
    MeasurableSet (validCoordinates rate rewards C_star C_h u t) :=
  (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
    rate rewards C_star C_h u t).preimage (by
      exact measurable_fst.comp (measurable_fst.comp
        (measurable_fst.comp measurable_fst)))

private theorem measurableSet_jointGate (j : Fin p.K) :
    MeasurableSet (jointGate rate rewards C_star C_h u t j) := by
  have hz : Measurable (coordinateSource rate rewards C_star C_h u t) := by
    apply Measurable.subtype_mk
    exact (measurable_fst.comp (measurable_fst.comp
      (measurable_fst.comp measurable_fst))).comp measurable_subtype_coe
  have ha : Measurable (fun w : validCoordinates rate rewards C_star C_h u t =>
      w.val.1.1.1.2) := by fun_prop
  have hU := (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalAuxiliarySample
    rate rewards C_star C_h u t).comp (hz.prodMk ha)
  have hv := measurable_snd.comp
    ((ReferenceFirstCollectionRenewalAuxiliaryLaw.measurable_renewalCallParameter
      rate rewards C_star C_h u t).comp hz)
  have hx : Measurable (fun w : validCoordinates rate rewards C_star C_h u t =>
      (sliceAssignmentSplitEquiv p).symm (w.val.1.2, w.val.2.1)) := by fun_prop
  exact (MeasurableEmbedding.subtype_coe
    (measurableSet_validCoordinates rate rewards C_star C_h u t)).measurableSet_image.mpr
      (((Set.to_countable
        {U : ReferenceFirstCollectionRenewalAuxiliaryLaw.SlowSet p | j ∉ U.val}).measurableSet.preimage hU).inter
        (measurable_varying_gate rate j _ _ hv hx))

private theorem jointGate_mem_iff (j : Fin p.K) (w : H × O)
    (hw : w ∈ validCoordinates rate rewards C_star C_h u t) :
    w ∈ jointGate rate rewards C_star C_h u t j ↔
      (⟨w, hw⟩ : validCoordinates rate rewards C_star C_h u t) ∈
        coordinateGate rate rewards C_star C_h u t j := by
  constructor
  · rintro ⟨a, ha, heq⟩
    have he : a = ⟨w, hw⟩ := Subtype.ext heq
    exact he ▸ ha
  · intro h
    exact ⟨⟨w, hw⟩, h, rfl⟩

private theorem retained_valid (control0 : ContinuousLearningRows.TimeControl p)
    (b : B) (o : O) :
    (retainedControlCoordinates rate rewards C_star C_h u t control0 b, o) ∈
      validCoordinates rate rewards C_star C_h u t :=
  (erasedSource rate rewards C_star C_h u t control0 b.1.1).property

private theorem gateEvent_eq_joint_preimage (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin p.K) :
    gateEvent rate rewards C_star C_h u t j =
      (fun b : B => (retainedControlCoordinates rate rewards C_star C_h u t control0 b,
        insertedControlRemainder rate rewards C_star C_h u t b)) ⁻¹'
          jointGate rate rewards C_star C_h u t j := by
  ext b
  rw [Set.mem_preimage, jointGate_mem_iff rate rewards C_star C_h u t j _
    (retained_valid rate rewards C_star C_h u t control0 b _)]
  have hs : (sliceAssignmentSplitEquiv p).symm
      ((retainedControlCoordinates rate rewards C_star C_h u t control0 b).2,
        (insertedControlRemainder rate rewards C_star C_h u t b).1) =
      (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1 := by
    change (sliceAssignmentSplitEquiv p).symm
      ((sliceAssignmentSplitEquiv p)
        (ReferenceFirstCollectionRenewalVectorInsertion.c t b.2.val).1) = _
    exact (sliceAssignmentSplitEquiv p).symm_apply_apply _
  rcases erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2
    with ⟨hv, hU⟩
  change (_ ∧ _) ↔ (_ ∧ _)
  change (j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2).val ∧ _) ↔
    (j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t
      (erasedSource rate rewards C_star C_h u t control0 b.1.1) b.1.2).val ∧ _)
  rw [hU, hv, hs]
  rfl

private theorem jointGate_section_mass (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin p.K) (b : B) :
    ((nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p))
      {o : O | (retainedControlCoordinates rate rewards C_star C_h u t control0 b, o) ∈
        jointGate rate rewards C_star C_h u t j} =
      ENNReal.ofReal (coefficient rate rewards C_star C_h u t j b) := by
  have hmem (o : O) := jointGate_mem_iff rate rewards C_star C_h u t j
    (retainedControlCoordinates rate rewards C_star C_h u t control0 b, o)
    (retained_valid rate rewards C_star C_h u t control0 b o)
  rcases erased_parameter_and_sample rate rewards C_star C_h u t control0 b.1.1 b.1.2
    with ⟨hv, hU⟩
  have hevent : {o : O |
      (retainedControlCoordinates rate rewards C_star C_h u t control0 b, o) ∈
        jointGate rate rewards C_star C_h u t j} =
      {o : O | j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2).val ∧
        pilotRecordingGate p.two_le_m p.m_lt_K (ConstructorDimensions.K_pos p)
          (ActiveRoundActions.coordinator p.two_le_m) j
          (CanonicalRecordingRates.xi p rate.eta.val
            (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 j /
            pilotRecordingGateRawProbability (K := p.K)
              (ActiveRoundActions.coordinator p.two_le_m))
          ((sliceAssignmentSplitEquiv p).symm
            (ReferenceFirstCollectionRenewalVectorInsertion.av t b.2.val, o.1))} := by
    ext o
    simp only [Set.mem_ofPred_eq]
    rw [hmem o]
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [hv, hU]
    rfl
  rw [hevent]
  by_cases hj : j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2).val
  · simp only [coefficient, hj, not_false_eq_true, true_and, ite_true]
    exact remainder_gate_mass rate rewards C_star C_h u t b.1.1 j _
  · simp only [hj, false_and, Set.ofPred_false, measure_empty, coefficient, ite_false,
      ENNReal.ofReal_zero]

/-- Every Borel retained-coordinate cylinder has the literal gate coefficient
under the same finite, unnormalized pair law on both sides. This also applies
when the renewal-event restriction has zero mass. -/
theorem gate_cylinder (control0 : ContinuousLearningRows.TimeControl p)
    (j : Fin p.K) (Hset : Set H) (hHset : MeasurableSet Hset) :
    mu {b | retainedControlCoordinates rate rewards C_star C_h u t control0 b ∈ Hset ∧
      b ∈ gateEvent rate rewards C_star C_h u t j} =
      ∫⁻ b in {b | retainedControlCoordinates rate rewards C_star C_h u t control0 b ∈ Hset},
        ENNReal.ofReal (coefficient rate rewards C_star C_h u t j b) ∂mu := by
  let R := retainedControlCoordinates rate rewards C_star C_h u t control0
  let Q := fun b : B => (R b, insertedControlRemainder rate rewards C_star C_h u t b)
  let rho := (nonAssignmentScalarLaw p).prod (ContinuousLearningRows.affineSamplesLaw p)
  let Dset : Set (H × O) := (Hset ×ˢ Set.univ) ∩
    jointGate rate rewards C_star C_h u t j
  have hR : Measurable R := measurable_retainedControlCoordinates
    rate rewards C_star C_h u t control0
  have hQ : Measurable Q := hR.prodMk
    (measurable_insertedControlRemainder rate rewards C_star C_h u t)
  have hD : MeasurableSet Dset :=
    (hHset.prod MeasurableSet.univ).inter
      (measurableSet_jointGate rate rewards C_star C_h u t j)
  have hevent : {b | R b ∈ Hset ∧ b ∈ gateEvent rate rewards C_star C_h u t j} =
      Q ⁻¹' Dset := by
    rw [gateEvent_eq_joint_preimage rate rewards C_star C_h u t control0 j]
    ext b
    simp only [Dset, Q, R, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_ofPred_eq]
  have hsection : Measurable (fun h : H => rho (Prod.mk h ⁻¹' Dset)) :=
    measurable_measure_prodMk_left hD
  calc
    _ = ((mu).map Q) Dset := by rw [Measure.map_apply hQ hD]; exact congrArg mu hevent
    _ = (((mu).map R).prod rho) Dset := by
      rw [ReferenceFirstCollectionRenewalControlFactor.pairLaw_retained_nonAssignment_product
        rate rewards C_star C_h u t control0]
    _ = ∫⁻ h, rho (Prod.mk h ⁻¹' Dset) ∂((mu).map R) := Measure.prod_apply hD
    _ = ∫⁻ b, rho (Prod.mk (R b) ⁻¹' Dset) ∂mu := lintegral_map hsection hR
    _ = ∫⁻ b, {b : B | R b ∈ Hset}.indicator
        (fun b => ENNReal.ofReal (coefficient rate rewards C_star C_h u t j b)) b ∂mu := by
      apply lintegral_congr
      intro b
      by_cases hb : R b ∈ Hset
      · rw [Set.indicator_of_mem (show b ∈ {b : B | R b ∈ Hset} from hb)]
        have he : Prod.mk (R b) ⁻¹' Dset =
            {o : O | (R b, o) ∈ jointGate rate rewards C_star C_h u t j} := by
          ext o
          simp only [Dset, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
            hb, Set.mem_univ, and_self, true_and, Set.mem_ofPred_eq]
        rw [he]
        exact jointGate_section_mass rate rewards C_star C_h u t control0 j b
      · rw [Set.indicator_of_notMem (show b ∉ {b : B | R b ∈ Hset} from hb)]
        have he : Prod.mk (R b) ⁻¹' Dset = ∅ := by
          ext o
          simp only [Dset, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod,
            hb, false_and, Set.notMem_empty]
        rw [he, measure_empty]
    _ = _ := lintegral_indicator (hHset.preimage hR) _

private theorem actual_call_slice (z : Z)
    (d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
      rate rewards C_star C_h u t z) :
    (ReferenceFirstCollectionRenewalVectorInsertion.c t z.val).1 =
      ContinuousLearningRows.sliceAt d.record.input.time d.record.input.row.2 := by
  have hm := d.record_mem
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z.val rewards C_star C_h with
  | none =>
    simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hl,
      dite_true, List.not_mem_nil] at hm
  | some active =>
    rw [ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z.val rewards C_star C_h active hl] at hm
    obtain ⟨hrows, hselected, _⟩ := ReferenceActivePhysicalHorizon.run_record_inputs
      active z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
      rewards _ _ _ _ d.record hm
    have hrow : d.record.input.row =
        z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val) := by
      change d.record.input.rows d.record.input.selected = _
      rw [hrows, hselected]
    rw [hrow, d.time_eq]
    rfl

/-- The very same actual call and recording supplied by the admitted gate
producer have the original prechoice weights and the literal event above.
Input-row identification uses membership in the original complete suffix,
its full row table, and its actual selected index, as well as the timestamp. -/
theorem ae_actual_recording_gate :
    ∀ᵐ b : B ∂mu,
      ∃ d : ReferenceFirstCollectionRenewalAuxiliaryLaw.ActualRenewalCall
          rate rewards C_star C_h u t b.2,
        ∃ recording : CoordinatorRecordingOperation.Output p,
          d.record.output.coordinator.recording = some recording ∧
          (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 =
            AssignmentScoreReconstruction.currentWeight d.out ∧
          ∀ j : Fin p.K, recording.gateArm = some j ↔
            b ∈ gateEvent rate rewards C_star C_h u t j := by
  filter_upwards
    [ReferenceFirstCollectionRenewalCoordinatorGate.ae_pairLaw_actual_coordinator_gate
      rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalInstallationCoupling.ae_pairLaw_chronological_support
        rate rewards C_star C_h u t] with b hgate hchron
  dsimp only at hgate hchron
  rcases hgate with ⟨d, recording, hrecording, hgate⟩
  rcases hchron with ⟨_, _, _, _, _, _, _, _, _, hparameter, _⟩
  have hweight := (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1
  have hw : (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 =
      AssignmentScoreReconstruction.currentWeight d.out :=
    (congrArg Prod.snd hparameter).trans
      ((congrArg Prod.snd d.parameter_eq).trans hweight)
  refine ⟨d, recording, hrecording, hw, ?_⟩
  intro j
  rw [hgate j]
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [hw, actual_call_slice rate rewards C_star C_h u t b.2 d]

end Bandits.Support.ReferenceFirstCollectionRenewalGateCoefficient

end
