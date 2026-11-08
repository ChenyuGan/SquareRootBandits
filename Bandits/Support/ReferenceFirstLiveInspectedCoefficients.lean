/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInspectedGuardReadout

/-!
# Coefficients read from the inspected first-live state

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-348`,
`sources/zip4/manuscript/06_interruptions.tex:391-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

This file reads the five real coefficients from the actual incoming LIVE code
on the existing enlarged analysis field. The coefficients vanish analytically
outside the literal first-live guarded event. No policy or source filtration is
defined here; the result is an internal pointwise readout for the later
conditional-service and waiting arguments.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInspectedCoefficients

abbrev SourceInput := ReferenceFirstLiveGuardedConditionalService.SourceInput

abbrev CoefficientValues := ℝ × (ℝ × (ℝ × (ℝ × ℝ)))

variable {p : Parameters}

def guardedEvent
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) : Set (SourceInput p) :=
  ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
    rate rewards C_star C_h control0 i t q s hs b

private abbrev inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) : MeasurableSpace (SourceInput p) :=
  ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h t.val (le_of_lt t.isLt)

def zeroValues : CoefficientValues := (0, (0, (0, (0, 0))))

/-- The five real coefficients on the original source. Every selector and
validity witness in the live branch is computed from the actual guarded
remainder; the zero branch is an analytic coefficient convention only. -/
noncomputable def firstLiveInspectedCoefficientValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    CoefficientValues := by
  classical
  exact if hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b then
    let branch : z ∈ ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
        rate rewards C_star C_h control0 i t q s hs := hz.1
    let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
      rate rewards C_star C_h control0 i t q s hs z branch
    let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
      rate rewards C_star C_h control0 i t q s hs z branch
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
      rate rewards C_star C_h q t s hs control0 i x hx
    let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
    let payload := selected0.view.payload
    let weights := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0
    let bounds := fun a =>
      ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected0 hvalid a
    let e := ReleaseRoundKernel.auxiliaryFastArm payload.assignment payload.slowSet
      payload.assignment_image.symm
    let qAux := CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
      payload.eta_le_source_cap payload.anchor weights payload.anchor_pos
      (fun a => (bounds a).1) (fun a => (bounds a).2.1) (fun a => (bounds a).2.2)
      payload.slowSet e
    (ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row,
      (ReleaseRoundKernel.chi row (payload.assignment.assigned i) /
        (2 * (p.K : ℝ)),
       (ReleaseRoundKernel.chi row payload.assignment.auxiliary,
        (ReleaseRoundKernel.chi row (payload.assignment.assigned i),
          qAux * ReleaseRoundKernel.chi row payload.assignment.auxiliary))))
  else zeroValues

/-- The actual first-live UP coefficient. On the guarded support it is the
literal slice-mass formula from the selected whole-field baseline. -/
def firstLiveInspectedUpCoefficient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) : ℝ :=
  (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b z).1

/-- The actual first-live DATA coefficient, retaining this follower's assigned
arm index. -/
def firstLiveInspectedDataCoefficient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) : ℝ :=
  (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b z).2.1

/-- The guarded auxiliary reward readout used by finite-support waiting. -/
def firstLiveInspectedAuxiliaryChi
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) : ℝ :=
  (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b z).2.2.1

/-- The guarded assigned-arm reward readout. It is indexed by the actual
follower `i`, not by a shared replacement arm. -/
def firstLiveInspectedAssignedChi
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) : ℝ :=
  (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b z).2.2.2.1

/-- The guarded actual auxiliary-weighted reward `Qe * chi(row,e)`. -/
def firstLiveInspectedAuxiliaryWeightedChi
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) : ℝ :=
  (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b z).2.2.2.2

private def incomingCodeWholeWeights
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (code : ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : Fin p.K → ℝ :=
  fun a => if a ∈ payload.slowSet.val then payload.anchor a
    else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
      (code.scores a)

private def incomingLiveValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (live : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) : CoefficientValues :=
  let payload := live.1
  let code := live.2
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let anchor := AssignmentPayloadDerivedMeasurability.inputAnchor payload
  let weights := incomingCodeWholeWeights payload code
  let auxiliary := AssignmentPayloadDerivedMeasurability.inputAuxiliary payload
  let assigned := payload.assignment.assigned i
  let qAux := ReferenceLiveRecorderJointMeasurability.qGammaAtArm
    (p := p) (rate := rate) payload.slowSet.val (anchor, weights) auxiliary
  (ReleaseRoundKernel.chi row auxiliary * (1 - qAux) /
      (4 * (p.m - 1 : ℝ) * (p.K : ℝ)),
    (ReleaseRoundKernel.chi row assigned / (2 * (p.K : ℝ)),
      (ReleaseRoundKernel.chi row auxiliary,
        (ReleaseRoundKernel.chi row assigned,
          qAux * ReleaseRoundKernel.chi row auxiliary))))

private def incomingStateCodeValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (code : ReferenceActivePhysicalStepMeasurability.StateCode p rate) : CoefficientValues :=
  Sum.elim (fun _ : Unit => zeroValues)
    (Sum.elim (incomingLiveValues rate rewards i t)
      (Sum.elim (fun _ => zeroValues) (fun _ : Unit => zeroValues))) code.1

private def incomingOptionValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) :
    CoefficientValues := (code.map (incomingStateCodeValues rate rewards i t)).getD zeroValues

private theorem measurable_payloadSlowSet
    (rate : ReferenceActivePhysicalStep.RateInput p) :
    Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.slowSet) := by
  have hobs : Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _
  have hval : Measurable (fun payload : ReferenceActivePhysicalStep.Payload rate =>
      payload.slowSet.val) := by
    change Measurable (fun payload : AssignmentStartPayload.Input p rate.eta =>
      (LaterAssignmentStartMeasurability.payloadObservation payload).2.2.1)
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hobs))
  exact hval.subtype_mk

private theorem measurable_incomingLiveValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (incomingLiveValues rate rewards i t) := by
  classical
  let payload := fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.1
  let live := fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.2
  have hslow : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.1.slowSet.val) :=
    measurable_subtype_coe.comp
      ((measurable_payloadSlowSet (p := p) rate).comp measurable_fst)
  have hanchorPayload : Measurable
      (AssignmentPayloadDerivedMeasurability.inputAnchor (p := p) (eta := rate.eta)) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAnchor
  have hanchor : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      AssignmentPayloadDerivedMeasurability.inputAnchor z.1) :=
    hanchorPayload.comp measurable_fst
  have hauxPayload : Measurable
      (AssignmentPayloadDerivedMeasurability.inputAuxiliary (p := p) (eta := rate.eta)) :=
    AssignmentPayloadDerivedMeasurability.measurable_inputAuxiliary
  have haux : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      AssignmentPayloadDerivedMeasurability.inputAuxiliary z.1) :=
    hauxPayload.comp measurable_fst
  have hpayloadSlow : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.1.slowSet) :=
    (measurable_payloadSlowSet (p := p) rate).comp
      (measurable_fst : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.1))
  have hassigned : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => z.1.assignment.assigned i) := by
    have hmap : Measurable (fun U : CanonicalOrientedSetLaw.SlowSet p.K p.m =>
        CanonicalAssignmentVector.followerArm p.two_le_m U i) := Measurable.of_discrete
    have h := hmap.comp hpayloadSlow
    convert h using 1
    funext z
    rfl
  have hweights : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      fun a : Fin p.K =>
        if a ∈ z.1.slowSet.val then
          AssignmentPayloadDerivedMeasurability.inputAnchor z.1 a
        else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (z.2.scores a)) := by
    apply measurable_pi_iff.mpr
    intro a
    have hmemSet : Measurable (fun U : Finset (Fin p.K) => decide (a ∈ U)) :=
      Measurable.of_discrete
    have hmemBool := hmemSet.comp hslow
    have hmem : MeasurableSet {z : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p |
        a ∈ z.1.slowSet.val} := by
      have htrue : Measurable (fun _ : ReferenceActivePhysicalStep.Payload rate ×
          ReferenceActivePhysicalStepMeasurability.LiveDiscrete p => true) := measurable_const
      have heq := measurableSet_eq_fun hmemBool htrue
      simpa only [Function.comp_apply, decide_eq_true_eq] using heq
    have hanarm : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        AssignmentPayloadDerivedMeasurability.inputAnchor z.1 a) :=
      (measurable_pi_apply a).comp hanchor
    have hscore : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (z.2.scores a)) := by
      exact (Measurable.of_discrete (f := fun code :
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (code.scores a))).comp measurable_snd
    have hpiece : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
        if a ∈ z.1.slowSet.val then
          AssignmentPayloadDerivedMeasurability.inputAnchor z.1 a
        else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (z.2.scores a)) := Measurable.ite hmem hanarm hscore
    exact hpiece
  have hvalue : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      (AssignmentPayloadDerivedMeasurability.inputAnchor z.1, fun a : Fin p.K =>
        if a ∈ z.1.slowSet.val then
          AssignmentPayloadDerivedMeasurability.inputAnchor z.1 a
        else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (z.2.scores a))) := hanchor.prodMk hweights
  have hcode : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      (z.1.slowSet.val,
        AssignmentPayloadDerivedMeasurability.inputAuxiliary z.1)) :=
    hslow.prodMk haux
  have hq : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
        z.1.slowSet.val
        (AssignmentPayloadDerivedMeasurability.inputAnchor z.1,
          fun a : Fin p.K =>
            if a ∈ z.1.slowSet.val then
              AssignmentPayloadDerivedMeasurability.inputAnchor z.1 a
            else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
              (z.2.scores a))
        (AssignmentPayloadDerivedMeasurability.inputAuxiliary z.1)) := by
    have hjoint : Measurable (fun z :
        (Finset (Fin p.K) × Fin p.K) ×
          (ReferenceActivePhysicalStep.Payload rate ×
            ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) =>
        ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
          z.1.1 (AssignmentPayloadDerivedMeasurability.inputAnchor z.2.1, fun a : Fin p.K =>
            if a ∈ z.2.1.slowSet.val then
              AssignmentPayloadDerivedMeasurability.inputAnchor z.2.1 a
            else ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
              (z.2.2.scores a)) z.1.2) := by
      apply measurable_from_prod_countable_right
      intro c
      exact (ReferenceLiveRecorderJointMeasurability.measurable_qGammaAtArm
        (p := p) (rate := rate) c.1 c.2).comp hvalue
    exact hjoint.comp (hcode.prodMk measurable_id)
  have hchiAux : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (AssignmentPayloadDerivedMeasurability.inputAuxiliary z.1)) := by
    exact (Measurable.of_discrete (f := fun a : Fin p.K =>
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) a)).comp haux
  have hchiAssigned : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (z.1.assignment.assigned i)) :=
    (Measurable.of_discrete (f := fun a : Fin p.K =>
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t) a)).comp hassigned
  have hfirst : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (AssignmentPayloadDerivedMeasurability.inputAuxiliary z.1) *
      (1 - ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
        z.1.slowSet.val
        (AssignmentPayloadDerivedMeasurability.inputAnchor z.1,
          incomingCodeWholeWeights z.1 z.2)
        (AssignmentPayloadDerivedMeasurability.inputAuxiliary z.1)) /
        (4 * (p.m - 1 : ℝ) * (p.K : ℝ))) := by
    exact hchiAux.mul (measurable_const.sub hq) |>.div_const _
  have hdata : Measurable (fun z : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p =>
      ReleaseRoundKernel.chi
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
        (z.1.assignment.assigned i) / (2 * (p.K : ℝ))) :=
    hchiAssigned.div_const _
  have hweighted := hq.mul hchiAux
  exact hfirst.prodMk (hdata.prodMk (hchiAux.prodMk (hchiAssigned.prodMk hweighted)))

private theorem measurable_incomingStateCodeValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (incomingStateCodeValues rate rewards i t) := by
  have hlive := measurable_incomingLiveValues (p := p) rate rewards i t
  have htail : Measurable (fun v :
      (ReferenceActivePhysicalStep.Payload rate ×
        (ReferenceActivePhysicalStep.Ledger rate ×
          Option (Fin p.T × Bool))) ⊕ Unit => zeroValues) := measurable_const
  have hmiddle : Measurable (fun v :
      (ReferenceActivePhysicalStep.Payload rate ×
        ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) ⊕
        ((ReferenceActivePhysicalStep.Payload rate ×
          (ReferenceActivePhysicalStep.Ledger rate ×
            Option (Fin p.T × Bool))) ⊕ Unit) =>
      Sum.elim (incomingLiveValues rate rewards i t) (fun _ => zeroValues) v) :=
    hlive.sumElim htail
  have hcoord : Measurable (fun v : ReferenceActivePhysicalStepMeasurability.CoordinatorCode p rate =>
      Sum.elim (fun _ : Unit => zeroValues)
        (Sum.elim (incomingLiveValues rate rewards i t)
          (Sum.elim (fun _ => zeroValues) (fun _ : Unit => zeroValues))) v) :=
    measurable_const.sumElim hmiddle
  exact hcoord.comp measurable_fst

private theorem measurable_incomingOptionValues
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (incomingOptionValues rate rewards i t) := by
  have hcode := measurable_incomingStateCodeValues (p := p) rate rewards i t
  have hsum : Measurable
      (Sum.elim (incomingStateCodeValues rate rewards i t)
        (fun _ : PUnit => zeroValues) :
          ReferenceActivePhysicalStepMeasurability.StateCode p rate ⊕ PUnit →
            CoefficientValues) := hcode.sumElim measurable_const
  have h := hsum.comp (comap_measurable
    (Equiv.optionEquivSumPUnit
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate)))
  convert h using 1
  funext code
  cases code <;> rfl

private theorem qGammaAtArm_eq_canonical
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (e : CanonicalFastSampling.FastArm U) :
    ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
      U.val (v, w) e.1 =
    CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
      (by simpa using rate.sourceCap) v w hv hw hvw hwv U e := by
  have he : e.1 ∈ (Finset.univ : Finset (Fin p.K)) \ U.val := e.property
  unfold ReferenceLiveRecorderJointMeasurability.qGammaAtArm
  rw [ite_eq_left he]
  simp only [ReferenceLiveRecorderJointMeasurability.qGammaFormula,
    CanonicalFastSampling.qGamma, FiniteOrientationDisintegration.conditionalFastLaw]

private theorem coefficientValues_eq_incoming_on_guard
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b) :
    firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b z =
      incomingOptionValues rate rewards i t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) := by
  let branch : z ∈ ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
      rate rewards C_star C_h control0 i t q s hs := hz.1
  let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
    rate rewards C_star C_h control0 i t q s hs z branch
  let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
    rate rewards C_star C_h control0 i t q s hs z branch
  let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
    rate rewards C_star C_h q t s hs control0 i x hx
  let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
    rate rewards C_star C_h q t s hs control0 i x hx
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  have hfields := ReferenceFirstLiveInspectedGuardReadout.baseline_fields_eq_incoming
    rate rewards C_star C_h control0 i t q s hs b z hz
  dsimp only at hfields
  rcases hfields with ⟨code, payload, live, hin, hcode, _hdecoded, _htime,
    hpayload, hweights, _htimeAt, _hpending, _hprior, _hcutoff, _hvalid, _hframe⟩
  cases hpayload
  have hregisterWeights : HEq selected0.view.complementWeights
      (ReferenceActivePhysicalStep.liveRegistersAt
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters
          selected0.view.payload live) t).complementWeights := by
    change HEq selected0.view.complementWeights _ at hweights
    exact hweights
  have hregisterWeightsEq : selected0.view.complementWeights =
      (ReferenceActivePhysicalStep.liveRegistersAt
        (ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters
          selected0.view.payload live) t).complementWeights := eq_of_heq hregisterWeights
  have hwhole : ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0 =
      incomingCodeWholeWeights selected0.view.payload live := by
    funext a
    by_cases ha : a ∈ selected0.view.payload.slowSet.val
    · simp [ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
        incomingCodeWholeWeights, ha]
    · let j : CanonicalFastSampling.FastArm selected0.view.payload.slowSet :=
        ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ha⟩⟩
      have hweight := congrFun hregisterWeightsEq j
      have hscore : selected0.view.complementWeights j =
          ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
            (live.scores a) := by
        simpa only [ReferenceActivePhysicalStep.liveRegistersAt,
          CoordinatorLiveChoiceRecorderStep.Registers.complementWeights,
          ReferenceActivePhysicalStepMeasurability.decodeLiveRegisters] using hweight
      simpa [ReferenceFirstLiveReleaseGeometry.completeCurrentWeights,
        incomingCodeWholeWeights, ha, j] using hscore
  have he : (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
      selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm).1 =
        AssignmentPayloadDerivedMeasurability.inputAuxiliary selected0.view.payload := rfl
  have hmem : AssignmentPayloadDerivedMeasurability.inputAuxiliary
      selected0.view.payload ∈ (Finset.univ : Finset (Fin p.K)) \
        selected0.view.payload.slowSet.val := by
    rw [← he]
    exact (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
      selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm).property
  have hq :
      CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
        selected0.view.payload.eta_le_source_cap selected0.view.payload.anchor
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
        selected0.view.payload.anchor_pos
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalid a).1)
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalid a).2.1)
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalid a).2.2)
        selected0.view.payload.slowSet
        (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
          selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm) =
      ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
        selected0.view.payload.slowSet.val
        (AssignmentPayloadDerivedMeasurability.inputAnchor selected0.view.payload,
          incomingCodeWholeWeights selected0.view.payload live)
        (AssignmentPayloadDerivedMeasurability.inputAuxiliary selected0.view.payload) := by
    have hqeq := qGammaAtArm_eq_canonical (p := p) rate selected0.view.payload.slowSet
      selected0.view.payload.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
      selected0.view.payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected0 hvalid a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected0 hvalid a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected0 hvalid a).2.2)
      (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
        selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm)
    have hqAt :
        ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
          selected0.view.payload.slowSet.val
          (selected0.view.payload.anchor,
            ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
          (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
            selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm).1 =
        ReferenceLiveRecorderJointMeasurability.qGammaAtArm (p := p) (rate := rate)
          selected0.view.payload.slowSet.val
          (AssignmentPayloadDerivedMeasurability.inputAnchor selected0.view.payload,
            incomingCodeWholeWeights selected0.view.payload live)
          (AssignmentPayloadDerivedMeasurability.inputAuxiliary selected0.view.payload) := by
      change ReferenceLiveRecorderJointMeasurability.qGammaAtArm
          (p := p) (rate := rate) selected0.view.payload.slowSet.val
          (selected0.view.payload.anchor,
            ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
          (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
            selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm).1 =
        ReferenceLiveRecorderJointMeasurability.qGammaAtArm
          (p := p) (rate := rate) selected0.view.payload.slowSet.val
          (selected0.view.payload.anchor, incomingCodeWholeWeights selected0.view.payload live)
          (ReleaseRoundKernel.auxiliaryFastArm selected0.view.payload.assignment
            selected0.view.payload.slowSet selected0.view.payload.assignment_image.symm).1
      rw [← hwhole]
    exact hqeq.symm.trans hqAt
  simp only [firstLiveInspectedCoefficientValues, dite_eq_left hz]
  simp only [incomingOptionValues, hin, Option.map_some, Option.getD_some,
    incomingStateCodeValues, hcode]
  dsimp only [x, hx, selected0, hvalid, row] at hwhole hq ⊢
  simp only [ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula] at hq ⊢
  rw [hq]
  rfl

private theorem incomingLiveValues_shared_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i j : Fin (p.m - 1)) (t : Fin p.T)
    (live : ReferenceActivePhysicalStep.Payload rate ×
      ReferenceActivePhysicalStepMeasurability.LiveDiscrete p) :
    (incomingLiveValues rate rewards i t live).1 =
        (incomingLiveValues rate rewards j t live).1 ∧
      (incomingLiveValues rate rewards i t live).2.2.1 =
        (incomingLiveValues rate rewards j t live).2.2.1 ∧
      (incomingLiveValues rate rewards i t live).2.2.2.2 =
        (incomingLiveValues rate rewards j t live).2.2.2.2 := by
  exact ⟨rfl, rfl, rfl⟩

private theorem incomingOptionValues_shared_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (i j : Fin (p.m - 1)) (t : Fin p.T)
    (code : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) :
    (incomingOptionValues rate rewards i t code).1 =
        (incomingOptionValues rate rewards j t code).1 ∧
      (incomingOptionValues rate rewards i t code).2.2.1 =
        (incomingOptionValues rate rewards j t code).2.2.1 ∧
      (incomingOptionValues rate rewards i t code).2.2.2.2 =
        (incomingOptionValues rate rewards j t code).2.2.2.2 := by
  cases code with
  | none => simp [incomingOptionValues, zeroValues]
  | some code =>
      cases hcoord : code.1 with
      | inl _ => simp [incomingOptionValues, incomingStateCodeValues, zeroValues, hcoord]
      | inr tail =>
          cases tail with
          | inl live =>
              simpa [incomingOptionValues, incomingStateCodeValues, hcoord] using
                incomingLiveValues_shared_readouts rate rewards i j t live
          | inr tail =>
              cases tail with
              | inl _ => simp [incomingOptionValues, incomingStateCodeValues, zeroValues, hcoord]
              | inr _ => simp [incomingOptionValues, incomingStateCodeValues, zeroValues, hcoord]

private theorem measurableCoefficientValues_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b) := by
  let field := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h t.val (le_of_lt t.isLt)
  have hguard := ReferenceFirstLiveInspectedGuardReadout.measurableSet_inspected_guard
    rate rewards C_star C_h control0 i t q s hs b
  have hincoming := ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
    rate rewards C_star C_h t.val (le_of_lt t.isLt) t le_rfl
  have hreadout := (measurable_incomingOptionValues (p := p) rate rewards i t).comp hincoming
  have hpiece : Measurable[field] (fun z : SourceInput p =>
      if z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b then
        incomingOptionValues rate rewards i t
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)
      else zeroValues) := Measurable.ite hguard hreadout measurable_const
  have heq : firstLiveInspectedCoefficientValues rate rewards C_star C_h
      control0 i t q s hs b = fun z =>
        if z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b then
          incomingOptionValues rate rewards i t
            (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)
        else zeroValues := by
    funext z
    by_cases hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b
    · simp only [ite_eq_left hz]
      exact coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
        control0 i t q s hs b z hz
    · simp [firstLiveInspectedCoefficientValues, hz, zeroValues]
  rw [heq]
  exact hpiece

private theorem measurableCoefficientValues_ambient
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedCoefficientValues rate rewards C_star C_h
      control0 i t q s hs b) := by
  exact (measurableCoefficientValues_in_inspectedField rate rewards C_star C_h
      control0 i t q s hs b).mono
    (ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)) le_rfl

theorem firstLiveInspectedCoefficientValues_measurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b) :=
  measurableCoefficientValues_in_inspectedField rate rewards C_star C_h
    control0 i t q s hs b

theorem firstLiveInspectedCoefficientValues_stronglyMeasurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0 i t q s hs b) :=
  (firstLiveInspectedCoefficientValues_measurable_in_inspectedField rate rewards C_star C_h
    control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedCoefficientValues_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedCoefficientValues rate rewards C_star C_h
      control0 i t q s hs b) :=
  measurableCoefficientValues_ambient rate rewards C_star C_h control0 i t q s hs b

theorem firstLiveInspectedCoefficientValues_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable (firstLiveInspectedCoefficientValues rate rewards C_star C_h
      control0 i t q s hs b) :=
  (firstLiveInspectedCoefficientValues_measurable rate rewards C_star C_h
    control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedUpCoefficient_measurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (firstLiveInspectedCoefficientValues_measurable_in_inspectedField
    rate rewards C_star C_h control0 i t q s hs b)

theorem firstLiveInspectedDataCoefficient_measurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (measurable_snd.comp
    (firstLiveInspectedCoefficientValues_measurable_in_inspectedField rate rewards C_star C_h
      control0 i t q s hs b))

theorem firstLiveInspectedAuxiliaryChi_measurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (firstLiveInspectedCoefficientValues_measurable_in_inspectedField rate rewards C_star C_h
      control0 i t q s hs b)))

theorem firstLiveInspectedAssignedChi_measurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedAssignedChi rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp
      (firstLiveInspectedCoefficientValues_measurable_in_inspectedField rate rewards C_star C_h
        control0 i t q s hs b))))

theorem firstLiveInspectedAuxiliaryWeightedChi_measurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp
      (firstLiveInspectedCoefficientValues_measurable_in_inspectedField rate rewards C_star C_h
        control0 i t q s hs b))))

private theorem selectedCoefficientValues_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceFirstLiveReleaseGeometry.Selection x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (i : Fin (p.m - 1)) (row : ActiveRoundActions.RewardRow p.K) :
    0 ≤ ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected hvalid row ∧
      ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected hvalid row ≤ 1 ∧
    0 ≤ ReleaseRoundKernel.chi row (selected.view.payload.assignment.assigned i) /
      (2 * (p.K : ℝ)) ∧
      ReleaseRoundKernel.chi row (selected.view.payload.assignment.assigned i) /
        (2 * (p.K : ℝ)) ≤ 1 ∧
    0 ≤ ReleaseRoundKernel.chi row selected.view.payload.assignment.auxiliary ∧
      ReleaseRoundKernel.chi row selected.view.payload.assignment.auxiliary ≤ 1 ∧
    0 ≤ ReleaseRoundKernel.chi row (selected.view.payload.assignment.assigned i) ∧
      ReleaseRoundKernel.chi row (selected.view.payload.assignment.assigned i) ≤ 1 ∧
    0 ≤ (CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
        selected.view.payload.eta_le_source_cap selected.view.payload.anchor
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
        selected.view.payload.anchor_pos
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected hvalid a).1)
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected hvalid a).2.1)
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected hvalid a).2.2)
        selected.view.payload.slowSet
        (ReleaseRoundKernel.auxiliaryFastArm selected.view.payload.assignment
          selected.view.payload.slowSet selected.view.payload.assignment_image.symm)) *
      ReleaseRoundKernel.chi row selected.view.payload.assignment.auxiliary ∧
    (CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
        selected.view.payload.eta_le_source_cap selected.view.payload.anchor
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
        selected.view.payload.anchor_pos
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected hvalid a).1)
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected hvalid a).2.1)
        (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected hvalid a).2.2)
        selected.view.payload.slowSet
        (ReleaseRoundKernel.auxiliaryFastArm selected.view.payload.assignment
          selected.view.payload.slowSet selected.view.payload.assignment_image.symm)) *
      ReleaseRoundKernel.chi row selected.view.payload.assignment.auxiliary ≤ 1 := by
  let payload := selected.view.payload
  let weights := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected
  let weightBounds := fun a =>
    ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid a
  let e := ReleaseRoundKernel.auxiliaryFastArm payload.assignment payload.slowSet
    payload.assignment_image.symm
  let qAux := CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
    payload.eta_le_source_cap payload.anchor weights payload.anchor_pos
    (fun a => (weightBounds a).1) (fun a => (weightBounds a).2.1)
    (fun a => (weightBounds a).2.2) payload.slowSet e
  have hmin : ∀ j : CanonicalFastSampling.FastArm payload.slowSet,
      payload.anchor e.1 ≤ payload.anchor j.1 := by
    intro j
    have he : e.1 = payload.assignment.auxiliary := rfl
    rw [he]
    exact payload.auxiliaryArm_anchor_minimum j.1 j.property
  have hqle : qAux ≤ 2 / 3 := by
    dsimp only [qAux, e, weightBounds, weights]
    exact CanonicalFastSampling.qGamma_auxiliary_arm_le_two_thirds
      p rate.eta.property payload.eta_le_source_cap payload.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).2.2) payload.slowSet e hmin
  have hqpos : 0 < qAux := by
    dsimp only [qAux, e, weightBounds, weights]
    exact CanonicalFastSampling.qGamma_pos p rate.eta.property
      payload.eta_le_source_cap payload.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected)
      payload.anchor_pos
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).2.1)
      (fun a => (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
        selected hvalid a).2.2) payload.slowSet e
  have hchiAux : 0 ≤ ReleaseRoundKernel.chi row payload.assignment.auxiliary ∧
      ReleaseRoundKernel.chi row payload.assignment.auxiliary ≤ 1 := by
    unfold ReleaseRoundKernel.chi
    split <;> norm_num
  have hchiAssigned : 0 ≤ ReleaseRoundKernel.chi row (payload.assignment.assigned i) ∧
      ReleaseRoundKernel.chi row (payload.assignment.assigned i) ≤ 1 := by
    unfold ReleaseRoundKernel.chi
    split <;> norm_num
  have hmR : (2 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast p.two_le_m
  have hm1 : (1 : ℝ) ≤ (p.m : ℝ) - 1 := by linarith
  have hK : (3 : ℝ) ≤ (p.K : ℝ) := by
    have hmK : p.m < p.K := p.m_lt_K
    have hmNat : 2 ≤ p.m := p.two_le_m
    have hKnat : 3 ≤ p.K := by omega
    exact_mod_cast hKnat
  have hdenUp : (12 : ℝ) ≤ 4 * ((p.m : ℝ) - 1) * (p.K : ℝ) := by
    nlinarith
  have hdenData : (6 : ℝ) ≤ 2 * (p.K : ℝ) := by
    nlinarith
  have hdenUpPos : 0 < 4 * ((p.m : ℝ) - 1) * (p.K : ℝ) := by linarith
  have hdenDataPos : 0 < 2 * (p.K : ℝ) := by linarith
  have hfactor : 0 ≤ 1 - qAux := by linarith
  have hnum : ReleaseRoundKernel.chi row payload.assignment.auxiliary * (1 - qAux) ≤ 1 := by
    calc
      ReleaseRoundKernel.chi row payload.assignment.auxiliary * (1 - qAux) ≤
          (1 : ℝ) * 1 :=
        mul_le_mul hchiAux.2 (sub_le_self 1 hqpos.le) hfactor (by norm_num)
      _ = 1 := by ring
  have hup_eq : ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
      selected hvalid row =
      ReleaseRoundKernel.chi row payload.assignment.auxiliary * (1 - qAux) /
        (4 * ((p.m : ℝ) - 1) * (p.K : ℝ)) := by
    rfl
  have hup_nonneg : 0 ≤ ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula
      selected hvalid row := by
    rw [hup_eq]
    exact div_nonneg (mul_nonneg hchiAux.1 hfactor) (le_of_lt hdenUpPos)
  have hup_le : ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected hvalid row ≤ 1 := by
    rw [hup_eq]
    apply (div_le_one hdenUpPos).2
    nlinarith [hnum, hdenUp]
  have hdata_nonneg : 0 ≤ ReleaseRoundKernel.chi row (payload.assignment.assigned i) /
      (2 * (p.K : ℝ)) :=
    div_nonneg hchiAssigned.1 (le_of_lt hdenDataPos)
  have hdata_le : ReleaseRoundKernel.chi row (payload.assignment.assigned i) /
      (2 * (p.K : ℝ)) ≤ 1 := by
    apply (div_le_one hdenDataPos).2
    exact hchiAssigned.2.trans (by linarith)
  have hweighted_nonneg : 0 ≤ qAux * ReleaseRoundKernel.chi row payload.assignment.auxiliary :=
    mul_nonneg hqpos.le hchiAux.1
  have hweighted_le : qAux * ReleaseRoundKernel.chi row payload.assignment.auxiliary ≤ 1 := by
    calc
      qAux * ReleaseRoundKernel.chi row payload.assignment.auxiliary ≤
          (2 / 3 : ℝ) * 1 :=
        mul_le_mul hqle hchiAux.2 hchiAux.1 (by norm_num)
      _ ≤ 1 := by norm_num
  refine ⟨hup_nonneg, hup_le, hdata_nonneg, hdata_le,
    hchiAux.1, hchiAux.2, hchiAssigned.1, hchiAssigned.2,
    hweighted_nonneg, ?_⟩
  simpa only [qAux, e, weightBounds, weights] using hweighted_le

private theorem coefficientValues_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    let c := firstLiveInspectedCoefficientValues rate rewards C_star C_h
      control0 i t q s hs b z
    0 ≤ c.1 ∧ c.1 ≤ 1 ∧
      0 ≤ c.2.1 ∧ c.2.1 ≤ 1 ∧
      0 ≤ c.2.2.1 ∧ c.2.2.1 ≤ 1 ∧
      0 ≤ c.2.2.2.1 ∧ c.2.2.2.1 ≤ 1 ∧
      0 ≤ c.2.2.2.2 ∧ c.2.2.2.2 ≤ 1 := by
  classical
  by_cases hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b
  · let branch : z ∈ ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
        rate rewards C_star C_h control0 i t q s hs := hz.1
    let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
      rate rewards C_star C_h control0 i t q s hs z branch
    let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
      rate rewards C_star C_h control0 i t q s hs z branch
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
      rate rewards C_star C_h q t s hs control0 i x hx
    let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
    have hbounds := selectedCoefficientValues_bounds rate selected0 hvalid i row
    simpa only [firstLiveInspectedCoefficientValues, dite_eq_left hz] using hbounds
  · simp only [firstLiveInspectedCoefficientValues, dite_eq_right hz, zeroValues]
    norm_num

/-- Every actual inspected coefficient and both reward readouts lie in the
unit interval. On the live branch the estimates use the selected whole-field
baseline and the same incoming-code fast-arm probability; outside it the
literal analytic coefficients are zero. -/
theorem firstLiveInspectedCoefficientValues_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    let c := firstLiveInspectedCoefficientValues rate rewards C_star C_h
      control0 i t q s hs b z
    0 ≤ c.1 ∧ c.1 ≤ 1 ∧
      0 ≤ c.2.1 ∧ c.2.1 ≤ 1 ∧
      0 ≤ c.2.2.1 ∧ c.2.2.1 ≤ 1 ∧
      0 ≤ c.2.2.2.1 ∧ c.2.2.2.1 ≤ 1 ∧
      0 ≤ c.2.2.2.2 ∧ c.2.2.2.2 ≤ 1 :=
  coefficientValues_bounds rate rewards C_star C_h control0 i t q s hs b z

private theorem integrable_of_unit_interval
    {f : SourceInput p → ℝ} (hf : Measurable f)
    (hbound : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Integrable f (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(hbound z).1], (hbound z).2⟩

theorem firstLiveInspectedUpCoefficient_stronglyMeasurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b) :=
  (firstLiveInspectedUpCoefficient_measurable_in_inspectedField
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedDataCoefficient_stronglyMeasurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b) :=
  (firstLiveInspectedDataCoefficient_measurable_in_inspectedField
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedAuxiliaryChi_stronglyMeasurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b) :=
  (firstLiveInspectedAuxiliaryChi_measurable_in_inspectedField
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedAssignedChi_stronglyMeasurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedAssignedChi rate rewards C_star C_h control0 i t q s hs b) :=
  (firstLiveInspectedAssignedChi_measurable_in_inspectedField
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedAuxiliaryWeightedChi_stronglyMeasurable_in_inspectedField
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable[ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
      rate rewards C_star C_h t.val (le_of_lt t.isLt)]
      (firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 i t q s hs b) :=
  (firstLiveInspectedAuxiliaryWeightedChi_measurable_in_inspectedField
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedUpCoefficient_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (firstLiveInspectedCoefficientValues_measurable
    rate rewards C_star C_h control0 i t q s hs b)

theorem firstLiveInspectedDataCoefficient_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (measurable_snd.comp
    (firstLiveInspectedCoefficientValues_measurable
      rate rewards C_star C_h control0 i t q s hs b))

theorem firstLiveInspectedAuxiliaryChi_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
    (firstLiveInspectedCoefficientValues_measurable
      rate rewards C_star C_h control0 i t q s hs b)))

theorem firstLiveInspectedAssignedChi_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedAssignedChi rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (firstLiveInspectedCoefficientValues_measurable
      rate rewards C_star C_h control0 i t q s hs b))))

theorem firstLiveInspectedAuxiliaryWeightedChi_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Measurable (firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (firstLiveInspectedCoefficientValues_measurable
      rate rewards C_star C_h control0 i t q s hs b))))

theorem firstLiveInspectedUpCoefficient_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable (firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b) := by
  exact (firstLiveInspectedUpCoefficient_measurable
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedDataCoefficient_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable (firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b) := by
  exact (firstLiveInspectedDataCoefficient_measurable
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedAuxiliaryChi_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable (firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b) := by
  exact (firstLiveInspectedAuxiliaryChi_measurable
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedAssignedChi_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable (firstLiveInspectedAssignedChi rate rewards C_star C_h control0 i t q s hs b) := by
  exact (firstLiveInspectedAssignedChi_measurable
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedAuxiliaryWeightedChi_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    StronglyMeasurable (firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 i t q s hs b) := by
  exact (firstLiveInspectedAuxiliaryWeightedChi_measurable
    rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

theorem firstLiveInspectedUpCoefficient_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Integrable (firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_unit_interval (firstLiveInspectedUpCoefficient_measurable
    rate rewards C_star C_h control0 i t q s hs b)
  intro z
  rcases firstLiveInspectedCoefficientValues_bounds rate rewards C_star C_h control0
      i t q s hs b z with ⟨h0, h1, -, -, -, -, -, -, -, -⟩
  exact ⟨h0, h1⟩

theorem firstLiveInspectedDataCoefficient_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Integrable (firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_unit_interval (firstLiveInspectedDataCoefficient_measurable
    rate rewards C_star C_h control0 i t q s hs b)
  intro z
  rcases firstLiveInspectedCoefficientValues_bounds rate rewards C_star C_h control0
      i t q s hs b z with ⟨-, -, h0, h1, -, -, -, -, -, -⟩
  exact ⟨h0, h1⟩

theorem firstLiveInspectedAuxiliaryChi_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Integrable (firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_unit_interval (firstLiveInspectedAuxiliaryChi_measurable
    rate rewards C_star C_h control0 i t q s hs b)
  intro z
  rcases firstLiveInspectedCoefficientValues_bounds rate rewards C_star C_h control0
      i t q s hs b z with ⟨-, -, -, -, h0, h1, -, -, -, -⟩
  exact ⟨h0, h1⟩

theorem firstLiveInspectedAssignedChi_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Integrable (firstLiveInspectedAssignedChi rate rewards C_star C_h control0 i t q s hs b)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_unit_interval (firstLiveInspectedAssignedChi_measurable
    rate rewards C_star C_h control0 i t q s hs b)
  intro z
  rcases firstLiveInspectedCoefficientValues_bounds rate rewards C_star C_h control0
      i t q s hs b z with ⟨-, -, -, -, -, -, h0, h1, -, -⟩
  exact ⟨h0, h1⟩

theorem firstLiveInspectedAuxiliaryWeightedChi_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) :
    Integrable (firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 i t q s hs b)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_of_unit_interval (firstLiveInspectedAuxiliaryWeightedChi_measurable
    rate rewards C_star C_h control0 i t q s hs b)
  intro z
  rcases firstLiveInspectedCoefficientValues_bounds rate rewards C_star C_h control0
      i t q s hs b z with ⟨-, -, -, -, -, -, -, -, h0, h1⟩
  exact ⟨h0, h1⟩

private theorem firstLiveInspectedUpCoefficient_eq_actual_on_guard
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b) :
    firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z := by
  have hsections := ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
    rate rewards C_star C_h control0 i t q s hs z hz.1
  rcases hsections with ⟨hup, _hdata, _hrelease, _hlower⟩
  simpa only [firstLiveInspectedUpCoefficient,
    firstLiveInspectedCoefficientValues, dite_eq_left hz] using hup.symm

private theorem firstLiveInspectedDataCoefficient_eq_actual_on_guard
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b) :
    firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z := by
  have hsections := ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
    rate rewards C_star C_h control0 i t q s hs z hz.1
  rcases hsections with ⟨_hup, hdata, _hrelease, _hlower⟩
  simpa only [firstLiveInspectedDataCoefficient,
    firstLiveInspectedCoefficientValues, dite_eq_left hz] using hdata.symm

private theorem firstLiveInspectedReleaseCoefficient_eq_actual_on_guard
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b) :
    firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b z +
        firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
        rate rewards C_star C_h control0 i t z := by
  have hsections := ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
    rate rewards C_star C_h control0 i t q s hs z hz.1
  rcases hsections with ⟨hup, hdata, hrelease, _hlower⟩
  rw [firstLiveInspectedUpCoefficient_eq_actual_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hz,
    firstLiveInspectedDataCoefficient_eq_actual_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hz]
  rw [hup, hdata]
  exact hrelease.symm

/-- Globally, the analytic UP coefficient is the indicator of the actual UP
control section. Its value is zero off the guarded first-live event. -/
theorem firstLiveInspectedUpCoefficient_eq_guarded_actualUpControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      (guardedEvent rate rewards C_star C_h control0 i t q s hs b).indicator
        (fun z => ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z) z := by
  classical
  by_cases hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b
  · rw [Set.indicator_of_mem hz]
    exact firstLiveInspectedUpCoefficient_eq_actual_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hz
  · rw [Set.indicator_of_notMem hz]
    simp [firstLiveInspectedUpCoefficient, firstLiveInspectedCoefficientValues,
      zeroValues, hz]

/-- Globally, the DATA coefficient is the indicator of the actual DATA
control section, retaining the actual follower index `i`. -/
theorem firstLiveInspectedDataCoefficient_eq_guarded_actualDataControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      (guardedEvent rate rewards C_star C_h control0 i t q s hs b).indicator
        (fun z => ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z) z := by
  classical
  by_cases hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b
  · rw [Set.indicator_of_mem hz]
    exact firstLiveInspectedDataCoefficient_eq_actual_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hz
  · rw [Set.indicator_of_notMem hz]
    simp [firstLiveInspectedDataCoefficient, firstLiveInspectedCoefficientValues,
      zeroValues, hz]

/-- The sum of the two actual inspected coefficients is globally the
indicator of the actual release control section. -/
theorem firstLiveInspectedCoefficients_sum_eq_guarded_actualReleaseControlSection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b z +
        firstLiveInspectedDataCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      (guardedEvent rate rewards C_star C_h control0 i t q s hs b).indicator
        (fun z => ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
          rate rewards C_star C_h control0 i t z) z := by
  classical
  by_cases hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b
  · rw [Set.indicator_of_mem hz]
    exact firstLiveInspectedReleaseCoefficient_eq_actual_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hz
  · rw [Set.indicator_of_notMem hz]
    simp [firstLiveInspectedUpCoefficient, firstLiveInspectedDataCoefficient,
      firstLiveInspectedCoefficientValues, zeroValues, hz]

/-- The first guarded coefficient dominates the source's local UP lower
bound. The right-hand side is the actual guarded auxiliary reward readout,
which is identically zero outside the live branch. -/
theorem firstLiveInspectedUpCoefficient_ge_guarded_auxiliary_lower_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p) :
    firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b z /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
      firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b z := by
  classical
  by_cases hz : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b
  · have hsections := ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
      rate rewards C_star C_h control0 i t q s hs z hz.1
    rcases hsections with ⟨hup, _hdata, _hrelease, hlower⟩
    rw [hup] at hlower
    simpa only [firstLiveInspectedAuxiliaryChi, firstLiveInspectedUpCoefficient,
      firstLiveInspectedCoefficientValues, dite_eq_left hz] using hlower
  · simp [firstLiveInspectedAuxiliaryChi, firstLiveInspectedUpCoefficient,
      firstLiveInspectedCoefficientValues, zeroValues, hz]

/-- The same source point and same incoming LIVE code determine the UP-side
coefficient for every follower whose guarded branch overlaps. The selected
payload, anchor, and complete current complement weights are recovered from
that shared code by `baseline_fields_eq_incoming`; `i` remains present only in
the assigned-arm DATA component. -/
theorem firstLiveInspectedUpCoefficient_eq_of_overlapping_guarded_branches
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i j : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hi : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b)
    (hj : z ∈ guardedEvent rate rewards C_star C_h control0 j t q s hs b) :
    firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 i t q s hs b z =
      firstLiveInspectedUpCoefficient rate rewards C_star C_h control0 j t q s hs b z := by
  change (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0
      i t q s hs b z).1 =
    (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0
      j t q s hs b z).1
  rw [coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hi,
    coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
      control0 j t q s hs b z hj]
  exact (incomingOptionValues_shared_readouts rate rewards i j t
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)).1

/-- The auxiliary reward readout agrees across overlapping guarded follower
branches because both are decoded from the same actual incoming LIVE payload. -/
theorem firstLiveInspectedAuxiliaryChi_eq_of_overlapping_guarded_branches
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i j : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hi : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b)
    (hj : z ∈ guardedEvent rate rewards C_star C_h control0 j t q s hs b) :
    firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 i t q s hs b z =
      firstLiveInspectedAuxiliaryChi rate rewards C_star C_h control0 j t q s hs b z := by
  change (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0
      i t q s hs b z).2.2.1 =
    (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0
      j t q s hs b z).2.2.1
  rw [coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hi,
    coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
      control0 j t q s hs b z hj]
  exact (incomingOptionValues_shared_readouts rate rewards i j t
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)).2.1

/-- The auxiliary fast-probability-weighted reward also agrees across an
overlap. Its fast probability uses the literal whole current weights recovered
from that same LIVE code, rather than a free or merely timestamp-matched law. -/
theorem firstLiveInspectedAuxiliaryWeightedChi_eq_of_overlapping_guarded_branches
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i j : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
    (s : ℕ) (hs : s ≤ t.val) (b : ℕ) (z : SourceInput p)
    (hi : z ∈ guardedEvent rate rewards C_star C_h control0 i t q s hs b)
    (hj : z ∈ guardedEvent rate rewards C_star C_h control0 j t q s hs b) :
    firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 i t q s hs b z =
      firstLiveInspectedAuxiliaryWeightedChi rate rewards C_star C_h control0 j t q s hs b z := by
  change (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0
      i t q s hs b z).2.2.2.2 =
    (firstLiveInspectedCoefficientValues rate rewards C_star C_h control0
      j t q s hs b z).2.2.2.2
  rw [coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
      control0 i t q s hs b z hi,
    coefficientValues_eq_incoming_on_guard rate rewards C_star C_h
      control0 j t q s hs b z hj]
  exact (incomingOptionValues_shared_readouts rate rewards i j t
    (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)).2.2

end Bandits.Support.ReferenceFirstLiveInspectedCoefficients

end
