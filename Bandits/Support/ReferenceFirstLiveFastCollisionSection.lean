/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInspectedConditionalService

/-!
# First-live fast-collision charge on one whole control section

Sources: sources/zip4/manuscript/05_binary_transport.tex:318-348 and
sources/zip4/manuscript/06_interruptions.tex:452-492.

This module proves the exact whole-control integral at an actual retained
first-live selected-empty choice and transports that section back to its
original source. The source law is neither normalized nor conditioned here.
This is not the inspected-history conditional law or the stopped waiting
theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped ENNReal

namespace Bandits.Support.ReferenceFirstLiveFastCollisionSection

abbrev Parameters := ConstructorDimensions.Parameters
abbrev TimeControl := ContinuousLearningRows.TimeControl

/-- The analytic sentinel charge on an actual physical record. -/
def recordFastCollisionCharge
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (M : ReferenceActivePhysicalStep.Payload rate)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ℝ :=
  if r.actions (ActiveRoundActions.coordinator p.two_le_m) = M.assignment.auxiliary ∧
      (ReferencePhysicalReleaseQuota.pendingSet M r).Nonempty then
    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
      r.input.rewards r.input.time).val M.assignment.auxiliary
  else 0

/-- The source readout keeps absent records and absent payloads absent. -/
def sourceFastCollisionCharge
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (source : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source with
  | none => 0
  | some r =>
      match ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator with
      | none => 0
      | some M => recordFastCollisionCharge M r

/-- The exact canonical fast probability at the selector's auxiliary arm. -/
def qAuxiliary
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights) : ℝ :=
  let M := selected.view.payload
  let w := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected
  let hb := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid
  CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
    M.eta_le_source_cap M.anchor w M.anchor_pos
    (fun a => (hb a).1) (fun a => (hb a).2.1) (fun a => (hb a).2.2)
    M.slowSet
    (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet M.assignment_image.symm)

private def fastDraw
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights)
    (u : TimeControl p) :
    CanonicalFastSampling.FastArm selected.view.payload.slowSet :=
  let M := selected.view.payload
  let w := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected
  let hb := ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds selected hvalid
  CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
    M.eta_le_source_cap M.anchor w M.anchor_pos
    (fun a => (hb a).1) (fun a => (hb a).2.1) (fun a => (hb a).2.2)
    M.slowSet (u.1 (ContinuousControlSlice.Label.fast))

private def fastAuxiliaryEvent
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (selected : ReferenceActivePhysicalStep.Selection x)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload
      selected.view.cutoff x.time selected.view.complementWeights) :
    Set (TimeControl p) :=
  {u | fastDraw selected hvalid u =
    ReleaseRoundKernel.auxiliaryFastArm selected.view.payload.assignment
      selected.view.payload.slowSet selected.view.payload.assignment_image.symm}

private theorem payloadCompleteCurrentWeights_congr
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (M₁ M₂ : ReferenceActivePhysicalStep.Payload rate) (hM : M₁ = M₂)
    (w₁ : CanonicalFastSampling.FastArm M₁.slowSet → ℝ)
    (w₂ : CanonicalFastSampling.FastArm M₂.slowSet → ℝ) (hw : HEq w₁ w₂) :
    ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights M₁ w₁ =
      ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights M₂ w₂ := by
  cases hM
  cases hw
  rfl

private theorem fastSample_value_congr
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (M₁ M₂ : ReferenceActivePhysicalStep.Payload rate) (hM : M₁ = M₂)
    (w₁ w₂ : Fin p.K → ℝ) (hw : w₁ = w₂)
    (bounds₁ : ∀ a, 0 < w₁ a ∧ M₁.anchor a ≤ w₁ a ∧ w₁ a ≤ 2 * M₁.anchor a)
    (bounds₂ : ∀ a, 0 < w₂ a ∧ M₂.anchor a ≤ w₂ a ∧ w₂ a ≤ 2 * M₂.anchor a)
    (z : ContinuousCategorical.Scalar) :
    (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
      M₁.eta_le_source_cap M₁.anchor w₁ M₁.anchor_pos
      (fun a => (bounds₁ a).1) (fun a => (bounds₁ a).2.1)
      (fun a => (bounds₁ a).2.2) M₁.slowSet z).val =
    (CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
      M₂.eta_le_source_cap M₂.anchor w₂ M₂.anchor_pos
      (fun a => (bounds₂ a).1) (fun a => (bounds₂ a).2.1)
      (fun a => (bounds₂ a).2.2) M₂.slowSet z).val := by
  cases hM
  cases hw
  rfl

private theorem choiceInputsValid_transport
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (M₁ M₂ : ReferenceActivePhysicalStep.Payload rate) (hM : M₁ = M₂)
    (c₁ c₂ : Option (CoordinatorLocalArmChoice.Cutoff p)) (hc : c₁ = c₂)
    (t₁ t₂ : Fin p.T) (ht : t₁ = t₂)
    (w₁ : CanonicalFastSampling.FastArm M₁.slowSet → ℝ)
    (w₂ : CanonicalFastSampling.FastArm M₂.slowSet → ℝ) (hw : HEq w₁ w₂)
    (hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid M₂ c₂ t₂ w₂) :
    CoordinatorLocalArmChoice.ChoiceInputsValid M₁ c₁ t₁ w₁ := by
  cases hM
  cases hc
  cases ht
  cases hw
  exact hvalid

/-- The marginal of the fast coordinate of a whole time control has the
accepted scalar sampler's exact singleton mass. -/
private theorem fastSample_coordinate_singleton
    (p : ConstructorDimensions.Parameters) (eta : ℝ) (heta : 0 < eta)
    (heta_le : eta ≤
      1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ)))
    (v w : Fin p.K → ℝ) (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hvw : ∀ j, v j ≤ w j) (hwv : ∀ j, w j ≤ 2 * v j)
    (U : CanonicalOrientedSetLaw.SlowSet p.K p.m)
    (e : CanonicalFastSampling.FastArm U) :
    ContinuousLearningRows.timeControlLaw p
        {u | CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U
          (u.1 (ContinuousControlSlice.Label.fast)) = e} =
      ENNReal.ofReal (CanonicalFastSampling.qGamma p eta heta heta_le v w hv hw hvw hwv U e) := by
  let coordinate : TimeControl p → ContinuousCategorical.Scalar :=
    fun u => ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1
  let sample : ContinuousCategorical.Scalar → CanonicalFastSampling.FastArm U :=
    CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U
  have hcoord : MeasurePreserving coordinate (ContinuousLearningRows.timeControlLaw p)
      ContinuousCategorical.uniform := by
    have hmp := (ContinuousControlSlice.measurePreserving_coordinate
      ContinuousControlSlice.Label.fast).comp
      (ContinuousLearningRows.measurePreserving_slice p)
    simpa only [coordinate, Function.comp_def, ContinuousControlSlice.scalarLaw,
      ContinuousCategorical.uniform] using hmp
  have hsample : Measurable sample :=
    CanonicalFastSampling.measurable_sampleFast p eta heta heta_le v w hv hw hvw hwv U
  have hpre : ContinuousLearningRows.timeControlLaw p
      (coordinate ⁻¹' (sample ⁻¹' {e})) =
        ContinuousCategorical.uniform (sample ⁻¹' {e}) :=
    hcoord.measure_preimage
      (s := sample ⁻¹' {e}) (hsample (measurableSet_singleton e)).nullMeasurableSet
  calc
    ContinuousLearningRows.timeControlLaw p
        {u | CanonicalFastSampling.sampleFast p eta heta heta_le v w hv hw hvw hwv U
          (u.1 (ContinuousControlSlice.Label.fast)) = e} =
        ContinuousLearningRows.timeControlLaw p (coordinate ⁻¹' (sample ⁻¹' {e})) := by
          rfl
    _ = ContinuousCategorical.uniform (sample ⁻¹' {e}) := hpre
    _ = ENNReal.ofReal (CanonicalFastSampling.qGamma p eta heta heta_le
          v w hv hw hvw hwv U e) :=
      CanonicalFastSampling.uniform_sampleFast_singleton p eta heta heta_le
        v w hv hw hvw hwv U e

/-- A record whose input is fixed is the literal physical record of that
input; the output equality supplies its only output field. -/
private theorem record_eq_recordOfInput
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (x : ReferenceActivePhysicalStep.RoundInput p rate) (h : r.input = x) :
    r = ReferencePhysicalReleaseObservability.recordOfInput x := by
  cases r with
  | mk input output output_eq =>
      cases h
      cases output_eq
      rfl

/-- Exact fast-collision section integral on the original retained
fixed-current whole-control remainder. -/
theorem retained_selected_empty_fast_collision_integral
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
    (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)
    (x : ReferenceRetainedBoundaryMeasurability.RetainedLaunchStart
      rate rewards C_star C_h q t s hs control0)
    (hn : t.val - s <
      (ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0).length)
    (selected0 : ReferenceActivePhysicalStep.Selection
      ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s]'hn).input)
    (hselected :
      ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s]'hn).output.preparation.coordinator.selection =
        some selected0)
    (hempty : selected0.view.pendingAtChoice = ∅) :
    ∃ hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
      selected0.view.cutoff
      ((ReferenceFirstLiveReleaseControlTransport.retainedWindow
        rewards C_star C_h q t s hs control0 x control0)[t.val - s]'hn).input.time
      selected0.view.complementWeights,
      let M := selected0.view.payload
      let P0 := ReferencePhysicalReleaseQuota.pendingAtStart M
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x).time
        (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
          rate rewards C_star C_h q t s hs control0 x).state
      let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
      let f := fun u : TimeControl p =>
        recordFastCollisionCharge M
          (ReferencePhysicalReleaseObservability.recordOfInput
            (ReferenceFirstLiveReleaseCylinderIntegral.currentInput
              rate rewards C_star C_h q t s hs control0 x u))
      MeasureTheory.Integrable f (ContinuousLearningRows.timeControlLaw p) ∧
        (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) =
          qAuxiliary selected0 hvalid * row.val M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) ∧
        (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) ≤
          qAuxiliary selected0 hvalid * ReleaseRoundKernel.chi row M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) := by
  classical
  let W := ReferenceFirstLiveReleaseControlTransport.retainedWindow (rate := rate)
    rewards C_star C_h q t s hs control0
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let n := t.val - s
  let x0 := (W x control0)[n]'hn
  let M := selected0.view.payload
  let P0 := ReferencePhysicalReleaseQuota.pendingAtStart M beta.time beta.state
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  have htransport :=
    ReferenceFirstLiveReleaseControlTransport.retained_first_live_control_transport
      rewards C_star C_h q t s hs control0 x hn selected0 hselected hempty
  rcases htransport with
    ⟨rLive, owned, base, hbeta, hstate, htimeNext, hprior, hpending,
      hnoCut, hpayload, hcutoff, hweights, d, hsStart, c, arm, hctor,
      hvalid, states, memories, hprepared, hfields, hpendingStatus, hcontrols⟩
  have hbetaTime : beta.time = x0.input.time := congrArg
    ReferenceActivePhysicalStep.RoundInput.time hbeta
  have hbetaState : beta.state = x0.input.state := congrArg
    ReferenceActivePhysicalStep.RoundInput.state hbeta
  have hvalidBase :
      CoordinatorLocalArmChoice.ChoiceInputsValid selected0.view.payload
        selected0.view.cutoff x0.input.time selected0.view.complementWeights := hvalid
  have hcutoffBase : selected0.view.cutoff = none := hcutoff
  let f := fun u : TimeControl p =>
    recordFastCollisionCharge M
      (ReferencePhysicalReleaseObservability.recordOfInput
        (ReferenceFirstLiveReleaseCylinderIntegral.currentInput
          rate rewards C_star C_h q t s hs control0 x u))
  let event := fastAuxiliaryEvent selected0 hvalidBase
  have hsampleMeas : Measurable (fun u : TimeControl p => fastDraw selected0 hvalidBase u) := by
    have hcoord : Measurable
        (fun u : TimeControl p =>
          ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast u.1) :=
      (ContinuousControlSlice.measurable_coordinate
        ContinuousControlSlice.Label.fast).comp measurable_fst
    exact (CanonicalFastSampling.measurable_sampleFast p rate.eta.val rate.eta.property
      M.eta_le_source_cap M.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
      M.anchor_pos
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.2)
      M.slowSet).comp hcoord
  have heventMeas : MeasurableSet event := by
    change MeasurableSet
      {u | fastDraw selected0 hvalidBase u =
        ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet
          M.assignment_image.symm}
    exact hsampleMeas (measurableSet_singleton _)
  have hqnonneg : 0 ≤ qAuxiliary selected0 hvalidBase := by
    change 0 ≤ CanonicalFastSampling.qGamma p rate.eta.val rate.eta.property
      M.eta_le_source_cap M.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
      M.anchor_pos
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.2)
      M.slowSet
      (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet M.assignment_image.symm)
    exact CanonicalFastSampling.qGamma_nonneg p rate.eta.property
      M.eta_le_source_cap M.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
      M.anchor_pos
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.2)
      M.slowSet
      (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet M.assignment_image.symm)
  have heventMeasure :
      ContinuousLearningRows.timeControlLaw p event =
        ENNReal.ofReal (qAuxiliary selected0 hvalidBase) := by
    change ContinuousLearningRows.timeControlLaw p
        {u | CanonicalFastSampling.sampleFast p rate.eta.val rate.eta.property
          M.eta_le_source_cap M.anchor
          (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
          M.anchor_pos
          (fun a =>
            (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
              selected0 hvalidBase a).1)
          (fun a =>
            (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
              selected0 hvalidBase a).2.1)
          (fun a =>
            (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
              selected0 hvalidBase a).2.2)
          M.slowSet (u.1 (ContinuousControlSlice.Label.fast)) =
          ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet
            M.assignment_image.symm} = _
    dsimp only [qAuxiliary]
    exact fastSample_coordinate_singleton p rate.eta.val rate.eta.property
      M.eta_le_source_cap M.anchor
      (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0)
      M.anchor_pos
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.1)
      (fun a =>
        (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
          selected0 hvalidBase a).2.2)
      M.slowSet
      (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet M.assignment_image.symm)
  let chargedEvent : Set (TimeControl p) :=
    {u | P0.Nonempty ∧ u ∈ event}
  have hchargedMeas : MeasurableSet chargedEvent := by
    by_cases hp : P0.Nonempty
    · simpa [chargedEvent, hp] using heventMeas
    · simp [chargedEvent, hp]
  have hchargedReal :
      (ContinuousLearningRows.timeControlLaw p).real chargedEvent =
        if P0.Nonempty then qAuxiliary selected0 hvalidBase else 0 := by
    by_cases hp : P0.Nonempty
    · have hset : chargedEvent = event := by
        ext u
        simp [chargedEvent, hp]
      rw [Measure.real, hset, heventMeasure, ENNReal.toReal_ofReal hqnonneg]
      simp [hp]
    · simp [chargedEvent, hp]
  have hrowLe :
      row.val M.assignment.auxiliary ≤
        ReleaseRoundKernel.chi row M.assignment.auxiliary := by
    unfold ReleaseRoundKernel.chi
    by_cases hpos : 0 < row.val M.assignment.auxiliary
    · simpa [hpos] using (row.property M.assignment.auxiliary).2
    · have hz : row.val M.assignment.auxiliary = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (row.property M.assignment.auxiliary).1
      simp [hz]
  have hsectionPoint :
      ∀ u : TimeControl p,
        f u = chargedEvent.indicator (fun _ : TimeControl p =>
          row.val M.assignment.auxiliary) u := by
    intro u
    let current := ReferenceFirstLiveReleaseCylinderIntegral.currentInput
      rate rewards C_star C_h q t s hs control0 x u
    obtain ⟨hwindow, hwindowInput, _, _, _, selectedU, hselectedU, hselectedOutputU,
      hpayloadU, hpendingU, hcutoffU, hweightsU, _⟩ := hcontrols u
    let record := (W x u)[n]'hwindow
    have hrecordInput : record.input =
        ReferenceLaterOptionalControlResampling.withControl beta u := by
      simpa only [record, n, W, ReferenceFirstLiveReleaseControlTransport.retainedWindow]
        using hwindowInput
    have hrecordInputTime : record.input.time = current.time := by
      calc
        record.input.time =
            (ReferenceLaterOptionalControlResampling.withControl beta u).time :=
          congrArg ReferenceActivePhysicalStep.RoundInput.time hrecordInput
        _ = current.time := rfl
    have hrecordInputState : record.input.state = current.state := by
      calc
        record.input.state =
            (ReferenceLaterOptionalControlResampling.withControl beta u).state :=
          congrArg ReferenceActivePhysicalStep.RoundInput.state hrecordInput
        _ = current.state := rfl
    have hrecordInputRewards : record.input.rewards = current.rewards := by
      calc
        record.input.rewards =
            (ReferenceLaterOptionalControlResampling.withControl beta u).rewards :=
          congrArg ReferenceActivePhysicalStep.RoundInput.rewards hrecordInput
        _ = current.rewards := rfl
    have hcurrentTime : current.time = beta.time := by
      change (ReferenceLaterOptionalControlResampling.withControl beta u).time = beta.time
      exact ReferenceLaterOptionalControlResampling.withControl_time beta u
    have hcurrentState : current.state = beta.state := by
      change (ReferenceLaterOptionalControlResampling.withControl beta u).state = beta.state
      exact ReferenceLaterOptionalControlResampling.withControl_state beta u
    have hcurrentRewards : current.rewards = beta.rewards := by
      change (ReferenceLaterOptionalControlResampling.withControl beta u).rewards = beta.rewards
      exact ReferenceLaterOptionalControlResampling.withControl_rewards beta u
    have htimeU : record.input.time = x0.input.time := by
      calc
        record.input.time = current.time := hrecordInputTime
        _ = beta.time := hcurrentTime
        _ = x0.input.time := hbetaTime
    have hvalidU : CoordinatorLocalArmChoice.ChoiceInputsValid selectedU.view.payload
        selectedU.view.cutoff record.input.time selectedU.view.complementWeights :=
      choiceInputsValid_transport selectedU.view.payload selected0.view.payload
        hpayloadU selectedU.view.cutoff selected0.view.cutoff hcutoffU
        record.input.time x0.input.time
        htimeU
        selectedU.view.complementWeights
        selected0.view.complementWeights hweightsU hvalidBase
    have hemptyU : selectedU.view.pendingAtChoice = ∅ := by
      rw [hpendingU, hempty]
    have hliveU : CoordinatorLocalArmChoice.assignmentIsLive selectedU.view.payload
        selectedU.view.cutoff record.input.time := by
      rw [hcutoffU, hcutoffBase]
      change CoordinatorLocalArmChoice.assignmentStart selectedU.view.payload ≤
          CoordinatorLocalArmChoice.sourceRound record.input.time ∧
        CoordinatorLocalArmChoice.sourceRound record.input.time <
          CoordinatorLocalArmChoice.cutoffRound none
      refine ⟨hvalidU.time.assignment_started, ?_⟩
      simp only [CoordinatorLocalArmChoice.cutoffRound, Option.elim_none]
      have hsource := hvalidU.time.source_round_le_horizon
      omega
    have hfastFacts :=
      ReferenceFirstLiveReleaseGeometry.actual_releaseRoundInput_fast_eq_selected
        selectedU hliveU hemptyU hvalidU
    let actualWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstLiveReleaseControlTransport.retainedRun
        rewards C_star C_h q t s hs control0 x u).records
    let actualRecord := actualWindow[n]'hwindow
    have hactualInput : actualRecord.input =
        ReferenceLaterOptionalControlResampling.withControl beta u := by
      simpa only [actualRecord, actualWindow] using hwindowInput
    have hcontrolSliceActual :
        (actualRecord.input.row.2 actualRecord.input.time).1 = u.1 := by
      rw [hactualInput]
      change ((ReferenceLaterOptionalControlResampling.withControl beta u).row.2
        beta.time).1 = u.1
      exact congrArg Prod.fst
        (ReferenceLaterOptionalControlResampling.withControl_currentControl beta u)
    have hfastCoordinateActual :
        ContinuousControlSlice.coordinate ContinuousControlSlice.Label.fast
          ((actualRecord.input.row.2 actualRecord.input.time).1) =
          u.1 (ContinuousControlSlice.Label.fast) := by
      change (actualRecord.input.row.2 actualRecord.input.time).1
        (ContinuousControlSlice.Label.fast) = _
      exact congrArg (fun z : ContinuousControlSlice.Slice p.m p.K =>
        z (ContinuousControlSlice.Label.fast)) hcontrolSliceActual
    have hfastCoordinateExpanded := hfastCoordinateActual
    simp only [actualRecord, actualWindow, n]
      at hfastCoordinateExpanded
    have hsampleU : (fastDraw selectedU hvalidU u).val = selectedU.arm := by
      have h := hfastFacts.1
      simp only [ReleaseRoundKernel.releaseRoundInput] at h
      rw [hfastCoordinateExpanded] at h
      simpa only [fastDraw, actualRecord, actualWindow,
        ReleaseRoundKernel.releaseRoundInput] using h
    have hsampleBase : (fastDraw selected0 hvalidBase u).val = selectedU.arm := by
      have hcompletePayload := payloadCompleteCurrentWeights_congr
        selectedU.view.payload selected0.view.payload hpayloadU
        selectedU.view.complementWeights selected0.view.complementWeights hweightsU
      have hcomplete : ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selectedU =
          ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0 := by
        calc
          ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selectedU =
              ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
                selectedU.view.payload selectedU.view.complementWeights := rfl
          _ = ReferenceFirstLiveReleaseSliceMass.payloadCompleteCurrentWeights
              selected0.view.payload selected0.view.complementWeights := hcompletePayload
          _ = ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0 := rfl
      have hsampleEq : (fastDraw selectedU hvalidU u).val =
          (fastDraw selected0 hvalidBase u).val := by
        unfold fastDraw
        exact fastSample_value_congr selectedU.view.payload selected0.view.payload
          hpayloadU (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selectedU)
          (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights selected0) hcomplete
          (fun a =>
            (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
              selectedU hvalidU a))
          (fun a =>
            (ReferenceFirstLiveReleaseGeometry.completeCurrentWeights_bounds
              selected0 hvalidBase a))
          (u.1 (ContinuousControlSlice.Label.fast))
      rw [hsampleEq] at hsampleU
      exact hsampleU
    have haction : record.actions (ActiveRoundActions.coordinator p.two_le_m) =
        selectedU.arm := by
      change record.output.preparation.arms.actions
        (ActiveRoundActions.coordinator p.two_le_m) = selectedU.arm
      rw [ReferenceActivePhysicalStep.PreparedRound.action_coordinator]
      change record.output.preparation.coordinator.arm = selectedU.arm
      have hselectedRecord :
          record.output.preparation.coordinator.selection = some selectedU := by
        simpa only [record, n, W,
          ReferenceFirstLiveReleaseControlTransport.retainedWindow] using hselectedOutputU
      simp [ReferenceActivePhysicalStep.DispatchCut.arm, hselectedRecord]
    have hpendingSet :
        ReferencePhysicalReleaseQuota.pendingSet M record = P0 := by
      change ReferencePhysicalReleaseQuota.pendingAtStart M record.input.time record.input.state =
        ReferencePhysicalReleaseQuota.pendingAtStart M beta.time beta.state
      rw [hrecordInputTime, hrecordInputState, hcurrentTime, hcurrentState]
    have hrowRecord :
        (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time) = row := by
      change ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow
          record.input.rewards record.input.time =
        ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
      rw [hrecordInputRewards, hrecordInputTime, hcurrentRewards, hcurrentTime,
        ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary_time]
      rfl
    have hauxValue :
        (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet
          M.assignment_image.symm).val = M.assignment.auxiliary := rfl
    have hcondition :
        record.actions (ActiveRoundActions.coordinator p.two_le_m) =
          M.assignment.auxiliary ↔
        fastDraw selected0 hvalidBase u =
          ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet
            M.assignment_image.symm := by
      constructor
      · intro h
        apply Subtype.ext
        calc
          (fastDraw selected0 hvalidBase u).val = selectedU.arm := hsampleBase
          _ = record.actions (ActiveRoundActions.coordinator p.two_le_m) := haction.symm
          _ = M.assignment.auxiliary := h
          _ = (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet
            M.assignment_image.symm).val := hauxValue.symm
      · intro h
        have hv := congrArg Subtype.val h
        calc
          record.actions (ActiveRoundActions.coordinator p.two_le_m) = selectedU.arm := haction
          _ = (fastDraw selected0 hvalidBase u).val := hsampleBase.symm
          _ = (ReleaseRoundKernel.auxiliaryFastArm M.assignment M.slowSet
            M.assignment_image.symm).val := hv
          _ = M.assignment.auxiliary := hauxValue
    have hindicator :
        recordFastCollisionCharge M record =
          chargedEvent.indicator (fun _ : TimeControl p =>
            row.val M.assignment.auxiliary) u := by
      unfold recordFastCollisionCharge
      rw [hrowRecord, hpendingSet]
      by_cases hp : P0.Nonempty
      · simp [chargedEvent, event, fastAuxiliaryEvent, M, hp, hcondition,
          Set.indicator_apply]
      · simp [chargedEvent, hp]
    have hrecordEq : record =
        ReferencePhysicalReleaseObservability.recordOfInput current := by
      apply record_eq_recordOfInput
      simpa only [current, ReferenceFirstLiveReleaseCylinderIntegral.currentInput] using
        hrecordInput
    rw [hrecordEq] at hindicator
    exact hindicator
  have hconstIntegrable :
      Integrable (fun _ : TimeControl p => row.val M.assignment.auxiliary)
        (ContinuousLearningRows.timeControlLaw p) := integrable_const _
  have hintegrableIndicator :
      Integrable (chargedEvent.indicator
        (fun _ : TimeControl p => row.val M.assignment.auxiliary))
        (ContinuousLearningRows.timeControlLaw p) :=
    hconstIntegrable.indicator hchargedMeas
  have hintegrable : Integrable f (ContinuousLearningRows.timeControlLaw p) := by
    apply hintegrableIndicator.congr
    exact Filter.Eventually.of_forall (fun u => (hsectionPoint u).symm)
  have hintegral :
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) =
        qAuxiliary selected0 hvalidBase * row.val M.assignment.auxiliary *
          (if P0.Nonempty then 1 else 0) := by
    calc
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) =
          ∫ u, chargedEvent.indicator
            (fun _ : TimeControl p => row.val M.assignment.auxiliary) u
              ∂ContinuousLearningRows.timeControlLaw p := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hsectionPoint
      _ = (ContinuousLearningRows.timeControlLaw p).real chargedEvent *
            row.val M.assignment.auxiliary := by
              rw [integral_indicator_const (row.val M.assignment.auxiliary) hchargedMeas,
                smul_eq_mul]
      _ = qAuxiliary selected0 hvalidBase * row.val M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) := by
              rw [hchargedReal]
              by_cases hp : P0.Nonempty <;> simp [hp, mul_comm]
  have hintegralBound :
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) ≤
        qAuxiliary selected0 hvalidBase *
          ReleaseRoundKernel.chi row M.assignment.auxiliary *
          (if P0.Nonempty then 1 else 0) := by
    by_cases hp : P0.Nonempty
    · simp only [ite_eq_left hp, mul_one] at hintegral ⊢
      rw [hintegral]
      exact mul_le_mul_of_nonneg_left hrowLe hqnonneg
    · simpa only [ite_eq_right hp, mul_zero] using hintegral.le
  refine ⟨hvalidBase, ?_⟩
  dsimp only
  exact ⟨hintegrable, hintegral, hintegralBound⟩

/-- On the actual first-live source branch, the original optional record and
stored payload recover the same fixed-control section, with no branch
probability normalization. -/
theorem actual_source_fast_collision_section
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (ConstructorDimensions.M p))
    (s : ℕ) (hs : s ≤ t.val)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (hbranch : source ∈
      ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
        rate rewards C_star C_h control0 i t q s hs) :
    let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
      rate rewards C_star C_h control0 i t q s hs source hbranch
    let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
      rate rewards C_star C_h control0 i t q s hs source hbranch
    let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
      rate rewards C_star C_h q t s hs control0 i x hx
    let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
      rate rewards C_star C_h q t s hs control0 i x hx
    let M := selected0.view.payload
    let P0 := ReferencePhysicalReleaseQuota.pendingAtStart M
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).time
      (ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
        rate rewards C_star C_h q t s hs control0 x).state
    let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
    let f := fun u : TimeControl p =>
      sourceFastCollisionCharge rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source u)
    MeasureTheory.Integrable f (ContinuousLearningRows.timeControlLaw p) ∧
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) =
        qAuxiliary selected0 hvalid * row.val M.assignment.auxiliary *
          (if P0.Nonempty then 1 else 0) ∧
      (∫ u, f u ∂ContinuousLearningRows.timeControlLaw p) ≤
        qAuxiliary selected0 hvalid * ReleaseRoundKernel.chi row M.assignment.auxiliary *
          (if P0.Nonempty then 1 else 0) := by
  classical
  let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
    rate rewards C_star C_h control0 i t q s hs source hbranch
  let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
    rate rewards C_star C_h control0 i t q s hs source hbranch
  let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
    rate rewards C_star C_h q t s hs control0 i x hx
  let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
    rate rewards C_star C_h q t s hs control0 i x hx
  let M := selected0.view.payload
  let beta := ReferenceRetainedBoundaryMeasurability.retainedIncomingBoundary
    rate rewards C_star C_h q t s hs control0 x
  let P0 := ReferencePhysicalReleaseQuota.pendingAtStart M beta.time beta.state
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let W := ReferenceFirstLiveReleaseControlTransport.retainedWindow (rate := rate)
    rewards C_star C_h q t s hs control0
  let n := t.val - s
  have hn := ReferenceFirstLiveReleaseCylinderIntegral.baseline_index_lt
    rate rewards C_star C_h q t s hs control0 i x hx
  have hspec := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_spec
    rate rewards C_star C_h q t s hs control0 i x hx
  obtain ⟨hsectionValid, hsectionFacts⟩ :=
    retained_selected_empty_fast_collision_integral rate rewards C_star C_h q t s hs
      control0 x hn selected0 hspec.1 hspec.2.1
  rcases hsectionFacts with
    ⟨hsectionIntegrable, hsectionIntegral, hsectionBound⟩
  have hvalidEq : qAuxiliary selected0 hsectionValid = qAuxiliary selected0 hvalid := by
    congr 1
  let fRetained := fun u : TimeControl p =>
    recordFastCollisionCharge M
      (ReferencePhysicalReleaseObservability.recordOfInput
        (ReferenceFirstLiveReleaseCylinderIntegral.currentInput
          rate rewards C_star C_h q t s hs control0 x u))
  let fSource := fun u : TimeControl p =>
    sourceFastCollisionCharge rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source u)
  have hpoint : ∀ u : TimeControl p, fSource u = fRetained u := by
    intro u
    have hflags :=
      ReferenceFirstLiveActualFlagSections.actual_flags_eq_retained_flags
        rate rewards C_star C_h control0 i t q s hs source hbranch u
    rcases hflags with ⟨hwindow, hrecord, hpayload, _, _⟩
    have hcontrols :=
      ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_all_controls
        rate rewards C_star C_h q t s hs control0 i x hx
    obtain ⟨_, hcontrols⟩ := hcontrols
    let hu := Classical.choose (hcontrols u)
    have hselectedExists := Classical.choose_spec (hcontrols u)
    let selectedU := Classical.choose hselectedExists
    have hinput := (Classical.choose_spec hselectedExists).1
    have hwindowProof : hu = hwindow := Subsingleton.elim _ _
    have hinput' :
        ((W x u)[n]'hwindow).input =
          ReferenceFirstLiveReleaseCylinderIntegral.currentInput
            rate rewards C_star C_h q t s hs control0 x u := by
      simpa only [hwindowProof] using hinput
    have hinputHu :
        ((W x u)[n]'hu).input =
          ReferenceFirstLiveReleaseCylinderIntegral.currentInput
            rate rewards C_star C_h q t s hs control0 x u := by
      simpa only [hwindowProof] using hinput
    have hrecordHu :
        ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source u) =
        some ((W x u)[n]'hu) := by
      simpa only [hwindowProof.symm] using hrecord
    have hpayloadHu :
        ReferenceAssignmentPayloadPersistence.storedPayload
          ((W x u)[n]'hu).input.state.coordinator = some selected0.view.payload := by
      simpa only [hwindowProof.symm] using hpayload
    have hrecordEq :
        (W x u)[n]'hu =
          ReferencePhysicalReleaseObservability.recordOfInput
            (ReferenceFirstLiveReleaseCylinderIntegral.currentInput
              rate rewards C_star C_h q t s hs control0 x u) := by
      exact record_eq_recordOfInput ((W x u)[n]'hu) _ hinputHu
    simp only [fSource, fRetained, sourceFastCollisionCharge, hrecordHu, hpayloadHu]
    exact congrArg (recordFastCollisionCharge M) hrecordEq

  have hfun : fSource = fRetained := funext hpoint
  have hsourceIntegrable :
      Integrable fSource (ContinuousLearningRows.timeControlLaw p) := by
    simpa only [hfun] using hsectionIntegrable
  have hsourceIntegral :
      (∫ u, fSource u ∂ContinuousLearningRows.timeControlLaw p) =
        qAuxiliary selected0 hvalid * row.val M.assignment.auxiliary *
          (if P0.Nonempty then 1 else 0) := by
    calc
      (∫ u, fSource u ∂ContinuousLearningRows.timeControlLaw p) =
          ∫ u, fRetained u ∂ContinuousLearningRows.timeControlLaw p := by
            rw [hfun]
      _ = qAuxiliary selected0 hsectionValid * row.val M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) := hsectionIntegral
      _ = qAuxiliary selected0 hvalid * row.val M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) := by rw [hvalidEq]
  have hsourceBound :
      (∫ u, fSource u ∂ContinuousLearningRows.timeControlLaw p) ≤
        qAuxiliary selected0 hvalid * ReleaseRoundKernel.chi row M.assignment.auxiliary *
          (if P0.Nonempty then 1 else 0) := by
    calc
      (∫ u, fSource u ∂ContinuousLearningRows.timeControlLaw p) =
          ∫ u, fRetained u ∂ContinuousLearningRows.timeControlLaw p := by
            rw [hfun]
      _ ≤ qAuxiliary selected0 hsectionValid *
            ReleaseRoundKernel.chi row M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) := hsectionBound
      _ = qAuxiliary selected0 hvalid *
            ReleaseRoundKernel.chi row M.assignment.auxiliary *
            (if P0.Nonempty then 1 else 0) := by rw [hvalidEq]
  refine ⟨hsourceIntegrable, hsourceIntegral, hsourceBound⟩

end Bandits.Support.ReferenceFirstLiveFastCollisionSection

end
